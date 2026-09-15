/// Experimental compiler target. Actor state remains inside each Actor object's
/// private closure. These tables contain roots, identities and continuations.
/// The actor* frontend will eventually generate receive/resume code; the initial
/// fixture supplies it explicitly. This is not yet a public language feature.
import LocalId "LocalId";
import Nat64 "mo:core/Nat64";
import Runtime "mo:core/Runtime";
import VarArray "mo:core/VarArray";
import List "mo:core/List";

module {
  public let rootedRequestMethod : Text = "\00moxzi.rooted.v1";
  public type Ref = { container : Principal; slot : Nat64; generation : Nat64 };
  public type IdentityStatus = {#live; #retired; #unknown; #foreign};
  public type Continuation = { owner : Ref; slot : Nat64; generation : Nat64 };
  public type Reply = { #ok : Blob; #err : Text };
  public type LocalCall = { target : Ref; method : Text; arg : Blob };
  public type ExternalCall = { target : Principal; method : Text; arg : Blob };
  public type Request = { #local : LocalCall; #external : ExternalCall; #rooted : {target : Ref; slot : Nat64; generation : Nat64} };
  public type Step = {
    #done : Reply;
    #suspend : { request : Request; resume : Reply -> Step };
    // Internal compiler target: release turn-owned transport roots on successful
    // resumption, cancellation or retirement. Cleanup is journaled, never finalizer GC.
    #suspendManaged : { request : Request; resume : Reply -> Step; cleanup : () -> () };
  };
  public type Outcome = { #done : Reply; #readOnly : Reply; #suspended : { request : Request; continuation : Continuation } };
  public type Frame = { outcome : Outcome; retired : [Ref] };
  public type Actor = { receive : (Text, Blob) -> Step };
  /// Caller is supplied by the scheduler, never inferred from a game payload.
  /// A queued sender's generation remains meaningful after its retirement.
  public type Caller = { #host; #external : Principal; #local : Ref };
  public type Context = { self : Ref; caller : Caller };
  public type ContextActor = { receive : (Context, Text, Blob) -> Step };
  public type RootContextActor = {receive : (Context,Text,Blob) -> Step; receiveRoot : (Context,Nat64,Nat64) -> Step};
  /// Compiler-private type erasure. Only the compiler may supply a signature
  /// and reconstitute a closure after resolveComputation validates it. This is
  /// not a source-level dynamic cast or a serializable method representation.
  public type ComputationMethod = { name : Text; signature : Text; value : Any };
  public type ComputationStorage = { methods : [ComputationMethod] };
  /// Trusted ingress provenance. Local provenance is derived from the executing
  /// frame, never supplied by a bound method or its creator.
  public type ComputationIngress = { #host; #external : Principal };
  type ComputationFrame = ?(Nat, Context, ComputationFrame);
  type Receiver = { receive : (?Caller, Text, Blob) -> Step; root : ?((Caller,Nat64,Nat64) -> Step); computations : ?ComputationStorage };
  type Entry = { identity : Ref; instance : Receiver; var queries : ?[Text]; var pending : ?Nat };
  type Pending = { identity : Continuation; resume : Reply -> Step; cleanup : ?(() -> ()); var prev : ?Nat; var next : ?Nat };

  public class Kernel(container : Principal, capacity : Nat, continuationCapacity : Nat) {
    /// Pure reference construction: validation and canonical owner binding only.
    public func referenceComputation(owner : ?Principal, id : Principal) : Ref {
      let ?parts=LocalId.decode(id) else Runtime.trap("invalid actor* local ID");
      {container=switch(owner){case null container;case(?explicit) explicit};
       slot=parts.slot;generation=parts.generation}
    };
    let actors = VarArray.repeat<?Entry>(null, capacity);
    let generations = VarArray.repeat<Nat64>(1, capacity);
    // Bounded retirement evidence: one high-water generation per registry slot.
    // Separate from next-generation counters so exhausted generations and slots
    // reserved for future use are never mistaken for completed retirement.
    let retiredGenerations = VarArray.repeat<Nat64>(0, capacity);
    let free = VarArray.tabulate<Nat>(capacity, func i { i + 1 });
    var freeHead = 0;
    var live = 0;
    let pending = VarArray.repeat<?Pending>(null, continuationCapacity);
    let continuationGenerations = VarArray.repeat<Nat64>(1, continuationCapacity);
    let continuationFree = VarArray.tabulate<Nat>(continuationCapacity, func i { i + 1 });
    var continuationHead = 0;
    var pendingCount = 0;
    var retired = List.empty<Ref>();
    var reading = false;
    var computationFrame : ComputationFrame = null;
    var computationTicket = 0;
    var computationDepth = 0;
    // Explicit bound for inline recursion, independent of display/actor count.
    let computationDepthLimit = 128;
    var scalarRootPublisher : ?((Ref,Ref,Nat64,Nat64) -> ()) = null;
    public func installScalarRequests(publish : (Ref,Ref,Nat64,Nat64) -> ()) {
      assert live == 0 and pendingCount == 0;
      switch scalarRootPublisher {case null {};case _ Runtime.trap("scalar root publisher already installed")};
      scalarRootPublisher := ?publish
    };
    var rootPublisher : ?((Ref, Ref, Blob) -> ()) = null;
    public func installRootedRequests(publish : (Ref, Ref, Blob) -> ()) {
      assert live == 0 and pendingCount == 0;
      switch rootPublisher {case null {}; case _ Runtime.trap("root publisher already installed")};
      rootPublisher := ?publish
    };

    /// Registry evidence only: live is an observation, never an authority/lease.
    /// Unknown (including future/unallocated IDs) must not authorize compensation.
    public func identityStatus(id : Ref) : IdentityStatus {
      if(id.container != container) return #foreign;
      let i=Nat64.toNat(id.slot);
      if(i>=capacity or id.generation==0) return #unknown;
      switch(actors[i]) {
        case(?e) {if(e.identity.generation==id.generation)return #live};
        case null {}
      };
      if(id.generation<=retiredGenerations[i]) #retired else #unknown
    };

    func entry(id : Ref) : Entry {
      if (id.container != container) Runtime.trap("foreign local-actor container");
      let i = Nat64.toNat(id.slot);
      if (i >= capacity) Runtime.trap("local actor slot out of range");
      switch (actors[i]) {
        case (?e) {
          if (e.identity.generation != id.generation) Runtime.trap("stale local actor generation");
          e;
        };
        case null Runtime.trap("local actor retired");
      };
    };
    func continuation(id : Continuation) : Pending {
      ignore entry(id.owner);
      let i = Nat64.toNat(id.slot);
      if (i >= continuationCapacity) Runtime.trap("continuation slot out of range");
      switch (pending[i]) {
        case (?p) {
          if (p.identity != id) Runtime.trap("stale local continuation");
          p;
        };
        case null Runtime.trap("local continuation already consumed");
      };
    };

    func allocate(make : Ref -> Receiver) : Ref {
      if (reading) Runtime.trap("actor creation is unavailable in a read-only call");
      if (freeHead >= capacity) Runtime.trap("local actor capacity exceeded");
      let i = freeHead;
      freeHead := free[i];
      let identity = { container; slot = Nat64.fromNat(i); generation = generations[i] };
      let instance = make(identity);
      actors[i] := ?{ identity; instance; var queries = null; var pending = null };
      live += 1;
      identity;
    };

    public func spawn(make : Ref -> Actor) : Ref {
      allocate(func id {
        let instance = make(id);
        { root = null; computations = null; receive = func (_caller : ?Caller, method : Text, arg : Blob) : Step { instance.receive(method, arg) } };
      });
    };
    public func spawnContext(make : Ref -> ContextActor) : Ref {
      allocate(func id {
        let instance = make(id);
        { root = null; computations = null; receive = func (caller : ?Caller, method : Text, arg : Blob) : Step {
          let source = switch caller {
            case (?value) value;
            case null Runtime.trap("local caller context required");
          };
          instance.receive({ self = id; caller = source }, method, arg);
        } };
      });
    };

    public func spawnRootContext(make : Ref -> RootContextActor) : Ref {
      allocate(func id {
        let instance=make(id);
        {computations=null;receive=func(caller : ?Caller,method : Text,arg : Blob) : Step {
          let ?source=caller else Runtime.trap("local caller context required");
          instance.receive({self=id;caller=source},method,arg)
        };
        root=?(func(caller : Caller,slot : Nat64,generation : Nat64) : Step {
          instance.receiveRoot({self=id;caller},slot,generation)
        })}
      })
    };
    /// Shares identity allocation and retirement with queued actors, but never
    /// installs a queued receiver. Factory execution is synchronous. Its private
    /// state is rooted by the registered method closures in this container heap.
    public func spawnComputation(make : Ref -> ComputationStorage) : Ref {
      allocate(func id {
        let storage = make(id);
        // Reject ambiguous compiler tables before publishing the identity.
        var i = 0;
        while (i < storage.methods.size()) {
          let method = storage.methods[i];
          if (method.name == "" or method.signature == "") Runtime.trap("invalid computation method descriptor");
          var j = 0;
          while (j < i) {
            if (storage.methods[j].name == method.name) Runtime.trap("duplicate computation method");
            j += 1
          };
          i += 1
        };
        { computations = ?storage; root = null;
          receive = func (_caller : ?Caller, _method : Text, _arg : Blob) : Step {
            Runtime.trap("computation actor requires inline dispatch")
          }
        }
      })
    };
    /// Call from INSIDE the deferred computation, on every execution. Resolving
    /// while building/caching a bound computation would bypass retirement.
    /// No method invocation, message, continuation allocation or commit occurs.
    public func resolveComputation(id : Ref, method : Text, signature : Text) : Any {
      let e = entry(id);
      let ?storage = e.instance.computations else Runtime.trap("actor lacks computation storage");
      for (candidate in storage.methods.vals()) {
        if (candidate.name == method) {
          if (candidate.signature != signature) Runtime.trap("computation method signature mismatch");
          return candidate.value
        }
      };
      Runtime.trap("unknown computation method")
    };
    /// Compiler-private execution ABI, not a source capability. Enter only
    /// after deferred receiver/signature resolution, on EVERY evaluation. The
    /// ingress argument must come from the host/IC execution context, not from
    /// the source program or a computation's captured creation context.
    ///
    /// This stack is container heap state: a trap rolls it back with the whole
    /// segment. Generated code must leave on normal returns AND caught-language
    /// error propagation. External suspension is not supported by this ABI;
    /// continuation save/restore belongs to S31. No message/commit is performed.
    public func enterComputation(id : Ref, ingress : ComputationIngress) : Nat {
      let e = entry(id);
      switch (e.instance.computations) {
        case null Runtime.trap("actor lacks computation storage");
        case _ {};
      };
      let caller : Caller = switch computationFrame {
        case (?( _, parent, _)) #local(parent.self);
        case null switch ingress {
          case (#host) #host;
          case (#external principal) #external(principal);
        };
      };
      // A depth or receiver ID alone would allow a stale exit token to pop a
      // later frame, particularly during A -> B -> A reentry. Never reuse a
      // ticket within a committed heap history. Trap rollback rolls back both.
      if (computationDepth >= computationDepthLimit) Runtime.trap("local computation depth limit exceeded");
      computationDepth += 1;
      computationTicket += 1;
      computationFrame := ?(computationTicket, {self = id; caller}, computationFrame);
      computationTicket
    };
    public func computationContext() : Context {
      switch computationFrame {
        case (?( _, context, _)) context;
        case null Runtime.trap("no executing computation actor");
      }
    };
    /// Explicit source self-retirement authority, tied to this invocation ticket.
    /// It cannot retire a sibling or be saved and reused by a later invocation.
    public func computationRetirementContext() : {self : Ref; caller : Caller; retire : () -> ()} {
      let ?(ticket, context, _) = computationFrame else Runtime.trap("no executing computation actor");
      {self=context.self; caller=context.caller; retire=func () {
        let ?(active, current, parent) = computationFrame else Runtime.trap("no executing computation actor");
        if(active != ticket or current.self != context.self)
          Runtime.trap("retirement requires its current computation invocation");
        var cursor=parent;
        label scan loop {
          switch cursor {
            case null break scan;
            case(?( _, other, rest)) {
              if(other.self==current.self) Runtime.trap("local actor retirement is busy");
              cursor := rest
            }
          }
        };
        retire(current.self)
      }}
    };
    public func leaveComputation(ticket : Nat) {
      switch computationFrame {
        case (?(current, _, parent)) {
          if (ticket != current) Runtime.trap("computation frame exit out of order");
          computationFrame := parent;
          computationDepth -= 1
        };
        case null Runtime.trap("no executing computation actor");
      }
    };
    public func dispatchRoot(id : Ref,caller : Caller,slot : Nat64,generation : Nat64) : Frame {
      switch caller {case (#local source) {assert source.container == container};case _ Runtime.trap("rooted request requires local caller")};
      let e=entry(id);
      let ?invoke=e.instance.root else Runtime.trap("actor lacks scalar request receiver");
      settle(id,invoke(caller,slot,generation))
    };

    func cleanup(p : Pending) {
      switch (p.cleanup) { case (?run) run(); case null {} }
    };

    func release(p : Pending) {
      let i = Nat64.toNat(p.identity.slot);
      let e = entry(p.identity.owner);
      switch (p.prev) {
        case null { e.pending := p.next };
        case (?j) { switch (pending[j]) { case (?before) before.next := p.next; case null Runtime.trap("broken continuation predecessor") } };
      };
      switch (p.next) {
        case null {};
        case (?j) { switch (pending[j]) { case (?after) after.prev := p.prev; case null Runtime.trap("broken continuation successor") } };
      };
      pending[i] := null;
      pendingCount -= 1;
      // Burn exhausted slots instead of letting an old token alias a new one.
      if (continuationGenerations[i] != 18_446_744_073_709_551_615) {
        continuationGenerations[i] += 1;
        continuationFree[i] := continuationHead;
        continuationHead := i;
      };
    };

    public func retire(id : Ref) {
      if (reading) Runtime.trap("actor retirement is unavailable in a read-only call");
      let e = entry(id);
      label clean loop {
        switch (e.pending) {
          case null break clean;
          case (?i) { switch (pending[i]) { case (?p) {cleanup(p); release(p)}; case null Runtime.trap("broken actor continuation list") } };
        };
      };
      let i = Nat64.toNat(id.slot);
      retiredGenerations[i] := id.generation;
      actors[i] := null;
      live -= 1;
      if (generations[i] != 18_446_744_073_709_551_615) {
        generations[i] += 1;
        free[i] := freeHead;
        freeHead := i;
      };
      List.add(retired, id);
    };

    func park(owner : Ref, request : Request, resume : Reply -> Step, clean : ?(() -> ())) : Outcome {
      let e = entry(owner);
      switch request {
        case (#rooted call) {
          let ?publish=scalarRootPublisher else Runtime.trap("scalar root publisher unavailable");
          publish(owner,call.target,call.slot,call.generation)
        };
        case (#local call) {
          if (call.method == rootedRequestMethod) {
            let ?publish = rootPublisher else Runtime.trap("rooted request publisher unavailable");
            publish(owner,call.target,call.arg)
          }
        };
        case _ {}
      };
      if (continuationHead >= continuationCapacity) Runtime.trap("local continuation capacity exceeded");
      let i = continuationHead;
      continuationHead := continuationFree[i];
      let identity = { owner; slot = Nat64.fromNat(i); generation = continuationGenerations[i] };
      let p = { identity; resume; cleanup = clean; var prev = null : ?Nat; var next = e.pending };
      switch (e.pending) {
        case null {};
        case (?j) { switch (pending[j]) { case (?old) old.prev := ?i; case null Runtime.trap("broken pending head") } };
      };
      pending[i] := ?p;
      e.pending := ?i;
      pendingCount += 1;
      #suspended({ request; continuation = identity })
    };

    func settle(owner : Ref, step : Step) : Frame {
      let outcome : Outcome = switch step {
        case (#done reply) #done(reply);
        case (#suspend action) park(owner, action.request, action.resume, null);
        case (#suspendManaged action) park(owner, action.request, action.resume, ?action.cleanup);
      };
      let removed = List.toArray(retired);
      retired := List.empty<Ref>();
      { outcome; retired = removed };
    };

    /// Host-only read entry. The host MUST roll back this entire slice, including
    /// successful calls. Prevent lifecycle identities escaping temporary state.
    public func read(id : Ref, method : Text, arg : Blob) : Reply { readFrom(id, #host, method, arg) };
    public func registerQueries(id : Ref, names : [Text]) {
      if (reading) Runtime.trap("query registration is unavailable in a read-only call");
      let e=entry(id);
      switch(e.queries) {case null {};case _ Runtime.trap("query methods already registered")};
      e.queries := ?names
    };
    func isQuery(e : Entry, method : Text) : Bool {
      switch(e.queries) {case null false;case(?names) {for(name in names.vals()) if(name==method) return true;false}}
    };
    func readFrom(id : Ref, caller : Caller, method : Text, arg : Blob) : Reply {
      if (reading) Runtime.trap("nested read-only dispatch");
      let e = entry(id);
      reading := true;
      let result = e.instance.receive(?caller, method, arg);
      reading := false;
      switch result {
        case (#done reply) reply;
        case _ Runtime.trap("read-only calls cannot suspend");
      }
    };

    public func dispatch(id : Ref, method : Text, arg : Blob) : Frame {
      let e = entry(id);
      if(isQuery(e,method)) return {outcome=#readOnly(readFrom(id,#host,method,arg));retired=[]};
      settle(id, e.instance.receive(null, method, arg));
    };
    public func dispatchFrom(id : Ref, caller : Caller, method : Text, arg : Blob) : Frame {
      switch caller {
        case (#local sender) {
          if (sender.container != container) Runtime.trap("foreign local caller");
          // Do not revalidate sender liveness here: an already committed queued
          // call can outlive its sender. Receivers may revoke their own grants.
        };
        case _ {};
      };
      let e = entry(id);
      if(isQuery(e,method)) return {outcome=#readOnly(readFrom(id,caller,method,arg));retired=[]};
      settle(id, e.instance.receive(?caller, method, arg));
    };
    public func resume(id : Continuation, reply : Reply) : Frame {
      let p = continuation(id);
      release(p);
      let step = p.resume(reply);
      cleanup(p);
      settle(id.owner, step);
    };
    /// A failed callback's transaction restores its continuation slot. The host
    /// then consumes it in a separate cleanup slice, before reporting rejection.
    public func cancel(id : Continuation) : Bool {
      let i = Nat64.toNat(id.slot);
      if (id.owner.container != container or i >= continuationCapacity) return false;
      switch (pending[i]) {
        case (?p) { if (p.identity != id) return false; cleanup(p); release(p); true };
        case null false;
      };
    };
    public func counts() : (Nat, Nat) { (live, pendingCount) };
  };
};
