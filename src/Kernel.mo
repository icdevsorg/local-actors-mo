/// Experimental compiler target. Actor state remains inside each Actor object's
/// private closure. These tables contain roots, identities and continuations.
/// The actor* frontend will eventually generate receive/resume code; the initial
/// fixture supplies it explicitly. This is not yet a public language feature.
import LocalId "LocalId";
import RegistryImage "RegistryImage";
import Nat64 "mo:core/Nat64";
import Runtime "mo:core/Runtime";
import VarArray "mo:core/VarArray";
import Array "mo:core/Array";
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
  /// `nameKey`/`signatureKey` (M7/O1) are COMPILER CONSTANTS: the table entry and the call site are
  /// hashed from the same texts at compile time, so the kernel never hashes and resolution compares
  /// integers instead of a name and a ~60-character signature. The texts stay for diagnostics and for
  /// the upgrade image's method contracts, and `resolveComputation` still resolves by them.
  public type ComputationMethod = { name : Text; signature : Text; nameKey : Nat32; signatureKey : Nat64; value : Any };
  /// T81: an actor* class's `system func preupgrade/postupgrade`, rebuilt with its methods.
  public type ComputationStorage = { methods : [ComputationMethod]; postupgrade : ?(() -> ()); preupgrade : ?(() -> ()) };
  /// Trusted ingress provenance. Local provenance is derived from the executing
  /// frame, never supplied by a bound method or its creator.
  /// M7/O2: `#message` is the container's current message caller, resolved LAZILY (through the
  /// reader installed by the generated container) only when a body reads its context. Measured:
  /// the eager `msg_caller` at every call site was ~7.1k instructions and ~97 B per call, paid
  /// even when the kernel discarded it for a nested frame.
  public type ComputationIngress = { #host; #external : Principal; #message };
  /// Compiler-private lease for one independently scheduled ordinary future.
  public type ComputationTask = { start : () -> (); finish : () -> (); settle : () -> () };
  type TaskPhase = { #queued; #running : Nat; #finished; #settled };
  type Origin = { #known : Caller; #message };
  /// M7/O2b: the parked stack of a suspended invocation, the only place frames are ever copied.
  type SavedFrames = { slots : [Nat64]; generations : [Nat64]; tickets : [Nat]; depth : Nat; root : Origin };
  type Receiver = { receive : (?Caller, Text, Blob) -> Step; root : ?((Caller,Nat64,Nat64) -> Step); computations : ?ComputationStorage };
  type Entry = { identity : Ref; instance : Receiver; var queries : ?[Text]; var pending : ?Nat };
  type Pending = { identity : Continuation; resume : Reply -> Step; cleanup : ?(() -> ()); var prev : ?Nat; var next : ?Nat };

  public class Kernel(container : Principal, capacity : Nat, continuationCapacity : Nat) {
    /// M8/T71: the outward spelling of an identity (`Actor.id`), for the compiler-generated local
    /// closure of an exported method, which names itself to the container's façade
    /// (`World.K_m(id, …)`). Data only; the registry never consults it.
    public func identityPrincipal(id : Ref) : Principal { LocalId.encode({slot = id.slot; generation = id.generation}) };
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
    // Allocated only when compiler-owned persistent instances are registered.
    var persistentRows : ?[var ?RegistryImage.Payload<Any>] = null;
    var restoringRegistry = false;
    let pending = VarArray.repeat<?Pending>(null, continuationCapacity);
    let continuationGenerations = VarArray.repeat<Nat64>(1, continuationCapacity);
    let continuationFree = VarArray.tabulate<Nat>(continuationCapacity, func i { i + 1 });
    var continuationHead = 0;
    var pendingCount = 0;
    var retired = List.empty<Ref>();
    var reading = false;
    var computationTicket = 0;
    var computationDepth = 0;
    /// M7/O3b: a callback's `restore()` no longer re-pushes the parked frames eagerly. It records
    /// them here; the first operation that needs the stack materializes them, and every MESSAGE
    /// ENTRY discards them instead. Why: the suspension's `finally restore` also runs on the
    /// trap-CLEANUP chain (moc's finally semantics), where nothing will ever pop what it pushes --
    /// the old per-call `finally leave` used to, and its removal left frames behind after every
    /// trap in a callback (S31/S34/S41 regressions). A pending restore reaching a message entry can
    /// only come from such a chain, so discarding it there is exact; the strict "empty stack"
    /// checks at those entries keep guarding REAL frames.
    var pendingRestore : ?SavedFrames = null;
    func materialize() {
      switch pendingRestore {
        case (?saved) {
          pendingRestore := null;
          var i = 0;
          while (i < saved.depth) {
            frameSlot[i] := saved.slots[i]; frameGeneration[i] := saved.generations[i]; frameTicket[i] := saved.tickets[i];
            i += 1
          };
          rootOrigin := saved.root;
          computationDepth := saved.depth
        };
        case null {}
      }
    };
    func discardPending() { pendingRestore := null };
    // Parked invocations retain retirement ownership but are not ambient callers.
    let suspendedComputations = VarArray.repeat<Nat>(0, capacity);
    // T62: a scheduled timer job captured this actor; until it fires (one-shot) or is
    // cancelled (recurring) the actor is as busy as with a queued task. Heap state, so a
    // trapped segment's scheduling rolls back with the timer node itself.
    let pendingTimers = VarArray.repeat<Nat>(0, capacity);
    var timerHolds : [(Nat, Nat)] = [];
    var timerBridge : ?{set : (Nat64, Bool, () -> async ()) -> Nat; cancel : Nat -> ()} = null;
    // T62b: cycles are attached to the CONTAINER's next outgoing call; no hold is involved,
    // and the stash (`@cycles`) is heap state, so it rolls back with the segment.
    func releaseTimerHold(id : Nat) {
      var slot : ?Nat = null;
      timerHolds := Array.filter<(Nat, Nat)>(timerHolds, func h { if (h.0 == id) { slot := ?h.1; false } else true });
      switch slot { case (?s) { assert pendingTimers[s] > 0; pendingTimers[s] -= 1 }; case null {} }
    };
    /// Installed once by generated container code, never by an author. Absent bridge means
    /// timers are unavailable (hand-built kernels in fixtures), and the capability traps.
    public func installTimerBridge(set : (Nat64, Bool, () -> async ()) -> Nat, cancel : Nat -> ()) {
      timerBridge := ?{set; cancel}
    };
    // Creation retains the owner until the independently scheduled body enters.
    let queuedComputations = VarArray.repeat<Nat>(0, capacity);
    // Explicit bound for inline recursion, independent of display/actor count.
    let computationDepthLimit = 128;
    /// M7/O2b: ALLOCATION-FREE frame stack. It was a linked `?(ticket, {self; origin}, parent)`:
    /// an option, a tuple and a record allocated on EVERY enter (~72 B of the ~709 B one actor*
    /// call allocated, and under private GC the collector's share is proportional to bytes). The
    /// depth is bounded by `computationDepthLimit` anyway, so the stack is three pre-allocated
    /// arrays indexed by depth, holding SCALARS: `entry()` has already proved every id's container
    /// is this container, so a frame is just its slot and generation. A `Ref` record is rebuilt
    /// only when a body actually asks (`computationContext`), and a nested frame's caller is
    /// derived from the frame below it, so only the ROOT frame's origin is stored.
    let frameSlot = VarArray.repeat<Nat64>(0, computationDepthLimit);
    let frameGeneration = VarArray.repeat<Nat64>(0, computationDepthLimit);
    let frameTicket = VarArray.repeat<Nat>(0, computationDepthLimit);
    var rootOrigin : Origin = #known(#host);
    func selfAt(level : Nat) : Ref = { container; slot = frameSlot[level]; generation = frameGeneration[level] };
    func callerAt(level : Nat) : Caller = if (level == 0) callerOf(rootOrigin) else #local(selfAt(level - 1));
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
      if (restoringRegistry) Runtime.trap("actor registry restoration is not complete");
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
      if (restoringRegistry) Runtime.trap("actor registry restoration is not complete");
      if (reading) Runtime.trap("actor creation is unavailable in a read-only call");
      if (freeHead >= capacity) Runtime.trap("local actor capacity exceeded");
      let i = freeHead;
      freeHead := free[i];
      let identity = { container; slot = Nat64.fromNat(i); generation = generations[i] };
      // T80: the instance under construction owns the timers its constructor schedules.
      let outer = constructing; constructing := ?identity;
      let instance = make(identity);
      constructing := outer;
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
    func computationReceiver(storage : ComputationStorage) : Receiver {
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
      {computations=?storage;root=null;
        receive=func(_caller : ?Caller,_method : Text,_arg : Blob) : Step {
          Runtime.trap("computation actor requires inline dispatch")
        }
      }
    };
    public func spawnComputation(make : Ref -> ComputationStorage) : Ref {
      allocate(func id {computationReceiver(make(id))})
    };

    /// Trusted compiler ABI. The typed class envelope owns schema/data casts.
    public func spawnPersistentComputation(schema : Text, make : Ref -> (ComputationStorage,Any)) : Ref {
      if(schema=="") Runtime.trap("missing actor registry class schema");
      allocate(func id {
        let (storage,data)=make(id);
        let receiver=computationReceiver(storage);
        let rows=switch(persistentRows){case(?rows)rows;case null {
          let rows=VarArray.repeat<?RegistryImage.Payload<Any>>(null,capacity);
          persistentRows:=?rows;rows
        }};
        rows[Nat64.toNat(id.slot)]:=?{schema;data;methods=methodContracts(storage)};receiver
      })
    };
    func methodContracts(storage:ComputationStorage):[RegistryImage.Method] {
      Array.map<ComputationMethod,RegistryImage.Method>(storage.methods,func method {{name=method.name;signature=method.signature}})
    };
    func registryQuiescent() {
      discardPending();
      if(restoringRegistry or reading or pendingCount!=0 or computationDepth!=0)
        Runtime.trap("actor registry persistence requires a quiescent container");
      for(i in suspendedComputations.keys()) {
        if(suspendedComputations[i]!=0 or queuedComputations[i]!=0 or pendingTimers[i]!=0)
          Runtime.trap("actor registry persistence has pending computations")
      }
    };
    /// A non-mutating upgrade projection. Explicitly transient instances are
    /// discarded and their generations burned/advanced in the image, not live RAM.
    /// T81: run each live instance's hook as its own task, in slot order; a trap aborts the upgrade.
    func runHooks(select : ComputationStorage -> ?(() -> ())) {
      var i=0;
      while(i < capacity) {
        switch(actors[i]) {
          case null {};
          case(?actorEntry) switch(actorEntry.instance.computations) {
            case null {};
            case(?storage) switch(select(storage)) {
              case null {};
              case(?hook) { let ticket=enterComputation(actorEntry.identity,#host); hook(); leaveComputation(ticket) }
            }
          }
        };
        i+=1
      }
    };
    public func snapshotComputationRegistry() : RegistryImage.Image<Any> {
      runHooks(func s = s.preupgrade);
      registryQuiescent();
      let gs=VarArray.tabulate<Nat64>(capacity,func i {generations[i]});
      let rs=VarArray.tabulate<Nat64>(capacity,func i {retiredGenerations[i]});
      let links=VarArray.tabulate<Nat>(capacity,func i {free[i]});
      var head=freeHead;
      let rows=VarArray.repeat<?RegistryImage.Payload<Any>>(null,capacity);
      var i=0;
      while(i < capacity) {
        switch(actors[i]) {
          case null {};
          case(?actorEntry) {
            let ?storage=actorEntry.instance.computations else Runtime.trap("queued actor registry upgrade is unsupported");
            let payload=switch(persistentRows){case(?stored)stored[i];case null null};
            switch(payload) {
              case(?value) rows[i]:=?{value with methods=methodContracts(storage)};
              case null {
                rs[i]:=gs[i];
                if(gs[i]!=RegistryImage.maxGeneration){gs[i]+=1;links[i]:=head;head:=i}
              }
            }
          }
        };
        i+=1
      };
      let image={version=RegistryImage.version;owner=container;generations=VarArray.toArray(gs);retired=VarArray.toArray(rs);free=VarArray.toArray(links);head;rows=VarArray.toArray(rows)};
      switch(RegistryImage.validate(image,container,capacity)){case(?why)Runtime.trap(why);case null {}};
      image
    };
    /// Build the candidate privately; publish only after all schemas bind.
    /// Rebinding may create methods, but cannot call or mutate this registry.
    public func restoreComputationRegistry(image : RegistryImage.Image<Any>,
      rebind : (Ref,Text,Any) -> (ComputationStorage,Text,Any)) {
      registryQuiescent();
      if(live!=0) Runtime.trap("actor registry restoration requires a fresh registry");
      for(i in generations.keys()) if(generations[i]!=1 or retiredGenerations[i]!=0)
        Runtime.trap("actor registry restoration requires a fresh registry");
      switch(RegistryImage.validate(image,container,capacity)){case(?why)Runtime.trap(why);case null {}};
      restoringRegistry:=true;
      let candidate=VarArray.repeat<?Entry>(null,capacity);
      let newRows=VarArray.repeat<?RegistryImage.Payload<Any>>(null,capacity);
      var restoredLive=0;
      for(i in image.rows.keys()) switch(image.rows[i]) {
        case null {};
        case(?payload) {
          let identity={container;slot=Nat64.fromNat(i);generation=image.generations[i]};
          let (storage,schema,data)=rebind(identity,payload.schema,payload.data);
          // T81: a migrated row is stored under its NEW schema and data; its method contracts are
          // the new class's (a migration may change them, as an actor's migration may).
          newRows[i]:=?{schema;data;methods=methodContracts(storage)};
          // Existing references retain their method contracts. New methods may
          // be added; removing or changing a saved method requires migration.
          if(schema==payload.schema) for(previous in payload.methods.vals()) {
            var compatible=false;
            for(current in storage.methods.vals()) {
              if(current.name==previous.name and current.signature==previous.signature) compatible:=true
            };
            if(not compatible) Runtime.trap("incompatible persistent actor method contract: " # previous.name)
          };
          let instance=computationReceiver(storage);
          candidate[i]:=?{identity;instance;var queries=null;var pending=null};restoredLive+=1
        }
      };
      for(i in generations.keys()) {
        generations[i]:=image.generations[i];retiredGenerations[i]:=image.retired[i];
        free[i]:=image.free[i];actors[i]:=candidate[i]
      };
      persistentRows:=?newRows;
      freeHead:=image.head;live:=restoredLive;restoringRegistry:=false;
      runHooks(func s = s.postupgrade)
    };
    /// Call from INSIDE the deferred computation, on every execution. Resolving
    /// while building/caching a bound computation would bypass retirement.
    /// No method invocation, message, continuation allocation or commit occurs.
    /// The path generated code takes. Measured: the text scan below was ~1,000 instructions per
    /// call and ~1,700 with a record-typed signature -- 5 % of an actor* call.
    public func resolveComputationKey(id : Ref, nameKey : Nat32, signatureKey : Nat64) : Any {
      let e = entry(id);
      let ?storage = e.instance.computations else Runtime.trap("actor lacks computation storage");
      for (candidate in storage.methods.vals()) {
        if (candidate.nameKey == nameKey) {
          if (candidate.signatureKey != signatureKey) Runtime.trap("computation method signature mismatch");
          return candidate.value
        }
      };
      Runtime.trap("unknown computation method")
    };
    /// Resolution BY TEXT, for hand-written kernel witnesses (S20/S21) and any caller that holds the
    /// names rather than the compiler's constants. Same entry checks, same traps, same scan shape.
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
    /// error propagation. Suspension detaches this stack through suspendComputation below.
    /// These operations never perform a message or commit themselves.
    /// Set only by compiler-generated ordinary query ingress. Query execution
    /// discards the complete container heap, including this bit, on every exit.
    public func beginComputationQuery() {
      discardPending();
      if (reading or computationDepth != 0) Runtime.trap("invalid computation query entry");
      reading := true
    };
    public func enterQueryComputation(id : Ref, ingress : ComputationIngress) : Nat {
      if (not reading) Runtime.trap("actor* query requires an enclosing query");
      enterComputation(id, ingress)
    };
    /// A ROOT call site (container code, frame depth 0): a message entry as far as the stack is
    /// concerned, so a pending restore left by a trap-cleanup chain is discarded first.
    public func enterRootComputation(id : Ref, ingress : ComputationIngress) : Nat {
      discardPending();
      enterComputation(id, ingress)
    };
    public func enterComputation(id : Ref, ingress : ComputationIngress) : Nat {
      materialize();
      let e = entry(id);
      switch (e.instance.computations) {
        case null Runtime.trap("actor lacks computation storage");
        case _ {};
      };
      // A depth or receiver ID alone would allow a stale exit token to pop a
      // later frame, particularly during A -> B -> A reentry. Never reuse a
      // ticket within a committed heap history. Trap rollback rolls back both.
      if (computationDepth >= computationDepthLimit) Runtime.trap("local computation depth limit exceeded");
      // Only a ROOT frame carries an ingress; a nested frame's caller is the frame below it.
      if (computationDepth == 0) rootOrigin := (switch ingress {
        case (#host) #known(#host);
        case (#external principal) #known(#external(principal));
        case (#message) #message;
      });
      computationTicket += 1;
      frameSlot[computationDepth] := id.slot;
      frameGeneration[computationDepth] := id.generation;
      frameTicket[computationDepth] := computationTicket;
      computationDepth += 1;
      computationTicket
    };
    /// Compiler-only continuation capability. Evaluate the future operand first,
    /// then park the complete logical stack. The returned restoration must run
    /// before success, rejection AND trap cleanup. Callback rollback restores
    /// this closure's unconsumed state, allowing cleanup to restore and unwind
    /// the original invocation against the latest committed heap.
    ///
    /// No world state is captured here, only immutable frame/context metadata.
    public func suspendComputation() : () -> () {
      materialize();
      let depth = computationDepth;
      var level = 0;
      while (level < depth) {
        // A retired invocation may unwind, but cannot acquire a new suspension.
        ignore entry(selfAt(level));
        level += 1
      };
      level := 0;
      while (level < depth) {
        suspendedComputations[Nat64.toNat(frameSlot[level])] += 1;
        level += 1
      };
      // The one place frames are copied: a suspension parks the whole stack off the arrays.
      let saved : SavedFrames = {
        slots = Array.tabulate<Nat64>(depth, func i = frameSlot[i]);
        generations = Array.tabulate<Nat64>(depth, func i = frameGeneration[i]);
        tickets = Array.tabulate<Nat>(depth, func i = frameTicket[i]);
        depth; root = rootOrigin
      };
      computationDepth := 0;
      var consumed = false;
      func () {
        if (consumed) Runtime.trap("computation suspension already restored");
        discardPending();
        if (computationDepth != 0) Runtime.trap("computation restoration requires an empty stack");
        var back = 0;
        while (back < saved.depth) {
          ignore entry({ container; slot = saved.slots[back]; generation = saved.generations[back] });
          let slot = Nat64.toNat(saved.slots[back]);
          assert suspendedComputations[slot] > 0;
          suspendedComputations[slot] -= 1;
          back += 1
        };
        consumed := true;
        pendingRestore := ?saved
      }
    };
    /// Prepare in the creating segment, before staging the ordinary async send.
    /// Capture ONLY the immediate owner, never a creator's stack/exit ticket.
    /// All phase/count changes are heap state and roll back with their segment.
    ///
    /// The compiler must settle on send-initiation failure and ordinary future
    /// settlement, even if the future is ignored. An initial body trap restores
    /// #queued; its rejection callback releases that hold. A running/suspended
    /// body must finish through ordinary cleanup before settlement can succeed.
    /// This ABI alone does not admit private source async bodies.
    public func prepareComputationTask() : ComputationTask {
      materialize();
      if (computationDepth == 0) return { start = func () {}; finish = func () {}; settle = func () {} };
      let owner = selfAt(computationDepth - 1);
      ignore entry(owner);
      let slot = Nat64.toNat(owner.slot);
      queuedComputations[slot] += 1;
      var phase : TaskPhase = #queued;
      {
        start = func () {
          switch phase { case (#queued) {}; case _ Runtime.trap("computation task already started or settled") };
          discardPending();
          if (computationDepth != 0) Runtime.trap("computation task requires an empty stack");
          let ticket = enterComputation(owner, #host);
          // This is a new invocation caused by the owning actor, not a replay
          // of the external caller that originally entered its creator.
          rootOrigin := #known(#local(owner));
          assert queuedComputations[slot] > 0;
          queuedComputations[slot] -= 1;
          phase := #running(ticket)
        };
        finish = func () {
          let #running(ticket) = phase else Runtime.trap("computation task is not running");
          // The task frame is a root: nested call sites inside the body carry no guard (O3b), so
          // an error that left the body uncaught may have left frames above it. Abandon them too.
          abandonComputation(ticket);
          phase := #finished
        };
        settle = func () {
          switch phase {
            case (#queued) {
              ignore entry(owner);
              assert queuedComputations[slot] > 0;
              queuedComputations[slot] -= 1
            };
            case (#running _) Runtime.trap("computation task cleanup is incomplete");
            case (#finished) {};
            case (#settled) return;
          };
          // Finished owners may already have retired/reused their slot. Never
          // inspect or decrement a replacement's ownership on late settlement.
          phase := #settled
        }
      }
    };
    public func computationContext() : Context {
      materialize();
      if (computationDepth == 0) Runtime.trap("no executing computation actor");
      { self = selfAt(computationDepth - 1); caller = callerAt(computationDepth - 1) }
    };
    /// Explicit source self-retirement authority, tied to this invocation ticket.
    /// It cannot retire a sibling or be saved and reused by a later invocation.
    /// T62c: the capabilities an actor* receives while it is being CONSTRUCTED
    /// (`shared({setTimer}) actor* class …`). Same record as a method's source context so
    /// one pattern type serves both; `retire` is meaningless here and traps. The owner's slot
    /// is reserved but not yet registered, so liveness is not checked at scheduling time --
    /// a constructor trap rolls the hold back with the registration.
    public func constructionContext(self : Ref) : {self : Ref; caller : Caller; retire : () -> ()} {
      materialize();
      let caller : Caller = if (computationDepth == 0) #host else #local(selfAt(computationDepth - 1));
      {self; caller; retire = func () { Runtime.trap("retirement is unavailable during construction") }}
    };
    var constructing : ?Ref = null;
    /// T80: the system pattern. `Timer.setTimer<system>` inside an actor* reaches the prelude
    /// `@setTimer` through this bridge (the factory isolation rebinds the name): the owner is the
    /// active frame's actor, or the instance under construction. The job runs as the owner's own
    /// task with caller #local(owner) and holds retirement, exactly as the retired capability did.
    public func frameSetTimer(delayNanos : Nat64, recurring : Bool, job : () -> async ()) : Nat {
      materialize();
      if (computationDepth > 0) return capabilitiesFor(selfAt(computationDepth - 1), true).setTimer(delayNanos, recurring, job);
      switch constructing {
        case (?id) capabilitiesFor(id, false).setTimer(delayNanos, recurring, job);
        case null Runtime.trap("actor* timers require an executing actor* frame");
      }
    };
    public func frameCancelTimer(id : Nat) {
      let ?bridge = timerBridge else Runtime.trap("actor* timers are unavailable in this container");
      bridge.cancel(id);
      releaseTimerHold(id)
    };
    /// The author-only capabilities, for a live method invocation (`live`: the owner must be
    /// registered) or for a constructor (`live = false`, slot reserved, not yet registered).
    func capabilitiesFor(owner : Ref, live : Bool) : {setTimer : (Nat64, Bool, () -> async ()) -> Nat; cancelTimer : Nat -> ()} {
      {setTimer=func (delayNanos : Nat64, recurring : Bool, job : () -> async ()) : Nat {
        let ?bridge = timerBridge else Runtime.trap("actor* timers are unavailable in this container");
        if (reading) Runtime.trap("actor* timers are unavailable in a read-only call");
        if (live) ignore entry(owner);
        let slot = Nat64.toNat(owner.slot);
        var id = 0;
        // Fired by the container's timer helper as an ordinary self-message with an empty
        // computation stack. Push the owner's frame so the job -- an S35 private task created
        // inside the owner -- captures the owner and starts with caller #local(owner).
        let fire = func () : async () {
          if (not recurring) releaseTimerHold(id);
          discardPending();
          if (computationDepth != 0) Runtime.trap("timer job requires an empty computation stack");
          let ticket = enterComputation(owner, #host);
          ignore job();
          leaveComputation(ticket)
        };
        id := bridge.set(delayNanos, recurring, fire);
        pendingTimers[slot] += 1;
        timerHolds := Array.concat(timerHolds, [(id, slot)]);
        id
       };
       cancelTimer=func (id : Nat) {
        let ?bridge = timerBridge else Runtime.trap("actor* timers are unavailable in this container");
        bridge.cancel(id);
        releaseTimerHold(id)
       }}
    };
    public func computationRetirementContext() : {self : Ref; caller : Caller; retire : () -> ()} {
      materialize();
      if (computationDepth == 0) Runtime.trap("no executing computation actor");
      let ticket = frameTicket[computationDepth - 1];
      let self = selfAt(computationDepth - 1);
      {self; caller=callerAt(computationDepth - 1);
       retire=func () {
        materialize();
        if (computationDepth == 0) Runtime.trap("no executing computation actor");
        // `top` counts DOWN from the depth, so the subtraction is on a value the guard above has
        // already proved positive; spelled with an explicit Nat annotation to keep M0155 quiet in
        // the bundled runtime (it would print on every user build).
        let top : Nat = computationDepth - 1 : Nat;
        if(frameTicket[top] != ticket or frameSlot[top] != self.slot or frameGeneration[top] != self.generation)
          Runtime.trap("retirement requires its current computation invocation");
        var level = 0;
        while (level < top) {
          if (frameSlot[level] == self.slot and frameGeneration[level] == self.generation)
            Runtime.trap("local actor retirement is busy");
          level += 1
        };
        retire(self)
       }}
    };
    var messageCaller : ?(() -> Principal) = null;
    /// Installed once by the generated container: how a `#message` frame learns its caller.
    public func installMessageCaller(read : () -> Principal) { messageCaller := ?read };
    func callerOf(origin : Origin) : Caller = switch origin {
      case (#known caller) caller;
      case (#message) {
        let ?read = messageCaller else Runtime.trap("message caller is unavailable in this container");
        #external(read())
      }
    };
    /// M7/O3b: frame recovery without a per-call `finally`. Measured (actor-pgc rung): the
    /// try/finally that popped the frame on every path cost ~7.9k instructions and ~240 B per
    /// call -- more than the callee's own work. Now a caught error is unwound where control
    /// resumes: every `catch`/`finally` handler lowered inside the container unwinds to the mark
    /// it took at `try` entry, and a call site's guard abandons its own invocation when an error
    /// passes through it. Frames strictly above a mark can only belong to invocations that ended
    /// by an error (a normal return leaves in order), so popping them is exact.
    public func markComputation() : Nat { materialize(); if (computationDepth == 0) 0 else frameTicket[computationDepth - 1] };
    public func unwindComputation(mark : Nat) {
      materialize();
      while (computationDepth > 0 and frameTicket[computationDepth - 1] > mark) computationDepth -= 1
    };
    /// Abandon the invocation entered with `ticket` and whatever it left behind. Tolerant of an
    /// already-unwound frame (a handler inside the invocation may have unwound first).
    public func abandonComputation(ticket : Nat) {
      materialize();
      while (computationDepth > 0 and frameTicket[computationDepth - 1] >= ticket) computationDepth -= 1
    };
    public func leaveComputation(ticket : Nat) {
      materialize();
      if (computationDepth == 0) Runtime.trap("no executing computation actor");
      if (ticket != frameTicket[computationDepth - 1]) Runtime.trap("computation frame exit out of order");
      computationDepth -= 1
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
      if (suspendedComputations[Nat64.toNat(id.slot)] != 0 or queuedComputations[Nat64.toNat(id.slot)] != 0) Runtime.trap("local actor retirement is busy");
      if (pendingTimers[Nat64.toNat(id.slot)] != 0) Runtime.trap("local actor retirement is busy: a scheduled timer job still captures it");
      label clean loop {
        switch (e.pending) {
          case null break clean;
          case (?i) { switch (pending[i]) { case (?p) {cleanup(p); release(p)}; case null Runtime.trap("broken actor continuation list") } };
        };
      };
      let i = Nat64.toNat(id.slot);
      retiredGenerations[i] := id.generation;
      actors[i] := null;
      switch(persistentRows){case(?rows) rows[i]:=null;case null {}};
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
