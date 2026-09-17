/// Bounded round-robin ticket queue. All fields are durable data. The containing
/// actor owns this metadata; work state remains in independent actors. This is
/// an admission adapter, not an executor: explicitly await the self-message that
/// performs work. Finish the cursor and queue acknowledgement in that segment.
import Jobs "Jobs";
import Array "mo:core/Array";
import Set "mo:core/Set";
import Nat "mo:core/Nat";
module {
  public type State = {schema:Nat;capacity:Nat;ready:[Jobs.Ticket];active:?Jobs.Ticket;failed:[Jobs.Ticket]};
  public type Error = {#invalid;#full;#duplicate;#busy;#empty;#stale};
  public type Result<T> = {#ok:T;#err:Error};
  public func empty(capacity:Nat) : State {
    assert capacity>0;{schema=1;capacity;ready=[];active=null;failed=[]}
  };
  public func size(q:State) : Nat {q.ready.size()+q.failed.size()+(switch(q.active){case null 0;case(?_) 1})};
  public func valid(q:State) : Bool {
    if(q.schema!=1 or q.capacity==0 or size(q)>q.capacity) return false;
    let ids=Set.empty<Nat>();
    func add(t:Jobs.Ticket) : Bool {
      if(Set.contains(ids,Nat.compare,t.id)) return false;
      Set.add(ids,Nat.compare,t.id);true
    };
    for(t in q.ready.values()){if(not add(t)) return false};
    for(t in q.failed.values()){if(not add(t)) return false};
    switch(q.active){case null true;case(?t) add(t)}
  };
  public func offer(q:State,t:Jobs.Ticket) : Result<State> {
    if(not valid(q)) return #err(#invalid);
    for(v in q.ready.values()){if(v.id==t.id) return #err(#duplicate)};
    for(v in q.failed.values()){if(v.id==t.id) return #err(#duplicate)};
    switch(q.active){case(?v) if(v.id==t.id) return #err(#duplicate);case null {}};
    if(size(q)==q.capacity) return #err(#full);
    #ok({q with ready=Array.concat(q.ready,[t])})
  };
  public func reserve(q:State) : Result<(State,Jobs.Ticket)> {
    if(not valid(q)) return #err(#invalid);
    if(q.active!=null) return #err(#busy);
    if(q.ready.size()==0) return #err(#empty);
    let t=q.ready[0];
    #ok(({q with ready=Array.tabulate<Jobs.Ticket>(q.ready.size()-1,func(i){q.ready[i+1]});active=?t},t))
  };
  /// The work method calls this after storing its cursor, before returning. A
  /// trapping work method keeps its reservation; its caller records fail next.
  public func complete(q:State,t:Jobs.Ticket,c:Jobs.Cursor) : Result<State> {
    if(not valid(q) or not Jobs.valid(c)) return #err(#invalid);
    if(q.active!=?t or c.id!=t.id or c.generation!=t.generation or c.next<=t.next) return #err(#stale);
    #ok({q with active=null;ready=if(c.status==#ready) Array.concat(q.ready,[Jobs.ticket(c)]) else q.ready})
  };
  public func fail(q:State,t:Jobs.Ticket) : Result<State> {
    if(not valid(q)) return #err(#invalid);
    if(q.active!=?t) return #err(#stale);
    #ok({q with active=null;failed=Array.concat(q.failed,[t])})
  };
  /// Recovery never automatically repeats a failed unit. An operator/application
  /// supplies the current committed cursor after deciding retry is appropriate.
  /// Already-completed/cancelled work releases the reserved slot. New generations
  /// need explicit removal/re-admission rather than implicit replacement.
  public func recover(q:State,c:Jobs.Cursor) : Result<State> {
    if(not valid(q) or not Jobs.valid(c)) return #err(#invalid);
    var found:?Jobs.Ticket=null;
    for(t in q.failed.values()){if(t.id==c.id) found:=?t};
    let t=switch(found){case null return #err(#stale);case(?t) t};
    if(c.next<t.next or not(c.generation==t.generation or (c.status==#cancelled and c.generation==t.generation+1))) return #err(#stale);
    #ok({q with failed=Array.filter<Jobs.Ticket>(q.failed,func(v){v.id!=c.id});ready=if(c.status==#ready) Array.concat(q.ready,[Jobs.ticket(c)]) else q.ready})
  };
  /// At recovery, a persisted reservation has unknown completion status. Move it
  /// to failed, inspect the committed cursor, then call recover explicitly.
  public func interrupt(q:State) : Result<State> {
    if(not valid(q)) return #err(#invalid);
    switch(q.active){case null #ok(q);case(?t) fail(q,t)}
  };
};
