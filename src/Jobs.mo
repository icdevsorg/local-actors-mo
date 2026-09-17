/// Experimental durable ordered-job cursor. This module schedules nothing and
/// introduces no implicit await/commit. Keep the ordered identity list beside
/// this cursor; each identity continues to own its own actor* state.
///
/// Protocol: authenticate the continuation; admit its ticket BEFORE touching
/// work; execute only the admitted range without a real await; complete and
/// store the cursor in that same message segment. Then use an explicit real
/// self-message/timer for the next ticket. await* alone is not a checkpoint.
/// A trapping unit rolls back its batch, including cursor changes. Previously
/// committed batches survive. One indivisible unit must still fit hard limits.
module {
  public type Status = {#ready; #done; #cancelled};
  public type Cursor = {
    schema : Nat; id : Nat; generation : Nat; next : Nat; total : Nat; status : Status
  };
  public type Ticket = {id : Nat; generation : Nat; next : Nat};
  public type Batch = {ticket : Ticket; start : Nat; end : Nat};
  public type Error = {#invalid; #stale; #inactive};
  public type Result<T> = {#ok : T; #err : Error};

  public func valid(c : Cursor) : Bool {
    c.schema == 1 and c.next <= c.total and
    (switch(c.status) {case(#ready) c.next < c.total; case(#done) c.next == c.total; case(#cancelled) true})
  };
  /// IDs must not be reused with the same generation for a different work list.
  public func create(id : Nat, generation : Nat, total : Nat) : Cursor {
    {schema=1;id;generation;next=0;total;status=if(total==0) #done else #ready}
  };
  public func ticket(c : Cursor) : Ticket {{id=c.id;generation=c.generation;next=c.next}};
  public func admit(c : Cursor, t : Ticket, maximumUnits : Nat) : Result<Batch> {
    if(not valid(c) or maximumUnits==0) return #err(#invalid);
    if(t != ticket(c)) return #err(#stale);
    if(c.status != #ready) return #err(#inactive);
    let remaining=c.total-c.next;
    let count=if(maximumUnits<remaining) maximumUnits else remaining;
    #ok({ticket=t;start=c.next;end=c.next+count})
  };
  /// Call only after all units succeeded in the same atomic segment. This is
  /// optimistic validation, not rollback across a real await. Trap on failure
  /// if work has already mutated state; do not commit that work with an old cursor.
  public func complete(c : Cursor, b : Batch) : Result<Cursor> {
    if(not valid(c) or b.start>=b.end or b.end>c.total) return #err(#invalid);
    if(b.ticket != ticket(c) or b.start!=c.next) return #err(#stale);
    if(c.status != #ready) return #err(#inactive);
    #ok({c with next=b.end;status=if(b.end==c.total) #done else #ready})
  };
  /// Cancellation invalidates outstanding tickets; it does not undo completed
  /// units. Repeated cancellation is idempotent. Restart requires a fresh job
  /// generation/work-list contract, not resetting this cursor's next field.
  public func cancel(c : Cursor) : Result<Cursor> {
    if(not valid(c)) return #err(#invalid);
    if(c.status != #ready) return #ok(c);
    #ok({c with generation=c.generation+1;status=#cancelled})
  };
  /// Explicit new work generation after completion/cancellation. Previous actor
  /// mutations remain; this intentionally starts a new ordered work list at zero.
  /// Never use this to silently retry already committed work in the old job.
  public func restart(c : Cursor, total : Nat) : Result<Cursor> {
    if(not valid(c)) return #err(#invalid);
    if(c.status==#ready) return #err(#inactive);
    #ok(create(c.id,c.generation+1,total))
  };

};
