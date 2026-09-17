/// Explicit membership/schema binding for Jobs cursors. Contains identities and
/// progress only. Restore worker state and verify handle liveness separately.
import Jobs "Jobs";
import LocalId "LocalId";
import Principal "mo:core/Principal";
import Set "mo:core/Set";
module {
  public type Snapshot = {schema:Nat;applicationSchema:Nat;cursor:Jobs.Cursor;members:[LocalId.Address]};
  func compare(a:LocalId.Address,b:LocalId.Address) : {#less;#equal;#greater} {
    switch(Principal.compare(a.owner,b.owner)){case(#equal) Principal.compare(a.id,b.id);case(order) order}
  };
  public func valid(s:Snapshot) : Bool {
    if(s.schema!=1 or s.applicationSchema==0 or not Jobs.valid(s.cursor) or s.members.size()!=s.cursor.total) return false;
    let seen=Set.empty<LocalId.Address>();
    for(member in s.members.values()) {
      if(LocalId.decode(member.id)==null or Set.contains(seen,compare,member)) return false;
      Set.add(seen,compare,member)
    };true
  };
  public func capture(cursor:Jobs.Cursor,applicationSchema:Nat,members:[LocalId.Address]) : Jobs.Result<Snapshot> {
    let s={schema=1;applicationSchema;cursor;members};
    if(valid(s)) #ok(s) else #err(#invalid)
  };
  /// Expected membership comes from the independently restored application world.
  /// Exact order, owner and generation-bearing identity must agree. No best-effort
  /// index remapping: that can silently repeat or skip already committed work.
  public func restore(s:Snapshot,applicationSchema:Nat,members:[LocalId.Address]) : Jobs.Result<Jobs.Cursor> {
    if(not valid(s) or applicationSchema==0) return #err(#invalid);
    if(s.applicationSchema!=applicationSchema or s.members!=members) return #err(#stale);
    #ok(s.cursor)
  };
};
