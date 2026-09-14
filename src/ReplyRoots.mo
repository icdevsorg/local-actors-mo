/// Internal compiler target. A pending caller continuation owns each slot.
/// T must be freshly projected immutable data; this table does not prove type
/// isolation or account for arbitrary transitive graphs. Never expose its
/// mutation methods to game code as a public actor API.
import Kernel "Kernel";
import Nat64 "mo:core/Nat64";
import VarArray "mo:core/VarArray";
import Runtime "mo:core/Runtime";
module {
  public type Token = {slot : Nat64; generation : Nat64};
  type Entry<T> = {source : Kernel.Ref; target : Kernel.Ref; var value : ?T};
  public class Replies<T>(capacity : Nat) {
    let values = VarArray.repeat<?Entry<T>>(null,capacity);
    let generations = VarArray.repeat<Nat64>(1,capacity);
    let next = VarArray.tabulate<Nat>(capacity,func i {i+1});
    var free = 0;
    var live = 0;
    func lookup(token : Token) : ?Entry<T> {
      let i = Nat64.toNat(token.slot);
      assert i < capacity;
      if (generations[i] != token.generation) return null;
      values[i]
    };
    public func reserve(source : Kernel.Ref,target : Kernel.Ref) : Token {
      assert source.container == target.container and free < capacity;
      let i=free; free:=next[i]; live+=1;
      values[i]:=?{source;target;var value=null};
      {slot=Nat64.fromNat(i);generation=generations[i]}
    };
    /// Authenticated dispatch context is captured by the generated callee adapter.
    /// An orphaned queued request still runs, but cannot revive a canceled reply.
    public func publish(context : Kernel.Context,token : Token,value : T) : Bool {
      let ?entry=lookup(token) else return false;
      assert context.self == entry.target and context.caller == #local(entry.source);
      switch (entry.value) {case null {};case _ Runtime.trap("reply already published")};
      entry.value:=?value;
      true
    };
    /// Generated resume reads before managed cleanup; a trap restores both.
    public func read(source : Kernel.Ref,target : Kernel.Ref,token : Token) : T {
      let ?entry=lookup(token) else Runtime.trap("reply root missing");
      assert source == entry.source and target == entry.target;
      let ?value=entry.value else Runtime.trap("reply not published");
      value
    };
    public func drop(source : Kernel.Ref,target : Kernel.Ref,token : Token) : Bool {
      let ?entry=lookup(token) else return false;
      assert source == entry.source and target == entry.target;
      let i=Nat64.toNat(token.slot);
      values[i]:=null;live-=1;
      if (generations[i] < 18_446_744_073_709_551_615) {
        generations[i]+=1;next[i]:=free;free:=i
      };
      true
    };
    public func count() : Nat {live};
  };
}
