/// Internal typed request storage. T must be explicitly projected into immutable
/// data by the compiler/adapter. This generic class is not a language isolation
/// proof. The host owns each committed reserved-method request until dispatch.
import Kernel "Kernel";
import Blob "mo:core/Blob";
import VarArray "mo:core/VarArray";
import Nat8 "mo:core/Nat8";
import Nat64 "mo:core/Nat64";
import Runtime "mo:core/Runtime";
module {
  public let method : Text = Kernel.rootedRequestMethod;
  type Id = {slot : Nat; generation : Nat64};
  func encode(id : Id) : Blob {
    let bytes = VarArray.repeat<Nat8>(0,16);
    var a = Nat64.fromNat(id.slot); var b = id.generation;
    for (i in bytes.keys()) {
      if (i < 8) {bytes[i] := Nat8.fromNat(Nat64.toNat(a % 256)); a /= 256}
      else {bytes[i] := Nat8.fromNat(Nat64.toNat(b % 256)); b /= 256}
    };
    Blob.fromVarArray(bytes)
  };
  func decode(token : Blob) : Id {
    assert token.size() == 16;
    let bytes = Blob.toArray(token);
    var a : Nat64 = 0; var b : Nat64 = 0; var i = 8;
    while (i > 0) {i -= 1; a := a * 256 + Nat64.fromNat(Nat8.toNat(bytes[i])); b := b * 256 + Nat64.fromNat(Nat8.toNat(bytes[i+8]))};
    {slot = Nat64.toNat(a); generation = b}
  };
  type Entry<T> = {source : Kernel.Ref; target : Kernel.Ref; value : T; var published : Bool};
  public class Requests<T>(capacity : Nat) {
    let values = VarArray.repeat<?Entry<T>>(null,capacity);
    let generations = VarArray.repeat<Nat64>(1,capacity);
    let next = VarArray.tabulate<Nat>(capacity,func i {i+1});
    var free = 0; var live = 0;
    func release(i : Nat) {
      values[i] := null; live -= 1;
      if (generations[i] < 18_446_744_073_709_551_615) {
        generations[i] += 1; next[i] := free; free := i
      }
    };
    func allocate(source : Kernel.Ref,target : Kernel.Ref,value : T) : Nat {
      assert source.container == target.container and free < capacity;
      let i=free;free:=next[i];live+=1;
      values[i]:=?{source;target;value;var published=false};
      i
    };
    public func request(source : Kernel.Ref,target : Kernel.Ref,value : T) : Kernel.Request {
      let i=allocate(source,target,value);
      #local({target;method;arg=encode({slot=i;generation=generations[i]})})
    };
    public func requestScalar(source : Kernel.Ref,target : Kernel.Ref,value : T) : Kernel.Request {
      let i=allocate(source,target,value);
      #rooted({target;slot=Nat64.fromNat(i);generation=generations[i]})
    };
    // Called by Kernel.park with the actual executing owner, before commit.
    // Claim exactly once so another local actor cannot forge or duplicate a token.
    public func publish(source : Kernel.Ref, target : Kernel.Ref, token : Blob) {
      let id=decode(token);
      publishScalar(source,target,Nat64.fromNat(id.slot),id.generation)
    };
    public func publishScalar(source : Kernel.Ref, target : Kernel.Ref, slot : Nat64, generation : Nat64) {
      let i=Nat64.toNat(slot);
      assert i < capacity and generations[i] == generation;
      let ?value = values[i] else Runtime.trap("request root missing");
      assert source == value.source and target == value.target and not value.published;
      value.published := true
    };
    public func take(context : Kernel.Context, token : Blob) : T {
      let id=decode(token);
      takeScalar(context,Nat64.fromNat(id.slot),id.generation)
    };
    public func takeScalar(context : Kernel.Context, slot : Nat64, generation : Nat64) : T {
      let i=Nat64.toNat(slot);
      assert i < capacity and generations[i] == generation;
      let ?value = values[i] else Runtime.trap("request root missing");
      assert value.published and context.self == value.target and context.caller == #local(value.source);
      release(i);
      value.value
    };
    // Idempotent for an already-consumed generation, never for the wrong owner.
    // Called only by the host cleanup ABI, inside a journaled local slice.
    public func drop(source : Kernel.Ref, target : Kernel.Ref, token : Blob) : Bool {
      let id=decode(token);
      dropScalar(source,target,Nat64.fromNat(id.slot),id.generation)
    };
    public func dropScalar(source : Kernel.Ref, target : Kernel.Ref, slot : Nat64, generation : Nat64) : Bool {
      let i=Nat64.toNat(slot);
      assert i < capacity;
      if (generations[i] != generation) return false;
      let ?value = values[i] else return false;
      assert source == value.source and target == value.target;
      release(i); true
    };
    public func count() : Nat {live};
  };
}
