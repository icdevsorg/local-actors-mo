/// Data-only allocation metadata for compiler-owned actor* upgrade envelopes.
/// Payload D is supplied by a typed compiler schema; this module never casts it.
import Nat64 "mo:core/Nat64";
import VarArray "mo:core/VarArray";
module {
  public type Method = {name : Text; signature : Text};
  public type Payload<D> = {schema : Text; data : D; methods : [Method]};
  public let version : Nat = 2;
  public type Image<D> = {
    version : Nat; owner : Principal;
    generations : [Nat64]; retired : [Nat64]; free : [Nat]; head : Nat;
    rows : [?Payload<D>]
  };
  public let maxGeneration : Nat64 = 18_446_744_073_709_551_615;
  /// Full validation precedes method reconstruction or registry mutation.
  public func validate<D>(image : Image<D>, owner : Principal, capacity : Nat) : ?Text {
    if(image.version!=version) return ?"unsupported actor registry image version";
    if(image.owner!=owner) return ?"actor registry image owner mismatch";
    if(image.generations.size()!=capacity or image.retired.size()!=capacity or image.free.size()!=capacity or image.rows.size()!=capacity)
      return ?"actor registry image capacity mismatch";
    if(image.head > capacity) return ?"actor registry free head out of range";
    let seen=VarArray.repeat<Bool>(false,capacity);
    var cursor=image.head;
    while(cursor < capacity) {
      if(seen[cursor]) return ?"actor registry free list cycle";
      seen[cursor]:=true;
      if(image.free[cursor] > capacity) return ?"actor registry free link out of range";
      switch(image.rows[cursor]) {case(?_)return ?"live actor in registry free list";case null {}};
      if(image.retired[cursor]==maxGeneration) return ?"exhausted actor slot in free list";
      cursor:=image.free[cursor]
    };
    var i=0;
    while(i < capacity) {
      let generation=image.generations[i];let retired=image.retired[i];
      if(generation==0 or retired > generation) return ?"invalid actor registry generation";
      switch(image.rows[i]) {
        case(?row) {
          if(row.schema=="") return ?"missing actor registry class schema";
          var methodIndex=0;
          for(method in row.methods.vals()) {
            if(method.name=="" or method.signature=="") return ?"missing persistent method contract";
            var previous=0;
            while(previous < methodIndex) {
              if(row.methods[previous].name==method.name) return ?"duplicate persistent method contract";
              previous+=1
            };
            methodIndex+=1
          };
          if(retired >= generation) return ?"live actor uses retired generation"
        };
        case null {
          if(not seen[i] and not (retired==maxGeneration and generation==maxGeneration)) return ?"unaccounted actor registry slot";
          if(seen[i] and retired >= generation) return ?"free actor uses retired generation"
        }
      };
      i+=1
    };
    null
  }
}
