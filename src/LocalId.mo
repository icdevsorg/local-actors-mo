/// Versioned local actor identity codec. Data only: no lookup or caller authority.
/// Format v1: "MXAS", 0x01, slot:u64be, generation:u64be, reserved Principal 0x7f.
import Array "mo:core/Array";
import Blob "mo:core/Blob";
import Nat8 "mo:core/Nat8";
import Nat64 "mo:core/Nat64";
import Principal "mo:core/Principal";

module {
  public type Parts = {slot : Nat64; generation : Nat64};
  public type Address = {container : Principal; id : Principal};
  public type Prototype = {container : Principal; slot : Nat64; generation : Nat64};

  public func encode(parts : Parts) : Principal {
    func byte(value : Nat64, index : Nat) : Nat8 {
      Nat8.fromNat(Nat64.toNat((value >> Nat64.fromNat(8 * (7 - index))) & 255))
    };
    let bytes = Array.tabulate<Nat8>(22, func i {
      if(i == 0) 0x4d else if(i == 1) 0x58 else if(i == 2) 0x41
      else if(i == 3) 0x53 else if(i == 4) 1
      else if(i < 13) byte(parts.slot, i - 5)
      else if(i < 21) byte(parts.generation, i - 13)
      else 0x7f
    });
    Principal.fromBlob(Blob.fromArray(bytes))
  };

  /// Reject noncanonical length, tag, version or Principal class. Zero and the
  /// full Nat64 range are representable; registry liveness is a separate check.
  public func decode(id : Principal) : ?Parts {
    let bytes = Blob.toArray(Principal.toBlob(id));
    if(bytes.size() != 22) return null;
    if(bytes[0] != 0x4d or bytes[1] != 0x58 or bytes[2] != 0x41 or
       bytes[3] != 0x53 or bytes[4] != 1 or bytes[21] != 0x7f) return null;
    func word(offset : Nat) : Nat64 {
      var value : Nat64 = 0;
      var i = 0;
      while(i < 8) {
        value := (value << 8) | Nat64.fromNat(Nat8.toNat(bytes[offset + i]));
        i += 1
      };
      value
    };
    ?{slot = word(5); generation = word(13)}
  };

  /// Exact compatibility with the current internal identity representation.
  public func fromPrototype(value : Prototype) : Address {
    {container = value.container; id = encode({slot=value.slot; generation=value.generation})}
  };
  public func toPrototype(address : Address) : ?Prototype {
    switch(decode(address.id)) {
      case null null;
      case(?parts) ?{container=address.container;slot=parts.slot;generation=parts.generation}
    }
  };
}
