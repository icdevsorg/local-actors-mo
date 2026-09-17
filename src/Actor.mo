/// Local actor addresses are data, not authenticated caller context. Converting
/// an address does not prove liveness or interface compatibility; dispatch does.
import Prim "mo:prim";
import LocalId "LocalId";
module {
  public type CanonicalAddress = LocalId.Address;
  public func id(value : actor* {}) : Principal {LocalId.encode(Prim.localActorAddress(value))};
  /// The CONTAINER (the canister) at every nesting depth -- identity is flat and the registry
  /// keeps no creator link (T78/F20). A parent relation is application state.
  public func container(value : actor* {}) : Principal {Prim.localActorAddress(value).container};
  public func canonicalAddress(value : actor* {}) : CanonicalAddress {LocalId.fromPrototype(Prim.localActorAddress(value))};
  // Preserve the existing prototype API while callers adopt canonical addresses.
  public type Address = {container : Principal; slot : Nat64; generation : Nat64};
  public func address(value : actor* {}) : Address {Prim.localActorAddress(value)};
  public func fromAddress<A <: actor* {}>(address : Address) : A {
    Prim.localActorFromAddress<A>(address)
  };
}
