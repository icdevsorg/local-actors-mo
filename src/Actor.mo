/// Local actor addresses are data, not authenticated caller context. Converting
/// an address does not prove liveness or interface compatibility; dispatch does.
import Prim "mo:prim";
module {
  public type Address = {container : Principal; slot : Nat64; generation : Nat64};
  public func address(value : actor* {}) : Address {Prim.localActorAddress(value)};
  public func fromAddress<A <: actor* {}>(address : Address) : A {
    Prim.localActorFromAddress<A>(address)
  };
}
