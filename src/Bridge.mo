/// Experimental compiler/host bridge for Kernel's outer delivery frame. This
/// removes its Candid envelope; game method argument/reply Blobs stay opaque.
/// The host supplies immutable input fields only during a journaled local slice.
import Prim "mo:prim";
import Kernel "Kernel";

module {
  func nat(field : Nat32) : Nat64 { Prim.moxziLocalReadNat64(field) };
  func blob(field : Nat32) : Blob { Prim.moxziLocalReadBlob(field) };
  func principal(field : Nat32) : Principal { Prim.principalOfBlob(blob(field)) };
  func text(field : Nat32) : Text {
    switch (Prim.decodeUtf8(blob(field))) {
      case (?value) value;
      case null Prim.trap("invalid direct local text");
    }
  };
  func put(field : Nat32, value : Nat64) { Prim.moxziLocalWriteNat64(field, value) };
  func bytes(field : Nat32, value : Blob) { Prim.moxziLocalWriteBlob(field, value) };

  func emit(frame : Kernel.Frame) {
    switch (frame.outcome) {
      case (#readOnly(#ok value)) {put(0,7);bytes(3,value)};
      case (#readOnly(#err error)) {put(0,8);bytes(3,Prim.encodeUtf8(error))};
      case (#done(#ok value)) {put(0,0);bytes(3,value)};
      case (#done(#err error)) {put(0,1);bytes(3,Prim.encodeUtf8(error))};
      case (#suspended action) {
        let continuation=action.continuation;
        bytes(0,Prim.blobOfPrincipal(continuation.owner.container));
        put(1,continuation.owner.slot);put(2,continuation.owner.generation);
        put(3,continuation.slot);put(4,continuation.generation);
        switch (action.request) {
          case (#local request) {
            put(0,2);bytes(1,Prim.blobOfPrincipal(request.target.container));
            put(5,request.target.slot);put(6,request.target.generation);
            bytes(2,Prim.encodeUtf8(request.method));bytes(3,request.arg)
          };
          case (#rooted request) {
            put(0,6);bytes(1,Prim.blobOfPrincipal(request.target.container));
            put(5,request.target.slot);put(6,request.target.generation);
            put(7,request.slot);put(8,request.generation)
          };
          case (#external request) {
            put(0,3);bytes(1,Prim.blobOfPrincipal(request.target));
            bytes(2,Prim.encodeUtf8(request.method));bytes(3,request.arg)
          }
        }
      }
    };
    for (id in frame.retired.vals()) {
      Prim.moxziLocalRetire(Prim.blobOfPrincipal(id.container),id.slot,id.generation)
    }
  };

  /// Called by a no-argument update named localBridgeV1. Same Kernel operations
  /// and queued continuations as localDispatchV2/localResume/localCancel; the
  /// host validates the completed frame before committing the current slice.
  public func run(kernel : Kernel.Kernel) {
    let owner : Kernel.Ref={container=principal(0);slot=nat(1);generation=nat(2)};
    switch (nat(0)) {
      case (0 or 3) {
        let caller : Kernel.Caller=switch (nat(3)) {
          case (0) #host;
          case (1) #external(principal(1));
          case (2) #local({container=principal(1);slot=nat(4);generation=nat(5)});
          case _ Prim.trap("invalid direct local caller kind")
        };
        if (nat(0)==3) emit(kernel.dispatchRoot(owner,caller,nat(6),nat(7)))
        else emit(kernel.dispatchFrom(owner,caller,text(2),blob(3)))
      };
      case (1) {
        let continuation : Kernel.Continuation={owner;slot=nat(6);generation=nat(7)};
        let reply : Kernel.Reply=switch (nat(8)) {
          case (0) #ok(blob(3));case (1) #err(text(3));
          case _ Prim.trap("invalid direct local reply kind")
        };
        emit(kernel.resume(continuation,reply))
      };
      case (2) {
        let continuation : Kernel.Continuation={owner;slot=nat(6);generation=nat(7)};
        put(0,if(kernel.cancel(continuation)) 5 else 4)
      };
      case _ Prim.trap("invalid direct local operation")
    }
  };
}
