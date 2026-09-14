/// Explicit compiler target for helpers containing await*. Pure helper work
/// runs in the caller's slice; only a Call suspends through the actor mailbox.
/// This is not automatic source lowering or a public replacement for async*.
import Kernel "Kernel";

module {
  public type Task<T> = {
    #done : T;
    #reject : Text;
    #call : { request : Kernel.Request; resume : Kernel.Reply -> Task<T> };
    #managed : {request : Kernel.Request; resume : Kernel.Reply -> Task<T>; cleanup : () -> ()};
  };
  public func done<T>(value : T) : Task<T> { #done(value) };
  public func bind<T, U>(task : Task<T>, next : T -> Task<U>) : Task<U> {
    switch task {
      case (#done value) next(value);
      case (#reject message) #reject(message);
      case (#managed action) #managed({request=action.request;cleanup=action.cleanup;
        resume=func(reply : Kernel.Reply) : Task<U> {bind(action.resume(reply),next)};
      });
      case (#call action) #call({ request = action.request;
        resume = func (reply : Kernel.Reply) : Task<U> { bind(action.resume(reply), next) };
      });
    };
  };
  /// Handle explicit/transport rejection from this computation. A trap in this
  /// actor's own slice still aborts that slice; it is not a catchable exception.
  public func recover<T>(task : Task<T>, handle : Text -> Task<T>) : Task<T> {
    switch task {
      case (#done value) #done(value);
      case (#reject message) handle(message);
      case (#managed action) #managed({request=action.request;cleanup=action.cleanup;
        resume=func(reply : Kernel.Reply) : Task<T> {recover(action.resume(reply),handle)};
      });
      case (#call action) #call({request = action.request;
        resume = func (reply : Kernel.Reply) : Task<T> {recover(action.resume(reply), handle)};
      });
    }
  };
  /// Completed iterations run in a loop, not a growing recursive call chain.
  /// Only the current suspended iteration retains a continuation. The array is
  /// immutable; actor-owned mutable state remains behind each action's mailbox.
  public func forEach<T>(values : [T], action : T -> Task<()>) : Task<()> {
    func next(start : Nat) : Task<()> {
      var index = start;
      while (index < values.size()) {
        switch (action(values[index])) {
          case (#done _) {index += 1};
          case (#reject message) return #reject(message);
          case (#managed pending) {
            let following=index+1;
            return #managed({request=pending.request;cleanup=pending.cleanup;
              resume=func(reply : Kernel.Reply) : Task<()> {
                bind<(),()>(pending.resume(reply),func _ {next(following)})
              };
            })
          };
          case (#call pending) {
            let following = index + 1;
            return #call({request = pending.request;
              resume = func (reply : Kernel.Reply) : Task<()> {
                bind<(), ()>(pending.resume(reply), func _ {next(following)})
              };
            })
          }
        }
      };
      #done(())
    };
    next(0)
  };
  public func call<T>(target : Kernel.Ref, method : Text, arg : Blob, decode : Blob -> T) : Task<T> {
    #call({ request = #local({ target; method; arg });
      resume = func (reply : Kernel.Reply) : Task<T> {
        switch reply { case (#ok bytes) #done(decode(bytes)); case (#err message) #reject(message) };
      };
    });
  };
  public func finish<T>(task : Task<T>, encode : T -> Blob) : Kernel.Step {
    switch task {
      case (#done value) #done(#ok(encode(value)));
      case (#reject message) #done(#err(message));
      case (#managed action) #suspendManaged({request=action.request;cleanup=action.cleanup;
        resume=func(reply : Kernel.Reply) : Kernel.Step {finish(action.resume(reply),encode)};
      });
      case (#call action) #suspend({ request = action.request;
        resume = func (reply : Kernel.Reply) : Kernel.Step { finish(action.resume(reply), encode) };
      });
    };
  };
};
