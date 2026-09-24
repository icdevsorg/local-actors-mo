# local-actors

The small public surface beside moxzi's `actor*` feature. The runtime that makes `actor*`
work is injected by the compiler (`moxzi:compiler-runtime`); you never import it. What
you *do* import is this:

```motoko
import Actor "mo:local-actors/Actor";

persistent actor Main {
  actor* class Counter(initial : Nat) {
    var value = initial;
    public func add(n : Nat) : async* Nat { value += n; value };
  };
  var counter = Counter(0);
  public func whoami() : async Principal { Actor.id(counter) };   // a principal you can hand out
};
```

`Actor.id`, `Actor.container`, `Actor.address` and `Actor.fromAddress` are the whole API
most programs need. Everything else in this package (`Kernel`, `Jobs`, `Wire`, …) is the
compiler-facing side and is documented below for people working on the runtime.

Requires moxzi (`moc` cannot compile `actor*`). This package declares that in its
`mops.toml` — `[moxzi] features = ["local-actors"]` — so `moxzi build` in a
consuming project adds `--experimental-local-actors` itself and says so. Hold instances in
stable state and you also need `--experimental-local-actor-persistence`; a library that
does so declares `local-actor-persistence` too. Details: `docs/mops-requirements.md` in
the moxzi repository.

---

# Experimental local-actor compiler target

`Kernel.mo` holds private Motoko object roots, generation-checked local references,
and continuation closures. The optional Moxzi `local-actors-prototype` runtime
supplies queued execution, sender context, per-slice rollback and coherent recovery.
This is not yet the `actor*` language frontend or an isolation boundary against
arbitrary Motoko code that shares mutable references.

`Computation.mo` represents a helper computation explicitly:

- `done` returns a value without suspension.
- `bind` runs its continuation immediately for a completed helper, or composes it
  behind the helper's next mailbox call.
- `call` yields one real local request; its reply decoder executes in the resumed
  caller slice. A transport rejection propagates through `#reject`.
- `finish` adapts the final typed result into a kernel step using a supplied encoder.
- `recover` handles explicit/transport rejection of a computation, including a
  failed callee call. It does not catch a trap in the caller's own slice.
- `forEach` sequences actions. Completed iterations run in a loop, while a queued
  call retains only the current iteration's continuation and immutable input array.

Only a `#call` introduces a mailbox suspension. This preserves the distinction
between an `await*` helper and a queued actor call. Trap handling is the runtime's
transaction contract; `Computation` does not catch traps or merge callee commits
into a caller transaction.

Callers choose their payload protocol. The experimental Colony port uses named
records for multiple parameters and a single `{value = result}` reply envelope.
Decoding `from_candid ... : ?(A, B)` expects multiple arguments; it must not be used
to decode one tuple-valued reply without an enclosing record.

`Wire.mo` is a retained, rejected packed-codec experiment. Candid remains the
prototype's default, and caller-aware V2 modules require that path.

Actual Colony integration lives in the sibling `motoko.game/games/lantern-colony-local`
source package. Its framework parity/recovery tests are in
`moxzi/runtime/tests/local_colony.rs`; the fixture imports the game via the explicit
`colony-local` package alias. No game-specific Rust host is required by these classes.

The actual Colony coordinator exercises these helpers through full game input,
clock and snapshot calls. Its tests are `moxzi/runtime/tests/local_game.rs`, including
saved nested calls, lost committed replies, partial-admission compensation,
retirement and identity reuse. Game source and framework player/save integration
remain separate: the generic player does not yet select a local backend.

### Experimental ordered checkpointed jobs

`import Jobs "mo:local-actors/Jobs"` provides a versioned cursor and generation/position
tickets for bounded work over an immutable ordered list of actor identities. Each
actor retains its own state. `admit` rejects stale work before it executes; `complete`
advances the cursor after a successful batch; `cancel` invalidates outstanding tickets
without undoing committed batches.

Authenticate continuation calls. Apply a batch and store its completed cursor in the
same atomic segment, with no real await in any unit. Then explicitly schedule a real
self-message/timer. `await*` alone does not commit. Trap if completion validation fails
after mutation. These records are ordinary data, not authorization capabilities.

Work-count limits do not guarantee fuel bounds: an indivisible oversized unit still
needs subdivision or explicit failure/recovery policy. This initial module provides
no timer adapter, hidden commits, external-effect exactly-once guarantee or live-stack
persistence. See `moxzi/runtime/tests/fixtures/cooperative/CheckpointJobs.mo` for the
self-message example and `.plan/actor-star/followups/cooperative-execution/checkpoint-jobs.md`
for the contract, evidence and remaining gates. No package release is implied.

`JobSnapshot` optionally validates a cursor against exact ordered canonical identities
and an application schema. `JobQueue` provides bounded round-robin admission with durable
active/failed reservations and explicit recovery. Neither module performs hidden awaits
or changes actor state ownership. Queue bounds include failed and in-flight jobs.
These controls now run on native, Pulley and PocketIC; whole-world restoration is tested
between the two local backends. Language-upgrade migration remains application work.
