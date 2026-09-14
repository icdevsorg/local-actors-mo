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
