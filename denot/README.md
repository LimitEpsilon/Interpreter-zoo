# A computable denotational semantics for a module language, with adequacy

Rocq 9.x, no axioms, no coinductive types, no external libraries.

```sh
make        # about 10 seconds
```

## The language

A call-by-value λ-calculus with first-class modules, constructors and pattern
matching ([Syntax.v](Syntax.v)):

```
e ::= x | λx.e | e e          functions
    | e ⋊ e | ε | x = e; e    link (import), empty module, bind-and-export
    | C e … e | match e { C x … x → e | … }
```

## What is proved

`denote n e` ([Semantics.v](Semantics.v)) is the n-th finite approximation of
the denotation of `e`. It is defined by structural recursion on `e` and takes
no environment: free variables become *shadows*, and a closure holds the
denotation of its body (a `nat`-indexed family of finite traces), not syntax.
`run n σ e` links the environment `σ` into that denotation.

`ev N e ρ` ([Reference.v](Reference.v)) is an ordinary environment-passing
interpreter with fuel, which knows nothing about shadows, traces or linking.

[Adequacy.v](Adequacy.v):

```coq
Theorem adequacy_fwd N e ρ v :
  ev N e ρ = Some v → ∃ n, run n (lift_env ρ) e = Some (lift v).

Theorem adequacy_bwd n e ρ w :
  run n (lift_env ρ) e = Some w → ∃ N v, ev N e ρ = Some v ∧ w = lift v.

Corollary termination e :
  (∃ N v, ev N e rnil = Some v) ↔ (∃ n w, run n nv_mt e = Some w).
```

`lift` ([Lift.v](Lift.v)) replaces the syntax in each closure by its
denotation. `Print Assumptions` reports "Closed under the global context" for
all three.

The key lemma ([LinkLink.v](LinkLink.v)) is the exact form of the Advance
Lemma: if `σ` resolves to `σ'` under `Σ0`, then linking `Σ0` into
(`σ` linked into `X`) returns the same value as linking `σ'` into `X`, in both
directions (`call_a`, `call_b`).

## Files

| File | Contents |
| --- | --- |
| `Syntax.v` | terms |
| `Domain.v` | shadows, environments, values, finite traces, `bind`, `dest` |
| `Semantics.v` | linking, `linkb` (fuel), `denote`, `run` |
| `Reference.v` | the reference interpreter `ev` |
| `Laws.v` | monad laws, linking distributes over `bind` |
| `Wf.v` | well-formed values: every closure body is a denotation |
| `Order.v` | approximation order; linking and `denote` are monotone in the fuel |
| `Conv.v` | finished traces are maximal; raising fuel; shapes of results |
| `LinkLink.v` | linking twice is linking once |
| `Lift.v` | embedding of reference values; `ev` is monotone in its fuel |
| `Adequacy.v` | the theorems above |
| `Examples.v` | closed runs, open denotations, separate evaluation then linking |

## Guards

A trace is `Bot`, `Ret v`, `Guard v t` or `Match s branches`. `Guard v t` says
that `v` must be resolved before `t` counts. The rule used here: whenever part
of a resolved value is discarded (reading one binding of a module, taking one
field of a constructor, selecting a branch, entering a body with a new
environment), the whole value is kept in a guard. This is what makes the
semantics exact: `(λx. O) (f y)` denotes `Guard [x ↦ Call f y] (Ret O)`, so
linking with a diverging `f` diverges, as call-by-value requires.

The earlier interpreter (`../modular_interpreter`, `ShadowInterpMatchGuard.v`)
guards variable reads and the empty module only; for that program it produces
the bare trace `O`.

## Differences from the earlier interpreter

- `x = e1; e2` is **not recursive** here. There are no μ-values or anchors;
  recursion in the examples uses a fixed-point combinator. Recursive bindings
  are the next step.
- Constructors take a list of arguments instead of an arity-indexed vector.
- Definitions are in direct style with `bind`, not CPS.
- Closures store `nat → trace` without the source-term annotation; the
  well-formedness predicate in `Wf.v` plays that role in the proofs.

## Proof outline

1. Everything the semantics produces is well formed (`Wf.v`), hence every
   closure body is an increasing chain and linking is monotone in the fuel
   (`Order.v`).
2. A finished trace is maximal, so more fuel leaves it unchanged (`Conv.v`).
3. Link-link (`LinkLink.v`): direction (a) by induction on the inner fuel,
   direction (b) by induction on the fuel of the single link. Direction (a)
   also bounds the number of guards.
4. Forward adequacy by induction on the interpreter's fuel, using (b).
   Backward adequacy by induction on the number of guards in the finished
   trace, using (a): entering a body always passes a guard, and the body's
   own run has strictly fewer.
