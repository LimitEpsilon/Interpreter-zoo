# A denotational semantics for a module language, with adequacy

This directory defines a computable denotational semantics for a call-by-value language with
first-class modules and recursive bindings. It proves that the semantics agrees with an
interpreter. The proofs are in Rocq 9. They use no axiom, no coinductive type and no library
other than the standard library.

```sh
make        # about 20 seconds
```

The terms are in [glossary.md](glossary.md). The definitions and the proofs are also in the
document [../doc/main.pdf](../doc/main.pdf).

## The language

```
e ::= x | λx.e | e e          variable, function, application
    | e ⋊ e | ε | x = e; e    link term, empty module, binding
    | C e … e                 constructor
    | match e { C x … x → e | … }
```

A module is a value that holds an environment. The link term `e1 ⋊ e2` evaluates `e2` in the
environment of the module of `e1`. The binding `x = e1; e2` binds `x` in `e2` and in `e1`. It
gives the module of `e2` with `x` in front. Thus a binding defines a recursive function, a
recursive functor, or mutually recursive modules.

## The semantics

The denotation of a term is one finite trace for each fuel. `denote n e` is a structural
recursion on `e`, and it takes no environment:

- Each free variable becomes a shadow, that is a computation that waits for the unknown
  environment.
- A closure holds the denotation of its body, not a term.
- Linking puts an environment in the place of the unknown environment and runs each shadow.
  `run n σ e` is the result of linking `σ` into the denotation of `e` at the fuel `n`.

So a client and a module can run apart. Linking the environment of the module into the
denotation of the client gives the value of the whole term.

### Guards

A trace is `Bot`, a leaf `Ret v`, a guard `Guard v t` or a branch node `Match s bs`. The guard
`Guard v t` says that linking must resolve `v` before `t` counts. When linking uses only a part
of a resolved value, it keeps the whole value in a guard. The cases are:

- a read of one variable of a module,
- one field of a constructor value,
- the selection of a branch,
- the environment of a body.

For example, the denotation of `(λx. O) (f y)` is `Guard [x ↦ Call f y] (Ret O)`. Linking it
with an `f` that does not return has no result, as call-by-value requires.

### Recursive bindings

An entry of an environment binds a variable to a weak value. A weak value is a value, a
recursive value `μ.v` or an anchor. Only a value is the result of a term.

An anchor is the placeholder for the value of a binding while its right side runs. Anchors are
locally nameless. A recursive value around an index binds the index, and a name is free. The
types are inductive, so open, close and unroll are structural recursions. They do not change
the body of a closure.

- The denotation of `x = e1; e2` links `x ↦ anchor` into the denotation of `e1`. It closes the
  anchor in the result, which gives `x ↦ μ.v`. Then it continues with `e2`.
- Linking into `μ.v` opens it with a fresh anchor, links, and closes it.
- A read forces the weak value of the variable. A value gives itself, and `μ.v` gives its
  unrolling. An anchor gives no value. So `x = x; ε` and `x = S x; ε` have no value.
- When an anchor leaves its scope, linking kills it in the guards. That is, it renames the
  anchor to the dead anchor, the name 0. A read of the dead anchor also gives no value.
- Linking into the opened body of a recursive value is not a structural recursion. It uses the
  same fuel as a call.

## What is proved

`ev N e ρ` is the reference interpreter. It has environments and fuel, and no shadows, no traces
and no linking. A closure of the interpreter holds a term. For a binding, the interpreter
evaluates `e1` with `x` bound to a fresh anchor, and then binds `x` to the recursive value of
the result.

`lift` puts the denotation of a term in the place of the term of each closure.

```coq
Theorem adequacy_fwd N e ρ v : closed_env ρ →
  ev N e ρ = Some v → ∃ n, run n (lift_env ρ) e = Some (lift v).

Theorem adequacy_bwd n e ρ w : closed_env ρ →
  run n (lift_env ρ) e = Some w → ∃ N v, ev N e ρ = Some v ∧ w = lift v.

Corollary termination e :
  (∃ N v, ev N e rnil = Some v) ↔ (∃ n w, run n nv_mt e = Some w).
```

`closed_env ρ` says that `ρ` is locally closed. The empty environment is locally closed.

The main lemma is that 2 linkings give the same result as 1 linking. Assume that `σ` resolves
to `σ'` under `Σ0`. Then linking `Σ0` into the trace of linking `σ` into `X` has the same result
as linking `σ'` into `X`. The lemma holds in the 2 directions (`call_a`, `call_b`).

## Layout

| File | Content |
|---|---|
| `Syntax.v` | terms |
| `Anchor.v` | anchors, and what open, close and rename do to one anchor |
| `Domain.v` | shadows, environments, weak values, values and traces, and the operations on anchors |
| `Nominal.v` | facts about open, close, rename and unroll |
| `Semantics.v` | linking, the fuel, the denotation |
| `Laws.v` | the monad laws of `bind`, and linking through `bind` |
| `Reference.v` | the reference interpreter |
| `Wf.v` | well-formed values and traces |
| `Order.v` | the order on traces, and more fuel |
| `Conv.v` | finished traces |
| `Fresh.v` | linking adds no free anchor |
| `Equiv.v` | linking and the renaming of anchors |
| `Subst.v` | linking and unrolling |
| `LinkLink.v` | 2 linkings and 1 linking |
| `Lift.v` | the lift of the values of the interpreter |
| `Adequacy.v` | the theorems |
| `Examples.v` | recursive functions, modules and functors, open terms, and linking after separate evaluation |
| `glossary.md` | the terms of the comments and the documents |

Each file starts with a header that tells what the file is for.
