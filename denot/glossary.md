# Glossary

One term for each concept. The comments, the README and the document in `doc/` use each term
with this meaning only. A name in backticks is a code name, not a term.

## The language

**term**: a program of the language (`tm`). (Do not write: expression.)

**function**: the term `λx.e`. Its **parameter** is `x`. An application `e1 e2` applies a function to an **argument**.

**module**: a value that holds an environment (`vl_exp`). The term `ε` gives the **empty module**.

**link term**: the term `e1 ⋊ e2`. It evaluates `e2` in the environment of the module of `e1`.

**binding**: the term `x = e1; e2`. It binds `x` to the value of `e1` in `e2` and in `e1`, and gives the module of `e2` with `x` in front. The term `e1` is the **right side** of the binding.

**constructor value**: a constructor name with a list of values, its **fields** (`vl_cstr`).

**match**: the term `match e { C x1 … xn → e' | … }`. The term `e` is its **scrutinee**. Each **branch** has a constructor name, its **pattern variables** and a term.

**closed term**: a term with no free variable. An **open term** has a free variable.

## Values and traces

**environment**: a list of entries, or a shadow that stands for a module (`nv`). An **entry** binds a variable to a value, to a recursive value or to an anchor.

**unknown environment**: the environment that a denotation does not have (`Init`).

**shadow**: a computation that waits for the unknown environment (`shdw`). It is the unknown environment, a **read shadow** `Read s x`, a **call shadow** `Call s v` or a **field shadow** `Dstr s c i`.

**value**: a module, a shadow, a closure or a constructor value (`vl`).

**closure**: a function value. It holds the parameter, the body and an environment (`vl_clos`).

**fuel**: the natural number that bounds the depth of the calls and of the recursive values in one linking.

**body**: one trace for each fuel (`body`). The body of a closure is the denotation of the term of its function.

**trace**: a finite tree (`trace`). A trace is `Bot`, a leaf, a guard or a branch node. `Bot` gives no information.

**leaf**: the node `Ret v` of a trace, and its value `v`.

**guard**: the node `Guard v t` of a trace, and its value `v`. Linking must resolve `v` before the trace `t` counts.

**branch node**: the node `Match s bs` of a trace. It has one trace for each branch of a match on the shadow `s`.

**spine**: the guards and the scrutinees of a trace, without its leaves.

**finished**: a trace is finished when it has only guards and then one leaf (`dest` gives a value).

**result**: the value of the leaf of a finished trace (`dest`). A term **has no value** when no fuel gives a result. (Do not write: diverges, is stuck, for a trace.)

**cost**: the number of guards of a finished trace (`cost`).

**extend**: a trace `t'` extends `t` when `t'` is `t` with a trace in the place of some `Bot` (`le_tr`). (Do not write: approximates, refines.)

**from some fuel**: a statement holds from some fuel when a fuel exists such that the statement holds for each larger fuel (`evc`, `evd`, `ev2`).

**well formed**: a value is well formed when each body of a closure is the denotation of a term and the value is locally closed (`wf_vl`).

## Linking and the semantics

**link** (verb): link an environment `σ` into a value or a trace. Linking puts `σ` in the place of the unknown environment and runs each shadow. The noun is **linking**.

**resolve**: linking resolves a value when the linked trace is finished. An environment `σ` resolves to `σ'` under `Σ0` when linking `Σ0` into `σ` has the result `σ'` at some fuel (`res`).

**call**: the trace that enters a body with an environment, behind a guard that holds the environment (`call`).

**inner linking**, **outer linking**: in the trace of linking `Σ0` into the trace of linking `σ` into `X`, the linking of `σ` is the inner linking and the linking of `Σ0` is the outer linking.

**denotation**: the body that the semantics gives to a term (`den`). `denote n e` is its trace at the fuel `n`.

**reference interpreter**: the interpreter with environments and fuel (`ev`). The short form is **interpreter**.

**lift**: put the denotation of a term in the place of the term of each closure of a value of the interpreter (`lift`).

**adequacy**: the denotation and the interpreter give the same values.

## Anchors

**anchor**: the placeholder for the value of a binding while the right side of the binding runs (`anc`).

**name**: a free anchor `F ℓ`. **index**: a bound anchor `B i`. A recursive value around an index binds the index.

**recursive value**: the entry `x ↦ μ.v` (`nv_mu`). The value `v` can hold the index of the entry.

**open**: make the index of a recursive value a name (`open_vl`).

**close**: make a name the index of a recursive value (`close_vl`).

**unroll**: replace the index of a recursive value `μ.v` in `v` by `μ.v` (`unroll`).

**rename**: change the names of the free anchors of a value with a function (`ren_vl`). A **renaming** is such a function.

**replace**: put a recursive value in the place of each entry with a given anchor (`sub_vl`). (Do not write: substitute.)

**fresh**: an anchor is fresh for a value when no entry of the value holds its name (`nf_vl`).

**dead anchor**: the name 0. No function selects it as a fresh name, so nothing closes it.

**kill**: rename an anchor to the dead anchor in the spine of a trace (`killg`). Linking kills an anchor when the anchor leaves its scope.

**locally closed**: each index of a value has a recursive value around it that binds it.
