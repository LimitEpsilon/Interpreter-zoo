# Plan: modular analysis as an abstraction of the shadow semantics

This plan is for a paper, and for the Rocq work that the paper needs. It starts from the
development in [../denot/](../denot/). The terms are the terms of
[../denot/glossary.md](../denot/glossary.md), and the section "Terms of the plan" adds some. The
references are at the end.

## The claim

The paper makes 1 claim. A modular analysis is an abstraction of the shadow semantics. The claim
has 3 parts.

1. The shadow semantics is the standard semantics of an open term. It gives the term a meaning
   before an environment exists, and it loses no result.
2. Each known method of modular analysis is an abstraction of the shadow semantics. The
   abstraction has 2 functions, an abstract denotation and an abstract linking.
3. The claim helps to design an analysis. The paper shows 1 analysis that the known methods do
   not give.

The language of the paper has functions, modules, recursive bindings, a store and threads.
`denot/` has the first 3. Steps 6 and 7 add the store and the threads.

The paper claims soundness only. It does not claim that a modular analysis is as precise as the
analysis of the whole term.

## The base

`denot/` proves these facts with no axiom.

| Fact | Rocq | Use in the paper |
|---|---|---|
| `denote n e` is a structural recursion on `e`, and it takes no environment. | `denote` in `Semantics.v` | The analysis of a term does not read the terms that bind its free variables. |
| Linking a closed environment into the denotation gives the value of the interpreter, and no other value. | `adequacy_fwd`, `adequacy_bwd` | The shadow semantics loses no result. |
| 2 linkings have the same result as 1 linking. | `call_a`, `call_b`, `ap_a`, `ap_b` in `LinkLink.v` | The order of the linkings does not change what an analysis is sound for. |
| A binding is recursive, also through a free variable. | `separate_knot` in `Examples.v` | The claim includes recursive modules. |

These facts are about the result and the cost of a finished trace. They say nothing about the
spine of a trace. Step 2 needs facts about the spine.

## Terms of the plan

**shadow semantics**: the denotation and the linking of `denot/`.

**standard semantics**: the semantics that an analysis abstracts.

**result function**: the function of a term that takes each closed environment `σ` to the value
of the term in `σ`. It is the usual `λσ. ⟦e⟧σ`.

**modular analysis**: an analysis of an open term that does not read the terms that bind its
free variables.

**semantic operation**: an operation on values that `denote` and linking use. The read of a
variable and the application are examples.

**signature**: the semantic operations with their types. An **instance** of the signature is a
domain with 1 function for each semantic operation.

**free instance**: the instance of the shadow semantics. An operation computes on a known value,
and it makes a shadow on a shadow. Each unknown is a **generator**.

**abstract value**, **abstract trace**: an element of the domain of an analysis. It stands for a
set of values, or for a set of traces. The **top value** `⊤` stands for each value.

**sound**: an abstract value is sound for a value when the set that it stands for contains the
value. The same word applies to traces.

**abstract denotation**: the function `denote♯` of an analysis. It gives an abstract trace for a
term.

**abstract linking**: the function `link♯` of an analysis. It links an abstract environment into
an abstract trace.

**derive**: get `denote♯` and `link♯` from the soundness conditions by calculation.

**call record**: the body and the environment of 1 call.

**collecting semantics**: the shadow semantics with a call record for each call.

**depth**: the number of `Read`, `Call` and `Dstr` around the unknown environment of a shadow.

**method**: each of the 4 basic methods of modular analysis in [CC02].

**location**: the name of a cell that holds a value. The **store** gives the value of each
location. A **write** changes the value of 1 location.

**unknown store**: the store that a denotation does not have.

**thread**: a term that runs at the same time as other terms and shares the store with them.

**choice node**: a node of a trace with 2 traces, for 2 possible runs.

## Step 1. The shadow semantics and the result function

The ordinary denotational semantics gives an open term its result function. A reader will ask
why the result function is not the standard semantics. The answer has 3 parts:

- An analysis cannot abstract a function space without a representation of its elements.
- The denotation is an exact, inductive representation of the result function, and linking
  applies it to an environment.
- So an abstraction is a structural recursion on traces.

Step 3 gives the same answer in the form of an algebra. The shadow semantics is the free
instance of the semantic operations.

A function summary [SP81] is an abstraction of the result function. Thus it is also an
abstraction of the shadow semantics.

Work (document only):

- State the result function with the interpreter `ev`.
- State adequacy as an application. That is, linking applies the denotation to an environment.
- Give 1 abstraction that is simple on traces and has no direct definition on the result
  function. The analysis of step 5 is a candidate.

Done when: the document has the statement and the argument. No Rocq work is necessary, because
`adequacy_fwd` and `adequacy_bwd` hold for each closed environment.

## Step 2. The collecting semantics

An analysis of control flow abstracts the calls of a term, not only its result. The traces of
`denot/` keep the result and the guards. The guard of a call holds the environment of the body,
but it does not hold the body.

Work (Rocq):

- Add the body to the guard of each call. Then the guard is a call record.
- Make the interpreter give the same call records.
- Prove adequacy for call records. That is, after the lift, the 2 semantics give the same call
  records.
- Prove that 2 linkings and 1 linking give the same call records.

Open points:

- A term with no value also makes calls. So the collecting semantics must take the call records
  of each fuel, not only the call records of a finished trace.
- Linking kills an anchor in the spine when the anchor leaves its scope. So a call record can
  hold the dead anchor. Decide what an analysis reads from such a call record.
- A different form is a separate node of the trace for each call record. Select 1 form before
  the proofs start.

Done when: `denot/` proves the 2 facts about call records with no axiom.

## Step 3. The framework

The framework says 1 time what an analysis is and when it is sound. Each analysis of the later
steps is an instance.

`denote` and linking use values through a small set of semantic operations:

- the read of a variable (`rd`), which forces a weak value (`force`),
- the application (`ap`),
- the field of a constructor value (`ds`),
- the selection of a branch,
- the call of a body (`call`),
- `bind`, and the constructors of values.

So the framework is a signature of these operations. An instance of the signature gives a
semantics:

- The shadow semantics is the free instance. Its generator is the unknown environment.
- Linking is the map from the free instance that sends the generator to an environment.
- An analysis is an instance with abstract values. `denote♯` is `denote` at this instance.

The free algebra domain of [LL24] is the model for this form. The parts correspond in this way:

| [LL24] | Shadow semantics |
|---|---|
| the signature `entry`, `apply`, `join`, `widen` | the semantic operations |
| the generic analysis `analyse(D)` | `denote` over the signature |
| the term `Entry` | the unknown environment `Init` |
| the term `Apply(R, s)` | the shadows `Read s x`, `Call s v` and `Dstr s c i` |
| the functor `Q`, which computes when a query gives the value | an operation computes on a known value |
| the concretization, which maps each term to an operation on sets of states | linking, which maps each shadow to an operation on values |
| the generated program | the trace |
| the forward simulation and the backward simulation | `adequacy_fwd` and `adequacy_bwd` |

[LL24] has no counterpart of linking, because no part of it replaces `Entry` in a result.

The soundness conditions are:

1. `denote♯ e` is sound for `denote n e` at each fuel `n`.
2. Assume that `σ♯` is sound for `σ` and that `t♯` is sound for `t`. Then `link♯ σ♯ t♯` is
   sound for the trace of linking `σ` into `t`, at each fuel.

Condition 1 follows from 1 condition for each semantic operation. That is, the abstract
operation is sound for the operation of the free instance.

Work (Rocq, in a file such as `denot/Abstract.v`):

- Write the signature, and write `denote` over the signature.
- Show that `denote` at the free instance is the `denote` of `Semantics.v`.
- Write the relation "sound" and the conditions as the parameters of a section.
- Prove the main theorem: `link♯ σ♯ (denote♯ e)` is sound for the value of `e` in `σ`. The proof
  uses the 2 conditions and then adequacy.
- Prove that an analysis can link 3 abstract denotations in each order. `call_a` and `call_b`
  say that the 2 orders are sound for the same result.
- Let an abstract closure hold a term, not a body. This is correct because each body of a
  well-formed value is the denotation of a term (`wfb`).

Open points:

- The denotation of a binding closes an anchor and kills it. Decide if the signature has these
  2 operations, or if an abstract value holds no anchor.
- An entry of an environment holds a weak value (`wvl`). Decide if an instance has a separate
  domain for weak values, or if an abstract entry holds an abstract value.
- The word "free" is a name, not a theorem. The theorem would give, for each instance and
  each environment, 1 map from the free instance that keeps the operations. Decide if the paper
  needs this theorem.

Done when: the 2 theorems hold in Rocq for results. The same theorems for call records come
after step 2.

## Step 4. The 4 methods

[CC02] names 4 basic methods of modular analysis. Part 2 of the claim says that each method is
an abstraction of the shadow semantics. The table is a first draft. Check it against [CC02]
before the work starts.

| Method | Abstraction of a shadow | What `link♯` does | Analysis to compare |
|---|---|---|---|
| worst case | the top value | nothing | none |
| interfaces | a specification of the free variable | checks the environment against the specification | [THV12] |
| symbolic relational | the shadow itself | runs each shadow on abstract values | [SP81] |
| simplification | the shadow, in a constraint | solves the constraints | [FF99] |

Work (document, and Rocq for 1 method or more):

- Check the table against [CC02].
- For each method, derive `denote♯` and `link♯` from the soundness conditions of step 3.
- For each method, show that the result is the known analysis, or state the difference.
- Derive an abstract linking that does not run the shadows again, as in [BJ03]. This is the
  hardest case. It shows that the cost of linking is a property of the abstraction.

Done when: the document has the 4 derivations, and 1 or more is an instance in Rocq.

Risk: the derivation for [BJ03] can fail. Then the paper states the limit. That is, the claim
holds only for the methods that run the shadows again.

## Step 5. An analysis with a bound on the depth of shadows

The analysis has a parameter `k`. A shadow with a depth above `k` becomes the top value. With
`k = 0` the analysis is the worst-case method. With no bound it is the symbolic relational
method. So 2 of the known methods are the 2 ends of 1 parameter.

Work (Rocq):

- Define the depth of a shadow and the analysis, as an instance of step 3.
- Prove the 2 soundness conditions. The main theorem then comes from the framework.
- Run the analysis on the terms of `Examples.v` with `k` = 0, 1 and 2. Show a term for which
  `k = 1` gives a smaller abstract value than `k = 0`.

Done when: the instance is in Rocq, and the examples compute with `vm_compute`.

## Step 6. A store

The language gets locations and a store. Then an analysis of the heap is an abstraction of the
shadow semantics. The sketch of a bottom-up type-state analysis has the design for commands
without functions. The sketch is in the repository `snt`, in `type-state-analysis/main.tex`.

- A store is a list of writes on top of the unknown store. An environment has the same form,
  with entries on top of a shadow.
- A read compares its location with the location of each write. When the 2 locations can be
  equal or different, the read has 2 cases, each with a condition.
- A read that gets to the unknown store gives a shadow.

Work (Rocq):

- Add terms that allocate, read and write a location.
- Make the unknown store a second generator. A denotation takes no environment and no store.
- Let a leaf hold a value and a store. Let a call shadow hold the store at the call.
- Add a branch node for the comparison of 2 locations. Linking selects the branch.
- Keep the locations of a term apart from the locations of the unknown store. The names and the
  renamings of `Nominal.v` are a base for this.
- Extend the interpreter. Prove adequacy and the fact about 2 linkings with the store.
- Derive the type-state analysis of the sketch as an instance of step 3.

Open points:

- The answer of a call shadow has a value and a store. So the store after an unknown call is a
  shadow, and each later read gives a shadow.
- The number of comparisons grows with the number of writes. The semantics keeps each branch. An
  abstraction can join the branches.
- With a store, a recursive value is also possible through a location. The anchors stay for the
  bindings.
- Decide if a location is a value or 1 more form of weak value.

Done when: `denot/` proves adequacy and the fact about 2 linkings with the store, with no axiom.
The type-state analysis is an instance of the framework.

## Step 7. Threads

The language gets threads. For the denotation of 1 thread, the other threads are unknown, as the
environment is. This is the idea of the 2 levels of [DHH+24].

Design points:

- A term has more than 1 result. So a trace needs a choice node, and each fact about the result
  becomes a fact about the set of results.
- At each point where a different thread can run, the store changes in an unknown way. So the
  denotation of a thread has a shadow for the store at each such point. Linking with the other
  threads resolves these shadows.
- Commit `aaef419` of this repository has a form of the semantics with multirelations. It is a
  second option for the set of results.

Work (Rocq and document):

- Select the terms for threads. A parallel composition is an example.
- Add the choice node. State the result of a trace as a set.
- Make the interpreter give a set of results.
- Prove adequacy and the fact about 2 linkings for sets of results.
- Translate a concurrent language of [DHH+24]. Show that its local semantics and its global
  semantics agree with the denotation and with linking.

Done when: `denot/` proves the 2 facts for sets of results, and the document has the
translation.

Risk: this step is the largest. The proofs about 2 linkings are the longest part of `denot/`,
and each proof changes. If the paper becomes too long, this step is a second paper.

## Step 8. Related work

The paper must give a position for each of these.

- **LAGC semantics [DHH+24].** It has the same 2 levels. A local semantics has symbolic values,
  and a global composition makes the values concrete. It is for concurrent imperative languages.
  It has no function values and no recursive modules. After steps 6 and 7 the shadow semantics
  has the store and the threads also. The translation of step 7 supports the claim that the
  shadow semantics is more expressive.
- **Compilation by abstract interpretation [LL24].** The analysis is generic in a domain
  signature. The free algebra over the signature gives a program as the result of the analysis.
  A shadow is a term of such a free algebra, see step 3. The language of [LL24] has no function
  calls and no memory. Its only unknown is the store at the start, and it does not link 2
  results.
- **Interaction trees [XZH+20].** An open program is a tree with call events, and a handler does
  the work of linking. The continuation of an event is a function of the host language, and the
  tree is coinductive. In the shadow semantics the answer of an unknown call is a value, the
  call shadow. [HIT25] gives a variant of interaction trees in Lean.
- **Partial evaluation and normalization by evaluation [D96].** A shadow is a neutral term. The
  denotation is the residual program of an evaluator with an unknown environment. The paper
  must say this first. Then it states what it adds:
  - linking as a function on denotations,
  - the fact about 2 linkings,
  - recursive modules,
  - the use for analysis.
- **Function summaries [SP81].** See step 1.
- **Symbolic execution with opaque values [THV12].** It is the interface method of step 4.
- **Heap analyses [CDOY09], [MRV12].** After step 6 they are candidates for step 4.

## Order of the work

1. Step 3 for results, then the worst-case method of step 4, then step 5. This is the smallest
   test of the claim.
2. Step 1.
3. Step 6, with the type-state analysis.
4. Step 2, then the other methods of step 4.
5. Step 7.
6. Step 8.

## Decisions for the author

- The number of papers: step 7 in the first paper, or in a second paper.
- The number of passes: steps 2, 6 and 7 each change the traces and the proofs about 2 linkings.
  The changes can come in 1 pass or in 3.
- The form of a call record: in the guard of the call, or in a separate node.
- The number of derivations of step 4 that have an instance in Rocq.

## References

The references come from memory and from searches. Check each one before the paper cites it.

- [BJ03] A. Banerjee, T. Jensen. Modular control-flow analysis with rank 2 intersection types.
  Mathematical Structures in Computer Science 13(1), 2003.
- [CC02] P. Cousot, R. Cousot. Modular static program analysis. CC 2002, LNCS 2304.
- [CDOY09] C. Calcagno, D. Distefano, P. O'Hearn, H. Yang. Compositional shape analysis by means
  of bi-abduction. POPL 2009.
- [D96] O. Danvy. Type-directed partial evaluation. POPL 1996.
- [DHH+24] C. C. Din, R. Hähnle, L. Henrio, E. B. Johnsen, V. K. I Pun, S. L. Tapia Tarifa.
  Locally abstract, globally concrete semantics of concurrent programming languages. TOPLAS
  46(1), 2024.
- [FF99] C. Flanagan, M. Felleisen. Componential set-based analysis. TOPLAS 21(2), 1999.
- [HIT25] HITrees: higher-order interaction trees. arXiv 2510.14558, 2025.
- [LL24] D. Lesbre, M. Lemerre. Compiling with abstract interpretation. PLDI 2024, PACMPL 8,
  article 162.
- [MRV12] R. Madhavan, G. Ramalingam, K. Vaswani. Modular heap analysis for higher-order
  programs. SAS 2012.
- [SP81] M. Sharir, A. Pnueli. Two approaches to interprocedural data flow analysis. In Program
  Flow Analysis: Theory and Applications, 1981.
- [THV12] S. Tobin-Hochstadt, D. Van Horn. Higher-order symbolic execution via contracts. OOPSLA
  2012.
- [XZH+20] L. Xia and others. Interaction trees: representing recursive and impure programs in
  Coq. POPL 2020.
