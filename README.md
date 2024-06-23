# Coq Interpreter Playground

Multiple examples of interpreters (with fuel), written in Coq.

## CPS transformer([CPS.v](CPS.v))

A CPS transformer and evaluator of a functional language featuring `raise` and `handle` operations.

## λ-calculus with modules

- Without recursion, using options ([ShadowInterpOption.v](ShadowInterpOption.v))
- Without recursion, using lists ([ShadowInterpList.v](ShadowInterpList.v))
- With recursion, using lists ([ShadowInterpRec.v](ShadowInterpRec.v))
- With recursion, add Peano naturals, using lists ([ShadowInterpMatchList.v](ShadowInterpMatchList.v))
- With recursion, add Peano naturals, remember constraints ([ShadowInterpMatchLazy.v](ShadowInterpMatchLazy.v))
- With recursion, add Peano naturals, remember constraints, use destructor ([ShadowInterpMatchEager.v](ShadowInterpMatchEager.v))
- With recursion, add general constructors, remember constraints ([ShadowInterpMatchGuard.v](ShadowInterpMatchGuard.v))

