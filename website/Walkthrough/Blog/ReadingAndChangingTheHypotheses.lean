import Verso.Genre.Blog
import Mathlib.Tactic
open Verso Genre Blog


#doc (Page) "Reading and Changing the Hypotheses" =>

```leanInit readingAndChangingTheHypotheses
```

```lean readingAndChangingTheHypotheses show:=false
set_option linter.unusedVariables false

open Lean Elab Tactic

```

All of the exercises here are going to build up to writing an `assumption` tactic — one that looks at all the hypotheses, and if any matches the goal, successfully proves it using that hypothesis.



# Reading the context — hypotheses

So now we can read and modify the _goal_ of a theorem.

What about the _hypotheses_?

All the hypotheses are stored in the local context, which is retrieved through `getLCtx`.

Some of them are not ones a human would think about when solving a theorem, that is, they are “implementation details” (e.g. the name of the theorem itself) and we skip them.

```lean readingAndChangingTheHypotheses

elab "print_hypotheses" : tactic => do
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hyp_name := ldecl.userName
    let hyp_type := ldecl.type
    logInfo m!"Name: '{hyp_name}'  Type: '{hyp_type}' "
```
