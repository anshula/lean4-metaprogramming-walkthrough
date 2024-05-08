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

We can test it out a theorem which has hypotheses that `a=2` and `b=3`.
```lean readingAndChangingTheHypotheses
example (a b : ℕ) (h1 : a = 2) (h2: b = 3) : a+b=5 := by
  print_hypotheses
  sorry
```

And we get all the relevant hypotheses.

# What goes wrong: the context doesn't update

Our tactic doesn’t seem to work when we add another hypothesis.
```lean readingAndChangingTheHypotheses
example (a b : ℕ) (h1 : a = 2) (h2: b = 3) : a+b=5 := by
  print_hypotheses -- prints h1 and h2
  have h3 : b-a = 1 := by {rw [h1, h2]}
  print_hypotheses -- still prints only h1 and h2
  sorry
```

 Our tactic doesn’t print the newest hypothesis.
