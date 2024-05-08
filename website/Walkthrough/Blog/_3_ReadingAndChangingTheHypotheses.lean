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

All of the exercises in this section and the next are going to build up to writing an `assumption` tactic — one that looks at all the hypotheses, and if any matches the goal, successfully proves it using that hypothesis.



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


# How to fix it: get the context from the goal

The new hypotheses are actually associated to the current goal.

So to get it, we need to modify our function to retrieve all hypotheses from the goal, with `(← goal.getDecl).lctx`.

```lean readingAndChangingTheHypotheses
elab "print_hypotheses'" : tactic => do
  let goal ← getMainGoal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    let hyp_name := ldecl.userName
    let hyp_type := ldecl.type
    logInfo m!"Name: '{hyp_name}'  Type: '{hyp_type}' "
```

Now when we test it out…
```lean readingAndChangingTheHypotheses
example (a b : ℕ) (h1 : a = 2) (h2: b = 3) : a+b=5 := by
  print_hypotheses' -- prints h1 and h2
  have h3 : b-a = 1 := by {rw [h1, h2]}
  print_hypotheses' -- prints h1 and h2 and h3
  sorry
```
… it does update to include the newest hypothesis.

# A cleaner way to fix it: get the context from `withMainContext`

We can also fix the same issue by just adding `withMainContext` to the beginning of the tactic.

```lean readingAndChangingTheHypotheses
elab "print_hypotheses''" : tactic => withMainContext do
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hyp_name := ldecl.userName
    let hyp_type := ldecl.type
    logInfo m!"Name: '{hyp_name}'  Type: '{hyp_type}' "
```


Why does this work?

 If you run a tactic, Lean works with the initial context of the theorem.

If you run `withMainContext`, then Lean gets the first goal (that is, the main metavariable), and adds in all of its context, and works with that.

We did that manually earlier by calling `goal ← getMainGoal` and then  `(← goal.getDecl).lctx`.  But `withMainContext` adds in all the right stuff for us.

# Extracting code out into a separate definition

At this point, the tactics have gotten longer, and before we start adding onto this tactic in the next section, we might want to move out parts of the tactic into bits we can reuse in other tactics.

We can do this as long as we move out the side-effect-causing tasks into a function wrapped into a monad, either `MetaM` or `TacticM`. (We’ll get into the differences between them later).

```lean readingAndChangingTheHypotheses
def printHypotheses : TacticM Unit := do
  let goal ← getMainGoal
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hypName := ldecl.userName
    let hypType := ldecl.type
    logInfo m!"Name: '{hypName}'  Type: '{hypType}'"
```

We can still call `print_hypotheses` as normal as long as we also create an `elab` that tells Lean which function to call when the user types `print_hypotheses`.
```lean readingAndChangingTheHypotheses
elab "print_hypotheses" : tactic => do
  printHypotheses
```


# What to return?

The function we used above looked like
```
def printHypotheses : TacticM Unit := do
	...
```

In general, if we ever write a tactic that doesn’t return anything (and perhaps, just prints something to the screen), it will have the `Unit` return type.

The `Unit` serves the purpose that `void` does in other programming languages — it tells us the function isn’t going to return anything interesting.

# MetaM vs TacticM

Our `printHypotheses` function worked when we had it return a `TacticM`.

But if we change it to use `MetaM`, it fails.
```
def printHypotheses' : MetaM Unit := do
  let goal ← getMainGoal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    let hypName := ldecl.userName
    let hypType := ldecl.type
    logInfo m!"Name: '{hypName}'  Type: '{hypType}'"
```
That’s because working within `TacticM` gives us access to the current goals — if we try to access the goals outside `TacticM`, we get an error.

In fact, `TacticM` has access to everything `MetaM` has access too, plus goals.

# So why ever use MetaM?

So if `TacticM` is just `MetaM` but more, why would we ever use `MetaM`?

The following code works if you use `MetaM`…
```lean readingAndChangingTheHypotheses
/-- Check the context for a theorem named `riemannHypothesis`. -/
def lookIntoEnvironment  : MetaM Unit := do
  let env ← getEnv
  dbg_trace (env.contains `riemannHypothesis)

#eval lookIntoEnvironment
```

… but fails if you use `TacticM`.

```
/-- Check the context for a theorem named `riemannHypothesis`. -/
def lookIntoEnvironment'  : TacticM Unit := do
  let env ← getEnv
  dbg_trace (env.contains `riemannHypothesis)

#eval lookIntoEnvironment'
```

What’s going on?

If we ever want to check how our functions work using `#eval` statements, they need to implement the `MetaEval` class — which allows output to be easily evaluated.  `MetaM` implements this class,  but `TacticM` doesn’t.

So, we ideally want to return something of type `TacticM` only when we really need it.

In summary, here are the perks of each:
- `MetaM` lets you access most of the local context (including declared _meta_variables, therefore the name `MetaM`).
- `TacticM` lets you access anything in `MetaM`, and also the current goals you have in the theorem the _tactic_ is being used in (therefore the name `TacticM`)..

And here are the downsides:
- We can’t use a `MetaM` function to peer into a goal — `MetaM` doesn’t allow us access to a list of goals.
- We can’t call a `TacticM` function from `#eval`.
