import Verso.Genre.Blog
import Mathlib.Tactic
open Verso Genre Blog

#doc (Page) "Comparing Goals and Hypotheses" =>

```leanInit comparingGH
```

```lean comparingGH show:=false
set_option linter.unusedVariables false
open Lean Elab Tactic
```

By the end of this section, you will have built an `assumption` tactic that compares hypotheses of a theorem to its goal, and proves the theorem if any hypothesis exactly matches the goal.

# Getting hypotheses as a list of declarations

We know how to print hypotheses.

But suppose we actually want to save the hypotheses, not just print them out, so we can see if any match the goal?

Let's do that now.

```lean comparingGH
def getHypotheses : TacticM (List LocalDecl) := do
  let mut hypotheses : List LocalDecl := []
  let goal ← getMainGoal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    hypotheses := ldecl :: hypotheses
  return hypotheses
```

Note that instead of returning a `Unit`, we return a `List LocalDecl`.

And we wrap it all up in the `TacticM` monad so we can access the goal.

# Getting hypotheses as a list of expressions

The actual human-readable part of the hypothesis isn’t its declaration, though.

It’s the _type_ of the hypothesis.

So, let’s write a method to get that.
```lean comparingGH
def getHypothesesTypes : TacticM (List Expr) := do
  return (← getHypotheses).map (
    fun hypothesis => hypothesis.type
  )

elab "print_hypotheses_types" : tactic => do
  let types ← getHypothesesTypes
  logInfo ("Hyp types:" ++ types)
```

Now if we test it out…
```lean comparingGH
example (a b : ℕ) (h1 : a = 2) (h2: b = 3) : a+b=5 := by
  print_hypotheses_types
  simp [h1, h2]
```

…we see that this tactic get us the relevant, human-readable information about hypotheses.

Notice that `getHypothesesTypes` returns `List Expr`.  All of the actual mathematical expressions in Lean need to be in type `Expr` to be manipulated.

# Getting the goal as a declaration & expression

Now how do we get the human-readable part of the goal?  That’s the goal _type_, and we can access it using `getGoalType` below.

```lean comparingGH
/--  Tactic to return goal variable -/
def getGoalVar : TacticM MVarId := do
  return ← getMainGoal

/--  Tactic to return goal declaration-/
def getGoalDecl : TacticM MetavarDecl := do
  return ← getMainDecl -- (← getGoalVar).getDecl

/--  Tactic to return goal expression (the type) -/
def getGoalType : TacticM Expr := do
  return ← getMainTarget
  -- or (← getGoalDecl).type
  -- or (← getGoalVar).getType
```

Note that there were three “layers” we had to peel back to get to the relevant information about the goal:
- Running `← getMainGoal` gets you the **metavariable** pointing to the goal (just a variable name and a pointer)…
- …then running `getDecl` on the metavariable gets you the **declaration** (the object that actually contains lots of information about the goal)…
- then running `type` on the declaration gets you the **expression** (the thing that actually contains relevant, human-readable information about the goal e.g. the expression `1+1=2`).

The `getMainTarget` function conveniently performs this sequence of operations in one go.
