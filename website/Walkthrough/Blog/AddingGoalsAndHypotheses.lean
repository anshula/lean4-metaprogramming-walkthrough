import Verso.Genre.Blog
import Mathlib.Tactic
open Verso Genre Blog

#doc (Page) "Adding goals and hypotheses" =>

```leanInit AGH
open Lean Meta Elab Tactic
```

By the end of this section, you'll create a version of the `apply` tactic.

We will begin by writing tactics to access and modify the goals in the tactic state.

# Getting the goals

We've seen before that `getMainGoal` gives us the details of the current goal. The `getUnsolvedGoals` command gives us *all* the active goals in the tactic state.

Here is a tactic that lets us test this out.

```lean AGH
elab "print_goals" : tactic => do
  let goals ← getUnsolvedGoals
  for goal in goals do
    logInfo goal

example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  print_goals
  constructor
  print_goals
  all_goals rfl
```

# Modifying the goals

The list of goals can also be modified with the `setGoals` command.

Here is an implementation of a `rotate_goals` tactic that reorders the goals to push the main goal to the end.

```AGH
elab "rotate_goals" : tactic => do
  let goals ← getUnsolvedGoals
  setGoals goals.rotateLeft

example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  rotate_goals -- the goals are now in a different order
  all_goals rfl
```

Now what happens if the user decides to use `setGoals` to just delete the list of active goals?

``AGH error := true
elab "clear_goals" : tactic => do
  setGoals []

example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  clear_goals -- there are no goals here
```

Doing this indeed clears all the goals in the tactic state, but a low-level kernel error now pops up near the start of the declaration. So Lean can't be tricked into accepting an incomplete proof, and the responsibility of making sure no active goals get dropped is on the meta-programmer.

# Adding a new goal

We will now look at modifying the tactic state beyond just manipulating the list of goals.

*Creating a goal* in Lean is really *creating a metavariable* (a variable whose value a.k.a proof isn’t known yet).
*Proving a goal* in Lean is *assigning a value a.k.a proof to that metavariable*.

We can extract out the basics of goal creation into a helper tactic: `createGoal`.

```lean AGH
open Lean Elab Meta Tactic

def createGoal (goalType : Expr) : TacticM Unit := do
  let goal ← mkFreshExprMVar goalType
  appendGoals [goal.mvarId!]
```

We can see this in action here. If we want our goal to be “find an instance of type `Nat`”, we create a metavariable with type `Nat`, like so:


```lean AGH
elab "create_nat_goal" : tactic => do
  -- make the goal to find an instance of type "Nat"
  let goalType := (Expr.const ``Nat [])
  createGoal goalType

example : 1 + 2 = 3 := by
  create_nat_goal
  simp
  use 5
```

If instead, we want to create a goal to be “prove 0 = 0”, then we create a metavariable with type `0 = 0`.

```lean AGH
elab "create_reflexivity_goal" : tactic => do
  -- make the metavariable goal to prove that "0 = 0"
  let goalType ← mkEq (toExpr 0) (toExpr 0)
  createGoal goalType

example : 1 + 2 = 3 := by
  create_reflexivity_goal; swap
  simp; simp
```

We can also modify the syntax of the tactic to include the type of the new goal as a parameter.

```lean AGH
elab "create_goal_of" t:term : tactic => do
  let e ← Term.elabTerm t none
  createGoal e

example : 1 + 2 = 3 := by
  create_goal_of (Nat.Prime 2)
  simp; exact Nat.prime_two
```

# Adding a new hypothesis

Similarly, we can extract out the basics of hypothesis creation into a helper tactic: `createHypothesis`.
