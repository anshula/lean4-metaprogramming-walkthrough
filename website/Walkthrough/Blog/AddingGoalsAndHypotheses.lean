import Verso.Genre.Blog
import Mathlib.Tactic
open Verso Genre Blog

#doc (Page) "Adding goals and hypotheses" =>

```leanInit AGH
```

By the end of this section, you'll create a version of the `apply` tactic.

We will begin by writing tactics to access and modify the goals in the tactic state.

# Getting the goals

We've seen before that `getMainGoal` gives us the details of the current goal. The `getUnsolvedGoals` command gives us *all* the active goals in the tactic state.

Here is a tactic that lets us test this out.

```lean AGH
open Lean Meta Elab Tactic

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

def createGoal (goalType : Expr) : TacticM Unit := withMainContext do
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
elab "create_goal" t:term : tactic => do
  let e ← Term.elabTerm t none
  createGoal e

example : 1 + 2 = 3 := by
  create_goal (Nat.Prime 2)
  simp; exact Nat.prime_two
```

# Adding a new hypothesis

Similarly, we can extract out the basics of hypothesis creation into a helper tactic: `createHypothesis`.

```lean AGH
def createHypothesis (hypType : Expr) (hypProof : Expr) (hypName := `h) : TacticM Unit := do
  let hyp : Hypothesis := { userName := hypName, type := hypType, value := hypProof }
  let (_, new_goal) ← (← getMainGoal).assertHypotheses (List.toArray [hyp])
  setGoals [new_goal]
```

Here’s an example of adding a hypothesis that looks like `h : ℕ`.

```lean AGH
elab "create_nat_hypothesis" : tactic => do
  let hypType := Expr.const ``Nat []
  let hypProof := (toExpr 0) -- use 0 as a term of type Nat
  createHypothesis hypType hypProof

example : 1 + 2 = 3 := by
  create_nat_hypothesis
  simp
```

Here’s an example of adding a hypothesis that is a proposition `0 = 0`.

```
elab "create_reflexivity_hypothesis" : tactic => do
  let hypType ← mkEq (toExpr 0) (toExpr 0) -- make the metavariable goal to prove that "0 = 0"
  let hypProof ← mkAppM ``Eq.refl #[toExpr 0] -- proof that Eq 0 0
  createHypothesis hypType hypProof

example : 1 + 2 = 3 := by
  create_reflexivity_hypothesis
  simp
```

# Catching errors when adding a hypothesis

Lean will technically let us create bogus hypotheses.

```lean AGH
elab "create_bogus_hypothesis" : tactic => do
  let hypType ← mkEq (toExpr 0) (toExpr 1) -- make the metavariable goal to prove that "0 = 0"
  let hypProof  ← mkAppM ``Eq.refl #[toExpr 0] -- proof that Eq 0 0
  createHypothesis hypType hypProof
```

```lean AGH
example : 0=1 := by
  create_bogus_hypothesis -- a new bogus hypothesis in the context
  sorry
```
But, if we actually try to use that hypothesis to prove a theorem, it will throw an error

```lean AGH error:=true
example : 0=1 := by
  create_bogus_hypothesis
  assumption
```

The issue here is that the tactic isn't checking the hypothesis statement matches the proof …

That is, by propositions-as-types and proofs-as-terms, the inferred type of the proof should be the type.

A similar thing occurred previously with `setGoals`, where we could drop all active goals from the tactic state.

So let's modify our `createHypothesis` function to check that ...

```lean AGH
def createHypothesisGuarded (hypType : Expr) (hypProof : Expr) : TacticM Unit := do
  let hypName := `h
  unless ← isDefEq hypType (← inferType hypProof) do
    throwError "The proof used for creating the hypothesis does not match the expected type."
  let hyp : Hypothesis := { userName := hypName, type := hypType, value := hypProof }
  let (_, new_goal) ← (← getMainGoal).assertHypotheses (List.toArray [hyp])
  setGoals [new_goal]
```

Here, the `inferType` function is used to deduce the type of `hypProof` (or the statement of the theorem it is a proof of, in the case of propositions). The `isDefEq` function is used to compare two expressions up to definitional equality; more will be said about this function in the later sections.

Adding the bogus hypothesis no longer works with the `createHypothesisGuarded` function.

```lean AGH error := true
elab "create_bogus_hypothesis" : tactic => do
  let hypType ← mkEq (toExpr 0) (toExpr 1) -- make the metavariable goal to prove that "0 = 0"
  let hypProof  ← mkAppM ``Eq.refl #[toExpr 0] -- proof that Eq 0 0
  createHypothesisGuarded hypType hypProof

example : 0=1 := by
  create_bogus_hypothesis
  assumption
```
