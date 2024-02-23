import Verso.Genre.Blog
import Mathlib.Tactic
open Verso Genre Blog

#doc (Page) "Adding goals and hypotheses" =>

```leanInit AGH
```

By the end of this section, you'll create a version of the `apply` tactic.

This is the tactic that is routinely used in Lean for backwards reasoning, i.e., reasoning backwards from the target.

For example, suppose the goal is to prove that `2 ^ 3` is not a prime number. The library contains the result `Nat.Prime.not_prime_pow`, which says that if `x` and `n` are natural numbers and `2 ≤ n`, then `x ^ n` is not a prime number.

A mathematician would say "to show that `2 ^ 3` is not prime, it is sufficient to show that `2 ≤ 3`, by the result `Nat.Prime.not_prime_pow`." (except maybe for the last bit); the `apply` tactic is a way to formally mirror this style of reasoning in Lean.

```lean AGH
#check Nat.Prime.not_prime_pow

example : ¬ Nat.Prime (2 ^ 3) := by
  apply Nat.Prime.not_prime_pow
  -- the goal is now to show that `2 ≤ 3`
  decide
```

We will begin by writing a tactic that creates an additional goal in the tactic state. Along the way, we will take a deeper look at how the tactic state in Lean works.

# Adding a new goal

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

# Adding a new hypothesis

Similarly, we can extract out the basics of hypothesis creation into a helper tactic: `createHypothesis`.
