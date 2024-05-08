import Verso.Genre.Blog
import Mathlib.Tactic
open Verso Genre Blog

#doc (Page) "Adding Goals and Hypotheses" =>

```leanInit AGH

```


By the end of this section, you'll create a version of the `apply` tactic.  This tactic "applies" a lemma which has a conclusion that matches the current goal, and updates the current goal accordingly.

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

```lean AGH
elab "rotate_goals" : tactic => do
  let goals ← getUnsolvedGoals
  setGoals goals.rotateLeft

example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  rotate_goals -- the goals are now in a different order
  all_goals rfl
```

Now what happens if the user decides to use `setGoals` to just delete the list of active goals?

```lean AGH error := true
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
def createGoal (goalType : Expr) : TacticM Unit :=
withMainContext do
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
  create_reflexivity_goal
  rotate_goals
  simp; simp
```

Until now, we had to be in an `elab` to decide what goal would be created.

But now, we can create a tactic that allows us to decide what the new goal is from within the proof itself.

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
def createHypothesis
  (hypType : Expr) (hypProof : Expr) (hypName := `h) :
  TacticM Unit :=
do
  let hyp : Hypothesis := {
    userName := hypName,
    type := hypType,
    value := hypProof
  }
  let (_, new_goal) ← (← getMainGoal).assertHypotheses (
    List.toArray [hyp]
  )
  setGoals [new_goal]
```

Here’s an example of adding a hypothesis that looks like `h : ℕ`.

```lean AGH
elab "create_nat_hypothesis" : tactic => do
  let hypType := Expr.const ``Nat [] -- type of Nat
  let hypProof := (toExpr 0) -- term of 0
  createHypothesis hypType hypProof

example : 1 + 2 = 3 := by
  create_nat_hypothesis
  simp
```

Here’s an example of adding a hypothesis that is a proposition `0 = 0`.

```
elab "create_reflexivity_hypothesis" : tactic => do
  let hypType ← mkEq (toExpr 0) (toExpr 0) -- statement that "0 = 0"
  let hypProof ← mkAppM ``Eq.refl #[toExpr 0] -- proof that "0 = 0"
  createHypothesis hypType hypProof

example : 1 + 2 = 3 := by
  create_reflexivity_hypothesis
  simp
```

# Catching errors when adding a hypothesis

Lean will technically let us create bogus hypotheses.

```lean AGH
elab "create_bogus_hypothesis" : tactic => do
  let hypType ← mkEq (toExpr 0) (toExpr 1)  -- statement that "0 = 1"
  let hypProof  ← mkAppM ``Eq.refl #[toExpr 0] -- proof that "0 = 0"
  createHypothesis hypType hypProof
```

```lean AGH
example : 0=1 := by
  create_bogus_hypothesis -- "0=1" is now a hypothesis
  sorry
```
But, if we actually try to use that hypothesis to prove a theorem, it will throw a low-level error in the kernel.  A similar thing occurred previously with `setGoals`, where we could drop all active goals from the tactic state, but we got a kernel error if we tried to then finish the proof.

```lean AGH error:=true
example : 0=1 := by
  create_bogus_hypothesis
  assumption
```

Ideally, we want to catch this error earlier.

To do that, we want our tactic to check that the hypothesis statement matches the proof. That is, by propositions-as-types and proofs-as-terms, the inferred type of the `hypProof` should be `hypType`.

So let's modify our `createHypothesis` function to perform this check.

```lean AGH
def createHypothesisGuarded
  (hypType : Expr) (hypProof : Expr) (hypName := `h):
  TacticM Unit :=
do
  unless ← isDefEq hypType (← inferType hypProof) do
    throwError
      "The proof used for creating the hypothesis
      does not match the expected type."
  let hyp : Hypothesis := {
    userName := hypName,
    type := hypType,
    value := hypProof
  }
  let (_, new_goal) ← (← getMainGoal).assertHypotheses (
    List.toArray [hyp]
  )
  setGoals [new_goal]
```

Here, the `inferType` function is used to deduce the type of `hypProof` (or the statement of the theorem it is a proof of, in the case of propositions). The `isDefEq` function is used to compare two expressions up to definitional equality; more will be said about this function in the later sections.

Adding the bogus hypothesis no longer works with the `createHypothesisGuarded` function.

```lean AGH error := true
elab "create_bogus_hypothesis'" : tactic => do
  let hypType ← mkEq (toExpr 0) (toExpr 1) -- statement that "0 = 1"
  let hypProof  ← mkAppM ``Eq.refl #[toExpr 0] -- proof that "0 = 0"
  createHypothesisGuarded hypType hypProof

example : 0=1 := by
  create_bogus_hypothesis'
  assumption
```

# Adding a known theorem as a hypothesis

We've previously seen that it's possible to retrieve the statement and proof of a theorem from the environment given its name.

As an easy application of the tools we've developed so far, let's write a tactic that takes the name of a theorem in the environment and adds it as a local hypothesis.

```lean AGH
elab "add_theorem_as_hypothesis" nm:name : tactic => do
  let some thm := (← getEnv).find? nm.getName |
    throwError s!"The result {nm} is not in the environment."
  createHypothesisGuarded thm.type thm.value!

example : 1 + 2 = 2 + 1 := by
  add_theorem_as_hypothesis `Nat.add_comm -- adds "h"
  exact (h 1 2)
```

# Making progress on a proof state

We typically make progress on a proof in Lean through *tactics*. These have the effect of replacing the current proof state with another, in a way that preserves provability (i.e., if the new set of goals is solvable, then so is the old one).

The converse is not true - it is possible to start from a solvable tactic state and go to an unsolvable one, for example by clearing an essential hypothesis or using backwards reasoning on the goal.

# Creating a tactic for backwards reasoning

So far, we have written tactics that work on the list of active goals or add hypotheses to the local context. To better understand how tactics manipulate the proof state, let's write a simplified version of the `apply` tactic - the tactic that is routinely used in Lean for backwards reasoning, i.e., reasoning backwards from the target.

For example, suppose the goal is to prove that `2 ^ 3` is not a prime number. The library contains the result `Nat.Prime.not_prime_pow`, which says that if `x` and `n` are natural numbers and `2 ≤ n`, then `x ^ n` is not a prime number.

A mathematician would say "to show that `2 ^ 3` is not prime, it is sufficient to show that `2 ≤ 3`, by the result `Nat.Prime.not_prime_pow`." (except maybe for the last bit). The `apply` tactic is a way to formally mirror this style of reasoning in Lean.

```lean AGH
#check Nat.Prime.not_prime_pow

example : ¬ Nat.Prime (2 ^ 3) := by
  apply Nat.Prime.not_prime_pow
  -- the goal is now to show that `2 ≤ 3`
  decide
```

We'll start with the scenario where we have a goal `Q` and a local hypothesis of type `P → Q` and try to set the goal to `P` by backwards reasoning.

Our rough strategy is going to be to:
- Check whether the hypothesis is an implication, i.e., of the form `P → Q`
- Check whether the conclusion of the hypothesis `h` matches the type of the current goal
- Create a new goal `p` of type `P`
- Assign the value `h p` to the current goal (remember `h` is of form `P → Q`, so `h p` is of form `Q`)
- Set `p` as the main goal

Here is what this strategy looks like translated into code (parts of this code are deliberately sub-optimal; we'll see ways of improving it shortly):


```lean AGH show:=false
def getHypothesisByFVarId (h : FVarId) : TacticM LocalDecl := withMainContext do
  let goal ← getMainGoal  -- the dynamically generated hypotheses are associated with this particular goal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    if ldecl.fvarId == h then
      return ldecl
  throwError m!"No hypothesis with fvarId {h.name}."

def getHypothesisByTerm (h : TSyntax `term) :  TacticM LocalDecl := withMainContext do
  let fvarId ← getFVarId h
  getHypothesisByFVarId fvarId
```

```lean AGH
elab "apply_hypothesis" h:term : tactic =>
withMainContext do
  -- ensure that the hypothesis is an implication
  let hyp ← getHypothesisByTerm h
  guard hyp.type.isArrow

  -- extract the implication's antecedent & consequent
  let .forallE _ P Q _ := hyp.type | unreachable!

  -- ensure that the conclusion of `h` matches the target
  unless Q == (← getMainTarget) do
    throwError m!"The type of the conclusion of {h}
    does not match the current target."

  -- create a new goal of type `P`
  let newGoal ← mkFreshExprMVar P

  -- close off the current goal with `h newGoal`
  (← getMainGoal).assign (.app hyp.toExpr newGoal)

  -- set `newGoal` as the main goal
  replaceMainGoal [newGoal.mvarId!]

example (h : Even 2 → Even 4) : Even 4 := by
  apply_hypothesis h -- the goal is now `Even 2`
  rw [even_iff_two_dvd]
```

However, our implementation has some shortcomings. Let's try to change the target to `Even (2 * 2)` instead of `Even 4`:

```lean AGH error:=true
example (h : Even 2 → Even 4) : Even (2 * 2) := by
  apply_hypothesis h -- a type mismatch error
```

We get a type mismatch error since Lean can't tell that `Even 4` is the same as `Even (2 * 2)`, even though they are equal by definition. This is because our comparison of expressions in the code uses "Boolean equality" (denoted `==`), which is too strict for our purposes.

The error goes away when we switch to the coarser notion of "definitional equality" (checked by the function `isDefEq`):

```lean AGH
elab "apply_hypothesis_defeq" h:term : tactic =>
withMainContext do
    -- ensure that the hypothesis is an implication
  let hyp ← getHypothesisByTerm h
  guard hyp.type.isArrow

  -- extract the implication's antecedent & consequent
  let .forallE _ P Q _ := hyp.type | unreachable!

  -- ensure that the conclusion of `h` matches the target
  unless ← isDefEq Q (← getMainTarget) do
    throwError m!"The type of the conclusion of {h}
    does not match the current target."

  -- create a new goal of type `P`
  let newGoal ← mkFreshExprMVar P

  -- assign the value `h newGoal` to the current goal
  (← getMainGoal).assign (.app hyp.toExpr newGoal)

  -- set `newGoal` as the main goal
  replaceMainGoal [newGoal.mvarId!]
```
Now the example works as intended.
```lean AGH
example (h : Even 2 → Even 4) : Even (2 * 2) := by
  apply_hypothesis_defeq h -- the goal is now `Even 2`
  rw [even_iff_two_dvd]
```
# Unification

As mentioned before, the function `isDefEq` does more than just checking for definitional equality - it also handles the *unification* (roughly, filling in holes) of *expressions containing meta-variables* (roughly, expressions with holes).

For example, consider the two expressions `(_ * 37)` and `(71 * _)`, where the underscores indicate "holes" in the expressions. While these expressions are not equal by `==`, they are by `isDefEq`, since they can be made equal by choosing the values for the holes appropriately (so that they both become `71 * 37`). This is the idea behind *unification*, and the `isDefEq` function tries to fill in the holes as much as possible to make the two expressions match up.

The word *meta-variable* was used earlier in a different sense - to refer to a goal in the tactic. However, the two senses of the word are essentially the same - a goal can be thought of as a hole for a proof of the appropriate type.

We can implement the `apply_hypothesis` using a strategy involving unification:
- Suppose the current goal is `Q`
- Create a meta-variable `?P` for the type of the new goal
- Check whether the type of the hypothesis unifies with the expression `?P → Q`
- If the unification succeeds and the meta-variable `?P` is assigned the value `P`, create a meta-variable `p` of type `P` for the new goal
- Assign the value `h p` to the current goal
- Set `p` as the main goal

With this approach, we no longer need to check if the hypothesis is an implication and explicitly extracting its antecedent and consequent.

```lean AGH

elab "apply_hypothesis_unif" h:term : tactic => withMainContext do
  -- get the hypothesis
  let hyp ← getHypothesisByTerm h

  -- try to unify hypothesis with `newTarget → currentTarget`
  let currentTarget ← getMainTarget
  let newTarget ← mkFreshExprMVar none
  unless ← isDefEq hyp.type (← mkArrow newTarget currentTarget) do
    throwError m!"The hypothesis is expected to be an implication
      with conclusion matching the current goal."

  -- fill in holes in `newTarget`
  let newTarget ← instantiateMVars newTarget

  -- create a new goal of type `newTarget`
  let newGoal ← mkFreshExprMVar newTarget

  -- logging information about the type of the new goal
  logInfo m!"The new target was updated from {currentTarget} to {newTarget}."

  -- assign the value `h newGoal` to the current goal
  (← getMainGoal).assign (.app hyp.toExpr newGoal)

  -- set `newGoal` as the main goal
  replaceMainGoal [newGoal.mvarId!]
```

And the tactic works the same as before.
```lean AGH
example (h : Even 2 → Even 4) : Even (2 * 2) := by
  apply_hypothesis_unif h
  rw [even_iff_two_dvd]
```

# A more general `apply` tactic

To finish off this chapter, we'll generalize our `apply_hypothesis` tactic to scenarios where the type of the argument is not just a single implication.

For example, suppose we have a target like `¬Nat.Prime (2 * 3)` that we want to prove by backwards reasoning using `Nat.not_prime_mul` (shown below), which says that the product of two numbers is not prime when those numbers are both not equal to 1.

```lean AGH
#check Nat.not_prime_mul
```

 We would like our `apply` tactic to infer values of the implicit parameters `a` and `b` through unification and create two new goals corresponding to the remaining arguments: `2 ≠ 1` and `3 ≠ 1`.

Lean contains utilities for taking expressions of the form `P₁ → (P₂ → ... → Pₖ → (... → Q))` and extracting the hypotheses `#[P₁, P₂, ..., Pₖ, ...]` along with the conclusion `Q` (which go under the fanciful name of "telescopes"). These turn out to be exactly what we need to implement a version of the `apply` tactic that does what we want.

Here is our rough strategy for implementing the tactic:
- Infer the type of the hypothesis being applied
- Using a telescope, obtain the list of meta-variables `#[p₁, p₂, ..., pₖ, ...]` for the conditions along with the conclusion `Q`
- Attempt to unify `Q` with the current target
- Assign the value `h p₁ p₂ ... pₖ ...` to the current goal, where `h` is the hypothesis being applied
- Make the hypotheses `#[P₁, P₂, ..., Pₖ, ...]` the new targets

```lean AGH
elab "apply_to_target" h:term : tactic => withMainContext do
  -- the hypothesis being applied (in the form of an expression)
  let hyp ← elabTerm h none
  -- infer the type of the hypothesis being applied
  let t ← inferType hyp
  -- obtain the conditions and the conclusion using a telescope
  let (conditions, _, conclusion) ← forallMetaTelescope t
  -- attempt to unify the conclusion with the main target
  unless ← isDefEq conclusion (← getMainTarget) do
    throwError m!"The conclusion of the hypothesis {h} does not match with the current target."
  -- Update the conditions with the values determined by unification
  let conditions ← conditions.mapM instantiateMVars
  -- assign the conclusion to the current goal
  (← getMainGoal).assign <| mkAppN hyp conditions
  -- set the hypotheses as the new goals
  replaceMainGoal <| conditions.toList.map Expr.mvarId!

example : ¬ Nat.Prime (2 * 3) := by
  apply_to_target Nat.not_prime_mul
  -- the two new goals are `2 ≠ 1` and `3 ≠ 1`
  all_goals decide
```
