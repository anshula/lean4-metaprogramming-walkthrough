import Verso.Genre.Blog
import Mathlib.Tactic
open Verso Genre Blog

#doc (Post) "Reading and Changing the Goal" =>

# A first tactic

```leanInit readingAndChangingTheGoal
```


Here is a super simple tactic: the `do_nothing` tactic.

```lean readingAndChangingTheGoal
open Lean Meta Elab Tactic Term Command

elab "do_nothing" : tactic => do
  return
```

Please feel free to **paste in these bits of code into your editor**, creating one big Lean file as we go! 


We’ll see that, indeed, this tactic changes nothing about the proof state (hover over the end-of-line bubbles to see the goal state):
```lean readingAndChangingTheGoal
example : True := by
  do_nothing -- the goal here is still `True`
  trivial
```

# Reading the context

Now, let’s create a tactic `print_goal` that reads what the current goal is. 
```lean readingAndChangingTheGoal
elab "print_goal" : tactic => do
  let goal ← getMainGoal
  logInfo goal
```

Let’s test the tactic:

```lean readingAndChangingTheGoal
example : 1+1=2 := by
  print_goal -- 1+1=2 
  trivial
```

And we get what we expect.

++
/-
# Reading the context another way

The above “goal” is really just a variable referencing the goal. It has type  `MVarId`, as can be seen by hovering over the constant named `goal` in the code block above.

To get the actual goal, you’d call `getType` on the variable (which gives you something of type `Expr`), and that will give you the actual goal expression:

```lean readingAndChangingTheGoal
elab "print_goal_type" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  logInfo goalType
```

Using `print_goal` and `print_goal_type` both print the same thing though…

```lean readingAndChangingTheGoal
example : True := by
  print_goal_type -- True
  trivial
```

…since when we were printing the goal variable, `logInfo` had some magic inside it that knew we actually wanted to print the _relevant goal information_ stored in the variable.

The `getMainTarget` command accomplishes the same thing as getting the goal and then getting its type.
++

# Modify the context

Now we can read the goal.  Let’s modify it.

Let’s write a tactic that turns a theorem into its contrapositive.  First, let’s prove that a contrapositive tactic could work.
```lean readingAndChangingTheGoal
theorem ctrp {P Q : Prop} : (¬ Q → ¬ P) → (P → Q) := by
  intro h
  rwa [not_imp_not] at h
```
We can test it out.
```lean readingAndChangingTheGoal
example {P : Prop} : P → True := by
  apply ctrp; simp
```

And it does what we expect.

Now we want to take the line `apply ctrp`, and, because it is so cumbersome to write out, wrap it up into a one-word tactic called `contrapos`.