import Verso.Genre.Blog
import Mathlib.Tactic
open Verso Genre Blog

#doc (Post) "Reading and Changing the Goal" =>

# A first tactic

```leanInit readingAndChangingTheGoal
```

Here is a super simple tactic: the `do_nothing` tactic.

```lean readingAndChangingTheGoal
open Lean Elab Tactic

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

# Modify the context

Now we can read the goal.  Let’s modify it.

Let’s write a tactic that turns a theorem into its contrapositive.  First, let’s prove that a contrapositive tactic could work.
```lean readingAndChangingTheGoal
theorem ctrp {P Q : Prop} : (¬ Q → ¬ P) → (P → Q) := by
  intro h
  rwa [not_imp_not] at h
```

Now, if we ever want to use this theorem, we can type `apply ctrp`.
```lean readingAndChangingTheGoal
example {P : Prop} : P → True := by
  apply ctrp
  simp
```

But since the line `apply ctrp` is so cumbersome to write out, lets wrap it up into a one-word tactic called `contrapos`.


## Writing a tactic — what doesn’t work

Now, we’ve been using `elab (name) : tactic => ...` to create tactics.
But `elab` is not very convenient to use if we are just planning on conglomerating a bunch of already-existing Lean tactics.

That is, the following code _doesn't_ work:
```lean readingAndChangingTheGoal error:=true
elab "contrapos" : tactic => do
  apply ctrp -- throws error!
```

That’s because there are a bunch of low-level configuration options you need to send to `apply` if you’re going to call it from within a tactic, and that’s a bit of a pain.

##  Writing a tactic — what does work

So, instead, when we want to conglomerate existing Lean tactics, we use ``macro``:
```lean readingAndChangingTheGoal
macro "contrapos" : tactic =>
  `(tactic| apply ctrp)
```

We can test it out.
```lean readingAndChangingTheGoal
example : P → True := by
  contrapos
  simp
```

So that’s “elaboration” and “macros” — we can use either to write Lean tactics.
