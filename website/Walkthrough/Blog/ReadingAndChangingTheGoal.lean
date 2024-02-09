import Verso.Genre.Blog
import Mathlib.Tactic
open Verso Genre Blog


#doc (Page) "Reading and Changing the Goal" =>

# A first tactic

```leanInit readingAndChangingTheGoal
```

```lean readingAndChangingTheGoal show:=false
set_option linter.unusedVariables false
```

Here is a super simple tactic: the `do_nothing` tactic.

```lean readingAndChangingTheGoal
open Lean Elab Tactic

elab "do_nothing" : tactic => do
  return
```

We’ll see that, indeed, this tactic changes nothing about the proof state.  **Hover over the end-of-line bubbles** to see the goal state.
```lean readingAndChangingTheGoal
example : True := by
  do_nothing -- the goal here is still `True`
  trivial
```

Please feel free to **paste in these bits of code into your editor**, creating one big Lean file as we go!


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

# Modifying the context

Now we can read the goal.  Let’s modify it.

Let’s write a tactic that turns a theorem into its contrapositive.  First, let’s prove that a contrapositive tactic could work.
```lean readingAndChangingTheGoal
theorem ctrp {P Q : Prop} :
  (contra: ¬ Q → ¬ P) → (P → Q) :=
  by
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

# Comparing `macro` and `elab`

We noticed that `apply` works easily within a macro, but not within an elab.  It’s the same with lots of Lean tactics, for example, `sorry`.

To write `sorry` in an `elab`, you have to get a bit lower level, and use “admitGoal” and pass it an argument.
```lean readingAndChangingTheGoal
elab "my_sorry_elab" : tactic => do
  let goal ← getMainGoal
  admitGoal goal
```

To write `sorry` in a `macro`, you don’t have to remember it’s encoded internally as `Lean.Elab.admitGoal`.
```lean readingAndChangingTheGoal
macro "my_sorry_macro" : tactic =>
  `(tactic| sorry)
```

In general, `macro` lets you work at a higher level than `elab`, but you get less control.

As such, if your tactic doesn’t have any real programming logic, and is just conglomerating some existing tactics, as above, you should use `macro`.

If there’s a task at hand that requires some level of customization, you should use `elab`.

# Providing arguments to tactics

We can also provide arguments to a `macro` or `elab`.  Here’s an example where arguments come in handy.

Say we have `P → Q → True`.

It’s quick to contrapose `Q` and `True`:

```lean readingAndChangingTheGoal
example {P Q : Prop} : P → Q → True := by
  intro p
  contrapos -- `Q` and `True` have been contraposed
  simp
```

But more annoying to contrapose `P` and `True`.

```lean readingAndChangingTheGoal
example {P Q : Prop} : P → Q → True := by
  intro p q
  revert p
  contrapos -- `P` and `True` have been contraposed
  simp
```

Let’s create a tactic that will contrapose the conclusion with the given hypothesis `h`.
```lean readingAndChangingTheGoal
macro "contrapos_with" h:ident : tactic => `(tactic|
  (revert $h; contrapos)
)
```
We can test it out.

```lean readingAndChangingTheGoal
example {P Q : Prop} :  P → Q → True  := by
  intro p q
  contrapos_with q -- `Q` and `True` have been contraposed
  simp_all
```



```lean readingAndChangingTheGoal

example {P Q : Prop} :  P → Q → True  := by
  intro p q
  contrapos_with p -- `P` and `True` have been contraposed
  simp_all
```

And it works as expected.


## Providing tactics as arguments to tactics

So above, we provided an argument that was a proposition.

We can also provide an argument that is another tactic.  For example, this example from the [Lean 4 Metaprogramming Book](https://github.com/leanprover-community/lean4-metaprogramming-book) takes two tactics, runs the first one (which potentially creates more goals), then runs the second one on all the goals.

So without the tactic, you might have to do something like this:
```lean readingAndChangingTheGoal
example: 1=1 ∧ 2=2 := by
  constructor -- split into two goals:  1 = 1 and 2 = 2
  rfl; rfl  -- solve each one

```

But then you create this tactic…
```lean readingAndChangingTheGoal
macro "and_then" a:tactic b:tactic : tactic => `(tactic|
  ($a:tactic; all_goals $b:tactic)
)
```

…And you can do this:
```lean readingAndChangingTheGoal
example: 1=1 ∧ 2=2 := by
  and_then constructor rfl
```

# Creating more intuitive syntax for tactics

Instead of writing `and_then constructor rfl`, it might be more intuitive to write the above tactic as `constructor and_then rfl`.

This is where it’s helpful to create a `syntax` rule.

```lean readingAndChangingTheGoal
syntax tactic " and_then " tactic : tactic
macro_rules
| `(tactic| $a:tactic and_then $b:tactic) =>
    `(tactic| and_then $a $b)
```

Now we can write this tactic much more intuitively:
```lean readingAndChangingTheGoal
example: 1 = 1 ∧ 2 = 2 := by
  constructor and_then rfl
```



# Another way to create more intuitive syntax for tactics

We can avoid using `syntax` altogether in this particular case, and just declare the macro with the arguments fed in the appropriate places.

```lean readingAndChangingTheGoal
macro  a:tactic "and_then'" b:tactic : tactic => `(tactic|
  ($a:tactic; all_goals $b:tactic)
)
```

```lean readingAndChangingTheGoal
example: 1 = 1 ∧ 2 = 2 := by
  constructor and_then' rfl
```


This works just the same!
