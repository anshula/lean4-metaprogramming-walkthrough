# Hands-on Lean 4 Tactic Writing



This is a tutorial on metaprogramming, or equivalently, writing tactics to help prove math theorems, in Lean 4.  

That is, instead of focusing on writing a_ formalized proof_ (programming), we focus on writing a _program that writes a formalized proof_ (metaprogramming).

## Code
- Here is the [full code](#) containing everything in the tutorial.
- Here is a short [”cheat sheet” containing helper functions ](#) you might find useful when metaprogramming in the future.

## Looking Ahead

By the end of the tutorial, you will have built a Lean tactic that takes an unnecessarily-weak theorem and turns it into a stronger theorem with an analogous proof (using an algorithm from the paper [ Generalization in Type Theory Based Proof Assistants](https://link.springer.com/content/pdf/10.1007/3-540-45842-5_14.pdf) by Oliver Pons). 
- For example, given the theorem that √2 is irrational….
	```python
	theorem sqrt_two_irrational : 
	  Irrational (sqrt 2) := ...
	```
	…this tactic will notice the proof never uses any properties of “2” besides that it is prime, and so it can generalize to the theorem that √p is irrational when p is prime.
	```python
	theorem sqrt_prime_irrational : 
	  ∀ (p : ℕ), Nat.Prime p → Irrational (sqrt p) := ...
	```




## Prerequisites

Before starting this tutorial, it’s helpful (but not absolutely necessary) to know:
- How to write theorems in a theorem-proving programming language (e.g. Coq, Isabelle, Lean, etc.).  If not, you can play the [Natural Number Game (for Lean 4)](https://adam.math.hhu.de/#/g/hhu-adam/NNG4).
- Basics about formalizing math (e.g. that types are propositions, and their terms are their proofs). If not, you can read some of the [Hitchiker’s Guide to Formal Verification (for Lean 4)](https://github.com/blanchette/logical_verification_2023/blob/main/hitchhikers_guide.pdf).

Another great resource on meta programming is the [Metaprogramming Videos (for Lean 3)](https://www.youtube.com/watch?v=o6oUjcE6Nz4)
(That is, this was approximately my background as I was writing the tutorial.)

## Setup

Make sure you have:
- Downloaded this project
- Downloaded mathlib with `VSCode > Command-Shift-P > Lean 4: Build Project`
- Downloaded the mathlib cache with `VSCode > Command-Shift-P > Lean 4: Fetch Mathlib Build Cache`

- Restarted Lean with `VSCode > Command-Shift-P > Lean Restart`

# Reading and Changing the Goal


## A first tactic



Here is a super simple tactic: the `do_nothing` tactic. 
```haskell
import Lean
open Lean Elab Tactic Meta Term

elab "do_nothing" : tactic => do
  return
```

Please feel free to paste in these bits of code into your editor, creating one big Lean file as we go!  We’ll see that, indeed, this tactic changes nothing about the proof state:
```haskell
example : True := by
  do_nothing
  trivial
```

Here it is in action:
![](Screen%20Shot%202024-01-18%20at%2010.40.49%20PM%20copy.jpg width="100%")

## Reading the context

Now, let’s create a tactic `print_goal` that reads what the current goal is. 
```python
elab "print_goal" : tactic => do
  let goal ← getMainGoal
  logInfo goal
```

Let’s test the tactic:
```python
example : 1+1=2 := by
  print_goal -- 1+1=2 
  trivial
```

And we get what we expect.
![](Screen%20Shot%202023-12-11%20at%206.51.50%20PM.png width="100%")

## Reading the context another way

The above “goal” is really just a variable referencing the goal.  It has type  `MVarId`.
![](Screen%20Shot%202023-12-11%20at%205.05.24%20PM.png width=400px)

To get the actual goal, you’d call `getType` on the variable (which gives you something of type `Expr`), and that will give you the actual goal expression:
```python
elab "print_goal_type" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  logInfo goalType
```

![](Screen%20Shot%202023-12-11%20at%205.05.46%20PM.png width=400px)

Using `print_goal` and `print_goal_type` both print the same thing through…
```python
example : True := by
  print_goal_type -- True
  trivial
```
![](Screen%20Shot%202024-01-18%20at%2010.46.48%20PM.png)
…since when we were printing the goal variable, `logInfo` had some magic inside it that knew we actually wanted to print the _relevant goal information_ stored in the variable.


## Getting types of objects in the context

Getting the actual type of the goal of takes another step — using `inferType`.
```python
import Lean
open Lean Elab Tactic Meta

elab "print_goal_type_type" : tactic => do
  let goal ← getMainGoal
  let goal_type ← goal.getType
  let goal_type_type ← inferType goal_type
  logInfo goal_type_type
```

If we test this out, we get what we expect — goals will typically be of type `Prop`.
```python
example : True := by
  print_goal_type_type -- Prop
  trivial

example : 1+1=2 := by
  print_goal_type_type -- Prop
  trivial
```

Here’s the last example above in action:	
![](Screen%20Shot%202023-12-11%20at%206.45.59%20PM.png)

Why do we use `getType` in the first case, and `inferType` in the second?
-  `getType` is for getting the type of variables (which is more or less straightforward, since types for variables are typically directly assigned).
- `inferType` is for getting the type of expressions (which is a bit trickier, therefore, the “infer”.  For example, you might have to look a bit into a particular instance of the multiplication operator to notice it is of type `ℕ → ℕ → ℕ`.)

## Modify the context

Now we can read the goal.  Let’s modify it.

Let’s write a tactic that turns a theorem into its contrapositive.  First, let’s prove that a contrapositive tactic could work.
```python
theorem ctrp {P Q : Prop} : (¬ Q → ¬ P) → (P → Q) := by 
  intros h p; by_contra nq; apply h nq p
```

We can test it out.
```
example {P : Prop} : P → True := by
  apply ctrp; simp
```

And it does what we expect.
![](Screen%20Shot%202024-01-18%20at%2011.06.08%20PM.png)

Now we want to take the line `apply ctrp`, and, because it is so cumbersome to write out, wrap it up into a one-word tactic called `contrapos`.

### What doesn’t work

Now, we’ve been using `elab (name) : tactic => ...` to create tactics.  

But `elab` is not very convenient to use if we are just planning on conglomerating a bunch of already-existing Lean tactics.  

That is, the following code _doesn't_ work:
```python
elab "contrapos" : tactic => do
  apply ctrp -- throws error!
```
That’s because there are a bunch of low-level configuration options you need to send to `apply` if you’re going to call it from within a tactic, and that’s a bit of a pain.

### What does work 

So, instead, when we want to conglomerate existing Lean tactics, we use `macro`:
```python
macro "contrapos" : tactic => 
  `(tactic| apply ctrp)
```

We can test it out.
```
example : P → True := by
  contrapos
  simp
```

And there are no surprises.

![](Screen%20Shot%202024-01-18%20at%2011.15.27%20PM.png)
So that’s “elaboration” and “macros” — we can use either to write Lean tactics.

## Macro vs Elab

We noticed that `apply`works easily within a macro, but not within an elab.  It’s the same with lots of Lean tactics, for example, `sorry`.

To write `sorry` in an `elab`, you have to get a bit lower level, and use “admitGoal” and pass it an argument.
```python
elab "my_sorry_elab" : tactic => do
  let goal ← getMainGoal
  admitGoal goal
```

To write “sorry” in a `macro`, you don’t have to remember it’s encoded internally as `Lean.Elab.admitGoal`.
```python
macro "my_sorry_macro" : tactic =>
  `(tactic| sorry)
```

In general, `macro` lets you work at a higher level than `elab`, but you get less control. 

As such, if your tactic doesn’t have any real programming logic, and is just conglomerating some existing tactics, as above, you should use `macro`.

If there’s a task at hand that requires some level of customization, you should use `elab`.

## Providing arguments to tactics

We can also provide arguments to a `macro` or `elab`.  Here’s an example where arguments come in handy.

Say we have $P \implies Q  \implies R.$

It’s quick to contrapose Q and R:
![](Screen%20Shot%202023-12-11%20at%2010.22.47%20PM.png)
But more annoying to contrapose P and R.
![](Screen%20Shot%202023-12-11%20at%2010.24.46%20PM.png)

Let’s create a tactic that will contrapose the conclusion with the given hypothesis `h`.
```python
macro "contrapos_with" h:ident : tactic => `(tactic|
  (revert $h; contrapos; intros)
)
```
We can test it out.
```python
example {P Q : Prop} :  P → Q → True  := by
  intro p q
  contrapos_with p 
```
And it works as expected.
![](Screen%20Shot%202024-01-18%20at%2011.25.36%20PM.png)
![](Screen%20Shot%202024-01-18%20at%2011.25.52%20PM.png)


## Providing tactics as arguments to tactics

So above, we provided an argument that was a proposition.

We can also provide an argument that is another tactic.  For example, this example from the [Lean 4 Metaprogramming Book](https://github.com/leanprover-community/lean4-metaprogramming-book) takes two tactics, runs the first one (which potentially creates more goals), then runs the second one on all the goals.

So without the tactic, you might have to do something like this:
```python
example: 1=1 ∧ 2=2 := by
  constructor -- split into two goals:  1 = 1 and 2 = 2
  rfl; rfl  -- solve each one

```

But then you create this tactic…
```python
macro "and_then" a:tactic b:tactic : tactic => `(tactic|
  ($a:tactic; all_goals $b:tactic)
)
```

…And you can do this:
```python
example: 1=1 ∧ 2=2 := by
  and_then constructor rfl
```
## Creating more intuitive syntax for tactics

Instead of writing `and_then constructor rfl`, it might be more intuitive to write the above tactic as `constructor and_then rfl`.

This is where it’s helpful to create a `syntax` rule.

```python
syntax tactic " and_then " tactic : tactic
macro_rules
| `(tactic| $a:tactic and_then $b:tactic) =>
    `(tactic| and_then $a $b)


```

Now we can write this tactic much more intuitively:
```
example: 1 = 1 ∧ 2 = 2 := by
  constructor and_then rfl
```
# Reading and Changing the Hypotheses

All of the exercises here are going to build up to writing an “assumption” tactic — one that looks at all the hypotheses, and if any matches the goal, successfully proves it using that hypothesis.

## Reading the context — hypotheses

So now we can read and modify the _goal_ of a theorem.

What about the _hypotheses_?

All the hypotheses are stored in the local context, which is retrieved through `getLCtx`.  

Some of them are not ones a human would think about when solving a theorem, that is, they are “implementation details” (e.g. the name of the theorem itself) and we skip them.

```python
elab "print_hypotheses" : tactic => do
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hyp_name := ldecl.userName 
    let hyp_type := ldecl.type 
    logInfo m!"Name: '{hyp_name}'  Type: '{hyp_type}' "
```

We can test it out a theorem which has hypotheses that $a=2$ and $b=3$.
```python
example (a b : ℕ) (h1 : a = 2) (h2: b = 3) : a+b=5 := by
  print_hypotheses 
```

And we get all the relevant hypotheses.
![](Screen%20Shot%202024-01-19%20at%203.42.02%20PM.png)

### What goes wrong

Our tactic doesn’t seem to work when we add another hypothesis. 
```Lean
example (a b : ℕ) (h1 : a = 2) (h2: b = 3) : a+b=5 := by
  print_hypotheses -- prints h1 and h2
  have h3 : b-a = 1 := by {rw [h1, h2]}
  print_hypotheses -- still prints only h1 and h2
```

 Our tactic doesn’t print the newest hypothesis.
![](Screen%20Shot%202024-01-19%20at%203.45.29%20PM.png)

### How to fix it

The new hypotheses are actually associated to the current goal.

So to get it, we need to modify our function to retrieve all hypotheses from the goal, with `(← goal.getDecl).lctx`.

```python
elab "print_hypotheses" : tactic => do
  let goal ← getMainGoal  -- the dynamically generated hypotheses are associated with this particular goal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    let hyp_name := ldecl.userName
    let hyp_type := ldecl.type
    logInfo m!"Name: '{hyp_name}'  Type: '{hyp_type}' "
```

Now when we test it out…
```Lean
example (a b : ℕ) (h1 : a = 2) (h2: b = 3) : a+b=5 := by
  print_hypotheses -- prints h1 and h2
  have h3 : b-a = 1 := by {rw [h1, h2]}
  print_hypotheses -- prints h1 and h2 and h3
```
… it does update to include the newest hypothesis.
![](Screen%20Shot%202024-01-19%20at%203.49.38%20PM.png)


## Extracting code out into a separate definition

At this point, the tactics have gotten longer, and before we start adding onto this tactic in the next section, we might want to move out parts of the tactic into bits we can reuse in other tactics.

We can do this as long as we move out the side-effect-causing tasks into a function that returns a monad, either `MetaM` or `TacticM`. (We’ll get into the differences between them later).

```python
def printHypotheses : TacticM Unit := do
  let goal ← getMainGoal  -- the dynamically generated hypotheses are associated with this particular goal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    let hypName := ldecl.userName
    let hypType := ldecl.type
    logInfo m!"Name: '{hypName}'  Type: '{hypType}'"
```

We can still call `print_hypotheses` as normal as long as we also create an `elab` that tells Lean which function to call when the user types `print_hypotheses`.
```python
elab "print_hypotheses" : tactic => do
  printHypotheses
```


## What to return?

The function we used above looked like
```Lean
def printHypotheses : TacticM Unit := do
	...
```

If we ever write a tactic that doesn’t return anything (and perhaps, just prints something to the screen), it will have the `Unit` return type.

The `Unit` serves the purpose that `void` does in other programming languages — it tells us the function isn’t going to return anything interesting.

## MetaM vs TacticM

Our `printHypotheses` function worked when we had it return a `TacticM`.

But if we change it to use `MetaM`, it fails.
![](Screen%20Shot%202024-01-19%20at%204.24.29%20PM.png)
That’s because working within `TacticM` gives us access to the current goals — if we try to access the goals outside `TacticM`, we get an error.

In fact, `TacticM` has access to everything `MetaM` has access too, plus goals.

## So why ever use MetaM?

So if `TacticM` is just `MetaM` but more, why would we ever use `MetaM`?

The following code works if you use `MetaM`…
```js
/-- Check if there’s any theorem called `riemannHypothesis` in the context. -/
def lookIntoEnvironment  : MetaM Unit := do
  let env ← getEnv
  dbg_trace (env.contains `riemannHypothesis)

#eval lookIntoEnvironment
```
… but fails if you use `TacticM`. 
![](Screen%20Shot%202024-01-19%20at%204.29.39%20PM.png)

What’s going on?

If we ever want to check how our functions work using `#eval` statements, they need to implement the `MetaEval` class — which allows output to be easily evaluated.  `MetaM` implements this class,  but `TacticM` doesn’t.

So, we ideally want to return something of type `TacticM` only when we really need it.

In summary, here are the perks of each:
- `MetaM` lets you access most of the local context (including declared metavariables, therefore the name `MetaM`).
- `TacticM` lets you access anything in `MetaM`, and also the current goals you have in the theorem the tactic is being used in.  

And here are the downsides:
- We can’t use a `MetaM` function to peer into a goal — `MetaM` doesn’t allow us access to a list of goals. 
- We can’t call a `TacticM` function from `#eval`.


## Getting hypotheses as a list of declarations

Suppose we do want to return something interesting, though?

Instead of printing text to screen, we might want to actually return the list of hypotheses (so we can do stuff with it, like, checking to see if any of them match the goal).  So let’s do that now.

```python
def getHypotheses : TacticM (List LocalDecl) := do
  let mut hypotheses : List LocalDecl := []
  let goal ← getMainGoal  -- the dynamically generated hypotheses are associated with this particular goal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    hypotheses := ldecl :: hypotheses
  return hypotheses
```

Note that instead of returning a `Unit`, we return a `List LocalDecl`.  

And we wrap it all up in the `TacticM` monad so we can access the goal.

## Getting hypotheses as a list of expressions

The actual human-readable part of the hypothesis isn’t its declaration, though.

It’s the _type_ of the hypothesis.

So, let’s write a method to get that.
```Lean
def getHypothesesTypes : TacticM (List Expr) := do
  return (← getHypotheses).map (fun hypothesis => hypothesis.type)

elab "print_hypotheses_types" : tactic => do
  let types ← getHypothesesTypes
  logInfo ("Hyp types:" ++ types)
```

Now if we test it out…
```Lean
example (a b : ℕ) (h1 : a = 2) (h2: b = 3) : a+b=5 := by
  print_hypotheses_types 
  simp [h1, h2]
```

…we see that this tactic get us the relevant, human-readable information about hypotheses.
![](Screen%20Shot%202024-01-19%20at%204.59.06%20PM.png)
Notice that `getHypothesesTypes` returns `List Expr`.  All of the actual mathematical expressions in Lean need to be in type `Expr` to be manipulated.

## Getting the goal as an expression

Now how do we get the human-readable part of the goal?  That’s the goal _type_, and we can access it using `getGoalType` below.

```python
/--  Tactic to return goal variable -/
def getGoalVar : TacticM MVarId := do
  return ← getMainGoal

/--  Tactic to return goal declaration-/
def getGoalDecl : TacticM MetavarDecl := do
  return ← getMainDecl -- (← getGoalVar).getDecl

/--  Tactic to return goal expression (the type) -/
def getGoalType : TacticM Expr := do
  return ← getMainTarget -- (← getGoalDecl).type or (← getGoalVar).getType
```

Note that there were three “layers” we had to peel back to get to the relevant information about the goal:
- Running `← getMainGoal` gets you the **metavariable** pointing to the goal (just a variable name and a pointer)…
- …then running `getDecl` on the metavariable gets you the **declaration** (the object that actually contains lots of information about the goal)…
- then running `type` on the declaration gets you the **expression** (the thing that actually contains relevant, human-readable information about the goal e.g. the expression `1+1=2`).


## Comparing hypotheses to the goal with an “assumption” tactic
Finally, using the functions we made to read the goal and hypothesis, we are able to make an “assumption” tactic.

```python
elab "assump" : tactic => do
  let goal_decl ← getGoalDecl
  for hyp_decl in ← getHypotheses do
    if ← isDefEq hyp_decl.type goal_decl.type then 
      closeMainGoal hyp_decl.toExpr
```

We find our function closes the goal when the conclusion is in the hypothesis, and does nothing if not.  Just as expected!
```
example {P : Prop} (p : P): P := by
  assump -- works

example {P : Prop} : P := by
  assump -- does nothing
```

Notice that when we `closeMainGoal` we need to pass it the expression `hyp_decl.toExpr` (the proof of the hypothesis) rather than the expression `hyp_decl.type` (the statement of the hypothesis).    They’re both expressions, but only the proof works as an argument to `closeMainGoal`.

In this example:
- `hyp_decl.toExpr` is the expression “p” (the “proof” of the proposition P)
- `hyp_decl.type` is the expression “P” (the proposition P.)

We need to close the main goal with `hyp_decl.toExpr`  because we actually need the _term_ (the proof of P), rather than the _type_ (the proposition P).

## Throwing errors in the “assumption” tactic

Currently, if there are no matching assumptions, the `assump` tactic silently fails, by not changing the proof state.

We can make a more elaborate version of this tactic by having it throw an error if there are no matching assumptions.

```Lean
elab "assump'" : tactic => do
  let goal_decl ← getGoalDecl

  -- check if any of the hypotheses matches the goal.
  for hyp_decl in ← getHypotheses do
    if ← isDefEq hyp_decl.type goal_decl.type then 
      closeMainGoal hyp_decl.toExpr
      return
  
  -- if no hypothesis matched, this tactic fails.
  throwError "No matching assumptions."  
```

Now, if we test it out…
```python
example {P : Prop} (p : P): P := by
  assump' -- works
	
example {P : Prop} : P := by
  assump' -- throws error "No matching assumptions."
```
…we get an error thrown if there are no matching assumptions.
![](Screen%20Shot%202024-01-19%20at%208.02.03%20PM.png)


## Rewriting the “assumption” tactic using `findM?`

There’s already a function called `findM?` which implements the sort of thing we did — looping over a bunch of items and returning one when a property is true.

```Lean
elab "assump''" : tactic => do
  let goal_decl ← getGoalDecl
  let hyp_decls ← getHypotheses

  -- check if any of the hypotheses matches the goal.
  let matching_hyp_decl ← hyp_decls.findM? (
    -- when isDefEq returns true, we return the corresponding hyp_decl
    -- if it never does, we return none
    fun hyp_decl => return ← isDefEq hyp_decl.type goal_decl.type
  )
  
   -- close the goal, or fail if no hypothesis matched
  match matching_hyp_decl with
  | some hyp_decl => closeMainGoal hyp_decl.toExpr
  | none => throwError "No matching assumptions."   
```

Note that this function requires the use of `(Option.)some` and `(Option.)none`.  This is because `findM?` must always return something of a consistent type. So it will sometimes return a hypothesis (wrapped in `Option.some`, if the hypothesis is found), and sometimes nothing (an an `Option.none`, if the hypothesis is not found).

# Adding Goals and Hypotheses


## Adding a new goal

_Creating a goal_ in Lean is really _creating a metavariable_ (a variable whose value a.k.a proof isn’t known yet).
_Proving a goal_ in Lean is _assigning a value a.k.a proof to that metavariable_.

We can extract out the basics of goal creation into a helper tactic: `createGoal`.
```js
def createGoal (goalType : Expr) : TacticM Unit := do
  let goal ← mkFreshExprMVar goalType
  appendGoals [goal.mvarId!]
```

We can see this in action here.  If we want our goal to be “find an instance of type Nat”, we create a metavariable with type “Nat”, like so:
```js
elab "create_nat_goal" : tactic => do
  let goalType := (Expr.const ``Nat []) -- make the goal to find an instance of type "Nat"
  createGoal goalType

example : 1 + 2 = 3 := by
  create_nat_goal 
  simp; use 5
```
![](Screen%20Shot%202024-01-19%20at%208.57.54%20PM.png)

If instead, we want to create a goal to be  “prove $0=0$”, then we create a metavariable with type “$0=0$”.
```js
elab "create_reflexivity_goal" : tactic => do
  let goalType ← mkEq (toExpr 0) (toExpr 0) -- make the metavariable goal to prove that "0 = 0"
  createGoal goalType

example : 1 + 2 = 3 := by
  create_reflexivity_goal; swap
  simp; simp
```
![](Screen%20Shot%202024-01-19%20at%208.57.07%20PM.png)


## Adding a new hypothesis

Similarly, we can extract out the basics of hypothesis creation into a helper tactic: `createHypothesis`.
```js
def createHypothesis (hypType : Expr) (hypProof : Expr) : TacticM Unit := do
  let hypName := `h
  let hyp : Hypothesis := { userName := hypName, type := hypType, value := hypProof }
  let (_, new_goal) ← (←getGoalVar).assertHypotheses (List.toArray [hyp])
  setGoals [new_goal]
```

Here’s an example of adding a hypothesis that looks like `h: ℕ`
```js
elab "create_nat_hypothesis" : tactic => do
  let hypType := Expr.const ``Nat []
  let hypProof :=  (toExpr 0) -- use 0 as a term of type Nat
  createHypothesis hypType hypProof

example : 1 + 2 = 3 := by
  create_nat_hypothesis 
  simp
```
![](Screen%20Shot%202024-01-19%20at%208.59.32%20PM.png)

Here’s an example of adding a hypothesis that is a proposition `0=0`.
```js
elab "create_reflexivity_hypothesis" : tactic => do
  let hypType ← mkEq (toExpr 0) (toExpr 0) -- make the metavariable goal to prove that "0 = 0"
  let hypProof := Lean.mkAppN (.const ``Eq []) #[(toExpr 0), (toExpr 0)] -- proof that Eq 0 0
  createHypothesis hypType hypProof

example : 1 + 2 = 3 := by
  create_reflexivity_hypothesis
  simp
```
![](Screen%20Shot%202024-01-19%20at%209.00.32%20PM.png)


## Adding optional arguments

We may want to be able to name our hypothesis when we want to, but leave it as the default when we don’t particularly care.

We can achieve this by making the `hypName` parameter optional by adding an`Option` to it…

```js
def createHypothesis (hypType : Expr) (hypProof : Expr) (hypName : Option Name := none) : TacticM Unit := do
  ...
```

… and retrieving that value using `getD` (“get with default”, which gets the value wrapped in the`Option`, but if there’s nothing in there, uses the default value given.)

```js
def createHypothesis (hypType : Expr) (hypProof : Expr) (hypName? : Option Name := none) : TacticM Unit := do
  let hypName := hypName?.getD `h -- use the name given first, otherwise call it `h
  ...
```

It is a convention to use a `?` at the end of optional arguments, but it doesn’t actually have impact on the code parsing or execution.

Now, we can see that if we specify we want the name of the new hypothesis to be `x`…
```js
elab "create_nat_hypothesis" : tactic => do 
  ...
  createHypothesis hypType hypProof `x
  ...
```

…we get that to happen!
![](Screen%20Shot%202024-01-19%20at%208.58.40%20PM.png)


# Introducing Expressions

We know how to read and change the context in small ways.

Now, to write _really_ powerful tactics in Lean, to really customize _how_ we change the context, we need to work with “expressions.” 


## Looking ahead

By the end of the next few sections, we should be able to take in a mathematical statement (e.g. $2+3=5$) identify all natural number subexpressions in an expression ($2$,$3$, $2+3$,and $5$).

And what’s the point of that?  It sets us up for the next section.

By the end of the next section, we should be able to generalize a particular natural number subexpression in a statement (e.g $2+3=5$) to an arbitrary constant of that type, and rewrite the statement accordingly (e.g. $\exists n : \mathbb{N}, n+3=5$). 

 This will pave the way for our algorithm that automatically generalizes unnecessarily weak theorems (the big project of this course.) 

## What are expressions?

Before a piece of code is compiled into Lean…
- it starts as a **string** that we type into the computer…
- …which as long as it has all the necessary context can later be turned into an **expression**…
- …which then can be compiled into code called a **term**.

So here are expressions…
```js
def zero := Expr.const ``Nat.zero []

def one := Expr.app (.const ``Nat.succ []) zero
```


And here is how we turn them into fully elaborated code (that is, a term).
```js
elab "zero" : term => return zero

elab "one" : term => return one
```

The benefit of working with expressions is that they’re easy to modify at a low-level.  

The benefit of working with terms is they are actual pieces of code that can be used to prove theorems.

## Where do we use expressions?

We previously constructed expressions when we were creating hypotheses and goals.

The only way to _create_ mathematical statements is to tell Lean the propositions (as expressions), and the only way to _prove_ them is to tell Lean the proofs (as expressions).

For example, we used `mkEq (toExpr 0) (toExpr 0)` to create the expression for the term `0=0`.
![](Screen%20Shot%202024-01-19%20at%2010.25.34%20PM.png)

## Converting code to expressions

When we turn a natural number into an expression, we’re actually doing something like this:
```js
def natExpr: Nat → Expr
| 0 => Expr.const ``Nat.zero []
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)

#eval natExpr 2
```

But luckily, there’s a function `toExpr`…
```js
#eval toExpr 2
```

…that does the same thing.
```js
#eval isDefEq (toExpr 2) (natExpr 2) -- true
```
## Converting code to expressions: limitations

Unfortunately,`toExpr`only works to express single values.  

So this works…
![](Screen%20Shot%202024-01-19%20at%2010.36.37%20PM.png)
And this doesn’t.
![](Screen%20Shot%202024-01-19%20at%2010.37.02%20PM.png)

Instead, if we want the expression `2+2=4`, we have to write it out laboriously...as we’ll do in the following puzzle.

## Pretty-printing expressions

Before we get into the upcoming puzzle, it’s helpful for debugging to be able to print out expressions nicely.

We can use `ppExpr` (pretty-print expression) for that, and extract it out into this helper function.
```js
def printPrettyExpression (e : Expr) : MetaM Unit := do
  dbg_trace "{←ppExpr e}"
```

Now what looked like this…
![](Screen%20Shot%202024-01-19%20at%2010.36.37%20PM-1.png)

…just looks like this:
![](Screen%20Shot%202024-01-19%20at%2011.06.35%20PM.png)


## Puzzle — Constructing Expressions

Here’s what we know:
- `mkEq (toExpr 0) (toExpr 0)` gives us the expression `0=0`
- ``Expr.app (.app (.const `Nat.add []) (toExpr 1)) (toExpr 2)`` gives us the expression `1+2`. (You first apply addition to 1, to create a partially applied function, then you apply it to 2.)

See if you can use the above to write out the expression `2+3=5`.
```js
#eval do {  -- should print out 2+3=5
  let two_plus_three_equals_five : Expr ← (FILL THIS OUT)
  printPrettyExpression $ two_plus_three_equals_five
}
```

The [exercise is here](https://lean.math.hhu.de/#code=import%20Lean%0Aopen%20Lean%20Elab%20Tactic%20Meta%20Term%0A%0A%2F--%20Print%20out%20the%20expression%20in%20a%20human-readable%20way%20%20--%2F%0Adef%20printPrettyExpression%20(e%20%3A%20Expr)%20%3A%20MetaM%20Unit%20%3A%3D%20do%0A%20%20dbg_trace%20%22%7B%E2%86%90ppExpr%20e%7D%22%0A%0A%2F--%20Some%20helpful%20examples%20to%20reference%20--%2F%0A%23eval%20do%20%7BprintPrettyExpression%20%24%20%E2%86%90%20mkEq%20(toExpr%200)%20(toExpr%200)%7D%0A%23eval%20do%20%7BprintPrettyExpression%20%24%20Expr.app%20(.app%20(.const%20%60Nat.add%20%5B%5D)%20(toExpr%200))%20(toExpr%201)%7D%0A%0A%2F--%20The%20puzzle%20--%2F%0A%23eval%20do%20%7B%20--%20should%20print%20out%202%2B3%3D5%0A%20%20let%20two_plus_three_equals_five%20%3A%20Expr%20%E2%86%90%20--%20FILL%20THIS%20OUT%0A%20%20printPrettyExpression%20%24%20two_plus_three_equals_five%0A%7D%20) in the Lean 4 web editor.
The [answer is here](https://lean.math.hhu.de/#code=import%20Lean%0Aopen%20Lean%20Elab%20Tactic%20Meta%20Term%0A%0A%2F--%20Print%20out%20the%20expression%20in%20a%20human-readable%20way%20%20--%2F%0Adef%20printPrettyExpression%20(e%20%3A%20Expr)%20%3A%20MetaM%20Unit%20%3A%3D%20do%0A%20%20dbg_trace%20%22%7B%E2%86%90ppExpr%20e%7D%22%0A%0A%2F--%20Some%20helpful%20examples%20to%20reference%20--%2F%0A%23eval%20do%20%7BprintPrettyExpression%20%24%20%E2%86%90%20mkEq%20(toExpr%200)%20(toExpr%200)%7D%0A%23eval%20do%20%7BprintPrettyExpression%20%24%20Expr.app%20(.app%20(.const%20%60Nat.add%20%5B%5D)%20(toExpr%200))%20(toExpr%201)%7D%0A%0A%2F--%20The%20Puzzle%20--%2F%0A%23eval%20do%20%7B%20--%20should%20print%20out%202%2B3%3D5%0A%20%20let%20two_plus_three_equals_five%20%3A%20Expr%20%E2%86%90%20mkEq%20%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20(Expr.app%20(.app%20(.const%20%60Nat.add%20%5B%5D)%20(toExpr%202))%20(toExpr%203))%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20(toExpr%205)%3B%0A%20%20printPrettyExpression%20%24%20two_plus_three_equals_five%0A%7D%20) is in the Lean 4 web editor.

## Converting code to expressions: a helper function

Is there an easier way to write out Lean expressions?

What’s actually happening is that the string `"@HMul.hMul Nat Nat Nat instHMul"`  is `Syntax`.  And to go from `Syntax` to `Expr`, we need to use `elabTerm`.  (The graphics below are from [Evgenia Karunus’s website](https://lakesare.brick.do/metaprogramming-in-lean-BEwZboNyq9ZO)).
![](Screen%20Shot%202023-12-28%20at%206.18.22%20PM.png)

This is a part of the Lean compilation process.  
![](Screen%20Shot%202023-12-28%20at%206.42.09%20PM.png)

So it might be handy to create a function that takes in the syntax, and outputs it as an expression, using `elabTerm`.

```js
def syntaxToExpr (e : TermElabM Syntax) : TermElabM Expr := do
  let e ← elabTermAndSynthesize (← e) none
  return e
```

Then, to make sure Lean parses the string we give it as `Syntax`, we need to wrap it with a ```()``
```js
#eval syntaxToExpr `(2+3=5)
```

And indeed, we get the long expression that we’d expect.
![](Screen%20Shot%202024-01-22%20at%2011.32.28%20AM.png)

Note that in the above function, instead of using the `TacticM` or `MetaM` monad, we use an elaboration monad: `TermElabM`.

## Converting code to expressions: an even better way

Before, we had to convert a term to syntax using backtick ```(...)`` notation.
```js
#eval syntaxToExpr `(2+3=5)
```

Suppose you’d want to find the expression without using backtick ```(...)`` notation that converts a term to syntax…like here:
```js
#term_to_expr (2+3=5)
```

We can create that using a `command`.   While a `tactic` can be called within a proof, a `command` can be called outside the context of a proof.
```js
elab "#term_to_expr" t:term : command => do
  let e ← liftTermElabM (Term.elabTerm t none)
  logInfo m!"The expression corresponding to {t} is:\n\n{repr e}"
```

Now when we test it out…
```js
#term_to_expr (2+3=5)
```

…we get the expected result.
![](Screen%20Shot%202024-01-22%20at%2011.36.19%20AM.png)

Why did we have to include the `liftTermElabM` part above?  We get into that in the next section.

## A common error:  switching between monads

An error you’ll likely encounter a lot has the form: `Has type MonadA (...) but is expected to have type MonadB (...)`.

For example, if we had tried to write the code above as 
```js
elab "#term_to_expr" t:term : command => do
  let e ← Term.elabTerm t none
  logInfo m!"The expression corresponding to {t} is:\n\n{repr e}"
```

We would have gotten an error.
![](Screen%20Shot%202024-01-22%20at%2011.37.40%20AM.png)

Since we are writing a `command`, we are working within the `CommandElabM` monad.

But `Term.elabTerm` wraps its output in a `TermElabM` monad.

So when Lean sees the `←` it is confused, because it thinks it should be unwrapping a `TermElabM`.

To unwrap and rewrap the right way, we use `lift`.   That is, we move to the `TermElabM` monad using `liftTermElabM`.

```js
elab "#term_to_expr" t:term : command => do
  let e ← liftTermElabM (Term.elabTerm t none)
  logInfo m!"The expression corresponding to {t} is:\n\n{repr e}"
```
## Fixing appearances of expressions 

Sometimes, what you’ll see in the proof context will look too much like an “expression”, rather than a fully elaborated term.

For example, this is the context when I use`Expr.const ``Nat.zero` to build the `goalType` in `createGoal`.
![](Screen%20Shot%202023-12-22%20at%201.41.31%20PM.png height=120px)
But, this is the goal when I use `toExpr 0` to build the goalType.
![](Screen%20Shot%202023-12-22%20at%201.42.04%20PM.png height=120px)
Both are provable by `simp`, but the second looks prettier.

And that’s because `toExpr 0` is actually a much more elaborate expression than ``Expr.const ``Nat.zero``:
![](Screen%20Shot%202023-12-22%20at%201.43.28%20PM.png)

So, if your expressions are ever looking too “expression-y” in the context, try to use `toExpr` to make sure they are fully elaborated.

## Converting Expressions to Code with `evalExpr`

So we now know how to convert code to expressions using `elab`.

Next, we’ll go the opposite direction, converting expressions to code using `eval`.  That is, we can see what these expressions actually are as Lean objects by running `#eval` or `evalExpr`.

For example, the output of our previous `#eval sumExpr 1 2` was
```js
Lean.Expr.app
  (Lean.Expr.const `Nat.succ [])
  (Lean.Expr.app
    (Lean.Expr.const `Nat.succ [])
    (Lean.Expr.app (Lean.Expr.const `Nat.succ []) (Lean.Expr.const `Nat.zero [])))
```

But ideally we’d want some easy way to make sure this just evaluates to “3”, in actual Lean code.  To turn an expression into Lean code, we use `evalExpr`.

The arguments to `evalExpr` are as follows:
- the actual type it should evaluate to (e.g. a Nat)
- the type it should evaluate to in Expr form (e.g. the Expression for a Nat)
- the actual value (e.g. the Expression for 1 + 2).

```js
def expectedType := Expr.const ``Nat []
def value := (sumExpr 1 2)

#eval evalExpr Nat expectedType value
```

And indeed, we get the output `3`.
![](Screen%20Shot%202023-12-12%20at%201.45.04%20PM.png)

## Converting Expressions to Code with `elab`

We just converted an expression to code using `evalExpr`.

We can more succinctly convert an expression to code using `elab`.

```js
elab "sumExpr12" : term => return (sumExpr 1 2)
#eval sumExpr12
```

And indeed, we again get the output `3`.
![](Screen%20Shot%202023-12-12%20at%202.47.55%20PM.png)


# Manipulating Expressions

Let’s work more deeply with expressions.

## Getting types of expressions — constants 

Remember that we’ve created expressions like this:
```js
def zero := Expr.const ``Nat.zero []

def pi := Expr.const ``Real.pi []
```

It turns out, we can check if a given expression is a constant (e.g. a natural number or a real number) using `isConst`.
```js
#eval zero.isConst  -- true, is a natural number constant

#eval pi.isConst    -- true, is a real number constant
```

But what if we want more detail than just “is constant”?  What if we want to distinguish between whether the expression is a natural number constant or a real number constant?  

That’s what we’ll do in the next puzzle.

## Puzzle - Getting types of expressions

Try to come up with the code for checking if an expression is a natural number.
```js
def isNat (e: Expr): MetaM Bool := do
  let type_expr ← inferType e
  dbg_trace "The type expression is: {repr type_expr}"
  return sorry
```

Hint: Look at the output of the following commands:
```js
#eval inferType zero  				-- Lean.Expr.const `Nat []
#eval inferType pi    				-- Lean.Expr.const `Real [] 
#eval (Expr.const `Nat []).isConstOf `Nat 	-- true
#eval (Expr.const `Nat []).isConstOf `Real 	-- false
```

Check it worked using these evals
```js
#eval isNat zero -- should be true
#eval isNat pi   -- should be false
```

The [exercise is here](https://lean.math.hhu.de/#code=import%20Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic%20%2F-%20%CF%80%20-%2F%0Aopen%20Lean%20Elab%20Tactic%20Meta%0A%0Adef%20zero%20%3A%3D%20Expr.const%20%60%60Nat.zero%20%5B%5D%0Adef%20pi%20%3A%3D%20Expr.const%20%60%60Real.pi%20%5B%5D%0A%0A%23eval%20zero.isConst%20%20--%20true%2C%20is%20a%20natural%20number%20constant%0A%23eval%20pi.isConst%20%20%20%20--%20true%2C%20is%20a%20real%20number%20constant%0A%0A%23eval%20inferType%20zero%20%20--%20Lean.Expr.const%20%60Nat%20%5B%5D%0A%23eval%20inferType%20pi%20%20%20%20--%20Lean.Expr.const%20%60Real%20%5B%5D%0A%0A%23eval%20(Expr.const%20%60Nat%20%5B%5D).isConstOf%20%60Nat%20--%20true%0A%23eval%20(Expr.const%20%60Nat%20%5B%5D).isConstOf%20%60Real%20--%20false%0A%0Adef%20isNat%20(e%3A%20Expr)%3A%20MetaM%20Bool%20%3A%3D%20do%0A%20%20let%20type_expr%20%E2%86%90%20inferType%20e%0A%20%20return%20sorry%0A%0A%23eval%20isNat%20zero%0A%23eval%20isNat%20pi) in the Lean 4 web editor.
The [answer is here](https://lean.math.hhu.de/#code=import%20Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic%20%2F-%20%CF%80%20-%2F%0Aopen%20Lean%20Elab%20Tactic%20Meta%0A%0Adef%20zero%20%3A%3D%20Expr.const%20%60%60Nat.zero%20%5B%5D%0Adef%20pi%20%3A%3D%20Expr.const%20%60%60Real.pi%20%5B%5D%0A%0A%23eval%20zero.isConst%20%20--%20true%2C%20is%20a%20natural%20number%20constant%0A%23eval%20pi.isConst%20%20%20%20--%20true%2C%20is%20a%20real%20number%20constant%0A%0A%23eval%20inferType%20zero%20%20--%20Lean.Expr.const%20%60Nat%20%5B%5D%0A%23eval%20inferType%20pi%20%20%20%20--%20Lean.Expr.const%20%60Real%20%5B%5D%0A%0A%23eval%20(Expr.const%20%60Nat%20%5B%5D).isConstOf%20%60Nat%20--%20true%0A%23eval%20(Expr.const%20%60Nat%20%5B%5D).isConstOf%20%60Real%20--%20false%0A%0Adef%20isNat%20(e%3A%20Expr)%3A%20MetaM%20Bool%20%3A%3D%20do%0A%20%20let%20type_expr%20%E2%86%90%20inferType%20e%0A%20%20return%20(type_expr.isConstOf%20%60Nat)%0A%0A%23eval%20isNat%20zero%0A%23eval%20isNat%20pi) is in the Lean 4 web editor.

## Printing for debugging

As our functions are getting more complicated, it would be nice to have a way to debug what’s going on in the middle of them.  

So, consider our previous function determining whether `e` is a natural number.  We can debug it with `dbg_trace`.

```js
def isNatDebug (e: Expr): MetaM Unit := do
  let type_expr ← inferType e
  dbg_trace "The type expression is: {type_expr}"

#eval isNatDebug zero 
```

Unfortunately, what the above prints out is that `type_expr` is a `Nat`.  
![](Screen%20Shot%202023-12-12%20at%205.10.21%20PM.png)

Ideally,  while debugging an expression, we want to see the raw syntax tree of that expression — we don’t want it to be automatically compiled.  We want to check whether `type_expr` looks like ``Lean.Expr.const `Nat []`` .

We can do that using `repr`.

```js
def isNatDebugRepr (e: Expr): MetaM Unit := do
  let type_expr ← inferType e
  dbg_trace "The type expression is: {repr type_expr}"

#eval isNatDebugRepr zero 
```

Now, we get what we want — that `type_expr` looks like ``Lean.Expr.const `Nat []``
![](Screen%20Shot%202023-12-12%20at%205.09.51%20PM.png)


## Printing for the end-user

If we want to print something for day-to-day use (not just debugging), we can use `logInfo`.  

Note that because it is end-user facing, when it’s used with an `#eval` (for a developer)…
```js
def sayHello : MetaM Unit := do
  logInfo "hi"

#eval sayHello -- doesn't output anything
```
… then `logInfo` doesn’t output anything.
![](Screen%20Shot%202023-12-14%20at%205.39.20%20PM.png)

But if it’s used within a tactic, which is used within a proof…
```js
elab "sayHello" : tactic => sayHello 

example : True := by
  sayHello -- outputs "hi"
  trivial
```
…then `logInfo` does output stuff.  
![](Screen%20Shot%202023-12-14%20at%205.40.04%20PM.png)



# Fixing printing errors

If you need to print a list or something, you might get an error that lean was expecting something of type `MessageData` but instead got a `List`. 
```js
logInfo freeIdents -- throws error
```

 You can fix this by using `toString`.
```js
logInfo (toString freeIdents) -- works
```
## Applying unary operations

Using `.app` on a _unary_ operator (like `succ` which that just takes _one_ number and increments it) is straightforward.  

 If you’re trying to write `f x` as an expression, you can make it with `.app f x`.
```js
def f := Expr.const `Nat.succ []
def x := Expr.const `Nat.zero []
#eval (Expr.app f x) -- Nat.succ Nat.zero
```

We can check this actually compiles to `Nat.succ Nat.zero`:
```js
elab "fx" : term => return (Expr.app f x)
#eval (fx = Nat.succ Nat.zero) -- true
```
## Applying binary operations

On a _binary_ operator (like `add`…that takes _two_ numbers and adds them), it’s a bit more complicated.   

If you’re trying to write `f x y` as an expression, then because of “currying”, you can make it with `.app (.app f x) y`.
```js
def f' := Expr.const `Nat.add []
def x' := Expr.const `Nat.zero []
def y' := Expr.const `Nat.zero []
#eval (Expr.app (.app f' x') y') -- Nat.add Nat.zero Nat.zero
```

We can check this actually compiles to `Nat.add Nat.zero Nat.zero`

```js
elab "fxy" : term => return (Expr.app (.app f' x') y')
#eval (fxy = Nat.add Nat.zero Nat.zero) -- true
```
## Puzzle — Applying operations

Try to create `sumExpr` using an application of `Nat.add`.
```js
def sumExpr': Nat → Nat → Expr
| m, n =>  sorry
```

And try to create `multExpr` using an applications of `Nat.mul`.
```js
def mulExpr': Nat → Nat → Expr
| m, n =>  sorry
```

The [exercise is here](https://lean.math.hhu.de/#code=import%20Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic%20%2F-%20%CF%80%20-%2F%0Aopen%20Lean%20Elab%20Tactic%20Meta%0A%0A%2F--The%20constant%20%22x%22-%2F%0Adef%20natExpr%3A%20Nat%20%E2%86%92%20Expr%0A%7C%200%20%3D%3E%20.const%20%60%60Nat.zero%20%5B%5D%0A%7C%20n%20%2B%201%20%3D%3E%20.app%20(.const%20%60%60Nat.succ%20%5B%5D)%20(natExpr%20n)%0A%0A%2F--The%20function%20%22f%22-%2F%0Adef%20addExpr%20%3A%3D%20Expr.const%20%60Nat.add%20%5B%5D%0Adef%20mulExpr%20%3A%3D%20Expr.const%20%60Nat.mul%20%5B%5D%0A%0A%2F--Applying%20%22f%22%20to%20%22x%22-%2F%0Adef%20sumExpr'%3A%20Nat%20%E2%86%92%20Nat%20%E2%86%92%20Expr%0A%7C%20m%2C%20n%20%3D%3E%20%20sorry%0Adef%20mulExpr'%3A%20Nat%20%E2%86%92%20Nat%20%E2%86%92%20Expr%0A%7C%20m%2C%20n%20%3D%3E%20%20sorry%0A%0A%2F--Testing-%2F%0Aelab%20%22sum12%22%20%3A%20term%20%3D%3E%20return%20sumExpr'%201%202%0Aelab%20%22mul12%22%20%3A%20term%20%3D%3E%20return%20mulExpr'%201%202%0A%23eval%20(sum12%20%3D%203)%20--%20should%20be%20true%0A%23eval%20(mul12%20%3D%202)%20--%20should%20be%20true%0A) in the Lean 4 web editor.
The [answer is here](https://lean.math.hhu.de/#code=import%20Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic%20%2F-%20%CF%80%20-%2F%0Aopen%20Lean%20Elab%20Tactic%20Meta%0A%0A%2F--The%20constant%20%22x%22-%2F%0Adef%20natExpr%3A%20Nat%20%E2%86%92%20Expr%0A%7C%200%20%3D%3E%20.const%20%60%60Nat.zero%20%5B%5D%0A%7C%20n%20%2B%201%20%3D%3E%20.app%20(.const%20%60%60Nat.succ%20%5B%5D)%20(natExpr%20n)%0A%0A%2F--The%20function%20%22f%22-%2F%0Adef%20addExpr%20%3A%3D%20Expr.const%20%60Nat.add%20%5B%5D%0Adef%20mulExpr%20%3A%3D%20Expr.const%20%60Nat.mul%20%5B%5D%0A%0A%2F--Applying%20%22f%22%20to%20%22x%22-%2F%0Adef%20sumExpr'%3A%20Nat%20%E2%86%92%20Nat%20%E2%86%92%20Expr%0A%7C%20m%2C%20n%20%3D%3E%20%20(Expr.app%20(.app%20addExpr%20(natExpr%20m))%20(natExpr%20n))%0Adef%20mulExpr'%3A%20Nat%20%E2%86%92%20Nat%20%E2%86%92%20Expr%0A%7C%20m%2C%20n%20%3D%3E%20%20(Expr.app%20(.app%20mulExpr%20(natExpr%20m))%20(natExpr%20n))%0A%0A%2F--Testing-%2F%0Aelab%20%22sum12%22%20%3A%20term%20%3D%3E%20return%20sumExpr'%201%202%0Aelab%20%22mul12%22%20%3A%20term%20%3D%3E%20return%20mulExpr'%201%202%0A%23eval%20(sum12%20%3D%203)%20--%20should%20be%20true%0A%23eval%20(mul12%20%3D%202)%20--%20should%20be%20true%0A) is in the Lean 4 web editor.

## Getting types of expressions — applications 

So, we figured out if a given expression was a constant (e.g. a real constant or natural number constant).

Similarly, you can check if a given expression is an application (e.g. an application of addition to two constants).
```js
#eval (sumExpr 1 2).isConst -- false, is an application
#eval (sumExpr 1 2).isApp   -- true, is an application
```

But what if we want more detail than just “is application”?  What if we want to distinguish between whether it’s an application of addition or multiplication?

We can do that in the next puzzle.

## Puzzle - Getting types of expressions — applications

So we already have something that takes two numbers and adds them, e.g.  `sumExpr' 1 2`.

And we have something that takes two numbers and multiplies them e.g. `mulExpr' 1 2`.

Let’s try to create a function that distinguishes them.
```js
def isAddition (e : Expr) :  MetaM Bool := do {
  dbg_trace "The function: {e.getAppFn}"
  sorry -- replace this line with "return false" if you just want the #eval functions to show the dbg_trace
}
```

And then test it:
```js
#eval isAddition (sumExpr' 1 2) -- should be true
#eval isAddition (mulExpr' 1 2) -- should be false
```

The [exercise is here](https://lean.math.hhu.de/#code=import%20Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic%20%2F-%20%CF%80%20-%2F%0Aopen%20Lean%20Elab%20Tactic%20Meta%0A%0A%2F--Helper%20functions-%2F%0Adef%20natExpr%3A%20Nat%20%E2%86%92%20Expr%0A%7C%200%20%3D%3E%20.const%20%60%60Nat.zero%20%5B%5D%0A%7C%20n%20%2B%201%20%3D%3E%20.app%20(.const%20%60%60Nat.succ%20%5B%5D)%20(natExpr%20n)%0A%0Adef%20addExpr%20%3A%3D%20Expr.const%20%60Nat.add%20%5B%5D%0Adef%20mulExpr%20%3A%3D%20Expr.const%20%60Nat.mul%20%5B%5D%0A%0Adef%20sumExpr'%3A%20Nat%20%E2%86%92%20Nat%20%E2%86%92%20Expr%0A%7C%20m%2C%20n%20%3D%3E%20%20(Expr.app%20(.app%20addExpr%20(natExpr%20m))%20(natExpr%20n))%0Adef%20mulExpr'%3A%20Nat%20%E2%86%92%20Nat%20%E2%86%92%20Expr%0A%7C%20m%2C%20n%20%3D%3E%20%20(Expr.app%20(.app%20mulExpr%20(natExpr%20m))%20(natExpr%20n))%0A%0A%2F--%20Exercise%20-%2F%0Adef%20isAddition%20(e%20%3A%20Expr)%20%3A%20%20MetaM%20Bool%20%3A%3D%20do%20%7B%0A%20%20dbg_trace%20%22The%20function%3A%20%7Be.getAppFn%7D%22%0A%20%20sorry%20--%20replace%20this%20line%20with%20%22return%20false%22%20if%20you%20just%20want%20the%20%23eval%20functions%20to%20show%20the%20dbg_trace%0A%7D%0A%20%20%0A%2F-%20Tests%20-%2F%0A%23eval%20isAddition%20(sumExpr'%201%202)%20--%20should%20be%20true%0A%23eval%20isAddition%20(mulExpr'%201%202)%20--%20should%20be%20false) in the Lean 4 web editor.
The [answer is here](https://lean.math.hhu.de/#code=import%20Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic%20%2F-%20%CF%80%20-%2F%0Aopen%20Lean%20Elab%20Tactic%20Meta%0A%0A%2F--Helper%20functions-%2F%0Adef%20natExpr%3A%20Nat%20%E2%86%92%20Expr%0A%7C%200%20%3D%3E%20.const%20%60%60Nat.zero%20%5B%5D%0A%7C%20n%20%2B%201%20%3D%3E%20.app%20(.const%20%60%60Nat.succ%20%5B%5D)%20(natExpr%20n)%0A%0Adef%20addExpr%20%3A%3D%20Expr.const%20%60Nat.add%20%5B%5D%0Adef%20mulExpr%20%3A%3D%20Expr.const%20%60Nat.mul%20%5B%5D%0A%0Adef%20sumExpr'%3A%20Nat%20%E2%86%92%20Nat%20%E2%86%92%20Expr%0A%7C%20m%2C%20n%20%3D%3E%20%20(Expr.app%20(.app%20addExpr%20(natExpr%20m))%20(natExpr%20n))%0Adef%20mulExpr'%3A%20Nat%20%E2%86%92%20Nat%20%E2%86%92%20Expr%0A%7C%20m%2C%20n%20%3D%3E%20%20(Expr.app%20(.app%20mulExpr%20(natExpr%20m))%20(natExpr%20n))%0A%0A%2F--%20Exercise%20-%2F%0Adef%20isAddition%20(e%20%3A%20Expr)%20%3A%20%20MetaM%20Bool%20%3A%3D%20do%20%7B%0A%20%20dbg_trace%20%22The%20function%3A%20%7Be.getAppFn%7D%22%0A%20%20if%20(%E2%86%90%20isDefEq%20e.getAppFn%20addExpr)%20then%20return%20true%20else%20return%20false%0A%7D%0A%20%20%0A%2F--%20Tests%20-%2F%0A%23eval%20isAddition%20(sumExpr'%201%202)%0A%23eval%20isAddition%20(mulExpr'%201%202)) is in the Lean 4 web editor.

## Converting Code to Expressions

So we’ve converted expressions to code (using `evalExpr` and `elab`).

Now let’s go the other way.

Let’s create a tactic that, given a goal, gives you a Lean expression.  You can do this using either `toExpr` or `repr` as we did previously.

```js
elab "print_goal_as_expression" : tactic => do
  let goal ← getGoalType
  logInfo (toExpr goal) 
```

Indeed, this prints the long `Expr` you’d expect.
![](Screen%20Shot%202023-12-13%20at%2010.42.15%20AM.png)

Technically:
- `toExpr` returns an `Expr` object…
- `repr` returns a `Format` object.

They are slightly different… 

|                                      |                                 |
| ------------------------------------ | ------------------------------- |
| This code using `toExpr`..![](a.jpg) | …outputs this…![](a%20copy.jpg) |

|                                                                                 |                                                                        |
| ------------------------------------------------------------------------------- | ---------------------------------------------------------------------- |
| This code using `repr`…![](Screen%20Shot%202023-12-13%20at%2011.03.20%20AM.png) | …outputs this…![](Screen%20Shot%202023-12-13%20at%2011.01.59%20AM.png) |

… but if what you want is to see the low-level structure of a Lean object, they both work fine.

## Getting theorems from the environment

It will be helpful to get expressions from theorem statements to play around with them for this chapter.

What if we want to find the expression for a theorem statement when we’re not in the theorem itself (like above)?

Then, we use `getEnv`.
```js
def getTheoremStatement (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | failure -- get the declaration with that name
  return thm.type -- return the theorem statement

#eval getTheoremStatement `multPermute 
```

We get this long expression.
![](Screen%20Shot%202023-12-13%20at%2012.34.18%20PM.png)

…but this is a pretty ugly expression.  Is it really what we started with: this expression here?
```js
∀ (n m p : ℕ), n * (m * p) = m * (n * p)
```

To do that, we will explore…

## Pretty-printing expressions 

When we just log a raw expression….
```js
def logExpression (e : Expr) : MetaM Unit := do
  dbg_trace "{repr e}" 
#eval do {let e ← getTheoremStatement `multPermute; logExpression e}
```
… we get something quite ugly:
![](Screen%20Shot%202023-12-14%20at%205.53.40%20PM.png)

To check an expression is actually what we think it is, we can use `ppExpr`.
```js
def logPrettyExpression (e : Expr) : MetaM Unit := do
  dbg_trace "{←ppExpr e}" 
#eval do {let e ← getTheoremStatement `multPermute; logPrettyExpression e}
```

And indeed, we get what we expect.
![](Screen%20Shot%202023-12-14%20at%205.46.23%20PM.png)


## Getting subexpressions

Now that we have an expression, let’s try to find some of its subexpressions.  




In particular, to create an autogeneralization tactic, we’d want to identify each constant subexpression in the hypothesis, and for each constant, see  which properties about it appear in the proof term, in order to generalize that constant.

To start, given an expression, let’s print out all subexpressions of it that involve constants.  

We use `forEachWhere` — which looks through all subexpressions of the given expression `e`, and checks whether the subexpression satisfies the first argument (`isConst`) and if so, applies the second argument (`logExpression`).

```js
def printConstantsIn (e : Expr) : MetaM Unit :=
  e.forEachWhere Expr.isConst logExpression
```

We can test it works on the statement of `multPermute`:
```js
#eval do {let e ← getTheoremStatement `multPermute; printConstantsIn e}
```

And indeed, we get the relevant constants.
![](Screen%20Shot%202023-12-13%20at%201.21.57%20PM.png)


## Puzzle — Getting subexpressions of a particular type

Now, try to come up with a function that, given an expression, prints out all subexpressions of it that are natural numbers.

Hint:  We can’t just change `isConst`to `isNat` unfortunately.   The following code throws an error:
```js
def printNatsIn (e : Expr) : MetaM Unit :=
  e.forEachWhere isNat logExpression -- DOESN'T WORK
```
…because `isNat` isn’t always guaranteed to take an expression to a boolean.  Rather than being of type `Expr → Bool`, it is of type `Expr → MetaM Bool`.  This is because type inference needs to be wrapped in a monad — it’s “not guaranteed to work.”

Instead, we need a variant of `forEachWhere`that works to take monads as arguments.  This variant is called `forEach`, which takes a function of type `Expr → MetaM Bool`. 
```js
def printIfNat (subexpr : Expr) : MetaM Unit := do
  try
	sorry --  FILL THIS IN
  catch
  | _ => return

def printNatsIn (e : Expr) : MetaM Unit := do
  e.forEach printIfNat
```

Try to fill in the function.

The [exercise is here](https://lean.math.hhu.de/#code=import%20Mathlib.Tactic.Ring%0Aopen%20Lean%20Elab%20Tactic%20Meta%0A%0Atheorem%20multPermute%20%3A%20%E2%88%80%20(n%20m%20p%20%3A%20Nat)%2C%20n%20*%20(m%20*%20p)%20%3D%20m%20*%20(n%20*%20p)%20%3A%3D%20by%0A%20%20ring_nf%3B%20simp%0A%0A%2F--%20What%20the%20expression%20looks%20like%2C%20but%20prettier%20%20--%2F%0Adef%20logPrettyExpression%20(e%20%3A%20Expr)%20%3A%20MetaM%20Unit%20%3A%3D%20do%0A%20%20dbg_trace%20%22%7B%E2%86%90ppExpr%20e%7D%22%0A%0A%2F--%20Getting%20theorems%20from%20context%20--%2F%0Adef%20getTheoremStatement%20(n%20%3A%20Name)%20%3A%20MetaM%20Expr%20%3A%3D%20do%0A%20%20let%20some%20thm%20%3A%3D%20(%E2%86%90%20getEnv).find%3F%20n%20%7C%20failure%20--%20get%20the%20declaration%20with%20that%20name%0A%20%20return%20thm.type%20--%20return%20the%20theorem%20statement%0A%0A%2F--%20Get%20all%20subexpressions%20that%20involve%20natural%20numbers%20--%2F%0Adef%20isNat%20(e%3A%20Expr)%3A%20MetaM%20Bool%20%3A%3D%20do%0A%20%20let%20type_expr%20%E2%86%90%20inferType%20e%0A%20%20return%20type_expr.isConstOf%20%60Nat%0A%20%20%0A%2F--%20TO%20DO%3A%20COMPLETE%20THIS%20HELPER%20FUNCTION%20--%2F%0Adef%20printIfNat%20(subexpr%20%3A%20Expr)%20%3A%20MetaM%20Unit%20%3A%3D%20do%0A%20%20try%0A%20%20%20%20sorry%20--%20FILL%20THIS%20IN%0A%20%20catch%0A%20%20%7C%20_%20%3D%3E%20return%0A%0A%2F--%20For%20each%20subexpression%2C%20print%20it%20out%20if%20its%20a%20natural%20number-%2F%0Adef%20printNatsIn%20(e%20%3A%20Expr)%20%3A%20MetaM%20Unit%20%3A%3D%20do%0A%20%20e.forEach%20printIfNat%0A%0A%23eval%20do%20%7Blet%20e%20%E2%86%90%20getTheoremStatement%20%60multPermute%3B%20%20printNatsIn%20e%7D%20%0A) in the Lean 4 web editor.
The [answer is here](https://lean.math.hhu.de/#code=import%20Mathlib.Tactic.Ring%0Aopen%20Lean%20Elab%20Tactic%20Meta%0A%0Atheorem%20multPermute%20%3A%20%E2%88%80%20(n%20m%20p%20%3A%20Nat)%2C%20n%20*%20(m%20*%20p)%20%3D%20m%20*%20(n%20*%20p)%20%3A%3D%20by%0A%20%20ring_nf%3B%20simp%0A%0A%2F--%20What%20the%20expression%20looks%20like%2C%20but%20prettier%20%20--%2F%0Adef%20logPrettyExpression%20(e%20%3A%20Expr)%20%3A%20MetaM%20Unit%20%3A%3D%20do%0A%20%20dbg_trace%20%22%7B%E2%86%90ppExpr%20e%7D%22%0A%0A%2F--%20Getting%20theorems%20from%20context%20--%2F%0Adef%20getTheoremStatement%20(n%20%3A%20Name)%20%3A%20MetaM%20Expr%20%3A%3D%20do%0A%20%20let%20some%20thm%20%3A%3D%20(%E2%86%90%20getEnv).find%3F%20n%20%7C%20failure%20--%20get%20the%20declaration%20with%20that%20name%0A%20%20return%20thm.type%20--%20return%20the%20theorem%20statement%0A%0A%2F--%20Get%20all%20subexpressions%20that%20involve%20natural%20numbers%20--%2F%0Adef%20isNat%20(e%3A%20Expr)%3A%20MetaM%20Bool%20%3A%3D%20do%0A%20%20let%20type_expr%20%E2%86%90%20inferType%20e%0A%20%20return%20type_expr.isConstOf%20%60Nat%0A%20%20%0A%2F--%20Helper%20function%20-%2F%0Adef%20printIfNat%20(subexpr%20%3A%20Expr)%20%3A%20MetaM%20Unit%20%3A%3D%20do%0A%20%20try%0A%20%20%20%20let%20isNatResult%20%E2%86%90%20isNat%20subexpr%0A%20%20%20%20if%20isNatResult%20%0A%20%20%20%20%20%20then%20logPrettyExpression%20subexpr%3B%20dbg_trace%20%22--------------%22%0A%20%20%20%20%20%20else%20return%0A%20%20catch%0A%20%20%7C%20Exception.error%20_%20_%20%3D%3E%20return%0A%20%20%7C%20_%20%3D%3E%20throwError%20%22Something%20about%20'isNat%20subexpr'%20is%20throwing%20an%20error.%22%20%0A%0A%2F--%20For%20each%20subexpression%2C%20print%20it%20out%20if%20its%20a%20natural%20number-%2F%0Adef%20printNatsIn%20(e%20%3A%20Expr)%20%3A%20MetaM%20Unit%20%3A%3D%20do%0A%20%20e.forEach%20printIfNat%0A%0A%23eval%20do%20%7Blet%20e%20%E2%86%90%20getTheoremStatement%20%60multPermute%3B%20%20printNatsIn%20e%7D%20%0A) is in the Lean 4 web editor.

## Try-catch statements

Why did we need a `try-catch` above?

Well, let’s try removing it.

The following code type-checks, but we notice it fails at runtime (in the `#eval` statement).  It works to print out a few subexpressions, but stops at one of them, saying:  `unexpected bound variable #2`.
```js
def printIfNat (subexpr : Expr) : MetaM Unit := do
  let isNatResult ← isNat subexpr
  dbg_trace "{isNatResult}"
  if isNatResult then logExpression subexpr else return

def printNatsIn (e : Expr) : MetaM Unit := do
  e.forEach printIfNat

#eval do {let e ← getTheoremStatement `multPermute;  printNatsIn e}
```

When we log which subexpression it gets stuck on, we find the code stops running once it reaches the subexpression that says `#2` (which, if we write out its full representation using `repr`, we find is short for `Lean.Expr.bvar 2`, or bound variable #2).
![](Screen%20Shot%202023-12-14%20at%209.37.46%20PM.png)
That is, `isNat`’s type inference doesn’t work on this, and so it fails, and so it causes our whole program to fail. 

Ideally, we want `isNat` to silently fail when the subexpression isn’t well-formed enough to perform type inference.  So, we want to encapsulate all of this in a “try-catch” clause.
```js
def printIfNat (subexpr : Expr) : MetaM Unit := do
  try
    let isNatResult ← isNat subexpr
    if isNatResult 
      then logPrettyExpression subexpr; dbg_trace "---"
      else return
  catch
  | Exception.error _ _ => return
  | _ => throwError "Something about 'isNat subexpr' is throwing an error." 

def printNatsIn (e : Expr) : MetaM Unit := do
  e.forEach printIfNat

#eval do {let e ← getTheoremStatement `multPermute;  printNatsIn e}
```

Indeed, we end up printing out all the natural numbers, besides the ones we forced to fail because  they were just a single instance of a bound variable (`#0`, `#1`, and `#2`).
![](Screen%20Shot%202023-12-14%20at%209.52.07%20PM.png)


## Getting subexpressions of a particular type — a better way.

So, above, when we asked Lean to identify all the natural numbers in…
```js
∀ (n m p : ℕ), n * (m * p) = m * (n * p)
```
…it identified…
```js
#2 * (#1 * #0)		-- n * (m * p) 
#1 * #0			-- m * p
#1 * (#2 * #0)		-- m * (n * p)
#2 * #0			-- n * p
```
…but not…
```js
#0					-- p
#1					-- m
#2					-- n
```

That makes sense — with that single variable, Lean didn’t know what type it was.  But once it was operated on with the natural-number-multiplication operator `*`, it was clear it was a natural number.

But that’s not great…ideally, Lean should be able to deduce from context that those bound variables are natural numbers too.

**Todo: I still don’t know how to deal with this in an elegant way — besides manually passing to Lean which bound variables are natural numbers.**



## Manipulating subexpressions

Now, let’s have the function _replace_ the term with the type of it (creating a more general statement).

That is, given this theorem…
```js
theorem flt_example : 2^4 % 5 = 1 := by rfl
```
… we want to find all the natural numbers, and replace them with the type `Nat`.  We could do this with `generalize`.
```js
theorem flt_example' : 2^4 % 5 = 1 := by 
  generalize ha: 2 = a
  generalize hn: 5 = n
  generalize hm: 4 = m
  ...
```
Now our goal looks more general:
![](Screen%20Shot%202023-12-18%20at%2012.37.03%20PM.png width=250px)

But now, we want to create a tactic `generalizeAllNats` that automates it — i.e. create a tactic that finds all the natural numbers in an expression and replaces them with the type `Nat`.  Here’s the scaffolding code:
```js
theorem flt_example' : 2^4 % 5 = 1 := by 
	generalizeAllNats
```

Why do this?  This is the first step in working towards generalizing this theorem to any theorem that looks like:
```js
theorem flt_general : (hp : Nat.Prime p) (hpn : IsCoprime a p) : 
	a ^ (p - 1) % p = 1
```

We’ll explore these in the next sections.

## Getting and filtering lists of subexpressions

Now suppose instead of printing those natural numbers, we want to put them in a list so we can more easily do something with them.

We can first recursively collect a list of all the subexpressions in an expression `e`:
```js
def getSubexpressionsIn (e : Expr) : MetaM (List Expr) :=
  let rec getSubexpressionsInRec (e : Expr) (acc : List Expr) : MetaM (List Expr) :=
    match e with
    | Expr.forallE _ d b _   => return [e] ++ (← getSubexpressionsInRec d acc) ++ (← getSubexpressionsInRec b acc)
    | Expr.lam _ d b _       => return [e] ++ (← getSubexpressionsInRec d acc) ++ (← getSubexpressionsInRec b acc)
    | Expr.letE _ t v b _    => return [e] ++ (← getSubexpressionsInRec t acc) ++ (← getSubexpressionsInRec v acc) ++ (← getSubexpressionsInRec b acc)
    | Expr.app f a           => return [e] ++ (← getSubexpressionsInRec f acc) ++ (← getSubexpressionsInRec a acc)
    | Expr.mdata _ b         => return [e] ++ (← getSubexpressionsInRec b acc)
    | Expr.proj _ _ b        => return [e] ++ (← getSubexpressionsInRec b acc)
    | _                      => return acc
  getSubexpressionsInRec e []

#eval do {let e ← getTheoremStatement `multPermute;  getSubexpressionsIn e}
```

And then we create a helper function that identifies only natural numbers:
```js
def getIfNat (subexpr : Expr) : MetaM (Option Expr) := do
  try
    let isNatResult ← isNat subexpr
    if isNatResult
      then return some subexpr
      else return none
  catch
  | Exception.error _ _ => return none
  | _ => throwError "Something about 'isNat subexpr' is throwing an error."

```

And then we can keep only the subexpressions that are of type `Nat` using `filterMapM`:
```js
/- Get (in a list) all subexpressions that involve natural numbers -/
def getNatsIn (e : Expr) : MetaM (List Expr) := do
  let subexprs ← getSubexpressionsIn e
  let natSubexprs ← subexprs.filterMapM getIfNat
  return natSubexprs
```

When we test out our function…
```js
theorem flt_example : 2^4 % 5 = 1 := by simp

#eval do { let e ← getTheoremStatement `flt_example; let natsInE ← getNatsIn e; natsInE.forM logPrettyExpression}
```

…we get a list of exactly the Nats we want from the `flt_example` (` 2^4 % 5 = 1`).
![](Screen%20Shot%202023-12-20%20at%205.10.18%20PM.png)


# Puzzle — Deconstructing expressions

We ultimately want to create a tactic `generalizeNat` that generalizes _all_ natural numbers in the goal.

But right now, when we get a list of all subexpressions of type Nat, we get:
```js
2 ^ 4 % 5
2 ^ 4
2
4
5
1
```

Instead, we want a list of all “atomic” subexpressions of type Nat.
```js
2
4
5
1
```

Create some code that does this.  Here is some scaffolding code:
```js
def isAtomicNat (e : Expr) : MetaM Bool := do
  if not (← isNat e) then return false else
    let rec getFirstNonAppTerm (e : Expr) : MetaM Expr := match e with
    | Expr.app f a => return (← getFirstNonAppTerm f)
    | _ => return e
    let nonAppTerm ← getFirstNonAppTerm e
    sorry


#eval isAtomicNat (toExpr 1) -- true
#eval isAtomicNat (sumExpr 1 2) -- false

/- Get (in a list) all subexpressions that are just a single natural numbers like 3 and 4, not 3^4 -/
def getIfAtomicNat (subexpr : Expr) : MetaM (Option Expr) := do
  if (← isAtomicNat subexpr)
    then return some subexpr
    else return none

/-- Returns nats like 3 and 4, not 3^4 or 3*4 -/
def getAtomicNatsIn (e : Expr) : MetaM (List Expr) := do
  let subexprs ← getSubexpressionsIn e
  let natSubexprs ← subexprs.filterMapM getIfAtomicNat
  return natSubexprs

```

Hint: 
- The expression for `1` (an atomic Nat) looks like this:
	![](Screen%20Shot%202023-12-23%20at%208.34.50%20PM.png)

- But the expression for `1+2` (a non-atomic Nat) looks like this:
	![](Screen%20Shot%202023-12-23%20at%208.35.29%20PM.png)

The [exercise is here](https://lean.math.hhu.de/#code=import%20Lean%0Aopen%20Lean%20Elab%20Tactic%20Meta%0A%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%2F-%20Helper%20definitions%20and%20functions%20%20-%2F%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%0Atheorem%20flt_example%20%3A%202%5E4%20%25%205%20%3D%201%20%3A%3D%20by%20rfl%0A%0Adef%20natExpr%3A%20Nat%20%E2%86%92%20Expr%0A%7C%200%20%3D%3E%20.const%20%60%60Nat.zero%20%5B%5D%0A%7C%20n%20%2B%201%20%3D%3E%20.app%20(.const%20%60%60Nat.succ%20%5B%5D)%20(natExpr%20n)%0A%0Adef%20sumExpr%3A%20Nat%20%E2%86%92%20Nat%20%E2%86%92%20Expr%0A%7C%20m%2C%20n%20%3D%3E%20%20Expr.app%20(.app%20(.const%20%60Nat.add%20%5B%5D)%20(natExpr%20m))%20(natExpr%20n)%0A%0Adef%20isNat%20(e%3A%20Expr)%3A%20MetaM%20Bool%20%3A%3D%20do%0A%20%20let%20type_expr%20%E2%86%90%20inferType%20e%0A%20%20return%20type_expr.isConstOf%20%60Nat%0A%0Adef%20getTheoremStatement%20(n%20%3A%20Name)%20%3A%20MetaM%20Expr%20%3A%3D%20do%0A%20%20let%20some%20thm%20%3A%3D%20(%E2%86%90%20getEnv).find%3F%20n%20%7C%20failure%20--%20get%20the%20declaration%20with%20that%20name%0A%20%20return%20thm.type%20--%20return%20the%20theorem%20statement%0A%0Adef%20logPrettyExpression%20(e%20%3A%20Expr)%20%3A%20MetaM%20Unit%20%3A%3D%20do%0A%20%20dbg_trace%20%22%7B%E2%86%90ppExpr%20e%7D%22%0A%0Adef%20getSubexpressionsIn%20(e%20%3A%20Expr)%20%3A%20MetaM%20(List%20Expr)%20%3A%3D%0A%20%20let%20rec%20getSubexpressionsInRec%20(e%20%3A%20Expr)%20(acc%20%3A%20List%20Expr)%20%3A%20MetaM%20(List%20Expr)%20%3A%3D%0A%20%20%20%20match%20e%20with%0A%20%20%20%20%7C%20Expr.forallE%20_%20d%20b%20_%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20d%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.lam%20_%20d%20b%20_%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20d%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.letE%20_%20t%20v%20b%20_%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20t%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20v%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.app%20f%20a%20%20%20%20%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20f%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20a%20acc)%0A%20%20%20%20%7C%20Expr.mdata%20_%20b%20%20%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.proj%20_%20_%20b%20%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20_%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%3D%3E%20return%20acc%0A%20%20getSubexpressionsInRec%20e%20%5B%5D%0A%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%2F-%20The%20exercise%20-%2F%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%0Adef%20isAtomicNat%20(e%20%3A%20Expr)%20%3A%20MetaM%20Bool%20%3A%3D%20do%0A%20%20if%20not%20(%E2%86%90%20isNat%20e)%20then%20return%20false%20else%0A%20%20%20%20let%20rec%20getFirstNonAppTerm%20(e%20%3A%20Expr)%20%3A%20MetaM%20Expr%20%3A%3D%20match%20e%20with%0A%20%20%20%20%7C%20Expr.app%20f%20_%20%3D%3E%20return%20(%E2%86%90%20getFirstNonAppTerm%20f)%0A%20%20%20%20%7C%20_%20%3D%3E%20return%20e%0A%20%20%20%20let%20nonAppTerm%20%E2%86%90%20getFirstNonAppTerm%20e%0A%20%20%20%20return%20false%20--%20REPLACE%20THIS%20LAST%20LINE%20WITH%20THE%20REST%20OF%20THE%20CORRECT%20FUNCTION%0A%0A%23eval%20toExpr%201%0A%23eval%20sumExpr%201%202%0A%23eval%20isAtomicNat%20(toExpr%201)%20--%20true%0A%23eval%20isAtomicNat%20(sumExpr%201%202)%20--%20false%0A%0A%2F-%20Get%20(in%20a%20list)%20all%20subexpressions%20that%20are%20just%20a%20single%20natural%20numbers%20-%2F%0Adef%20getIfAtomicNat%20(subexpr%20%3A%20Expr)%20%3A%20MetaM%20(Option%20Expr)%20%3A%3D%20do%0A%20%20if%20(%E2%86%90%20isAtomicNat%20subexpr)%0A%20%20%20%20then%20return%20some%20subexpr%0A%20%20%20%20else%20return%20none%0A%0A%2F--%20Returns%20single%20nats%20like%203%20and%204%2C%20not%203%5E4%20or%203*4%20-%2F%0Adef%20getAtomicNatsIn%20(e%20%3A%20Expr)%20%3A%20MetaM%20(List%20Expr)%20%3A%3D%20do%0A%20%20let%20subexprs%20%E2%86%90%20getSubexpressionsIn%20e%0A%20%20let%20natSubexprs%20%E2%86%90%20subexprs.filterMapM%20getIfAtomicNat%0A%20%20return%20natSubexprs%0A%0A%23eval%20do%20%7B%20let%20e%20%E2%86%90%20getTheoremStatement%20%60flt_example%3B%20let%20natsInE%20%E2%86%90%20getAtomicNatsIn%20e%3B%20natsInE.forM%20logPrettyExpression%7D) in the Lean 4 web editor.
The [answer is here](https://lean.math.hhu.de/#code=import%20Lean%0Aopen%20Lean%20Elab%20Tactic%20Meta%0A%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%2F-%20Helper%20definitions%20and%20functions%20%20-%2F%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%0Atheorem%20flt_example%20%3A%202%5E4%20%25%205%20%3D%201%20%3A%3D%20by%20rfl%0A%0Adef%20natExpr%3A%20Nat%20%E2%86%92%20Expr%0A%7C%200%20%3D%3E%20.const%20%60%60Nat.zero%20%5B%5D%0A%7C%20n%20%2B%201%20%3D%3E%20.app%20(.const%20%60%60Nat.succ%20%5B%5D)%20(natExpr%20n)%0A%0Adef%20sumExpr%3A%20Nat%20%E2%86%92%20Nat%20%E2%86%92%20Expr%0A%7C%20m%2C%20n%20%3D%3E%20%20Expr.app%20(.app%20(.const%20%60Nat.add%20%5B%5D)%20(natExpr%20m))%20(natExpr%20n)%0A%0Adef%20isNat%20(e%3A%20Expr)%3A%20MetaM%20Bool%20%3A%3D%20do%0A%20%20let%20type_expr%20%E2%86%90%20inferType%20e%0A%20%20return%20type_expr.isConstOf%20%60Nat%0A%0Adef%20getTheoremStatement%20(n%20%3A%20Name)%20%3A%20MetaM%20Expr%20%3A%3D%20do%0A%20%20let%20some%20thm%20%3A%3D%20(%E2%86%90%20getEnv).find%3F%20n%20%7C%20failure%20--%20get%20the%20declaration%20with%20that%20name%0A%20%20return%20thm.type%20--%20return%20the%20theorem%20statement%0A%20%20%0Adef%20logPrettyExpression%20(e%20%3A%20Expr)%20%3A%20MetaM%20Unit%20%3A%3D%20do%0A%20%20dbg_trace%20%22%7B%E2%86%90ppExpr%20e%7D%22%0A%0Adef%20getSubexpressionsIn%20(e%20%3A%20Expr)%20%3A%20MetaM%20(List%20Expr)%20%3A%3D%0A%20%20let%20rec%20getSubexpressionsInRec%20(e%20%3A%20Expr)%20(acc%20%3A%20List%20Expr)%20%3A%20MetaM%20(List%20Expr)%20%3A%3D%0A%20%20%20%20match%20e%20with%0A%20%20%20%20%7C%20Expr.forallE%20_%20d%20b%20_%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20d%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.lam%20_%20d%20b%20_%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20d%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.letE%20_%20t%20v%20b%20_%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20t%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20v%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.app%20f%20a%20%20%20%20%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20f%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20a%20acc)%0A%20%20%20%20%7C%20Expr.mdata%20_%20b%20%20%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.proj%20_%20_%20b%20%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20_%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%3D%3E%20return%20acc%0A%20%20getSubexpressionsInRec%20e%20%5B%5D%0A%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%2F-%20The%20exercise%20-%2F%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%0Adef%20isAtomicNat%20(e%20%3A%20Expr)%20%3A%20MetaM%20Bool%20%3A%3D%20do%0A%20%20if%20not%20(%E2%86%90%20isNat%20e)%20then%20return%20false%20else%0A%20%20%20%20let%20rec%20getFirstNonAppTerm%20(e%20%3A%20Expr)%20%3A%20MetaM%20Expr%20%3A%3D%20match%20e%20with%0A%20%20%20%20%7C%20Expr.app%20f%20_%20%3D%3E%20return%20(%E2%86%90%20getFirstNonAppTerm%20f)%0A%20%20%20%20%7C%20_%20%3D%3E%20return%20e%0A%20%20%20%20let%20nonAppTerm%20%E2%86%90%20getFirstNonAppTerm%20e%0A%20%20%20%20--%20dbg_trace%20repr%20e%0A%20%20%20%20--%20dbg_trace%20%22%3E%3E%3E%22%0A%20%20%20%20if%20nonAppTerm.isConstOf%20%60OfNat.ofNat%20--nonAppTerm.isLit%20-%0A%20%20%20%20%20%20then%0A%20%20%20%20%20%20%20%20--%20dbg_trace%20repr%20nonAppTerm%3B%20dbg_trace%20%22%3D%3D%3D%3D%3D%3D%3D%3D%3D%3D%22%3B%0A%20%20%20%20%20%20%20%20return%20true%0A%20%20%20%20%20%20else%0A%20%20%20%20%20%20%20%20--%20dbg_trace%20repr%20nonAppTerm%3B%20dbg_trace%20%22%3D%3D%3D%3D%3D%3D%3D%3D%3D%3D%22%3B%0A%20%20%20%20%20%20%20%20return%20false%0A%0A%23eval%20toExpr%201%0A%23eval%20sumExpr%201%202%0A%23eval%20isAtomicNat%20(toExpr%201)%20--%20true%0A%23eval%20isAtomicNat%20(sumExpr%201%202)%20--%20false%0A%0A%2F-%20Get%20(in%20a%20list)%20all%20subexpressions%20that%20are%20just%20a%20single%20natural%20numbers%20-%2F%0Adef%20getIfAtomicNat%20(subexpr%20%3A%20Expr)%20%3A%20MetaM%20(Option%20Expr)%20%3A%3D%20do%0A%20%20if%20(%E2%86%90%20isAtomicNat%20subexpr)%0A%20%20%20%20then%20return%20some%20subexpr%0A%20%20%20%20else%20return%20none%0A%0A%2F--%20Returns%20single%20nats%20like%203%20and%204%2C%20not%203%5E4%20or%203*4%20-%2F%0Adef%20getAtomicNatsIn%20(e%20%3A%20Expr)%20%3A%20MetaM%20(List%20Expr)%20%3A%3D%20do%0A%20%20let%20subexprs%20%E2%86%90%20getSubexpressionsIn%20e%0A%20%20let%20natSubexprs%20%E2%86%90%20subexprs.filterMapM%20getIfAtomicNat%0A%20%20return%20natSubexprs%0A%0A%23eval%20do%20%7B%20let%20e%20%E2%86%90%20getTheoremStatement%20%60flt_example%3B%20let%20natsInE%20%E2%86%90%20getAtomicNatsIn%20e%3B%20natsInE.forM%20logPrettyExpression%7D) is in the Lean 4 web editor.

# Structures in Lean

We will ultimately want to use the `generalize` tactic in Lean.

But it takes an argument called `GeneralizeArg` which is a `structure`.  The way you initialize structures in Lean is that when it’s defined like this…
![](Screen%20Shot%202023-12-26%20at%205.20.59%20PM.png)
…you instantiate it like this…
```
 let genArg : GeneralizeArg := { expr := e, xName? := x, hName? := h }``
```

We’ll see what this looks like in context in the next section.

## Generalizing 

Now, we can generalize using the `generalize` function.
``
```

def generalizeTerm (e : Expr) (x : Name) (h : Name) : TacticM Unit := do
  let genArg : GeneralizeArg := { expr := e, xName? := x, hName? := h }
  let (_, new_goal) ← (←getGoalVar).generalize (List.toArray [genArg])
  setGoals [new_goal]
```

Here’s how we would generalize the number `2` to an arbitrary natural number `x`.

```js
elab "generalize2" : tactic => do
  let e := (toExpr 2)
  let x := `x
  let h := `h
  generalizeTerm e x h -- like the lean command "generalize h : e = x"

example : 2^4 % 5 = 1 := by
  generalize2
```

And indeed it
![](Screen%20Shot%202023-12-22%20at%2011.08.43%20PM.png)


# Getting dynamically generated hypotheses

You’ll notice that even though we’ve introduced two new hypotheses, `getHypotheses`shows us none.
![](Screen%20Shot%202023-12-23%20at%2011.25.38%20PM.png)
That’s because the local context (where `getHypotheses` operates) only gets the initial hypotheses from when the theorem was declared.

If we want to get the hypotheses that were dynamically generated, we need to look inside the goal metavariable — these dynamic hypotheses are associated with the dynamically changing goal.

So let’s create a function `getAllHypotheses`.
```js
/--  Tactic to return hypotheses declarations (including dynamically generated ones)-/
def getAllHypotheses : TacticM (List LocalDecl) := do
  let mut hypotheses : List LocalDecl := []
  let goal ← getMainGoal  -- the dynamically generated hypotheses are associated with this particular goal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    hypotheses := ldecl :: hypotheses
  return hypotheses
```

And now let’s print out their names
```js
def getAllHypothesesNames : TacticM (List Name) := do
  let mut hypotheses_names : List Name := []
  for hypothesis in ← getAllHypotheses do
    hypotheses_names := hypothesis.userName :: hypotheses_names
  return hypotheses_names
elab "getAllHypothesesNames" : tactic => do
  let names ← getAllHypothesesNames
  logInfo ("Hyp names:" ++ toString names)
```

Indeed, now we get the dynamically generated hypotheses.
![](Screen%20Shot%202023-12-23%20at%2011.26.01%20PM.png)


# Generalizing with nice variable names

We’d ideally like to automatically generate the variable names.  We can do that with `Lean.mkFreshId`.
```js
def generalizeTerm (e : Expr) (x? : Option Name := none) (h? : Option Name := none) : TacticM Unit := do
  let x := x?.getD (← Lean.mkFreshId) -- use the given variable name, or if it's not there, make one
  let h := h?.getD (← Lean.mkFreshId) -- use the given hypothesis name, or if it's not there, make one
  let genArg : GeneralizeArg := { expr := e, xName? := x, hName? := h }
  let (_, new_goal) ← (←getGoalVar).generalize (List.toArray [genArg])
  setGoals [new_goal]
```

But this creates really ugly names…
![](Screen%20Shot%202023-12-23%20at%209.29.45%20PM.png)

To make prettier user names, use `Lean. mkFreshUserName`
```js
def generalizeTerm (e : Expr) (x? : Option Name := none) (h? : Option Name := none) : TacticM Unit := do
  let x := x?.getD (← Lean.mkFreshUserName `x) -- use the given variable name, or if it's not there, make one
  let h := h?.getD (← Lean.mkFreshUserName `h) -- use the given hypothesis name, or if it's not there, make one
  let genArg : GeneralizeArg := { expr := e, xName? := x, hName? := h }
  let (_, new_goal) ← (←getGoalVar).generalize (List.toArray [genArg])
  setGoals [new_goal]
```

If you use ``mkFreshUserName `x`` then Lean will use `x` as the “base word” in defining the variable name, adding other symbols to make sure the name is unique. 
![](Screen%20Shot%202023-12-23%20at%209.30.29%20PM.png)

So for example now when you generalize something else, `mkFreshUserName` follows the same “base names”, but still ensures the names are unique.
![](Screen%20Shot%202023-12-23%20at%209.32.26%20PM.png)

If you want the names to look even nicer, we can use a custom helper function `mkPrettyName`, inspired by Lean’s `mkAuxName`.  It takes arguments `baseName` and `idx`, and names the variable `baseName_idx` if that is available.  Otherwise, it names it `baseName_(idx+1)` if available…or increments until it finds an available name.

```js
partial def mkPrettyNameHelper(hypNames : List Name) (base : Name) (i : Nat) : Name :=
  let candidate := base.appendIndexAfter i
  if (hypNames).contains candidate then
    mkPrettyNameHelper hypNames base (i+1)
  else
    candidate

/-- Names a function baseName_idx if that is available.  otherwise, names it baseName_idx+1 if available...and so on. -/
def mkPrettyName (baseName : Name) (idx : Nat) : TacticM Name := do
  return mkPrettyNameHelper (← getAllHypothesesNames) baseName idx
```

(Note: we need to say the first function is `partial` because otherwise, Lean throws an error saying it can’t prove the recursion will terminate.  And, luckily, if you declare it a `partial` function, it won’t complain.)

(Because `partial` functions might loop infinitely when you’re evaluating it, it can’t be used directly in a mathematical proof…the prover will refuse to type-check something that might cause it to loop infinitely).

Now, we can use `mkPrettyName` in our generalizing function.  
```js
def generalizeTerm (e : Expr) (x? : Option Name := none) (h? : Option Name := none) : TacticM Unit := do
    let x := x?.getD (← mkPrettyName `x 0) -- use the given variable name, or if it's not there, make one
    let h := h?.getD (← mkPrettyName `h 0) -- use the given hypothesis name, or if it's not there, make one
    let genArg : GeneralizeArg := { expr := e, xName? := x, hName? := h }
    let (_, new_goal) ← (←getGoalVar).generalize (List.toArray [genArg])
    setGoals [new_goal]
```

Now look how much nicer those names are!
![](Screen%20Shot%202023-12-23%20at%2011.38.59%20PM.png)


# Puzzle — generalizing based on type

Now, create a tactic `generalizeNat` that generalizes _all_ natural numbers in the goal.

```js
elab "generalizeAllNats" : tactic => do
  return -- FILL THIS IN --

example : 2^4 % 5 = 1 := by
  generalizeAllNats
```

When you’re done, the goal should look like this:
![](Screen%20Shot%202023-12-23%20at%2011.49.30%20PM.png)

The [exercise is here](https://lean.math.hhu.de/#code=import%20Lean%0Aopen%20Lean%20Elab%20Tactic%20Meta%0A%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%2F-%20Helper%20definitions%20and%20functions%20%20-%2F%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%0Atheorem%20flt_example%20%3A%202%5E4%20%25%205%20%3D%201%20%3A%3D%20by%20rfl%0A%0Adef%20getGoalVar%20%3A%20TacticM%20MVarId%20%3A%3D%20do%0A%20%20return%20%E2%86%90%20getMainGoal%0A%0Adef%20getGoalType%20%3A%20TacticM%20Expr%20%3A%3D%20do%0A%20%20return%20%E2%86%90%20getMainTarget%20--%20(%E2%86%90%20getGoalDecl).type%20or%20(%E2%86%90%20getGoalVar).getType%0A%0Adef%20getAllHypotheses%20%3A%20TacticM%20(List%20LocalDecl)%20%3A%3D%20do%0A%20%20let%20mut%20hypotheses%20%3A%20List%20LocalDecl%20%3A%3D%20%5B%5D%0A%20%20let%20goal%20%E2%86%90%20getMainGoal%20%20--%20the%20dynamically%20generated%20hypotheses%20are%20associated%20with%20this%20particular%20goal%0A%20%20for%20ldecl%20in%20(%E2%86%90%20goal.getDecl).lctx%20do%0A%20%20%20%20if%20ldecl.isImplementationDetail%20then%20continue%0A%20%20%20%20hypotheses%20%3A%3D%20ldecl%20%3A%3A%20hypotheses%0A%20%20return%20hypotheses%0A%0Adef%20getAllHypothesesNames%20%3A%20TacticM%20(List%20Name)%20%3A%3D%20do%0A%20%20let%20mut%20hypotheses_names%20%3A%20List%20Name%20%3A%3D%20%5B%5D%0A%20%20for%20hypothesis%20in%20%E2%86%90%20getAllHypotheses%20do%0A%20%20%20%20hypotheses_names%20%3A%3D%20hypothesis.userName%20%3A%3A%20hypotheses_names%0A%20%20return%20hypotheses_names%0Aelab%20%22getAllHypothesesNames%22%20%3A%20tactic%20%3D%3E%20do%0A%20%20let%20names%20%E2%86%90%20getAllHypothesesNames%0A%20%20logInfo%20(%22Hyp%20names%3A%22%20%2B%2B%20toString%20names)%0A%0Adef%20isNat%20(e%3A%20Expr)%3A%20MetaM%20Bool%20%3A%3D%20do%0A%20%20let%20type_expr%20%E2%86%90%20inferType%20e%0A%20%20return%20type_expr.isConstOf%20%60Nat%0A%0Apartial%20def%20mkPrettyNameHelper(hypNames%20%3A%20List%20Name)%20(base%20%3A%20Name)%20(i%20%3A%20Nat)%20%3A%20Name%20%3A%3D%0A%20%20let%20candidate%20%3A%3D%20base.appendIndexAfter%20i%0A%20%20if%20(hypNames).contains%20candidate%20then%0A%20%20%20%20mkPrettyNameHelper%20hypNames%20base%20(i%2B1)%0A%20%20else%0A%20%20%20%20candidate%0A%0A%2F--%20Names%20a%20function%20baseName_idx%20if%20that%20is%20available.%20%20otherwise%2C%20names%20it%20baseName_idx%2B1%20if%20available...and%20so%20on.%20-%2F%0Adef%20mkPrettyName%20(baseName%20%3A%20Name)%20(idx%20%3A%20Nat)%20%3A%20TacticM%20Name%20%3A%3D%20do%0A%20%20return%20mkPrettyNameHelper%20(%E2%86%90%20getAllHypothesesNames)%20baseName%20idx%0A%0A%2F--%20Generalizing%20a%20term%20in%20a%20theorem%20%20-%2F%0Adef%20generalizeTerm%20(e%20%3A%20Expr)%20(x%3F%20%3A%20Option%20Name%20%3A%3D%20none)%20(h%3F%20%3A%20Option%20Name%20%3A%3D%20none)%20%3A%20TacticM%20Unit%20%3A%3D%20do%0A%20%20%20%20let%20x%20%3A%3D%20x%3F.getD%20(%E2%86%90%20mkPrettyName%20%60x%200)%20--%20use%20the%20given%20variable%20name%2C%20or%20if%20it's%20not%20there%2C%20make%20one%0A%20%20%20%20let%20h%20%3A%3D%20h%3F.getD%20(%E2%86%90%20mkPrettyName%20%60h%200)%20--%20use%20the%20given%20hypothesis%20name%2C%20or%20if%20it's%20not%20there%2C%20make%20one%0A%20%20%20%20let%20genArg%20%3A%20GeneralizeArg%20%3A%3D%20%7B%20expr%20%3A%3D%20e%2C%20xName%3F%20%3A%3D%20x%2C%20hName%3F%20%3A%3D%20h%20%7D%0A%20%20%20%20let%20(_%2C%20new_goal)%20%E2%86%90%20(%E2%86%90getGoalVar).generalize%20(List.toArray%20%5BgenArg%5D)%0A%20%20%20%20setGoals%20%5Bnew_goal%5D%0A%0Adef%20getSubexpressionsIn%20(e%20%3A%20Expr)%20%3A%20MetaM%20(List%20Expr)%20%3A%3D%0A%20%20let%20rec%20getSubexpressionsInRec%20(e%20%3A%20Expr)%20(acc%20%3A%20List%20Expr)%20%3A%20MetaM%20(List%20Expr)%20%3A%3D%0A%20%20%20%20match%20e%20with%0A%20%20%20%20%7C%20Expr.forallE%20_%20d%20b%20_%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20d%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.lam%20_%20d%20b%20_%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20d%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.letE%20_%20t%20v%20b%20_%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20t%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20v%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.app%20f%20a%20%20%20%20%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20f%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20a%20acc)%0A%20%20%20%20%7C%20Expr.mdata%20_%20b%20%20%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.proj%20_%20_%20b%20%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20_%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%3D%3E%20return%20acc%0A%20%20getSubexpressionsInRec%20e%20%5B%5D%0A%0A%0Adef%20isAtomicNat%20(e%20%3A%20Expr)%20%3A%20MetaM%20Bool%20%3A%3D%20do%0A%20%20if%20not%20(%E2%86%90%20isNat%20e)%20then%20return%20false%20else%0A%20%20%20%20let%20rec%20getFirstNonAppTerm%20(e%20%3A%20Expr)%20%3A%20MetaM%20Expr%20%3A%3D%20match%20e%20with%0A%20%20%20%20%7C%20Expr.app%20f%20_%20%3D%3E%20return%20(%E2%86%90%20getFirstNonAppTerm%20f)%0A%20%20%20%20%7C%20_%20%3D%3E%20return%20e%0A%20%20%20%20let%20nonAppTerm%20%E2%86%90%20getFirstNonAppTerm%20e%0A%20%20%20%20--%20dbg_trace%20repr%20e%0A%20%20%20%20--%20dbg_trace%20%22%3E%3E%3E%22%0A%20%20%20%20if%20nonAppTerm.isConstOf%20%60OfNat.ofNat%20--nonAppTerm.isLit%20-%0A%20%20%20%20%20%20then%0A%20%20%20%20%20%20%20%20--%20dbg_trace%20repr%20nonAppTerm%3B%20dbg_trace%20%22%3D%3D%3D%3D%3D%3D%3D%3D%3D%3D%22%3B%0A%20%20%20%20%20%20%20%20return%20true%0A%20%20%20%20%20%20else%0A%20%20%20%20%20%20%20%20--%20dbg_trace%20repr%20nonAppTerm%3B%20dbg_trace%20%22%3D%3D%3D%3D%3D%3D%3D%3D%3D%3D%22%3B%0A%20%20%20%20%20%20%20%20return%20false%0A%0A%0A%2F-%20Get%20(in%20a%20list)%20all%20subexpressions%20that%20are%20just%20a%20single%20natural%20numbers%20-%2F%0Adef%20getIfAtomicNat%20(subexpr%20%3A%20Expr)%20%3A%20MetaM%20(Option%20Expr)%20%3A%3D%20do%0A%20%20if%20(%E2%86%90%20isAtomicNat%20subexpr)%0A%20%20%20%20then%20return%20some%20subexpr%0A%20%20%20%20else%20return%20none%0A%0A%2F--%20Returns%20single%20nats%20like%203%20and%204%2C%20not%203%5E4%20or%203*4%20-%2F%0Adef%20getAtomicNatsIn%20(e%20%3A%20Expr)%20%3A%20MetaM%20(List%20Expr)%20%3A%3D%20do%0A%20%20let%20subexprs%20%E2%86%90%20getSubexpressionsIn%20e%0A%20%20let%20natSubexprs%20%E2%86%90%20subexprs.filterMapM%20getIfAtomicNat%0A%20%20return%20natSubexprs%0A%0A%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%2F-%20The%20exercise%20-%2F%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%0A%2F--%20Generalizing%20all%20natural%20numbers%20in%20a%20theorem%20%20-%2F%0Aelab%20%22generalizeAllNats%22%20%3A%20tactic%20%3D%3E%20do%0A%20%20return%0A%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%2F-%20The%20test%20-%2F%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%0Aexample%20%3A%202%5E4%20%25%205%20%3D%201%20%3A%3D%20by%0A%20%20generalizeAllNats%0A%20%20rw%20%20%5B%E2%86%90h_0%2C%20%E2%86%90h_1%2C%20%E2%86%90h_2%2C%20%E2%86%90h_3%5D%3B%20rfl) in the Lean 4 web editor.
The [answer is here](https://lean.math.hhu.de/#code=import%20Lean%0Aopen%20Lean%20Elab%20Tactic%20Meta%0A%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%2F-%20Helper%20definitions%20and%20functions%20%20-%2F%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%0Atheorem%20flt_example%20%3A%202%5E4%20%25%205%20%3D%201%20%3A%3D%20by%20rfl%0A%0Adef%20getGoalVar%20%3A%20TacticM%20MVarId%20%3A%3D%20do%0A%20%20return%20%E2%86%90%20getMainGoal%0A%0Adef%20getGoalType%20%3A%20TacticM%20Expr%20%3A%3D%20do%0A%20%20return%20%E2%86%90%20getMainTarget%20--%20(%E2%86%90%20getGoalDecl).type%20or%20(%E2%86%90%20getGoalVar).getType%0A%0Adef%20getAllHypotheses%20%3A%20TacticM%20(List%20LocalDecl)%20%3A%3D%20do%0A%20%20let%20mut%20hypotheses%20%3A%20List%20LocalDecl%20%3A%3D%20%5B%5D%0A%20%20let%20goal%20%E2%86%90%20getMainGoal%20%20--%20the%20dynamically%20generated%20hypotheses%20are%20associated%20with%20this%20particular%20goal%0A%20%20for%20ldecl%20in%20(%E2%86%90%20goal.getDecl).lctx%20do%0A%20%20%20%20if%20ldecl.isImplementationDetail%20then%20continue%0A%20%20%20%20hypotheses%20%3A%3D%20ldecl%20%3A%3A%20hypotheses%0A%20%20return%20hypotheses%0A%0Adef%20getAllHypothesesNames%20%3A%20TacticM%20(List%20Name)%20%3A%3D%20do%0A%20%20let%20mut%20hypotheses_names%20%3A%20List%20Name%20%3A%3D%20%5B%5D%0A%20%20for%20hypothesis%20in%20%E2%86%90%20getAllHypotheses%20do%0A%20%20%20%20hypotheses_names%20%3A%3D%20hypothesis.userName%20%3A%3A%20hypotheses_names%0A%20%20return%20hypotheses_names%0Aelab%20%22getAllHypothesesNames%22%20%3A%20tactic%20%3D%3E%20do%0A%20%20let%20names%20%E2%86%90%20getAllHypothesesNames%0A%20%20logInfo%20(%22Hyp%20names%3A%22%20%2B%2B%20toString%20names)%0A%0Adef%20isNat%20(e%3A%20Expr)%3A%20MetaM%20Bool%20%3A%3D%20do%0A%20%20let%20type_expr%20%E2%86%90%20inferType%20e%0A%20%20return%20type_expr.isConstOf%20%60Nat%0A%0Apartial%20def%20mkPrettyNameHelper(hypNames%20%3A%20List%20Name)%20(base%20%3A%20Name)%20(i%20%3A%20Nat)%20%3A%20Name%20%3A%3D%0A%20%20let%20candidate%20%3A%3D%20base.appendIndexAfter%20i%0A%20%20if%20(hypNames).contains%20candidate%20then%0A%20%20%20%20mkPrettyNameHelper%20hypNames%20base%20(i%2B1)%0A%20%20else%0A%20%20%20%20candidate%0A%0A%2F--%20Names%20a%20function%20baseName_idx%20if%20that%20is%20available.%20%20otherwise%2C%20names%20it%20baseName_idx%2B1%20if%20available...and%20so%20on.%20-%2F%0Adef%20mkPrettyName%20(baseName%20%3A%20Name)%20(idx%20%3A%20Nat)%20%3A%20TacticM%20Name%20%3A%3D%20do%0A%20%20return%20mkPrettyNameHelper%20(%E2%86%90%20getAllHypothesesNames)%20baseName%20idx%0A%0A%2F--%20Generalizing%20a%20term%20in%20a%20theorem%20%20-%2F%0Adef%20generalizeTerm%20(e%20%3A%20Expr)%20(x%3F%20%3A%20Option%20Name%20%3A%3D%20none)%20(h%3F%20%3A%20Option%20Name%20%3A%3D%20none)%20%3A%20TacticM%20Unit%20%3A%3D%20do%0A%20%20%20%20let%20x%20%3A%3D%20x%3F.getD%20(%E2%86%90%20mkPrettyName%20%60x%200)%20--%20use%20the%20given%20variable%20name%2C%20or%20if%20it's%20not%20there%2C%20make%20one%0A%20%20%20%20let%20h%20%3A%3D%20h%3F.getD%20(%E2%86%90%20mkPrettyName%20%60h%200)%20--%20use%20the%20given%20hypothesis%20name%2C%20or%20if%20it's%20not%20there%2C%20make%20one%0A%20%20%20%20let%20genArg%20%3A%20GeneralizeArg%20%3A%3D%20%7B%20expr%20%3A%3D%20e%2C%20xName%3F%20%3A%3D%20x%2C%20hName%3F%20%3A%3D%20h%20%7D%0A%20%20%20%20let%20(_%2C%20new_goal)%20%E2%86%90%20(%E2%86%90getGoalVar).generalize%20(List.toArray%20%5BgenArg%5D)%0A%20%20%20%20setGoals%20%5Bnew_goal%5D%0A%0Adef%20getSubexpressionsIn%20(e%20%3A%20Expr)%20%3A%20MetaM%20(List%20Expr)%20%3A%3D%0A%20%20let%20rec%20getSubexpressionsInRec%20(e%20%3A%20Expr)%20(acc%20%3A%20List%20Expr)%20%3A%20MetaM%20(List%20Expr)%20%3A%3D%0A%20%20%20%20match%20e%20with%0A%20%20%20%20%7C%20Expr.forallE%20_%20d%20b%20_%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20d%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.lam%20_%20d%20b%20_%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20d%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.letE%20_%20t%20v%20b%20_%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20t%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20v%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.app%20f%20a%20%20%20%20%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20f%20acc)%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20a%20acc)%0A%20%20%20%20%7C%20Expr.mdata%20_%20b%20%20%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20Expr.proj%20_%20_%20b%20%20%20%20%20%20%20%20%3D%3E%20return%20%5Be%5D%20%2B%2B%20(%E2%86%90%20getSubexpressionsInRec%20b%20acc)%0A%20%20%20%20%7C%20_%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%3D%3E%20return%20acc%0A%20%20getSubexpressionsInRec%20e%20%5B%5D%0A%0A%0Adef%20isAtomicNat%20(e%20%3A%20Expr)%20%3A%20MetaM%20Bool%20%3A%3D%20do%0A%20%20if%20not%20(%E2%86%90%20isNat%20e)%20then%20return%20false%20else%0A%20%20%20%20let%20rec%20getFirstNonAppTerm%20(e%20%3A%20Expr)%20%3A%20MetaM%20Expr%20%3A%3D%20match%20e%20with%0A%20%20%20%20%7C%20Expr.app%20f%20_%20%3D%3E%20return%20(%E2%86%90%20getFirstNonAppTerm%20f)%0A%20%20%20%20%7C%20_%20%3D%3E%20return%20e%0A%20%20%20%20let%20nonAppTerm%20%E2%86%90%20getFirstNonAppTerm%20e%0A%20%20%20%20--%20dbg_trace%20repr%20e%0A%20%20%20%20--%20dbg_trace%20%22%3E%3E%3E%22%0A%20%20%20%20if%20nonAppTerm.isConstOf%20%60OfNat.ofNat%20--nonAppTerm.isLit%20-%0A%20%20%20%20%20%20then%0A%20%20%20%20%20%20%20%20--%20dbg_trace%20repr%20nonAppTerm%3B%20dbg_trace%20%22%3D%3D%3D%3D%3D%3D%3D%3D%3D%3D%22%3B%0A%20%20%20%20%20%20%20%20return%20true%0A%20%20%20%20%20%20else%0A%20%20%20%20%20%20%20%20--%20dbg_trace%20repr%20nonAppTerm%3B%20dbg_trace%20%22%3D%3D%3D%3D%3D%3D%3D%3D%3D%3D%22%3B%0A%20%20%20%20%20%20%20%20return%20false%0A%0A%0A%2F-%20Get%20(in%20a%20list)%20all%20subexpressions%20that%20are%20just%20a%20single%20natural%20numbers%20-%2F%0Adef%20getIfAtomicNat%20(subexpr%20%3A%20Expr)%20%3A%20MetaM%20(Option%20Expr)%20%3A%3D%20do%0A%20%20if%20(%E2%86%90%20isAtomicNat%20subexpr)%0A%20%20%20%20then%20return%20some%20subexpr%0A%20%20%20%20else%20return%20none%0A%0A%2F--%20Returns%20single%20nats%20like%203%20and%204%2C%20not%203%5E4%20or%203*4%20-%2F%0Adef%20getAtomicNatsIn%20(e%20%3A%20Expr)%20%3A%20MetaM%20(List%20Expr)%20%3A%3D%20do%0A%20%20let%20subexprs%20%E2%86%90%20getSubexpressionsIn%20e%0A%20%20let%20natSubexprs%20%E2%86%90%20subexprs.filterMapM%20getIfAtomicNat%0A%20%20return%20natSubexprs%0A%0A%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%2F-%20The%20exercise%20-%2F%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%0A%2F--%20Generalizing%20all%20natural%20numbers%20in%20a%20theorem%20%20-%2F%0Aelab%20%22generalizeAllNats%22%20%3A%20tactic%20%3D%3E%20do%0A%20%20let%20nats%20%E2%86%90%20getAtomicNatsIn%20(%E2%86%90%20getGoalType)%0A%20%20nats.forM%20generalizeTerm%0A%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%2F-%20The%20test%20-%2F%0A%2F-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%20-%2F%0A%0Aexample%20%3A%202%5E4%20%25%205%20%3D%201%20%3A%3D%20by%0A%20%20generalizeAllNats%0A%20%20rw%20%20%5B%E2%86%90h_0%2C%20%E2%86%90h_1%2C%20%E2%86%90h_2%2C%20%E2%86%90h_3%5D%3B%20rfl) is in the Lean 4 web editor.

## Examining the proof term

We want to notice that we don’t really need thee numbers to be, say, 2 and 5.   Because in the proof term, the only fact we use about 2 is that it is coprime to 5, and the only fact we use about 5 is that it is prime.

So, how do we go about collecting that information from the proof term?

To see the proof term at a glance, use the macro `#print`.
- We can see the simple proof prints this simple proof term:
	![](Screen%20Shot%202023-12-18%20at%2012.48.30%20PM.png)
- And the complicated proof prints a more complicated proof term:
	![](Screen%20Shot%202023-12-18%20at%2012.47.32%20PM.png)

Now how do we extract that information in code?

We can write a helper function `getTheoremProof`,
```js
def getTheoremProof (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | failure -- get the declaration with that name
  return thm.value!
```
# Calling tactics with arguments

We know how to call a `macro` with arguments.  But macros only let us implement things that are already commands.  
```js
macro "contraposWith" h:ident : tactic => `(tactic|
  (revert $h; contrapose)
)
```

If we need to call a customized `elab` with arguments, we can use `ident` and then `getId`.  We’ll do this to create some scaffolding for our autogeneralize tactic.
```js
def autogeneralize (hypName : Name) : TacticM Unit := do
  logInfo hypName

elab "autogeneralize" h:ident : tactic =>
  autogeneralize h.getId

example : True := by
  have multPermuteHyp := multPermute
  autogeneralize multPermuteHyp 
```
# Accessing the proof of a hypothesis

Suppose we create the hypothesis `h` using
```js
have h : 1+1 = 2 := by rfl
```


Athen later, we want to access the proof of the given hypothesis `h`.  The below code doesn’t work.
```js
def printProofOf (hypName : Name) : TacticM Unit := do
  logInfo hypName
  let hyp ← getHypothesisByName hypName
  let hypType := hyp.type
  let hypValue := hyp.hasValue
  logInfo ("Type of hypothesis: " ++ hypType)
  logInfo ("Value of hypothesis? " ++ (toString hypValue))
  -- printing "hyp.value" in the line below causes a panic
  -- logInfo ("Value of hypothesis? " ++ hyp.value)
  
elab "printProofOf" h:ident : tactic =>
  printProofOf h.getId

example : True := by
  have h : 1+1 = 2 := by rfl
  printProofOf h 
```

Changing the `have` to a `let` fixes the issue.

For whatever reason Lean remembers the proofs of `let` statements, but throws away the proofs of `have` statements.  (Thanks Anand, for telling me about this!)

So, if the proof of your hypothesis is ever important, use `let`. And if your hypothesis is proof-irrelevant, use `have`.


```js
def printProofOf (hypName : Name) : TacticM Unit := do
  logInfo hypName
  let hyp ← getHypothesisByName hypName
  let hypType := hyp.type
  let hypValue := hyp.value
  logInfo ("Type of hypothesis: " ++ hypType)
  logInfo ("Value of hypothesis? " ++ hyp.value)

elab "printProofOf" h:ident : tactic =>
  printProofOf h.getId

example : True := by
  let h : 1+1 = 2 := by rfl
  printProofOf h 
```

Note that the logic of `printProofOf` is the same.  So ultimately, we just use this function:
```js
def getHypothesisProof (h : Name) : TacticM Expr := do
  let hyp ← getHypothesisByName h
  return hyp.value
```

To be friendly to our future self, we can modify it like this:
```js
def getHypothesisProof (h : Name) : TacticM Expr := do
  let hyp ← getHypothesisByName h
  if hyp.hasValue
    then return hyp.value
    else throwError "The hypothesis was likely declared with a 'have' rather than 'let' statement, so its proof is not accessible."

elab "printHypothesisProof"  h:ident : tactic => do
  let pf ← getHypothesisProof h.getId
  logInfo pf
```

And now, if we try doing the same thing as before we get an error, to save our future selves the trouble!
```js
example : True := by
  have multPermuteHyp := multPermute
  have h : 1+1 = 2 := by rfl
  printHypothesisProof h -- adds multPermuteGen to list of hypotheses

```
![](Screen%20Shot%202023-12-26%20at%204.57.07%20PM.png)


# Converting Syntax to Expressions

Inside a theorem, we can call generalize like this:
```js
example : 2*2=4 :=
by
  generalize hm : @HMul.hMul Nat Nat Nat instHMul = f
```

But inside a tactic, we aren’t allowed to access these high level tactics.  We have to call generalize like this: 
```js
generalizeTerm ...
```

But…we want to go from that string `"@HMul.hMul Nat Nat Nat instHMul"` into an expression.

Lean obviously does this somehow, because when we do it in the theorem, it gets done.

So how can we replicate that behaviour?

What’s actually happening is that the string `"@HMul.hMul Nat Nat Nat instHMul"`  is `Syntax`.  And to go from `Syntax` to `Expr`, we need to use `elabTerm`.  [Graphic from Evgenia Karunus](https://lakesare.brick.do/metaprogramming-in-lean-BEwZboNyq9ZO)
![](Screen%20Shot%202023-12-28%20at%206.18.22%20PM-1.png)

This is a part of the Lean compilation process.  [Graphic from Evgenia Karunus](https://lakesare.brick.do/metaprogramming-in-lean-BEwZboNyq9ZO)
![](Screen%20Shot%202023-12-28%20at%206.42.09%20PM-1.png)

So it might be handy to create a function that takes in the term, and outputs it as an expression, using `elabTerm`.

```js
def syntaxToExpr (e : TermElabM Syntax) : TermElabM Expr := do
  let e ← elabTermAndSynthesize (← e) none
  return e
```

Then, to make sure Lean parses the string we give it as `Syntax`, we need to wrap it with a ```()``
```js
#eval syntaxToExpr `(@HMul.hMul Nat Nat Nat instHMul)
```

And indeed, we get what we’d expect.
![](Screen%20Shot%202023-12-28%20at%206.24.59%20PM.png)

Note that in the above function, instead of using the `TacticM` or `MetaM` monad, we use an elaboration monad: `TermElabM`.

Finally, using what our `syntaxtoExpr` printed out, we can guide how to create that expression from scratch using `mkApp`.

```js
elab "generalizef" : tactic => do
  let hmul := .const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero]
  let nat := .const ``Nat []
  let inst :=   mkApp2 (.const `instHMul [Lean.Level.zero]) nat (.const `instMulNat [])
  let f := mkApp4 hmul nat nat nat inst
  generalizeTerm f

example : True := by
  generalizef
  simp
```

# Recursing into metavariable expressions

We had written a simple `getHypothesisProof` function.
```js
def getHypothesisProof (h : Name) : TacticM Expr := do
  let hyp ← getHypothesisByName h
  if hyp.hasValue
    then return hyp.value
  else throwError [...]
```


But the expression returned by `hyp.value` is actually a metavariable expression.  So while it prints ok, it’s difficult to recurse on — all you get is a `mvarid`.

To get the actual proof term that we can recurse on, we need to use `getExprMVarAssignemnt`.  Now instead of returning an Expr that is an `mvar`, it returns an expression that is a `lam`.
- you need ``getExprMVarAssignemnt` if the hypothesis proof written with ``:= by ...
- and you use `hyp.value` if the hypothesis proof is written just like `:= proof term`



```js
def getHypothesisProof (h : Name) : TacticM Expr := do
  let hyp ← getHypothesisByName h
  if hyp.hasValue
    then
      let val ← getExprMVarAssignment? hyp.value.mvarId!
      return ← val
  else throwError [...]
```













# Converting between TacticM and MetaM

Sometimes you’ll write a method that uses the `MetaM` monad.  (Like `getTheoremStatement`).

But then you’ll call it within a function that uses `TacticM`.  And so you’ll get an error saying it expected `TacticM`.
```js
let theoremStatements ← theoremNames.mapM getTheoremStatement
```

It would be annoying to have to write a custom function each time— where you take the statement that was a MetaM, and rewrite it as a TacticM, like `def getTheoremStatement' (n : Name) : TacticM Expr := return ← getTheoremStatement n`.  

That’s so tedious! What you should use is `liftMetaM`, which will turn unwrap the `MetaM` monad and rewrap it into whatever monad makes sense in context.
```js
let theoremStatements ← liftMetaM (theoremNames.mapM getTheoremStatement)
```
# Converting between TacticM and OptionM

Again, same deal — if you have an `option` but you want something else, use  use `liftOption`.

So this might throw an error because “val” is type “Option Expr”.
```js
def getHypothesisProof (h : Name) : TacticM Expr := do
	....
	return ← val
```
`
`But this fixes it
```js
def getHypothesisProof (h : Name) : TacticM Expr := do
	....
	return ← liftOption val
```

Here’s the full context: 
```js
def getHypothesisProof (h : Name) : TacticM Expr := do
  let hyp ← getHypothesisByName h
  if hyp.hasValue
    -- then return hyp.value
    then
      let val ← getExprMVarAssignment? hyp.value.mvarId!
      return ← liftOption val
    else throwError "The hypothesis was likely declared with a 'have' rather than 'let' statement, so its proof is not accessible."

```
# Mapping lists

We know how to filter lists — with `filterM`.

But if we want to take every item in a list, and get some property about it, we use `mapM`.

```js
let freeIdentsTypes ← liftMetaM (freeIdents.mapM getTheoremStatement)
```


# Checking if an expression contains a subexpression

In most programming languages, this might be under `contains`.  In lean, it is `occurs`.  As in, `e.occurs f` returns true if the expression `e` occurs in the expression `f`.  

So, we update our code accordingly.  Now, we only keep the expressions that contain the generalized term f (which in our case is multiplication) in their type.
```js
let freeIdentsContainingF := freeIdentsTypes.filter f.occurs
```
# Replacing parts of expressions

In Lean, we use the `replace` function.
```js
originalExpr.replace replacementFunction
```

The `replace` function takes in an expression to match on, and outputs…
- `none` if the expression shouldn’t be changed
- `some X` if the expression should be changed to `X`.

Here’s a full example
```js
-- Suppose you have an expression 1 + 1
def originalExpr : Expr := mkApp2 (Expr.const `Nat.add []) (mkNatLit 1) (mkNatLit 1)

-- Define a replacement function
def replacementFunction : Expr → Option Expr
  | .lit (Literal.natVal 1) => some $ .lit (Literal.natVal 2)
  | _                      => none

-- -- Use the replace function to replace all occurrences of "1" in the original expression with "2"
def replacedExpr : Expr := originalExpr.replace replacementFunction

-- Print the original and replaced expressions
#eval ppExpr originalExpr
#eval ppExpr replacedExpr
```
# Matching expressions to expressions

Here’s an issue you may run into when writing inductive matching functions.

I can create a matching function:
```js
def matchThese : Expr →  String
  | .const `Nat []  => "The two match."
  | _          => "The two don't match."

```

But when I try to generalize out the pattern it matches to, Lean doesn’t seem to recognize it as a valid pattern anymore.
```js
def matchTheseGeneralized_Failing (template : Expr) : Expr →  String
  | template   => "The two match."
  | _          => "The two don't match." 
#eval matchTheseGeneralized_Failing (.const `Nat []) (.const `Real []) -- falsely says they match
```


(The `_` is listed as a “redundant alternative”, which makes me think that template is seen as something that matches with everything).

I can get around it by using == as follows, but am curious what’s going on!
```js
def matchTheseGeneralized_Working (template : Expr) : Expr → String := fun e =>
  if e == template
    then "The two match."
    else "The two don't match." 
#eval matchTheseGeneralized_Failing (.const `Nat []) (.const `Real [])  -- correctly saying they don't match
```


Code [playground](https://lean.math.hhu.de/#code=import%20Lean%0Aopen%20Lean%20Elab%20Tactic%20Meta%20Term%0A%0Adef%20matchThese%20%3A%20Expr%20%E2%86%92%20%20String%0A%20%20%7C%20.const%20%60Nat%20%5B%5D%20%20%3D%3E%20%22The%20two%20match.%22%0A%20%20%7C%20_%20%20%20%20%20%20%20%20%20%20%3D%3E%20%22The%20two%20don't%20match.%22%0A%0Adef%20matchTheseGeneralized_Failing%20(template%20%3A%20Expr)%20%3A%20Expr%20%E2%86%92%20%20String%0A%20%20%7C%20template%20%20%20%3D%3E%20%22The%20two%20match.%22%0A%20%20%7C%20_%20%20%20%20%20%20%20%20%20%20%3D%3E%20%22The%20two%20don't%20match.%22%0A%0Adef%20matchTheseGeneralized_Working%20(template%20%3A%20Expr)%20%3A%20Expr%20%E2%86%92%20String%20%3A%3D%20fun%20e%20%3D%3E%0A%20%20if%20e%20%3D%3D%20template%0A%20%20%20%20then%20%22The%20two%20match.%22%0A%20%20%20%20else%20%22The%20two%20don't%20match.%22%0A%0A%23eval%20matchThese%20(.const%20%60Nat%20%5B%5D)%20--%20match%0A%23eval%20matchThese%20(.const%20%60Real%20%5B%5D)%20--%20don't%20match%0A%0A%23eval%20matchTheseGeneralized_Failing%20(.const%20%60Nat%20%5B%5D)%20(.const%20%60Nat%20%5B%5D)%20--%20match%0A%23eval%20matchTheseGeneralized_Failing%20(.const%20%60Nat%20%5B%5D)%20(.const%20%60Real%20%5B%5D)%20--%20FAILURE%3A%20false%20positive%0A%0A%23eval%20matchTheseGeneralized_Working%20(.const%20%60Nat%20%5B%5D)%20(.const%20%60Nat%20%5B%5D)%20--%20match%0A%23eval%20matchTheseGeneralized_Working%20(.const%20%60Nat%20%5B%5D)%20(.const%20%60Real%20%5B%5D)%20--%20don't%20match) here: 

Anand says his guess is “that the template in the pattern match is treated as a new variable.”

B/c he gets unused variable errors.

That’s because usually in this syntax, it’s a new variable…letting you return the same thing
```js
 def wrap : Expr → Option Expr
    | original => some original
```
# Puzzle — replacing parts of expressions

Using that replacement function, replace all instances of 

This is our hardcoded replacement function, which replaces the specific multiplication `*` operator  with the more general `f` operator.
```js
def replacementRule' : Expr → Option Expr
  | (Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
        (Lean.Expr.const `Nat []))
      (Lean.Expr.const `Nat []))
    (Lean.Expr.const `Nat []))
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Nat []))
    (Lean.Expr.const `instMulNat []))) => some $ (.const `f [])
  | _                      => none
```

When we test it out…
```js
let e := freeIdentsContainingF[0]!
let replaced := e.replace replacementRule'
logInfo ("Before: " ++ e)
logInfo ("After: " ++ replaced)
```

…it works.
![](Screen%20Shot%202023-12-31%20at%203.47.40%20PM.png)

Now, generalize it.
```js
/-- Creating a replacementRule to replace "original" with "replacement" -/
def replacementRule (original : Expr) (replacement: Expr) : Expr → Option Expr
  
	-- FILL THIS IN
```

…so that `replacementRule f (mkConst fName)` gives us the same function.
```js
let e := freeIdentsContainingF[0]!
let replaced := e.replace replacementRule f (mkConst fName)
logInfo ("Before: " ++ e)
logInfo ("After: " ++ replaced)
```

We should get the same result.
![](Screen%20Shot%202023-12-31%20at%203.47.40%20PM-1.png)


Answer:
```js
def replacementRule (original : Expr) (replacement: Expr) : Expr → Option Expr := fun e =>
  if e == original
    then some replacement
    else none
```


(Pattern matching like `| original => ...` doesn’t work…because Lean interprets `original` as a new variable you’re using, so it would interpret
`| original => some original` to take in any pattern, and wrap it in a “some”




# Working within the local context

Sometimes you can get away without explicitly calling `withContext`.   Here, we can get the type and proof of a hypothesis quite simply.
```js
elab "hypothesisPrinting" : tactic => do
  let hypName := `h

  let hypType ← getHypothesisType hypName
  logInfo hypType

  let hypProof ← getHypothesisProof hypName
  logInfo hypProof

  let hypFVarId ← getHypothesisFVarId hypName
  logInfo (repr hypFVarId)

example : True := by
  let h : 1+1=2 := by simp
  hypothesisPrinting 
  assumption
```

Sometimes, you can’t get away with it.  Here, we can get and print the `fvarid` of a hypothesis without an error, but calling `getDecl` doesn’t work…
```js
elab "hypothesisPrinting2" : tactic => do
  let hypName := `h

  let hypFVarId ← getHypothesisFVarId hypName
  logInfo (repr hypFVarId)

  let d ← hypFVarId.getDecl
  logInfo (d.type)

example : True := by
  let h : 1+1=2 := by simp
  hypothesisPrinting2
  assumption
```
![](Screen%20Shot%202023-12-31%20at%206.15.58%20PM.png)

…until we fix it by adding a `withContext` around the code that retrieves the declaration:
```js
elab "hypothesisPrinting2'" : tactic => do
  let hypName := `h

  let hypFVarId ← getHypothesisFVarId hypName
  logInfo (repr hypFVarId)

  (← getMainGoal).withContext do
    let d ← hypFVarId.getDecl
    logInfo (d.type)

example : True := by
  let h : 1+1=2 := by simp
  hypothesisPrinting2'
  simp
```

The full code is in the[ Lean Web editor here](https://lean.math.hhu.de/#code=import%20Lean%0Aopen%20Lean%20Elab%20Tactic%20Meta%20Term%0A%0A--%20%20Tactic%20get%20a%20hypothesis%20by%20its%20name%20-%2F%0Adef%20getHypothesisByName%20(h%20%3A%20Name)%20%3A%20TacticM%20LocalDecl%20%3A%3D%20do%0A%20%20let%20goal%20%E2%86%90%20getMainGoal%20%20--%20the%20dynamically%20generated%20hypotheses%20are%20associated%20with%20this%20particular%20goal%0A%20%20for%20ldecl%20in%20(%E2%86%90%20goal.getDecl).lctx%20do%0A%20%20%20%20if%20ldecl.isImplementationDetail%20then%20continue%0A%20%20%20%20if%20ldecl.userName%20%3D%3D%20h%20then%0A%20%20%20%20%20%20return%20ldecl%0A%20%20throwError%20%22No%20hypothesis%20by%20that%20name.%22%0A%0A%2F--%20Get%20the%20FVarID%20for%20a%20hypothesis%20(given%20its%20name)%20-%2F%0Adef%20getHypothesisFVarId%20(h%20%3A%20Name)%20%3A%20TacticM%20FVarId%20%3A%3D%20do%0A%20%20let%20hyp%20%E2%86%90%20getHypothesisByName%20h%0A%20%20return%20hyp.fvarId%0A%0A%2F--%20Get%20the%20proposition%20for%20a%20given%20hypothesis%20(given%20its%20name)%20-%2F%0Adef%20getHypothesisType%20(h%20%3A%20Name)%20%3A%20TacticM%20Expr%20%3A%3D%20do%0A%20%20let%20hyp%20%E2%86%90%20getHypothesisByName%20h%0A%20%20return%20hyp.type%0A%0A%2F--%20Get%20the%20proof%20of%20a%20given%20hypothesis%20(given%20its%20name)%20-%2F%0Adef%20getHypothesisProof%20(h%20%3A%20Name)%20%3A%20TacticM%20Expr%20%3A%3D%20do%0A%20%20let%20hyp%20%E2%86%90%20getHypothesisByName%20h%0A%20%20if%20hyp.hasValue%0A%20%20%20%20--%20then%20return%20hyp.value%0A%20%20%20%20then%0A%20%20%20%20%20%20let%20val%20%E2%86%90%20getExprMVarAssignment%3F%20hyp.value.mvarId!%0A%20%20%20%20%20%20return%20%E2%86%90%20liftOption%20val%0A%20%20%20%20else%20throwError%20%22The%20hypothesis%20was%20likely%20declared%20with%20a%20'have'%20rather%20than%20'let'%20statement%2C%20so%20its%20proof%20is%20not%20accessible.%22%0A%0A%2F--%20Demo%20of%20retrieving%20info%20within%20and%20without%20context%20-%2F%0Aelab%20%22hypothesisPrinting1%22%20%3A%20tactic%20%3D%3E%20do%0A%20%20let%20hypName%20%3A%3D%20%60h%0A%0A%20%20--%20Get%20the%20type%20and%20proof%20and%20fvar%20--%20doesn't%20need%20withContext%0A%20%20let%20hypType%20%E2%86%90%20getHypothesisType%20hypName%0A%20%20logInfo%20hypType%0A%0A%20%20let%20hypProof%20%E2%86%90%20getHypothesisProof%20hypName%0A%20%20logInfo%20hypProof%0A%0A%20%20let%20hypFVarId%20%E2%86%90%20getHypothesisFVarId%20hypName%0A%20%20logInfo%20(repr%20hypFVarId)%0A%0Aexample%20%3A%20True%20%3A%3D%20by%0A%20%20let%20h%20%3A%201%2B1%3D2%20%3A%3D%20by%20simp%0A%20%20hypothesisPrinting1%0A%20%20simp%0A%0Aelab%20%22hypothesisPrinting2%22%20%3A%20tactic%20%3D%3E%20do%0A%20%20let%20hypName%20%3A%3D%20%60h%0A%0A%20%20let%20hypFVarId%20%E2%86%90%20getHypothesisFVarId%20hypName%0A%20%20logInfo%20(repr%20hypFVarId)%0A%0A%20%20let%20d%20%E2%86%90%20hypFVarId.getDecl%0A%20%20logInfo%20(d.type)%0A%0Aexample%20%3A%20True%20%3A%3D%20by%0A%20%20let%20h%20%3A%201%2B1%3D2%20%3A%3D%20by%20simp%0A%20%20hypothesisPrinting2%0A%20%20simp%0A%0A%0Aelab%20%22hypothesisPrinting2'%22%20%3A%20tactic%20%3D%3E%20do%0A%20%20let%20hypName%20%3A%3D%20%60h%0A%0A%20%20let%20hypFVarId%20%E2%86%90%20getHypothesisFVarId%20hypName%0A%20%20logInfo%20(repr%20hypFVarId)%0A%0A%20%20(%E2%86%90%20getMainGoal).withContext%20do%0A%20%20%20%20let%20d%20%E2%86%90%20hypFVarId.getDecl%0A%20%20%20%20logInfo%20(d.type)%0A%0Aexample%20%3A%20True%20%3A%3D%20by%0A%20%20let%20h%20%3A%201%2B1%3D2%20%3A%3D%20by%20simp%0A%20%20hypothesisPrinting2'%0A%20%20simp)

I’m not exactly sure when you need to use `withContext`.  

But a rule of thumb may be that whenever you get an `unknown variable` error when the variable is actually in the context, try seeing if `withContext` fixes the error.

Keep this in mind for the next puzzle!

# Generalizing Arguments

You can use `generalize ... at h` to generalize at a hypothesis `h`.

For example, we use it here, after having declared `h` with a `have`statement.

```
theorem multPermute''' : True :=
by
  have h :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  generalize @HMul.hMul Nat Nat Nat instHMul = f at h
  simp
```

But we can’t do it here, after having declared `h` with a `let`statement.
```js
theorem multPermute'' : True :=
by
  let h :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  generalize @HMul.hMul Nat Nat Nat instHMul = f at h
  simp
```

You get a type error.
![](Screen%20Shot%202023-12-31%20at%207.34.13%20PM.png)

I think this is because the new type doesn’t match the proof term…but if you don’t include the proof term, it’s no issue?

So now we need to have 
- one hypothesis that has an associated term (that we can extract the proof from)
- one hypothesis with no associated proof term (whose type we can generalize without errors)

# Calling tactics within labs

Use `evalTactic`

(Example from Lean 4 meta programming book)

```js
elab "suppose " n:ident " : " t:term : tactic => do
  let n : Name := n.getId
  let mvarId ← getMainGoal
  mvarId.withContext do
  let t ← elabType t
  let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
  let (_, mvarIdNew) ← MVarId.intro1P $ ← mvarId.assert n t p
  replaceMainGoal [p.mvarId!, mvarIdNew]
  evalTactic $ ← `(tactic|rotate_left)

example : 0 + a = a := by
  suppose add_comm : 0 + a = a + 0
  rw [add_comm]; rfl -- closes the initial main goal
  rw [Nat.zero_add]; rfl -- proves `add_co

```
# Creating for-all expressions

We use `forallE`:
```js
Expr.forallE `x (.sort .zero) (.app (.app (.const `And []) (.bvar 0)) (.bvar 0)) .default
```

The arguments are:
- the name of the bound variable  e.g. ```x``
- its type e.g. `Prop` which is `.sort .zero`.
- the expression (probably using the bound variables) that depends on it e.g. `...(.bvar 0)...`
- the binder info (e.g. `.default`)

# Folding over a list.

Suppose we want to “join together” every item in a list.


We can do this using `foldl`
where:
```js
foldl f init [a, b, c] = f (f (f init a) b) c
```

Using a multiplication symbol, for example, we get this:
```js
foldl f 1 [a, b, c] = * (* (* 1 a) b) c
```
…which is really…
```js
foldl f 1 [a, b, c] = * (* (1 * a) b) c
```
…which is…
```js
foldl f 1 [a, b, c] = * ((1*a)*b) c
```
…which is…
```js
foldl f 1 [a, b, c] = ((1*a)*b)*c
```


A clever way to not have to use a “dummy” initial value like “1” is to split up the list into the first value (the list head) and the rest of it (the list tail)
```js
foldl * [a, b, c].head! [a, b, c].tail
```
…which is…
```
foldl * a [b, c].tail
```
…which is…
```
(* (* a b)c)
```
…which is…
```
(a*b)*c
```
Since our function uses a monad, we’ll use the monad version: `foldlM`.

# When should you `foldl` and when should you `foldr`?

Suppose you have a list of a bunch of hypotheses.
```js
[h1, h2, h3]
```

For the intros tactic to work correctly, you want your end goal to look like this:
```js
h1 → (goal)
```
Or….
```js
h1 → (h2 → goal)
```
Or…
```js
h1 → (h2 → (h3 → goal))
```
And so on.  That is, you want right-associativity by default.

In short, `foldl` creates left associativity, and `foldr` creates right associativity.
- This is what happens when we use `foldl` on our hypotheses:
	```js
	((h1→h2)→h3)
	```
- This is what happens when we use `foldr` on our hypotheses:
	```
	(h2→(h3→h1))
	```


But notice the order is wrong!

Example code here:

This is just adding the arrows with `foldl`
```js
def hyps := ["h1", "h2", "h3"]
#eval hyps.tail.foldl (fun s1 s2 => s1 ++ "→" ++ s2) (hyps.head (by simp))
```
Which outputs
```js
h1→h2→h3
```

This is making it clear where the associativity is with `foldl`
```js
def hyps := ["h1", "h2", "h3"]
#eval hyps.tail.foldl (fun s1 s2 => "(" ++ s1 ++ "→" ++ s2 ++ ")") (hyps.head (by simp))
```
Which outputs
```js
((h1→h2)→h3)
```

This is making it clear where the associativity is with `foldr`
```js
def hyps := ["h1", "h2", "h3"]
#eval hyps.tail.foldr (fun s1 s2 => "(" ++ s1 ++ "→" ++ s2 ++ ")") (hyps.head (by simp))

```
Which outputs
```js
(h2→(h3→h1))
```

But note — ahh — the order is wrong!

Puzzle — fix the above `foldr` code so it outputs
```js
(h1→(h2→(h3→g)))
```

Scaffolding:
```js
def hyps := ["h1", "h2", "h3"]
def goal := "g"
#eval ....
```

So, if you’re using `fold` to put together a chain of implications, you should always use `foldr`.

Answer:
```js
def hyps := ["h1", "h2", "h3"]
def goal := "g"
#eval hyps.foldr (fun s1 s2 => "(" ++ s1 ++ "→" ++ s2 ++ ")") (goal)
```
Outputs
```js
(h1→(h2→(h3→g)))
```
# Puzzle — folding over a list

Create an expression that puts an “implies” between every list item in `freeIdentsAbstracted`.

Answer:
```js
def mkImplies (d b : Expr) : TacticM Expr :=
  return Lean.mkForall (← mkFreshUserName `x) BinderInfo.default d b

let genPropType ← freeIdentsAbstracted.tail.foldlM (mkImplies) freeIdentsAbstracted.head!
  logInfo s!"Building up the type {genPropType}"
```
# Debugging — Adding hypotheses without proving them

It may seem that you can get away with creating false statements without proving them

For example here, I create a  false hypotheses that implies any binary operator is associative and commutative…
```js
∀ (f : ℕ → ℕ → ℕ) (n m p : ℕ), f n (f m p) = f m (f n p)
```
…and a bogus proof for it…
```js
let genPropProof := toExpr 42
```
…and then 
```js
createHypothesis genPropType genPropProof `gen
```

To create this…that gets accepted into the Lean context.
![](Screen%20Shot%202024-01-01%20at%202.10.40%20PM.png)

And it looks like we got away with it, but at the end of our code….
```js
def myF (a : Nat) (b : Nat) := a
example : 1=2 := by
  let multPermuteHyp :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  have multPermuteHypGen :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize multPermuteHyp multPermuteHypGen -- adds multPermuteGen to list of hypotheses
  specialize gen myF 1 2 3
  unfold myF at gen
  assumption
```

…we get an error saying they expected that “42” proof to make more sense.
![](Screen%20Shot%202024-01-01%20at%202.13.09%20PM.png)

(Simplify this example by using `createHypothesis` to create a hypothesis that says “False” rather than something this complicated)

# Bound variables

The variable x in “for all x, …” or “there exists x, …” is a bound variable 
- actually it’s just the ones that appear in the body…show image with for all x, x times 2 is even, the SECOND x is the bound variable 
- then show how this expression looks in lean, highlighting the bound variable part

We want to update all references to “f” to be the lates bound variable

Here is the code to do that
```js

```
# Using let statements outside monads

We’re used to using newlines in monads

Without monads, we use semicolons
```js
def countBVars (e : Expr) : Nat :=
  let bvars := (getAllBVars e);
  if bvars == [] then  0
```
# Warning: The fvarid of a hypothesis can change even if the hypothesis doesn’t change

After you change a hypothesis, the FVarId of it changes

Butmore than that — whenever you change the goal at all, the fvarids all change (I think…print stuff out repeatedly to show this)

The fvarid is associated with the goal
That is, lean uses the word “goal” for what we really call “the entire proof state.”

Like in this code here, you have to run `getHypothesisFVarId genThmName` twice.

And if you repeatedly put `  logInfo (repr (← getHypothesisFVarId genThmName))` — it changes each time.

TAKEAWAY: retrieve the FvarId _just_ before you use it

```js
  -- Get details about the un-generalized proof we're going to generalize
  let thmType ← getHypothesisType thmName
  let thmProof ← getHypothesisProof thmName

  -- Put up scaffolding of the generalized proof
  let genThmName := thmName.append `Gen
  createHypothesis thmType thmProof genThmName
  let genThmFVarId ← getHypothesisFVarId genThmName -- the generalized hypothesis (without proof) is the one we'll modify

  -- Get details about the term we're going to generalize
  let hmul := .const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero]
  let nat := .const ``Nat []
  let inst :=   mkApp2 (.const `instHMul [Lean.Level.zero]) nat (.const `instMulNat [])
  let f := mkApp4 hmul nat nat nat inst

  -- Do the first bit of generalization -- generalizing the variable "f" to its type
  let (fName,   fType,      fId) ← generalizeTermInHypothesis genThmFVarId f `f
  --   f       (ℕ → ℕ → ℕ)

  -- Do the next bit of generalization -- figure out which all hypotheses we need to add to make the generalization true
  let genThmType ← autogeneralizeType genThmName thmType thmProof f fName fType fId

  -- Then, prove those hypotheses are all you need.
  let genThmProof := toExpr 42

 

  let l ← getAllHypotheses
  for h in l do
    logInfo (repr h.fvarId)

  -- update the FVarId of the generalized theorem
  let genThmFVarId ← getHypothesisFVarId genThmName 

```
# An elaboration taking a hypothesis and a term

Use `elabTerm`

```js
elab "autogeneralize" h:ident t:term : tactic => do
  let e ← (Lean.Elab.Term.elabTerm t none)
  autogeneralize h.getId e
```
# Comparing expressions: `isDefEq` vs `==`

This is saying there were no occurrences of our term `*` in the expression

What they have in the expression is:
```js
Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
        (Lean.Expr.const `Nat []))
      (Lean.Expr.const `Nat []))
    (Lean.Expr.const `Nat []))
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Nat []))
    (Lean.Expr.const `instMulNat []))
```

What our term elaborates to is:
```js
Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.const
          `HMul.hMul
          [Lean.Level.mvar (Lean.Name.mkNum `_uniq 232341),
           Lean.Level.mvar (Lean.Name.mkNum `_uniq 232340),
           Lean.Level.mvar (Lean.Name.mkNum `_uniq 232339)])
        (Lean.Expr.const `Nat []))
      (Lean.Expr.const `Nat []))
    (Lean.Expr.const `Nat []))
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.const `instHMul [Lean.Level.mvar (Lean.Name.mkNum `_uniq 232342)])
      (Lean.Expr.mvar (Lean.Name.mkNum `_uniq 232343)))
    (Lean.Expr.mvar (Lean.Name.mkNum `_uniq 232344)))
```

It turns out if you ask Lean if these two expressions are equal with
```js
#eval e1==e2
```
It says false.

But if you ask with
```js
#eval (← isDefEq e1 e2)
```
It says true.


So this coarser definition of equality is actually the one we’re interested in.


## the explanation from Anand

Yep, `(. * .)`  is a term with meta-variables.
```js
#check (· * ·)
/-
fun x x_1 => x * x_1 : (x : ?m.3686) → (x_1 : ?m.3696 x) → ?m.3697 x x_1
-/
```
When you try isDefEq, Lean tries to assign the meta-variables to make it equal to the term it is being compared with. If there is an assignment of meta-variables that succeeds, then then those meta-variables are instantiated to those values and the function `(. * .)` specialises down to HMul.hMul Nat Nat Nat (since all the meta-variables are assigned the value Nat).

# Error: Unexpected bound variable

If we isDefEq comparing a bunch of subexpressions, we get this error. 

The solution: — run `hasLooseBVars` to sanitize input — the expressions with loose bvars are not fully formed expressions

So we update `getSubexpressionsIn` accordingly

```js
def getSubexpressionsIn (e : Expr) : List Expr :=
  let rec getSubexpressionsInRec (e : Expr) (acc : List Expr) : List Expr :=
    match e with
    | Expr.forallE _ d b _   => [e] ++ (getSubexpressionsInRec d acc) ++ (getSubexpressionsInRec b acc)
    | Expr.lam _ d b _       => [e] ++ (getSubexpressionsInRec d acc) ++ (getSubexpressionsInRec b acc)
    | Expr.letE _ t v b _    => [e] ++ (getSubexpressionsInRec t acc) ++ (getSubexpressionsInRec v acc) ++ (getSubexpressionsInRec b acc)
    | Expr.app f a           => [e] ++ (getSubexpressionsInRec f acc) ++ (getSubexpressionsInRec a acc)
    | Expr.mdata _ b         => [e] ++ (getSubexpressionsInRec b acc)
    | Expr.proj _ _ b        => [e] ++ (getSubexpressionsInRec b acc)
    | Expr.mvar _            => [e] ++ acc
    | Expr.bvar _            => [e] ++ acc
    | _                      => acc
  let subexprs := getSubexpressionsInRec e [];
  let subexprs := subexprs.filter $ fun subexpr => !subexpr.hasLooseBVars -- remove the ones that will cause errors when parsing
  subexprs
```


# Puzzle — replacing expressions

Modify the replacement rule so it replaces as long as original matches up to definitional equality

Answer:
```js
def replaceIsDefEq (original : Expr) (replacement: Expr) : Expr → MetaM Expr := fun e => do

```
# 

Right now have to write full HMUL stuff

```js
  autogeneralize multPermuteHyp (@HMul.hMul Nat Nat Nat instHMul) -- adds multPermuteGen to list of hypotheses

```


But you can use `.*.`
```js
autogeneralize multPermuteHyp (.*.)
```

And that’s because
```js
(.-1)
```
means
```js
fun x => x - 1
```

So 
```js
(.-.)
```
means
```js
fun x y => x - y
```

So the syntax `.*.` is creating a multiplication function

# Visual clean up

Doesn’t show the proof of the “let” statement in the screen

```js
set_option pp.showLetValues false
```
# Delaboration

Elaboration turns Syntax to an expression.
Delaboration turns Expr into Syntax.

From Lean 4 Metaprogramming:
> During delaboration, Expr is turned into the Syntax object; and then the formatter turns it into a Format object, which can be displayed inLean’s infoview. Every time you log something to the screen, or see some output upon hovering over #check, it’s the work of the delaborator.

So you can override the way its usually implemented
```js
@[delab forallE]
def delabForAlls : Delab := do
  `(1)
```


This will make it so instead of a `forall` statement in the InfoView, you’ll see a 1.

![](Screen%20Shot%202024-01-09%20at%201.33.43%20PM.png)

Let’s start out with the default code (tagged `@[builtin_delab forallE]` if you want to search for it in Moogle)

# Printing strings with objects

`m!"stuff"` prints a MessageData
`f!"stuff"` prints a Format 
`s!"stuff"`prints a string


(Show an example showing one thing and how it differs with all the different things)

![](Screen%20Shot%202024-01-09%20at%201.23.00%20PM.png)


# Using `fold` to create multiple nested lambdas

You have this function
```js
def mkLambda (x : Name) (bi : BinderInfo) (t : Expr) (b : Expr) : Expr :=
  .lam x t b bi

```

And a list of Names and Types  e.g.
```js
Names = [x,y]
Types = [Nat, Real]

```

And you have a body
```js
Body = 1+1
```

You want to create a lambda expression
```js
fun x:Nat => fun y:Real => body
```

How do you do this using mkLambda and List.fold?

# Answer

Here’s code that works
```js
-- Lists of Names and Types
def names : List Name := [`x, `y]
def types : List Expr := [Expr.const ``Nat [], Expr.const ``Real []]

-- Body expression
def body : Expr := (mkNatLit 1)  -- Assuming mkAdd and mkNatLit are available

-- Use list.foldr to create nested lambda expressions
def lambdaExpr : MetaM Expr := do
  let e ← (names.zip types).foldrM
   (fun pair acc => do
    let (name, typ) := pair
    return mkLambda name .default typ acc
  ) body
  return e

#eval lambdaExpr
#eval (do let e ←lambdaExpr; logPrettyExpression e)
```
# Pretty printing with explicits

Sometimes the result of pretty-printing is ambiguous.

It can lead to errors like…you have Lean print out the proof term of something…
```js
theorem fPermute :
∀ (f : Nat → Nat → Nat)
-- (f_assoc : ∀ (n m p : Nat),  f n (f m p) = f (f n m) p ) -- n (m p) = (n m) p
(gen_mul_assoc : ∀ (n m p : Nat),  f (f n m) p = f n (f m p)) -- n (m p) = (n m) p
(gen_mul_comm : ∀ (n m : Nat), f n m = f m n)
(n m p : Nat), f n (f m p) = f m (f n p) -- n (m p) = m (n p)
:= by
  intros f gen_mul_assoc gen_mul_comm n m p
  -- generalize f = fgen
  rw [← gen_mul_assoc]
  rw [gen_mul_comm n m]
  rw [gen_mul_assoc]
#print fPermute
```

And then when you paste it back in, Lean says the proof (the very proof it printed out to you!) is incorrect
```js
theorem fPermute : ∀ (f : ℕ → ℕ → ℕ),
  (∀ (n m p : ℕ), f (f n m) p = f n (f m p)) →
    (∀ (n m : ℕ), f n m = f m n) → ∀ (n m p : ℕ), f n (f m p) = f m (f n p) :=
fun f gen_mul_assoc gen_mul_comm n m p =>
  Eq.mpr (id ((gen_mul_assoc n m p).symm ▸ Eq.refl (f n (f m p) = f m (f n p))))
    (Eq.mpr (id (gen_mul_comm n m ▸ Eq.refl (f (f n m) p = f m (f n p))))
      (Eq.mpr (id (gen_mul_assoc m n p ▸ Eq.refl (f (f m n) p = f m (f n p)))) (Eq.refl (f m (f n p)))))
```


But that’s because there are implicit parameters being passed in that Lean might not be able to figure out.  So reveal all of these use
```js
set_option pp.explicit true
```

Now, when you run…
```js
#print fPermute
```

You get a more elaborate theorem, which raises no errors:
```js
theorem fPermute : ∀ (f : ℕ → ℕ → ℕ),
  (∀ (n m p : ℕ), @Eq ℕ (f (f n m) p) (f n (f m p))) →
    (∀ (n m : ℕ), @Eq ℕ (f n m) (f m n)) → ∀ (n m p : ℕ), @Eq ℕ (f n (f m p)) (f m (f n p)) :=
fun f gen_mul_assoc gen_mul_comm n m p =>
  @Eq.mpr (@Eq ℕ (f n (f m p)) (f m (f n p))) (@Eq ℕ (f (f n m) p) (f m (f n p)))
    (@id (@Eq Prop (@Eq ℕ (f n (f m p)) (f m (f n p))) (@Eq ℕ (f (f n m) p) (f m (f n p))))
      (@Eq.ndrec ℕ (f n (f m p)) (fun _a => @Eq Prop (@Eq ℕ (f n (f m p)) (f m (f n p))) (@Eq ℕ _a (f m (f n p))))
        (@Eq.refl Prop (@Eq ℕ (f n (f m p)) (f m (f n p)))) (f (f n m) p)
        (@Eq.symm ℕ (f (f n m) p) (f n (f m p)) (gen_mul_assoc n m p))))
    (@Eq.mpr (@Eq ℕ (f (f n m) p) (f m (f n p))) (@Eq ℕ (f (f m n) p) (f m (f n p)))
      (@id (@Eq Prop (@Eq ℕ (f (f n m) p) (f m (f n p))) (@Eq ℕ (f (f m n) p) (f m (f n p))))
        (@Eq.ndrec ℕ (f n m) (fun _a => @Eq Prop (@Eq ℕ (f (f n m) p) (f m (f n p))) (@Eq ℕ (f _a p) (f m (f n p))))
          (@Eq.refl Prop (@Eq ℕ (f (f n m) p) (f m (f n p)))) (f m n) (gen_mul_comm n m)))
      (@Eq.mpr (@Eq ℕ (f (f m n) p) (f m (f n p))) (@Eq ℕ (f m (f n p)) (f m (f n p)))
        (@id (@Eq Prop (@Eq ℕ (f (f m n) p) (f m (f n p))) (@Eq ℕ (f m (f n p)) (f m (f n p))))
          (@Eq.ndrec ℕ (f (f m n) p) (fun _a => @Eq Prop (@Eq ℕ (f (f m n) p) (f m (f n p))) (@Eq ℕ _a (f m (f n p))))
            (@Eq.refl Prop (@Eq ℕ (f (f m n) p) (f m (f n p)))) (f m (f n p)) (gen_mul_assoc m n p)))
        (@Eq.refl ℕ (f m (f n p)))))
```

This is a valuable debugging tool — if Lean is giving you some vague error in your meta program about why the proof term doesn’t match the proof type, use `pp.explicit` to paste in the proof term and type into a separate lean file, and investigate where exactly stuff goes wrong.

# Lists vs Arrays

People in Lean tend to use Arrays, instead of Lists

In short, arrays are more efficient.

Both can be dynamically sized
Both have similar methods…

So why would you use a list?
- lists are inductive type in lean…so you can reason about them…so if you have proof s… i
- t’s easier to prove things about lists than 

## Switching between them
- use `[1,2,3]` to make a list
- use `#[1,2,3]` to define an array

## Size
- use `length` for list
- use `size` for array

## Accessing elements
- use `mylist[0]!` for lists
- use `myarray.get! 0` for arrays


# Errors encountered with structures

## Deriving Repr, ToString

## Deriving Inhabited

You can get an error if you perform `get` on an array / list that has no default value.  For example, here modifiers is an array of modifiers, and modifiers has no default value.

```js
let hypName := modifiers.get! i
```

It says:
```js
failed to synthesize instance
  Inhabited Modifier
```

But the fix is to have your structure derive `Inhabited` so it has a default value
```js
structure Modifier where
  oldName : Name                    -- name that exists in the context e.g. Nat.mul_assoc
  newName : Name := mkAbstractedName oldName -- usually something like gen_mul_assoc
  oldType : Expr                    -- the type that has the ungeneralized "f"
  newType : Expr                    -- the type that has the placeholder of "f"
deriving Inhabited
```
# Trick to not having to keep track of bound variables

Instead of doing the custom bvar depths

You can create a temporary hypothesis using `withLocalDecls` (the local decl you’re working “with” is the f)
- and then once you create the lambda for it (using revert) Lean `mkLambdaFVars` takes care of the bound variable tracking for you.

```js
  let genThmProof ← withLocalDecl f.name .default f.type (fun placeholder => do
    let body ← replaceCoarsely f.placeholder placeholder genThmProof
    mkLambdaFVars #[placeholder] body
  )

```


# Debugging proofs

Using `pp.explicit true` then pasting in the thing

For example, here was what printed when I wrote the correct thing and did `#print`
```js
theorem fPermute'' :
∀ (f : Nat → Nat → Nat)
(gen_mul_assoc : ∀ (n m p : Nat),  f (f n m) p = f n (f m p)) -- n (m p) = (n m) p
(gen_mul_comm : ∀ (n m : Nat), f n m = f m n)
(n m p : Nat), f n (f m p) = f m (f n p) -- n (m p) = m (n p)
:= fun f gen_mul_assoc gen_mul_comm n m p =>
  @Eq.mpr (@Eq ℕ (f n (f m p)) (f m (f n p))) (@Eq ℕ (f (f n m) p) (f m (f n p)))
    (@id (@Eq Prop (@Eq ℕ (f n (f m p)) (f m (f n p))) (@Eq ℕ (f (f n m) p) (f m (f n p))))
      (@Eq.ndrec ℕ (f n (f m p)) (fun _a => @Eq Prop (@Eq ℕ (f n (f m p)) (f m (f n p))) (@Eq ℕ _a (f m (f n p))))
        (@Eq.refl Prop (@Eq ℕ (f n (f m p)) (f m (f n p)))) (f (f n m) p)
        (@Eq.symm ℕ (f (f n m) p) (f n (f m p)) (gen_mul_assoc n m p))))
    (@Eq.mpr (@Eq ℕ (f (f n m) p) (f m (f n p))) (@Eq ℕ (f (f m n) p) (f m (f n p)))
      (@id (@Eq Prop (@Eq ℕ (f (f n m) p) (f m (f n p))) (@Eq ℕ (f (f m n) p) (f m (f n p))))
        (@Eq.ndrec ℕ (f n m) (fun _a => @Eq Prop (@Eq ℕ (f (f n m) p) (f m (f n p))) (@Eq ℕ (f _a p) (f m (f n p))))
          (@Eq.refl Prop (@Eq ℕ (f (f n m) p) (f m (f n p)))) (f m n) (gen_mul_comm n m)))
      (@Eq.mpr (@Eq ℕ (f (f m n) p) (f m (f n p))) (@Eq ℕ (f m (f n p)) (f m (f n p)))
        (@id (@Eq Prop (@Eq ℕ (f (f m n) p) (f m (f n p))) (@Eq ℕ (f m (f n p)) (f m (f n p))))
          (@Eq.ndrec ℕ (f (f m n) p) (fun _a => @Eq Prop (@Eq ℕ (f (f m n) p) (f m (f n p))) (@Eq ℕ _a (f m (f n p))))
            (@Eq.refl Prop (@Eq ℕ (f (f m n) p) (f m (f n p)))) (f m (f n p)) (gen_mul_assoc m n p)))
        (@Eq.refl ℕ (f m (f n p)))))
```


Here is what my code is giving me
```js
theorem fPermute''' :
∀ (f : Nat → Nat → Nat)
(gen_mul_assoc : ∀ (n m p : Nat),  f (f n m) p = f n (f m p)) -- n (m p) = (n m) p
(gen_mul_comm : ∀ (n m : Nat), f n m = f m n)
(n m p : Nat), f n (f m p) = f m (f n p) -- n (m p) = m (n p)
:= fun f gen_mul_comm gen_mul_assoc n m p =>
  @Eq.mpr (@Eq ℕ (f n (f m p)) (f m (f n p))) (@Eq ℕ (f (f n m) p) (f m (f n p)))
    (@id (@Eq Prop (@Eq ℕ (f n (f m p)) (f m (f n p))) (@Eq ℕ (f (f n m) p) (f m (f n p))))
      (@Eq.ndrec ℕ (f n (f m p)) (fun _a => @Eq Prop (@Eq ℕ (f n (f m p)) (f m (f n p))) (@Eq ℕ _a (f m (f n p))))
        (@Eq.refl Prop (@Eq ℕ (f n (f m p)) (f m (f n p)))) (f (f n m) p)
        (@Eq.symm ℕ (f (f n m) p) (f n (f m p)) (gen_mul_assoc n m p))))
    (@Eq.mpr (@Eq ℕ (f (f n m) p) (f m (f n p))) (@Eq ℕ (f (f m n) p) (f m (f n p)))
      (@id (@Eq Prop (@Eq ℕ (f (f n m) p) (f m (f n p))) (@Eq ℕ (f (f m n) p) (f m (f n p))))
        (@Eq.ndrec ℕ (f n m) (fun _a => @Eq Prop (@Eq ℕ (f (f n m) p) (f m (f n p))) (@Eq ℕ (f _a p) (f m (f n p))))
          (@Eq.refl Prop (@Eq ℕ (f (f n m) p) (f m (f n p)))) (f m n) (gen_mul_comm n m)))
      (@Eq.mpr (@Eq ℕ (f (f m n) p) (f m (f n p))) (@Eq ℕ (f m (f n p)) (f m (f n p)))
        (@id (@Eq Prop (@Eq ℕ (f (f m n) p) (f m (f n p))) (@Eq ℕ (f m (f n p)) (f m (f n p))))
          (@Eq.ndrec ℕ (f (f m n) p) (fun _a => @Eq Prop (@Eq ℕ (f (f m n) p) (f m (f n p))) (@Eq ℕ _a (f m (f n p))))
            (@Eq.refl Prop (@Eq ℕ (f (f m n) p) (f m (f n p)))) (f m (f n p)) (gen_mul_assoc m n p)))
        (@Eq.refl ℕ (f m (f n p)))))
```

And then I realize it’s flipping the `mul_assoc` and `mul_comm`!

# Tricking the linter

![](Screen%20Shot%202024-01-18%20at%207.19.55%20PM.png)

Calling it `_multPermute` instead of `multPermute` gets the linter to stop complaining

Because the linter is instructed to ignore names beginning with an underscore.

# janky delaboration

It’s so weird it’s writing out the binder names sometimes, and not other times.

![](screen_shot_2024-01-24_at_6.20.28_pm.png)

Why is it happening?  **It turns out, lean only writes out the binder names of for-all statements when they are used in the type.**


# a corollary

When binder names are used in the name, the hypothesis NEEDS to be named.

e.g. this code doesn’t work when we have `(AddCommSemigroup f)`
```js
theorem gen'' : ∀ (f : Type) (AddCommSemigroup f) (a b : f),
  @Eq f (@HAdd.hAdd f f f (@instHAdd f _) a b)
    (@HAdd.hAdd f f f (@instHAdd f _) b a) :=
fun _ _ => add_comm
#print gen''
```

This code does, when we have `(h : AddCommSemigroup f) `
```js
theorem gen'' : ∀ (f : Type) (h : AddCommSemigroup f) (a b : f),
  @Eq f (@HAdd.hAdd f f f (@instHAdd f _) a b)
    (@HAdd.hAdd f f f (@instHAdd f _) b a) :=
fun _ _ => add_comm
#print gen''
```

We can see that when we print it, the stuff that goes the filled-in hole `_` refers to h.  **If it can’t refer to h, it can’t fill in the hole.**