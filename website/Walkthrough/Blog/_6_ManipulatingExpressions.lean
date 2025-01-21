import VersoBlog
import Mathlib.Tactic
open Verso Genre Blog

#doc (Page) "Manipulating Expressions" =>

```leanInit manipulatingExpressions
```

```lean manipulatingExpressions show:=false
set_option linter.unusedVariables false
open Lean Meta Elab Tactic Term
```

We know how to read and change the context in small ways.

Now, to write _really_ powerful tactics in Lean, to really customize _how_ we change the context, we need to work with _expressions_.

# Looking ahead


By the end of the next few sections, we should be able to take in a mathematical statement (e.g. $`2+3=5`) identify all natural number subexpressions in an expression ($`2`,$`3`, $`2+3`,and $`5`).

And what’s the point of that?  It sets us up for the next section.

By the end of the next section, we should be able to generalize a particular natural number subexpression in a statement (e.g $`2+3=5`) to an arbitrary constant of that type, and rewrite the statement accordingly (e.g. $`\exists n : \mathbb{N}, n+3=5`).

This will pave the way for our algorithm that automatically generalizes unnecessarily weak theorems (the big project of this course.)

# What are expressions?

Before a piece of code is compiled into Lean…
- it starts as a **string** that we type into the computer…
- …which as long as it has all the necessary context can later be turned into an **expression**…
- …which then can be evaluated to give a **term**, which is a piece of Lean code.

Expressions, roughly speaking, are an abstract representation of Lean code. By writing programs that manipulate expressions, users can transform one piece of Lean code into another. Expressions can be turned into actual Lean code using an *elaborator*.

So here are expressions…
```lean manipulatingExpressions
def zero := Expr.const ``Nat.zero []

def one := Expr.app (.const ``Nat.succ []) zero
```

And here is how we turn them into fully elaborated code (that is, a term).
```lean manipulatingExpressions
elab "zero" : term => return zero

elab "one" : term => return one
```

The benefit of working with expressions is that they’re easy to modify at a low-level.

The benefit of working with terms is they are actual pieces of code that can be used to prove theorems.

## Where do we use expressions?

We previously constructed expressions when we were creating hypotheses and goals.

The only way to _create_ mathematical statements is to tell Lean the propositions (as expressions), and the only way to _prove_ them is to tell Lean the proofs (as expressions).

For example, we used `mkEq (toExpr 0) (toExpr 0)` to create the expression for the term `0=0`.

# Converting code to expressions

When we turn a natural number into an expression, we’re actually doing something like this:
```lean manipulatingExpressions
def natExpr : Nat → Expr
| 0 => Expr.const ``Nat.zero []
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)

#eval natExpr 2
```

But luckily, there’s a function `toExpr`…
```lean manipulatingExpressions
#eval toExpr 2
```

…that does the same thing.
```lean manipulatingExpressions
#eval isDefEq (toExpr 2) (natExpr 2) -- true
```

# Converting code to expressions: limitations

Unfortunately, `toExpr` only works to express single values.

Instead, if we want the expression $`2+2=4`, we have to write it out laboriously...as we’ll do in the following puzzle.

# Pretty-printing expressions

Before we get into the upcoming puzzle, it’s helpful for debugging to be able to print out expressions nicely.

We can use `ppExpr` (pretty-print expression) for that, and extract it out into this helper function.

```lean manipulatingExpressions
def printPrettyExpression (e : Expr) : MetaM Unit := do
  dbg_trace "{←ppExpr e}"
```

# Puzzle — Constructing Expressions

Here’s what we know:
- `mkEq (toExpr 0) (toExpr 0)` gives us the expression `0=0`
- ``Expr.app (.app (.const `Nat.add []) (toExpr 1)) (toExpr 2)`` gives us the expression `1+2`. (You first apply addition to 1, to create a partially applied function, then you apply it to 2.)

The [exercise is here](https://live.lean-lang.org/#code=import%20Lean%0Aopen%20Lean%20Elab%20Tactic%20Meta%20Term%0A%0A%2F--%20Print%20out%20the%20expression%20in%20a%20human-readable%20way%20%20--%2F%0Adef%20printPrettyExpression%20(e%20%3A%20Expr)%20%3A%20MetaM%20Unit%20%3A%3D%20do%0A%20%20dbg_trace%20%22%7B%E2%86%90ppExpr%20e%7D%22%0A%0A%2F--%20Some%20helpful%20examples%20to%20reference%20--%2F%0A%23eval%20do%20%7BprintPrettyExpression%20%24%20%E2%86%90%20mkEq%20(toExpr%200)%20(toExpr%200)%7D%0A%23eval%20do%20%7BprintPrettyExpression%20%24%20Expr.app%20(.app%20(.const%20%60Nat.add%20%5B%5D)%20(toExpr%200))%20(toExpr%201)%7D%0A%0A%2F-%20The%20puzzle%20-%2F%0A%23eval%20do%20%7B%20--%20should%20print%20out%202%2B3%3D5%0A%20%20let%20two_plus_three_equals_five%20%3A%20Expr%20%E2%86%90%20--%20FILL%20THIS%20OUT%0A%20%20printPrettyExpression%20%24%20two_plus_three_equals_five%0A%7D) in the Lean 4 web editor.
The [answer is here](https://live.lean-lang.org/#code=import%20Lean%0Aopen%20Lean%20Elab%20Tactic%20Meta%20Term%0A%0A%2F--%20Print%20out%20the%20expression%20in%20a%20human-readable%20way%20%20--%2F%0Adef%20printPrettyExpression%20(e%20%3A%20Expr)%20%3A%20MetaM%20Unit%20%3A%3D%20do%0A%20%20dbg_trace%20%22%7B%E2%86%90ppExpr%20e%7D%22%0A%0A%2F-%20Some%20helpful%20examples%20to%20reference%20--%2F%0A%23eval%20do%20%7BprintPrettyExpression%20%24%20%E2%86%90%20mkEq%20(toExpr%200)%20(toExpr%200)%7D%0A%23eval%20do%20%7BprintPrettyExpression%20%24%20Expr.app%20(.app%20(.const%20%60Nat.add%20%5B%5D)%20(toExpr%200))%20(toExpr%201)%7D%0A%0A%2F-%20The%20Puzzle%20--%2F%0A%23eval%20do%20%7B%20--%20should%20print%20out%202%2B3%3D5%0A%20%20let%20two_plus_three_equals_five%20%3A%20Expr%20%E2%86%90%20mkEq%20%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20(Expr.app%20(.app%20(.const%20%60Nat.add%20%5B%5D)%20(toExpr%202))%20(toExpr%203))%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20(toExpr%205)%3B%0A%20%20printPrettyExpression%20%24%20two_plus_three_equals_five%0A%7D) is in the Lean 4 web editor.
