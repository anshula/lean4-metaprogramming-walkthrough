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

The [exercise is here](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAGQKYEMB2AoCYlsavAUQBsUAjOAFRQGMZga4BZJGFKpKEDDAegFo4ABSjA08CAFd4MABZI4SAB5goSAM7rgEPGLjtZkkOn5qUAE3LEFAdxQBPOHH68M5pADM4qsTBGsYe0IVNU1tPAAKBQAuOGDVAEo4WJY2JjgAVTRgeGiAXjhzCAwnczIAcwB9GChaBQAiAG9ABMIwMHioRQBfep4BOABlCBAFeWIwD0liRSUUcGt1OBgIODUPTlwaBRcMAGIkADcUaaK4Rp9xfxhAjo0tHTgAEjhmuBAAa0IARzgI5Y64AAGJJ/CAA4FdPaHY6FFbnUSXNTXIIhO7hJ5xEIAOhQbV+OLxESxNB06ngAAMAHIoGA48zmOAAbQAuiD/iEgQk2WCOQBGBKQviCSjybySABe4uszlc+yOJzhzkE6lkUmIDIuEmkcAATABqADMeQArCU4NYZDYIJUwMRJOpqrI1EhKkgvpJjg6PMADjFMaoXnBKkq4AAxACSCAQVAAEuGBnAAPIZShmzVXG6osIPZ4wK02u0OuTO13uz2Vb2+jBdIA) in the Lean 4 web editor.
The [answer is here](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAGQKYEMB2AoCYlsavAUQBsUAjOAFRQGMZga4BZJGFKpKEDDAegFo4ABSjA08CAFd4MABZI4SAB5goSAM7rgEPGLjtZkkOn5qUAE3LEFAdxQBPOHH68M5pADM4qsTBGsYe0IVNU1tPAAKBQAuOGDVAEo4WJY2JjgAVTRgeGiAXjhzCAwnczIAcwB9GChaBQAiAG9ABMIwMHioRQBfep4BOABlCBAFeWIwD0liRSUUcGt1OBgIODUPTlwaBRcMAGIkADcUaaK4Rp9xfxhAjo0tHTgAEjhmuBAAa0IARzgI5Y64AAGJJ/CAA4FdPaHY6FFbnUSXNTXIIhO7hJ5xEIAOhQbV+OLxESxNB06ngAAMAHIoGA48zmOAAbQAuiD/iEgQk2WCOQBGBKQviCSjybySABe4uszlc+yOJzhzkE6lkUmIDIuEmkcAATABqADMeQArCU4NYZDYIJUwMRJOpqrI1EhKkgvpJjg6PMADjFMaoXnAzU4Pt9fh0CWB8bio0SSWgyXByVSaXSGSzuQCdVzfuyAwac6CAcaEmbNVcbqiwg9njArTa7Q65M7Xe7PZVvb6MF0gA) is in the Lean 4 web editor.
