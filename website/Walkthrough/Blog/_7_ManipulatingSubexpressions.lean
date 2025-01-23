import VersoBlog
import Mathlib.Tactic
open Verso Genre Blog

#doc (Page) "Manipulating Subexpressions" =>

Now that we have an expression, let’s try to find some of its subexpressions.

In particular, to create an autogeneralization tactic, we need to look thorugh all lemmas used in a proof, and check which ones use the term we want to generalize.  This requires checking whether a subexpression occurs in a larger expression.

# Getting and filtering lists of subexpressions

We can first recursively collect a list of all the subexpressions in an expression `e`:

```leanInit manipSub
```

```lean manipSub
open Lean

def getSubexpressionsIn (e : Expr) : List Expr :=
  let rec getSubexpressionsInRec (e : Expr) (acc : List Expr) : List Expr :=
    match e with
    | Expr.forallE _ d b _   => [e] ++ (getSubexpressionsInRec d acc) ++ (getSubexpressionsInRec b acc)
    | Expr.lam _ d b _       => [e] ++ (getSubexpressionsInRec d acc) ++ (getSubexpressionsInRec b acc)
    | Expr.app f a           => [e] ++ (getSubexpressionsInRec f acc) ++ (getSubexpressionsInRec a acc)
    | Expr.mdata _ b         => [e] ++ (getSubexpressionsInRec b acc)
    | Expr.proj _ _ b        => [e] ++ (getSubexpressionsInRec b acc)
    | e                      => [e] ++ acc
  let subexprs := getSubexpressionsInRec e [];
  let subexprs := subexprs.filter $ fun subexpr => !subexpr.hasLooseBVars -- remove the ones that will cause errors when parsing
  subexprs
```

# Comparing Lists and Arrays

Why have we been using so many arrays with `#[]` instead of lists with `[]`?

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


# Checking if an expression contains a subexpression

In most programming languages, this might be under `contains`.  In lean, it is `occurs`.  As in, `e.occurs f` returns true if the expression `e` occurs in the expression `f`.

So, we update our code accordingly.  Now, we only keep the expressions that contain the generalized term f (which in our case is multiplication) in their type.
```
let freeIdentsContainingF := freeIdentsTypes.filter f.occurs
```

But this doesn't check accounting for definitional equality.  To do that, we need to write our own "occurs"

```
/-- Returns true if "e" contains "subexpr".  Differs from "occurs" because this uses the coarser "isDefEq" rather than "==" -/
def containsExpr(subexpr : Expr)  (e : Expr) : MetaM Bool := do
  let mctx ← getMCtx -- save metavar context before using isDefEq
  let e_subexprs := getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => return ← isDefEq e_subexpr subexpr)
  setMCtx mctx -- revert metavar context after using isDefEq, so this function doesn't have side-effects on the expr e
  return firstExprContainingSubexpr.isSome

/- Replaces all subexpressions where "condition" holds with the "replacement" in the expression e -/
def containsExprWhere (condition : Expr → Bool) (e : Expr)   : MetaM Bool := do
  let e_subexprs := getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => return condition e_subexpr)
  return firstExprContainingSubexpr.isSome

```
