import Verso.Genre.Blog
open Verso Genre Blog

#doc (Post) "Introduction" =>

This is a tutorial on metaprogramming, or equivalently, writing tactics to help prove math theorems, in Lean 4.
That is, instead of focusing on writing a _formalized proof_ (programming), we focus on writing a _program that writes a formalized proof_ (metaprogramming).

# Code
- Here is the [full code](http://google.com) containing everything in the tutorial.
- Here is a [short "cheet sheet"](http://google.com) containing helper functions you might find useful when metaprogramming in the future.

# Looking Ahead

By the end of the tutorial, you will have built an "auto-generalization" Lean tactic that takes an unnecessarily-weak theorem and turns it into a stronger theorem with an analogous proof (using an algorithm from the paper [Generalization in Type Theory Based Proof Assistants](http://cedric.cnam.fr/~pons/PAPERS/types00.pdf) by Oliver Pons).

```leanInit demo
-- This block initializes a Lean context
```

```lean demo
def sqrt : Nat → Nat := sorry
def Irrational : Nat → Prop := sorry
def Nat.Prime : Nat → Prop := sorry
```

For example, given the theorem that √2 is irrational….
```lean demo
theorem sqrt_two_irrational :
    Irrational (sqrt 2) := sorry
```

…this tactic will notice the proof never uses any properties of “2” besides that it is prime, and so it can generalize to the theorem that √p is irrational when p is prime.

```lean demo
theorem sqrt_prime_irrational :
    ∀ (p : Nat), Nat.Prime p → Irrational (sqrt p) := sorry
```
