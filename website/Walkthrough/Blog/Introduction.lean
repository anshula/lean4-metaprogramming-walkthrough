--import Mathlib.Data.Real.Irrational
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
```

```lean demo show:=false
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

# Pre-requisites

Before starting this tutorial, it’s helpful (but not absolutely necessary) to know:
- How to write theorems in a theorem-proving programming language (e.g. Coq, Isabelle, Lean, etc.).  If not, you can play the [Natural Number Game (for Lean 4)](https://adam.math.hhu.de/#/g/hhu-adam/NNG4).
- Basics about formalizing math (e.g. that types are propositions, and their terms are their proofs). If not, you can read some of the [Hitchiker’s Guide to Formal Verification (for Lean 4)](https://github.com/blanchette/logical_verification_2023/blob/main/hitchhikers_guide.pdf).

- How to use monads to sidestep around the fact that functional programs shouldn’t have side effects.  [Metaprogramming Videos (for Lean 3)](https://www.youtube.com/watch?v=o6oUjcE6Nz4&list=PLlF-CfQhukNnq2kDCw2P_vI5AfXN7egP2)

# Setup

Make sure you:
- Download this project
- Download mathlib with `VSCode > Command-Shift-P > Lean 4: Build Project`
- Download the mathlib cache with `VSCode > Command-Shift-P > Lean 4: Fetch Mathlib Build Cache`

- Restart Lean with `VSCode > Command-Shift-P > Lean Restart`

Alternatively, you can use the [Lean web editor](https://live.lean-lang.org/) to work through this tutorial.
