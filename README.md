# lean4-metaprogramming-walkthrough
This is a hands-on, project-based tutorial on metaprogramming (or equivalently, writing tactics to help prove math theorems) in Lean 4.  

## Initial set-up

To set up the repository after cloning, run

```
lake exe cache get
```

to fetch the `Mathlib` cache.

## Building the website

To build the website, run:
```haskell
./run.sh
```

You should then be able to go on a browser to [http://localhost:8800][1] to view the website.

[1]:	http://localhost:8800
