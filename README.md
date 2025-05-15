# lean4-metaprogramming-walkthrough
This is a hands-on, project-based tutorial on metaprogramming (or equivalently, writing tactics to help prove math theorems) in Lean 4.  

# For learners

Switch to the `_out/walkthroughsite` directory with the command

```
cd _out/walkthroughsite
```

and start a Python web server by running

```
python3 -m http.server 8800
```

The tutorial should now be available to view on the URL [http://localhost:8800][1].

# For contributors

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
