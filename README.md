# lean4-metaprogramming-walkthrough
This is a hands-on, project-based tutorial on metaprogramming (or equivalently, writing tactics to help prove math theorems) in Lean 4.  

To create an executable to build the website, run:
```haskell
lake build
```

To run that executable, run:
```haskell
lake exe walkthrough --output _out/walkthroughsite
```

The correct html feels should be in `_out/examples/demosite` now.  To run the server for the website.
```haskell
python3 -m http.server 8800 --directory _out/walkthroughsite
```
Then go on a browser to [http://localhost:8800][1] to view the website.

To kill  & restart the web server.
```haskell
lsof -i:8800
kill $PID
```

[1]:	http://localhost:8800