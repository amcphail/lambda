# lambda
An untyped lambda calculus interpreter

To run in ghci
```
    $ ghci
    > :l Lambda
    Lambda> main
```

To compile with ghcjs and run with Node.js:
```
    $ ghcjs -o lambda Lambda
    $ node lambda.jsexe/all.js
```

The abstractor is the carat symbol `^` so the identity function is `(^x.x)` optionally without brackets.

There is no line editing.
