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

There is no line editing, other than backspace.

Example session:
```
    lambda term? mul four four
    -> ^f x.f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f x)))))))))))))))
    lambda term? exp zero five
    -> one
    lambda term? add (mul two three) one
    -> ^f x.f(f(f(f(f(f(f x))))))
    -> quit
```

