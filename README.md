# JamesPRL: A proof refinement logic in the style of JonPRL for my own edification

Ensure that `sml` is in your path. Then build with `./configure` and `make`.

Then run the test with `./jamesprl tests/example.jamesprl`. You should see
something like:

```
Got command:
theorem identity : (A@1 : U{0}) -> (_@2 : A@1) -> A@1 {
intro with U{1}; [eq, intro with U{0} as x; [hypeq A, hyp x]]
}.
Proved!
done!
```
