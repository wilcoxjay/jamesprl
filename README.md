# jamesprl: A proof refinement logic in the style of JonPRL for my own edification

## Build instructions 
Ensure that `sml` is in your path. Then build with `./configure` and `make`.

## Test
After building, run the test with `./jamesprl example.jamesprl`. The beginning of 
the output should be something like:
```
Got command:
theorem identity : U{0} -> A -> A {
intro with U{1}; [eq, intro with U{0} as x; [hypeq, hyp x]]
}.
Proved! Extract:
\A. \x. x
```

There is also a (silent and slightly out-dated) [video demo](https://www.youtube.com/watch?v=NSoXNqOeFLA).

## Use in Emacs

Open a `jamesprl` file and evaluate the following elisp in that buffer (e.g. using `M-:`) to get a reasonable interaction mode. You need to replace `<filename>` with the name of your file, and `<path>/<to>/jamesprl` with the absolute path to the `jamesprl` executable in the root of this repository. 

```
(progn
    (local-set-key (kbd "C-c C-l") 'compile)
    (setq compile-command "<path>/<to>/jamesprl <filename>.jamesprl"))
```

Then as you work on your proof, save and hit `C-c C-l` to see the remaining subgoals. 

## Keywords
The following words may not be used as variable names
- `in`
- `as`
- `with`

Otherwise, variables may consist of any sequence of letters and underscores. 

## Expression Syntax
At the time of writing, the `jamesprl` computation system supports the following constructs:
- Functions
    - Pi types: `(x : A) -> B` or `A -> B`
    - Lambdas: `\x. x`
    - Application: `f x`
- Equality: `e1 = e2 in A` or `e in A` as a shorthand for `e = e in A`. Note that unlike JonPRL, this shorthand is really just a notation, and is handled by the parser/pretty printer, so there is no need to unfold it. 
- Universes: `U{0}`, `U{1}`, etc. So for example, the polymorphic identity function would have type `(A : U{0}) -> A -> A`
- (Family) intersection types: `{x : A} B`
- Trivial evidence: `tt` 
  
## Tactics
`jamesprl` supports the following tactics: 
- `id` the identity (no-op) tactic (analogous to `idtac` in Coq)
- `fail` the tactic that always fails
- `tac1; tac2` execute `tac1` and then execute `tac2` on all resulting subgoals
- `tac; [tac1, tac2, ..., tacn]` execute `tac`, which must produce exactly `n` subgoals, and then execute the corresponding `taci` on each
- `hyp x` use assumption `x` (analogous to `exact x` in Coq, except that `exact` accepts an arbitary expression, whereas jamesprl's `hyp` only accepts a hypothesis name)
- `hypeq` solve goals of the form `x = x in A` where `x : A` is in the context
- `intro [with <expr>] [as <name>]` generic introduction tactic. Looks at the goal and applies one step of introduction. At the time of writing, `intro` only works if the goal is a pi or intersection type. 
    - The `with` form is used to pass an arbitary expression to whichever type-specific introduction rule is chosen. `with` is optional in the parser, but required in practice at the moment because both pi and intersection introduction require it in order to specify which universe level the introduced type should live in. 
    - The `as` form is used to pass a variable name to the rule. It is syntactically (and practically) optional. The pi and intersection rules will take advantage of it, if given, to name the introduced variable. 
- `eq [with <expr>]` generic equality tactic. Looks at the goal, which is expected to be an equality, and attempts to make one step of progress on it. At the time of writing, `eq` works in the following cases
    - `U{i} = U{i} in U{i+1}`
    - `(\x. e1) = (\y. e2) in (z : A) -> B` the `with` form is required in this case, in order to give a universe level in which `A` lives
    - `(x : A1) -> B1 = (y : A2) -> B2 in U{i}`
    - `{x : A1} B1 = {y : A2} B2 in U{i}`
    - `e1 = e2 in {x : A} B`
- `elim x [with <expr>]` generic elimination tactic. Looks at the type of `x` and does one step of elimination. At the time of writing, `elim` only supports intersection types.
- `reduce` performs as much computation as possible everywhere (analogous to `compute in *` in Coq, except that it may not terminate (but let's be real, `compute in *` may not *practically* terminate either))
- `ext [as x]` invokes the function extensionality rule.
- `subst with e1 = e2 in A` generates a subgoal to prove the given equality, and then replaces all occurrences of `e1` with `e2` in the main goal.

## Commands
At the time of writing, `jamesprl` supports two commands:
- `definition foo := <expr>.` This command parses successfully but is currently unimplemented and will throw an exception. 
- `theorem bar : <expr> { <tactic> }.` Attempts to prove that the type represented by the given expression is inhabited by applying the given tactic. If the tactic does not finish the proof, the remaining subgoals are printed. If the tactic finishes the proof, then the computational content of the proof is printed. Note that, at the time of writing, there is no way to use previously proved theorems.
