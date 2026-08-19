# cas

A basic computer algebra system whose computational substrate is
[tree calculus](https://treecalcul.us/) (Barry Jay; triage rules of
Johannes Bader), implemented in Lean 4.

Expressions **are** binary trees. Arithmetic **is** reduction. Case
analysis on an expression is the same leaf / stem / fork split that
`triage` performs.

## Tree calculus

One operator `△`. Application is left-associative. The five rules:

```
△ △ y z             →  y
△ (△ x) y z         →  x z (y z)
△ (△ w x) y △       →  w
△ (△ w x) y (△ u)   →  x u
△ (△ w x) y (△ u v) →  y u v
```

Irreducible terms are binary trees: a *leaf* `△`, a *stem* `△ a`, or a
*fork* `△ a b`. Combinators and data are just particular trees:

| thing        | tree                          |
|--------------|-------------------------------|
| `K`          | `△ △`                         |
| `S`          | `△ (△ (K △)) △`               |
| `I = S K K`  | `△ (△ K) K`                   |
| `false`, `0` | `△`                           |
| `true`       | `△ △`                         |
| `n+1`        | `△ n`                         |
| pair / cons  | `△ a b`                       |
| `triage l s f` | `△ (△ l s) f`               |

`triage l s f` applied to a value selects `l` on a leaf, `s u` on a
stem, and `f u v` on a fork. That is the whole of pattern matching.

The original book uses a single fork rule `△ (△ w x) y z → z w x`
instead of (3a–c). This project follows the public
[specification](https://treecalcul.us/specification/).

## The CAS

Two layers share the same encoding.

**Surface language** (`Cas.Expr`) — polynomials and a few
transcendentals, with parse / pretty-print, substitution, constant
folding, expansion, like-term collection, and symbolic differentiation.

**Kernel** (`Cas.Program`, `Cas.Kernel`) — the same expressions as
trees (`△ ⟨ctor⟩ ⟨payload⟩`). `teval`, `tdiff` and `tsimp` are `Y2`
programs: a `triage` dispatch inspects the constructor *before* the
recursor is applied, then `plus` / `times` / `pow` do the arithmetic
and `tsimp` rewrites the encoded tree.

```
teval ⬝ ⌜x^2+1⌝ ⬝ ⌜3⌝  →*  ⌜10⌝
tdiff ⬝ ⌜x^2⌝ ⬝ ⌜x⌝    →*  ⌜2x⌝
```

`tequal` is Jay’s intensional equality as a tree program: a `Y2` of
nested `triage` that compares two programs node by node. In particular
`equal ⬝ equal ⬝ equal` is true — no encoding of programs as syntax.

```
tequal ⬝ K ⬝ K  →*  true
tequal ⬝ K ⬝ I  →*  false
```

`tsize` is the matching generic query for node count:

```
tsize ⬝ △      →*  1
tsize ⬝ tsize  →*  ⌜|tsize|⌝
```

Binary nats (`Value.ofBin`) store bits LSB-first, so plus and times walk
`O(log n)` forks instead of a unary stem-chain:

```
0      = △
2k     = △ △ k
2k + 1 = △ (△ △) k
```

`tbPlus`, `tbTimes`, `tbMinus` and `tbPow` are `Y2` programs on that
encoding. `tbGcd` / `tbDiv` / `tbMod` implement Euclidean division.

Signed integers are sign-magnitude (`+n = △ △ n`, `−n = △ (△ △) n`)
with a **binary** magnitude. Rationals are a reduced pair
`p/q = △ ⌜p⌝ ⌜q⌝₂`. Kernel eval uses that encoding, so `inv` and
division compute:

```
teval ⬝ ⌜x-1⌝ ⬝ ⌜4⌝     →*  ⌜3⌝
teval ⬝ ⌜1-x⌝ ⬝ ⌜4⌝     →*  ⌜-3⌝
teval ⬝ ⌜1/2+1/3⌝       →*  ⌜5/6⌝
teval ⬝ ⌜1/x⌝ ⬝ ⌜4⌝     →*  ⌜1/4⌝
tsimp ⬝ ⌜2 * x^1 * 1⌝    →*  ⌜2x⌝
```

`cas trace` walks the same call-by-value order as `eval`: the redex is
always a program-fork applied to a program. Each line marks that redex
in `[…]`, names the rule (`1` / `2` / `3a` / `3b` / `3c`), and prints
the term size.

```
$ lake exe cas trace "I △"
   [I △]    2    (size 7)
   [K △ (K △)]    1    (size 6)
   △    (size 1)
2 steps, normal form
```

## Build

Lean 4.33 (see `lean-toolchain`).

```
lake build
lake exe cas
lake exe cas eval "2*x+1" x=4
lake exe cas diff "x^2 + sin(x)"
lake exe cas normalize "(x+1)*(x-1)"
lake exe cas arith 2 + 3
lake exe cas reduce "S K K △"
lake exe cas trace "S K K △"
lake exe cas trace "K 3 7"
lake exe cas equal K I
lake exe cas equal "S K K" I
lake exe cas size I
lake exe cas size size
lake exe cas bin + 13 21
lake exe cas bin '*' 6 7
lake exe cas bin '^' 2 5
lake exe cas kernel-eval "x-1" x=4
lake exe cas kernel-eval "1-x" x=4
lake exe cas int + 3 -5
lake exe cas int - 1 4
lake exe cas rat + 1/2 1/3
lake exe cas rat inv 2/3
lake exe cas kernel-eval "x^2+1" x=3
lake exe cas kernel-eval "1/2+1/3" x=0
lake exe cas kernel-eval "1/x" x=4
lake exe cas kernel-diff "x^2 + sin(x)"
lake exe cas kernel-diff "x+y" x
lake exe cas kernel-diff "x+y" y
lake exe cas kernel-simp "2*x^1*1"
lake exe cas test
```

## Proofs

`Cas/Arith.lean` records the denotation of unary-nat arithmetic
(`plusV`, `mulV`, `powV`) and proves it matches `Nat` `+` / `*` / `^`.
Any 2-argument function with the same recurrences is unique on encoded
nats (`plus_rec_unique`, and the same for times and pow). Predecessor
and zero-test reduce by unfolding the small `triage` programs.
`evalPoly` is the denotation of kernel evaluation on nat-polynomials
and agrees with ordinary `Nat` evaluation (`evalPoly_natPoly`).
`toRat_ofRat` says a coprime `p/q` decodes as itself.

## Layout

```
Cas/Tree.lean       terms, K, S, I, triage
Cas/Reduce.lean     the five rules, evaluator
Cas/Bracket.lean    star abstraction, Y2
Cas/Encode.lean     bool / nat / pair / list, plus, times, pow, equal, size
Cas/Bin.lean        little-endian binary nats and their programs
Cas/Int.lean        sign-magnitude integers; plus / minus / times
Cas/Rat.lean        reduced rationals; plus / minus / times / inv
Cas/Expr.lean       surface AST ↔ tree
Cas/Algebra.lean    eval, subst, simplify, expand, collect
Cas/Diff.lean       symbolic differentiation + lemmas
Cas/Parse.lean      expression and tree parsers
Cas/Program.lean    teval / tdiff as Y2 + triage programs
Cas/Simp.lean       tsimp, one bottom-up rewrite pass
Cas/Kernel.lean     run those programs; Lean walkers as spec
Cas/Semantics.lean  fuelled evaluator lemmas (K, I, wait, values)
Cas/Arith.lean      plus/times/pow denotation, uniqueness, pred/isZero
Cas/StarBeta.lean   operational star-β
Cas/Fixpoint.lean   Y2 / Z / swap unfolding
Cas/Trace.lean      CBV tracer for the five rules
Cas/Tests.lean      compile-time #guard checks + runtime self-test
```
