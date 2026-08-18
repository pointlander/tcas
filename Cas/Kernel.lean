/-
  The CAS kernel *in* tree calculus.

  Expressions are binary trees (see `Expr.encode`). Operations analyse
  those trees by the same leaf / stem / fork split that `triage` performs,
  and they do arithmetic by reducing the combinators `tplus`, `ttimes`
  and `tpow`.
-/

import Cas.Encode
import Cas.Expr
import Cas.Algebra
import Cas.Diff
import Cas.Bracket
import Cas.Program

namespace Cas

/-- Apply a compiled 2-argument tree program to two values. -/
def run2 (prog : Tree) (a b : Value) (fuel : Nat := Value.defaultFuel) : Option Value :=
  match eval fuel prog with
  | none => none
  | some f =>
      match Value.apply fuel f a with
      | none => none
      | some fa => Value.apply fuel fa b

def run1 (prog : Tree) (a : Value) (fuel : Nat := Value.defaultFuel) : Option Value :=
  match eval fuel prog with
  | none => none
  | some f => Value.apply fuel f a

/-- Natural addition by reducing `tplus`. -/
def kernelAdd (a b : Value) : Option Value :=
  run2 tplusDirect a b

/-- Natural multiplication by reducing `ttimes`. -/
def kernelMul (a b : Value) : Option Value :=
  run2 ttimes a b

/-- Natural exponentiation by reducing `tpow`. -/
def kernelPow (b e : Value) : Option Value :=
  run2 tpow e b

/-- Predecessor / successor as tree programs. -/
def kernelPred (a : Value) : Option Value :=
  run1 tpred a

def kernelSucc (a : Value) : Value :=
  .stem a

def kernelIsZero (a : Value) : Option Value :=
  run1 tisZero a

/-- Intensional equality of two programs, as a boolean. -/
def kernelEqual (a b : Value) (fuel : Nat := Value.defaultFuel) : Option Bool :=
  match run2 tequal a b fuel with
  | some v => v.toBool?
  | none   => none

/-- Size of a program, as a unary nat. -/
def kernelSize (a : Value) (fuel : Nat := Value.defaultFuel) : Option Nat :=
  match run1 tsize a fuel with
  | some v => v.toNat?
  | none   => none

/-! ### Intensional analysis of encoded expressions

  A fork `△ tag payload` is an expression constructor. Nested stems on
  `tag` are the constructor index — the same information `triage` reads
  one layer at a time.
-/

/-- Constructor index of an encoded expression. -/
def ctor? : Value → Option Nat
  | .fork tag _ => tag.toNat?
  | _           => none

/-- Payload of an encoded expression. -/
def payload? : Value → Option Value
  | .fork _ p => some p
  | _         => none

/-- Binary payload `△ left right`. -/
def pairPayload? : Value → Option (Value × Value)
  | .fork a b => some (a, b)
  | _         => none

/-- Lean-side intensional walker; the specification of `teval`. -/
partial def walkEval (x : Value) (e : Value) : Option Value :=
  match e with
  | .fork tag payload =>
      match tag.toNat? with
      | some 0 =>
          -- const: `ofInt` is `△ sign mag`. Only non-negative constants.
          match payload with
          | .fork .leaf mag => some mag
          | _ => none
      | some 1 => some x
      | some 2 =>
          match payload with
          | .fork a b =>
              match walkEval x a, walkEval x b with
              | some va, some vb => kernelAdd va vb
              | _, _ => none
          | _ => none
      | some 3 =>
          match payload with
          | .fork a b =>
              match walkEval x a, walkEval x b with
              | some va, some vb => kernelMul va vb
              | _, _ => none
          | _ => none
      | some 4 =>
          match payload with
          | .fork a b =>
              match walkEval x a, walkEval x b with
              | some va, some vb => kernelPow va vb
              | _, _ => none
          | _ => none
      | some 5 =>
          -- neg: only `-0`
          match walkEval x payload with
          | some v =>
              match v.toNat? with
              | some 0 => some (.leaf)
              | _ => none
          | none => none
      | _ => none
  | _ => none

/-- Reduce `teval ⬝ e ⬝ x`. -/
def kernelEval (x e : Value) (fuel : Nat := Value.defaultFuel) : Option Value :=
  run2 teval e x fuel

def kernelEvalExpr (x : Nat) (e : Expr) : Option Nat :=
  match kernelEval (Value.ofNat x) (Expr.encode e) with
  | some v => v.toNat?
  | none   => none

/-- Lean-side intensional walker; the specification of `tdiff`. -/
partial def walkDiff : Value → Option Value
  | .fork tag payload =>
      match tag.toNat? with
      | some 0 =>
          -- d/dx const = 0
          some (Expr.encode (.const 0))
      | some 1 =>
          -- d/dx var = 1
          some (Expr.encode (.const 1))
      | some 2 =>
          match payload with
          | .fork a b =>
              match walkDiff a, walkDiff b with
              | some da, some db =>
                  some (Expr.tagged 2 (.fork da db))
              | _, _ => none
          | _ => none
      | some 3 =>
          -- (uv)' = u'v + uv'
          match payload with
          | .fork a b =>
              match walkDiff a, walkDiff b with
              | some da, some db =>
                  let left  := Expr.tagged 3 (.fork da b)
                  let right := Expr.tagged 3 (.fork a db)
                  some (Expr.tagged 2 (.fork left right))
              | _, _ => none
          | _ => none
      | some 4 =>
          -- (u^n)' = n * u^(n-1) * u'   when n is a constant nat
          match payload with
          | .fork a b =>
              match b with
              | .fork bt bp =>
                  match bt.toNat? with
                  | some 0 =>
                      match bp with
                      | .fork .leaf mag =>
                          match mag.toNat?, walkDiff a with
                          | some n, some da =>
                              let nE   := Expr.encode (.const (Int.ofNat n))
                              let nm1  := Expr.encode (.const (Int.ofNat (n - 1)))
                              let pow' := Expr.tagged 4 (.fork a nm1)
                              let mid  := Expr.tagged 3 (.fork nE pow')
                              some (Expr.tagged 3 (.fork mid da))
                          | _, _ => none
                      | _ => none
                  | _ =>
                      -- non-constant exponent: a^b · (b' ln a + b · a'/a)
                      match walkDiff a, walkDiff b with
                      | some da, some db =>
                          let lnA  := Expr.tagged 10 a
                          let invA := Expr.tagged 6 a
                          let left := Expr.tagged 3 (.fork db lnA)
                          let mid  := Expr.tagged 3 (.fork da invA)
                          let right := Expr.tagged 3 (.fork b mid)
                          let sum  := Expr.tagged 2 (.fork left right)
                          let pow  := Expr.tagged 4 (.fork a b)
                          some (Expr.tagged 3 (.fork pow sum))
                      | _, _ => none
              | _ => none
          | _ => none
      | some 5 =>
          match walkDiff payload with
          | some da => some (Expr.tagged 5 da)
          | none    => none
      | some 6 =>
          -- (1/u)' = -u' / u^2
          match walkDiff payload with
          | some da =>
              let u2   := Expr.tagged 4 (.fork payload (Expr.encode (.const 2)))
              let inv  := Expr.tagged 6 u2
              let prod := Expr.tagged 3 (.fork da inv)
              some (Expr.tagged 5 prod)
          | none => none
      | some 7 =>
          match walkDiff payload with
          | some da =>
              let c := Expr.tagged 8 payload
              some (Expr.tagged 3 (.fork c da))
          | none => none
      | some 8 =>
          match walkDiff payload with
          | some da =>
              let s := Expr.tagged 7 payload
              let p := Expr.tagged 3 (.fork s da)
              some (Expr.tagged 5 p)
          | none => none
      | some 9 =>
          match walkDiff payload with
          | some da =>
              let e := Expr.tagged 9 payload
              some (Expr.tagged 3 (.fork e da))
          | none => none
      | some 10 =>
          match walkDiff payload with
          | some da =>
              let inv := Expr.tagged 6 payload
              some (Expr.tagged 3 (.fork da inv))
          | none => none
      | _ => none
  | _ => none

/-- Reduce `tdiff ⬝ e`. -/
def kernelDiff (e : Value) (fuel : Nat := Value.defaultFuel) : Option Value :=
  run1 tdiff e fuel

def kernelDiffExpr (e : Expr) : Option Expr :=
  match kernelDiff (Expr.encode e) with
  | some v => Expr.decode v
  | none   => none

/-! ### A self-contained tree program for `plus` on encoded nats

  Exposed so the CLI can print the program and reduce it.
-/

def plusProgram : Tree := tplusDirect
def timesProgram : Tree := ttimes
def powProgram : Tree := tpow
def predProgram : Tree := tpred
def isZeroProgram : Tree := tisZero
def notProgram : Tree := tnot
def equalProgram : Tree := tequal
def sizeProgram : Tree := tsize
def evalProgram : Tree := teval
def diffProgram : Tree := tdiff

def describeKernel : String :=
  "tree-calculus kernel\n\
   nats     0 = △, n+1 = △ n\n\
   bools    false = △, true = △ △\n\
   plus     Y2 (λm p n. triage {n, λm₁. △ (p m₁ n), λ_ _. n} m)\n\
   times    Y2 (λn t m. triage {0, λn₁. plus m (t n₁ m), λ_ _. 0} n)\n\
   pow      Y2 (λe p b. triage {1, λe₁. times b (p e₁ b), λ_ _. 1} e)\n\
   expr     △ ⟨ctor⟩ ⟨payload⟩   ctor = stem-chain index\n\
   eval     Y2 + nested triage; plus/times/pow for arithmetic\n\
   diff     Y2 + nested triage; result is an encoded expression\n\
   equal    Y2 + nested triage on both arguments (intensional)\n\
   size     Y2 + triage {1, λx. succ (size x), λx y. succ (size x + size y)}"

end Cas
