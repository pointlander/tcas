/-
  The CAS kernel *in* tree calculus.

  Expressions are binary trees (see `Expr.encode`). Operations analyse
  those trees by the same leaf / stem / fork split that `triage` performs,
  and they do arithmetic by reducing the combinators `tplus`, `ttimes`
  and `tpow`.
-/

import Cas.Encode
import Cas.Bin
import Cas.Int
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

/-- Binary-nat operations. -/
def kernelBinSucc (a : Value) (fuel : Nat := Value.defaultFuel) : Option Nat :=
  match run1 tbSucc a fuel with
  | some v => v.toBin?
  | none   => none

def kernelBinPred (a : Value) (fuel : Nat := Value.defaultFuel) : Option Nat :=
  match run1 tbPred a fuel with
  | some v => v.toBin?
  | none   => none

def kernelBinAdd (a b : Value) (fuel : Nat := Value.defaultFuel) : Option Nat :=
  match run2 tbPlus a b fuel with
  | some v => v.toBin?
  | none   => none

def kernelBinMul (a b : Value) (fuel : Nat := Value.defaultFuel) : Option Nat :=
  match run2 tbTimes a b fuel with
  | some v => v.toBin?
  | none   => none

/-- `kernelBinPow b e` is `b^e`. -/
def kernelBinPow (b e : Value) (fuel : Nat := Value.defaultFuel) : Option Nat :=
  match run2 tbPow e b fuel with
  | some v => v.toBin?
  | none   => none

def kernelBinSub (a b : Value) (fuel : Nat := Value.defaultFuel) : Option Nat :=
  match run2 tbMinus a b fuel with
  | some v => v.toBin?
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

/-- Lean-side intensional walker; the specification of `teval`.
    Results are sign-magnitude integers (`Value.ofInt`). -/
partial def walkEval (x : Value) (e : Value) : Option Value :=
  match e with
  | .fork tag payload =>
      match tag.toNat? with
      | some 0 =>
          -- const: payload is already an `ofInt`
          some payload
      | some 1 =>
          -- var: pack the binary input as `+x`
          some (.fork .leaf x)
      | some 2 =>
          match payload with
          | .fork a b =>
              match walkEval x a, walkEval x b with
              | some va, some vb =>
                  match va.toInt?, vb.toInt? with
                  | some i, some j => some (Value.ofInt (i + j))
                  | _, _ => none
              | _, _ => none
          | _ => none
      | some 3 =>
          match payload with
          | .fork a b =>
              match walkEval x a, walkEval x b with
              | some va, some vb =>
                  match va.toInt?, vb.toInt? with
                  | some i, some j => some (Value.ofInt (i * j))
                  | _, _ => none
              | _, _ => none
          | _ => none
      | some 4 =>
          match payload with
          | .fork a b =>
              match walkEval x a, walkEval x b with
              | some va, some vb =>
                  match va.toInt?, vb.toInt? with
                  | some i, some j =>
                      if 0 ≤ j then
                        some (Value.ofInt (i ^ j.toNat))
                      else none
                  | _, _ => none
              | _, _ => none
          | _ => none
      | some 5 =>
          match walkEval x payload with
          | some v =>
              match v.toInt? with
              | some i => some (Value.ofInt (-i))
              | none => none
          | none => none
      | _ => none
  | _ => none

/-- Reduce `teval ⬝ e ⬝ x`. -/
def kernelEval (x e : Value) (fuel : Nat := Value.defaultFuel) : Option Value :=
  run2 teval e x fuel

def kernelEvalInt (x : Nat) (e : Expr) : Option Int :=
  match kernelEval (Value.ofBin x) (Expr.encode e) with
  | some v => v.toInt?
  | none   => none

def kernelEvalExpr (x : Nat) (e : Expr) : Option Nat :=
  match kernelEvalInt x e with
  | some i => if 0 ≤ i then some i.toNat else none
  | none => none

def kernelMinus (a b : Value) : Option Value :=
  run2 tminus a b

def kernelIAdd (a b : Value) : Option Value :=
  run2 tiPlus a b

def kernelISub (a b : Value) : Option Value :=
  run2 tiMinus a b

def kernelIMul (a b : Value) : Option Value :=
  run2 tiTimes a b

def kernelINeg (a : Value) : Option Value :=
  run1 tiNeg a

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
                          match mag.toBin?, walkDiff a with
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
def bsuccProgram : Tree := tbSucc
def bpredProgram : Tree := tbPred
def bplusProgram : Tree := tbPlus
def btimesProgram : Tree := tbTimes
def bpowProgram : Tree := tbPow
def bminusProgram : Tree := tbMinus
def minusProgram : Tree := tminus
def inegProgram : Tree := tiNeg
def iplusProgram : Tree := tiPlus
def iminusProgram : Tree := tiMinus
def itimesProgram : Tree := tiTimes
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
   size     Y2 + triage {1, λx. succ (size x), λx y. succ (size x + size y)}\n\
   binary   0 = △, 2k = △ △ k, 2k+1 = △ (△ △) k  (LSB first)\n\
   int      +n = △ △ ⌜n⌝₂, −n = △ (△ △) ⌜n⌝₂   (binary magnitude)"

end Cas
