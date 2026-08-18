/-
  Little-endian binary naturals, as tree programs.

  Encoding (`Value.ofBin`):

    0      = △
    2k     = △ △ k
    2k + 1 = △ (△ △) k

  Canonical form has no trailing zero-bits. `plus` / `times` / `pow`
  walk the bits rather than a stem-chain, so they scale past toy unaries.
-/

import Cas.Encode

namespace Cas

/-! ### Unfolding lemmas for `ofBin` -/

theorem ofBin_zero : Value.ofBin 0 = .leaf := by
  conv => lhs; rw [Value.ofBin]
  rfl

theorem ofBin_even {n : Nat} (h0 : n ≠ 0) (hev : n % 2 = 0) :
    Value.ofBin n = .fork .leaf (Value.ofBin (n / 2)) := by
  conv => lhs; rw [Value.ofBin]
  rw [if_neg h0, if_pos hev]

theorem ofBin_odd {n : Nat} (hod : n % 2 = 1) :
    Value.ofBin n = .fork (.stem .leaf) (Value.ofBin (n / 2)) := by
  have h0 : n ≠ 0 := by omega
  have hne : ¬n % 2 = 0 := by omega
  conv => lhs; rw [Value.ofBin]
  rw [if_neg h0, if_neg hne]

theorem ofBin_one : Value.ofBin 1 = .fork (.stem .leaf) .leaf := by
  rw [ofBin_odd (by decide), ofBin_zero]

/-! ### Denotation -/

/-- `0 :: t`, collapsing `0 :: 0` to `0`. -/
def cons0V : Value → Value
  | .leaf => .leaf
  | t     => .fork .leaf t

def cons1V (t : Value) : Value :=
  .fork (.stem .leaf) t

def succBinV : Value → Value
  | .leaf => cons1V .leaf
  | .fork .leaf rest => cons1V rest
  | .fork (.stem .leaf) rest => cons0V (succBinV rest)
  | v => v

def predBinV : Value → Value
  | .leaf => .leaf
  | .fork .leaf rest => cons1V (predBinV rest)
  | .fork (.stem .leaf) rest => cons0V rest
  | v => v

def plusBinV : Value → Value → Value
  | .leaf, n => n
  | .stem _, n => n
  | .fork b1 m1, n =>
    match n with
    | .leaf => .fork b1 m1
    | .stem _ => .fork b1 m1
    | .fork b2 n1 =>
      match b1, b2 with
      | .leaf, .leaf => cons0V (plusBinV m1 n1)
      | .leaf, .stem .leaf => cons1V (plusBinV m1 n1)
      | .stem .leaf, .leaf => cons1V (plusBinV m1 n1)
      | .stem .leaf, .stem .leaf => cons0V (succBinV (plusBinV m1 n1))
      | _, _ => .fork b1 m1

def mulBinV : Value → Value → Value
  | .leaf, _ => .leaf
  | .stem _, _ => .leaf
  | .fork .leaf n1, m => cons0V (mulBinV n1 m)
  | .fork (.stem .leaf) n1, m => plusBinV m (cons0V (mulBinV n1 m))
  | .fork _ _, _ => .leaf

def powBinV (b : Value) : Value → Value
  | .leaf => Value.ofBin 1
  | .stem _ => Value.ofBin 1
  | .fork .leaf e1 => powBinV (mulBinV b b) e1
  | .fork (.stem .leaf) e1 => mulBinV b (powBinV (mulBinV b b) e1)
  | .fork _ _ => Value.ofBin 1

theorem cons0V_ofBin (n : Nat) : cons0V (Value.ofBin n) = Value.ofBin (2 * n) := by
  cases n with
  | zero =>
      rw [ofBin_zero, cons0V]
  | succ n =>
      have hne : Value.ofBin (n + 1) ≠ .leaf := by
        intro h
        have := congrArg Value.toBin? h
        simp [Value.toBin_ofBin, Value.toBin?] at this
      match hv : Value.ofBin (n + 1) with
      | .leaf => exact (hne hv).elim
      | .stem _ =>
          simp [cons0V]
          have h2 : 2 * (n + 1) ≠ 0 := by omega
          have hev : (2 * (n + 1)) % 2 = 0 := by omega
          rw [ofBin_even h2 hev]
          congr 1
          have : (2 * (n + 1)) / 2 = n + 1 := by omega
          simp [this]
          exact hv.symm
      | .fork _ _ =>
          simp [cons0V]
          have h2 : 2 * (n + 1) ≠ 0 := by omega
          have hev : (2 * (n + 1)) % 2 = 0 := by omega
          rw [ofBin_even h2 hev]
          congr 1
          have : (2 * (n + 1)) / 2 = n + 1 := by omega
          simp [this]
          exact hv.symm

theorem cons1V_ofBin (n : Nat) : cons1V (Value.ofBin n) = Value.ofBin (2 * n + 1) := by
  have hod : (2 * n + 1) % 2 = 1 := by omega
  rw [cons1V, ofBin_odd hod]
  congr 1
  have : (2 * n + 1) / 2 = n := by omega
  simp [this]

theorem succBinV_ofBin (n : Nat) :
    succBinV (Value.ofBin n) = Value.ofBin (n + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases h0 : n = 0
      · subst h0
        rw [ofBin_zero, succBinV, cons1V, ofBin_one]
      · by_cases hev : n % 2 = 0
        · rw [ofBin_even h0 hev, succBinV, cons1V_ofBin]
          congr 1
          have := Nat.div_add_mod n 2
          omega
        · have hod : n % 2 = 1 := by
            have : n % 2 < 2 := Nat.mod_lt n (by decide)
            omega
          have hlt : n / 2 < n :=
            Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)
          rw [ofBin_odd hod, succBinV, ih (n / 2) hlt, cons0V_ofBin]
          congr 1
          have := Nat.div_add_mod n 2
          omega

theorem predBinV_ofBin (n : Nat) :
    predBinV (Value.ofBin n) = Value.ofBin (n - 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases h0 : n = 0
      · subst h0
        rw [ofBin_zero, predBinV]
      · by_cases hev : n % 2 = 0
        · have hlt : n / 2 < n :=
            Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)
          rw [ofBin_even h0 hev, predBinV, ih (n / 2) hlt, cons1V_ofBin]
          have hn : 2 * (n / 2) = n := by
            have := Nat.div_add_mod n 2
            omega
          cases hdiv : n / 2 with
          | zero =>
              simp [hdiv] at hn
              exact absurd hn.symm h0
          | succ k =>
              -- n = 2*(k+1), n-1 = 2k+1
              have : n - 1 = 2 * k + 1 := by
                simp [hdiv] at hn
                omega
              simp [this]
        · have hod : n % 2 = 1 := by
            have : n % 2 < 2 := Nat.mod_lt n (by decide)
            omega
          rw [ofBin_odd hod, predBinV, cons0V_ofBin]
          have hn : 2 * (n / 2) + 1 = n := by
            have := Nat.div_add_mod n 2
            omega
          have : 2 * (n / 2) = n - 1 := by omega
          rw [this]

theorem plusBinV_zero_left (n : Value) : plusBinV .leaf n = n := rfl

theorem plusBinV_zero_right (m : Nat) :
    plusBinV (Value.ofBin m) .leaf = Value.ofBin m := by
  by_cases h0 : m = 0
  · subst h0
    rw [ofBin_zero, plusBinV]
  · by_cases hev : m % 2 = 0
    · rw [ofBin_even h0 hev, plusBinV]
    · have hod : m % 2 = 1 := by
        have : m % 2 < 2 := Nat.mod_lt m (by decide)
        omega
      rw [ofBin_odd hod, plusBinV]

theorem plusBinV_ofBin (m n : Nat) :
    plusBinV (Value.ofBin m) (Value.ofBin n) = Value.ofBin (m + n) := by
  induction m using Nat.strongRecOn generalizing n with
  | ind m ihm =>
      by_cases hm0 : m = 0
      · subst hm0
        rw [ofBin_zero, plusBinV, Nat.zero_add]
      · by_cases hn0 : n = 0
        · subst hn0
          rw [ofBin_zero, plusBinV_zero_right, Nat.add_zero]
        · have hm2 : m / 2 < m :=
            Nat.div_lt_self (Nat.pos_of_ne_zero hm0) (by decide)
          have hn2 : n / 2 < n :=
            Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by decide)
          by_cases hmev : m % 2 = 0
          · by_cases hnev : n % 2 = 0
            · rw [ofBin_even hm0 hmev, ofBin_even hn0 hnev, plusBinV,
                ihm (m / 2) hm2 (n / 2), cons0V_ofBin]
              congr 1
              have := Nat.div_add_mod m 2
              have := Nat.div_add_mod n 2
              omega
            · have hnod : n % 2 = 1 := by
                have : n % 2 < 2 := Nat.mod_lt n (by decide)
                omega
              rw [ofBin_even hm0 hmev, ofBin_odd hnod, plusBinV,
                ihm (m / 2) hm2 (n / 2), cons1V_ofBin]
              congr 1
              have := Nat.div_add_mod m 2
              have := Nat.div_add_mod n 2
              omega
          · have hmod : m % 2 = 1 := by
              have : m % 2 < 2 := Nat.mod_lt m (by decide)
              omega
            by_cases hnev : n % 2 = 0
            · rw [ofBin_odd hmod, ofBin_even hn0 hnev, plusBinV,
                ihm (m / 2) hm2 (n / 2), cons1V_ofBin]
              congr 1
              have := Nat.div_add_mod m 2
              have := Nat.div_add_mod n 2
              omega
            · have hnod : n % 2 = 1 := by
                have : n % 2 < 2 := Nat.mod_lt n (by decide)
                omega
              rw [ofBin_odd hmod, ofBin_odd hnod, plusBinV,
                ihm (m / 2) hm2 (n / 2), succBinV_ofBin, cons0V_ofBin]
              congr 1
              have := Nat.div_add_mod m 2
              have := Nat.div_add_mod n 2
              omega

theorem mulBinV_ofBin (m n : Nat) :
    mulBinV (Value.ofBin m) (Value.ofBin n) = Value.ofBin (m * n) := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
      by_cases h0 : m = 0
      · subst h0
        rw [ofBin_zero, mulBinV, Nat.zero_mul, ofBin_zero]
      · have hlt : m / 2 < m :=
          Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)
        by_cases hev : m % 2 = 0
        · have hm : m = 2 * (m / 2) := by
            have := Nat.div_add_mod m 2
            omega
          rw [ofBin_even h0 hev, mulBinV, ih (m / 2) hlt, cons0V_ofBin]
          congr 1
          have hm : 2 * (m / 2) = m := by
            have := Nat.div_add_mod m 2
            omega
          rw [← Nat.mul_assoc, hm]
        · have hod : m % 2 = 1 := by
            have : m % 2 < 2 := Nat.mod_lt m (by decide)
            omega
          have hm : 2 * (m / 2) + 1 = m := by
            have := Nat.div_add_mod m 2
            omega
          rw [ofBin_odd hod, mulBinV, ih (m / 2) hlt, cons0V_ofBin, plusBinV_ofBin]
          congr 1
          calc
            n + 2 * (m / 2 * n) = 2 * (m / 2) * n + n := by
                rw [Nat.mul_assoc, Nat.add_comm]
            _ = (2 * (m / 2) + 1) * n := by
                rw [Nat.add_mul, Nat.one_mul]
            _ = m * n := by rw [hm]

theorem powBinV_ofBin (b e : Nat) :
    powBinV (Value.ofBin b) (Value.ofBin e) = Value.ofBin (b ^ e) := by
  induction e using Nat.strongRecOn generalizing b with
  | ind e ih =>
      by_cases h0 : e = 0
      · subst h0
        rw [ofBin_zero, powBinV, Nat.pow_zero, ofBin_one]
      · have hlt : e / 2 < e :=
          Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)
        by_cases hev : e % 2 = 0
        · have heq : e = 2 * (e / 2) := by
            have := Nat.div_add_mod e 2
            omega
          rw [ofBin_even h0 hev, powBinV, mulBinV_ofBin, ih (e / 2) hlt]
          apply congrArg Value.ofBin
          calc
            (b * b) ^ (e / 2) = (b ^ 2) ^ (e / 2) := by rw [Nat.pow_two]
            _ = b ^ (2 * (e / 2)) := by rw [← Nat.pow_mul]
            _ = b ^ e := by rw [← heq]
        · have hod : e % 2 = 1 := by
            have : e % 2 < 2 := Nat.mod_lt e (by decide)
            omega
          have heq : e = 2 * (e / 2) + 1 := by
            have := Nat.div_add_mod e 2
            omega
          rw [ofBin_odd hod, powBinV, mulBinV_ofBin, ih (e / 2) hlt, mulBinV_ofBin]
          apply congrArg Value.ofBin
          calc
            b * (b * b) ^ (e / 2) = b * (b ^ 2) ^ (e / 2) := by rw [Nat.pow_two]
            _ = b * b ^ (2 * (e / 2)) := by rw [← Nat.pow_mul]
            _ = b ^ (2 * (e / 2)) * b := Nat.mul_comm _ _
            _ = b ^ (2 * (e / 2) + 1) := by rw [← Nat.pow_succ]
            _ = b ^ e := by rw [← heq]

/-! ### Tree programs -/

/-- `cons0 t` is `0 :: t`, or `0` if `t` is `0`. -/
def tbCons0 : Tree :=
  star "t" (
    triage △
      (star "_" (△ ⬝ △ ⬝ .ref "t"))
      (star "_" (star "_" (△ ⬝ △ ⬝ .ref "t")))
      ⬝ .ref "t")

/-- `cons1 t` is `1 :: t`. -/
def tbCons1 : Tree :=
  star "t" (△ ⬝ ttrue ⬝ .ref "t")

/-- Binary successor. -/
def tbSucc : Tree :=
  Y2 (star "n" (
    triage
      (star "s" (△ ⬝ ttrue ⬝ △))
      (star "_" (star "s" (△ ⬝ ttrue ⬝ △)))
      (star "bit" (star "rest" (star "s" (
        triage
          (△ ⬝ ttrue ⬝ .ref "rest")
          (star "_" (tbCons0 ⬝ (.ref "s" ⬝ .ref "rest")))
          (star "_" (star "_" (△ ⬝ ttrue ⬝ .ref "rest")))
          ⬝ .ref "bit"))))
      ⬝ .ref "n"))

/-- Binary predecessor (`pred 0 = 0`). -/
def tbPred : Tree :=
  Y2 (star "n" (
    triage
      (star "p" △)
      (star "_" (star "p" △))
      (star "bit" (star "rest" (star "p" (
        triage
          (tbCons1 ⬝ (.ref "p" ⬝ .ref "rest"))
          (star "_" (tbCons0 ⬝ .ref "rest"))
          (star "_" (star "_" △))
          ⬝ .ref "bit"))))
      ⬝ .ref "n"))

/-- `isZero` on a binary nat is the same leaf test. -/
def tbIsZero : Tree := tisZero

open Tm

private def q (t : Tree) : Tm := .embed t

/-- Bit-wise step: `tbBitAdd plus m1 n1 b1 b2`. -/
private def tbBitAdd : Tree :=
  Tm.compile <|
    lam "plus" <| lam "m1" <| lam "n1" <| lam "b1" <| lam "b2" <|
      let sum : Tm := v "plus" ◃ v "m1" ◃ v "n1"
      let ssum : Tm := q tbSucc ◃ sum
      Tm.triage
        (Tm.triage
          (q tbCons0 ◃ sum)
          (lam "_" (q tbCons1 ◃ sum))
          (lam "_" (lam "_" (q tbCons0 ◃ sum)))
          (v "b2"))
        (lam "_"
          (Tm.triage
            (q tbCons1 ◃ sum)
            (lam "_" (q tbCons0 ◃ ssum))
            (lam "_" (lam "_" (q tbCons1 ◃ sum)))
            (v "b2")))
        (lam "_" (lam "_" (q tbCons0 ◃ sum)))
        (v "b1")

/-- Binary addition. -/
def tbPlus : Tree :=
  Y2 <| Tm.compile <|
    lam "m" <|
      Tm.triage
        (lam "plus" (lam "n" (v "n")))
        (lam "_" (lam "plus" (lam "n" (v "n"))))
        (lam "b1" <| lam "m1" <| lam "plus" <| lam "n" <|
          Tm.triage
            (Tm.node ◃ v "b1" ◃ v "m1")
            (lam "_" (Tm.node ◃ v "b1" ◃ v "m1"))
            (lam "b2" <| lam "n1" <|
              q tbBitAdd ◃ v "plus" ◃ v "m1" ◃ v "n1" ◃ v "b1" ◃ v "b2")
            (v "n"))
        (v "m")

/-- Binary multiplication. -/
def tbTimes : Tree :=
  Y2 <| Tm.compile <|
    lam "n" <|
      Tm.triage
        (lam "times" (lam "m" Tm.node))
        (lam "_" (lam "times" (lam "m" Tm.node)))
        (lam "bit" <| lam "n1" <| lam "times" <| lam "m" <|
          Tm.triage
            (q tbCons0 ◃ (v "times" ◃ v "n1" ◃ v "m"))
            (lam "_"
              (q tbPlus ◃ v "m" ◃ (q tbCons0 ◃ (v "times" ◃ v "n1" ◃ v "m"))))
            (lam "_" (lam "_" Tm.node))
            (v "bit"))
        (v "n")

/-- Binary exponentiation by square-and-multiply. `tbPow ⬝ e ⬝ b = b^e`. -/
def tbPow : Tree :=
  Y2 <| Tm.compile <|
    lam "e" <|
      Tm.triage
        (lam "pow" (lam "b" (q (△ ⬝ ttrue ⬝ △))))
        (lam "_" (lam "pow" (lam "b" (q (△ ⬝ ttrue ⬝ △)))))
        (lam "bit" <| lam "e1" <| lam "pow" <| lam "b" <|
          Tm.triage
            (v "pow" ◃ v "e1" ◃ (q tbTimes ◃ v "b" ◃ v "b"))
            (lam "_"
              (q tbTimes ◃ v "b" ◃
                (v "pow" ◃ v "e1" ◃ (q tbTimes ◃ v "b" ◃ v "b"))))
            (lam "_" (lam "_" (q (△ ⬝ ttrue ⬝ △))))
            (v "bit"))
        (v "e")

/-- Three-way compare on binary nats: `△` = LT, `△ △` = EQ, `△ △ △` = GT. -/
def tbCmp : Tree :=
  Y2 <| Tm.compile <|
    lam "m" <|
      Tm.triage
        (lam "cmp" <| lam "n" <|
          Tm.triage (q ttrue) (lam "_" Tm.node) (lam "_" (lam "_" Tm.node)) (v "n"))
        (lam "_" (lam "cmp" (lam "n" (q ttrue))))
        (lam "b1" <| lam "m1" <| lam "cmp" <| lam "n" <|
          Tm.triage
            (q (△ ⬝ △ ⬝ △))
            (lam "_" (q (△ ⬝ △ ⬝ △)))
            (lam "b2" <| lam "n1" <|
              Tm.triage
                Tm.node
                (lam "_"
                  (Tm.triage
                    (Tm.triage (q ttrue) (lam "_" Tm.node)
                      (lam "_" (lam "_" (q ttrue))) (v "b2"))
                    (lam "_"
                      (Tm.triage (q (△ ⬝ △ ⬝ △)) (lam "_" (q ttrue))
                        (lam "_" (lam "_" (q (△ ⬝ △ ⬝ △)))) (v "b2")))
                    (lam "_" (lam "_" (q ttrue)))
                    (v "b1")))
                (lam "_" (lam "_" (q (△ ⬝ △ ⬝ △))))
                (v "cmp" ◃ v "m1" ◃ v "n1"))
            (v "n"))
        (v "m")

/-- Subtract binary nats, assuming `m ≥ n`. -/
def tbRawSub : Tree :=
  Y2 <| Tm.compile <|
    lam "m" <|
      Tm.triage
        (lam "sub" (lam "n" Tm.node))
        (lam "_" (lam "sub" (lam "n" Tm.node)))
        (lam "b1" <| lam "m1" <| lam "sub" <| lam "n" <|
          Tm.triage
            (Tm.node ◃ v "b1" ◃ v "m1")
            (lam "_" (Tm.node ◃ v "b1" ◃ v "m1"))
            (lam "b2" <| lam "n1" <|
              let d : Tm := v "sub" ◃ v "m1" ◃ v "n1"
              Tm.triage
                (Tm.triage
                  (q tbCons0 ◃ d)
                  (lam "_" (q tbCons1 ◃ (q tbPred ◃ d)))
                  (lam "_" (lam "_" (q tbCons0 ◃ d)))
                  (v "b2"))
                (lam "_"
                  (Tm.triage
                    (q tbCons1 ◃ d)
                    (lam "_" (q tbCons0 ◃ d))
                    (lam "_" (lam "_" (q tbCons1 ◃ d)))
                    (v "b2")))
                (lam "_" (lam "_" (q tbCons0 ◃ d)))
                (v "b1"))
            (v "n"))
        (v "m")

/-- Saturating binary subtraction. -/
def tbMinus : Tree :=
  Tm.compile <|
    lam "m" <| lam "n" <|
      Tm.triage
        Tm.node
        (lam "_" Tm.node)
        (lam "_" (lam "_" (q tbRawSub ◃ v "m" ◃ v "n")))
        (q tbCmp ◃ v "m" ◃ v "n")

def minusBinV (a b : Value) : Value :=
  match a.toBin?, b.toBin? with
  | some m, some n => Value.ofBin (m - n)
  | _, _ => .leaf

theorem minusBinV_ofBin (m n : Nat) :
    minusBinV (Value.ofBin m) (Value.ofBin n) = Value.ofBin (m - n) := by
  simp [minusBinV, Value.toBin_ofBin]

/-- `1` as a binary nat. -/
def tbin1 : Tree := △ ⬝ ttrue ⬝ △

/-- `true` iff the binary nat is even. -/
def tbEven : Tree :=
  triage ttrue (K ⬝ tfalse)
    (star "bit" (star "_" (
      triage ttrue (K ⬝ tfalse) (K ⬝ (K ⬝ tfalse)) ⬝ .ref "bit")))

/-- Saturating `m % n` (`m % 0 = m`). -/
def tbMod (_ : Unit := ()) : Tree :=
  Y2 <| Tm.compile <|
    lam "m" <|
      Tm.triage
        (lam "mod" (lam "n" Tm.node))
        (lam "_" (lam "mod" (lam "n" Tm.node)))
        (lam "b" <| lam "m1" <| lam "mod" <| lam "n" <|
          let mval : Tm := Tm.node ◃ v "b" ◃ v "m1"
          Tm.triage
            mval
            (lam "_" mval)
            (lam "_" (lam "_"
              (Tm.triage
                mval
                (lam "_" Tm.node)
                (lam "_" (lam "_"
                  (v "mod" ◃ (q tbRawSub ◃ mval ◃ v "n") ◃ v "n")))
                (q tbCmp ◃ mval ◃ v "n"))))
            (v "n"))
        (v "m")

/-- Saturating `m / n` (`m / 0 = 0`). -/
def tbDiv (_ : Unit := ()) : Tree :=
  Y2 <| Tm.compile <|
    lam "m" <|
      Tm.triage
        (lam "div" (lam "n" Tm.node))
        (lam "_" (lam "div" (lam "n" Tm.node)))
        (lam "b" <| lam "m1" <| lam "div" <| lam "n" <|
          let mval : Tm := Tm.node ◃ v "b" ◃ v "m1"
          Tm.triage
            Tm.node
            (lam "_" Tm.node)
            (lam "_" (lam "_"
              (Tm.triage
                Tm.node
                (lam "_" (q tbin1))
                (lam "_" (lam "_"
                  (q tbSucc ◃ (v "div" ◃ (q tbRawSub ◃ mval ◃ v "n") ◃ v "n"))))
                (q tbCmp ◃ mval ◃ v "n"))))
            (v "n"))
        (v "m")

/-- Euclidean gcd on binary nats. `gcd 0 n = n`. -/
def tbGcd (_ : Unit := ()) : Tree :=
  Y2 <| Tm.compile <|
    lam "m" <|
      Tm.triage
        (lam "gcd" (lam "n" (v "n")))
        (lam "_" (lam "gcd" (lam "n" (v "n"))))
        (lam "b" <| lam "m1" <| lam "gcd" <| lam "n" <|
          let mval : Tm := Tm.node ◃ v "b" ◃ v "m1"
          Tm.triage
            mval
            (lam "_" mval)
            (lam "_" (lam "_"
              (v "gcd" ◃ v "n" ◃ (q (tbMod ()) ◃ mval ◃ v "n"))))
            (v "n"))
        (v "m")

def divBinV (a b : Value) : Value :=
  match a.toBin?, b.toBin? with
  | some m, some n => Value.ofBin (m / n)
  | _, _ => .leaf

def modBinV (a b : Value) : Value :=
  match a.toBin?, b.toBin? with
  | some m, some 0 => Value.ofBin m
  | some m, some n => Value.ofBin (m % n)
  | _, _ => .leaf

def gcdBinV (a b : Value) : Value :=
  match a.toBin?, b.toBin? with
  | some m, some n => Value.ofBin (Nat.gcd m n)
  | _, _ => .leaf

theorem divBinV_ofBin (m n : Nat) :
    divBinV (Value.ofBin m) (Value.ofBin n) = Value.ofBin (m / n) := by
  simp [divBinV, Value.toBin_ofBin]

theorem modBinV_ofBin (m n : Nat) :
    modBinV (Value.ofBin m) (Value.ofBin n) =
      Value.ofBin (if n = 0 then m else m % n) := by
  cases n with
  | zero => simp [modBinV, Value.toBin_ofBin]
  | succ n => simp [modBinV, Value.toBin_ofBin]

theorem gcdBinV_ofBin (m n : Nat) :
    gcdBinV (Value.ofBin m) (Value.ofBin n) = Value.ofBin (Nat.gcd m n) := by
  simp [gcdBinV, Value.toBin_ofBin]

end Cas
