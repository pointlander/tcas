/-
  Surface language of the CAS. Expressions are themselves trees; this
  inductive type is the typed view of that encoding.
-/

import Cas.Tree
import Cas.Reduce
import Cas.Encode

namespace Cas

inductive Expr where
  | const : Int → Expr
  | var   : String → Expr
  | add   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
  | pow   : Expr → Expr → Expr
  | neg   : Expr → Expr
  | inv   : Expr → Expr
  | sin   : Expr → Expr
  | cos   : Expr → Expr
  | exp   : Expr → Expr
  | ln    : Expr → Expr
  deriving BEq, Repr, Inhabited

namespace Expr

/-- Integer environment. First binding of each name wins. -/
abbrev Env := List (String × Int)
abbrev FEnv := List (String × Float)

/-! ### Constructors and notation -/

instance : OfNat Expr n where
  ofNat := const (Int.ofNat n)

instance : Neg Expr := ⟨neg⟩
instance : Add Expr := ⟨add⟩
instance : Mul Expr := ⟨mul⟩

def sub (a b : Expr) : Expr := add a (neg b)
def div (a b : Expr) : Expr := mul a (inv b)

instance : Sub Expr := ⟨sub⟩
instance : Div Expr := ⟨div⟩

def x : Expr := var "x"
def y : Expr := var "y"
def z : Expr := var "z"

def isConst : Expr → Bool
  | const _ => true
  | _       => false

def asConst? : Expr → Option Int
  | const n => some n
  | _       => none

def size : Expr → Nat
  | const _ | var _ => 1
  | neg a | inv a | sin a | cos a | exp a | ln a => 1 + size a
  | add a b | mul a b | pow a b => 1 + size a + size b

/-- Free variables, in first-seen order. -/
def vars : Expr → List String
  | const _ => []
  | var v   => [v]
  | neg a | inv a | sin a | cos a | exp a | ln a => vars a
  | add a b | mul a b | pow a b =>
      let va := vars a
      (va ++ (vars b).filter (fun x => !va.contains x))

/-! ### Pretty printer -/

/-- Binding strength; higher binds tighter. -/
def prec : Expr → Nat
  | const n => if n ≥ 0 then 10 else 3
  | var _   => 10
  | neg _   => 3
  | add _ _ => 1
  | mul _ _ => 2
  | pow _ _ => 4
  | inv _   => 2
  | sin _ | cos _ | exp _ | ln _ => 10

private def paren (need : Bool) (s : String) : String :=
  if need then s!"({s})" else s

partial def toString : Expr → String
  | const n => ToString.toString n
  | var v   => v
  | neg a   =>
      let body := paren (prec a < 3) (toString a)
      s!"-{body}"
  | add a b =>
      match b with
      | neg c =>
          s!"{paren (prec a < 1) (toString a)} - {paren (prec c < 1) (toString c)}"
      | const n =>
          if n < 0 then
            s!"{paren (prec a < 1) (toString a)} - {n.natAbs}"
          else if n == 0 then
            toString a
          else
            s!"{paren (prec a < 1) (toString a)} + {ToString.toString n}"
      | _ =>
          s!"{paren (prec a < 1) (toString a)} + {paren (prec b < 1) (toString b)}"
  | mul a (inv b) =>
      s!"{paren (prec a < 2) (toString a)} / {paren (prec b ≤ 2) (toString b)}"
  | mul a b =>
      s!"{paren (prec a < 2) (toString a)} * {paren (prec b < 2) (toString b)}"
  | pow a b =>
      s!"{paren (prec a < 4) (toString a)}^{paren (prec b < 4) (toString b)}"
  | inv a =>
      s!"1 / {paren (prec a ≤ 2) (toString a)}"
  | sin a => s!"sin({toString a})"
  | cos a => s!"cos({toString a})"
  | exp a => s!"exp({toString a})"
  | ln a  => s!"ln({toString a})"

instance : ToString Expr := ⟨toString⟩

/-! ### Tree encoding

  An expression is a fork `△ tag payload`. Tags are stem-chains so a
  tree program can dispatch with nested `triage`:

    0 const | 1 var | 2 add | 3 mul | 4 pow
    5 neg   | 6 inv | 7 sin | 8 cos | 9 exp | 10 ln

  Binary operators store `△ left right` as the payload. Variables are
  encoded as lists of character codes (nats).
-/

def tag : Nat → Value
  | 0     => .leaf
  | n + 1 => .stem (tag n)

def tagged (n : Nat) (payload : Value) : Value :=
  .fork (tag n) payload

/-- Binary natural (LSB first). Used for character codes and for
    the magnitude of kernel integers. -/
def ofNatBin (n : Nat) : Value := Value.ofBin n

def toNatBin? (v : Value) : Option Nat := Value.toBin? v

def encodeString (s : String) : Value :=
  Value.ofList (s.toList.map (fun c => ofNatBin c.toNat))

/-- Association list `△ ⟨⌜name⌝, ⌜n⌝⟩ rest` for `teval`. -/
def encodeEnv : Env → Value
  | [] => .leaf
  | (k, n) :: rest =>
      .fork (.fork (encodeString k) (Value.ofRat n 1)) (encodeEnv rest)

partial def decodeString? : Value → Option String
  | v =>
    match v.toList? with
    | none => none
    | some vs =>
        let rec go : List Value → Option (List Char)
          | [] => some []
          | h :: t =>
              match toNatBin? h, go t with
              | some n, some cs => some (Char.ofNat n :: cs)
              | _, _ => none
        match go vs with
        | some cs => some (String.ofList cs)
        | none    => none

def encode : Expr → Value
  | const n => tagged 0 (Value.ofInt n)
  | var v   => tagged 1 (encodeString v)
  | add a b => tagged 2 (.fork (encode a) (encode b))
  | mul a b => tagged 3 (.fork (encode a) (encode b))
  | pow a b => tagged 4 (.fork (encode a) (encode b))
  | neg a   => tagged 5 (encode a)
  | inv a   => tagged 6 (encode a)
  | sin a   => tagged 7 (encode a)
  | cos a   => tagged 8 (encode a)
  | exp a   => tagged 9 (encode a)
  | ln a    => tagged 10 (encode a)

def encodeTree (e : Expr) : Tree := (encode e).toTree

def decode : Value → Option Expr
  | .fork t p =>
      match t.toNat? with
      | some 0 => p.toInt?.map const
      | some 1 => decodeString? p |>.map var
      | some 2 =>
          match p with
          | .fork a b =>
              match decode a, decode b with
              | some a', some b' => some (add a' b')
              | _, _ => none
          | _ => none
      | some 3 =>
          match p with
          | .fork a b =>
              match decode a, decode b with
              | some a', some b' => some (mul a' b')
              | _, _ => none
          | _ => none
      | some 4 =>
          match p with
          | .fork a b =>
              match decode a, decode b with
              | some a', some b' => some (pow a' b')
              | _, _ => none
          | _ => none
      | some 5 => decode p |>.map neg
      | some 6 => decode p |>.map inv
      | some 7 => decode p |>.map sin
      | some 8 => decode p |>.map cos
      | some 9 => decode p |>.map exp
      | some 10 => decode p |>.map ln
      | _ => none
  | _ => none

def decodeTree (t : Tree) (fuel : Nat := Value.defaultFuel) : Option Expr :=
  match eval fuel t with
  | some v => decode v
  | none   => none

end Expr

/-! ### Encoding correctness -/

theorem tag_toNat (n : Nat) : (Expr.tag n).toNat? = some n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [Expr.tag, Value.toNat?, ih]

theorem encode_const (n : Int) :
    Expr.encode (.const n) = .fork (Expr.tag 0) (Value.ofInt n) := rfl

theorem encode_var (x : String) :
    Expr.encode (.var x) = .fork (Expr.tag 1) (Expr.encodeString x) := rfl

theorem encode_add (a b : Expr) :
    Expr.encode (.add a b) =
      .fork (Expr.tag 2) (.fork (Expr.encode a) (Expr.encode b)) := rfl

theorem encode_mul (a b : Expr) :
    Expr.encode (.mul a b) =
      .fork (Expr.tag 3) (.fork (Expr.encode a) (Expr.encode b)) := rfl

theorem encode_pow (a b : Expr) :
    Expr.encode (.pow a b) =
      .fork (Expr.tag 4) (.fork (Expr.encode a) (Expr.encode b)) := rfl

theorem encode_neg (a : Expr) :
    Expr.encode (.neg a) = .fork (Expr.tag 5) (Expr.encode a) := rfl

theorem encode_inv (a : Expr) :
    Expr.encode (.inv a) = .fork (Expr.tag 6) (Expr.encode a) := rfl

theorem encode_sin (a : Expr) :
    Expr.encode (.sin a) = .fork (Expr.tag 7) (Expr.encode a) := rfl

theorem encode_cos (a : Expr) :
    Expr.encode (.cos a) = .fork (Expr.tag 8) (Expr.encode a) := rfl

theorem encode_exp (a : Expr) :
    Expr.encode (.exp a) = .fork (Expr.tag 9) (Expr.encode a) := rfl

theorem encode_ln (a : Expr) :
    Expr.encode (.ln a) = .fork (Expr.tag 10) (Expr.encode a) := rfl

private theorem map_ofBin_char_inj {cs ds : List Char}
    (h : cs.map (fun c => Value.ofBin c.toNat) =
      ds.map (fun c => Value.ofBin c.toNat)) : cs = ds := by
  induction cs generalizing ds with
  | nil =>
      cases ds with
      | nil => rfl
      | cons _ _ => simp at h
  | cons c cs ih =>
      cases ds with
      | nil => simp at h
      | cons d ds =>
          simp at h
          obtain ⟨hcd, hrest⟩ := h
          have hnat : c.toNat = d.toNat := Value.ofBin_inj hcd
          have : c = d := by
            cases c; cases d
            apply Char.ext
            simp [Char.toNat] at hnat
            exact UInt32.toNat_inj.mp hnat
          subst this
          rw [ih hrest]

theorem encodeString_inj {s t : String} (h : Expr.encodeString s = Expr.encodeString t) :
    s = t := by
  simp [Expr.encodeString] at h
  have := Value.ofList_inj h
  have := map_ofBin_char_inj this
  exact String.ext this

end Cas
