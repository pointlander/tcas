/-
  Call-by-value reduction tracer.

  Values *are* programs (leaf / stem / fork). The only redex is a
  program-fork applied to a program — that is exactly one of the five
  rules. Building a stem or a fork is the grammar, not a step.
-/

import Cas.Tree
import Cas.Reduce

namespace Cas

/-- One of the five specification rules. -/
inductive Rule where
  /-- `△ △ y z → y` -/
  | k
  /-- `△ (△ x) y z → x z (y z)` -/
  | s
  /-- `△ (△ w x) y △ → w` -/
  | triageL
  /-- `△ (△ w x) y (△ u) → x u` -/
  | triageS
  /-- `△ (△ w x) y (△ u v) → y u v` -/
  | triageF
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Rule

def toString : Rule → String
  | k       => "1"
  | s       => "2"
  | triageL => "3a"
  | triageS => "3b"
  | triageF => "3c"

instance : ToString Rule := ⟨toString⟩

def descr : Rule → String
  | k       => "△ △ y z → y"
  | s       => "△ (△ x) y z → x z (y z)"
  | triageL => "△ (△ w x) y △ → w"
  | triageS => "△ (△ w x) y (△ u) → x u"
  | triageF => "△ (△ w x) y (△ u v) → y u v"

end Rule

/-- Location of the contracted redex. -/
inductive Redex where
  | here
  | fn  : Redex → Redex
  | arg : Redex → Redex
  deriving Repr, BEq, Inhabited

/-- Apply a program-fork to a program. -/
def contract : Tree → Tree → Option (Tree × Rule)
  | △ ⬝ a ⬝ b, y =>
      match a with
      | △ => some (b, .k)
      | △ ⬝ x => some (x ⬝ y ⬝ (b ⬝ y), .s)
      | △ ⬝ w ⬝ x =>
          match y with
          | △ => some (w, .triageL)
          | △ ⬝ u ⬝ v => some (b ⬝ u ⬝ v, .triageF)
          | △ ⬝ u => some (x ⬝ u, .triageS)
          | _ => none
      | _ => none
  | _, _ => none

/-- One CBV step: leftmost-innermost program-fork applied to a program. -/
def step : Tree → Option (Tree × Rule × Redex)
  | △ | .ref _ => none
  | f ⬝ a =>
      if (f ⬝ a).isProgram then none
      else if !f.isProgram then
        match step f with
        | some (f', r, p) => some (f' ⬝ a, r, .fn p)
        | none => none
      else if !a.isProgram then
        match step a with
        | some (a', r, p) => some (f ⬝ a', r, .arg p)
        | none => none
      else
        match contract f a with
        | some (t', r) => some (t', r, .here)
        | none => none

structure TraceStep where
  term : Tree
  rule : Rule
  redex : Redex
  deriving Repr

inductive TraceStatus where
  | done
  | stuck
  | budget
  deriving Repr, BEq, DecidableEq, Inhabited

structure TraceResult where
  steps  : List TraceStep
  final  : Tree
  status : TraceStatus
  deriving Repr

def defaultMaxSteps : Nat := 10_000

def runTrace (t : Tree) (maxSteps : Nat := defaultMaxSteps) : TraceResult :=
  let rec go (n : Nat) (t : Tree) (acc : List TraceStep) : TraceResult :=
    match n with
    | 0 => { steps := acc.reverse, final := t, status := .budget }
    | n + 1 =>
        match step t with
        | none =>
            let st := if t.isProgram then TraceStatus.done else .stuck
            { steps := acc.reverse, final := t, status := st }
        | some (t', r, p) =>
            go n t' ({ term := t, rule := r, redex := p } :: acc)
  go maxSteps t []

/-- The normal form, if the trace finished on a program. -/
def TraceResult.nf? (tr : TraceResult) : Option Tree :=
  match tr.status with
  | .done => some tr.final
  | _     => none

/-! ### Pretty-printing -/

/-- Stem-chain length if `t` is a unary nat. -/
def Tree.natVal? : Tree → Option Nat
  | △ => some 0
  | △ ⬝ a => (natVal? a).map (· + 1)
  | _ => none

/-- Combinator name, variable, leaf, or (when `natOk`) a unary nat `≥ 2`. -/
def Tree.atomPrint? (t : Tree) (natOk : Bool := true) : Option String :=
  if t == I then some "I"
  else if t == S then some "S"
  else if t == K then some "K"
  else
    match t with
    | △ => some "△"
    | .ref x => some x
    | _ =>
        if natOk then
          match t.natVal? with
          | some n => if n ≥ 2 then some (Nat.repr n) else none
          | none => none
        else none

/-- Combinator-aware printer. Nats print as digits only as arguments (or the whole term),
    never in function position — so a triage spine stays `△ (△ K …)`, not `△ (2 …)`. -/
def Tree.prettyCore (natOk : Bool) : Tree → String
  | △ => "△"
  | .ref x => x
  | f ⬝ a =>
      match (f ⬝ a).atomPrint? natOk with
      | some s => s
      | none =>
          let fs := prettyCore false f
          let as := prettyCore true a
          if (a.atomPrint? true).isSome then s!"{fs} {as}"
          else s!"{fs} ({as})"

def Tree.pretty (t : Tree) : String := t.prettyCore true

/-- `pretty` with the contracted redex wrapped in `[…]`. -/
def Tree.prettyAtCore (natOk : Bool) : Tree → Redex → String
  | t, .here => s!"[{t.prettyCore natOk}]"
  | f ⬝ a, .fn p =>
      let fs := prettyAtCore false f p
      let as := a.prettyCore true
      if (a.atomPrint? true).isSome then s!"{fs} {as}" else s!"{fs} ({as})"
  | f ⬝ a, .arg p =>
      let fs := f.prettyCore false
      let as := prettyAtCore true a p
      if (a.atomPrint? true).isSome then s!"{fs} {as}" else s!"{fs} ({as})"
  | t, _ => t.prettyCore natOk

def Tree.prettyAt (t : Tree) (p : Redex) : String := t.prettyAtCore true p

def TraceStatus.toString : TraceStatus → String
  | .done   => "normal form"
  | .stuck  => "stuck"
  | .budget => "budget exhausted"

instance : ToString TraceStatus := ⟨TraceStatus.toString⟩

def formatTrace (t : Tree) (maxSteps : Nat := defaultMaxSteps) : String :=
  let tr := runTrace t maxSteps
  let rec lines (acc : String) : List TraceStep → String
    | [] => acc
    | s :: rest =>
        let row :=
          s!"   {s.term.prettyAt s.redex}    {s.rule}    (size {s.term.size})"
        let acc := if acc.isEmpty then row else acc ++ "\n" ++ row
        lines acc rest
  let body := lines "" tr.steps
  let last := s!"   {tr.final.pretty}    (size {tr.final.size})"
  let body := if body.isEmpty then last else body ++ "\n" ++ last
  let n := tr.steps.length
  let noun := if n == 1 then "step" else "steps"
  body ++ s!"\n{n} {noun}, {tr.status}"

end Cas
