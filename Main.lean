import Cas
import Cas.Tests

open Cas

def usage : String :=
  "cas — a computer algebra system in tree calculus\n\
   \n\
   Usage:\n\
     cas                     run the built-in demo\n\
     cas test                reduce teval / tdiff on a small suite\n\
     cas help                this message\n\
     cas eval <expr> [x=n …] evaluate (ℤ if possible, else Float)\n\
     cas simplify <expr>     rewrite + constant fold\n\
     cas expand <expr>       distribute and collect\n\
     cas normalize <expr>    expand, collect like terms, simplify\n\
     cas diff <expr> [var]   differentiate (default var: x)\n\
     cas subst <expr> x=rhs  substitute a sub-expression\n\
     cas encode <expr>       print the expression as a tree\n\
     cas reduce <tree>       reduce a tree-calculus term\n\
     cas trace <tree> [n]    show each of the five rules (at most n steps)\n\
     cas arith <n> +|*|^ <m> natural arithmetic via tree reduction\n\
     cas kernel-eval <expr> x=<n>\n\
                             evaluate a polynomial by tree reduction (ℤ)\n\
     cas kernel-diff <expr>  differentiate the encoded tree\n\
     cas equal <t1> <t2>     intensional equality of two tree programs\n\
     cas size <tree>         count nodes of a tree program\n\
     cas bin + <n> <m>       binary-nat addition\n\
     cas bin '*' <n> <m>     binary-nat multiplication\n\
     cas bin '^' <n> <m>     binary-nat exponent (quote * and ^)\n\
     cas bin succ|pred <n>   binary successor / predecessor\n\
     cas int +|-|* <i> <j>   signed-int arithmetic\n\
     cas int neg <i>         signed-int negation\n\
     cas show plus|times|pow|pred|minus|iplus|eval|diff\n\
                             print a kernel combinator\n\
   \n\
     expressions:  2*x^3 + sin(x) - 1/x\n\
     trees:        △, K, S, I, nats, juxtaposition, parentheses\n"

def runProgramSelfTest : IO Bool := do
  IO.println s!"   teval {teval.size} nodes (program {teval.isProgram})"
  IO.println s!"   tdiff {tdiff.size} nodes (program {tdiff.isProgram})"
  IO.println s!"   tequal {tequal.size} nodes (program {tequal.isProgram})"
  IO.println s!"   tsize {tsize.size} nodes (program {tsize.isProgram})"
  match Cas.Tests.programSelfTest with
  | none =>
      IO.println "   program self-test: ok"
      return true
  | some name =>
      IO.eprintln s!"   program self-test failed: {name}"
      return false

def demo : IO Unit := do
  IO.println "CAS in tree calculus"
  IO.println "===================="
  IO.println ""
  IO.println "1. Kernel reductions"
  let showNat (label : String) (t : Tree) : IO Unit := do
    match evalNat t with
    | some n => IO.println s!"   {label}  ⇒  {n}"
    | none   => IO.println s!"   {label}  ⇒  {eval! t}"
  showNat "I △"           (I ⬝ △)
  showNat "K 3 7"         (K ⬝ ofNat 3 ⬝ ofNat 7)
  showNat "S K K 5"       (S ⬝ K ⬝ K ⬝ ofNat 5)
  showNat "pred 4"        (tpred ⬝ ofNat 4)
  match eval! (tnot ⬝ tfalse) |>.toBool? with
  | some b => IO.println s!"   not false  ⇒  {b}"
  | none   => IO.println "   not false  ⇒  ?"
  IO.println ""
  IO.println "2. Tree-calculus arithmetic"
  let runOp (name : String) (op : Value → Value → Option Value) (a b : Nat) : IO Unit := do
    match op (Value.ofNat a) (Value.ofNat b) with
    | some v =>
        match v.toNat? with
        | some n => IO.println s!"   {a} {name} {b}  ⇒  {n}"
        | none   => IO.println s!"   {a} {name} {b}  ⇒  {v}"
    | none => IO.println s!"   {a} {name} {b}  ⇒  (diverged)"
  runOp "+" kernelAdd 2 3
  runOp "*" kernelMul 3 4
  runOp "^" kernelPow 2 5
  IO.println ""
  IO.println "3. Surface algebra"
  let showE (label : String) (s : String) (f : Expr → String) : IO Unit := do
    match parseExpr? s with
    | none => IO.println s!"   (parse error) {s}"
    | some e => IO.println s!"   {label}{f e}"
  showE "eval  2*x+1 | x=4   =  " "2*x+1" (fun e =>
    match Expr.evalInt [("x", 4)] e with
    | some n => toString n
    | none   => "?")
  showE "norm   (x+1)^3      =  " "(x+1)^3" (fun e => toString (Expr.normalize e))
  showE "norm   (x+1)*(x-1)  =  " "(x+1)*(x-1)" (fun e => toString (Expr.normalize e))
  showE "d/dx   x^2 + sin(x) =  " "x^2 + sin(x)" (fun e => toString (Expr.dsimp "x" e))
  IO.println ""
  IO.println "4. eval / diff as tree programs"
  IO.println s!"   teval  ({teval.size} nodes)"
  IO.println s!"   tdiff  ({tdiff.size} nodes)"
  match parseExpr? "x+1" with
  | none => pure ()
  | some e =>
      IO.println s!"   encode(x+1)  =  {Expr.encode e}"
      match kernelEvalExpr 4 e with
      | some n => IO.println s!"   teval ⬝ ⌜x+1⌝ ⬝ ⌜4⌝  ⇒  {n}"
      | none   => IO.println "   teval ⬝ ⌜x+1⌝ ⬝ ⌜4⌝  ⇒  (diverged)"
      match kernelDiffExpr e with
      | some d => IO.println s!"   tdiff ⬝ ⌜x+1⌝        ⇒  {Expr.simplify d}"
      | none   => IO.println "   tdiff ⬝ ⌜x+1⌝        ⇒  (diverged)"
  match parseExpr? "x^2+1" with
  | none => pure ()
  | some e =>
      match kernelEvalExpr 3 e with
      | some n => IO.println s!"   teval ⬝ ⌜x^2+1⌝ ⬝ ⌜3⌝ ⇒  {n}"
      | none   => IO.println "   teval ⬝ ⌜x^2+1⌝ ⬝ ⌜3⌝ ⇒  (diverged)"
      match kernelDiffExpr e with
      | some d => IO.println s!"   tdiff ⬝ ⌜x^2+1⌝       ⇒  {Expr.simplify d}"
      | none   => IO.println "   tdiff ⬝ ⌜x^2+1⌝       ⇒  (diverged)"
  match parseExpr? "sin(x)" with
  | none => pure ()
  | some e =>
      match kernelDiffExpr e with
      | some d => IO.println s!"   tdiff ⬝ ⌜sin(x)⌝      ⇒  {Expr.simplify d}"
      | none   => IO.println "   tdiff ⬝ ⌜sin(x)⌝      ⇒  (diverged)"
  match parseExpr? "x-1" with
  | none => pure ()
  | some e =>
      match kernelEvalInt 4 e with
      | some n => IO.println s!"   teval ⬝ ⌜x-1⌝ ⬝ ⌜4⌝   ⇒  {n}"
      | none   => IO.println "   teval ⬝ ⌜x-1⌝ ⬝ ⌜4⌝   ⇒  (diverged)"
  match parseExpr? "1-x" with
  | none => pure ()
  | some e =>
      match kernelEvalInt 4 e with
      | some n => IO.println s!"   teval ⬝ ⌜1-x⌝ ⬝ ⌜4⌝   ⇒  {n}"
      | none   => IO.println "   teval ⬝ ⌜1-x⌝ ⬝ ⌜4⌝   ⇒  (diverged)"
  IO.println ""
  IO.println "5. Reduction trace (cas trace \"K 3 7\")"
  IO.println (formatTrace (K ⬝ ofNat 3 ⬝ ofNat 7))
  IO.println ""
  IO.println "6. Intensional equality"
  IO.println s!"   tequal  ({tequal.size} nodes, program {tequal.isProgram})"
  let showEq (label : String) (a b : Tree) : IO Unit := do
    match kernelEqual (eval! a) (eval! b) with
    | some v => IO.println s!"   equal {label}  ⇒  {v}"
    | none   => IO.println s!"   equal {label}  ⇒  (diverged)"
  showEq "K K" K K
  showEq "K I" K I
  showEq "3 3" (ofNat 3) (ofNat 3)
  showEq "3 4" (ofNat 3) (ofNat 4)
  IO.println ""
  IO.println "7. Program size"
  IO.println s!"   tsize  ({tsize.size} nodes, program {tsize.isProgram})"
  let showSz (label : String) (t : Tree) : IO Unit := do
    match kernelSize (eval! t) with
    | some n => IO.println s!"   size {label}  ⇒  {n}"
    | none   => IO.println s!"   size {label}  ⇒  (diverged)"
  showSz "△" △
  showSz "K" K
  showSz "I" I
  showSz "3" (ofNat 3)
  IO.println ""
  IO.println "8. Binary nats"
  IO.println s!"   tbPlus   ({tbPlus.size} nodes, program {tbPlus.isProgram})"
  IO.println s!"   tbTimes  ({tbTimes.size} nodes, program {tbTimes.isProgram})"
  let showBin (label : String) (r : Option Nat) : IO Unit :=
    match r with
    | some n => IO.println s!"   {label}  ⇒  {n}"
    | none   => IO.println s!"   {label}  ⇒  (diverged)"
  showBin "13 + 21" (kernelBinAdd (Value.ofBin 13) (Value.ofBin 21))
  showBin "6 * 7" (kernelBinMul (Value.ofBin 6) (Value.ofBin 7))
  showBin "2 ^ 5" (kernelBinPow (Value.ofBin 2) (Value.ofBin 5))
  IO.println ""
  let _ ← runProgramSelfTest
  IO.println ""
  IO.println describeKernel

def kernelNamed : String → Option Tree
  | "plus"  => some plusProgram
  | "times" => some timesProgram
  | "pow"   => some powProgram
  | "pred"  => some predProgram
  | "not"   => some notProgram
  | "equal" => some equalProgram
  | "size"  => some sizeProgram
  | "minus" => some minusProgram
  | "ineg"  => some inegProgram
  | "iplus" => some iplusProgram
  | "iminus" => some iminusProgram
  | "itimes" => some itimesProgram
  | "bsucc" => some bsuccProgram
  | "bpred" => some bpredProgram
  | "bplus" => some bplusProgram
  | "btimes" => some btimesProgram
  | "bpow"  => some bpowProgram
  | "eval"  => some evalProgram
  | "diff"  => some diffProgram
  | "I"     => some I
  | "K"     => some K
  | "S"     => some S
  | _       => none

/-- A kernel name (`size`, `I`, …) or a raw tree term. -/
def parseTreeOrProg? (s : String) : Option Tree :=
  kernelNamed s <|> parseTree? s

def fail (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return 1

def needExpr : List String → Except String (Expr × List String)
  | [] => .error "missing expression"
  | s :: rest =>
      match parseExpr! s with
      | .ok e => .ok (e, rest)
      | .error m => .error m

def printResult (e : Expr) : IO UInt32 := do
  IO.println e
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["demo"] =>
      demo
      return 0
  | ["help"] | ["-h"] | ["--help"] =>
      IO.println usage
      return 0
  | ["test"] =>
      if (← runProgramSelfTest) then return 0 else return 1
  | "eval" :: rest =>
      match needExpr rest with
      | .error m => fail m
      | .ok (e, rest) =>
          match parseEnv rest with
          | .error m => fail m
          | .ok env =>
              match Expr.evalInt env e with
              | some n =>
                  IO.println n
                  return 0
              | none =>
                  match Expr.evalFloat (envToFloat env) e with
                  | some f =>
                      IO.println f
                      return 0
                  | none => fail "cannot evaluate (missing bindings or non-numeric)"
  | "simplify" :: rest =>
      match needExpr rest with
      | .error m => fail m
      | .ok (e, _) => printResult (Expr.simplify e)
  | "expand" :: rest =>
      match needExpr rest with
      | .error m => fail m
      | .ok (e, _) => printResult (Expr.expand e)
  | "normalize" :: rest =>
      match needExpr rest with
      | .error m => fail m
      | .ok (e, _) => printResult (Expr.normalize e)
  | "diff" :: rest =>
      match needExpr rest with
      | .error m => fail m
      | .ok (e, rest) =>
          let x := match rest with | v :: _ => v | [] => "x"
          printResult (Expr.dsimp x e)
  | "subst" :: rest =>
      match needExpr rest with
      | .error m => fail m
      | .ok (e, rest) =>
          match rest with
          | [] => fail "subst needs a binding, e.g. x=sin(y)"
          | b :: _ =>
              let parts := b.splitOn "="
              match parts with
              | [k, v] =>
                  match parseExpr? (trim v) with
                  | none => fail s!"cannot parse rhs: {v}"
                  | some rhs => printResult (Expr.simplify (Expr.subst (trim k) rhs e))
              | _ => fail "expected name=expr"
  | "encode" :: rest =>
      match needExpr rest with
      | .error m => fail m
      | .ok (e, _) =>
          IO.println (Expr.encode e)
          return 0
  | "reduce" :: rest =>
      match rest with
      | [] => fail "missing tree term"
      | s :: _ =>
          match parseTree? s with
          | none => fail s!"cannot parse tree: {s}"
          | some t =>
              match nf t with
              | some v =>
                  IO.println v
                  return 0
              | none => fail "reduction exhausted the evaluation budget"
  | "trace" :: rest =>
      match rest with
      | [] => fail "missing tree term"
      | s :: more =>
          match parseTree? s with
          | none => fail s!"cannot parse tree: {s}"
          | some t =>
              let maxSteps :=
                match more with
                | n :: _ => n.toNat?.getD defaultMaxSteps
                | [] => defaultMaxSteps
              IO.println (formatTrace t maxSteps)
              return 0
  | "equal" :: rest =>
      match rest with
      | sa :: sb :: _ =>
          match parseTree? sa, parseTree? sb with
          | some a, some b =>
              match nf a, nf b with
              | some av, some bv =>
                  match kernelEqual (eval! av) (eval! bv) with
                  | some v =>
                      IO.println v
                      return 0
                  | none => fail "equal exhausted the evaluation budget"
              | _, _ => fail "equal expects two closed programs"
          | none, _ => fail s!"cannot parse tree: {sa}"
          | _, none => fail s!"cannot parse tree: {sb}"
      | _ => fail "equal needs two tree terms"
  | "size" :: rest =>
      match rest with
      | [] => fail "missing tree term"
      | s :: _ =>
          match parseTreeOrProg? s with
          | none => fail s!"cannot parse tree: {s}"
          | some t =>
              match nf t with
              | none => fail "size expects a closed program"
              | some v =>
                  match kernelSize (eval! v) with
                  | some n =>
                      IO.println n
                      return 0
                  | none => fail "size exhausted the evaluation budget"
  | "bin" :: "succ" :: s :: _ =>
      match s.toNat? with
      | none => fail "bin succ expects a natural"
      | some n =>
          match kernelBinSucc (Value.ofBin n) with
          | some k =>
              IO.println k
              return 0
          | none => fail "binary succ exhausted the evaluation budget"
  | "bin" :: "pred" :: s :: _ =>
      match s.toNat? with
      | none => fail "bin pred expects a natural"
      | some n =>
          match kernelBinPred (Value.ofBin n) with
          | some k =>
              IO.println k
              return 0
          | none => fail "binary pred exhausted the evaluation budget"
  | "bin" :: op :: sa :: sb :: _ =>
      match sa.toNat?, sb.toNat? with
      | some a, some b =>
          let r :=
            match op with
            | "+" => kernelBinAdd (Value.ofBin a) (Value.ofBin b)
            | "*" => kernelBinMul (Value.ofBin a) (Value.ofBin b)
            | "^" => kernelBinPow (Value.ofBin a) (Value.ofBin b)
            | _   => none
          match r with
          | some n =>
              IO.println n
              return 0
          | none =>
              if op == "+" || op == "*" || op == "^" then
                fail "binary reduction diverged"
              else
                fail s!"unknown binary operator {op} (use + * ^ succ pred)"
      | _, _ => fail "bin expects two natural numbers"
  | "int" :: "neg" :: s :: _ =>
      match parseInt? s with
      | none => fail "int neg expects an integer"
      | some n =>
          match kernelINeg (Value.ofInt n) with
          | some v =>
              match v.toInt? with
              | some i =>
                  IO.println i
                  return 0
              | none => fail "int neg produced a non-integer"
          | none => fail "int neg exhausted the evaluation budget"
  | "int" :: op :: sa :: sb :: _ =>
      match parseInt? sa, parseInt? sb with
      | some a, some b =>
          let r :=
            match op with
            | "+" => kernelIAdd (Value.ofInt a) (Value.ofInt b)
            | "-" => kernelISub (Value.ofInt a) (Value.ofInt b)
            | "*" => kernelIMul (Value.ofInt a) (Value.ofInt b)
            | _   => none
          match r with
          | some v =>
              match v.toInt? with
              | some i =>
                  IO.println i
                  return 0
              | none => fail "int op produced a non-integer"
          | none =>
              if op == "+" || op == "-" || op == "*" then
                fail "signed-int reduction diverged"
              else
                fail s!"unknown int operator {op} (use + - * neg)"
      | _, _ => fail "int expects two integers"
  | "arith" :: sa :: op :: sb :: _ =>
      let na := sa.toNat?
      let nb := sb.toNat?
      match na, nb with
      | some a, some b =>
          let r :=
            match op with
            | "+" => kernelAdd (Value.ofNat a) (Value.ofNat b)
            | "*" => kernelMul (Value.ofNat a) (Value.ofNat b)
            | "^" => kernelPow (Value.ofNat a) (Value.ofNat b)
            | _   => none
          match r with
          | some v =>
              match v.toNat? with
              | some n =>
                  IO.println n
                  return 0
              | none =>
                  IO.println v
                  return 0
          | none =>
              if op == "+" || op == "*" || op == "^" then
                fail "tree reduction diverged"
              else
                fail s!"unknown operator {op} (use + * ^)"
      | _, _ => fail "arith expects two natural numbers"
  | "kernel-eval" :: rest =>
      match needExpr rest with
      | .error m => fail m
      | .ok (e, rest) =>
          match parseEnv rest with
          | .error m => fail m
          | .ok env =>
              match Expr.lookup "x" env <|> env.head?.map (·.snd) with
              | none => fail "kernel-eval needs x=<nat>"
              | some xv =>
                  if xv < 0 then fail "kernel-eval expects a natural x"
                  else
                    match kernelEvalInt xv.toNat e with
                    | some n =>
                        IO.println n
                        return 0
                    | none => fail "kernel-eval could not evaluate the encoded tree"
  | "kernel-diff" :: rest =>
      match needExpr rest with
      | .error m => fail m
      | .ok (e, _) =>
          match kernelDiffExpr e with
          | some d => printResult (Expr.simplify d)
          | none   => fail "kernel-diff could not analyse the encoded tree"
  | "show" :: kind :: _ =>
      match kernelNamed kind with
      | some t =>
          IO.println s!"{kind}  ({t.size} nodes)"
          IO.println t
          return 0
      | none => fail s!"unknown kernel program {kind}"
  | _ =>
      fail s!"unknown command\n\n{usage}"
