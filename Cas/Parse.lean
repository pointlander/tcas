/-
  Parsers for surface expressions and raw tree-calculus terms.
-/

import Cas.Expr
import Cas.Encode

namespace Cas

open String.Pos.Raw (atEnd get next)

structure Parser where
  input : String
  pos   : String.Pos.Raw
  deriving Repr

namespace Parser

def ofString (s : String) : Parser := ⟨s, ⟨0⟩⟩

def done (p : Parser) : Bool :=
  atEnd p.input p.pos

def peek (p : Parser) : Option Char :=
  if p.done then none else some (get p.input p.pos)

def bump (p : Parser) : Parser :=
  if p.done then p else { p with pos := next p.input p.pos }

partial def skipWs (p : Parser) : Parser :=
  match p.peek with
  | some c => if c.isWhitespace then skipWs p.bump else p
  | none   => p

partial def startsWith (p : Parser) (s : String) : Bool :=
  let rec go (i j : String.Pos.Raw) : Bool :=
    if atEnd s j then true
    else if atEnd p.input i then false
    else if get p.input i == get s j then
      go (next p.input i) (next s j)
    else false
  go p.pos ⟨0⟩

partial def consume (p : Parser) (s : String) : Option Parser :=
  if p.startsWith s then
    let rec skip (p : Parser) (j : String.Pos.Raw) : Parser :=
      if atEnd s j then p else skip p.bump (next s j)
    some (skip p ⟨0⟩)
  else none

def consumeChar (p : Parser) (c : Char) : Option Parser :=
  match p.peek with
  | some c' => if c == c' then some p.bump else none
  | none    => none

partial def parseNat (p : Parser) : Option (Nat × Parser) :=
  let rec digits (p : Parser) (acc : Nat) (seen : Bool) : Option (Nat × Parser) :=
    match p.peek with
    | some c =>
        if c.isDigit then
          digits p.bump (acc * 10 + (c.toNat - '0'.toNat)) true
        else if seen then some (acc, p) else none
    | none => if seen then some (acc, p) else none
  digits p 0 false

partial def parseIdent (p : Parser) : Option (String × Parser) :=
  let rec go (p : Parser) (acc : String) : Option (String × Parser) :=
    match p.peek with
    | some c =>
        if c.isAlphanum || c == '_' then
          go p.bump (acc.push c)
        else if acc.isEmpty then none else some (acc, p)
    | none => if acc.isEmpty then none else some (acc, p)
  match p.peek with
  | some c =>
      if c.isAlpha || c == '_' then go p.bump c.toString else none
  | none => none

end Parser

/-! ### Expression parser

  expr   ::= term (("+" | "-") term)*
  term   ::= unary (("*" | "/") unary)*
  unary  ::= "-" unary | power
  power  ::= atom ("^" unary)?
  atom   ::= number | ident ("(" expr ")")? | "(" expr ")"
-/

partial def parseExpr : Parser → Option (Expr × Parser)
  | p => parseExpr.go (p.skipWs)
where
  go (p : Parser) : Option (Expr × Parser) :=
    match parseTerm p with
    | none => none
    | some (a, p) => tail a p.skipWs
  tail (acc : Expr) (p : Parser) : Option (Expr × Parser) :=
    match p.peek with
    | some '+' =>
        match parseTerm p.bump.skipWs with
        | some (b, p) => tail (Expr.add acc b) p.skipWs
        | none => none
    | some '-' =>
        -- binary minus, not the start of a number already consumed
        match parseTerm p.bump.skipWs with
        | some (b, p) => tail (Expr.sub acc b) p.skipWs
        | none => none
    | _ => some (acc, p)

  parseTerm (p : Parser) : Option (Expr × Parser) :=
    match parseUnary p.skipWs with
    | none => none
    | some (a, p) => termTail a p.skipWs
  termTail (acc : Expr) (p : Parser) : Option (Expr × Parser) :=
    match p.peek with
    | some '*' =>
        match parseUnary p.bump.skipWs with
        | some (b, p) => termTail (Expr.mul acc b) p.skipWs
        | none => none
    | some '/' =>
        match parseUnary p.bump.skipWs with
        | some (b, p) => termTail (Expr.div acc b) p.skipWs
        | none => none
    | _ => some (acc, p)

  parseUnary (p : Parser) : Option (Expr × Parser) :=
    let p := p.skipWs
    match p.peek with
    | some '-' =>
        (parseUnary p.bump).map (fun (a, p) => (Expr.neg a, p))
    | _ => parsePower p

  parsePower (p : Parser) : Option (Expr × Parser) :=
    match parseAtom p.skipWs with
    | none => none
    | some (a, p) =>
        let p := p.skipWs
        match p.peek with
        | some '^' =>
            (parseUnary p.bump.skipWs).map (fun (b, p) => (Expr.pow a b, p))
        | _ => some (a, p)

  parseAtom (p : Parser) : Option (Expr × Parser) :=
    let p := p.skipWs
    -- parenthesised
    if let some p := p.consumeChar '(' then
      match parseExpr p with
      | some (e, p) =>
          let p := p.skipWs
          (p.consumeChar ')').map (fun p => (e, p))
      | none => none
    -- number
    else if let some (n, p) := p.parseNat then
      some (Expr.const (Int.ofNat n), p)
    -- identifier or function
    else if let some (id, p) := p.parseIdent then
      let p := p.skipWs
      if p.peek == some '(' then
        match parseExpr p.bump with
        | some (arg, p) =>
            let p := p.skipWs
            match p.consumeChar ')' with
            | none => none
            | some p =>
                match id with
                | "sin" => some (.sin arg, p)
                | "cos" => some (.cos arg, p)
                | "exp" => some (.exp arg, p)
                | "ln" | "log" => some (.ln arg, p)
                | "neg" => some (.neg arg, p)
                | _ => none
        | none => none
      else
        some (Expr.var id, p)
    else none

def parseExpr? (s : String) : Option Expr :=
  match parseExpr (Parser.ofString s) with
  | some (e, p) =>
      if p.skipWs.done then some e else none
  | none => none

def parseExpr! (s : String) : Except String Expr :=
  match parseExpr? s with
  | some e => .ok e
  | none   => .error s!"cannot parse expression: {s}"

/-! ### Tree-calculus term parser

  atom ::= "△" | "Δ" | "K" | "S" | "I" | nat | ident | "(" term ")"
  term ::= atom+   (juxtaposition = application)
-/

partial def parseTree : Parser → Option (Tree × Parser)
  | p =>
      let p := p.skipWs
      match parseAtom p with
      | none => none
      | some (t, p) => apps t p.skipWs
where
  apps (acc : Tree) (p : Parser) : Option (Tree × Parser) :=
    let p := p.skipWs
    match p.peek with
    | none => some (acc, p)
    | some ')' => some (acc, p)
    | some c =>
        if c.isWhitespace then apps acc p.skipWs
        else
          match parseAtom p with
          | some (a, p) => apps (acc ⬝ a) p
          | none => some (acc, p)

  parseAtom (p : Parser) : Option (Tree × Parser) :=
    let p := p.skipWs
    if let some p := p.consume "(" then
      match parseTree p with
      | some (t, p) => (p.skipWs.consumeChar ')').map (fun p => (t, p))
      | none => none
    else if let some p := p.consume "△" then some (△, p)
    else if let some p := p.consume "Δ" then some (△, p)
    else if let some p := p.consume "K" then
      if identCont p then none else some (K, p)
    else if let some p := p.consume "S" then
      if identCont p then none else some (S, p)
    else if let some p := p.consume "I" then
      if identCont p then none else some (I, p)
    else if let some (n, p) := p.parseNat then
      some (ofNat n, p)
    else if let some (id, p) := p.parseIdent then
      some (.ref id, p)
    else none

  identCont (p : Parser) : Bool :=
    match p.peek with
    | some c => c.isAlphanum || c == '_'
    | none   => false

def parseTree? (s : String) : Option Tree :=
  match parseTree (Parser.ofString s) with
  | some (t, p) => if p.skipWs.done then some t else none
  | none => none

/-! ### `x=1,y=2` environment parser -/

partial def trim : String → String
  | s =>
      let rec lcut (p : String.Pos.Raw) : String.Pos.Raw :=
        if atEnd s p then p
        else if (get s p).isWhitespace then lcut (next s p) else p
      let rec rcut (p : String.Pos.Raw) (last : String.Pos.Raw) : String.Pos.Raw :=
        if atEnd s p then last
        else if (get s p).isWhitespace then rcut (next s p) last
        else rcut (next s p) (next s p)
      let a := lcut ⟨0⟩
      let b := rcut a a
      let rec copy (p : String.Pos.Raw) (acc : String) : String :=
        if p == b || atEnd s p then acc
        else copy (next s p) (acc.push (get s p))
      copy a ""

def parseBinding (s : String) : Option (String × Int) :=
  let parts := s.splitOn "="
  match parts with
  | [k, v] =>
      let k := trim k
      let v := trim v
      if k.isEmpty then none
      else
        let rec intOf (s : String) : Option Int :=
          if s.startsWith "-" then
            (s.dropPrefix? "-").bind (fun sl => sl.toString.toNat?.map (fun n => -Int.ofNat n))
          else
            s.toNat?.map Int.ofNat
        (intOf v).map (fun n => (k, n))
  | _ => none

def parseEnv (ss : List String) : Except String Expr.Env :=
  let rec go : List String → Except String Expr.Env
    | [] => .ok []
    | s :: rest =>
        match parseBinding s with
        | none => .error s!"bad binding: {s}  (expected name=int)"
        | some b =>
            match go rest with
            | .ok env => .ok (b :: env)
            | .error e => .error e
  go ss

def envToFloat (env : Expr.Env) : Expr.FEnv :=
  env.map (fun (k, v) => (k, Float.ofInt v))

end Cas
