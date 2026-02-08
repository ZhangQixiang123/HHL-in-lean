/-
  Hyper Hoare Logic - Programming Language Syntax
  Based on "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties"
  by Dardinier and Müller (ETH Zurich)
-/

import Untitled.Basic

/-!
# Phase 2a: Programming Language Syntax

This file defines the syntax of an IMP-like programming language with:
- Arithmetic expressions
- Boolean expressions
- Commands (including nondeterministic choice and havoc)
-/

namespace HHL

/-! ## Arithmetic Expressions -/

/-- Binary operators on program values -/
inductive BinOp where
  | add : BinOp  -- addition
  | sub : BinOp  -- subtraction
  | mul : BinOp  -- multiplication
  | div : BinOp  -- integer division
  | mod : BinOp  -- modulo
deriving DecidableEq, Repr

namespace BinOp

/-- Evaluate a binary operator -/
def eval : BinOp → PVal → PVal → PVal
  | add, v₁, v₂ => v₁ + v₂
  | sub, v₁, v₂ => v₁ - v₂
  | mul, v₁, v₂ => v₁ * v₂
  | div, v₁, v₂ => if v₂ = 0 then 0 else v₁ / v₂
  | mod, v₁, v₂ => if v₂ = 0 then 0 else v₁ % v₂

end BinOp

/-- Comparison operators -/
inductive CmpOp where
  | eq  : CmpOp  -- equal
  | ne  : CmpOp  -- not equal
  | lt  : CmpOp  -- less than
  | le  : CmpOp  -- less than or equal
  | gt  : CmpOp  -- greater than
  | ge  : CmpOp  -- greater than or equal
deriving DecidableEq, Repr

namespace CmpOp

/-- Evaluate a comparison operator -/
def eval : CmpOp → PVal → PVal → Bool
  | eq, v₁, v₂ => v₁ == v₂
  | ne, v₁, v₂ => v₁ != v₂
  | lt, v₁, v₂ => v₁ < v₂
  | le, v₁, v₂ => v₁ ≤ v₂
  | gt, v₁, v₂ => v₁ > v₂
  | ge, v₁, v₂ => v₁ ≥ v₂

end CmpOp

/-- Arithmetic expressions -/
inductive Expr where
  | const : PVal → Expr                      -- constant value
  | var : PVar → Expr                        -- program variable
  | binop : BinOp → Expr → Expr → Expr       -- binary operation
deriving Repr

namespace Expr

/-- Evaluate an expression in a program state -/
def eval : Expr → PState → PVal
  | const v, _ => v
  | var x, σ => σ x
  | binop op e₁ e₂, σ => op.eval (e₁.eval σ) (e₂.eval σ)

/-- Variables occurring in an expression -/
def vars : Expr → Set PVar
  | const _ => ∅
  | var x => {x}
  | binop _ e₁ e₂ => e₁.vars ∪ e₂.vars

/-- Substitute a variable with an expression -/
def subst (e : Expr) (x : PVar) (e' : Expr) : Expr :=
  match e with
  | const v => const v
  | var y => if y = x then e' else var y
  | binop op e₁ e₂ => binop op (e₁.subst x e') (e₂.subst x e')

-- Convenient constructors
def zero : Expr := const 0
def one : Expr := const 1

instance : OfNat Expr n := ⟨const n⟩
instance : Add Expr := ⟨binop .add⟩
instance : Sub Expr := ⟨binop .sub⟩
instance : Mul Expr := ⟨binop .mul⟩
instance : Div Expr := ⟨binop .div⟩
instance : Mod Expr := ⟨binop .mod⟩

end Expr

/-! ## Boolean Expressions -/

/-- Boolean expressions -/
inductive BExpr where
  | tt : BExpr                               -- true
  | ff : BExpr                               -- false
  | not : BExpr → BExpr                      -- negation
  | and : BExpr → BExpr → BExpr              -- conjunction
  | or : BExpr → BExpr → BExpr               -- disjunction
  | cmp : CmpOp → Expr → Expr → BExpr        -- comparison
deriving Repr

namespace BExpr

/-- Evaluate a boolean expression in a program state -/
def eval : BExpr → PState → Bool
  | tt, _ => true
  | ff, _ => false
  | not b, σ => !(b.eval σ)
  | and b₁ b₂, σ => b₁.eval σ && b₂.eval σ
  | or b₁ b₂, σ => b₁.eval σ || b₂.eval σ
  | cmp op e₁ e₂, σ => op.eval (e₁.eval σ) (e₂.eval σ)

/-- Variables occurring in a boolean expression -/
def vars : BExpr → Set PVar
  | tt => ∅
  | ff => ∅
  | not b => b.vars
  | and b₁ b₂ => b₁.vars ∪ b₂.vars
  | or b₁ b₂ => b₁.vars ∪ b₂.vars
  | cmp _ e₁ e₂ => e₁.vars ∪ e₂.vars

/-- Substitute a variable with an expression -/
def subst (b : BExpr) (x : PVar) (e : Expr) : BExpr :=
  match b with
  | tt => tt
  | ff => ff
  | not b' => not (b'.subst x e)
  | and b₁ b₂ => and (b₁.subst x e) (b₂.subst x e)
  | or b₁ b₂ => or (b₁.subst x e) (b₂.subst x e)
  | cmp op e₁ e₂ => cmp op (e₁.subst x e) (e₂.subst x e)

-- Convenient constructors
def eq (e₁ e₂ : Expr) : BExpr := cmp .eq e₁ e₂
def ne (e₁ e₂ : Expr) : BExpr := cmp .ne e₁ e₂
def lt (e₁ e₂ : Expr) : BExpr := cmp .lt e₁ e₂
def le (e₁ e₂ : Expr) : BExpr := cmp .le e₁ e₂
def gt (e₁ e₂ : Expr) : BExpr := cmp .gt e₁ e₂
def ge (e₁ e₂ : Expr) : BExpr := cmp .ge e₁ e₂

end BExpr

/-! ## Commands -/

/-- Commands of the programming language -/
inductive Cmd where
  | skip : Cmd                               -- no-op
  | assign : PVar → Expr → Cmd               -- assignment: x := e
  | seq : Cmd → Cmd → Cmd                    -- sequence: c₁ ; c₂
  | choice : Cmd → Cmd → Cmd                 -- nondeterministic choice: c₁ [] c₂
  | assume : BExpr → Cmd                     -- assume: assume(b)
  | havoc : PVar → Cmd                       -- havoc: x := *
  | whileLoop : BExpr → Cmd → Cmd            -- while loop: while b do c
deriving Repr

namespace Cmd

/-- If-then-else as syntactic sugar using choice and assume -/
def ite (b : BExpr) (c₁ c₂ : Cmd) : Cmd :=
  choice (seq (assume b) c₁) (seq (assume b.not) c₂)

/-- Assert as assume (programs that violate the assertion get stuck) -/
def assert (b : BExpr) : Cmd := assume b

/-- Sequential composition of a list of commands -/
def seqList : List Cmd → Cmd
  | [] => skip
  | [c] => c
  | c :: cs => seq c (seqList cs)

/-- Variables written (modified) by a command -/
def writtenVars : Cmd → Set PVar
  | skip => ∅
  | assign x _ => {x}
  | seq c₁ c₂ => c₁.writtenVars ∪ c₂.writtenVars
  | choice c₁ c₂ => c₁.writtenVars ∪ c₂.writtenVars
  | assume _ => ∅
  | havoc x => {x}
  | whileLoop _ body => body.writtenVars

/-- Variables read by a command -/
def readVars : Cmd → Set PVar
  | skip => ∅
  | assign _ e => e.vars
  | seq c₁ c₂ => c₁.readVars ∪ c₂.readVars
  | choice c₁ c₂ => c₁.readVars ∪ c₂.readVars
  | assume b => b.vars
  | havoc _ => ∅
  | whileLoop b body => b.vars ∪ body.readVars

-- Notation for sequential composition
infixl:60 " ;; " => seq

-- Notation for nondeterministic choice
infixl:55 " [] " => choice

end Cmd

end HHL
