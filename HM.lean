/- implementing HM algorithm on a simple language -/
import Std.Data.HashMap
open Std

#check Decidable


namespace simple
  /- A simple syntax to write expressions. No dependent types.
  purely for testing our HM implementation. This language allows some nonsense
  expressions like `3 + false`, but which a user might write and we have to
  be able to parse and attempt to typecheck. -/

  abbrev var := String -- store vars as just their names
  inductive const where
  | nat (n : Nat)
  | bool (b : Bool)
  | plus

  inductive expr where
  | const (c : const)
  | var (name : String)
  | lam (name : String) (body : expr)
  | if_else (e1 e2 e3 : expr)
  | apply (f : expr) (inp : expr)

/-
  Could do this?
  inductive type (baseType: Type) where
  | base : baseType -> type
  | arrow : type → type → type

  inductive base where
  | nat
  | bool

  simple.type := type base

  inductive varBase where
  | const : base -> varBase
  | var : varType -> varBase
-/

  inductive type where
  | nat
  | bool
  | arrow : type → type → type --unused rn because we usually only represent arrow as a typeExpr which allows variable types...
  deriving DecidableEq, BEq, Repr

  -- examples
  #check (expr.const (const.nat 3) : expr)
  #check (expr.const (const.bool true) : expr)
  #check (expr.const const.plus : expr)
  #check (expr.apply (expr.const const.plus) (expr.const (const.nat 3)) : expr) -- curried function λ x => 3 + x
  #check (expr.apply (expr.const (const.bool false)) (expr.var "y") : expr) -- this is technically valid, but will fail typechecking
  #check (expr.lam "x" (expr.apply (expr.const const.plus) (expr.var "x")) : expr)
  #check (expr.if_else (expr.var "x") (expr.var "y") (expr.const (const.nat 3)) : expr)
end simple

open simple

inductive ErrorT where
| fail
deriving Repr, DecidableEq, BEq

abbrev typeVar : Type := Nat -- unknown type variable, e.g. 't1
abbrev InferM := StateT Nat (Except ErrorT) -- Monad to thread the next fresh type var, along with failures
abbrev UnifyM := Except ErrorT

-- get a fresh type variable
def fresh : InferM typeVar := do
  let n ← get
  set (n + 1)
  return n


-- an expression over types
inductive typeExpr where
| const : type → typeExpr -- known type, e.g. int
| var : typeVar → typeExpr -- expression of just a typeVar
| arrow : typeExpr → typeExpr → typeExpr -- function, e.g. int → 't1
deriving DecidableEq, BEq, Repr

#check (typeExpr.arrow (typeExpr.const type.nat) (typeExpr.var 1) : typeExpr)


-- environment = a mapping from variables to their types
abbrev env := HashMap var typeExpr
abbrev env.ofList : List (var × typeExpr) → env := HashMap.ofList
#check (env.ofList [("a", typeExpr.const type.nat), ("b", typeExpr.var 1)] : env)


-- a constraint of the form 't1 = 't2
abbrev Constraint := typeExpr × typeExpr


-- substitution {subst / var}, e.g. {int → int / 't}
structure Substitution where
  subst : type
  var : typeVar


-- return both the type of the expression and a list of constraints
def infer (e : expr) (Γ : env) : InferM (typeExpr × List Constraint) :=
  match e with
  | expr.const c => match c with
    | const.nat _ => do return (typeExpr.const type.nat, [])
    | const.bool _ => do return (typeExpr.const type.bool, [])
    | const.plus => do return (typeExpr.const (type.arrow type.nat type.nat), [])
  | expr.var name => match Γ[name]? with
    | some t => do return (t, [])
    | none => throw ErrorT.fail
  | expr.if_else e1 e2 e3 => do
    let t' ← fresh -- the final output type
    let (t1, C1 )← infer e1 Γ
    let (t2, C2) ← infer e2 Γ
    let (t3, C3) ← infer e3 Γ
    let C := [
      (t1, typeExpr.const type.bool),
      (t2, (typeExpr.var t')),
      (t3, (typeExpr.var t'))
    ]
    return (typeExpr.var t', C1 ++ C2 ++ C3 ++ C)
  | expr.lam name e => do
    let t' ← fresh
    let (t1, C) ← infer e (Γ.insert name (typeExpr.var t'))
    return (typeExpr.arrow (typeExpr.var t') t1, C)
  | expr.apply f inp => do
    let t' ← fresh
    let (t1, C1) ← infer f Γ
    let (t2, C2) ← infer inp Γ
    let C := [(t1, typeExpr.arrow t2 (typeExpr.var t'))]
    return (typeExpr.var t', C1 ++ C2 ++ C)

def runInfer (e : expr) (Γ : env := ∅) : Except ErrorT (typeExpr × List Constraint) :=
  (infer e Γ).run' 0


-- #eval runInfer (expr.const (const.nat 4))
example : (runInfer (expr.const (const.nat 4)) = Except.ok (typeExpr.const (simple.type.nat), [])) := rfl

#eval runInfer (expr.var "a") -- fail
#eval runInfer (expr.var "a") (env.ofList [("a", typeExpr.const type.nat)]) -- nat


def occurs (v : typeVar) (e : typeExpr) : Bool := sorry

def applySubst (s : Substitution) (into : typeExpr) : typeExpr := sorry

def applySubstList (s : Substitution) (into : List Constraint) : List Constraint :=
  sorry -- substitute s into the list

def unify (C: List Constraint) : UnifyM (List Substitution) :=
  match C with
  | [] => do return []
  | (t1, t2) :: tail =>
    match t1, t2 with
    -- already unified, skip
    | .const t1, .const t2 =>
      if t1 = t2 then unify tail else throw ErrorT.fail
    | .var t1', .var t2' =>
      if t1' = t2' then unify tail else throw ErrorT.fail
    -- new subst
    | .var t1', .const t2 | .const t2, .var t1' => do
      let Sh := { subst := t2, var := t1'}
      let St ← unify (applySubstList Sh tail)
      return Sh :: St
    | .var t1', .arrow t2 t3 | .arrow t2 t3, .var t1' =>
      if occurs t1' t2 ∨ occurs t1' t3 then throw ErrorT.fail else do
      let Sh := { subst := type.arrow t2 t3, var := t1'}
      let St ← unify (applySubstList Sh tail)
      return Sh :: St

    | .arrow t1 t2, .arrow t3 t4 =>
      unify ((t1, t3) :: (t3, t4) :: tail) -- push the two reduced constraints
    | _, _ => throw ErrorT.fail



-- def getSubstitution (substs : (List Substitution)) : UnifyM typeExpr
