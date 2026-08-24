/- implementing HM algorithm on a simple language -/
import Std.Data.HashMap
open Std



inductive type (baseType : Type) where
  | base : baseType → type baseType
  | arrow : type baseType → type baseType → type baseType
  deriving DecidableEq, BEq, Repr

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

  inductive base where
  | nat
  | bool
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


/- HM Algorithm -/

inductive ErrorT where
| fail
deriving Repr, DecidableEq, BEq

inductive varBase where
| const : base → varBase -- known type, nat or bool
| var : Nat → varBase -- unknown type variable, e.g. 't1
deriving DecidableEq, BEq, Repr

abbrev var_type := type varBase -- type expressions with variable types
abbrev const_type := type base -- type expressions with only known, constant types

abbrev InferM := StateT Nat (Except ErrorT) -- Monad to thread the next fresh type var, along with failures
abbrev UnifyM := Except ErrorT

-- get a fresh type variable
def fresh : InferM Nat := do
  let n ← get
  set (n + 1)
  return n

-- environment = a mapping from variables to their types
abbrev env := HashMap var var_type
abbrev env.ofList : List (var × var_type) → env := HashMap.ofList
#check (env.ofList [("a", type.base (varBase.const base.nat)), ("b", type.base (varBase.var 1))] : env)

-- a constraint of the form 't1 = 't2
abbrev Constraint := var_type × var_type

-- return both the type of the expression and a list of constraints
def infer (e : expr) (Γ : env) : InferM (var_type × List Constraint) :=
  match e with
  | expr.const c => match c with
    | const.nat _ => do return (type.base (varBase.const base.nat), [])
    | const.bool _ => do return (type.base (varBase.const base.bool), [])
    | const.plus => do return (type.arrow (type.base (varBase.const base.nat)) (type.base (varBase.const base.nat)), [])
  | expr.var name => match Γ[name]? with
    | some t => do return (t, [])
    | none => throw ErrorT.fail
  | expr.if_else e1 e2 e3 => do
    let t' ← fresh -- the final output type
    let (t1, C1 )← infer e1 Γ
    let (t2, C2) ← infer e2 Γ
    let (t3, C3) ← infer e3 Γ
    let C := [
      (t1, type.base (varBase.const base.bool)),
      (t2, (type.base (varBase.var t'))),
      (t3, (type.base (varBase.var t')))
    ]
    return (type.base (varBase.var t'), C1 ++ C2 ++ C3 ++ C)
  | expr.lam name e => do
    let t' ← fresh
    let (t1, C) ← infer e (Γ.insert name (type.base (varBase.var t')))
    return (type.arrow (type.base (varBase.var t')) t1, C)
  | expr.apply f inp => do
    let t' ← fresh
    let (t1, C1) ← infer f Γ
    let (t2, C2) ← infer inp Γ
    let C := [(t1, type.arrow t2 (type.base (varBase.var t')))]
    return (type.base (varBase.var t'), C1 ++ C2 ++ C)

def runInfer (e : expr) (Γ : env := ∅) : Except ErrorT (var_type × List Constraint) :=
  (infer e Γ).run' 0


#eval runInfer (expr.const (const.nat 4))
#eval runInfer (expr.var "a") -- fail

-- substitution {subst / var}, e.g. {int → int / 't}
structure Substitution where
  subst : var_type
  var : Nat


def occurs (v : Nat) (e : var_type) : Bool :=
  match e with
  | .base (.var x) => x = v
  | .arrow t1 t2 => (occurs v t1) ∨ (occurs v t2)
  | _ => false

def applySubst (s : Substitution) (into : var_type) : var_type :=
  match into with
  | .base (.var x) => if x = s.var then s.subst else into
  | .arrow t1 t2 => .arrow (applySubst s t1) (applySubst s t2)
  | _ => into

def applySubstList (s : Substitution) (into : List Constraint) : List Constraint :=
  into.map (fun c => (applySubst s c.1, applySubst s c.2))


-- total number of nodes in the tree
def sizeT : var_type → Nat
  | .base _ => 1
  | .arrow a b => 1 + sizeT a + sizeT b

-- sizeT summed over a list of constraints
def sizeC (c : List Constraint) : Nat :=
  let sizes := c.map (fun c => sizeT c.1 + sizeT c.2)
  sizes.sum

def varsOf : var_type → List Nat
  | .base (.var x) => [x]
  | .arrow t1 t2 => varsOf t1 ++ varsOf t2
  | _ => []

def distinctVarsT (t : var_type) : Nat := (varsOf t).eraseDups.length

def distinctVarsC (C : List Constraint) : Nat :=
  (C.map (fun c => distinctVarsT c.1 + distinctVarsT c.2)).sum

def unify (C: List Constraint) : UnifyM (List Substitution) :=
  match C with
  | [] => do return []
  | (t1, t2) :: tail =>
    let bindVar (x : Nat) (t : var_type) (tail : List Constraint): UnifyM (List Substitution) :=
      if occurs x t then throw ErrorT.fail else do
        let s := { subst := t, var := x }
        let St ← unify (applySubstList s tail)
        return s :: St
    match t1, t2 with
    -- identical variables / identical constants: nothing to learn
    | .base (.var x), .base (.var y) =>
      if x = y then unify tail else bindVar x t2 tail
    | .base (.const a), .base (.const b) =>
      if a = b then unify tail else throw ErrorT.fail
    -- a variable = anything else
    | .base (.var x), t | t, .base (.var x) => bindVar x t2 tail
    -- reduce
    | .arrow t1 t2, .arrow t3 t4 =>
      unify ((t1, t3) :: (t2, t4) :: tail) -- push the two reduced constraints
    | _, _ => throw ErrorT.fail
  termination_by (distinctVarsC C, sizeC C)
  decreasing_by sorry; sorry; sorry; sorry




-- def getSubstitution (substs : (List Substitution)) : UnifyM typeExpr
