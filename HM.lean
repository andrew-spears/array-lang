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


  /- Surface syntax, so we can write `[lang| fun x => if x then 1 else 0]`
  instead of nesting constructors by hand. -/
  declare_syntax_cat lang

  syntax num : lang
  syntax ident : lang
  syntax "(" lang ")" : lang
  syntax:100 lang:100 lang:101 : lang                 -- application, left assoc
  syntax:65 lang:65 " + " lang:66 : lang              -- addition, left assoc
  syntax:10 "fun " ident " => " lang:10 : lang
  syntax:10 "if " lang " then " lang " else " lang:10 : lang

  syntax "[lang| " lang "]" : term

  macro_rules
  | `([lang| $n:num])            => `(expr.const (const.nat $n))
  | `([lang| $x:ident])          =>
    -- `true`/`false`/`plus` are keywords of the object language, not variables
    match x.getId.toString with
    | "true"  => `(expr.const (const.bool true))
    | "false" => `(expr.const (const.bool false))
    | "plus"  => `(expr.const const.plus)
    | name    => `(expr.var $(Lean.quote name))
  | `([lang| ($e)])              => `([lang| $e])
  | `([lang| $f $a])             => `(expr.apply [lang| $f] [lang| $a])
  | `([lang| $a + $b])           => `(expr.apply (expr.apply (expr.const const.plus) [lang| $a]) [lang| $b])
  | `([lang| fun $x => $b])      => `(expr.lam $(Lean.quote x.getId.toString) [lang| $b])
  | `([lang| if $c then $t else $e]) => `(expr.if_else [lang| $c] [lang| $t] [lang| $e])

  -- examples
  #check [lang| 3]
  #check [lang| true]
  #check [lang| 3 + x]
  #check [lang| f x y]                          -- application is left assoc: (f x) y
  #check [lang| false y]                        -- parses fine, fails typechecking later
  #check [lang| fun x => x + 1]
  #check [lang| if x then y else 3]
  #check [lang| fun x => if x then 1 else 0]
  #check [lang| (fun x => x + 1) 5]
end simple

open simple



/- HM Algorithm -/

-- types of errors during inference. just generic fail for now
inductive ErrorT where
| fail
deriving Repr, DecidableEq, BEq

/- a different base type to use for the algorithm. this intercepts the `base` of
the actual language to allow variable types in type expressions -/
inductive varBase where
| const : base → varBase -- known type, nat or bool
| var : Nat → varBase -- unknown type variable, e.g. 't1
deriving DecidableEq, BEq, Repr

abbrev const_type := type base -- alias for type expressions with only known, constant types
abbrev var_type := type varBase -- alias for type expressions with variable types

/- Surface syntax for type expressions, so we can write `[ty| nat -> '0]`
instead of nesting constructors. `->` is right assoc, as usual. -/
declare_syntax_cat ty

syntax "nat" : ty
syntax "bool" : ty
syntax "?" num : ty                             -- type variable, e.g. ?0
syntax "?" "(" term ")" : ty                    -- type variable from a runtime Nat, e.g. ?(t')
syntax "~" "(" term ")" : ty                    -- splice in a whole var_type, e.g. ~(t1)
syntax "(" ty ")" : ty
syntax:25 ty:26 " -> " ty:25 : ty               -- arrow, right assoc

syntax "[ty| " ty "]" : term

macro_rules
| `([ty| nat])        => `(type.base (varBase.const base.nat))
| `([ty| bool])       => `(type.base (varBase.const base.bool))
| `([ty| ?$n:num])    => `(type.base (varBase.var $n))
| `([ty| ?($t:term)]) => `(type.base (varBase.var $t))
| `([ty| ~($t:term)]) => `($t)
| `([ty| ($t)])       => `([ty| $t])
| `([ty| $a -> $b])   => `(type.arrow [ty| $a] [ty| $b])

#check [ty| nat]
#check [ty| nat -> bool]
#check [ty| ?0 -> ?1 -> ?0]                     -- right assoc: ?0 -> (?1 -> ?0)
#check [ty| (nat -> bool) -> ?2]

/- Print types back in the `[ty| ...]` surface syntax rather than as raw
constructors, so `#eval` output is readable. Parenthesise the left side of an
arrow only, since `->` is right assoc. -/
instance : ToString base where
  toString
    | base.nat => "nat"
    | base.bool => "bool"

instance : ToString varBase where
  toString
    | varBase.const b => toString b
    | varBase.var n => s!"?{n}"

def type.toString [ToString α] : type α → String
  | .base b => ToString.toString b
  | .arrow a b =>
    let l := match a with
      | .arrow _ _ => s!"({type.toString a})"   -- left side needs parens
      | _ => type.toString a
    s!"{l} -> {type.toString b}"

instance [ToString α] : ToString (type α) := ⟨type.toString⟩
instance [ToString α] : Repr (type α) := ⟨fun t _ => type.toString t⟩

#eval [ty| nat -> bool]
#eval [ty| ?0 -> ?1 -> ?0]
#eval [ty| (nat -> bool) -> ?2]

abbrev InferM := StateT Nat (Except ErrorT) -- Monad to thread the next fresh type var, along with failures
abbrev UnifyM := Except ErrorT

-- get a fresh unused type variable
def fresh : InferM Nat := do
  let n ← get
  set (n + 1)
  return n

-- environment = a mapping from variables to their types. can be variable
abbrev env := HashMap var var_type
abbrev env.ofList : List (var × var_type) → env := HashMap.ofList
#check (env.ofList [("a", [ty| nat]), ("b", [ty| ?1])] : env)

-- a constraint of the form 't1 = 't2
abbrev Constraint := var_type × var_type

-- return both the type of the expression (variable) and a list of constraints
def infer (e : expr) (Γ : env) : InferM (var_type × List Constraint) :=
  match e with
  | expr.const c => match c with
    | const.nat _ => do return ([ty| nat], [])
    | const.bool _ => do return ([ty| bool], [])
    | const.plus => do return ([ty| nat -> nat -> nat], [])
  | expr.var name => match Γ[name]? with
    | some t => do return (t, [])
    | none => throw ErrorT.fail
  | expr.if_else e1 e2 e3 => do
    let t' ← fresh -- the final output type
    let (t1, C1 )← infer e1 Γ
    let (t2, C2) ← infer e2 Γ
    let (t3, C3) ← infer e3 Γ
    let C := [
      (t1, [ty| bool]),
      (t2, [ty| ?(t')]),
      (t3, [ty| ?(t')])
    ]
    return ([ty| ?(t')], C1 ++ C2 ++ C3 ++ C)
  | expr.lam name e => do
    let t' ← fresh
    let (t1, C) ← infer e (Γ.insert name [ty| ?(t')])
    return ([ty| ?(t') -> ~(t1)], C)
  | expr.apply f inp => do
    let t' ← fresh
    let (t1, C1) ← infer f Γ
    let (t2, C2) ← infer inp Γ
    let C := [(t1, [ty| ~(t2) -> ?(t')])]
    return ([ty| ?(t')], C1 ++ C2 ++ C)

def runInfer (e : expr) (Γ : env := ∅) : Except ErrorT (var_type × List Constraint) :=
  (infer e Γ).run' 0

  #eval runInfer [lang| 3]
  #eval runInfer [lang| true]
  #eval runInfer [lang| 3 + x] (env.ofList [("x", [ty| nat])])
  #eval runInfer [lang| f x y]                          -- application is left assoc: (f x) y
  #eval runInfer [lang| false y]                        -- parses fine, fails typechecking later
  #eval runInfer [lang| fun x => x + 1]
  #eval runInfer [lang| if x then y else 3]
  #eval runInfer [lang| fun x => if x then 1 else 0]
  #eval runInfer [lang| (fun x => x + 1) 5]


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


-- -- total number of nodes in the tree
-- def sizeT : var_type → Nat
--   | .base _ => 1
--   | .arrow a b => 1 + sizeT a + sizeT b

-- -- sizeT summed over a list of constraints
-- def sizeC (c : List Constraint) : Nat :=
--   let sizes := c.map (fun c => sizeT c.1 + sizeT c.2)
--   sizes.sum

-- def varsOf : var_type → List Nat
--   | .base (.var x) => [x]
--   | .arrow t1 t2 => varsOf t1 ++ varsOf t2
--   | _ => []

-- theorem varOf_applySubst (s : Substitution) (into : var_type) :
--   varsOf (applySubst s into) ⊆ (varsOf into).erase s.var

-- def distinctVarsT (t : var_type) : Nat := (varsOf t).eraseDups.length

-- def distinctVarsC (C : List Constraint) : Nat :=
--   (C.map (fun c => distinctVarsT c.1 + distinctVarsT c.2)).sum -- TODO: completely wrong lol

partial def unify (C: List Constraint) : UnifyM (List Substitution) :=
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
    | .base (.var x), _ | _, .base (.var x) => bindVar x t2 tail
    -- reduce
    | .arrow t1 t2, .arrow t3 t4 =>
      unify ((t1, t3) :: (t2, t4) :: tail) -- push the two reduced constraints
    | _, _ => throw ErrorT.fail






-- def getSubstitution (substs : (List Substitution)) : UnifyM typeExpr
