/- implementing HM algorithm on a simple language -/
import Std.Data.HashMap
open Std

/- a parametric type. Either base or arrow between bases.
used here so that the same type expressions can be used for
actual types of simple (nat, bool), but also variable types in the HM algorithm -/
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

section simple_syntax
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
  | `([lang| $a + $b])           => `(expr.apply (expr.apply (expr.var "+") [lang| $a]) [lang| $b])
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
end simple_syntax
end simple

open simple


/- HM Algorithm -/
section hindley_milner

-- types of errors during inference. just generic fail for now
inductive ErrorT where
| fail
deriving Repr, DecidableEq, BEq
abbrev InferM := StateT Nat (Except ErrorT) -- Monad to thread the next fresh type var, along with failures
abbrev UnifyM := Except ErrorT
instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

/- a different base type which intercepts the `base` of
the actual language to allow variable types in type expressions -/
inductive varBase where
| const : base → varBase -- known type, nat or bool
| var : Nat → varBase -- unknown type variable, e.g. 't1
deriving DecidableEq, BEq, Repr
abbrev const_type := type base -- alias for type expressions with only known, constant types
abbrev var_type := type varBase -- alias for type expressions with variable types

section var_type_syntax
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
end var_type_syntax

section constraints

  -- get a fresh unused type variable
  def fresh : InferM Nat := do
    let n ← get
    set (n + 1)
    return n

  -- type variable occurs in type expression
  def occurs (v : Nat) (e : var_type) : Bool :=
    match e with
    | .base (.var x) => x = v
    | .arrow t1 t2 => (occurs v t1) ∨ (occurs v t2)
    | _ => false

  -- environment = a mapping from variables to their types. can be variable
  abbrev env := var → Option var_type
  abbrev env.empty : env := fun _ => none
  abbrev env.update (x : var) (t : var_type) : env → env :=
    fun Γ y => if y=x then some t else Γ y
  abbrev env.ofList (L : List (var × var_type)) : env :=
    L.foldl (λ Γ (x, t) => Γ.update x t) env.empty
  abbrev env.union (Γ Γ' : env) : env := -- preference to right arg
    fun x => if Γ' x = none then Γ x else Γ' x

  -- initial environment with types of built-ins
  abbrev initialEnv := env.ofList [("+", [ty| nat -> nat -> nat])]
  abbrev env.extendInitial (Γ : env) := initialEnv.union Γ

  -- a constraint of the form 't1 = 't2
  abbrev Constraint := var_type × var_type

  -- return both the type of the expression (variable) and a list of constraints
  -- env |- e : t -| C, return t, C
  def infer (e : expr) (Γ : env) : InferM (var_type × List Constraint) :=
    match e with
    | expr.const c => match c with
      | const.nat _ => do return ([ty| nat], [])
      | const.bool _ => do return ([ty| bool], [])
    | expr.var x => match Γ x with
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
      let (t1, C) ← infer e (Γ.update name [ty| ?(t')])
      return ([ty| ?(t') -> ~(t1)], C)
    | expr.apply f inp => do
      let t' ← fresh
      let (t1, C1) ← infer f Γ
      let (t2, C2) ← infer inp Γ
      let C := [(t1, [ty| ~(t2) -> ?(t')])]
      return ([ty| ?(t')], C1 ++ C2 ++ C)

  def runInfer (e : expr) (Γ : env := initialEnv) : Except ErrorT (var_type × List Constraint) :=
    (infer e Γ).run' 0

end constraints

section unification

  -- substitution {subst / var}, e.g. {int → int / 't}
  abbrev SingleSubst := var_type × Nat
  abbrev Substitution := List SingleSubst

  def applySingleSubst (s : SingleSubst) (into : var_type) : var_type :=
    match into with
    | .base (.var x) => if x = s.2 then s.1 else into
    | .arrow t1 t2 => .arrow (applySingleSubst s t1) (applySingleSubst s t2)
    | _ => into
  def applySubst (S : Substitution) (into : var_type) : var_type :=
    S.foldl (fun acc s => applySingleSubst s acc) into

  def applySubstConstraints (S : Substitution) (into : List Constraint) : List Constraint :=
    into.map (fun c => (applySubst S c.1, applySubst S c.2))

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

  partial def unify (C: List Constraint) : UnifyM Substitution :=
    match C with
    | [] => do return []
    | (t1, t2) :: C' =>
      let bindVar (x : Nat) (t : var_type) (C' : List Constraint): UnifyM Substitution :=
        if occurs x t then throw ErrorT.fail else do
          let S := [(t, x)]
          let S' ← unify (applySubstConstraints S C')
          return S ++ S'
      match t1, t2 with
      -- identical variables / identical constants: nothing to learn
      | .base (.var x), .base (.var y) =>
        if x = y then unify C' else bindVar x t2 C'
      | .base (.const a), .base (.const b) =>
        if a = b then unify C' else throw ErrorT.fail
      -- a variable = anything else
      | .base (.var x), t | t, .base (.var x) => bindVar x t C'
      -- reduce
      | .arrow t1 t2, .arrow t3 t4 =>
        unify ((t1, t3) :: (t2, t4) :: C') -- push the two reduced constraints
      | _, _ => throw ErrorT.fail

end unification

def inferAndSolve (e : expr) (Γ : env := initialEnv) : Except ErrorT var_type := do
  let inferred ← runInfer e Γ
  let (t', constraints) := inferred
  let subst ← unify constraints
  let solved := applySubst subst t'
  return solved

/- end to end tests -/

def test_env := env.extendInitial <| env.ofList [
  ("x", [ty| nat]),
  ("y", [ty| nat]),
  ("b1", [ty| bool]),
  ("b2", [ty| bool]),
  ("f", [ty| nat -> nat]),
  ("g", [ty| nat -> nat]),
  ("h", [ty| nat -> nat -> nat]),
  ("nb", [ty| nat -> bool]),
  ("bn", [ty| bool -> nat]),
  ("bb", [ty| bool -> bool])
]
#eval inferAndSolve [lang| 3] test_env -- nat
#eval inferAndSolve [lang| true] test_env -- bool
#eval inferAndSolve [lang| 3 + x]  test_env -- nat
#eval inferAndSolve [lang| 3 + x]  test_env -- nat
#eval inferAndSolve [lang| f x] test_env -- nat
#eval inferAndSolve [lang| f (g x)] test_env -- nat
#eval inferAndSolve [lang| h x y] test_env -- nat
#eval inferAndSolve [lang| nb (h x y)] test_env -- bool
#eval inferAndSolve [lang| bn (nb (h x y))] test_env -- nat
#eval inferAndSolve [lang| false y] test_env -- fail
#eval inferAndSolve [lang| fun x => x + 1] test_env -- nat → nat
#eval inferAndSolve [lang| if b1 then y else 3] test_env -- nat
#eval inferAndSolve [lang| fun x => if x then 1 else 0] test_env
#eval inferAndSolve [lang| (fun x => x + 1) 5] test_env


end hindley_milner
