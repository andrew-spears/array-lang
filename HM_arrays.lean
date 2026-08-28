/- implementing HM algorithm on a simple language -/
open Std

/- a parametric type. Either base or arrow between bases.
used here so that the same type expressions can be used for
actual types of simple (nat, bool), but also variable types in the HM algorithm -/
inductive type (baseType : Type) where
| base : baseType → type baseType
| arrow : type baseType → type baseType → type baseType
deriving DecidableEq, BEq, Repr

namespace arr
  /- A language with array objects. types specify array shapes
  only allow 2d matrices over integers
  -/

  abbrev Var := String -- store vars as just their names
  inductive Const where
  | bool (b : Bool)
  | matrix (m n : Nat) -- this should really include the actual value, but im being lazy here

  inductive Expr where
  | const (c : Const)
  | var (name : String)
  | lam (name : String) (body : Expr)
  | if_else (e1 e2 e3 : Expr)
  | apply (f : Expr) (inp : Expr)
  | let_in (name : String) (e1 e2 : Expr) -- let [name] = [e1] in [e2]

  inductive BaseType where
  | bool
  | matrix (m n : Nat) -- type includes the shape now
  deriving DecidableEq, BEq, Repr

  def getType (c : Const) : BaseType := -- the canonical mapping of constants to their types
    match c with
    | .bool _ => .bool
    | .matrix m n => .matrix m n

section simple_syntax
  /- Surface syntax, so we can write `[lang| fun x => if x then 1 else 0]`
  instead of nesting constructors by hand. -/
  declare_syntax_cat lang

  syntax num : lang
  syntax "(" num ", " num ")" : lang        -- matrix literal, e.g. (3, 2)
  syntax ident : lang
  syntax "(" lang ")" : lang
  syntax:100 lang:100 lang:101 : lang                 -- application, left assoc
  syntax:65 lang:65 " + " lang:66 : lang              -- addition, left assoc
  syntax:10 "fun " ident " => " lang:10 : lang
  syntax:10 "if " lang " then " lang " else " lang:10 : lang
  syntax:10 "let " ident " = " lang " in " lang:10 : lang


  syntax "[lang| " lang "]" : term

  macro_rules
  | `([lang| ($m:num, $n:num)])  => `(Expr.const (Const.matrix $m $n))
  | `([lang| $x:ident])          =>
    match x.getId.toString with
    | "true"  => `(Expr.const (Const.bool true))
    | "false" => `(Expr.const (Const.bool false))
    | name    => `(Expr.var $(Lean.quote name))
  | `([lang| ($e)])              => `([lang| $e])
  | `([lang| $f $a])             => `(Expr.apply [lang| $f] [lang| $a])
  | `([lang| $a + $b])           => `(Expr.apply (Expr.apply (Expr.var "+") [lang| $a]) [lang| $b])
  | `([lang| fun $x => $b])      => `(Expr.lam $(Lean.quote x.getId.toString) [lang| $b])
  | `([lang| if $c then $t else $e]) => `(Expr.if_else [lang| $c] [lang| $t] [lang| $e])
  | `([lang| let $x = $e1 in $e2]) => `(Expr.let_in $(Lean.quote x.getId.toString) [lang| $e1] [lang| $e2])

  -- examples
  #check [lang| (3, 2)]
  #check [lang| f x y]                          -- application is left assoc: (f x) y
  #check [lang| false y]                        -- parses fine, fails typechecking later
  #check [lang| fun x => (2, 2)]
  #check [lang| if x then y else (1, 1)]
  #check [lang| fun x => if x then (2, 2) else (2, 2)]
  #check [lang| (fun x => x) (3, 3)]
  #check [lang| let x = (2, 3) in x]
  #check [lang| let x = (5, 5) in fun y => y + x]
end simple_syntax
end arr

open arr


/- HM Algorithm -/
section hindley_milner


abbrev TVar := Nat -- a type variable
inductive ErrorT where
| fail
deriving Repr, DecidableEq, BEq
abbrev Error := Except ErrorT
abbrev fail {α} : Error α := Except.error ErrorT.fail
instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false
abbrev InferM := StateT TVar Error -- Monad to thread the next fresh type var, along with failures

inductive TypeAtom where -- leaves of an OpenType
| const : BaseType → TypeAtom -- known type
| var : TVar → TypeAtom -- unknown TVar, e.g. 't1
deriving DecidableEq, BEq, Repr

abbrev OpenType  := type TypeAtom   -- may contain TVars; what inference works with
abbrev GroundType := type BaseType     -- no variables; a finished, concrete type

def type.tvars (t : OpenType) : List TVar :=
  match t with
  | .base (.var x) => [x]
  | .arrow t1 t2 => (t1.tvars ++ t2.tvars).eraseDups
  | _ => []

/- universally quantified type, e.g. ∀ 'a, 'a -> 'a.
This is fundamentally different than free type variables, e.g. ?0 -> ?0.
The first only appears in inference, and isn't truly a valid type of an expression.
The second is not actually polymorphic - ?0 -> ?0 means the identity function for a specific, unknown type.
`(fun f -> (f 0, f true)) (fun x -> x)`     -- rejected by HM
`let f = fun x -> x in (f 0, f true)`       -- accepted -/
structure TypeScheme where
  bound : List TVar
  body : OpenType
instance : Coe OpenType TypeScheme := ⟨fun t => { bound := [], body := t }⟩
-- TVars present in the body but not quantified
def TypeScheme.free (σ : TypeScheme) : List TVar :=
  σ.body.tvars.removeAll σ.bound

section open_type_syntax
  /- Surface syntax for type expressions, so we can write `[ty| nat -> '0]`
  instead of nesting constructors. `->` is right assoc, as usual. -/
  declare_syntax_cat ty

  syntax "bool" : ty
  syntax "(" num ", " num ")" : ty                -- matrix of shape m, n
  syntax "?" num : ty                             -- type variable, e.g. ?0
  syntax "?" "(" term ")" : ty                    -- type variable from a runtime Nat, e.g. ?(t')
  syntax "~" "(" term ")" : ty                    -- splice in a whole OpenType, e.g. ~(t1)
  syntax "(" ty ")" : ty
  syntax:25 ty:26 " -> " ty:25 : ty               -- arrow, right assoc

  syntax "[ty| " ty "]" : term

  macro_rules
  | `([ty| bool])       => `(type.base (TypeAtom.const BaseType.bool))
  | `([ty| ($m:num, $n:num)])       => `(type.base (TypeAtom.const (BaseType.matrix $m $n)))
  | `([ty| ?$n:num])    => `(type.base (TypeAtom.var $n))
  | `([ty| ?($t:term)]) => `(type.base (TypeAtom.var $t))
  | `([ty| ~($t:term)]) => `($t)
  | `([ty| ($t)])       => `([ty| $t])
  | `([ty| $a -> $b])   => `(type.arrow [ty| $a] [ty| $b])

  #check [ty| bool]
  #check [ty| (2, 3)]
  #check [ty| ?0 -> ?1 -> ?0]                     -- right assoc: ?0 -> (?1 -> ?0)
  #check [ty| ((2, 3) -> bool) -> ?2]

  /- Print types back in the `[ty| ...]` surface syntax rather than as raw
  constructors, so `#eval` output is readable. Parenthesise the left side of an
  arrow only, since `->` is right assoc. -/
  instance : ToString BaseType where
    toString
      | BaseType.bool => "bool"
      | BaseType.matrix m n => s!"({m}, {n})"

  instance : ToString TypeAtom where
    toString
      | TypeAtom.const b => toString b
      | TypeAtom.var n => s!"?{n}"

  def type.toString [ToString α] : type α → String
    | .base b => ToString.toString b
    | .arrow a b =>
      let l := match a with
        | .arrow _ _ => s!"({type.toString a})"   -- left side needs parens
        | _ => type.toString a
      s!"{l} -> {type.toString b}"

  instance [ToString α] : ToString (type α) := ⟨type.toString⟩
  instance [ToString α] : Repr (type α) := ⟨fun t _ => type.toString t⟩

  #eval [ty| (2, 3) -> (3, 4)]
  #eval [ty| ?0 -> ?1 -> ?0]
  #eval [ty| ((1, 1) -> bool) -> ?2]

    /- Surface syntax for type schemes: `[sch| forall ?0 ?1, ?0 -> ?1]`, or
  `[sch| nat -> bool]` for a monomorphic one (empty binder list). -/
  syntax "[sch| " "forall " (("?" num)+) ", " ty "]" : term
  syntax "[sch| " ty "]" : term

  macro_rules
  | `([sch| forall $[?$ns:num]*, $t]) => `({ bound := [$[$ns],*], body := [ty| $t] : TypeScheme })
  | `([sch| $t:ty])                   => `({ bound := [], body := [ty| $t] : TypeScheme })

  /- Print schemes back in that syntax. Monomorphic schemes print as bare types,
  matching how OCaml hides the quantifier. -/
  def TypeScheme.toString (σ : TypeScheme) : String :=
  match σ.bound with
  | [] => ToString.toString σ.body
  | bs => "forall " ++ String.intercalate " " (bs.map (s!"?{·}")) ++ ", " ++ ToString.toString σ.body

  instance : ToString TypeScheme := ⟨TypeScheme.toString⟩
  instance : Repr TypeScheme := ⟨fun σ _ => TypeScheme.toString σ⟩

  #eval [sch| forall ?0, ?0 -> ?0]              -- the identity function's scheme
  #eval [sch| forall ?0 ?1, ?0 -> ?1 -> ?0]     -- fun x y => x
  #eval [sch| (2, 2) -> ?3]                       -- monomorphic, bound = []
  #eval [sch| forall ?0, (4, 4)]                   -- representable but generalize won't build it

end open_type_syntax


-- get a fresh unused type variable
def fresh : InferM TVar := do
  let n ← get
  set (n + 1)
  return n
def occurs (v : TVar) (e : OpenType) : Bool :=
  match e with
  | .base (.var x) => x = v
  | .arrow t1 t2 => (occurs v t1) ∨ (occurs v t2)
  | _ => false

-- environment = a mapping from variables to their types (implicitly TypeSchemes)
structure Env where
  lookup : Var → Option TypeScheme
  domain : List Var
abbrev Env.empty : Env := { lookup := λ _ => none, domain := [] }
abbrev Env.update (name : Var) (t : TypeScheme) : Env → Env :=
  λ Γ => { lookup:= λ x => if x=name then some t else Γ.lookup x,
            domain := name :: Γ.domain }
abbrev Env.ofList (L : List (Var × TypeScheme)) : Env :=
  L.foldl (λ Γ (name, t) => Γ.update name t) Env.empty
abbrev Env.union (Γ Γ' : Env) : Env := -- preference to right arg
  { lookup:= λ name => if Γ'.lookup name = none then Γ.lookup name else Γ'.lookup name,
    domain:= Γ.domain ++ Γ'.domain }
-- union of the free TVars across every binding
def Env.free (Γ : Env) :=
  (Γ.domain.filterMap Γ.lookup).flatMap TypeScheme.free |>.eraseDups

-- initial environment with types of built-ins
abbrev initialEnv := Env.ofList [("+", [sch| (2, 2) -> (2, 2) -> (2, 2)])] -- for now. Should really be forall m n, (m, n) -> (m, n) -> (m, n)
abbrev Env.extendInitial (Γ : Env) := initialEnv.union Γ

/- substitution {subst / var}, e.g. {int → int / 't}. -/
abbrev Subst := TVar → Option OpenType
abbrev Subst.empty : Subst := λ _ => none
abbrev Subst.singleton (x : TVar) (t : OpenType): Subst :=
  λ y => if x=y then some t else none

def type.subst (t : OpenType) (S : Subst) : OpenType :=
  match t with
  | .base (.var x) => match S x with
    | some t' => t' -- substitute
    | none => t -- leave alone
  | .arrow t1 t2 => type.arrow (t1.subst S) (t2.subst S)
  | _ => t

abbrev Subst.compose (S S' : Subst) : Subst := -- apply right to left
  λ x => match S' x with
  | none => S x
  | some t => t.subst S
abbrev Subst.update (S : Subst) (x : TVar) (t : OpenType) : Subst := -- compose by adding to the left
  (Subst.singleton x t).compose S
abbrev Subst.sequential (L : List (TVar × OpenType)) : Subst :=
  L.foldr (λ (x, t) S => S.update x t) Subst.empty -- TODO: this is backwards from convention?
abbrev Subst.parallel (L : List (TVar × OpenType)) : Subst :=
  λ x => L.lookup x

/- Subst should never overwrite a bound variable (generalize should prevent this too) -/
def TypeScheme.subst (σ : TypeScheme) (S : Subst) : TypeScheme :=
  { σ with body := σ.body.subst (λ x => if σ.bound.contains x then none else S x) }
def Env.subst (Γ : Env) (S : Subst) : Env :=
  { lookup := λ name => (Γ.lookup name).map (·.subst S),
    domain := Γ.domain }

abbrev Constraint := OpenType × OpenType
def Constraint.subst (c : Constraint) (S : Subst) : Constraint :=
  (c.1.subst S, c.2.subst S)
def substConstraints (C : List Constraint) (S : Subst) : List Constraint :=
  C.map (·.subst S)

-- return (the most general) substitution that unifies all constraints
partial def unify (C: List Constraint) : Error Subst :=
  match C with
  | [] => do return Subst.empty
  | (t1, t2) :: C' =>
    let bindVar (x : TVar) (t : OpenType) (C' : List Constraint): Error Subst :=
      if occurs x t then throw ErrorT.fail else do
        let S := Subst.singleton x t
        let S' ← unify (substConstraints C' S)
        return S'.compose S
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

-- replace all bound variables in a type scheme with fresh vars
def instantiate (σ : TypeScheme) : InferM OpenType := do
  let fresh_vars ← σ.bound.mapM (λ a' => do
    let b' ← fresh
    return (a', [ty| ?(b')])
  )
  let S := Subst.parallel fresh_vars
  return σ.body.subst S

-- generalize [name] into a universally quantified variable, return the modified env
def generalize (C : List Constraint) (Γ : Env) (name : Var) (t : OpenType) : Error Env := do
  let S ← unify C -- might fail
  let u := t.subst S
  let Γ' := Γ.subst S
  let vars := u.tvars.removeAll Γ'.free
  let scheme := { bound := vars, body := u }
  let Γ'' := Γ'.update name scheme
  return Γ''


-- return both the type of the expression (variable) and a list of constraints
-- Γ |- e : t -| C, return t, C
def buildConstraints (e : Expr) (Γ : Env) : InferM (OpenType × List Constraint) :=
  match e with
  | Expr.const c => do return (type.base (TypeAtom.const (getType c)), [])
  | Expr.var x => match Γ.lookup x with
    | some σ => do
      let t ← instantiate σ
      return (t, [])
    | none => throw ErrorT.fail
  | Expr.if_else e1 e2 e3 => do
    let t' ← fresh -- the final output type
    let (t1, C1 )← buildConstraints e1 Γ
    let (t2, C2) ← buildConstraints e2 Γ
    let (t3, C3) ← buildConstraints e3 Γ
    let C := [
      (t1, [ty| bool]),
      (t2, [ty| ?(t')]),
      (t3, [ty| ?(t')])
    ]
    return ([ty| ?(t')], C1 ++ C2 ++ C3 ++ C)
  | Expr.lam name e => do
    let t' ← fresh
    let (t1, C) ← buildConstraints e (Γ.update name [ty| ?(t')])
    return ([ty| ?(t') -> ~(t1)], C)
  | Expr.apply f inp => do
    let t' ← fresh
    let (t1, C1) ← buildConstraints f Γ
    let (t2, C2) ← buildConstraints inp Γ
    let C := [(t1, [ty| ~(t2) -> ?(t')])]
    return ([ty| ?(t')], C1 ++ C2 ++ C)
  | Expr.let_in name e1 e2 => do
    let (t1, C1) ← buildConstraints e1 Γ
    let Γ' ← generalize C1 Γ name t1
    let (t2, C2) ← buildConstraints e2 Γ'
    return (t2, C1 ++ C2)

def runBuildConstraints (e : Expr) (Γ : Env := initialEnv) : Error (OpenType × List Constraint) :=
  (buildConstraints e Γ).run' 0


-- reduce open TVars like ?2 down to the lowest distinct naturals
def lowerTVars (t : OpenType) : OpenType :=
  let rn := t.tvars.zipIdx
  t.subst (fun x => (rn.lookup x).map (fun i => [ty| ?(i)]))

-- top level function, returns the inferred type
def infer (e : Expr) (Γ : Env := initialEnv) : Error OpenType := do
  let (t', constraints)  ← runBuildConstraints e Γ
  let subst ← unify constraints
  let solved := t'.subst subst
  let lowered := lowerTVars solved
  return lowered

section testing
  /- end to end tests -/

  def test_env := Env.extendInitial <| Env.ofList [
    ("x", [ty| (2, 2)]),
    ("y", [ty| (2, 2)]),
    ("b1", [ty| bool]),
    ("b2", [ty| bool]),
    ("f", [ty| (2, 2) -> (2, 2)]),
    ("g", [ty| (2, 2) -> (2, 2)]),
    ("h", [ty| (2, 2) -> (2, 2) -> (2, 2)]),
    ("nb", [ty| (2, 2) -> bool]),
    ("bn", [ty| bool -> (2, 2)]),
    ("bb", [ty| bool -> bool])
  ]

  macro "#test " e:term " : " t:term : command => `(
    #eval (do
      let expected : Error OpenType := $t
      let actual := infer $e test_env
      if actual == expected then pure ()
      else throw (IO.userError s!"expected {repr expected}, got {repr actual}")
      : IO Unit)
  )

  #test [lang| f x] : (Except.ok [ty| (2, 2)])
  #test [lang| f (g x)] : (.ok [ty| (2, 2)])
  #test [lang| h x y] : (.ok [ty| (2, 2)])
  #test [lang| nb (h x y)] : (.ok [ty| bool])
  #test [lang| bn (nb (h x y))] : (.ok [ty| (2, 2)])
  #test [lang| false y] : fail
  #test [lang| fun x => x + 1] : (.ok [ty| (2, 2) -> (2, 2)])
  #test [lang| if b1 then y else (2, 2)] : (.ok [ty| (2, 2)])
  #test [lang| fun x' => if x' then (2, 2) else (2, 2)] : (.ok [ty| bool -> (2, 2)])
  #test [lang| (fun x' => x' + (2, 2)) (2, 2)] : (.ok [ty| (2, 2)])
  #test [lang| (fun f' => fun x' => f' (x' + (2, 2)))] : (.ok [ty| ((2, 2) -> ?0) -> (2, 2) -> ?0])
  #test [lang| (let id = fun x => x in id)] : (.ok [ty| ?0 -> ?0])
  #test [lang| (let id = fun x => x in id true)] : (.ok [ty| bool])
  #test [lang| (let id = fun x => x in id (2, 2))] : (.ok [ty| (2, 2)])

  /- let-polymorphism -/
  #test [lang| let x' = (2, 2) in x'] : (.ok [ty| (2, 2)])
  #test [lang| let x' = (2, 2) in let y' = true in y'] : (.ok [ty| bool])
  #test [lang| let x' = (2, 2) in x' + (2, 2)] : (.ok [ty| (2, 2)])
  #test [lang| let f' = fun x' => x' + (2, 2) in f' (2, 2)] : (.ok [ty| (2, 2)])
  #test [lang| let f' = fun x' => x' + (2, 2) in f' true] : fail

  -- the point of generalization: one binding used at two different types
  #test [lang| let id = fun x => x in let a = id (2, 2) in id true] : (.ok [ty| bool])
  #test [lang| let id = fun x => x in if id true then id (2, 2) else (2, 2)] : (.ok [ty| (2, 2)])
  #test [lang| let id = fun x => x in (id (id (2, 2)))] : (.ok [ty| (2, 2)])
  #test [lang| let id = fun x => x in fun z => id z] : (.ok [ty| ?0 -> ?0])
  #test [lang| let id = fun x => x in fun z => id (id z)] : (.ok [ty| ?0 -> ?0])

  -- contrast: lambda-bound is NOT generalized, so this must fail
  #test [lang| fun id => if id true then id (2, 2) else (2, 2)] : fail

  /- generalizing multiple variables -/
  #test [lang| let k = fun a => fun b => a in k (2, 2) true] : (.ok [ty| (2, 2)])
  #test [lang| let k = fun a => fun b => a in k true (2, 2)] : (.ok [ty| bool])
  #test [lang| let k = fun a => fun b => a in k] : (.ok [ty| ?0 -> ?1 -> ?0])
  #test [lang| let ap = fun f' => fun v => f' v in ap (fun n => n + (2, 2)) (2, 2)] : (.ok [ty| (2, 2)])
  #test [lang| let ap = fun f' => fun v => f' v in ap] : (.ok [ty| (?0 -> ?1) -> ?0 -> ?1])

  /- variables free in the env must NOT be generalized -/
  #test [lang| fun y' => let f' = fun z => y' in f' (2, 2)] : (.ok [ty| ?0 -> ?0])
  #test [lang| fun y' => let f' = fun z => y' in if f' (2, 2) then f' (2, 2) else (2, 2)] : fail
  #test [lang| fun y' => let f' = fun z => y' in (f' (2, 2)) + (f' true)] : (.ok [ty| (2, 2) -> (2, 2)])
  #test [lang| fun y' => let f' = fun z => y' in if y' then f' (2, 2) else f' true] : (.ok [ty| bool -> bool])


  /- nesting and shadowing -/
  #test [lang| let id = fun x => x in let id2 = id in id2 true] : (.ok [ty| bool])
  #test [lang| let x' = (2, 2) in let x' = true in x'] : (.ok [ty| bool])
  #test [lang| let f' = fun x => x in let g' = fun y => f' y in g' (2, 2)] : (.ok [ty| (2, 2)])
  #test [lang| let c = fun a => fun b => a + b in c (2, 2) (2, 2)] : (.ok [ty| (2, 2)])
  #test [lang| let b = true in if b then let n = (2, 2) in n else (2, 2)] : (.ok [ty| (2, 2)])

end testing
end hindley_milner
