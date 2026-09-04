import ArrayLang.Matrices
open Matrices
open Std

universe u

/- implementing HM algorithm on an array language -/

/- a parametric type. Either base or arrow between bases.
used here so that the same type expressions can be used for
actual types of simple (nat, bool), but also variable types in the HM algorithm -/
inductive type (baseType : Type) where
| base : baseType → type baseType
| arrow : type baseType → type baseType → type baseType
deriving DecidableEq, BEq, Repr

section arr
  /- A language with array objects. types specify array shapes
  only allow 2d matrices over integers
  -/

  abbrev Var := String -- store vars as just their names
  inductive Const where
  | matrix (m n : Nat) (A : Matrix Int m n)

  inductive Expr where
  | const (c : Const)
  | var (name : String)
  | lam (name : String) (body : Expr)
  -- | if_else (e1 e2 e3 : Expr)
  | apply (f : Expr) (inp : Expr)
  | let_in (name : String) (e1 e2 : Expr) -- let [name] = [e1] in [e2]

  inductive Dim where
  | const : Nat → Dim
  | var : Nat → Dim -- variable dimension. Nat is just an index
  deriving DecidableEq, BEq, Repr

  inductive BaseType where
  | arr (m n : Dim) -- type includes the shape
  deriving DecidableEq, BEq, Repr

  def getType (c : Const) : BaseType := -- the canonical mapping of constants to their types
    match c with
    | .matrix m n _ => .arr (Dim.const m) (Dim.const n)

section arr_syntax
  /- Surface syntax, so we can write `[lang| fun x => if x then 1 else 0]`
  instead of nesting constructors by hand. -/
  declare_syntax_cat lang

  syntax num : lang
  syntax ident : lang
  syntax "(" lang ")" : lang
  syntax:100 lang:100 lang:101 : lang                 -- application, left assoc
  syntax:65 lang:65 " + " lang:66 : lang              -- addition, left assoc
  syntax:65 lang:65 " * " lang:66 : lang              -- matrix mult, left assoc
  syntax:10 "fun " ident " => " lang:10 : lang
  -- syntax:10 "if " lang " then " lang " else " lang:10 : lang
  syntax:10 "let " ident " = " lang " in " lang:10 : lang


  syntax "[lang| " lang "]" : term

  macro_rules
  | `([lang| $x:ident])          =>
    match x.getId.toString with
    | "I" => `(Expr.var "I")
    | name    => `(Expr.var $(Lean.quote name))
  | `([lang| ($e)])              => `([lang| $e])
  | `([lang| $f $a])             => `(Expr.apply [lang| $f] [lang| $a])
  | `([lang| $a + $b])           => `(Expr.apply (Expr.apply (Expr.var "+") [lang| $a]) [lang| $b])
  | `([lang| $a * $b])           => `(Expr.apply (Expr.apply (Expr.var "*") [lang| $a]) [lang| $b])
  | `([lang| fun $x => $b])      => `(Expr.lam $(Lean.quote x.getId.toString) [lang| $b])
  -- | `([lang| if $c then $t else $e]) => `(Expr.if_else [lang| $c] [lang| $t] [lang| $e])
  | `([lang| let $x = $e1 in $e2]) => `(Expr.let_in $(Lean.quote x.getId.toString) [lang| $e1] [lang| $e2])

   -- examples
  #check [lang| I]
  #check [lang| true]
  #check [lang| I4 + x]
  #check [lang| I4 * x]
  #check [lang| f x y]                          -- application is left assoc: (f x) y
  #check [lang| false y]                        -- parses fine, fails typechecking later
  #check [lang| fun x => x + I2]
  #check [lang| (fun x => x + I2) y]
  #check [lang| let x = I2 + I3 in x] -- should fail typecheck
  #check [lang| let x = I2 in fun y => y + x]
end arr_syntax
end arr



/- HM Algorithm -/
section hindley_milner

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

abbrev InferM := StateT (Nat × Nat) Error -- Monad to thread the next fresh type var and dimension var, along with failures.

inductive TypeAtom where -- leaves of an OpenType
| const : BaseType → TypeAtom -- known type, with variable dimensions -- TODO should this be DimBase +?
| var : Nat → TypeAtom -- unknown TVar, e.g. 't1
deriving DecidableEq, BEq, Repr

abbrev OpenType := type TypeAtom -- may contain TVars; not a 'real' type in the language

structure Vars where
  tys : List Nat
  dims : List Nat
deriving Repr, BEq
def Vars.empty : Vars := ⟨[], []⟩
def Vars.union (a b : Vars) : Vars :=
  ⟨(a.tys ++ b.tys).eraseDups, (a.dims ++ b.dims).eraseDups⟩
def Vars.removeAll (a b : Vars) : Vars :=
  ⟨a.tys.removeAll b.tys, a.dims.removeAll b.dims⟩

def Dim.Vars (d : Dim) : Vars :=
  match d with
  | .var x => Vars.mk [] [x]
  | .const _ => Vars.empty
def type.Vars (t : OpenType) : Vars :=
  match t with
  | .base (.var x) => Vars.mk [x] []
  | .base (.const (.arr m n)) => Vars.union m.Vars n.Vars
  | .arrow t1 t2 => Vars.union t1.Vars t2.Vars

/- universally quantified type, e.g. ∀ 'a, 'a -> 'a.
This is fundamentally different than free type variables, e.g. ?0 -> ?0.
The first only appears in inference, and isn't truly a valid type of an expression.
The second is not actually polymorphic - ?0 -> ?0 means the identity function for a specific, unknown type.
`(fun f -> (f 0, f true)) (fun x -> x)`     -- rejected by HM
`let f = fun x -> x in (f 0, f true)`       -- accepted -/
structure TypeScheme where
  bound : Vars
  body : OpenType
instance : Coe OpenType TypeScheme := ⟨fun t => { bound := Vars.empty, body := t }⟩

-- Vars present in the body but not quantified
def TypeScheme.free (σ : TypeScheme) : Vars :=
  σ.body.Vars.removeAll σ.bound

section open_type_syntax
  /- Surface syntax for type expressions, so we can write `[ty| nat -> '0]`
  instead of nesting constructors. `->` is right assoc, as usual. -/

  declare_syntax_cat dim

  syntax "#" num : dim -- variable dimension
  syntax "#" "(" term ")" : dim -- variable dimension
  syntax num : dim -- known dimension

  declare_syntax_cat ty

  syntax "(" dim ", " dim ")" : ty                -- matrix of shape m, n
  syntax "?" num : ty                             -- type variable, e.g. ?0
  syntax "?" "(" term ")" : ty                    -- type variable from a runtime Nat, e.g. ?(t')
  syntax "~" "(" term ")" : ty                    -- splice in a whole OpenType, e.g. ~(t1)
  syntax "(" ty ")" : ty
  syntax:25 ty:26 " -> " ty:25 : ty               -- arrow, right assoc
  syntax "[ty| " ty "]" : term

  def expandDim : Lean.TSyntax `dim → Lean.MacroM (Lean.TSyntax `term)
    | `(dim | #$n:num) => `(Dim.var $n)
    | `(dim | #($t:term)) => `(Dim.var $t)
    | `(dim | $n:num) => `(Dim.const $n)
    | _ => Lean.Macro.throwUnsupported

  macro_rules
  | `([ty| ($m:dim, $n:dim)])   => do
      let m ← expandDim m
      let n ← expandDim n
      `(type.base (TypeAtom.const (BaseType.arr $m $n)))
  | `([ty| ?$n:num])    => `(type.base (TypeAtom.var $n))
  | `([ty| ?($t:term)]) => `(type.base (TypeAtom.var $t))
  | `([ty| ~($t:term)]) => `($t)
  | `([ty| ($t)])       => `([ty| $t])
  | `([ty| $a -> $b])   => `(type.arrow [ty| $a] [ty| $b])

  #check [ty| (#0, #1) -> (#1, #2) -> (#0, #2)] -- matrix product
  #check [ty| (4, #0)]
  #check [ty| (2, 3)]
  #check [ty| ?0 -> ?1 -> ?0]
  #check [ty| ((#0, 3) -> (#0, 1)) -> ?2]
  -- #check [ty| (#())]

  /- Print types back in the `[ty| ...]` surface syntax rather than as raw
  constructors, so `#eval` output is readable. Parenthesise the left side of an
  arrow only, since `->` is right assoc. -/
  instance (n: Nat) : OfNat Dim n where
    ofNat := Dim.const n
  instance : ToString Dim where
    toString := λ d : Dim => match d with
    | .var n => "#" ++ (toString n)
    | .const n => toString n
  -- instance : ToString BaseType where
  --   toString
  --     | BaseType.arr m n => s!"({m}, {n})"

  instance : ToString BaseType where
    toString
      | BaseType.arr m n => s!"({m}, {n})"

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

  #eval [ty| (#0, #1) -> (#1, #2) -> (#0, #2)] -- matrix product
  #eval [ty| (4, #0)]
  #eval [ty| (2, 3)]
  #eval [ty| ?0 -> ?1 -> ?0]
  #eval [ty| ((#0, 3) -> (#0, 1)) -> ?2]

    /- Surface syntax for type schemes: `[sch| forall ?0 ?1, ?0 -> ?1]`, or
  `[sch| nat -> bool]` for a monomorphic one (empty binder list). -/
  syntax "[sch| " "forall " (("?" num)*) (("#" num)*) ", " ty "]" : term
  syntax "[sch| " ty "]" : term

  macro_rules
  | `([sch| forall $[?$ns:num]* $[#$ms:num]*, $t]) =>
      `({ bound := ⟨[$[$ns],*], [$[$ms],*]⟩, body := [ty| $t] : TypeScheme })
  | `([sch| $t:ty])                   => `({ bound := Vars.empty, body := [ty| $t] : TypeScheme })

  /- Print schemes back in that syntax. Monomorphic schemes print as bare types,
  matching how OCaml hides the quantifier. -/
  def TypeScheme.toString (σ : TypeScheme) : String :=
  match σ.bound with
  | ⟨[], []⟩ => ToString.toString σ.body
  | ⟨ts, ds⟩ => "forall " ++ String.intercalate " " (ts.map (s!"?{·}")) ++ String.intercalate " " (ds.map (s!"#{·}"))  ++ ", " ++ ToString.toString σ.body

  instance : ToString TypeScheme := ⟨TypeScheme.toString⟩
  instance : Repr TypeScheme := ⟨fun σ _ => TypeScheme.toString σ⟩

  #eval [sch| forall ?0, ?0 -> ?0]              -- the identity function's scheme
  #eval [sch| forall ?0 ?1, ?0 -> ?1 -> ?0]     -- fun x y => x
  #eval [sch| (2, 2) -> ?3]                       -- monomorphic, bound = []
  #eval [sch| forall ?0, (4, 4)]                   -- representable but generalize won't build it
  #eval [sch| forall ?0 #0 #1, (4, 4) -> (#0, #1) -> ?0]

end open_type_syntax

def freshT : InferM Nat := do -- get a fresh unused type variable
  let (n, m) ← get
  set (n + 1, m)
  return n
def freshD : InferM Nat := do -- get a fresh unused dimension variable
  let (n, m) ← get
  set (n, m + 1)
  return m
def occurs (v : Nat) (e : OpenType) : Bool :=
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
def Env.free (Γ : Env) : Vars :=
  (Γ.domain.filterMap Γ.lookup).foldl (fun acc σ => acc.union σ.free) Vars.empty

-- initial environment with types of built-ins
abbrev initialEnv := Env.ofList [
  ("*", [sch| forall #0 #1 #2, (#0, #1) -> (#1, #2) -> (#0, #2)]),
  ("+", [sch| forall #0 #1, (#0, #1) -> (#0, #1) -> (#0, #1)]),
  ("I", [sch| forall #0 #1, (#0, #1)])
]
abbrev Env.extendInitial (Γ : Env) := initialEnv.union Γ


-- substitution {subst / var}, e.g. {int → int / 't}.
structure Subst where
  tys : List (Nat × OpenType) -- apply right to left
  dims : List (Nat × Dim)
deriving Nonempty
def Subst.singletonT (v : Nat) (t : OpenType) : Subst := Subst.mk [(v, t)] []
def Subst.singletonD (v : Nat) (d : Dim) : Subst := Subst.mk [] [(v, d)]
def Subst.empty : Subst := Subst.mk [] []
def Dim.subst (d : Dim) (S : Subst) : Dim :=
  match d with
  | .const _ => d
  | .var x => match S.dims.lookup x with
    | some d' => d'
    | none => d
def type.subst (t : OpenType) (S : Subst) : OpenType :=
  match t with
  | .base (.var x) => match S.tys.lookup x with
    | some t' => t'
    | none => t
  | .base (.const (.arr m n)) => .base (.const (.arr (m.subst S) (n.subst S))) -- dim subst
  | .arrow t1 t2 => type.arrow (t1.subst S) (t2.subst S)
def Subst.compose (S1 S2 : Subst) : Subst :=  -- apply S2 then S1
  { tys := S1.tys.map (λ (x, t) => (x, t.subst S2)) ++ S2.tys,  -- apply S2 into S1, so the composition is idempotent
    dims := S1.dims.map (λ (x, d) => (x, d.subst S2)) ++ S2.dims}
def Subst.restrict (S : Subst) (bound : Vars) : Subst := -- drop these vars
  { tys := S.tys.filter (λ (x, _) => !bound.tys.contains x),
    dims := S.dims.filter (λ (x, _) => !bound.dims.contains x)}
def TypeScheme.subst (σ : TypeScheme) (S : Subst) : TypeScheme :=
  { σ with body := σ.body.subst (S.restrict σ.bound) } --Subst should never overwrite a bound variable (generalize should prevent this too)
def Env.subst (Γ : Env) (S : Subst) : Env :=
  { Γ with lookup := λ name => (Γ.lookup name).map (·.subst S) }

#eval (Dim.const 3).subst (Subst.singletonD 3 8) -- should leave alone
#eval (Dim.var 3).subst (Subst.singletonD 3 8) -- should substitute
#eval (Dim.var 3).subst (Subst.singletonT 3 [ty| (2, 3)]) -- should leave alone

/- Constraint of equality between two types -/
abbrev Constraint := OpenType × OpenType
def Constraint.subst (c : Constraint) (S : Subst) : Constraint :=
  (c.1.subst S, c.2.subst S)
def substConstraints (C : List Constraint) (S : Subst) : List Constraint :=
  C.map (·.subst S)


/- unification: generating a substitution that solves constraints -/
def unifyDims (m1 m2 : Dim) : Error Subst :=
  match m1, m2 with
  | .var x, d | d, .var x => .ok (Subst.singletonD x d)
  | .const x, .const y => if x = y then .ok (Subst.empty) else throw ErrorT.fail
def unifyShapes (a b : BaseType) : Error Subst :=
  match a, b with
  | .arr m1 n1, .arr m2 n2 => do
    let S1 ← unifyDims m1 m2
    let S2 ← unifyDims n1 n2
    return Subst.compose S1 S2

-- return (the most general) substitution that unifies all constraints
partial def unify (C: List Constraint) : Error Subst :=
  match C with
  | [] => do return Subst.empty
  | (t1, t2) :: C' =>
    let bindVar (x : Nat) (t : OpenType) (C' : List Constraint): Error Subst :=
      if occurs x t then throw ErrorT.fail else do
        let S := Subst.singletonT x t
        let S' ← unify (substConstraints C' S)
        return Subst.compose S' S
    match t1, t2 with
    -- identical variables / identical constants: nothing to learn
    | .base (.var x), .base (.var y) =>
      if x = y then unify C' else bindVar x t2 C'
    | .base (.const a), .base (.const b) => do
      let S ← unifyShapes a b
      let S' ← unify (substConstraints C' S)
      return Subst.compose S' S
    -- a variable = anything else
    | .base (.var x), t | t, .base (.var x) => bindVar x t C'
    -- reduce
    | .arrow t1 t2, .arrow t3 t4 =>
      unify ((t1, t3) :: (t2, t4) :: C') -- push the two reduced constraints
    | _, _ => throw ErrorT.fail

-- replace all bound variables in a type scheme with fresh vars
def instantiate (σ : TypeScheme) : InferM OpenType := do
  let fresh_tys ← σ.bound.tys.mapM (λ a' => do
    let b' ← freshT
    return (a', type.base (TypeAtom.var b'))
  )
  let fresh_dims ← σ.bound.dims.mapM (λ m' => do
    let n' ← freshD
    return (m', Dim.var n')
  )
  let S := Subst.mk fresh_tys fresh_dims
  return σ.body.subst S

-- generalize [name] into a universally quantified variable, return the modified env
def generalize (C : List Constraint) (Γ : Env) (name : Var) (t : OpenType) : Error Env := do
  let S ← unify C -- might fail
  let u := t.subst S
  let Γ' := Γ.subst S
  let vars := u.Vars.removeAll Γ'.free
  let scheme := { bound := vars, body := u }
  let Γ'' := Γ'.update name scheme
  return Γ''


-- return both the type of the expression (variable) and a list of constraints
-- Γ |- e : t -| C, return t, C
def buildConstraints (e : Expr) (Γ : Env) : InferM (OpenType × List Constraint) :=
  match e with
  | .const c => do return (type.base (TypeAtom.const (getType c)), [])
  | .var x => match Γ.lookup x with
    | some σ => do
      let t ← instantiate σ
      return (t, [])
    | none => throw ErrorT.fail
  -- | .if_else e1 e2 e3 => do
  --   let t' ← fresh -- the final output type
  --   let (t1, C1 )← buildConstraints e1 Γ
  --   let (t2, C2) ← buildConstraints e2 Γ
  --   let (t3, C3) ← buildConstraints e3 Γ
  --   let C := [
  --     (t1, [ty| bool]),
  --     (t2, [ty| ?(t')]),
  --     (t3, [ty| ?(t')])
  --   ]
  --   return ([ty| ?(t')], C1 ++ C2 ++ C3 ++ C)
  | .lam name e => do
    let t' ← freshT
    let (t1, C) ← buildConstraints e (Γ.update name [ty| ?(t')])
    return ([ty| ?(t') -> ~(t1)], C)
  | .apply f inp => do
    let t' ← freshT
    let (t1, C1) ← buildConstraints f Γ
    let (t2, C2) ← buildConstraints inp Γ
    let C := [(t1, [ty| ~(t2) -> ?(t')])]
    return ([ty| ?(t')], C1 ++ C2 ++ C)
  | .let_in name e1 e2 => do
    let (t1, C1) ← buildConstraints e1 Γ
    let Γ' ← generalize C1 Γ name t1
    let (t2, C2) ← buildConstraints e2 Γ'
    return (t2, C1 ++ C2)

def runBuildConstraints (e : Expr) (Γ : Env := initialEnv) : Error (OpenType × List Constraint) :=
  (buildConstraints e Γ).run' (0, 0)


-- reduce open TVars like ?2 down to the lowest distinct naturals
def lowerVars (t : OpenType) : OpenType :=
  let rnT := t.Vars.tys.zipIdx
  let rnD := t.Vars.dims.zipIdx
  t.subst { tys := rnT.map (λ (x, y) => (x, [ty| ?(y)])), dims := rnD.map (λ (x, y) => (x, Dim.var y))}

#eval lowerVars [ty| ?2 -> ?3]
#eval lowerVars [ty| ?5 -> ?3 -> (#0, #4)]

-- top level function, returns the inferred type
def infer (e : Expr) (Γ : Env := initialEnv) : Error OpenType := do
  let (t', constraints)  ← runBuildConstraints e Γ
  let subst ← unify constraints
  let solved := t'.subst subst
  let lowered := lowerVars solved
  return lowered

section testing
  /- end to end tests -/

 def test_env := Env.extendInitial <| Env.ofList [
    -- square matrices
    ("x", [ty| (2, 2)]),
    ("y", [ty| (2, 2)]),
    ("z", [ty| (3, 3)]),
    -- rectangular, chosen so a*b*c chains: (2,3)(3,4)(4,5) = (2,5)
    ("a", [ty| (2, 3)]),
    ("b", [ty| (3, 4)]),
    ("c", [ty| (4, 5)]),
    ("r", [ty| (3, 2)]),
    -- function-typed bindings
    ("f",  [ty| (2, 2) -> (2, 2)]),
    ("h",  [ty| (2, 3) -> (3, 2)]),
    ("g",  [sch| forall #0 #1, (#0, #1) -> (#0, #1)]),   -- shape-preserving map
    ("tr", [sch| forall #0 #1, (#0, #1) -> (#1, #0)]),   -- transpose
  ]

  macro "#test " e:term " : " t:term : command => `(
    #eval (do
      let expected : Error OpenType := $t
      let actual := infer $e test_env
      if actual == expected then pure ()
      else throw (IO.userError s!"expected {repr expected}, got {repr actual}")
      : IO Unit)
  )

 /- ---------- basics: env lookup ---------- -/
  #test [lang| x] : (.ok [ty| (2, 2)])
  #test [lang| a] : (.ok [ty| (2, 3)])
  #test [lang| unbound_name] : fail

  /- ---------- addition: shapes must agree exactly ---------- -/
  #test [lang| x + y] : (.ok [ty| (2, 2)])
  #test [lang| x + z] : fail                    -- (2,2) vs (3,3)
  #test [lang| a + a] : (.ok [ty| (2, 3)])
  #test [lang| a + b] : fail                    -- (2,3) vs (3,4)
  #test [lang| a + r] : fail                    -- (2,3) vs (3,2): transposed, not equal
  #test [lang| x + y + x] : (.ok [ty| (2, 2)])  -- left assoc, all (2,2)
  #test [lang| x + (y + x)] : (.ok [ty| (2, 2)])

  /- ---------- matrix multiply: inner dimensions must match ---------- -/
  #test [lang| a * b] : (.ok [ty| (2, 4)])
  #test [lang| b * c] : (.ok [ty| (3, 5)])
  #test [lang| x * y] : (.ok [ty| (2, 2)])
  #test [lang| a * c] : fail        -- inner 3 vs 4
  #test [lang| a * a] : fail        -- inner 3 vs 2
  #test [lang| a * r] : (.ok [ty| (2, 2)])   -- (2,3)(3,2)
  #test [lang| r * a] : (.ok [ty| (3, 3)])   -- (3,2)(2,3)

  -- chained, left assoc: ((a*b)*c) : (2,3)(3,4)(4,5) = (2,5)
  #test [lang| a * b * c] : (.ok [ty| (2, 5)])
  -- explicit right nesting: same answer, different constraint order
  #test [lang| a * (b * c)] : (.ok [ty| (2, 5)])

  /- `+` and `*` are both precedence 65 and left assoc, so mixed expressions
  group strictly left to right: `a + b * c` is `(a + b) * c`, NOT `a + (b * c)`. -/
  #test [lang| x + y * z] : fail             -- (x+y):(2,2) times z:(3,3), inner 2 vs 3
  #test [lang| x + y * x] : (.ok [ty| (2, 2)])
  #test [lang| a * r + x] : (.ok [ty| (2, 2)])   -- (a*r):(2,2) plus x:(2,2)

  /- The worked example from HM-notes.md: `dot (dot A B) C` where B's shape is
  unknown. Inference must implicitly solve B : (3,4) from the surrounding
  constraints and return (2,5). Here B is a lambda-bound variable. -/
  #test [lang| fun bb => a * bb * c] : (.ok [ty| (3, 4) -> (2, 5)])

  /- ---------- polymorphic I : forall #0 #1, (#0, #1) ---------- -/
  #test [lang| I] : (.ok [ty| (#0, #1)])        -- stays fully polymorphic
  #test [lang| x + I] : (.ok [ty| (2, 2)])      -- I instantiates to (2,2)
  #test [lang| I + x] : (.ok [ty| (2, 2)])
  #test [lang| a + I] : (.ok [ty| (2, 3)])      -- I is not square-only
  #test [lang| a * I] : (.ok [ty| (2, #0)])  -- inner solved, outer free
  #test [lang| I * a] : (.ok [ty| (#0, 3)])
  #test [lang| I * I] : (.ok [ty| (#0, #1)])

  -- each *use* of I gets fresh dims, so two uses may take different shapes
  -- #test [lang| let i = I in a * i] : (.ok [ty| (2, #0)])


  -- each *use* of I gets fresh dims, so two uses may take different shapes
  -- #test [lang| let i = I in ~(mul [lang| a] [lang| i])] : (.ok [ty| (2, #0)])
  -- #test [lang| (x + I) + z] : fail              -- forces (2,2) then (3,3)

  /- ---------- lambdas and arrow types ---------- -/
  #test [lang| fun v => v] : (.ok [ty| ?0 -> ?0])
  #test [lang| fun v => v + x] : (.ok [ty| (2, 2) -> (2, 2)])
  #test [lang| fun v => v + a] : (.ok [ty| (2, 3) -> (2, 3)])
  -- #test [lang| fun v => v + I] : (.ok [ty| (#0, #1) -> (#0, #1)])
  #test [lang| fun v => fun w => v + w] : (.ok [ty| (#0, #1) -> (#0, #1) -> (#0, #1)])
  #test [lang| fun v => v * a] : (.ok [ty| (#0, 2) -> (#0, 3)])
  #test [lang| fun v => a * v] : (.ok [ty| (3, #0) -> (2, #0)])


  /- ---------- application of function-typed bindings ---------- -/
  #test [lang| f x] : (.ok [ty| (2, 2)])
  #test [lang| f z] : fail                      -- f wants (2,2)
  #test [lang| f (f x)] : (.ok [ty| (2, 2)])
  #test [lang| h a] : (.ok [ty| (3, 2)])
  #test [lang| h x] : fail
  #test [lang| g x] : (.ok [ty| (2, 2)])        -- g is shape-polymorphic
  #test [lang| g a] : (.ok [ty| (2, 3)])
  #test [lang| tr a] : (.ok [ty| (3, 2)])       -- transpose flips
  #test [lang| tr (tr a)] : (.ok [ty| (2, 3)])  -- involution
  #test [lang| a + (tr r)] : (.ok [ty| (2, 3)]) -- (3,2) transposed is (2,3)
  #test [lang| a + (tr a)] : fail               -- (2,3) vs (3,2)
  #test [lang| a * (tr a)] : (.ok [ty| (2, 2)])   -- A Aᵀ
  #test [lang| (tr a) * a] : (.ok [ty| (3, 3)])   -- Aᵀ A


  /- ---------- let-polymorphism over dimensions ----------
  The worked example at HM-notes.md:407. `let f = fun v => v + I in f` should
  generalize to a shape-preserving function, then be usable at a chosen shape. -/
  -- #test [lang| let ff = fun v => v + I in ff]
  --   : (.ok [ty| (#0, #1) -> (#0, #1)])
  -- #test [lang| let ff = fun v => v + I in ff x] : (.ok [ty| (2, 2)])
  -- #test [lang| let ff = fun v => v + I in ff a] : (.ok [ty| (2, 3)])
  -- -- the payoff: one binding used at two different shapes
  -- #test [lang| let ff = fun v => v + I in let p = ff x in ff a]
  --   : (.ok [ty| (2, 3)])
  -- monomorphic contrast: this one is pinned to (2,2) by x
  #test [lang| let ff = fun v => v + x in ff a] : fail

  #test [lang| let idm = fun v => v in idm x] : (.ok [ty| (2, 2)])
  #test [lang| let idm = fun v => v in idm] : (.ok [ty| ?0 -> ?0])
  #test [lang| let idm = fun v => v in let p = idm x in idm a]
    : (.ok [ty| (2, 3)])
  #test [lang| let idm = fun v => v in idm (idm a)] : (.ok [ty| (2, 3)])
  #test [lang| let idm = fun v => v in fun w => idm w] : (.ok [ty| ?0 -> ?0])

  /- ---------- generalization boundaries ----------
  lambda-bound variables must NOT be generalized, so a lambda-bound function
  used at two shapes must fail, while the let-bound version above succeeds. -/
  #test [lang| fun k => (k x) * (k a)] : fail
  -- variables free in the env must not be generalized
  #test [lang| fun w => let ff = fun v => w in ff x] : (.ok [ty| ?0 -> ?0])
  #test [lang| fun w => let ff = fun v => w in (ff x) + (ff a)]
    : (.ok [ty| (#0, #1) -> (#0, #1)])

  /- ---------- occurs check ---------- -/
  #test [lang| fun s => s s] : fail
  #test [lang| let w = fun s => s s in w] : fail

  /- ---------- nesting and shadowing ---------- -/
  #test [lang| let p = x in p] : (.ok [ty| (2, 2)])
  #test [lang| let p = x in let p = a in p] : (.ok [ty| (2, 3)])
  #test [lang| let p = x in let q = a in p + x] : (.ok [ty| (2, 2)])
  #test [lang| let idm = fun v => v in let id2 = idm in id2 a]
    : (.ok [ty| (2, 3)])
  #test [lang| let ff = fun v => v in let gg = fun w => ff w in gg a]
    : (.ok [ty| (2, 3)])
  #test [lang| let addx = fun v => v + x in addx (x + y)] : (.ok [ty| (2, 2)])

  /- ---------- lowerVars normalization ----------
  Open results must be renumbered from 0, regardless of how many fresh vars
  inference burned through internally. -/
  #test [lang| fun v => fun w => v] : (.ok [ty| ?0 -> ?1 -> ?0])
  #test [lang| fun v => fun w => w] : (.ok [ty| ?0 -> ?1 -> ?1])
  #test [lang| let kk = fun v => fun w => v in kk] : (.ok [ty| ?0 -> ?1 -> ?0])
  #test [lang| let kk = fun v => fun w => v in kk a x] : (.ok [ty| (2, 3)])
  #test [lang| let kk = fun v => fun w => v in kk x a] : (.ok [ty| (2, 2)])
  #test [lang| let ap = fun ff => fun v => ff v in ap] : (.ok [ty| (?0 -> ?1) -> ?0 -> ?1])
  #test [lang| let ap = fun ff => fun v => ff v in ap g a] : (.ok [ty| (2, 3)])

  /- ---------- blocked: `I2` literal syntax ----------
  These depend on the macro at line 68 actually building identity matrices.
  As written it matches the literal string "I$n", which no identifier equals,
  so `I2` becomes `Expr.var "I2"` and every one of these fails as unbound. -/
  #test [lang| I2] : (.ok [ty| (2, 2)])
  #test [lang| I2 + x] : (.ok [ty| (2, 2)])
  #test [lang| I3 + x] : fail
  #test [lang| let p = I2 + I3 in p] : fail
  #test (mul [lang| I2] [lang| I2]) : (.ok [ty| (2, 2)])

end testing
end hindley_milner
