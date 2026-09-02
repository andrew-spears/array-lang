inductive Ty (baseType : Type) where
| arrow : Ty baseType → Ty baseType → Ty baseType
| base : baseType → Ty baseType

inductive ConstBase (dimType : Type) where
| arr (m n : dimType)

inductive VarDim where
| const : Nat → VarDim
| var

inductive VarBase (constBase : Type) where
| const : constBase → VarBase constBase
| var

-- things of Type : Ty (VarBase (ConstBase Nat)) OR Ty (VarBase (ConstBase VarDim))
abbrev OpenType := Ty (VarBase (ConstBase Nat)) ⊕ Ty (VarBase (ConstBase VarDim))

#check (.inr (Ty.base (VarBase.var)) : OpenType)
#check (.inl (Ty.base (VarBase.const (ConstBase.arr 2 3))) : OpenType)
#check (.inr (Ty.base (VarBase.const (ConstBase.arr (VarDim.const 2) (VarDim.var)))) : OpenType)

abbrev OpenType2 {D : Type} := Ty (VarBase (ConstBase D))

#check (Ty.base (VarBase.var) : OpenType2 )
#check (Ty.base (VarBase.const (ConstBase.arr 2 3)) : OpenType2)
#check (.inr (Ty.base (VarBase.const (ConstBase.arr (VarDim.const 2) (VarDim.var)))) : OpenType2)








-- #check Ty (ConstBase Nat)
-- #check Ty (VarBase (ConstBase Nat))

-- #check Ty.base VarBase.var
-- #check Ty.base (VarBase.const (ConstBase.arr VarDim.var VarDim.var)) -- a variable node with variable dims
-- #check Ty.base (VarBase.const (ConstBase.arr VarDim.var (VarDim.const 3)))

-- #check Ty.base (VarBase.const (ConstBase.arr 2 3))
-- #check Ty.base (ConstBase.arr 2 3) -- a true constant base
