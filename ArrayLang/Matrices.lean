namespace Matrices

variable (T : Type) [Zero T] [HMul T T T] [HAdd T T T]

def sum (n : Nat) (f : Fin n → T) : T := Fin.foldr n (fun i acc => f i + acc) 0

/- Define matrices very abstractly as functions from indices
 to an element type. Matrices take two indices -/
def Matrix (m n : Nat) : Type := Fin m → Fin n → T

def identity (n : Nat) : Matrix Int n n := λ i j => if i = j then 1 else 0

/- Products -/
-- notation to allow writing A ⬝ B for all products, overloaded on types
class Dot (α : Type) (β : Type) (γ : outParam Type) where
  dot : α → β → γ
infixl:72 " ⬝ " => Dot.dot

def Matrix.mul {m n p} (A : Matrix T m n) (B : Matrix T n p) : Matrix T m p :=
    λ (i : Fin m) (k : Fin p) => sum T n (λ j => A i j * B j k)
instance {m n p} : Dot (Matrix T m n) (Matrix T n p) (Matrix T m p) := ⟨Matrix.mul T⟩

end Matrices
