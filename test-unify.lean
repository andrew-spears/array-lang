import HM
/- Test cases for unify. `unify` is `partial`, so it has no equation lemmas and
won't reduce with `decide`/`rfl`; `native_decide` compiles and runs it instead. -/

-- trivial
example : (unify [] == .ok []) = true := by native_decide
example : (unify [([ty| nat], [ty| nat])] == .ok []) = true := by native_decide          -- nothing to learn
example : (unify [([ty| ?0], [ty| ?0])] == .ok []) = true := by native_decide            -- same var

-- immediate failures
example : (unify [([ty| nat], [ty| bool])] == .error .fail) = true := by native_decide          -- distinct constants
example : (unify [([ty| nat], [ty| nat -> nat])] == .error .fail) = true := by native_decide    -- base vs arrow
example : (unify [([ty| ?0], [ty| ?0 -> nat])] == .error .fail) = true := by native_decide      -- occurs check

-- single substitutions
example : (unify [([ty| ?0], [ty| nat])] == .ok [⟨[ty| nat], 0⟩]) = true := by native_decide
example : (unify [([ty| nat -> nat], [ty| ?0])] == .ok [⟨[ty| nat -> nat], 0⟩]) = true := by native_decide  -- var on the right
example : (unify [([ty| ?0], [ty| ?1])] == .ok [⟨[ty| ?1], 0⟩]) = true := by native_decide                  -- var to var

-- structural decomposition
example : (unify [([ty| ?0 -> ?1], [ty| nat -> bool])] == .ok [⟨[ty| nat], 0⟩, ⟨[ty| bool], 1⟩]) = true := by native_decide
example : (unify [([ty| ?0 -> ?0], [ty| nat -> bool])] == .error .fail) = true := by native_decide                            -- ?0 can't be both

-- substitution must propagate into later constraints
example : (unify [([ty| ?0], [ty| nat]), ([ty| ?0], [ty| bool])] == .error .fail) = true := by native_decide                            -- fails only if subst propagates
example : (unify [([ty| ?0], [ty| ?1]), ([ty| ?1], [ty| nat])] == .ok [⟨[ty| ?1], 0⟩, ⟨[ty| nat], 1⟩]) = true := by native_decide     -- chain: both end up nat
example : (unify [([ty| ?0 -> ?1], [ty| ?1 -> nat])] == .ok [⟨[ty| ?1], 0⟩, ⟨[ty| nat], 1⟩]) = true := by native_decide     -- needs propagation

-- from `3 + x`
example : (unify [([ty| nat -> nat -> nat], [ty| nat -> ?1]), ([ty| ?1], [ty| nat -> ?0])] == .ok [⟨[ty| nat -> nat], 1⟩, ⟨[ty| nat], 0⟩]) = true := by native_decide

-- from the notes: 'x -> ('x -> int) = int -> 'y,  'x -> 'x = 'y
example : (unify [([ty| ?0 -> (?0 -> nat)], [ty| nat -> ?1]), ([ty| ?0 -> ?0], [ty| ?1])] == .ok [⟨[ty| nat], 0⟩, ⟨[ty| nat -> nat], 1⟩]) = true := by native_decide

-- nested, deeper occurs check
example : (unify [([ty| ?0], [ty| (nat -> ?0) -> bool])] == .error .fail) = true := by native_decide
