import Dubon2026.SourceRegularLocalNilpotence
import Dubon2026.SourceStrictUpperLie
import Dubon2026.SourceInducedLieComplements
import Mathlib.Algebra.Lie.Engel
import Mathlib.RingTheory.Finiteness.Nilpotent

/-! Nonzero infinitesimal upper-unipotent invariants in actual source Lie submodules.
All nilpotence and finite-dimensionality premises are derived on the original
source module before applying pinned Mathlib's Engel theorem. Passing from infinitesimal
invariance to all-algebra unipotent invariance remains a separate bridge.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (K : Type u) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℤ)

omit [CharZero K] in
/-- Iterating the restricted strictly upper triangular action gives exactly the iterated original regular-function differential. -/
theorem sourceInduced_strictUpper_pow_val
    (W : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin n) K)
      (generalLinearIntegralInducedSubmodule K n lam))
    (X : sourceStrictUpperLie K n) (k : ℕ) (p : W) :
    (((LieModule.toEnd K (sourceStrictUpperLie K n) W X) ^ k) p).val.val =
      ((sourceRegularDifferential X.val.val).toLinearMap ^ k) p.val.val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
    change sourceRegularDifferential X.val.val
      ((((LieModule.toEnd K (sourceStrictUpperLie K n) W X) ^ k) p).val.val) =
        sourceRegularDifferential X.val.val
          (((sourceRegularDifferential X.val.val).toLinearMap ^ k) p.val.val)
    exact congrArg (sourceRegularDifferential X.val.val) ih

/-- Every original strictly upper triangular matrix acts nilpotently on every original induced Lie submodule; neither nilpotence nor finite dimension is supplied. -/
theorem sourceInduced_strictUpper_isNilpotent {m : ℕ}
    (weight : Fin (m + 1) → ℤ)
    (W : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
      (generalLinearIntegralInducedSubmodule K (m + 1) weight))
    (X : sourceStrictUpperLie K (m + 1)) :
    IsNilpotent (LieModule.toEnd K (sourceStrictUpperLie K (m + 1)) W X) := by
  apply Module.End.isNilpotent_iff_of_finite.mpr
  intro p
  have hx : IsNilpotent X.val.val := sourceStrictUpper_isNilpotent X.val.val X.property
  have ht : X.val.val.trace = 0 := X.val.property
  obtain ⟨k, hk⟩ := sourceRegularDifferential_locallyNilpotent X.val.val hx ht p.val.val
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  rw [sourceInduced_strictUpper_pow_val, hk]
  rfl

/-- Every nonzero original induced Lie submodule contains a nonzero vector annihilated by all original strictly upper triangular infinitesimal directions, over the original characteristic-zero field. -/
theorem sourceInduced_exists_nonzero_strictUpper_invariant {m : ℕ}
    (weight : Fin (m + 1) → ℤ)
    (W : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
      (generalLinearIntegralInducedSubmodule K (m + 1) weight)) [Nontrivial W] :
    ∃ p : generalLinearIntegralInducedSubmodule K (m + 1) weight,
      p ∈ W ∧ p ≠ 0 ∧
      ∀ X : sourceStrictUpperLie K (m + 1),
        sourceRegularDifferential X.val.val p.val = 0 := by
  let H := sourceStrictUpperLie K (m + 1)
  letI : LieModule.IsNilpotent H W :=
    (LieModule.isNilpotent_iff_forall' (R := K)).mpr
      (sourceInduced_strictUpper_isNilpotent K weight W)
  letI : Nontrivial (LieModule.maxTrivSubmodule K H W) :=
    LieModule.nontrivial_max_triv_of_isNilpotent K H W
  let zeroInvariant : LieModule.maxTrivSubmodule K H W :=
    ⟨0, fun X => lie_zero X⟩
  obtain ⟨v, hv⟩ := exists_ne zeroInvariant
  refine ⟨v.val.val, v.val.property, ?_, ?_⟩
  · intro he
    apply hv
    exact Subtype.ext (Subtype.ext he)
  · intro X
    have he : ⁅X, v.val⁆ = 0 := v.property X
    exact congrArg (fun q : W => q.val.val) he

end
end Dubon2026
