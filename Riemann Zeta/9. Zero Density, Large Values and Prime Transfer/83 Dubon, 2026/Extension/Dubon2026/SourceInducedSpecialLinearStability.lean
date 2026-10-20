import Dubon2026.SourceSpecialLinearGeneration
import Dubon2026.SourceInducedSquareZeroStability

/-! Full special-linear stability of the original induced coefficient Lie submodules.
The finite exponential supplies each actual elementary matrix. The adapted
field generation theorem supplies every determinant-one matrix. This removes
the special-linear group-stability premise in the DUB-17/18 coefficient chain.
General-linear stability and irreducibility remain separate obligations.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (K : Type u) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℤ)

/-- Every original induced Lie submodule is stable under every actual special-linear matrix. -/
theorem sourceInducedLieSubmodule_specialLinear_stable
    (W : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin n) K)
      (generalLinearIntegralInducedSubmodule K n lam))
    (g : SpecialLinearGroup (Fin n) K)
    (p : generalLinearIntegralInducedSubmodule K n lam) (hp : p ∈ W) :
    generalLinearIntegralInducedRepresentation K n lam (SpecialLinearGroup.toGL g) p ∈ W := by
  have h :
      ∀ g : SpecialLinearGroup (Fin n) K,
        ∀ q : generalLinearIntegralInducedSubmodule K n lam, q ∈ W →
          generalLinearIntegralInducedRepresentation K n lam (SpecialLinearGroup.toGL g) q ∈ W := by
    intro g
    apply sourceSL_transvection_induction _ _ _ _ g
    · intro q hq
      simpa using hq
    · intro i j hij t q hq
      let X := LieAlgebra.SpecialLinear.single i j hij (1 : K)
      have hX : X.val * X.val = 0 := by
        change Matrix.single i j (1 : K) * Matrix.single i j 1 = 0
        rw [Matrix.single_mul_single_of_ne (h := hij.symm)]
      have he : SpecialLinearGroup.toGL (sourceSLTransvection hij t) =
          sourceSquareZeroLine X.val hX t := by
        apply Units.ext
        change 1 + Matrix.single i j t = 1 + t • Matrix.single i j (1 : K)
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [he]
      exact sourceInducedLieSubmodule_squareZero_stable K n lam W X hX t q hq
    · intro g h hg hh q hq
      simpa only [map_mul, Module.End.mul_apply] using hg _ (hh q hq)
  exact h g p hp

/-- The actual source-induced coefficient module has invariant Lie complements stable under every original determinant-one matrix, with no supplied group-stability or complete-reducibility certificate. -/
theorem sourceInduced_exists_specialLinear_stable_complement {m : ℕ}
    (weight : Fin (m + 1) → ℤ)
    (W : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
      (generalLinearIntegralInducedSubmodule K (m + 1) weight)) :
    ∃ U : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
        (generalLinearIntegralInducedSubmodule K (m + 1) weight),
      IsCompl W U ∧
      ∀ (g : SpecialLinearGroup (Fin (m + 1)) K)
        (p : generalLinearIntegralInducedSubmodule K (m + 1) weight), p ∈ U →
          generalLinearIntegralInducedRepresentation K (m + 1) weight
            (SpecialLinearGroup.toGL g) p ∈ U := by
  obtain ⟨U, hU⟩ := sourceInducedSpecialLinear_exists_complement K weight W
  exact ⟨U, hU, sourceInducedLieSubmodule_specialLinear_stable K (m + 1) weight U⟩

end
end Dubon2026
