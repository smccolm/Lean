import Dubon2026.SourceAllAlgebraUnipotentInvariant
import Dubon2026.SourceInducedEngelInvariant
import Dubon2026.IntegralUnipotentLine

/-! Actual nonzero unipotent invariants in original source Lie submodules.
The constructed Engel invariant satisfies every coefficient-algebra
quantifier required by the proved original highest-line uniqueness theorem.
-/

namespace Dubon2026
noncomputable section

universe u
variable (K : Type u) [Field K] [CharZero K]

/-- Every nonzero original induced Lie submodule contains a nonzero vector satisfying the original all-algebra upper-unipotent invariance contract. -/
theorem sourceInduced_exists_nonzero_unipotent_invariant {m : ℕ}
    (weight : Fin (m + 1) → ℤ)
    (W : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
      (generalLinearIntegralInducedSubmodule K (m + 1) weight)) [Nontrivial W] :
    ∃ p : generalLinearIntegralInducedSubmodule K (m + 1) weight,
      p ∈ W ∧ p ≠ 0 ∧
      ∀ (A : Type u) [CommRing A] [Algebra K A]
        (g : Matrix.GeneralLinearGroup (Fin (m + 1)) A) (b : generalLinearBorel A (m + 1)),
        (∀ i, generalLinearBorelDiagonalUnit b i = 1) →
          generalLinearRegularEval (g * b.val) p.val = generalLinearRegularEval g p.val := by
  obtain ⟨p, hp, hp0, hpi⟩ := sourceInduced_exists_nonzero_strictUpper_invariant K weight W
  exact ⟨p, hp, hp0, fun A _ _ g b hb => sourceUnipotent_allAlgebra_invariant p.val hpi g b hb⟩

/-- Every nonzero original induced Lie submodule for a dominant source weight contains a nonzero scalar multiple of the actual original highest vector. -/
theorem sourceInduced_exists_highest_multiple {m : ℕ}
    (weight : Fin (m + 1) → ℤ) (hw : Antitone weight)
    (W : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
      (generalLinearIntegralInducedSubmodule K (m + 1) weight)) [Nontrivial W] :
    ∃ c : K, c ≠ 0 ∧ c • integralDominantHighestVector K weight hw ∈ W := by
  obtain ⟨p, hp, hp0, hpu⟩ := sourceInduced_exists_nonzero_unipotent_invariant K weight W
  have he := integralInduced_unipotent_eq_highest K weight hw p hpu
  refine ⟨generalLinearRegularEval (integralWeightLongest K (m + 1)) p.val, ?_, he ▸ hp⟩
  intro hc
  rw [hc, zero_smul] at he
  exact hp0 he

end
end Dubon2026
