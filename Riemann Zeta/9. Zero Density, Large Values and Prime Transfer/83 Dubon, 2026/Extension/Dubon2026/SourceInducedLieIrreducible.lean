import Dubon2026.SourceInducedUnipotentInvariant

/-! Irreducibility and highest-vector generation for the actual source Lie action.
Every nonzero Lie submodule contains the same actual highest vector. The
constructed Weyl complement therefore forces the submodule to be the whole
original induction. Recovery of group irreducibility and integral base change
remain separate source obligations.
-/

namespace Dubon2026
noncomputable section

universe u
variable (K : Type u) [Field K] [CharZero K]
variable {m : ℕ} (weight : Fin (m + 1) → ℤ) (hw : Antitone weight)

/-- Every nonzero original source Lie submodule contains the actual normalized highest vector. -/
theorem sourceInduced_highest_mem
    (W : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
      (generalLinearIntegralInducedSubmodule K (m + 1) weight))
    (hW : W ≠ ⊥) : integralDominantHighestVector K weight hw ∈ W := by
  letI : Nontrivial W := (LieSubmodule.nontrivial_iff_ne_bot K _ _).mpr hW
  obtain ⟨c, hc, hv⟩ := sourceInduced_exists_highest_multiple K weight hw W
  have h := W.smul_mem c⁻¹ hv
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h

include hw in
/-- The actual source special-linear Lie action is irreducible: every original invariant Lie submodule is zero or the entire original coefficient module. -/
theorem sourceInduced_lieSubmodule_eq_bot_or_top
    (W : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
      (generalLinearIntegralInducedSubmodule K (m + 1) weight)) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨U, hU⟩ := sourceInducedSpecialLinear_exists_complement K weight W
  by_cases hU0 : U = ⊥
  · exact eq_top_of_isCompl_bot (hU0 ▸ hU)
  have hvW := sourceInduced_highest_mem K weight hw W hW
  have hvU := sourceInduced_highest_mem K weight hw U hU0
  have hv : integralDominantHighestVector K weight hw ∈ W ⊓ U := ⟨hvW, hvU⟩
  rw [hU.inf_eq_bot, LieSubmodule.mem_bot] at hv
  exact (integralDominantHighestVector_ne_zero K weight hw hv).elim

/-- The actual highest vector generates the entire original induced coefficient module under its actual special-linear Lie action. -/
theorem sourceInduced_highest_lieSpan :
    LieSubmodule.lieSpan K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
      {integralDominantHighestVector K weight hw} = ⊤ := by
  have hmem : integralDominantHighestVector K weight hw ∈
      LieSubmodule.lieSpan K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
        {integralDominantHighestVector K weight hw} :=
    LieSubmodule.subset_lieSpan rfl
  rcases sourceInduced_lieSubmodule_eq_bot_or_top K weight hw
      (LieSubmodule.lieSpan K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
        {integralDominantHighestVector K weight hw}) with h | h
  · rw [h, LieSubmodule.mem_bot] at hmem
    exact (integralDominantHighestVector_ne_zero K weight hw hmem).elim
  · exact h

end
end Dubon2026
