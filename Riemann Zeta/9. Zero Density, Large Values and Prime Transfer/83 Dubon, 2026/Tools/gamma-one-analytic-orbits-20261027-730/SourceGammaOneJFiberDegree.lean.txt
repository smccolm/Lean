import Dubon2026.SourceGammaOneAnalyticResidues
import Dubon2026.SourceCurveTranscendentalDegree

/-! DUB-17/18 -> actual Gamma1 global charts -> exact elliptic ramification.
Every finite actual j fiber has the same total order, namely the finite
degree over the actual j coordinate. Reuse the existing positive-order
sum and actual residue-field bijectivity; no exact degree is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve IntermediateField
open scoped IntermediateField

theorem sum_j_fiber_orders_eq_finrank
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) (c : ℂ) :
    (∑ᶠ v : {v : Place ℂ (functionFieldOver Γ ℂ) //
        0 < v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c)},
      v.1.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c)) =
        (Module.finrank ℂ⟮jCoordinateOver Γ ℂ⟯ (functionFieldOver Γ ℂ) : ℤ) := by
  have ht : Transcendental ℂ
      (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c) := by
    intro h
    apply transcendental_jCoordinateOver Γ ℂ
    simpa only [sub_add_cancel] using h.add (isAlgebraic_algebraMap c)
  have he : ℂ⟮jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c⟯ =
      ℂ⟮jCoordinateOver Γ ℂ⟯ := by
    apply le_antisymm
    · exact adjoin_simple_le_iff.mpr
        (ℂ⟮jCoordinateOver Γ ℂ⟯.sub_mem (mem_adjoin_simple_self _ _)
          (ℂ⟮jCoordinateOver Γ ℂ⟯.algebraMap_mem c))
    · apply adjoin_simple_le_iff.mpr
      have h := (ℂ⟮jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c⟯).add_mem
        (mem_adjoin_simple_self _ _) (IntermediateField.algebraMap_mem _ c)
      simpa only [sub_add_cancel] using h
  haveI : FiniteDimensional
      ℂ⟮jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c⟯
      (functionFieldOver Γ ℂ) := by
    rw [he]
    exact finiteDimensional_jCoordinateOver hT ℂ
  have h := sum_positive_orders_eq_finrank_adjoin _ ht
  have hr : ∀ v : Place ℂ (functionFieldOver Γ ℂ), Module.finrank ℂ v.ResidueField = 1 :=
    fun v => Module.finrank_of_bijective_algebraMap (place_residue_bijective hT v)
  simp only [hr, Nat.cast_one, mul_one] at h
  rwa [he] at h

end
end Dubon2026.SourceFunctionField.GammaOne
