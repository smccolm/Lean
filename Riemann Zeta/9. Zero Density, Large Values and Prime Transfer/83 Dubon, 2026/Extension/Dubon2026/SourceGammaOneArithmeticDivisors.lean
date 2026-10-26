import Dubon2026.SourceGammaOneArithmeticPlaces
import Dubon2026.SourceCurveDivisorDegree
import Dubon2026.SourceCurvePicardGroup
import Dubon2026.SourceCurveFiniteCoordinateResidues

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> genuine arithmetic Picard action. Existing finite-coordinate
closed residues and the actual place permutation prove preservation of
degree and principal divisors. Both Gamma1 and its Hecke subgroup satisfy
the translation/finite-index conditions in the final consumer. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) {L : Type*} [Field L] [Algebra ℚ L]
local notation "F" => functionFieldOver Γ L

theorem functionFieldOver_residue_bijective [Γ.FiniteIndex] [IsAlgClosed L]
    (hT : ModularGroup.T ∈ Γ) (v : Place L F) :
    Function.Bijective (algebraMap L v.ResidueField) := by
  haveI := finiteDimensional_jCoordinateOver hT L
  exact place_residue_bijective_of_finite_coordinate (jCoordinateOver Γ L) v

/-- Pushforward of original divisors under the genuine arithmetic place permutation. -/
def arithmeticDivisorEquiv (σ : L ≃ₐ[ℚ] L) : Divisor L F ≃+ Divisor L F :=
  Finsupp.domCongr (arithmeticPlaceEquiv Γ σ)

theorem arithmeticDivisorEquiv_apply (σ : L ≃ₐ[ℚ] L) (D : Divisor L F)
    (v : Place L F) :
    arithmeticDivisorEquiv Γ σ D (arithmeticPlace Γ σ v) = D v := by
  change Finsupp.equivMapDomain (arithmeticPlaceEquiv Γ σ) D
    (arithmeticPlaceEquiv Γ σ v) = D v
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

theorem arithmeticDivisor_degree [Γ.FiniteIndex] [IsAlgClosed L]
    (hT : ModularGroup.T ∈ Γ)
    (σ : L ≃ₐ[ℚ] L) (D : Divisor L F) :
    Divisor.degree (arithmeticDivisorEquiv Γ σ D) = Divisor.degree D := by
  have hr (v : Place L F) : Module.finrank L v.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (functionFieldOver_residue_bijective Γ hT v)
  induction D using Finsupp.induction with
  | zero => rw [map_zero, map_zero]
  | single_add v n D _ _ ih =>
    rw [map_add, map_add, map_add, ih]
    change Divisor.degree (Finsupp.equivMapDomain (arithmeticPlaceEquiv Γ σ)
      (Finsupp.single v n)) + _ = _
    rw [Finsupp.equivMapDomain_single, Divisor.degree_single, Divisor.degree_single, hr, hr]

theorem arithmeticDivisor_principal (σ : L ≃ₐ[ℚ] L) (D : Divisor L F)
    (hD : Divisor.IsPrincipal D) :
    Divisor.IsPrincipal (arithmeticDivisorEquiv Γ σ D) := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨arithmeticRingAut Γ σ f, (map_ne_zero _).mpr hf, fun w => ?_⟩
  obtain ⟨v, rfl⟩ := (arithmeticPlaceEquiv Γ σ).surjective w
  change arithmeticDivisorEquiv Γ σ D (arithmeticPlace Γ σ v) =
    (arithmeticPlace Γ σ v).ord (arithmeticRingAut Γ σ f)
  rw [arithmeticDivisorEquiv_apply, arithmeticPlace_ord_action]
  exact hD v

end
end Dubon2026.SourceFunctionField.GammaOne
