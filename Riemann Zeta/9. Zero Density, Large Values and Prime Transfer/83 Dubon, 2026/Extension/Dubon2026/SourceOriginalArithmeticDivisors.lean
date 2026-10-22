import Dubon2026.SourceOriginalArithmeticPlaces
import Dubon2026.SourceCurveDivisorDegree

/-! DUB-17/18 -> original modular Galois association -> arithmetic
divisor-class action. The genuine permutation of original places acts
additively on finite divisors, preserves degree over algebraically closed
constants, and carries the divisor of f to that of the actual coefficient
transform of f. These are precisely the relations needed to descend to
the original degree-zero divisor quotient.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) {L : Type*} [Field L] [Algebra ℚ L]
local notation "F" => modularFunctionFieldOver N L

/-- Pushforward of original divisors under the genuine arithmetic place permutation. -/
def originalArithmeticDivisorEquiv (σ : L ≃ₐ[ℚ] L) : Divisor L F ≃+ Divisor L F :=
  Finsupp.domCongr (originalArithmeticPlaceEquiv N σ)

theorem originalArithmeticDivisorEquiv_apply (σ : L ≃ₐ[ℚ] L) (D : Divisor L F)
    (v : Place L F) :
    originalArithmeticDivisorEquiv N σ D (originalArithmeticPlace N σ v) = D v := by
  change Finsupp.equivMapDomain (originalArithmeticPlaceEquiv N σ) D
    (originalArithmeticPlaceEquiv N σ v) = D v
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

theorem originalArithmeticDivisor_degree [NeZero N] [IsAlgClosed L]
    (σ : L ≃ₐ[ℚ] L) (D : Divisor L F) :
    Divisor.degree (originalArithmeticDivisorEquiv N σ D) = Divisor.degree D := by
  have hr (v : Place L F) : Module.finrank L v.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (original_place_residue_algebraMap_bijective N L v)
  induction D using Finsupp.induction with
  | zero => rw [map_zero, map_zero]
  | single_add v n D _ _ ih =>
    rw [map_add, map_add, map_add, ih]
    change Divisor.degree (Finsupp.equivMapDomain (originalArithmeticPlaceEquiv N σ)
      (Finsupp.single v n)) + _ = _
    rw [Finsupp.equivMapDomain_single, Divisor.degree_single, Divisor.degree_single, hr, hr]

theorem originalArithmeticDivisor_principal (σ : L ≃ₐ[ℚ] L) (D : Divisor L F)
    (hD : Divisor.IsPrincipal D) :
    Divisor.IsPrincipal (originalArithmeticDivisorEquiv N σ D) := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨originalArithmeticRingAut N σ f, (map_ne_zero _).mpr hf, fun w => ?_⟩
  obtain ⟨v, rfl⟩ := (originalArithmeticPlaceEquiv N σ).surjective w
  change originalArithmeticDivisorEquiv N σ D (originalArithmeticPlace N σ v) =
    (originalArithmeticPlace N σ v).ord (originalArithmeticRingAut N σ f)
  rw [originalArithmeticDivisorEquiv_apply, originalArithmeticPlace_ord_action]
  exact hD v

end
end Dubon2026.SourceFunctionField
