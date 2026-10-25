import Dubon2026.SourceResidueCoefficientPlaceOrders
import Dubon2026.SourceCurveDivisorDegree
import Dubon2026.SourceCurvePicardGroup
import Dubon2026.SourceModularCoefficientResidue

/-! DUB-17/18 -> original Frobenius/Picard comparison -> residue
divisor classes. The proved coefficient place permutation preserves degree
over the actual closed residue constants and sends a principal divisor to
the divisor of the coefficient transform. This adapts the existing original
divisor proof using the proved all-characteristic residue degree theorem. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) (K : Type*) [Field K]
local notation "FF" => modularFunctionFieldCoeff N K

/-- Pushforward of residue divisors under the genuine arithmetic place permutation. -/
def residueCoefficientDivisorEquiv (e : K ≃+* K) : Divisor K FF ≃+ Divisor K FF :=
  Finsupp.domCongr (residueCoefficientPlaceEquiv N K e)

theorem residueCoefficientDivisorEquiv_apply (e : K ≃+* K) (D : Divisor K FF)
    (v : Place K FF) :
    residueCoefficientDivisorEquiv N K e D (residueCoefficientPlace N K e v) = D v := by
  change Finsupp.equivMapDomain (residueCoefficientPlaceEquiv N K e) D
    (residueCoefficientPlaceEquiv N K e v) = D v
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

theorem residueCoefficientDivisor_degree [NeZero N] [IsAlgClosed K]
    (e : K ≃+* K) (D : Divisor K FF) :
    Divisor.degree (residueCoefficientDivisorEquiv N K e D) = Divisor.degree D := by
  have hr (v : Place K FF) : Module.finrank K v.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (coeff_place_residue_algebraMap_bijective N K v)
  induction D using Finsupp.induction with
  | zero => rw [map_zero, map_zero]
  | single_add v n D _ _ ih =>
    rw [map_add, map_add, map_add, ih]
    change Divisor.degree (Finsupp.equivMapDomain (residueCoefficientPlaceEquiv N K e)
      (Finsupp.single v n)) + _ = _
    rw [Finsupp.equivMapDomain_single, Divisor.degree_single, Divisor.degree_single, hr, hr]

theorem residueCoefficientDivisor_principal (e : K ≃+* K) (D : Divisor K FF)
    (hD : Divisor.IsPrincipal D) :
    Divisor.IsPrincipal (residueCoefficientDivisorEquiv N K e D) := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨residueCoefficientRingAut N K e f, (map_ne_zero _).mpr hf, fun w => ?_⟩
  obtain ⟨v, rfl⟩ := (residueCoefficientPlaceEquiv N K e).surjective w
  change residueCoefficientDivisorEquiv N K e D (residueCoefficientPlace N K e v) =
    (residueCoefficientPlace N K e v).ord (residueCoefficientRingAut N K e f)
  rw [residueCoefficientDivisorEquiv_apply, residueCoefficientPlace_ord_action]
  exact hD v

end
end Dubon2026.SourceFunctionField
