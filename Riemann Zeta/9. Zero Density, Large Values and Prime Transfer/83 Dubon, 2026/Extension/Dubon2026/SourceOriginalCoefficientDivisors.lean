import Dubon2026.SourceOriginalCoefficientPlaceAction
import Dubon2026.SourceCurvePrincipalDivisorTransport
import Dubon2026.SourceOriginalArithmeticPicard
import Dubon2026.SourceModularCoefficientCurve

/-! DUB-17/18 -> original Picard inertia -> transfer of the actual
reduction to original divisor classes. The proved field identification
permutes genuine places, preserves degrees and preserves and reflects
principal divisors. Existing order transport and closed residue fields
discharge these obligations; no new divisor or Picard model is introduced. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ)
local notation "Fo" => modularFunctionFieldOver N Qbar
local notation "F" => modularFunctionFieldCoeff N Qbar

/-- Literal transport of finite divisors through the identical modular fields. -/
def originalCoefficientDivisorEquiv : Divisor Qbar Fo ≃+ Divisor Qbar F :=
  Finsupp.domCongr (originalCoefficientPlaceEquiv N)

theorem originalCoefficientDivisorEquiv_apply (D : Divisor Qbar Fo) (P : Place Qbar Fo) :
    originalCoefficientDivisorEquiv N D (originalCoefficientPlaceEquiv N P) = D P := by
  change Finsupp.equivMapDomain (originalCoefficientPlaceEquiv N) D
    (originalCoefficientPlaceEquiv N P) = D P
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

theorem originalCoefficientDivisor_degree [NeZero N] (D : Divisor Qbar Fo) :
    Divisor.degree (originalCoefficientDivisorEquiv N D) = Divisor.degree D := by
  letI : FiniteDimensional (IntermediateField.adjoin Qbar {jCoeff N Qbar}) F :=
    finiteDimensional_coeff_field N Qbar
  exact degree_divisorTransform (originalCoefficientEquiv N) D
    (original_place_residue_algebraMap_bijective N Qbar)
    (place_residue_bijective_of_finite_coordinate (jCoeff N Qbar))

theorem originalCoefficientDivisor_principal_iff (D : Divisor Qbar Fo) :
    Divisor.IsPrincipal (originalCoefficientDivisorEquiv N D) ↔ Divisor.IsPrincipal D := by
  constructor
  · rintro ⟨f, hf, hD⟩
    refine ⟨(originalCoefficientEquiv N).symm f, (map_ne_zero _).mpr hf, fun P => ?_⟩
    have h := hD (originalCoefficientPlaceEquiv N P)
    rw [originalCoefficientDivisorEquiv_apply] at h
    exact h.trans (P.ord_comapEquiv (originalCoefficientEquiv N).symm f)
  · rintro ⟨f, hf, hD⟩
    refine ⟨originalCoefficientEquiv N f, (map_ne_zero _).mpr hf, ?_⟩
    exact divisorTransform_orders (originalCoefficientEquiv N) hD

end
end Dubon2026.SourceFunctionField.GaussReduction
