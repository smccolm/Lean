import Dubon2026.OriginalRelativeCoefficientFiberEquiv
import Mathlib.RingTheory.Kaehler.Basic

/-! # Genuine relative cotangent maps and original continuous dual-number coefficient points -/

namespace Dubon2026

noncomputable section

variable {O R : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]

/-- The actual relative cotangent maps to the original residue point's genuine epsilon ideal, with its coefficient action given by the original constant residue lift. -/
abbrev OriginalResidueCotangentMaps
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :=
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  KaehlerDifferential O R →ₗ[R]
    (TrivSqZeroExt.kerIdeal (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O))

/-- Actual relative cotangent maps classify every original continuous residue-preserving dual-number coefficient point in the original maximal-adic topology. -/
def originalResidueCotangentContinuousFiberEquiv
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    OriginalResidueCotangentMaps eR ≃
      (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
         ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
       OriginalContinuousCoefficientFiber eR (relativeDualNumberResidueEquiv O)) := by
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  exact (KaehlerDifferential.linearMapEquivDerivation O R
    (M := TrivSqZeroExt.kerIdeal (IsLocalRing.ResidueField O)
      (IsLocalRing.ResidueField O))).toEquiv.trans
        (originalResidueDerivationContinuousFiberEquiv hR eR)

/-- Every genuine original continuous coefficient point comes uniquely from a linear map on the actual relative Kaehler differential module. -/
theorem originalResidueCotangentContinuousFiberEquiv_bijective
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    Function.Bijective (originalResidueCotangentContinuousFiberEquiv hR eR) :=
  (originalResidueCotangentContinuousFiberEquiv hR eR).bijective

/-- The original cotangent map evaluates a relative dual-number point by its genuine universal differential and the same original constant residue value. -/
theorem originalResidueCotangentContinuousFiberEquiv_apply
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (d : OriginalResidueCotangentMaps eR) (r : R) :
    (originalResidueCotangentContinuousFiberEquiv hR eR d).val r =
      (d (KaehlerDifferential.D O R r) : DualNumber (IsLocalRing.ResidueField O)) +
        originalResidueConstantDualLift eR r := rfl

end
end Dubon2026
