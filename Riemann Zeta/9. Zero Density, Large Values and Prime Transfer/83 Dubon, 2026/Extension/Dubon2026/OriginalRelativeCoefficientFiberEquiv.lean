import Dubon2026.OriginalCoefficientAutomaticContinuity
import Dubon2026.RelativeDualNumberDerivations
import Dubon2026.OriginalCoefficientFramedEquivalence

/-! # Actual algebraic and continuous relative dual-number coefficient fibers -/

namespace Dubon2026

noncomputable section

variable {O R : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]

/-- All genuine relative dual-number coefficient maps are automatically continuous in the original proved maximal-adic topology, and their ordinary reduction is the actual true residue reduction. -/
def originalRelativeContinuousCoefficientFiberEquiv
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    OriginalRelativeDualNumberFiber eR ≃
      (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
         ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
       OriginalContinuousCoefficientFiber eR (relativeDualNumberResidueEquiv O)) where
  toFun f := by
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
      ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    have hres : (localCoefficientReduction (relativeDualNumberResidueEquiv O)).comp f.val =
        localCoefficientReduction eR := by
      ext r
      exact (relativeDualNumberResidueEquiv_reduction O (f.val r)).trans
        (DFunLike.congr_fun f.property r)
    exact ⟨f.val, originalCoefficientMap_continuous_of_topology_eq hR rfl eR
      (relativeDualNumberResidueEquiv O) f.val hres, hres⟩
  invFun f := by
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
      ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    refine ⟨f.val, ?_⟩
    ext r
    exact (relativeDualNumberResidueEquiv_reduction O (f.val r)).symm.trans
      (DFunLike.congr_fun f.property.2 r)
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    rfl

/-- The actual original relative residue derivations classify all genuine continuous residual dual-number coefficient points. -/
def originalResidueDerivationContinuousFiberEquiv
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    OriginalResidueDerivations eR ≃
      (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
         ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
       OriginalContinuousCoefficientFiber eR (relativeDualNumberResidueEquiv O)) :=
  (originalResidueDerivationEquiv eR).trans (originalRelativeContinuousCoefficientFiberEquiv hR eR)

/-- Each original continuous relative dual-number coefficient point has a unique genuine relative residue derivation. -/
theorem originalResidueDerivationContinuousFiberEquiv_bijective
    (hR : (inferInstance : TopologicalSpace R) = (IsLocalRing.maximalIdeal R).adicTopology)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    Function.Bijective (originalResidueDerivationContinuousFiberEquiv hR eR) :=
  (originalResidueDerivationContinuousFiberEquiv hR eR).bijective

end
end Dubon2026
