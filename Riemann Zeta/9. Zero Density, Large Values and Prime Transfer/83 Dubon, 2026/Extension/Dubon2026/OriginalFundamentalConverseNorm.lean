import Dubon2026.OriginalDoubleShiftDivisibility
import Dubon2026.OriginalCoinducedNormPullback
import Dubon2026.OriginalIntegralInvariantNormCriterion
import Dubon2026.OriginalPGroupInternalHomAcyclicity
import Mathlib.RingTheory.Flat.TorsionFree

/-! # The actual finite fundamental-class converse norm criterion

Two original coinduced shifts turn the actual H2-map kernel into
integral invariant divisibility. The proved degree-zero criterion
constructs a norm there, and the genuine diagrams carry its witness
back to the original coefficient morphism. Subgroup H1/H2 vanishing
of the fundamental extension discharges the extension premises.
This is the finite converse criterion on DUB-17's class/Ext route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
variable {G : Type} [Group G] [Fintype G]
variable (M C : Rep.{0} ℤ G) [Module.Finite ℤ M] [Module.Projective ℤ M]
variable (φ : groupCohomology.cocycles₂ C)

/-- Full order and the actual fundamental extension's subgroup vanishing imply that every original lattice morphism with zero induced H2 map is a literal coefficient norm. -/
theorem originalFundamental_h2_zero_norm
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (ho : addOrderOf (groupCohomology.H2π C φ) = Fintype.card G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2))
    (χ : M ⟶ C) (hχ : (groupCohomology.functor ℤ G 2).map χ = 0) :
    ∃ η : M →ₗ[ℤ] C, originalCoefficientNormMorphism M C η = χ := by
  letI := originalCoinducedQuotient_finite M
  letI := originalCoinducedQuotient_torsionFree M
  letI := originalCoinducedQuotient_projective M
  letI := originalCoinducedQuotient_finite (originalCoinducedQuotient M)
  letI := originalCoinducedQuotient_torsionFree (originalCoinducedQuotient M)
  letI := originalCoinducedQuotient_projective (originalCoinducedQuotient M)
  obtain ⟨d, hd⟩ := originalCoinducedExtensionDiagram_exists M
    (Y := originalFundamentalSplittingShortComplex C φ)
    (originalPGroup_internalHom_positive_zero (originalCoinducedQuotient M)
      (originalFundamentalSplittingModule C φ) p hG h 0) χ
  have hreg : Limits.IsZero (groupCohomology
      ((Rep.ihom (originalCoinducedQuotient (originalCoinducedQuotient M))).obj
        (Rep.leftRegular ℤ G)) 1) :=
    (originalInternalHomCoinducedTarget_positive_zero
      (originalCoinducedQuotient (originalCoinducedQuotient M)) (Rep.trivial ℤ G ℤ) 0).of_iso
        ((groupCohomology.functor ℤ G 1).mapIso
          ((Rep.ihom (originalCoinducedQuotient (originalCoinducedQuotient M))).mapIso
            originalRegularCoinducedIso))
  obtain ⟨e, he⟩ := originalCoinducedExtensionDiagram_exists (originalCoinducedQuotient M)
    (Y := originalAugmentationShortComplex ℤ G) hreg d.τ₃
  have hf : (groupCohomology.functor ℤ G 2).map d.τ₁ = 0 :=
    (congrArg (groupCohomology.functor ℤ G 2).map hd).trans hχ
  obtain ⟨η, hη⟩ := originalIntegralInvariant_norm_of_divisibility
    (originalCoinducedQuotient (originalCoinducedQuotient M)) e.τ₃
    (originalDoubleShift_invariant_divisibility M C φ ho d e he hf)
  obtain ⟨ξ, hξ⟩ := originalCoinducedDiagram_norm_pullback (originalCoinducedQuotient M)
    (originalAugmentationShortComplex_shortExact ℤ G) e η hη
  obtain ⟨ζ, hζ⟩ := originalCoinducedDiagram_norm_pullback M
    (originalFundamentalSplittingShortComplex_shortExact C φ) d ξ (hξ.trans he)
  exact ⟨ζ, hζ.trans hd⟩

end
end Dubon2026
