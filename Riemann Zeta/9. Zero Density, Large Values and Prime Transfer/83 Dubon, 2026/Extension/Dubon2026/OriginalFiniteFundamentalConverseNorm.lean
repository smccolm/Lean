import Dubon2026.OriginalFiniteInternalHomFirstVanishing
import Dubon2026.OriginalFundamentalConverseNorm

/-! # The literal converse norm criterion for arbitrary finite groups

The constructed arithmetic enlargement on DUB-17's relation-extension
chain need not have p-group Galois group. The existing two-shift proof
requires only one internal-Hom H1 vanishing statement. The actual Sylow
comparison supplies that statement, removing the p-group assumption
without adding a replacement norm or duality certificate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
variable {G : Type} [Group G] [Fintype G]
variable (M C : Rep.{0} ℤ G) [Module.Finite ℤ M] [Module.Projective ℤ M]
variable (φ : groupCohomology.cocycles₂ C)

/-- For any finite group, full fundamental order and actual subgroup
H1/H2 vanishing turn a zero induced H2 map into a literal norm witness. -/
theorem originalFiniteFundamental_h2_zero_norm
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
    (originalFinite_internalHom_first_zero (originalCoinducedQuotient M)
      (originalFundamentalSplittingModule C φ) h) χ
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
