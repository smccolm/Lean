import Dubon2026.OriginalFundamentalHomologyWitness

/-! # Independence of the actual fundamental norm-lift choices

The abelian norm-index route for DUB-17 requires a well-defined map
from original morphism norm classes to actual homology. Injective norm
on the actual middle coinvariants and the genuine augmentation boundary
prove that every permitted middle lift gives the same homology class.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- The original fundamental homology witness is independent of its actual middle norm lift. -/
theorem originalFundamentalHomologyWitness_unique
    {G : Type} [Group G] [Fintype G] (M C : Rep.{0} ℤ G)
    [Module.Projective ℤ M] (φ : groupCohomology.cocycles₂ C)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology
        (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
      Limits.IsZero (groupCohomology
        (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2))
    (χ : M ⟶ C)
    {y z : groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1}
    (hy : OriginalFundamentalHomologyWitness M C φ χ y)
    (hz : OriginalFundamentalHomologyWitness M C φ χ z) : y = z := by
  obtain ⟨b, hb, hby⟩ := hy
  obtain ⟨c, hc, hcz⟩ := hz
  let B := (Rep.ihom M).obj (originalFundamentalSplittingModule C φ)
  let I := (Rep.ihom M).obj (originalAugmentationIdeal ℤ G)
  let π : B ⟶ I := (Rep.ihom M).map (originalFundamentalSplittingProjection C φ)
  have hN : B.ρ.norm (b - c) = 0 := by
    rw [map_sub, hb, hc, sub_self]
  have hinj := (originalPGroup_internalHom_norm_homology M
    (originalFundamentalSplittingModule C φ) p hG h).1
  have hd := congrArg (Representation.Coinvariants.map B.ρ I.ρ π.hom) (hinj _ hN)
  rw [Representation.Coinvariants.map_mk, map_zero] at hd
  have he : Representation.Coinvariants.mk I.ρ (π.hom b) =
      Representation.Coinvariants.mk I.ρ (π.hom c) := by
    apply sub_eq_zero.mp
    simpa only [map_sub] using hd
  have hfirst := (originalPGroup_regularInternalHom_norm_homology M p hG).2
  have hm : Mono (groupHomology.δ
      (originalAugmentationInternalHomSequence_shortExact M) 1 0 rfl) :=
    groupHomology.mono_δ_of_isZero (originalAugmentationInternalHomSequence_shortExact M) 0 hfirst
  apply (ModuleCat.mono_iff_injective _).mp hm
  apply (groupHomology.H0Iso I).toLinearEquiv.injective
  exact hby.trans (he.trans hcz.symm)

end
end Dubon2026
