import Dubon2026.OriginalFundamentalClassKilling
import Dubon2026.OriginalInvariantConnectingKernel

/-! # The actual double connecting map represents the original class

The identity point in the regular coefficient lifts the invariant
integer one. Its augmentation differences lift to the same explicit
cochain already used to kill the fundamental two-cocycle. The genuine
two connecting maps therefore return that original class, with its
sign fixed, on DUB-17's direct two-shift norm route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {G : Type} [Group G] (C : Rep.{0} ℤ G) (φ : groupCohomology.cocycles₂ C)

/-- The genuine augmentation and fundamental connecting maps send the invariant integer one to the original two-cocycle class. -/
theorem originalFundamental_double_connecting_one :
    (groupCohomology.δ (originalFundamentalSplittingShortComplex_shortExact C φ) 1 2 rfl)
      ((groupCohomology.δ (originalAugmentationShortComplex_shortExact ℤ G) 0 1 rfl)
        ((groupCohomology.H0Iso (Rep.trivial ℤ G ℤ)).inv ⟨1, fun _ => rfl⟩)) =
      groupCohomology.H2π C φ := by
  let e : Rep.leftRegular ℤ G := Finsupp.single 1 1
  have he : (originalAugmentation ℤ G).hom e = 1 := by
    exact Finsupp.linearCombination_single _ _ _
  have hd : (originalAugmentationInclusion ℤ G).hom ∘
      (fun g : G => originalAugmentationDifference (k := ℤ) g) =
      groupCohomology.d₀₁ (Rep.leftRegular ℤ G) e := by
    funext g
    rw [groupCohomology.d₀₁_hom_apply]
    change Finsupp.single g 1 - Finsupp.single 1 1 =
      Finsupp.lmapDomain ℤ ℤ (g * ·) (Finsupp.single 1 1) - Finsupp.single 1 1
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, mul_one]
  let z : groupCohomology.cocycles₁ (originalAugmentationIdeal ℤ G) :=
    ⟨_, groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁
      (originalAugmentationShortComplex_shortExact ℤ G) hd⟩
  have h0 := groupCohomology.δ₀_apply (originalAugmentationShortComplex_shortExact ℤ G)
    (⟨1, fun _ => rfl⟩ : (Rep.trivial ℤ G ℤ).ρ.invariants) e he
    (fun g : G => originalAugmentationDifference (k := ℤ) g) hd
  refine (congrArg (fun t : groupCohomology (originalAugmentationIdeal ℤ G) 1 =>
    (groupCohomology.δ (originalFundamentalSplittingShortComplex_shortExact C φ) 1 2 rfl) t)
      h0).trans ?_
  let y : G → originalFundamentalSplittingModule C φ :=
    fun g => (φ (g, 1), originalAugmentationDifference g)
  have hy : (originalFundamentalSplittingProjection C φ).hom ∘ y = z := rfl
  have hx : (originalFundamentalSplittingInclusion C φ).hom ∘ (φ : G × G → C) =
      groupCohomology.d₁₂ (originalFundamentalSplittingModule C φ) y := by
    funext p
    obtain ⟨g, h⟩ := p
    rw [groupCohomology.d₁₂_hom_apply]
    apply Prod.ext
    · change φ (g, h) = C.ρ g (φ (h, 1)) +
        originalFundamentalCocycleTwist C φ g (Finsupp.single h 1 - Finsupp.single 1 1) -
          φ (g * h, 1) + φ (g, 1)
      rw [map_sub, originalFundamentalCocycleTwist_single,
        originalFundamentalCocycleTwist_single]
      erw [one_smul, one_smul]
      rw [originalFundamentalCocycle_one_right_action]
      abel
    · exact (originalAugmentationDifference_cocycle g h).symm
  exact groupCohomology.δ₁_apply (originalFundamentalSplittingShortComplex_shortExact C φ)
    z y hy φ hx

/-- The actual two connecting homomorphisms on the invariant integer coefficient. -/
def originalFundamentalDoubleConnectingMap : ℤ →ₗ[ℤ] groupCohomology C 2 :=
  (groupCohomology.δ (originalFundamentalSplittingShortComplex_shortExact C φ) 1 2 rfl).hom.comp
    ((groupCohomology.δ (originalAugmentationShortComplex_shortExact ℤ G) 0 1 rfl).hom.comp
      (groupCohomology.H0IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv.hom)

/-- The actual double connecting map is integral multiplication by the original fundamental class. -/
theorem originalFundamentalDoubleConnectingMap_apply (z : ℤ) :
    originalFundamentalDoubleConnectingMap C φ z = z • groupCohomology.H2π C φ := by
  have h1 : originalFundamentalDoubleConnectingMap C φ 1 = groupCohomology.H2π C φ :=
    originalFundamental_double_connecting_one C φ
  have hz := map_zsmul (originalFundamentalDoubleConnectingMap C φ).toAddMonoidHom z (1 : ℤ)
  simp only [zsmul_eq_mul, mul_one] at hz
  exact hz.trans (congrArg (fun x => z • x) h1)

/-- Full additive order of the actual fundamental class makes the double connecting kernel exactly group-order divisibility. -/
theorem originalFundamentalDoubleConnectingMap_zero_iff [Fintype G]
    (ho : addOrderOf (groupCohomology.H2π C φ) = Fintype.card G) (z : ℤ) :
    originalFundamentalDoubleConnectingMap C φ z = 0 ↔ (Fintype.card G : ℤ) ∣ z := by
  rw [originalFundamentalDoubleConnectingMap_apply, ← ho]
  exact addOrderOf_dvd_iff_zsmul_eq_zero.symm

end
end Dubon2026
