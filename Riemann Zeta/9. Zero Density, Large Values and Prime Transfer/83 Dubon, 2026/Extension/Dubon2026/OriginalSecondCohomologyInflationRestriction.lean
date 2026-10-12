import Dubon2026.OriginalNormalSequenceCohomologyMaps

/-! # The actual second-degree inflation-restriction exact sequence -/

namespace Dubon2026
noncomputable section

open CategoryTheory CategoryTheory.Limits
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G]
  (A : Rep.{0} k G) (S : Subgroup G) [S.Normal]
  (hfirst : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1))

include hfirst in
/-- The original quotient inflation followed by original subgroup
restriction is zero in H2 when the original subgroup H1 vanishes. -/
theorem originalSecondCohomology_inflation_restriction_zero :
    groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2 ≫
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2 = 0 := by
  let d := groupCohomology.δ (originalCoinducedInvariantSequence_shortExact A S hfirst) 1 2 rfl
  haveI : IsIso d := originalCoinducedInvariantDimensionShift_isIso A S hfirst
  apply (cancel_epi d).mp
  erw [← Category.assoc, originalCoinduced_delta_inflation A S hfirst,
    Category.assoc, originalCoinduced_delta_restriction A S, ← Category.assoc]
  change ((groupCohomology.H1InfRes (originalCoinducedQuotient A) S).f ≫
    (groupCohomology.H1InfRes (originalCoinducedQuotient A) S).g) ≫ _ = _
  erw [(groupCohomology.H1InfRes (originalCoinducedQuotient A) S).zero, zero_comp, comp_zero]
  rfl

/-- The original H2 inflation and restriction maps form an actual short
complex, with the original normal quotient invariant coefficients. -/
def originalSecondCohomologyInfRes : ShortComplex (ModuleCat k) where
  X₁ := groupCohomology (A.quotientToInvariants S) 2
  X₂ := groupCohomology A 2
  X₃ := groupCohomology (Rep.res S.subtype A) 2
  f := groupCohomology.map (A := A.quotientToInvariants S) (B := A)
    (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2
  g := groupCohomology.map (A := A) (B := Rep.res S.subtype A)
    S.subtype (𝟙 (Rep.res S.subtype A)) 2
  zero := originalSecondCohomology_inflation_restriction_zero A S hfirst

/-- Actual second-degree inflation is injective, derived through
the actual dimension shifts and the original first-degree injection. -/
theorem originalSecondCohomology_inflation_mono :
    Mono (originalSecondCohomologyInfRes A S hfirst).f := by
  let eQ := @asIso _ _ _ _
    (groupCohomology.δ (originalCoinducedInvariantSequence_shortExact A S hfirst) 1 2 rfl)
    (originalCoinducedInvariantDimensionShift_isIso A S hfirst)
  let eG := @asIso _ _ _ _
    (groupCohomology.δ (originalCoinducedShortComplex_shortExact A) 1 2 rfl)
    (originalCoinducedGlobalDimensionShift_isIso A)
  let X := groupCohomology.H1InfRes (originalCoinducedQuotient A) S
  have hmap (z : X.X₁) :
      (originalSecondCohomologyInfRes A S hfirst).f (eQ.toLinearEquiv z) =
        eG.toLinearEquiv (X.f z) := by
    exact congrArg (fun f : X.X₁ ⟶ groupCohomology A 2 => f z)
      (originalCoinduced_delta_inflation A S hfirst)
  apply (ModuleCat.mono_iff_injective _).mpr
  intro x y hxy
  obtain ⟨u, rfl⟩ := eQ.toLinearEquiv.surjective x
  obtain ⟨v, rfl⟩ := eQ.toLinearEquiv.surjective y
  rw [hmap, hmap] at hxy
  have huv := (ModuleCat.mono_iff_injective X.f).mp inferInstance
    (eG.toLinearEquiv.injective hxy)
  exact congrArg eQ.toLinearEquiv huv

/-- The actual kernel of second-degree restriction is exactly the image
of original quotient inflation. This is proved from the original H1
inflation-restriction theorem and genuine natural dimension shifts. -/
theorem originalSecondCohomology_inflation_restriction_exact :
    (originalSecondCohomologyInfRes A S hfirst).Exact := by
  let eQ := @asIso _ _ _ _
    (groupCohomology.δ (originalCoinducedInvariantSequence_shortExact A S hfirst) 1 2 rfl)
    (originalCoinducedInvariantDimensionShift_isIso A S hfirst)
  let eG := @asIso _ _ _ _
    (groupCohomology.δ (originalCoinducedShortComplex_shortExact A) 1 2 rfl)
    (originalCoinducedGlobalDimensionShift_isIso A)
  let eS := @asIso _ _ _ _
    (groupCohomology.δ (originalCoinducedShortComplex_restrict_shortExact A S) 1 2 rfl)
    (originalCoinducedDimensionShift_isIso A S)
  let X := groupCohomology.H1InfRes (originalCoinducedQuotient A) S
  let Y := originalSecondCohomologyInfRes A S hfirst
  have hinf (z : X.X₁) : Y.f (eQ.toLinearEquiv z) = eG.toLinearEquiv (X.f z) := by
    exact congrArg (fun f : X.X₁ ⟶ groupCohomology A 2 => f z)
      (originalCoinduced_delta_inflation A S hfirst)
  have hres (z : X.X₂) : Y.g (eG.toLinearEquiv z) = eS.toLinearEquiv (X.g z) := by
    exact congrArg (fun f : X.X₂ ⟶ groupCohomology (Rep.res S.subtype A) 2 => f z)
      (originalCoinduced_delta_restriction A S)
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
  change Y.g x = 0 at hx
  obtain ⟨y, rfl⟩ := eG.toLinearEquiv.surjective x
  have hy : X.g y = 0 := by
    apply eS.toLinearEquiv.injective
    erw [map_zero, ← hres, hx]
    rfl
  have hex := (groupCohomology.H1InfRes_exact (originalCoinducedQuotient A) S).moduleCat_range_eq_ker
  have hy' : y ∈ X.f.hom.range := by rw [hex]; exact hy
  obtain ⟨z, hz⟩ := hy'
  refine ⟨eQ.toLinearEquiv z, ?_⟩
  exact (hinf z).trans (congrArg eG.toLinearEquiv hz)

end
end Dubon2026
