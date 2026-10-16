import Dubon2026.OriginalIdeleSingleFiniteEquivariance

/-! # Lifting the original local H2 at a full-decomposition prime

The original single-coordinate coefficient section and group reindexing
give a section of actual idele localization. Full decomposition is the
proved prime-selection output, not a cohomological lifting assumption.
This is needed to realize the local full-order invariant in the original
idele-class H2 on DUB-17's reciprocity route.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L)) (hw : OriginalFiniteDecompositionGroup K L w = ⊤)

/-- At a full-decomposition prime, the original stabilizer inclusion is the actual Galois group equivalence. -/
def originalFullDecompositionEquiv : OriginalFiniteDecompositionGroup K L w ≃* Gal(L/K) where
  toFun := Subtype.val
  invFun σ := ⟨σ, by rw [hw]; exact Subgroup.mem_top σ⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Single-prime insertion is an original full Galois coefficient map when the decomposition group is full. -/
def originalFullDecompositionSingleRepHom :
    Rep.res (originalFullDecompositionEquiv K L w hw).symm.toMonoidHom
      (originalAdicUnitRep K L w) ⟶ originalFullIdeleRep K L :=
  Rep.ofHom ⟨(originalIdeleSingleFiniteHom L w).toAdditive.toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro u
    exact congrArg Additive.ofMul (originalIdeleSingleFinite_galois K L w
      ((originalFullDecompositionEquiv K L w hw).symm σ) u.toMul).symm⟩

/-- The original local cohomology class is reindexed along the full decomposition equivalence and inserted at its actual prime. -/
def originalFullDecompositionIdeleH2Lift :
    groupCohomology (originalAdicUnitRep K L w) 2 ⟶
      groupCohomology (originalFullIdeleRep K L) 2 :=
  (originalCohomologyReindex (originalAdicUnitRep K L w)
    (originalFullDecompositionEquiv K L w hw).symm 2).hom ≫
      (groupCohomology.functor ℤ Gal(L/K) 2).map
        (originalFullDecompositionSingleRepHom K L w hw)

/-- Actual localization of the lifted original local class is exactly that same local class. -/
theorem originalFullDecompositionIdeleH2Lift_section
    (x : groupCohomology (originalAdicUnitRep K L w) 2) :
    originalFullIdeleAdicH2 K L w (originalFullDecompositionIdeleH2Lift K L w hw x) = x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    simp only [originalFullIdeleAdicH2, originalFullDecompositionIdeleH2Lift,
      ModuleCat.comp_apply, originalCohomologyReindex, CategoryTheory.asIso_hom,
      groupCohomology.functor, groupCohomology.H2π_comp_map_apply]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext g
    exact congrArg Additive.ofMul (originalIdeleSingleFinite_same L w (c.val g).toMul)

/-- The lifted local class has zero actual localization at every other original finite prime. -/
theorem originalFullDecompositionIdeleH2Lift_other
    (v : HeightOneSpectrum (𝓞 L)) (hv : v ≠ w)
    (x : groupCohomology (originalAdicUnitRep K L w) 2) :
    originalFullIdeleAdicH2 K L v (originalFullDecompositionIdeleH2Lift K L w hw x) = 0 := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    simp only [originalFullIdeleAdicH2, originalFullDecompositionIdeleH2Lift,
      ModuleCat.comp_apply, originalCohomologyReindex, CategoryTheory.asIso_hom,
      groupCohomology.functor, groupCohomology.H2π_comp_map_apply]
    rw [← map_zero (groupCohomology.H2π (originalAdicUnitRep K L v)).hom]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext g
    exact congrArg Additive.ofMul (originalIdeleSingleFinite_ne L w v hv _)

end
end Dubon2026
