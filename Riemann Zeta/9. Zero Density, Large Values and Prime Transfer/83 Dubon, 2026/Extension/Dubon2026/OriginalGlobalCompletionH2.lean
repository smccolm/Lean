import Dubon2026.OriginalGlobalAdicH2

/-! # Original global H2 localized in the actual completion Galois group

The inverse of the proved original decomposition/Galois equivalence gives
literal restriction to the original number field. Its coefficient map is
the original field-to-completion embedding. Comparison with the already
proved decomposition-group localization connects finite local killing to
global odd-primary detection, on DUB-17's invariant sum-zero dependency.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
attribute [-instance] UniformSpace.Completion.instSMul
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- Restriction from the actual completion Galois group to the original global Galois group. -/
def originalCompletionGaloisRestriction :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    Gal(w.adicCompletion L/v.adicCompletion K) →* Gal(L/K) :=
  (OriginalFiniteDecompositionGroup K L w).subtype.comp
    (originalAdicDecompositionGaloisEquiv K L v w).symm.toMonoidHom

/-- Actual completion restriction preserves the literal embedding of every original field element. -/
theorem originalCompletionGaloisRestriction_commutes :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∀ (σ : Gal(w.adicCompletion L/v.adicCompletion K)) (x : L),
      algebraMap L (w.adicCompletion L) (originalCompletionGaloisRestriction K L v w σ x) =
        σ (algebraMap L (w.adicCompletion L) x) := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  intro σ x
  obtain ⟨τ, rfl⟩ := (originalAdicDecompositionGaloisEquiv K L v w).surjective σ
  change algebraMap L (w.adicCompletion L)
    (((originalAdicDecompositionGaloisEquiv K L v w).symm
      (originalAdicDecompositionGaloisEquiv K L v w τ)).val x) = _
  rw [MulEquiv.symm_apply_apply, originalAdicDecompositionGaloisEquiv_apply]
  exact (numberFieldGaloisLocalTransport_algebraMap K L τ.val w w τ.property x).symm

/-- The literal original global-unit embedding intertwines the actual completion action. -/
def originalGlobalCompletionUnitRepHom :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    Rep.res (originalCompletionGaloisRestriction K L v w) (Rep.ofAlgebraAutOnUnits K L) ⟶
      Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L) := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  refine Rep.ofHom ⟨(Units.map (algebraMap L (w.adicCompletion L)).toMonoidHom).toAdditive.toIntLinearMap, ?_⟩
  intro σ
  apply LinearMap.ext
  intro x
  apply congrArg Additive.ofMul
  apply Units.ext
  exact originalCompletionGaloisRestriction_commutes K L v w σ x.toMul.val

/-- Original global H2 mapped to the actual finite completion Galois cohomology. -/
def originalGlobalCompletionH2 :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) 2 :=
  groupCohomology.map (originalCompletionGaloisRestriction K L v w)
    (originalGlobalCompletionUnitRepHom K L v w) 2

/-- The actual completion localization agrees with the original decomposition localization on every original H2 class. -/
theorem originalGlobalCompletionH2_decomposition
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    (originalAdicUnitCohomologyIso K L v w 2).hom
      (originalGlobalCompletionH2 K L v w x) = originalGlobalAdicH2 K L w x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    simp only [originalAdicUnitCohomologyIso, originalCohomologyReindex,
      Iso.trans_hom, Functor.mapIso_hom, asIso_hom, ModuleCat.comp_apply,
      groupCohomology.functor_map, originalGlobalCompletionH2, originalGlobalAdicH2,
      groupCohomology.H2π_comp_map_apply]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext g
    change Additive.ofMul (Units.map (algebraMap L (w.adicCompletion L)).toMonoidHom
      (c (((originalAdicDecompositionGaloisEquiv K L v w).symm
        (originalAdicDecompositionGaloisEquiv K L v w g.1)).val,
        ((originalAdicDecompositionGaloisEquiv K L v w).symm
          (originalAdicDecompositionGaloisEquiv K L v w g.2)).val)).toMul) = _
    simp only [MulEquiv.symm_apply_apply]
    rfl

end
end Dubon2026
