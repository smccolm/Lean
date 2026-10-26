import Dubon2026.SourceGammaOneHeckeGeometricSubgroup
import Dubon2026.SourceGammaOneConstantHecke
import Dubon2026.OriginalGroupCohomologyReindex

/-! DUB-17/18 -> original all-weight adic association -> actual finite
Gamma1 character realization -> geometric/H1 comparison preserving the
original homogeneous coefficient action. The two actual geometric group
maps are inclusion and integral level raising. Native cohomology
composition identifies trace along the latter after pullback along the
former with the existing full Gamma1 operator. This does not yet identify
the Picard action with H1 or remove the parabolic/diamond comparison. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CategoryTheory CongruenceSubgroup Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

variable (M d : ℕ) [NeZero d]

/-- The group map for the actual forgetful geometric correspondence. -/
def geometricAlphaGroup : ↥(Gamma1 M ⊓ Gamma0 (d * M)) →* Gamma1 M :=
  Subgroup.inclusion inf_le_left

/-- The group map for the actual analytic dilation in the geometric correspondence. -/
def geometricBetaGroup : ↥(Gamma1 M ⊓ Gamma0 (d * M)) →* Gamma1 M :=
  (sourceGammaOneHeckeUpper M d).subtype.comp
    (heckeUpperGeometricEquiv M d).symm.toMonoidHom

theorem geometricBetaGroup_injective : Function.Injective (geometricBetaGroup M d) :=
  Subtype.val_injective.comp (heckeUpperGeometricEquiv M d).symm.injective

theorem geometricAlphaGroup_upper (g : sourceGammaOneHeckeUpper M d) :
    geometricAlphaGroup M d (heckeUpperGeometricEquiv M d g) =
      sourceGammaOneHeckeConjugation M d g := rfl

theorem geometricBetaGroup_matrix (g : ↥(Gamma1 M ⊓ Gamma0 (d * M))) :
    levelRaiseMatrix d * mapGL ℝ g.val =
      mapGL ℝ (geometricBetaGroup M d g).val * levelRaiseMatrix d := by
  have h := upperToGeometric_matrix M d ((heckeUpperGeometricEquiv M d).symm g)
  change levelRaiseMatrix d * mapGL ℝ
    ((heckeUpperGeometricEquiv M d) ((heckeUpperGeometricEquiv M d).symm g)).val =
      mapGL ℝ (geometricBetaGroup M d g).val * levelRaiseMatrix d at h
  simpa only [MulEquiv.apply_symm_apply] using h

theorem geometricBetaGroup_smul (g : ↥(Gamma1 M ⊓ Gamma0 (d * M))) (z : ℍ) :
    levelRaiseMatrix d • (g.val • z) =
      (geometricBetaGroup M d g).val • (levelRaiseMatrix d • z) := by
  have h := upperToGeometric_smul M d ((heckeUpperGeometricEquiv M d).symm g) z
  change levelRaiseMatrix d •
    (((heckeUpperGeometricEquiv M d) ((heckeUpperGeometricEquiv M d).symm g)).val • z) =
      (geometricBetaGroup M d g).val • (levelRaiseMatrix d • z) at h
  simpa only [MulEquiv.apply_symm_apply] using h

variable (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]

/-- Pullback along the actual forgetful group map retains the prescribed coefficient map. -/
def geometricAlphaMorphism (b : Module.End R V) :
    Rep.res (geometricAlphaGroup M d) (Rep.trivial R (Gamma1 M) V) ⟶
      Rep.trivial R ↥(Gamma1 M ⊓ Gamma0 (d * M)) V :=
  Rep.ofHom {
    toLinearMap := b
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro x
      rfl }

private local instance upperCosetsFinite :
    Fintype (Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) := by
  letI := sourceGammaOneHeckeUpper_finiteIndex M d
  exact Fintype.ofFinite _

/-- Trace along the actual dilation, factored through its proved upper-subgroup
isomorphism. Its source is the genuine geometric correspondence group. -/
def geometricBetaH1Trace :
    groupCohomology.H1 (Rep.trivial R ↥(Gamma1 M ⊓ Gamma0 (d * M)) V) →ₗ[R]
      groupCohomology.H1 (Rep.trivial R (Gamma1 M) V) :=
  (sourceHeckeH1Trace (Rep.trivial R (Gamma1 M) V) (sourceGammaOneHeckeUpper M d)).comp
    (originalCohomologyReindex
      (Rep.trivial R ↥(Gamma1 M ⊓ Gamma0 (d * M)) V)
      (heckeUpperGeometricEquiv M d) 1).hom.hom

/-- The cohomological geometric correspondence, with the original coefficient endomorphism. -/
def geometricHeckeH1 (b : Module.End R V) :
    Module.End R (groupCohomology.H1 (Rep.trivial R (Gamma1 M) V)) :=
  (geometricBetaH1Trace M d R V).comp
    (groupCohomology.map (geometricAlphaGroup M d) (geometricAlphaMorphism M d R V b) 1).hom

/-- The actual geometric pullback/trace is exactly the existing full Gamma1 H1
operator. In particular the higher-weight homogeneous coefficient map is retained. -/
theorem geometricHeckeH1_eq (b : Module.End R V) :
    geometricHeckeH1 M d R V b = sourceGammaOneConstantHeckeH1 R V M d b := by
  unfold geometricHeckeH1 geometricBetaH1Trace sourceGammaOneConstantHeckeH1
  rw [LinearMap.comp_assoc]
  congr 1
  change (groupCohomology.map (geometricAlphaGroup M d)
      (geometricAlphaMorphism M d R V b) 1 ≫
    groupCohomology.map (heckeUpperGeometricEquiv M d).toMonoidHom
      (𝟙 (Rep.res (heckeUpperGeometricEquiv M d).toMonoidHom
        (Rep.trivial R ↥(Gamma1 M ⊓ Gamma0 (d * M)) V))) 1).hom = _
  rw [← groupCohomology.map_comp]
  rfl

end
end Dubon2026.SourceFunctionField.GammaOne
