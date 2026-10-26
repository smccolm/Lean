import Dubon2026.SourceGammaOneGeometricCohomology

/-! DUB-17/18 -> original all-weight adic association -> arithmetic
realization of finite Gamma1 characters -> geometric/H1 comparison with
the original homogeneous coefficient action. Separate the explicit
coefficient endomorphism from the ordinary constant-coefficient
correspondence by its literal finite sum. Both orders are proved, so
geometric realization must retain this factor rather than discard it. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CategoryTheory CongruenceSubgroup
variable (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (M : ℕ)

/-- The native H1 map induced by the prescribed endomorphism of the actual
trivial Gamma1 coefficient representation. -/
def constantCoefficientH1 (b : Module.End R V) :
    Module.End R (groupCohomology.H1 (Rep.trivial R (Gamma1 M) V)) :=
  (groupCohomology.map (MonoidHom.id (Gamma1 M))
    ((Rep.trivialFunctor R (Gamma1 M)).map (ModuleCat.ofHom b)) 1).hom

theorem constantCoefficientH1_cocycle (b : Module.End R V)
    (c : groupCohomology.cocycles₁ (Rep.trivial R (Gamma1 M) V)) :
    constantCoefficientH1 R V M b (groupCohomology.H1π (Rep.trivial R (Gamma1 M) V) c) =
      groupCohomology.H1π (Rep.trivial R (Gamma1 M) V)
        (groupCohomology.mapCocycles₁ (MonoidHom.id (Gamma1 M))
          ((Rep.trivialFunctor R (Gamma1 M)).map (ModuleCat.ofHom b)) c) :=
  groupCohomology.H1π_comp_map_apply _ _ c

variable (d : ℕ) [NeZero d]

private local instance upperCosetsFinite :
    Fintype (Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) := by
  letI := sourceGammaOneHeckeUpper_finiteIndex M d
  exact Fintype.ofFinite _

theorem constantHeckeCocycles_coefficient_left (b : Module.End R V)
    (c : groupCohomology.cocycles₁ (Rep.trivial R (Gamma1 M) V)) :
    sourceGammaOneConstantHeckeCocycles R V M d b c =
      groupCohomology.mapCocycles₁ (MonoidHom.id (Gamma1 M))
        ((Rep.trivialFunctor R (Gamma1 M)).map (ModuleCat.ofHom b))
        (sourceGammaOneConstantHeckeCocycles R V M d LinearMap.id c) := by
  apply Subtype.ext
  funext g
  change (∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d,
      b (c (sourceGammaOneHeckeConjugation M d
        (cosetTransition (sourceGammaOneHeckeUpper M d) g q)))) =
    b (∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d,
      c (sourceGammaOneHeckeConjugation M d
        (cosetTransition (sourceGammaOneHeckeUpper M d) g q)))
  rw [map_sum]

theorem constantHeckeCocycles_coefficient_right (b : Module.End R V)
    (c : groupCohomology.cocycles₁ (Rep.trivial R (Gamma1 M) V)) :
    sourceGammaOneConstantHeckeCocycles R V M d b c =
      sourceGammaOneConstantHeckeCocycles R V M d LinearMap.id
        (groupCohomology.mapCocycles₁ (MonoidHom.id (Gamma1 M))
          ((Rep.trivialFunctor R (Gamma1 M)).map (ModuleCat.ofHom b)) c) := rfl

theorem constantHeckeH1_coefficient_left (b : Module.End R V) :
    sourceGammaOneConstantHeckeH1 R V M d b =
      (constantCoefficientH1 R V M b).comp
        (sourceGammaOneConstantHeckeH1 R V M d LinearMap.id) := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H1π
    (Rep.trivial R (Gamma1 M) V))).mp inferInstance x
  rw [LinearMap.comp_apply, sourceGammaOneConstantHeckeH1_cocycle,
    sourceGammaOneConstantHeckeH1_cocycle, constantCoefficientH1_cocycle,
    constantHeckeCocycles_coefficient_left]
  rfl

theorem constantHeckeH1_coefficient_right (b : Module.End R V) :
    sourceGammaOneConstantHeckeH1 R V M d b =
      (sourceGammaOneConstantHeckeH1 R V M d LinearMap.id).comp
        (constantCoefficientH1 R V M b) := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H1π
    (Rep.trivial R (Gamma1 M) V))).mp inferInstance x
  rw [LinearMap.comp_apply, sourceGammaOneConstantHeckeH1_cocycle,
    constantCoefficientH1_cocycle, sourceGammaOneConstantHeckeH1_cocycle,
    constantHeckeCocycles_coefficient_right]

/-- The original coefficient factor is retained under the exact geometric
cohomology comparison; no equality with the ordinary Picard operator is assumed. -/
theorem geometricHeckeH1_coefficient (b : Module.End R V) :
    geometricHeckeH1 M d R V b =
      (constantCoefficientH1 R V M b).comp (geometricHeckeH1 M d R V LinearMap.id) ∧
    geometricHeckeH1 M d R V b =
      (geometricHeckeH1 M d R V LinearMap.id).comp (constantCoefficientH1 R V M b) := by
  simp only [geometricHeckeH1_eq]
  exact ⟨constantHeckeH1_coefficient_left R V M d b,
    constantHeckeH1_coefficient_right R V M d b⟩

end
end Dubon2026.SourceFunctionField.GammaOne
