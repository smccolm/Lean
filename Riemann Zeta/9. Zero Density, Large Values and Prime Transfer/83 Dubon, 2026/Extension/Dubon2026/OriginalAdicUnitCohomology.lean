import Dubon2026.OriginalAdicFiniteGalois
import Dubon2026.OriginalGroupCohomologyReindex

/-! # Original decomposition-unit cohomology is the actual completion Galois cohomology

Both coefficients are the same original completion-unit group. The proved
decomposition/Galois equivalence preserves its action on literal values.
This identifies the finite local H2 input required for DUB-17's normalized
local invariant comparison and cyclic cyclotomic killing argument.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance] Units.mulDistribMulActionRight
attribute [local instance 1100] Rep.hV2 AddCommGroup.toAddCommMonoid
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The actual original decomposition group acting on original completion units. -/
def originalAdicUnitRep (w : HeightOneSpectrum (𝓞 L)) :
    Rep ℤ (OriginalFiniteDecompositionGroup K L w) := by
  letI := originalAdicDecompositionAction K L w
  exact Rep.ofMulDistribMulAction (OriginalFiniteDecompositionGroup K L w) (w.adicCompletion L)ˣ

variable [NumberField K] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The completion Galois and original decomposition representations agree on the same original units. -/
def originalAdicUnitCoefficientIso :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    Rep.res (originalAdicDecompositionGaloisEquiv K L v w).toMonoidHom
      (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) ≅
        originalAdicUnitRep K L w := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  apply Rep.mkIso
  refine Representation.Equiv.mk (LinearEquiv.refl ℤ (Additive (w.adicCompletion L)ˣ)) ?_
  intro σ
  apply LinearMap.ext
  intro x
  rfl

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual original finite-place stabilizer cohomology is the original finite completion Galois cohomology. -/
def originalAdicUnitCohomologyIso (n : ℕ) :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    groupCohomology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) n ≅
      groupCohomology (originalAdicUnitRep K L w) n := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  exact originalCohomologyReindex _ (originalAdicDecompositionGaloisEquiv K L v w) n ≪≫
    (groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) n).mapIso
      (originalAdicUnitCoefficientIso K L v w)

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The coefficient comparison preserves every actual original completion unit literally. -/
theorem originalAdicUnitCoefficientIso_hom_apply (x : Additive (w.adicCompletion L)ˣ) :
    (originalAdicUnitCoefficientIso K L v w).hom.hom x = x := rfl

end
end Dubon2026
