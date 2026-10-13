import Dubon2026.OriginalIdeleBaseChangeTower

/-! # Scalar towers for the literal original completion embeddings

The proved composition identity supplies the scalar towers required by
finite local H2 base change. No alternative embedding of a completion is
chosen. These towers connect the constructed cyclotomic local degrees to
the original global class on DUB-17's invariant sum-zero dependency.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul

/-- The original completion embeddings in an actual number-field tower form the required scalar tower. -/
theorem originalAdicBaseChange_isScalarTower
    (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
    (w : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal]
    [w.asIdeal.LiesOver u.asIdeal] [w.asIdeal.LiesOver v.asIdeal] :
    letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
      (originalAdicBaseChangeMap K E v u).toAlgebra
    letI : Algebra (u.adicCompletion E) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap E L u w).toAlgebra
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    IsScalarTower (v.adicCompletion K) (u.adicCompletion E) (w.adicCompletion L) := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
    (originalAdicBaseChangeMap K E v u).toAlgebra
  letI : Algebra (u.adicCompletion E) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap E L u w).toAlgebra
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact (originalAdicBaseChangeMap_tower K E L v u w x).symm

end
end Dubon2026
