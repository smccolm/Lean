import Dubon2026.OriginalFullIdeleCompletionBaseChange
import Dubon2026.LocalFieldFiniteBaseChangeNormalizedInvariant
import Dubon2026.OriginalFullIdeleCompletionInvariant
import Dubon2026.FiniteGaloisH2InverseBaseChangeComparison

/-! # Actual local idele invariants under finite base change

The actual completion square, same-cocycle continuous comparison and
proved local degree formula give the normalized invariant of the
base-changed original idele class. This is the summand identity needed
for DUB-17's auxiliary-class restriction and arbitrary-stage transfer.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField
variable (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional K L]
  [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
  (w : HeightOneSpectrum (𝓞 L)) (t : HeightOneSpectrum (𝓞 M))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  [t.asIdeal.LiesOver v.asIdeal] [t.asIdeal.LiesOver u.asIdeal] [t.asIdeal.LiesOver w.asIdeal]
  (Ω : Type) [Field Ω]
  [Algebra (v.adicCompletion K) Ω] [Algebra (u.adicCompletion E) Ω]
  [Algebra (w.adicCompletion L) Ω] [Algebra (t.adicCompletion M) Ω]
  [IsScalarTower (v.adicCompletion K) (u.adicCompletion E) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (t.adicCompletion M) Ω]
  [IsScalarTower (u.adicCompletion E) (t.adicCompletion M) Ω]
  [IsScalarTower (w.adicCompletion L) (t.adicCompletion M) Ω]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (u.adicCompletion E) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (u.adicCompletion E) Ω)]

/-- The original normalized completion invariant after actual base change is multiplied by the actual local base degree. -/
theorem originalFullIdeleCompletionInvariant_baseChange
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    letI : IsGalois (u.adicCompletion E) Ω :=
      IsGalois.tower_top_of_isGalois (v.adicCompletion K) (u.adicCompletion E) Ω
    originalFullIdeleCompletionInvariant E M u t Ω
      (originalFullIdeleBaseChangeH2 K E L M x) =
      Module.finrank (v.adicCompletion K) (u.adicCompletion E) •
        originalFullIdeleCompletionInvariant K L v w Ω x := by
  letI : IsGalois (u.adicCompletion E) Ω :=
    IsGalois.tower_top_of_isGalois (v.adicCompletion K) (u.adicCompletion E) Ω
  letI := originalAdicBaseChange_isScalarTower K E M v u t
  letI := originalAdicBaseChange_isScalarTower K L M v w t
  letI := originalAdicNormValuation_hasExtension K E v u
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (u.adicCompletion E) (t.adicCompletion M)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (u.adicCompletion E) (t.adicCompletion M)) := ⟨rfl⟩
  let eL := continuousDiscreteH2Equiv
    (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
    (discreteGaloisUnitAction_continuous (K := v.adicCompletion K) (Ω := w.adicCompletion L))
  let eM := continuousDiscreteH2Equiv
    (Rep.ofAlgebraAutOnUnits (u.adicCompletion E) (t.adicCompletion M))
    (discreteGaloisUnitAction_continuous (K := u.adicCompletion E) (Ω := t.adicCompletion M))
  let y := eL.symm (originalFullIdeleCompletionH2 K L v w x)
  have h := continuousDiscreteH2Equiv_symm_finiteGaloisBaseChange
    (v.adicCompletion K) (u.adicCompletion E) (w.adicCompletion L) (t.adicCompletion M)
    (originalFullIdeleCompletionH2 K L v w x)
  have hc' := (congrArg eM.symm
    (originalFullIdeleCompletionH2_baseChange K E L M v u w t x)).symm.trans h
  have hi := localFieldFiniteBaseChange_normalized_invariant
    (v.adicCompletion K) (u.adicCompletion E) (w.adicCompletion L) (t.adicCompletion M) Ω y
  exact (congrArg (fun z => localFieldContinuousH2InvariantEquiv (u.adicCompletion E) Ω
    (continuousGaloisUnitBaseChangeH2 (u.adicCompletion E) (u.adicCompletion E)
      (t.adicCompletion M) Ω z)) hc').trans hi

end
end Dubon2026
