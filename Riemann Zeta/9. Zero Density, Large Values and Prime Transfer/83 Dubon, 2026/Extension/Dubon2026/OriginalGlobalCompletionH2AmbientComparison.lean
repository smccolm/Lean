import Dubon2026.OriginalGlobalCompletionCocycleAmbientComparison

/-! # Finite global localization and ambient continuous base change agree

The original completion cocycle and the direct ambient cocycle have the
same values, by the proved restriction comparison and the original unit
embedding tower. This identifies the existing finite-global invariant
needed for DUB-17's number-field reciprocity sum, rather than introducing
a substitute invariant or a finite-support assumption.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryGalois
  originalCompletionCarryFinite originalCompletionCarryValuation originalCompletionCarryLocalField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra L Ω]
  [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
  [IsScalarTower K L Ω] [IsScalarTower K (v.adicCompletion K) Ω]
  [IsScalarTower L (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]

/-- Original finite completion localization followed by ambient inflation is the literal continuous base change of the same global class. -/
theorem originalGlobalCompletionH2_ambient
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
      (w.adicCompletion L) Ω
      ((continuousDiscreteH2Equiv
        (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
        (discreteGaloisUnitAction_continuous (K := v.adicCompletion K)
          (Ω := w.adicCompletion L))).symm
        (originalGlobalCompletionH2 K L v w
          (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
            (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) x))) =
      continuousGaloisUnitBaseChangeH2 K (v.adicCompletion K) L Ω x := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    let e := continuousDiscreteH2Equiv
      (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
      (discreteGaloisUnitAction_continuous (K := v.adicCompletion K)
        (Ω := w.adicCompletion L))
    have hd := originalGlobalCompletionH2_continuousCocycle K L v w c.val
    have he := (congrArg e.symm hd).trans (e.symm_apply_apply _)
    have hleft := congrArg
      (continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
        (w.adicCompletion L) Ω) he
    have hright := congrArg
      (fun d : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω) =>
        (Submodule.Quotient.mk d : GaloisUnitContinuousH2 (K := v.adicCompletion K) (Ω := Ω)))
      (originalGlobalCompletionContinuousCocycle_ambient K L v w Ω c)
    exact hleft.trans hright

/-- The existing normalized original finite-global invariant equals the invariant of literal ambient localization, with no new invariant convention. -/
theorem originalGlobalCompletionInvariant_ambient [IsSepClosed Ω]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    originalGlobalCompletionInvariant K L v w Ω
      (continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
        (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) x) =
      localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω
        (continuousGaloisUnitBaseChangeH2 K (v.adicCompletion K) L Ω x) :=
  congrArg (localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω)
    (originalGlobalCompletionH2_ambient K L v w Ω x)

end
end Dubon2026
