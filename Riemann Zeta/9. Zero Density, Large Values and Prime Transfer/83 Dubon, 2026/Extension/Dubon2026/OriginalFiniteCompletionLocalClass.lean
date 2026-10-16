import Dubon2026.OriginalSinglePrimeNormalizedLocalLift

/-! # Original local classes from finite completion cohomology

Retain the actual continuous/discrete comparison and completion/decomposition
isomorphism. The genuine single-prime trace recovers any supplied finite
completion class, so its normalized invariant is exactly the original local
inflation invariant. DUB-17 uses this to consume supplied local fundamental
classes in the source's normalization convention.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- Original completion localization of the genuine single-prime trace recovers the actual completion class corresponding to the supplied decomposition-group class. -/
theorem originalSinglePrimeIdeleH2Lift_completion_section
    (x : groupCohomology (originalAdicUnitRep K L w) 2) :
    letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
    originalFullIdeleCompletionH2 K L v w (originalSinglePrimeIdeleH2Lift K L w x) =
      (originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv.symm x := by
  letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  exact congrArg (originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv.symm
    (congrArg (fun f => f.hom x) (originalSinglePrimeIdeleH2Lift_section K L w))

/-- The actual finite-completion class transported to original decomposition-group cohomology by the proved continuous/discrete and original completion isomorphisms. -/
def originalFiniteCompletionLocalClass :
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
    GaloisUnitContinuousH2 (K := v.adicCompletion K) (Ω := w.adicCompletion L) ≃ₗ[ℤ]
      groupCohomology (originalAdicUnitRep K L w) 2 := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
  exact (continuousDiscreteH2Equiv
    (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
    (discreteGaloisUnitAction_continuous (K := v.adicCompletion K) (Ω := w.adicCompletion L))).trans
      (originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv

variable (Ω : Type) [Field Ω]
  [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]

/-- Every supplied original finite-completion class has exactly its original ambient local invariant after transport to the decomposition group and genuine single-prime trace lift. -/
theorem originalFiniteCompletionLocalClass_trace_invariant :
    letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
    ∀ y : GaloisUnitContinuousH2 (K := v.adicCompletion K) (Ω := w.adicCompletion L),
      originalFullIdeleCompletionInvariant K L v w Ω
        (originalSinglePrimeIdeleH2Lift K L w (originalFiniteCompletionLocalClass K L v w y)) =
      localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω
        (continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
          (w.adicCompletion L) Ω y) := by
  letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
  let eL := continuousDiscreteH2Equiv
    (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
    (discreteGaloisUnitAction_continuous (K := v.adicCompletion K) (Ω := w.adicCompletion L))
  let eD := (originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv
  change ∀ y : GaloisUnitContinuousH2 (K := v.adicCompletion K) (Ω := w.adicCompletion L),
    originalFullIdeleCompletionInvariant K L v w Ω
      (originalSinglePrimeIdeleH2Lift K L w (eD (eL y))) =
      localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω
        (continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
          (w.adicCompletion L) Ω y)
  intro y
  let x := originalSinglePrimeIdeleH2Lift K L w (eD (eL y))
  have hl : originalFullIdeleCompletionH2 K L v w x = eL y :=
    (originalSinglePrimeIdeleH2Lift_completion_section K L v w (eD (eL y))).trans
      (eD.symm_apply_apply _)
  have he : eL.symm (originalFullIdeleCompletionH2 K L v w x) = y :=
    (congrArg eL.symm hl).trans (eL.symm_apply_apply y)
  exact congrArg (fun z => localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω
    (continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
      (w.adicCompletion L) Ω z)) he

end
end Dubon2026
