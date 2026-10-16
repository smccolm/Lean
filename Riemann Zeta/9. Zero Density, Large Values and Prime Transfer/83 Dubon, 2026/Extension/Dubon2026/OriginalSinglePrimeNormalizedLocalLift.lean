import Dubon2026.OriginalSinglePrimeIdeleH2Lift
import Dubon2026.OriginalFiniteLocalNormalizedClass
import Dubon2026.OriginalFullIdeleCompletionInvariant
import Dubon2026.OriginalAdicDecompositionDegree

/-! # Normalize the original local lift without full decomposition

The existing finite local fundamental class is transported through the
actual completion/decomposition comparison. The new genuine trace lift
recovers it, so its original completion invariant is the positive
reciprocal of the actual decomposition-group order.
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
  (Ω : Type) [Field Ω]
  [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]

/-- At every original finite prime, a constructed local H2 class has a genuine trace lift with invariant the reciprocal of the actual decomposition-group order. -/
theorem originalSinglePrime_exists_normalized_local_lift :
    letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
    ∃ y : groupCohomology (originalAdicUnitRep K L w) 2,
      originalFullIdeleCompletionInvariant K L v w Ω (originalSinglePrimeIdeleH2Lift K L w y) =
        (↑((1 : ℚ) / Nat.card (OriginalFiniteDecompositionGroup K L w)) : AddCircle (1 : ℚ)) := by
  letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
  obtain ⟨y, hy⟩ := originalFiniteLocal_exists_normalized_class (v.adicCompletion K) (w.adicCompletion L) Ω
  let eL := continuousDiscreteH2Equiv
    (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
    (discreteGaloisUnitAction_continuous (K := v.adicCompletion K) (Ω := w.adicCompletion L))
  let eD := (originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv
  let x := originalSinglePrimeIdeleH2Lift K L w (eD (eL y))
  have hsection : originalFullIdeleAdicH2 K L w x = eD (eL y) :=
    congrArg (fun f => f.hom (eD (eL y))) (originalSinglePrimeIdeleH2Lift_section K L w)
  have hloc : originalFullIdeleCompletionH2 K L v w x = eL y := by
    change eD.symm (originalFullIdeleAdicH2 K L w x) = eL y
    rw [hsection]
    exact eD.symm_apply_apply _
  refine ⟨eD (eL y), ?_⟩
  have he : eL.symm (originalFullIdeleCompletionH2 K L v w x) = y :=
    (congrArg eL.symm hloc).trans (eL.symm_apply_apply y)
  have hi := congrArg (fun z => localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω
    (continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
      (w.adicCompletion L) Ω z)) he
  exact hi.trans (hy.trans (congrArg (fun n : ℕ => (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)))
    (originalAdicBaseChange_finrank_eq_decomposition_card K L v w)))

end
end Dubon2026
