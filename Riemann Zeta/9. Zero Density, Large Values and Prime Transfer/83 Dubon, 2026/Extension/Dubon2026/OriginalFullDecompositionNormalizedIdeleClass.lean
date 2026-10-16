import Dubon2026.OriginalFullDecompositionIdeleH2Lift
import Dubon2026.OriginalFiniteLocalNormalizedClass
import Dubon2026.OriginalFullIdeleCompletionInvariant
import Dubon2026.OriginalAdicDecompositionDegree

/-! # The normalized original idele H2 class at a full-decomposition prime

The original local fundamental class is lifted by the actual single-prime
coefficient inclusion. Its normalized invariant is the positive reciprocal
of the global degree and every other original finite localization is zero.
This supplies the full-order witness before descent to original idele
classes on DUB-17's finite class-invariant route.
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

/-- Full original decomposition produces an actual full-idele H2 class with positive reciprocal global degree at its original completion and zero localization at every other finite prime. -/
theorem originalFullDecomposition_exists_normalized_idele_class
    (hw : OriginalFiniteDecompositionGroup K L w = ⊤) :
    ∃ x : groupCohomology (originalFullIdeleRep K L) 2,
      originalFullIdeleCompletionInvariant K L v w Ω x =
        (↑((1 : ℚ) / Module.finrank K L) : AddCircle (1 : ℚ)) ∧
      ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 L), t ≠ w →
        originalFullIdeleAdicH2 K L t x = 0 := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
  obtain ⟨y, hy⟩ := originalFiniteLocal_exists_normalized_class (v.adicCompletion K) (w.adicCompletion L) Ω
  let eL := continuousDiscreteH2Equiv
    (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
    (discreteGaloisUnitAction_continuous (K := v.adicCompletion K) (Ω := w.adicCompletion L))
  let eD := (originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv
  let x := originalFullDecompositionIdeleH2Lift K L w hw (eD (eL y))
  have hloc : originalFullIdeleCompletionH2 K L v w x = eL y := by
    change eD.symm (originalFullIdeleAdicH2 K L w x) = eL y
    rw [originalFullDecompositionIdeleH2Lift_section]
    exact eD.symm_apply_apply _
  have hd : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = Module.finrank K L := by
    rw [originalAdicBaseChange_finrank_eq_decomposition_card K L v w]
    exact (Nat.card_congr (originalFullDecompositionEquiv K L w hw).toEquiv).trans
      (IsGalois.card_aut_eq_finrank K L)
  refine ⟨x, ?_, ?_⟩
  · have he : eL.symm (originalFullIdeleCompletionH2 K L v w x) = y :=
      (congrArg eL.symm hloc).trans (eL.symm_apply_apply y)
    have hi := congrArg (fun z => localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω
      (continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
        (w.adicCompletion L) Ω z)) he
    exact hi.trans (hy.trans (congrArg (fun n : ℕ => (↑((1 : ℚ) / n) : AddCircle (1 : ℚ))) hd))
  · intro t ht
    exact originalFullDecompositionIdeleH2Lift_other K L w hw t ht (eD (eL y))

end
end Dubon2026
