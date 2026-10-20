import Dubon2026.IntegralInducedTensorContinuity
import Dubon2026.CMIntegralInducedTensorAction

/-! The proved induced tensor continuity composed with the original
unitary local evaluation maps. This is the exact arithmetic-action
bridge used by the source coefficient-field specialization.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField TensorProduct

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable (R E : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] [CharZero R]
  [TopologicalSpace R] [CompactSpace R] [IsTopologicalRing R]
  [Field E] [Infinite E] [Algebra R E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
  [ContinuousSMul R E] [T2Space E]
  {I : Type} [Finite I] (v : I → HeightOneSpectrum (𝓞 K))
  (e : ∀ i, Valued.integer ((v i).adicCompletion K) →+* R)

omit [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] [CharZero R]
    [CompactSpace R] [IsTopologicalRing R] [Finite I] in
/-- Original local unitary evaluations followed by continuous integer embeddings give continuous coefficient matrices. -/
theorem cmIntegralCoefficientMatrixMap_continuous (n : ℕ)
    (H : Matrix (Fin n) (Fin n) K) (he : ∀ i, Continuous (e i)) :
    Continuous (cmIntegralCoefficientMatrixMap K R v e n H) :=
  continuous_pi fun i => (generalLinearCoefficientMap_continuous n (e i) (he i)).comp
    (cmFiniteAdelicIntegralLocalMap_continuous K H (v i))

/-- The original unitary arithmetic action on the literal integral tensor is jointly continuous. -/
theorem cmIntegralInducedTensorRepresentation_continuous (n : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (lam : I → Fin (n + 1) → ℤ)
    [TopologicalSpace (IntegralInducedTensor R (n + 1) lam)]
    [IsModuleTopology R (IntegralInducedTensor R (n + 1) lam)]
    (hRE : Function.Injective (algebraMap R E)) (hcont : Continuous (algebraMap R E))
    (he : ∀ i, Continuous (e i)) :
    Continuous (fun x : cmFiniteAdelicIntegralLevel K H × IntegralInducedTensor R (n + 1) lam =>
      cmIntegralInducedTensorRepresentation K R v e (n + 1) H lam x.1 x.2) := by
  change Continuous (fun x : cmFiniteAdelicIntegralLevel K H × IntegralInducedTensor R (n + 1) lam =>
    integralInducedTensorRepresentation R (n + 1) lam
      (cmIntegralCoefficientMatrixMap K R v e (n + 1) H x.1) x.2)
  have hm : Continuous (fun x : cmFiniteAdelicIntegralLevel K H ×
      IntegralInducedTensor R (n + 1) lam =>
      (cmIntegralCoefficientMatrixMap K R v e (n + 1) H x.1, x.2)) :=
    ((cmIntegralCoefficientMatrixMap_continuous K R v e (n + 1) H he).comp
      continuous_fst).prodMk continuous_snd
  have ht : Continuous (fun y : (I → GeneralLinearGroup (Fin (n + 1)) R) ×
      IntegralInducedTensor R (n + 1) lam =>
      integralInducedTensorRepresentation R (n + 1) lam y.1 y.2) :=
    integralLocalInducedTensorRepresentation_continuous R E (I := I) lam hRE hcont
  have hc := ht.comp hm
  exact hc

/-- The original small auxiliary level inclusion is continuous in its actual adelic subspace topology. -/
theorem cmSmallParabolicIntegralInclusion_continuous {S : Type*}
    (a : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (w : HeightOneSpectrum (𝓞 K)) :
    Continuous (cmSmallParabolicIntegralInclusion K a n H w) :=
  continuous_subtype_val.subtype_mk _

/-- The original small auxiliary level acts continuously on the actual induced tensor coefficient module. -/
theorem cmSmallParabolicInducedTensorRepresentation_continuous {S : Type*}
    (a : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (w : HeightOneSpectrum (𝓞 K))
    (lam : I → Fin (n + 1) → ℤ)
    [TopologicalSpace (IntegralInducedTensor R (n + 1) lam)]
    [IsModuleTopology R (IntegralInducedTensor R (n + 1) lam)]
    (hRE : Function.Injective (algebraMap R E)) (hcont : Continuous (algebraMap R E))
    (he : ∀ i, Continuous (e i)) :
    Continuous (fun x : cmFiniteAdelicSmallParabolicZero K a n H w ×
        IntegralInducedTensor R (n + 1) lam =>
      cmSmallParabolicInducedTensorRepresentation K R v e a n H w lam x.1 x.2) := by
  change Continuous (fun x : cmFiniteAdelicSmallParabolicZero K a n H w ×
      IntegralInducedTensor R (n + 1) lam =>
    cmIntegralInducedTensorRepresentation K R v e (n + 1) H lam
      (cmSmallParabolicIntegralInclusion K a n H w x.1) x.2)
  have hm : Continuous (fun x : cmFiniteAdelicSmallParabolicZero K a n H w ×
      IntegralInducedTensor R (n + 1) lam =>
      (cmSmallParabolicIntegralInclusion K a n H w x.1, x.2)) :=
    ((cmSmallParabolicIntegralInclusion_continuous K a n H w).comp
      continuous_fst).prodMk continuous_snd
  have ht : Continuous (fun y : cmFiniteAdelicIntegralLevel K H ×
      IntegralInducedTensor R (n + 1) lam =>
      cmIntegralInducedTensorRepresentation K R v e (n + 1) H lam y.1 y.2) :=
    cmIntegralInducedTensorRepresentation_continuous K R E (I := I) v e n H lam hRE hcont he
  have hc := ht.comp hm
  exact hc

end
end Dubon2026
