import Dubon2026.IntegralInducedActionContinuity
import Dubon2026.IntegralInducedTensor

/-! Continuity of Geraghty's literal finite embedding tensor action.
The native tensor-basis coordinate formula reduces pure tensors to a
finite sum of products of continuous original coordinates. No tensor
action topology or continuous representation is assumed. This is the
coefficient continuity dependency of the automorphy route to Theorem 2.6.
-/

namespace Dubon2026
noncomputable section
open Matrix Topology
open scoped TensorProduct

universe u

/-- The original pure tensor map is continuous in canonical finite free module topologies, by its native tensor-basis coordinates. -/
theorem finiteBasis_piTensorProduct_continuous
    {R I : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Fintype I]
    {M : I → Type u} {J : I → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, IsModuleTopology R (M i)] [∀ i, Fintype (J i)]
    [TopologicalSpace (⨂[R] i, M i)] [IsModuleTopology R (⨂[R] i, M i)]
    (b : ∀ i, Module.Basis (J i) R (M i)) :
    Continuous (PiTensorProduct.tprod R : (∀ i, M i) → ⨂[R] i, M i) := by
  classical
  letI : ContinuousAdd (⨂[R] i, M i) := IsModuleTopology.toContinuousAdd R _
  have he (p : ∀ i, M i) : PiTensorProduct.tprod R p =
      ∑ j : ∀ i, J i, (∏ i, (b i).coord (j i) (p i)) • Basis.piTensorProduct b j := by
    conv_lhs => rw [← (Basis.piTensorProduct b).sum_repr (PiTensorProduct.tprod R p)]
    simp only [Basis.piTensorProduct_repr_tprod_apply, Module.Basis.coord_apply]
  apply Continuous.congr _ (fun p => (he p).symm)
  apply continuous_finsetSum
  intro j _
  apply Continuous.smul _ continuous_const
  apply continuous_finsetProd
  intro i _
  exact (IsModuleTopology.continuous_of_linearMap ((b i).coord (j i))).comp (continuous_apply i)

/-- The actual tensor of the original integral induced actions is jointly continuous in its canonical source coefficient topology. -/
theorem integralLocalInducedTensorRepresentation_continuous
    (R E : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] [CharZero R]
    [TopologicalSpace R] [CompactSpace R] [IsTopologicalRing R]
    [Field E] [Infinite E] [Algebra R E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
    [ContinuousSMul R E] [T2Space E]
    {I : Type u} [Finite I] {n : ℕ} (lam : I → Fin (n + 1) → ℤ)
    [TopologicalSpace (IntegralInducedTensor R (n + 1) lam)]
    [IsModuleTopology R (IntegralInducedTensor R (n + 1) lam)]
    (hRE : Function.Injective (algebraMap R E)) (hcont : Continuous (algebraMap R E)) :
    Continuous (fun p : (I → GeneralLinearGroup (Fin (n + 1)) R) ×
        IntegralInducedTensor R (n + 1) lam =>
      integralInducedTensorRepresentation R (n + 1) lam p.1 p.2) := by
  classical
  letI := Fintype.ofFinite I
  letI : ∀ i, TopologicalSpace (generalLinearIntegralInducedSubmodule R (n + 1) (lam i)) :=
    fun i => moduleTopology R (generalLinearIntegralInducedSubmodule R (n + 1) (lam i))
  letI : TopologicalSpace (⨂[R] i, generalLinearIntegralInducedSubmodule R (n + 1) (lam i)) :=
    inferInstanceAs (TopologicalSpace (IntegralInducedTensor R (n + 1) lam))
  letI : IsModuleTopology R (⨂[R] i, generalLinearIntegralInducedSubmodule R (n + 1) (lam i)) :=
    inferInstanceAs (IsModuleTopology R (IntegralInducedTensor R (n + 1) lam))
  apply finiteBasis_linearFamily_continuous (integralLocalInducedTensorBasis R lam)
  intro j
  have he (g : I → GeneralLinearGroup (Fin (n + 1)) R) :
      integralInducedTensorRepresentation R (n + 1) lam g (integralLocalInducedTensorBasis R lam j) =
        PiTensorProduct.tprod R (fun i =>
          generalLinearIntegralInducedRepresentation R (n + 1) (lam i) (g i)
            (Module.Free.chooseBasis R (generalLinearIntegralInducedSubmodule R (n + 1) (lam i)) (j i))) := by
    have hb : integralLocalInducedTensorBasis R lam j = PiTensorProduct.tprod R
        (fun i => Module.Free.chooseBasis R
          (generalLinearIntegralInducedSubmodule R (n + 1) (lam i)) (j i)) :=
      Basis.piTensorProduct_apply _ j
    rw [hb, integralInducedTensorRepresentation_tprod]
  simp_rw [he]
  apply (finiteBasis_piTensorProduct_continuous (fun i =>
    Module.Free.chooseBasis R (generalLinearIntegralInducedSubmodule R (n + 1) (lam i)))).comp
  apply continuous_pi
  intro i
  exact (integralLocalInducedRepresentation_orbit_continuous R E (lam i) hRE hcont _).comp
    (continuous_apply i)

end
end Dubon2026
