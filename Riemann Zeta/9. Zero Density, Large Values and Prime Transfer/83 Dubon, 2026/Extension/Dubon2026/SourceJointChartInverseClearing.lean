import Dubon2026.SourceJointChartIntegralAlgebras
import Dubon2026.SourceCurvePoleBasisBound
import Dubon2026.SourceCurveClosedSeparatingPrincipalDivisors

/-! DUB-17/18 -> Kummer genus inequality -> common residue-chart constants.
The existing principal-divisor and pole-bound proofs clear an inverse-chart
element by a power of the original coordinate. This supplies the actual
inclusion of the inverse localization into the overlap, avoiding another
general theorem about extensions of valuation rings. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open IsLocalRing

theorem exists_mul_pow_mem_Sg
    {L F : Type*} [Field L] [IsAlgClosed L] [CharZero L]
    {A : ValuationSubring L} [Field F] [Algebra L F]
    {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i)) (f : F)
    (hf : ∀ i, f ∈ (R i).integers) (htr : Transcendental L f)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (u : F) (hu : u ∈ Sg R f⁻¹) : ∃ m : ℕ, u * f ^ m ∈ Sg R f := by
  have hfi : Transcendental L f⁻¹ := fun h => htr (IsAlgebraic.inv_iff.mp h)
  haveI : FiniteDimensional (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
    rw [adjoin_singleton_inv_eq]
    infer_instance
  haveI := hasPrincipalDivisors_closed_of_separating_coordinate f⁻¹ hfi
  have hf0 : f⁻¹ ≠ 0 := fun h => hfi (h ▸ isAlgebraic_zero)
  obtain ⟨D, hD, _⟩ := HasPrincipalDivisors.exists_divisor (K := L) f⁻¹ hf0
  have hs : {v : Place L F | v.ord f⁻¹ ≠ 0}.Finite := by
    apply D.support.finite_toSet.subset
    intro v hv
    exact Finsupp.mem_support_iff.mpr (by rwa [hD v])
  obtain ⟨m, hm⟩ := exists_forall_mem_lSpace_nsmul_poleDivisor f⁻¹ hs
    (fun _ : Fin 1 => u) (fun _ v hv => v.ord_nonneg_of_mem
      ((mem_originalChart_iff f⁻¹ u).mp hu.2 v.toValuationSubring
        v.algebraMap_mem' (v.mem_of_ord_nonneg hv)))
  refine ⟨m, fun i => mul_mem (hu.1 i) (pow_mem (hf i) m), ?_⟩
  have hi := (integral_charts_of_pole_bound f⁻¹ hfi (poleDivisor f⁻¹ hs)
    (fun v => by rw [poleDivisor_apply, max_comm]) m (hm 0)).2
  apply (mem_originalChart_iff f (u * f ^ m)).mpr
  intro V hV hfV
  have hv := Joint.mem_valuation_of_integral_chart hi V hV
    (show f⁻¹⁻¹ ∈ V by simpa only [inv_inv] using hfV)
  simpa only [inv_pow, inv_inv] using hv

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
