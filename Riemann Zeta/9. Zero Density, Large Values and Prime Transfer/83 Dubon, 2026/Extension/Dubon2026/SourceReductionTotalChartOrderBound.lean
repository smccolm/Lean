import Dubon2026.SourceReductionLocalFiberOrder
import Dubon2026.SourceCurveFilteredOrders

/-! DUB-17/18 -> modular good reduction -> principal-divisor pushforward ->
equality of total chart orders. Summing the proved local fiber inequalities
over the actual finite residue divisor support gives the first total-order
inequality. Unique chart reduction places make the original fibers disjoint;
integrality controls the omitted terms. No total-order comparison is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open scoped Classical
open IsLocalRing
variable {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [HasPrincipalDivisors (ResidueField A) Fbar]
local notation "k" => ResidueField A

theorem residue_chartOrderSum_le (R : RegularProlongation A F Fbar) (x : R.integers)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar] (hx : Transcendental k (R.residue x))
    (hfin : 0 < Module.finrank (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin k {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (g : R.integers) (hgi : IsIntegral (Algebra.adjoin L {(x : F)}) (g : F))
    (hg : R.residue g ≠ 0) :
    chartOrderSum ((fun Q : Place k Fbar => R.residue x ∈ Q.toValuationSubring)) (R.residue g) ≤ chartOrderSum ((ChartDomain A · (x : F))) (g : F) := by
  have hE : ∀ P, (ChartDomain A · (x : F)) P → ∃! Q : Place k Fbar, (ChartReducesTo A R (x : F)) P Q := fun P hP =>
    existsUnique_reduction_chart_place R x hx hfin hdeg
      hchart P hP
  set Dg : Divisor L F := principalOrderDivisor L (g : F) with hDg
  set T : Place k Fbar → Finset (Place L F) := fun Q =>
    Dg.support.filter fun P => (ChartDomain A · (x : F)) P ∧ (ChartReducesTo A R (x : F)) P Q with hT
  have hchild : ∀ Q, (fun Q : Place k Fbar => R.residue x ∈ Q.toValuationSubring) Q → Q.ord (R.residue g) ≤ ∑ P ∈ T Q, Dg P := fun Q hQ =>
    residue_order_le_sum_fiber_orders A R x hx hfin hdeg hchart g
      hgi hg Q hQ Dg (fun P => principalOrderDivisor_apply _ _) (T Q) (fun P => by
        simp only [hT, Finset.mem_filter, Finsupp.mem_support_iff, ChartDomain, ChartReducesTo])
  set SQ : Finset (Place k Fbar) := (principalOrderDivisor k (R.residue g)).support.filter ((fun Q : Place k Fbar => R.residue x ∈ Q.toValuationSubring)) with hSQ
  calc chartOrderSum ((fun Q : Place k Fbar => R.residue x ∈ Q.toValuationSubring)) (R.residue g)
      = ∑ Q ∈ SQ, Q.ord (R.residue g) := rfl
    _ ≤ ∑ Q ∈ SQ, ∑ P ∈ T Q, Dg P :=
        Finset.sum_le_sum fun Q hQ => hchild Q (Finset.mem_filter.mp hQ).2
    _ = ∑ P ∈ SQ.biUnion T, Dg P := by
        rw [Finset.sum_biUnion]
        intro Q₁ _ Q₂ _ hne
        change Disjoint (T Q₁) (T Q₂)
        refine Finset.disjoint_left.mpr fun P h1 h2 => hne ?_
        simp only [hT, Finset.mem_filter] at h1 h2
        exact (hE P h1.2.1).unique h1.2.2 h2.2.2
    _ ≤ ∑ P ∈ Dg.support.filter ((ChartDomain A · (x : F))), Dg P := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro P hP
          rw [Finset.mem_biUnion] at hP
          obtain ⟨Q, -, hPQ⟩ := hP
          simp only [hT, Finset.mem_filter] at hPQ
          exact Finset.mem_filter.mpr ⟨hPQ.1, hPQ.2.1⟩
        · intro P hP _
          rw [hDg, principalOrderDivisor_apply]
          obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hP).2
          exact P.ord_nonneg_of_mem (P.mem_of_integral_adjoin
            (mem_of_sub_algebraMap_mem_nonunits P ha) hgi)
    _ = chartOrderSum ((ChartDomain A · (x : F))) (g : F) := by
        unfold chartOrderSum
        exact Finset.sum_congr rfl fun P _ => principalOrderDivisor_apply _ _

end
end Dubon2026.SourceCurve.RegularProlongation
