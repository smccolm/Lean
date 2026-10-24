import Dubon2026.SourceJointReductionFrame

/-! DUB-17/18 -> Kummer power lifting -> sum-of-genera inequality ->
joint residue dimension. Joint coordinate-power independence passes to the
actual coordinate field through the pinned fraction-ring independence API.
This avoids a second rational-denominator independence proof. -/
namespace Dubon2026.SourceCurve.RegularProlongation.Joint
noncomputable section
variable {L F : Type*} [Field L] [Field F] [Algebra L F]

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem linearIndependent_adjoinField_of_powers {J : Type*} (f : F) (z : J → F)
    (h2 : LinearIndependent L (fun p : ℕ × J => f ^ p.1 * z p.2)) :
    LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z := by
  classical
  apply (LinearIndependent.iff_fractionRing (Algebra.adjoin L ({f} : Set F))
    (IntermediateField.adjoin L ({f} : Set F))).mp
  rw [linearIndependent_iff']
  intro t g hsum
  have hg : ∀ i, ∃ p : Polynomial L, Polynomial.aeval f p = (g i : F) := fun i => by
    have h : (g i : F) ∈ (Polynomial.aeval (R := L) f).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact (g i).2
    exact (AlgHom.mem_range _).1 h
  choose p hp using hg
  set N := t.sup (fun i => (p i).natDegree) + 1
  have hlt : ∀ i ∈ t, (p i).natDegree < N := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (p i).natDegree) hi)
  have hzero := linearIndependent_iff'.mp h2 (Finset.range N ×ˢ t)
    (fun q => (p q.2).coeff q.1) ?_
  · intro i hi
    have hpi : p i = 0 := by
      ext j
      by_cases hj : j < N
      · exact hzero (j, i) (Finset.mk_mem_product (Finset.mem_range.mpr hj) hi)
      · rw [Polynomial.coeff_zero]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_lt_of_le (hlt i hi) (not_lt.mp hj))
    apply Subtype.ext
    rw [← hp i, hpi, map_zero]
    rfl
  · rw [Finset.sum_product_right, ← hsum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Subalgebra.smul_def, ← hp i, Polynomial.aeval_eq_sum_range' (hlt i hi), Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul]
    exact (smul_mul_assoc _ _ _).symm

end
end Dubon2026.SourceCurve.RegularProlongation.Joint
