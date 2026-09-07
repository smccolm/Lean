import PrimeShell.F1Verdict
import PrimeShell.KernelSymmetry

namespace PrimeShell

open Zeta23

/-- An actual pair of rows of the pinned Zeta23 dyadic kernel, at the same
dyadic block and the same positive shift, with one row zero and the other
strictly positive.  This discharges the row-variation premise that remained
in the abstract Phase-I F1 obstruction. -/
theorem exists_concrete_literal_kernel_row_variation :
    ∃ k : ℕ,
      concreteDyadicBase < concreteZeroRow ∧
      concreteZeroRow + concreteRowShift ≤ 2 * concreteDyadicBase ∧
      concreteDyadicBase < concretePositiveRow ∧
      concretePositiveRow + concreteRowShift ≤ 2 * concreteDyadicBase ∧
      8 * concreteSourceParams.w ≤
        concreteSourceParams.L (concretePhaseHeight k) ∧
      dyadicShiftKernel
          (concreteSourceParams.PhiR (concretePhaseHeight k))
          (concretePhaseHeight k) concreteZeroRow concreteRowShift = 0 ∧
      0 < dyadicShiftKernel
          (concreteSourceParams.PhiR (concretePhaseHeight k))
          (concretePhaseHeight k) concretePositiveRow concreteRowShift := by
  obtain ⟨k, hwL, hpositive⟩ := eventually_concrete_positive_row.exists
  have hrows := concrete_rows_in_same_dyadic_block
  refine ⟨k, (Finset.mem_Ioc.mp hrows.1).1,
    (Finset.mem_Ioc.mp hrows.2.1).2,
    (Finset.mem_Ioc.mp hrows.2.2.1).1,
    (Finset.mem_Ioc.mp hrows.2.2.2).2, hwL, ?_, hpositive⟩
  apply dyadicShiftKernel_PhiR_eq_zero_of_midpoint_cos_eq_zero
    concreteSourceParams concreteSourceParams_valid hwL
  · rw [show Real.log concreteZeroRow -
        Real.log (concreteZeroRow + concreteRowShift) =
          -(3 * concreteStepLog) by
      rw [← concrete_zero_row_log_step]
      ring]
    exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) concreteStepLog_pos.ne')
  · exact concrete_zero_row_midpoint_cos k

/-- Unconditional F1 FAIL for the literal pinned source kernel.  There is an
explicit height family and a concrete pair of positions in one dyadic block
for which every collapsed shift prefix can vanish while the exact kernel
functional is nonzero.  Hence a prefix-only GM interface cannot be the
Prime-Shell arithmetic consumer. -/
theorem concrete_literal_prefix_only_transfer_fails :
    ∃ k : ℕ,
      ¬ PrefixOnlyTwoPointTransfer
        (fun j => dyadicShiftKernel
          (concreteSourceParams.PhiR (concretePhaseHeight k))
          (concretePhaseHeight k) concreteZeroRow j)
        (fun j => dyadicShiftKernel
          (concreteSourceParams.PhiR (concretePhaseHeight k))
          (concretePhaseHeight k) concretePositiveRow j) := by
  obtain ⟨k, _, _, _, _, _, hzero, hpositive⟩ :=
    exists_concrete_literal_kernel_row_variation
  refine ⟨k, literal_prefix_only_transfer_fails_of_row_variation
    (concreteSourceParams.PhiR (concretePhaseHeight k))
    (concretePhaseHeight k) (n₀ := concreteZeroRow)
    (n₁ := concretePositiveRow) (h := concreteRowShift)
    (by norm_num [concreteRowShift]) ?_⟩
  rw [hzero]
  exact ne_of_lt hpositive

end PrimeShell
