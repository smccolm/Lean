import TaoTrudgianYang2025.SargosSymmetricTwelfth

/-! Removing the actual parity indicators and retaining all square-diagonal sextuples. -/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace TaoTrudgianYang2025

def sargosFullSymmetricTriple (a : ℤ → ℂ) (M H : ℕ) (m : ℤ)
    (t : SargosInitialMomentTuple H 3) : ℂ :=
  ∏ i, sargosPaddedSequence a M (m+(t i:ℤ))*sargosPaddedSequence a M (m-(t i:ℤ))

def sargosFullSextupleCorrelation (a : ℤ → ℂ) (M H : ℕ) : ℝ :=
  ∑ q ∈ sargosSquareDiagonal H,
    ‖∑ m ∈ Finset.Ico (0:ℤ) M,
      sargosFullSymmetricTriple a M H m q.1*conj (sargosFullSymmetricTriple a M H m q.2)‖

theorem sargosFullSextupleCorrelation_nonneg (a : ℤ → ℂ) (M H : ℕ) :
    0 ≤ sargosFullSextupleCorrelation a M H :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem sargosSymmetricTriple_indicator (a : ℤ → ℂ) (M H j : ℕ) (m : ℤ)
    (t : SargosInitialMomentTuple H 3) :
    sargosSymmetricTriple a M H j m t =
      if (∀ i, (t i:ℤ) ∈ sargosPositiveOffsets H j)
      then sargosFullSymmetricTriple a M H m t else 0 := by
  classical
  by_cases ht : ∀ i, (t i:ℤ) ∈ sargosPositiveOffsets H j
  · rw [if_pos ht]
    apply Finset.prod_congr rfl
    intro i hi
    exact if_pos (ht i)
  · rw [if_neg ht]
    push Not at ht
    obtain ⟨i,hi⟩ := ht
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact if_neg hi

theorem sargosSymmetricSextupleCorrelation_le_full (a : ℤ → ℂ) (M H j : ℕ) :
    sargosSymmetricSextupleCorrelation a M H j ≤ sargosFullSextupleCorrelation a M H := by
  apply Finset.sum_le_sum
  intro q hq
  have he (m : ℤ) :
      sargosSymmetricTriple a M H j m q.1*conj (sargosSymmetricTriple a M H j m q.2) =
        if ((∀ i, (q.1 i:ℤ) ∈ sargosPositiveOffsets H j) ∧
          (∀ i, (q.2 i:ℤ) ∈ sargosPositiveOffsets H j)) then
          sargosFullSymmetricTriple a M H m q.1*conj (sargosFullSymmetricTriple a M H m q.2)
        else 0 := by
    rw [sargosSymmetricTriple_indicator,sargosSymmetricTriple_indicator]
    split_ifs <;> simp_all
  by_cases ht : (∀ i, (q.1 i:ℤ) ∈ sargosPositiveOffsets H j) ∧
    (∀ i, (q.2 i:ℤ) ∈ sargosPositiveOffsets H j)
  · simp only [he,if_pos ht,le_refl]
  · simp only [he,if_neg ht,Finset.sum_const_zero,norm_zero]
    exact norm_nonneg _

theorem sargos_finite_sextuple_differencing (a : ℤ → ℂ) {M H : ℕ}
    (hH : 1 ≤ H) (hHM : H ≤ M) :
    ‖∑ m ∈ Finset.Ico (0:ℤ) M, a m‖^12 ≤
      1492992*((M:ℝ)/H)^6*(∑ m ∈ Finset.Ico (0:ℤ) M, ‖a m‖^2)^6+
      (382205952*(M:ℝ)^11/(H:ℝ)^4)*sargosFullSextupleCorrelation a M H := by
  obtain ⟨j,hj,h⟩ := sargos_symmetric_twelfth a hH hHM
  exact h.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (sargosSymmetricSextupleCorrelation_le_full a M H j)
      (by positivity)))

end TaoTrudgianYang2025
