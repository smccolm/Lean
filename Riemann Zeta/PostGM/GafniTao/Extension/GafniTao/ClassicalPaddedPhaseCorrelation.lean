import GafniTao.ClassicalA2BLogCurvature

/-!
# Exact zero-padded correlations for an arbitrary real phase

This module separates the finite reindexing in van der Corput's `A` process
from the analytic shape of the phase.  It is used below with the first
logarithmic difference as the input phase.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def integerPhaseTerm (F : ℝ → ℝ) (n : ℤ) : ℂ :=
  unitaryPhase (F n)

@[simp] theorem norm_integerPhaseTerm (F : ℝ → ℝ) (n : ℤ) :
    ‖integerPhaseTerm F n‖ = 1 := by
  simp [integerPhaseTerm]

noncomputable def phaseForwardDifference
    (F : ℝ → ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  F x - F (x + d)

theorem padded_phase_correlation_eq
    (F : ℝ → ℝ) (N H h k : ℕ)
    (hk : k < H) (hhk : h < k) :
    (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift (integerPhaseTerm F) N n h) *
        paddedShift (integerPhaseTerm F) N n k) =
      star (∑ m ∈ Finset.range (N - (k - h)),
        unitaryPhase (phaseForwardDifference F (k - h) m)) := by
  unfold paddedShift
  let s := (Finset.Ico (-(H : ℤ)) N).filter (fun n =>
    n + (h : ℤ) ∈ Finset.Ico (0 : ℤ) N ∧
      n + (k : ℤ) ∈ Finset.Ico (0 : ℤ) N)
  have hrestrict :
      (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
        star (if n + (h : ℤ) ∈ Finset.Ico (0 : ℤ) N then
          integerPhaseTerm F (n + h) else 0) *
        (if n + (k : ℤ) ∈ Finset.Ico (0 : ℤ) N then
          integerPhaseTerm F (n + k) else 0)) =
      ∑ n ∈ s, star (integerPhaseTerm F (n + h)) *
        integerPhaseTerm F (n + k) := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hhmem : n + (h : ℤ) ∈ Finset.Ico (0 : ℤ) N
    · by_cases hkmem : n + (k : ℤ) ∈ Finset.Ico (0 : ℤ) N
      · simp [hhmem, hkmem]
      · simp [hhmem, hkmem]
    · simp [hhmem]
  rw [hrestrict]
  have hsum :
      (∑ n ∈ s,
        star (integerPhaseTerm F (n + h)) * integerPhaseTerm F (n + k)) =
        ∑ m ∈ Finset.range (N - (k - h)),
          star (integerPhaseTerm F m) *
            integerPhaseTerm F (m + (k - h)) := by
    apply Finset.sum_bij (fun n _hn => Int.toNat (n + h))
    case hi =>
      intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hnh := Finset.mem_Ico.mp hnData.2.1
      have hnk := Finset.mem_Ico.mp hnData.2.2
      apply Finset.mem_range.mpr
      have heq : n + (k : ℤ) = (n + h) + (k - h : ℕ) := by omega
      rw [heq] at hnk
      have hto : ((Int.toNat (n + h) : ℕ) : ℤ) = n + h :=
        Int.toNat_of_nonneg hnh.1
      have hcastInt :
          ((Int.toNat (n + h) + (k - h) : ℕ) : ℤ) < (N : ℤ) := by
        push_cast
        rw [hto]
        exact hnk.2
      have hcast : Int.toNat (n + h) + (k - h) < N := by
        exact_mod_cast hcastInt
      omega
    case i_inj =>
      intro n₁ hn₁ n₂ hn₂ heq
      have h₁ := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₁).2.1).1
      have h₂ := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₂).2.1).1
      have heqInt := congrArg (fun m : ℕ => (m : ℤ)) heq
      change ((Int.toNat (n₁ + h) : ℕ) : ℤ) =
        ((Int.toNat (n₂ + h) : ℕ) : ℤ) at heqInt
      rw [Int.toNat_of_nonneg h₁, Int.toNat_of_nonneg h₂] at heqInt
      omega
    case i_surj =>
      intro m hm
      have hm' := Finset.mem_range.mp hm
      refine ⟨(m : ℤ) - h, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_Ico.mpr
          constructor <;> omega
        · constructor
          · apply Finset.mem_Ico.mpr
            constructor <;> omega
          · apply Finset.mem_Ico.mpr
            constructor <;> omega
      · simp
    case h =>
      intro n hn
      have hnonneg := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).2.1).1
      have hnat : ((Int.toNat (n + h) : ℕ) : ℤ) = n + h :=
        Int.toNat_of_nonneg hnonneg
      congr 2
      · rw [hnat]
      · rw [hnat]
        omega
  rw [hsum]
  change (∑ m ∈ Finset.range (N - (k - h)),
      star (integerPhaseTerm F m) * integerPhaseTerm F (m + (k - h))) =
    (starRingEnd ℂ) (∑ m ∈ Finset.range (N - (k - h)),
      unitaryPhase (phaseForwardDifference F (k - h) m))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  change star (integerPhaseTerm F m) * integerPhaseTerm F (m + (k - h)) =
    star (unitaryPhase (phaseForwardDifference F (k - h) m))
  unfold integerPhaseTerm phaseForwardDifference
  rw [unitaryPhase_sub]
  rw [star_mul']
  rw [show star ((starRingEnd ℂ)
      (unitaryPhase (F ((m : ℝ) + (k - h : ℕ))))) =
      unitaryPhase (F ((m : ℝ) + (k - h : ℕ))) by
    change star (star (unitaryPhase
      (F ((m : ℝ) + (k - h : ℕ))))) = _
    rw [star_star]]
  congr 2
  push_cast
  rw [Nat.cast_sub hhk.le]

theorem integerPhaseSum_eq_range (F : ℝ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Ico (0 : ℤ) N, integerPhaseTerm F n) =
      ∑ n ∈ Finset.range N, unitaryPhase (F n) := by
  apply Finset.sum_bij (fun n _hn => Int.toNat n)
  case hi =>
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    apply Finset.mem_range.mpr
    have hcast : ((Int.toNat n : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn'.1
    have : ((Int.toNat n : ℕ) : ℤ) < (N : ℤ) := by
      rw [hcast]
      exact hn'.2
    exact_mod_cast this
  case i_inj =>
    intro n₁ hn₁ n₂ hn₂ heq
    have h₁ := (Finset.mem_Ico.mp hn₁).1
    have h₂ := (Finset.mem_Ico.mp hn₂).1
    have hcast := congrArg (fun m : ℕ => (m : ℤ)) heq
    change ((Int.toNat n₁ : ℕ) : ℤ) = ((Int.toNat n₂ : ℕ) : ℤ) at hcast
    rw [Int.toNat_of_nonneg h₁, Int.toNat_of_nonneg h₂] at hcast
    exact hcast
  case i_surj =>
    intro m hm
    refine ⟨(m : ℤ), ?_, by simp⟩
    apply Finset.mem_Ico.mpr
    constructor
    · positivity
    · exact_mod_cast Finset.mem_range.mp hm
  case h =>
    intro n hn
    unfold integerPhaseTerm
    congr 2
    have hn0 := (Finset.mem_Ico.mp hn).1
    have hcast : ((Int.toNat n : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
    exact_mod_cast hcast.symm

#print axioms padded_phase_correlation_eq
#print axioms integerPhaseSum_eq_range

end

end GafniTao
