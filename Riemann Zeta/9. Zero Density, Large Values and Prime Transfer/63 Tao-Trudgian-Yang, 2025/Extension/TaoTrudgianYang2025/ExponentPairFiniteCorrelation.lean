import GuthMaynard.Weyl

/-!
# Exact finite correlations of arbitrary padded source sequences

This is the source-index identity needed before applying an analytic
exponent-pair estimate to a shifted phase. It includes empty overlap.
-/

noncomputable section

open Complex Finset
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem padded_sequence_correlation_eq (a : ℤ → ℂ) (N H h k : ℕ)
    (hh : h < H) (hk : k < H) (hhk : h < k) :
    (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift a N n h)*paddedShift a N n k) =
      ∑ m ∈ Finset.range (N-(k-h)), star (a m)*a (m+(k-h)) := by
  unfold paddedShift
  let s := (Finset.Ico (-(H : Int)) N).filter (fun n =>
    n + (h : Int) ∈ Finset.Ico (0 : Int) N ∧
      n + (k : Int) ∈ Finset.Ico (0 : Int) N)
  have hrestrict :
      (∑ n ∈ Finset.Ico (-(H : Int)) N,
        star (if n + (h : Int) ∈ Finset.Ico (0 : Int) N then
          a (n + h) else 0) *
        (if n + (k : Int) ∈ Finset.Ico (0 : Int) N then
          a (n + k) else 0)) =
      ∑ n ∈ s, star (a (n + h)) *
        a (n + k) := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hhmem : n + (h : Int) ∈ Finset.Ico (0 : Int) N
    · by_cases hkmem : n + (k : Int) ∈ Finset.Ico (0 : Int) N
      · simp [hhmem, hkmem]
      · simp [hhmem, hkmem]
    · simp [hhmem]
  rw [hrestrict]
  have hsum :
      (∑ n ∈ s,
        star (a (n + h)) *
          a (n + k)) =
        ∑ m ∈ Finset.range (N - (k - h)),
          star (a m) *
            a (m + (k - h)) := by
    apply Finset.sum_bij (fun n _hn => Int.toNat (n + h))
    case hi =>
      intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hnh := Finset.mem_Ico.mp hnData.2.1
      have hnk := Finset.mem_Ico.mp hnData.2.2
      apply Finset.mem_range.mpr
      have heq : n + (k : Int) = (n + h) + (k - h : Nat) := by
        omega
      rw [heq] at hnk
      have hcast : Int.toNat (n + h) + (k - h) < N := by
        have hto : ((Int.toNat (n + h) : Nat) : Int) = n + h :=
          Int.toNat_of_nonneg hnh.1
        have hcastInt : ((Int.toNat (n + h) + (k - h) : Nat) : Int) < (N : Int) := by
          push_cast
          rw [hto]
          exact hnk.2
        exact_mod_cast hcastInt
      omega
    case i_inj =>
      intro n₁ hn₁ n₂ hn₂ heq
      have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₁).2.1).1
      have h2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₂).2.1).1
      have heqInt := congrArg (fun m : Nat => (m : Int)) heq
      change ((Int.toNat (n₁ + h) : Nat) : Int) =
        ((Int.toNat (n₂ + h) : Nat) : Int) at heqInt
      rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at heqInt
      omega
    case i_surj =>
      intro m hm
      have hm' := Finset.mem_range.mp hm
      refine ⟨(m : Int) - h, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_Ico.mpr
          constructor
          · have := hh
            omega
          · omega
        · constructor
          · apply Finset.mem_Ico.mpr
            constructor
            · omega
            · have hmk : m + (k - h) < N := by omega
              push_cast at hmk ⊢
              omega
          · apply Finset.mem_Ico.mpr
            constructor
            · omega
            · have hmk : m + (k - h) < N := by omega
              push_cast at hmk ⊢
              omega
      · simp
    case h =>
      intro n hn
      have hnonneg := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).2.1).1
      have hnat : ((Int.toNat (n + h) : Nat) : Int) = n + h := Int.toNat_of_nonneg hnonneg
      congr 2
      · rw [hnat]
      · rw [hnat]
        omega
  exact hsum

theorem padded_sequence_correlation_reverse (a : ℤ → ℂ) (N H h k : ℕ) :
    (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift a N n h)*paddedShift a N n k) =
    star (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift a N n k)*paddedShift a N n h) := by
  change _ = (starRingEnd ℂ) _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  change star (paddedShift a N n h)*paddedShift a N n k =
    star (star (paddedShift a N n k)*paddedShift a N n h)
  rw [star_mul',star_star]
  ring

end TaoTrudgianYang2025
