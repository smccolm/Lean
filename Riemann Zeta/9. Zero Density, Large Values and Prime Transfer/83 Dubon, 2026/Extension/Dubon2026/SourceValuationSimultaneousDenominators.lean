import Mathlib

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
actual extending residue fields. Finite valuation approximation supplies
independent residue vectors; the degree-q cover then forces each residue
extension to have degree one. Adapted from the frozen Apache-2.0 FLT
finite-valuation approximation proof (6e837e75355538c7f80bab5b956861e86c4eacc2).
No value-group coarsening or arbitrary-constant normalization is imported. -/
namespace Dubon2026.SourceCurve.ValuationApproximation
noncomputable section
open IsLocalRing ValuationSubring

theorem pow_eq_self_of_orderOf_dvd {M : Type*} [Monoid M] (u : M) {D : ℕ}
    (hD : orderOf u ∣ D) (N : ℕ) : u ^ (1 + N * D) = u := by
  have h1 : u ^ D = 1 := orderOf_dvd_iff_pow_eq_one.mp hD
  rw [pow_add, pow_one, pow_mul', h1, one_pow, mul_one]

theorem eq_of_pow_eq_pow_of_not_isOfFinOrder {κ : Type*} [Field κ] {u : κ} (hu : u ≠ 0)
    (hfin : ¬ IsOfFinOrder u) {a b : ℕ} (h : u ^ a = u ^ b) : a = b := by
  wlog hab : a ≤ b generalizing a b
  · exact (this h.symm (le_of_not_ge hab)).symm
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add] at h
  have hc : u ^ c = 1 := by
    have h' : u ^ a * u ^ c = u ^ a * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel₀ (pow_ne_zero a hu) h'
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · omega
  · exact absurd (isOfFinOrder_iff_pow_eq_one.mpr ⟨c, hpos, hc⟩) hfin

theorem exists_exponent {ι : Type*} [Fintype ι] (κ : ι → Type*) [∀ j, Field (κ j)]
    (u : ∀ j, κ j) (hu : ∀ j, u j ≠ 0) :
    ∃ m : ℕ, 2 ≤ m ∧ ∀ j, 1 - u j + u j ^ m ≠ 0 := by
  classical
  let d : ι → ℕ := fun j => if IsOfFinOrder (u j) then orderOf (u j) else 1
  set D : ℕ := ∏ j, d j with hDdef
  have hDpos : 0 < D := Finset.prod_pos fun j _ => by
    simp only [d]
    split_ifs with h
    · exact h.orderOf_pos
    · exact one_pos
  have hdvd : ∀ j, IsOfFinOrder (u j) → orderOf (u j) ∣ D := fun j hj => by
    have h := Finset.dvd_prod_of_mem d (Finset.mem_univ j)
    simpa [d, hj] using h
  let m : ℕ → ℕ := fun N => 1 + (N + 1) * D
  have hm2 : ∀ N, 2 ≤ m N := fun N => by
    show 2 ≤ 1 + (N + 1) * D
    nlinarith
  have hminj : ∀ N N', m N = m N' → N = N' := fun N N' h => by
    have h' : (N + 1) * D = (N' + 1) * D := by
      change 1 + (N + 1) * D = 1 + (N' + 1) * D at h; omega
    have := Nat.eq_of_mul_eq_mul_right hDpos h'
    omega
  have htors : ∀ j, IsOfFinOrder (u j) → ∀ N, 1 - u j + u j ^ m N ≠ 0 := fun j hj N => by
    have h : u j ^ m N = u j := pow_eq_self_of_orderOf_dvd (u j) (hdvd j hj) (N + 1)
    rw [h, sub_add_cancel]
    exact one_ne_zero
  have hnt : ∀ j, ¬ IsOfFinOrder (u j) → ∀ N N',
      1 - u j + u j ^ m N = 0 → 1 - u j + u j ^ m N' = 0 → N = N' := by
    intro j hj N N' h1 h2
    apply hminj
    apply eq_of_pow_eq_pow_of_not_isOfFinOrder (hu j) hj
    have e1 : u j ^ m N = u j - 1 := by linear_combination h1
    have e2 : u j ^ m N' = u j - 1 := by linear_combination h2
    rw [e1, e2]
  by_contra hcon
  push Not at hcon
  have hex : ∀ N : Fin (Fintype.card ι + 1), ∃ j, 1 - u j + u j ^ m N = 0 :=
    fun N => hcon (m N) (hm2 N)
  choose f hf using hex
  obtain ⟨N, N', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  by_cases hj : IsOfFinOrder (u (f N))
  · exact htors _ hj N (hf N)
  · have h2 : 1 - u (f N) + u (f N) ^ m N' = 0 := by rw [heq]; exact hf N'
    exact hne (Fin.ext (hnt _ hj N N' (hf N) h2))

variable {K : Type*} [Field K] {ι : Type*}

theorem exists_mul_mem_forall [Fintype ι] (R : ι → ValuationSubring K) (x : K) :
    ∃ t : K, (∀ j, t ∈ R j) ∧ (∀ j, t * x ∈ R j) ∧
      (∀ j, x ∈ R j → (R j).valuation t = 1) := by
  classical

  let u : ∀ j, ResidueField (R j) := fun j =>
    if h : (R j).valuation x = 1 then
      IsLocalRing.residue (R j) ⟨x, ((R j).valuation_le_one_iff x).mp h.le⟩ else 1
  have hu : ∀ j, u j ≠ 0 := fun j => by
    by_cases h : (R j).valuation x = 1
    · simp only [u, dif_pos h]
      rw [ne_eq, residue_eq_zero_iff, valuation_lt_one_iff]
      exact fun hlt => hlt.ne h
    · simp only [u, dif_neg h]; exact one_ne_zero
  obtain ⟨m, hm2, hm⟩ := exists_exponent (fun j => ResidueField (R j)) u hu
  set P : K := 1 - x + x ^ m with hP

  have hA : ∀ j, x ∈ R j → (R j).valuation P = 1 := by
    intro j hxj
    rcases lt_or_eq_of_le (((R j).valuation_le_one_iff x).mpr hxj) with hlt | heq
    · have h1 : (R j).valuation (x ^ m - x) < 1 := by
        apply Valuation.map_sub_lt
        · rw [map_pow]; exact pow_lt_one₀ zero_le' hlt (by omega)
        · exact hlt
      have : P = 1 + (x ^ m - x) := by rw [hP]; ring
      rw [this]
      exact Valuation.map_one_add_of_lt _ h1
    · set xj : R j := ⟨x, hxj⟩ with hxjdef
      have hPj : P = ((1 - xj + xj ^ m : R j) : K) := by rw [hP]; push_cast; rfl
      rw [hPj]
      apply ((R j).valuation_eq_one_iff _).mp
      rw [← residue_ne_zero_iff_isUnit]
      have hres : IsLocalRing.residue (R j) xj = u j := by
        simp only [u, dif_pos heq]
        rfl
      rw [map_add, map_sub, map_one, map_pow, hres]
      exact hm j

  have hB : ∀ j, x ∉ R j → (R j).valuation P⁻¹ < 1 ∧ (R j).valuation (P⁻¹ * x) < 1 := by
    intro j hxj
    have hx0 : x ≠ 0 := by rintro rfl; exact hxj (ValuationSubring.zero_mem _)
    have hy : x⁻¹ ∈ R j := ((R j).mem_or_inv_mem x).resolve_left hxj
    have hylt : (R j).valuation x⁻¹ < 1 := by
      rcases lt_or_eq_of_le (((R j).valuation_le_one_iff _).mpr hy) with h | h
      · exact h
      · exfalso; apply hxj
        rw [← (R j).valuation_le_one_iff]
        rw [map_inv₀, inv_eq_one] at h
        exact h.le
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    set Q : K := 1 + (x⁻¹ ^ (n + 2) - x⁻¹ ^ (n + 1)) with hQ
    have hQv : (R j).valuation Q = 1 := by
      apply Valuation.map_one_add_of_lt
      apply Valuation.map_sub_lt
      · rw [map_pow]; exact pow_lt_one₀ zero_le' hylt (by omega)
      · rw [map_pow]; exact pow_lt_one₀ zero_le' hylt (by omega)
    have h1 : x ^ (n + 2) * x⁻¹ ^ (n + 2) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hx0, one_pow]
    have h2 : x ^ (n + 2) * x⁻¹ ^ (n + 1) = x := by
      rw [pow_succ, mul_comm (x ^ (n + 1)) x, mul_assoc, ← mul_pow, mul_inv_cancel₀ hx0, one_pow,
        mul_one]
    have h3 : x⁻¹ ^ (n + 2) * x = x⁻¹ ^ (n + 1) := by
      rw [pow_succ, mul_assoc, inv_mul_cancel₀ hx0, mul_one]
    have hPQ : P = x ^ (n + 2) * Q := by
      rw [hP, hQ]
      linear_combination (-1 : K) * h1 + h2
    have ht : P⁻¹ = x⁻¹ ^ (n + 2) * Q⁻¹ := by
      rw [hPQ, mul_inv, ← inv_pow]
    have htx : P⁻¹ * x = x⁻¹ ^ (n + 1) * Q⁻¹ := by
      rw [ht, mul_right_comm, h3]
    refine ⟨?_, ?_⟩
    · rw [ht, map_mul, map_inv₀, hQv, inv_one, mul_one, map_pow]
      exact pow_lt_one₀ zero_le' hylt (by omega)
    · rw [htx, map_mul, map_inv₀, hQv, inv_one, mul_one, map_pow]
      exact pow_lt_one₀ zero_le' hylt (by omega)
  refine ⟨P⁻¹, fun j => ?_, fun j => ?_, fun j hxj => ?_⟩
  · by_cases hxj : x ∈ R j
    · rw [← (R j).valuation_le_one_iff, map_inv₀, hA j hxj, inv_one]
    · rw [← (R j).valuation_le_one_iff]; exact (hB j hxj).1.le
  · by_cases hxj : x ∈ R j
    · rw [← (R j).valuation_le_one_iff, map_mul, map_inv₀, hA j hxj, inv_one, one_mul]
      exact ((R j).valuation_le_one_iff x).mpr hxj
    · rw [← (R j).valuation_le_one_iff]; exact (hB j hxj).2.le
  · rw [map_inv₀, hA j hxj, inv_one]


end
end Dubon2026.SourceCurve.ValuationApproximation
