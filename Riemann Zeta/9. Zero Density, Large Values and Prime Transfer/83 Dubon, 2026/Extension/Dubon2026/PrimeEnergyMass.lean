import Dubon2026.SecondPrimeMean
import Dubon2026.DeligneConcentration

namespace Dubon2026
open Filter Set
open scoped Topology
noncomputable section

private theorem dyadic_weight_of_prefix_mean {u : ℕ → ℝ}
    (hu : Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesLE N, u p) / (N:ℝ)) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => (∑ p ∈ dyadicPrimes N, u p) / (N:ℝ)) atTop (𝓝 (1/2)) := by
  have hhalf : Tendsto (fun N : ℕ => (((N / 2 : ℕ) : ℝ) / N)) atTop (𝓝 (1/2)) := by
    have hlow : Tendsto (fun N : ℕ => 1/2 - 1/(N:ℝ)) atTop (𝓝 (1/2)) := by
      simpa only [sub_zero] using
        ((tendsto_const_nhds (x := (1/2:ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
      have hp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have h : (N : ℝ) ≤ 2 * (((N/2 : ℕ) : ℝ)) + 1 := by exact_mod_cast (show N ≤ 2*(N/2)+1 by omega)
      field_simp [hp]
      linarith
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
      have hp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      apply (div_le_iff₀ hp).mpr
      have h : 2 * (((N/2 : ℕ) : ℝ)) ≤ N := by exact_mod_cast (show 2*(N/2) ≤ N by omega)
      linarith
  have hh := hu.sub ((hu.comp tendsto_nat_half_atTop).mul hhalf)
  norm_num at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with N hN
  have hsub : Nat.primesLE (N/2) ⊆ Nat.primesLE N := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans (Nat.div_le_self N 2), (Nat.mem_primesLE.mp hp).2⟩
  rw [dyadicPrimes_eq_sdiff, ← Finset.sum_sdiff hsub (f := u), add_div]
  have hn : ((N/2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show N/2 ≠ 0 by omega)
  field_simp
  ring

/-- The original normalized coefficients carry at least order N/log N squared
mass on every large dyadic prime interval. No good-prime bound is assumed. -/
theorem primitive_dyadic_prime_energy_lower {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    ∀ᶠ N : ℕ in atTop, ((N:ℝ) / Real.log N) / 4 ≤
      ∑ p ∈ dyadicPrimes N, ‖normalizedCuspCoefficients f.toCuspForm p‖^2 := by
  let u := primitivePrimeCharacter f 2
  let w := fun p : ℕ => Real.log p + u p * Real.log p
  have hp : Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesLE N, w p) / (N:ℝ)) atTop (𝓝 1) := by
    have h := tendsto_prime_log_sum_ratio.add (primitive_second_prime_log_mean f hk)
    simpa only [w, u, Finset.sum_add_distrib, add_div, add_zero] using h
  have hd := dyadic_weight_of_prefix_mean hp
  filter_upwards [hd.eventually (lt_mem_nhds (by norm_num : (1/4:ℝ)<1/2)),
    eventually_ge_atTop (2*Q+2)] with N hN hlarge
  have hNr : (1:ℝ) < N := by exact_mod_cast (show 1<N by omega)
  have hw : (∑ p ∈ dyadicPrimes N, w p) ≤
      (∑ p ∈ dyadicPrimes N, ‖normalizedCuspCoefficients f.toCuspForm p‖^2) * Real.log N := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hprime, _, hpN⟩ := mem_dyadicPrimes.mp hp
    have hl := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    have hgood : ¬p ∣ Q := fun he => by
      have := Nat.le_of_dvd (Nat.pos_of_neZero Q) he
      omega
    have heq : w p = ‖normalizedCuspCoefficients f.toCuspForm p‖^2 * Real.log p := by
      dsimp only [w,u]
      rw [primitive_second_character_at_good f hprime hgood]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast hprime.pos)
      (by exact_mod_cast hpN)) (sq_nonneg _)
  have H := (lt_div_iff₀ (by linarith : (0:ℝ)<N)).mp hN
  rw [div_right_comm]
  apply (div_le_iff₀ (Real.log_pos hNr)).mpr
  linarith

end
end Dubon2026
