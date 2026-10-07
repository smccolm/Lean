import Dubon2026.DyadicPrimeGrowth

/-! # Turning a prime-density statement into the literal selected dyadic block

The density assumption is a separate arithmetic input. The dyadic factor 1/2,
cardinality growth and logarithmic normalization are deduced using the audited PNT.
-/

namespace Dubon2026

open Filter Set
open scoped Topology

noncomputable section

/-- All primes up to N satisfying the indicated arithmetic selection. -/
def selectedPrimesUpTo (S : ℕ → Prop) (N : ℕ) : Finset ℕ := by
  classical
  exact (Nat.primesLE N).filter S

/-- The literal selected subset of the open/closed source dyadic block. -/
def selectedDyadicPrimes (S : ℕ → Prop) (N : ℕ) : Finset ℕ := by
  classical
  exact (dyadicPrimes N).filter S

theorem mem_selectedPrimesUpTo {S : ℕ → Prop} {N p : ℕ} :
    p ∈ selectedPrimesUpTo S N ↔ p ≤ N ∧ Nat.Prime p ∧ S p := by
  classical
  simp only [selectedPrimesUpTo, Finset.mem_filter, Nat.mem_primesLE]
  tauto

theorem mem_selectedDyadicPrimes {S : ℕ → Prop} {N p : ℕ} :
    p ∈ selectedDyadicPrimes S N ↔
      (Nat.Prime p ∧ (N : ℝ) / 2 < p ∧ p ≤ N) ∧ S p := by
  classical
  simp only [selectedDyadicPrimes, Finset.mem_filter, mem_dyadicPrimes]

theorem isolatedPrimeBlocks_selectedDyadicPrimes (S : ℕ → Prop) :
    IsolatedPrimeBlocks (selectedDyadicPrimes S) :=
  fun _ _ hp => (mem_selectedDyadicPrimes.mp hp).1

theorem selectedPrimesUpTo_mono (S : ℕ → Prop) {L N : ℕ} (h : L ≤ N) :
    selectedPrimesUpTo S L ⊆ selectedPrimesUpTo S N := by
  intro p hp
  obtain ⟨hpL, hp, hS⟩ := mem_selectedPrimesUpTo.mp hp
  exact mem_selectedPrimesUpTo.mpr ⟨hpL.trans h, hp, hS⟩

theorem selectedDyadicPrimes_eq_sdiff (S : ℕ → Prop) (N : ℕ) :
    selectedDyadicPrimes S N = selectedPrimesUpTo S N \ selectedPrimesUpTo S (N / 2) := by
  classical
  ext p
  simp only [selectedDyadicPrimes, Finset.mem_filter, dyadicPrimes_eq_sdiff,
    Finset.mem_sdiff, Nat.mem_primesLE, mem_selectedPrimesUpTo]
  tauto

theorem card_selectedDyadicPrimes (S : ℕ → Prop) (N : ℕ) :
    (selectedDyadicPrimes S N).card =
      (selectedPrimesUpTo S N).card - (selectedPrimesUpTo S (N / 2)).card := by
  rw [selectedDyadicPrimes_eq_sdiff,
    Finset.card_sdiff_of_subset (selectedPrimesUpTo_mono S (Nat.div_le_self N 2))]

theorem tendsto_nat_half_atTop : Tendsto (fun N : ℕ => N / 2) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨2 * b, ?_⟩
  intro N hN
  omega

/-- The arithmetic input is the natural density among primes, not the desired dyadic conclusion. -/
theorem selected_dyadic_density {S : ℕ → Prop} {η : ℝ}
    (hd : Tendsto (fun N : ℕ => ((selectedPrimesUpTo S N).card : ℝ) /
      Nat.primeCounting N) atTop (𝓝 η)) :
    Tendsto (fun N : ℕ => ((selectedDyadicPrimes S N).card : ℝ) /
      ((N : ℝ) / Real.log N)) atTop (𝓝 (η / 2)) := by
  have hf : Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) /
      ((N : ℝ) / Real.log N)) atTop (𝓝 1) := by
    simpa only [one_mul, Nat.floor_natCast] using
      tendsto_primeCounting_scaled (c := 1) (by norm_num)
  have hh : Tendsto (fun N : ℕ => (Nat.primeCounting (N / 2) : ℝ) /
      ((N : ℝ) / Real.log N)) atTop (𝓝 (1 / 2)) := by
    have he (N : ℕ) : (1 / 2 : ℝ) * N = (N : ℝ) / (2 : ℕ) := by push_cast; ring
    simpa only [he, Nat.floor_div_eq_div] using
      tendsto_primeCounting_scaled (c := 1 / 2) (by norm_num)
  have hlim := (hd.mul hf).sub ((hd.comp tendsto_nat_half_atTop).mul hh)
  have he : η * 1 - η * (1 / 2) = η / 2 := by ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [Nat.tendsto_primeCounting.eventually_ge_atTop 1,
    (Nat.tendsto_primeCounting.comp tendsto_nat_half_atTop).eventually_ge_atTop 1]
    with N hfull hhalf
  change 1 ≤ Nat.primeCounting (N / 2) at hhalf
  have hp : (Nat.primeCounting N : ℝ) ≠ 0 := by exact_mod_cast (show Nat.primeCounting N ≠ 0 by omega)
  have hq : (Nat.primeCounting (N / 2) : ℝ) ≠ 0 := by
    exact_mod_cast (show Nat.primeCounting (N / 2) ≠ 0 by omega)
  rw [card_selectedDyadicPrimes, Nat.cast_sub
    (Finset.card_le_card (selectedPrimesUpTo_mono S (Nat.div_le_self N 2))), sub_div]
  simp only [Function.comp_def]
  field_simp

/-- Positive density gives the growing number of genuinely selected prime coordinates. -/
theorem tendsto_card_of_positive_prime_scale {Q : ℕ → Finset ℕ} {c : ℝ} (hc : 0 < c)
    (hr : Tendsto (fun N : ℕ => ((Q N).card : ℝ) / ((N : ℝ) / Real.log N))
      atTop (𝓝 c)) : Tendsto (fun N => (Q N).card) atTop atTop := by
  have hh := hr.pos_mul_atTop hc tendsto_nat_div_log_atTop
  have hcast : Tendsto (fun N => ((Q N).card : ℝ)) atTop atTop := by
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    exact div_mul_cancel₀ _ (div_ne_zero (by positivity) (Real.log_pos hNr).ne')
  exact tendsto_natCast_atTop_iff.mp hcast

theorem tendsto_log_card_of_positive_prime_scale {Q : ℕ → Finset ℕ} {c : ℝ} (hc : 0 < c)
    (hr : Tendsto (fun N : ℕ => ((Q N).card : ℝ) / ((N : ℝ) / Real.log N))
      atTop (𝓝 c)) :
    Tendsto (fun N => Real.log (Q N).card / Real.log N) atTop (𝓝 1) := by
  apply tendsto_log_scaled_ratio hc (g := fun N => (N : ℝ) / Real.log N) ?_ hr
    tendsto_log_nat_div_log_ratio
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact div_pos (by positivity) (Real.log_pos hNr)

end

end Dubon2026
