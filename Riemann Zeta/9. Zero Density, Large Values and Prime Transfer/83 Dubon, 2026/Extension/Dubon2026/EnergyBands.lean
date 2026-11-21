import Dubon2026.DeligneConcentration
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Dubon2026
open Filter Set
open scoped Topology
noncomputable section

/-- Number of dyadic size classes needed up to a scaled squared amplitude of the cutoff cubed. -/
def energyBandCount (N : ℕ) := Nat.log 2 (N^3) + 1

private def kept (e : ℕ → ℝ) (N : ℕ) := (dyadicPrimes N).filter fun p => 1 ≤ N * e p
private def bucket (e : ℕ → ℝ) (N p : ℕ) := Nat.log 2 ⌊N * e p⌋₊
private def band (e : ℕ → ℝ) (N j : ℕ) := (kept e N).filter fun p => bucket e N p = j
private theorem max_band (e : ℕ → ℝ) (N : ℕ) :
    ∃ j ∈ Finset.range (energyBandCount N), ∀ i ∈ Finset.range (energyBandCount N),
      (∑ p ∈ band e N i, e p) ≤ ∑ p ∈ band e N j, e p :=
  Finset.exists_max_image _ _ ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩

/-- Choose the amplitude class carrying the largest total squared coefficient. -/
def maximalEnergyBand (e : ℕ → ℝ) (N : ℕ) := band e N (Classical.choose (max_band e N))

theorem maximalEnergyBand_subset (e : ℕ → ℝ) (N : ℕ) : maximalEnergyBand e N ⊆ dyadicPrimes N :=
  fun _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1

private theorem bucket_bounds {e : ℕ → ℝ} {N p : ℕ} (hp : p ∈ kept e N) :
    (2:ℝ)^(bucket e N p) ≤ N * e p ∧ N * e p < 2 * (2:ℝ)^(bucket e N p) := by
  have h := (Finset.mem_filter.mp hp).2
  have h0 := Nat.floor_pos.mpr h
  have hl : (2:ℝ)^(bucket e N p) ≤ (⌊N * e p⌋₊ : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 h0.ne'
  have hu : (⌊N * e p⌋₊ : ℝ) + 1 ≤ 2 ^ (bucket e N p + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) ⌊N * e p⌋₊
  refine ⟨hl.trans (Nat.floor_le (by linarith)), ?_⟩
  simpa only [pow_succ, mul_comm] using (Nat.lt_floor_add_one (N * e p)).trans_le hu

theorem maximalEnergyBand_comparable {e : ℕ → ℝ} {N p q : ℕ}
    (hp : p ∈ maximalEnergyBand e N) (hq : q ∈ maximalEnergyBand e N) :
    0 < e q ∧ e p ≤ 2 * e q := by
  obtain ⟨hp', hbp⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq', hbq⟩ := Finset.mem_filter.mp hq
  have hn : (0:ℝ) < N := by
    have h := mem_dyadicPrimes.mp (maximalEnergyBand_subset e N hp)
    exact_mod_cast h.1.pos.trans_le h.2.2
  have h := (Finset.mem_filter.mp hq').2
  have h1 := (bucket_bounds hp').2
  have h2 := (bucket_bounds hq').1
  rw [hbp] at h1
  rw [hbq] at h2
  exact ⟨pos_of_mul_pos_right (by linarith : 0 < (N:ℝ) * e q) hn.le,
    (mul_le_mul_iff_right₀ hn).mp (show (N:ℝ) * e p ≤ N * (2 * e q) by nlinarith only [h1,h2])⟩

/-- Discarding weights below 1/N costs at most one unit of mass. The remaining
mass is split between at most one more than the base-two logarithm of N cubed classes. -/
theorem maximalEnergyBand_mass {e : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hupper : ∀ p ∈ dyadicPrimes N, (N:ℝ) * e p ≤ (N:ℝ)^3) :
    (∑ p ∈ dyadicPrimes N, e p) ≤ 1 + (energyBandCount N : ℝ) * ∑ p ∈ maximalEnergyBand e N, e p := by
  classical
  have hmap : ∀ p ∈ kept e N, bucket e N p ∈ Finset.range (energyBandCount N) := by
    intro p hp
    have h := Nat.floor_le_floor (hupper p (Finset.mem_filter.mp hp).1)
    rw [show (N:ℝ)^3 = ((N^3:ℕ):ℝ) by push_cast; rfl, Nat.floor_natCast] at h
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_monotone h))
  have hsum := Finset.sum_fiberwise_of_maps_to hmap e
  have hmaj := Finset.sum_le_sum (s := Finset.range (energyBandCount N))
    (fun i hi => (Classical.choose_spec (max_band e N)).2 i hi)
  change (∑ i ∈ Finset.range (energyBandCount N), ∑ p ∈ band e N i, e p) = _ at hsum
  rw [hsum] at hmaj
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hmaj
  let S := (dyadicPrimes N).filter fun p => ¬ 1 ≤ N * e p
  have hs : S ⊆ Finset.Icc 1 N := fun p hp => by
    have h := mem_dyadicPrimes.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_Icc.mpr ⟨h.1.one_le,h.2.2⟩
  have hcard : (S.card : ℝ) ≤ N := by exact_mod_cast (show S.card ≤ N by simpa using Finset.card_le_card hs)
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hsmall : (∑ p ∈ S, e p) ≤ 1 := by
    calc
      _ ≤ ∑ _p ∈ S, 1 / (N:ℝ) := Finset.sum_le_sum fun p hp => (le_div_iff₀ hn).mpr (by
        have h := lt_of_not_ge (Finset.mem_filter.mp hp).2
        linarith [mul_comm (N:ℝ) (e p)])
      _ ≤ 1 := by simp only [Finset.sum_const,nsmul_eq_mul, mul_one_div]; exact (div_le_one hn).mpr hcard
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := dyadicPrimes N) (fun p => 1 ≤ N * e p) e
  change (∑ p ∈ kept e N, e p) + (∑ p ∈ S, e p) = _ at hsplit
  unfold maximalEnergyBand
  linarith

end
end Dubon2026
