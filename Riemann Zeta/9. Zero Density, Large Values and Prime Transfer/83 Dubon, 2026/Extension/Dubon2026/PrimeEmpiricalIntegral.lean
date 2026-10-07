import Dubon2026.PrimeEmpirical
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Exact finite averages for the genuine prime empirical probability -/

namespace Dubon2026

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

/-- The uniform finite probability integrates every function as its genuine finite average. -/
theorem integral_uniform_finset_real {s : Finset ℕ} (hs : s.Nonempty) (g : ℕ → ℝ) :
    (∫ n, g n ∂(PMF.uniformOfFinset s hs).toMeasure) = (∑ n ∈ s, g n) / s.card := by
  classical
  have he : (PMF.uniformOfFinset s hs).toMeasure.restrict (s : Set ℕ) =
      (PMF.uniformOfFinset s hs).toMeasure := by
    simpa only [PMF.support_uniformOfFinset] using
      (PMF.uniformOfFinset s hs).restrict_toMeasure_support
  calc
    _ = ∫ n in s, g n ∂(PMF.uniformOfFinset s hs).toMeasure := by rw [he]
    _ = ∑ n ∈ s, (PMF.uniformOfFinset s hs).toMeasure.real {n} • g n :=
      setIntegral_finset s IntegrableOn.finset
    _ = ∑ n ∈ s, (s.card : ℝ)⁻¹ * g n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n),
        PMF.uniformOfFinset_apply_of_mem hs hn]
      simp
    _ = _ := by rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

/-- The actual empirical coefficient integral is the literal prime average, with denominator pi(N). -/
theorem integral_primeEmpirical {x : ℕ → ℝ} {N : ℕ} (hN : 2 ≤ N)
    {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ t, g t ∂(primeEmpirical x N : Measure ℝ)) =
      (∑ p ∈ Nat.primesLE N, g (x p)) / Nat.primeCounting N := by
  classical
  have h : (Nat.primesLE N).Nonempty := ⟨2, Nat.mem_primesLE.mpr ⟨hN, Nat.prime_two⟩⟩
  simp only [primeEmpirical, dif_pos h]
  change (∫ t, g t ∂Measure.map x (PMF.uniformOfFinset (Nat.primesLE N) h).toMeasure) = _
  rw [integral_map (measurable_of_countable x).aemeasurable hg.aestronglyMeasurable,
    integral_uniform_finset_real, Nat.primesLE_card_eq_primeCounting]

/-- A bound on the actual prime values supplies support of every empirical probability, including its empty initial ranges. -/
theorem primeEmpirical_ae_mem_Icc {x : ℕ → ℝ} {a b : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b) (hx : ∀ p, Nat.Prime p → x p ∈ Icc a b) (N : ℕ) :
    ∀ᵐ t ∂(primeEmpirical x N : Measure ℝ), t ∈ Icc a b := by
  classical
  by_cases hs : (Nat.primesLE N).Nonempty
  · simp only [primeEmpirical, dif_pos hs]
    change ∀ᵐ t ∂Measure.map x (PMF.uniformOfFinset (Nat.primesLE N) hs).toMeasure,
      t ∈ Icc a b
    apply (ae_map_iff (p := fun t : ℝ => t ∈ Icc a b)
      (measurable_of_countable x).aemeasurable measurableSet_Icc).mpr
    have he : (PMF.uniformOfFinset (Nat.primesLE N) hs).toMeasure.restrict
        (Nat.primesLE N : Set ℕ) = (PMF.uniformOfFinset (Nat.primesLE N) hs).toMeasure := by
      simpa only [PMF.support_uniformOfFinset] using
        (PMF.uniformOfFinset (Nat.primesLE N) hs).restrict_toMeasure_support
    have hp : ∀ᵐ p ∂(PMF.uniformOfFinset (Nat.primesLE N) hs).toMeasure,
        p ∈ (Nat.primesLE N : Set ℕ) := by
      rw [← he]
      exact ae_restrict_mem (Nat.primesLE N).measurableSet
    filter_upwards [hp] with p hp
    exact hx p (Nat.mem_primesLE.mp hp).2
  · simp only [primeEmpirical, dif_neg hs]
    change ∀ᵐ t ∂Measure.dirac (0 : ℝ), t ∈ Icc a b
    exact (ae_dirac_iff (p := fun t : ℝ => t ∈ Icc a b) measurableSet_Icc).mpr ⟨ha, hb⟩

end
end Dubon2026
