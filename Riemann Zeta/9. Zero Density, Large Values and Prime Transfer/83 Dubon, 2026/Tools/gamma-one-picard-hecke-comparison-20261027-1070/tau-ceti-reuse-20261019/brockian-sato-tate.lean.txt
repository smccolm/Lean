/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open Filter Topology

/-! ## The Sato–Tate measure -/

/-- The density of the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`. -/

theorem sato_tate (W : WeierstrassCurve ℤ) (hST : SatoTateHolds W)
    {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi) :
    Tendsto (fun N : ℕ =>
        (((primesBelow N).filter (fun p => frobeniusAngle W p ∈ Set.Icc a b)).card : ℝ)
          / ((primesBelow N).card : ℝ))
      atTop (𝓝 (∫ x in a..b, satoTateDensity x)) := by
  classical
  rw [integral_satoTateDensity, Metric.tendsto_atTop]
  intro eps heps
  -- choose `delta` so that the Sato–Tate mass of the `delta`-collars is small
  obtain ⟨d1, hd1pos, hd1⟩ :=
    Metric.continuousAt_iff.mp (continuous_satoTateCDF.continuousAt (x := a)) (eps / 4)
      (by linarith)
  obtain ⟨d2, hd2pos, hd2⟩ :=
    Metric.continuousAt_iff.mp (continuous_satoTateCDF.continuousAt (x := b)) (eps / 4)
      (by linarith)
  set delta : ℝ := min d1 d2 / 2 with hdelta
  have hdpos : 0 < delta := by
    have := lt_min hd1pos hd2pos
    simp only [hdelta]
    linarith
  have hdd1 : delta < d1 := by
    have h := min_le_left d1 d2
    simp only [hdelta]
    linarith
  have hdd2 : delta < d2 := by
    have h := min_le_right d1 d2
    simp only [hdelta]
    linarith
  have hFa1 : |satoTateCDF (a - delta) - satoTateCDF a| < eps / 4 := by
    have := hd1 (x := a - delta) (by simp [abs_of_pos hdpos]; linarith)
    simpa [Real.dist_eq] using this
  have hFa2 : |satoTateCDF (a + delta) - satoTateCDF a| < eps / 4 := by
    have := hd1 (x := a + delta) (by simp [abs_of_pos hdpos]; linarith)
    simpa [Real.dist_eq] using this
  have hFb1 : |satoTateCDF (b - delta) - satoTateCDF b| < eps / 4 := by
    have := hd2 (x := b - delta) (by simp [abs_of_pos hdpos]; linarith)
    simpa [Real.dist_eq] using this
  have hFb2 : |satoTateCDF (b + delta) - satoTateCDF b| < eps / 4 := by
    have := hd2 (x := b + delta) (by simp [abs_of_pos hdpos]; linarith)
    simpa [Real.dist_eq] using this
  rw [abs_lt] at hFa1 hFa2 hFb1 hFb2
  -- the two test functions
  set gl : ℝ → ℝ := tent a b delta with hgl
  set gu : ℝ → ℝ := tent (a - delta) (b + delta) delta with hgu
  have hlim_l := hST gl (continuous_tent _ _ _)
  have hlim_u := hST gu (continuous_tent _ _ _)
  rw [Metric.tendsto_atTop] at hlim_l hlim_u
  obtain ⟨N1, hN1⟩ := hlim_l (eps / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := hlim_u (eps / 2) (by linarith)
  refine ⟨max N1 N2, fun N hN => ?_⟩
  have hN1' := hN1 N (le_trans (le_max_left _ _) hN)
  have hN2' := hN2 N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, abs_lt] at hN1' hN2' ⊢
  set S : Finset ℕ := primesBelow N with hS
  set C : ℝ := (((primesBelow N).filter
    (fun p => frobeniusAngle W p ∈ Set.Icc a b)).card : ℝ) with hC
  have hcard_nonneg : (0:ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hlow : (∑ p ∈ S, gl (frobeniusAngle W p)) / (S.card : ℝ) ≤ C / (S.card : ℝ) := by
    have := sum_tent_le_card (theta := frobeniusAngle W) (a := a) (b := b) hdpos N
    gcongr
  have hupp : C / (S.card : ℝ) ≤ (∑ p ∈ S, gu (frobeniusAngle W p)) / (S.card : ℝ) := by
    have := card_le_sum_tent (theta := frobeniusAngle W) (a := a) (b := b) hdpos N
    gcongr
  have hIu : (∫ x in (0:ℝ)..Real.pi, gu x * satoTateDensity x)
      ≤ satoTateCDF (b + delta) - satoTateCDF (a - delta) := integral_tent_upper hdpos h0 hab hb
  have hIl : satoTateCDF (b - delta) - satoTateCDF (a + delta)
      ≤ ∫ x in (0:ℝ)..Real.pi, gl x * satoTateDensity x := integral_tent_lower hdpos h0 hb
  constructor
  · linarith [hN1'.1, hlow]
  · linarith [hN2'.2, hupp]

/-- The same statement with the Sato–Tate measure of `[a, b]` written out explicitly:
`(2/π) ∫_a^b sin²θ dθ = ((b - sin b cos b) - (a - sin a cos a))/π`. -/
