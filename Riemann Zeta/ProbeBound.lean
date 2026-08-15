import RiemannZeta.GuthMaynard.DFIEquation29

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology Interval
open Classical

namespace RiemannZeta.GuthMaynard

theorem probe_one_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {A B S : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 < S)
    (hSB : 1 ≤ S * B) (j : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc S (2 * S))
    (hDeriv : ∀ r ≤ j + 2,
      ‖iteratedDeriv r g x‖ ≤ A * B ^ r) :
    ‖iteratedDeriv j (dfiEquation29BesselShiftIterate 2 g) x‖ ≤
      A * (((j : ℝ) + 3) * S * B ^ 2) * B ^ j := by
  rw [hg.iteratedDeriv_besselShift_two]
  have h1 := hDeriv (j + 1) (by omega)
  have h2 := hDeriv (j + 2) (by omega)
  have hx0 : 0 ≤ x := hS.le.trans hx.1
  have hxnorm : ‖(x : ℂ)‖ ≤ 2 * S := by
    simpa [Real.norm_of_nonneg hx0] using hx.2
  have hcoeff : ‖(1 : ℂ) + j‖ = (j : ℝ) + 1 := by
    rw [show (1 : ℂ) + j = (((j : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_of_nonneg]
    positivity
  have hBstep : B ^ (j + 1) ≤ S * B ^ (j + 2) := by
    rw [show B ^ (j + 1) = B ^ j * B by
      simpa using pow_succ B j]
    rw [show B ^ (j + 2) = B ^ j * B ^ 2 by
      calc
        B ^ (j + 2) = B ^ j * B ^ 2 := by rw [pow_add]
        _ = _ := rfl]
    have hBB : B ≤ S * B ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hSB hB]
    calc
      B ^ j * B ≤ B ^ j * (S * B ^ 2) :=
        mul_le_mul_of_nonneg_left hBB (pow_nonneg hB j)
      _ = S * (B ^ j * B ^ 2) := by ring
  calc
    ‖((1 : ℂ) + j) * iteratedDeriv (j + 1) g x +
        (x : ℂ) * iteratedDeriv (j + 2) g x‖ ≤
      ‖(1 : ℂ) + j‖ * ‖iteratedDeriv (j + 1) g x‖ +
        ‖(x : ℂ)‖ * ‖iteratedDeriv (j + 2) g x‖ := by
          calc
            _ ≤ ‖((1 : ℂ) + j) * iteratedDeriv (j + 1) g x‖ +
                ‖(x : ℂ) * iteratedDeriv (j + 2) g x‖ := norm_add_le _ _
            _ = _ := by rw [norm_mul, norm_mul]
    _ ≤ ((j : ℝ) + 1) * (A * B ^ (j + 1)) +
        (2 * S) * (A * B ^ (j + 2)) := by
          rw [hcoeff]
          gcongr
    _ ≤ ((j : ℝ) + 1) * (A * (S * B ^ (j + 2))) +
        (2 * S) * (A * B ^ (j + 2)) := by
          gcongr
    _ = A * (((j : ℝ) + 3) * S * B ^ 2) * B ^ j := by
      rw [show B ^ (j + 2) = B ^ j * B ^ 2 by
        rw [show j + 2 = j + 1 + 1 by omega, pow_succ, pow_succ]
        ring]
      ring

theorem probe_iter_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {A B S D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 < S)
    (hSB : 1 ≤ S * B)
    (hSupport : Function.support g ⊆ Set.Icc S (2 * S)) (k p : ℕ)
    (hD : (p + 2 * k + 3 : ℕ) ≤ D)
    (hDeriv : ∀ r ≤ p + 2 * k, ∀ x : ℝ,
      ‖iteratedDeriv r g x‖ ≤ A * B ^ r) :
    ∀ j ≤ p, ∀ x ∈ Set.Icc S (2 * S),
      ‖iteratedDeriv j (dfiEquation29BesselRecurrenceIterate k g) x‖ ≤
        A * (D * S * B ^ 2) ^ k * B ^ j := by
  induction k generalizing g A p with
  | zero =>
      intro j hj x hx
      simp only [dfiEquation29BesselRecurrenceIterate_zero, pow_zero, mul_one]
      exact hDeriv j (by simpa using hj) x
  | succ k ih =>
      let Rg : ℝ → ℂ := dfiEquation29BesselShiftIterate 2 g
      have hRg : DFIVoronoiTestFunction Rg := hg.besselShiftIterate 2
      have hRgSupport : Function.support Rg ⊆ Set.Icc S (2 * S) := by
        intro x hx
        apply closure_minimal hSupport isClosed_Icc
        have hxR : x ∈ tsupport Rg := subset_tsupport Rg hx
        have hxL : x ∈ tsupport (dfiMellinLogOperator 1 (deriv g)) := by
          rw [show Rg = dfiMellinLogOperator 1 (deriv g) from
            hg.besselShift_two_eq] at hxR
          exact hxR
        exact tsupport_deriv_subset
          (tsupport_dfiMellinLogOperator_subset 1 (deriv g) hxL)
      have hSS : S ≤ 2 * S := by linarith
      let hRgS : DFIVoronoiTestFunction Rg := {
        lower := S
        upper := 2 * S
        lower_pos := hS
        lower_le_upper := hSS
        smooth := hRg.smooth
        support_subset := hRgSupport }
      let A' : ℝ := A * (D * S * B ^ 2)
      have hFactor : 0 ≤ D * S * B ^ 2 := by
        have hD0 : 0 ≤ D := by
          exact le_trans (Nat.cast_nonneg _) hD
        positivity
      have hA' : 0 ≤ A' := mul_nonneg hA hFactor
      have hD' : (p + 2 * k + 3 : ℕ) ≤ D := by
        exact le_trans (by exact_mod_cast (show p + 2 * k + 3 ≤
          p + 2 * (k + 1) + 3 by omega)) hD
      have hRgDeriv : ∀ r ≤ p + 2 * k, ∀ x : ℝ,
          ‖iteratedDeriv r Rg x‖ ≤ A' * B ^ r := by
        intro r hr x
        by_cases hx : x ∈ Set.Icc S (2 * S)
        · have hsource : ∀ s ≤ r + 2,
              ‖iteratedDeriv s g x‖ ≤ A * B ^ s := by
            intro s hs
            apply hDeriv s
            omega
          have hone := probe_one_bound hg hA hB hS hSB r x hx hsource
          have hrD : (r : ℝ) + 3 ≤ D := by
            have hrNat : r + 3 ≤ p + 2 * (k + 1) + 3 := by omega
            exact le_trans (by exact_mod_cast hrNat) hD
          calc
            ‖iteratedDeriv r Rg x‖ ≤
                A * (((r : ℝ) + 3) * S * B ^ 2) * B ^ r := hone
            _ ≤ A * (D * S * B ^ 2) * B ^ r := by gcongr
            _ = A' * B ^ r := rfl
        · have hxzero : iteratedDeriv r Rg x = 0 :=
            hRgS.iteratedDeriv_eq_zero_of_not_mem r (by simpa [hRgS] using hx)
          rw [hxzero, norm_zero]
          exact mul_nonneg hA' (pow_nonneg hB r)
      intro j hj x hx
      rw [dfiEquation29BesselRecurrenceIterate_succ]
      have hout := ih hRgS hA' hRgSupport p hD' hRgDeriv j hj x hx
      calc
        ‖iteratedDeriv j
            (dfiEquation29BesselRecurrenceIterate k Rg) x‖ ≤
            A' * (D * S * B ^ 2) ^ k * B ^ j := hout
        _ = A * (D * S * B ^ 2) ^ (k + 1) * B ^ j := by
          dsimp [A']
          rw [pow_succ]
          ring

end RiemannZeta.GuthMaynard
