import Dubon2026.AnalyticRectangleMoments
import Dubon2026.WeightedRectangleZeros

/-! # Analytic dependence of the actual multiplicity-weighted zero power sums -/

namespace Dubon2026

open Filter Complex Set
open scoped BigOperators Topology

noncomputable section

/-- The literal finite power sum of zeros inside the source rectangle, with analytic multiplicity. -/
def complexPhaseZeroPowerSum (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u T : ℝ) (k : ℕ) (x : PrimeCoordinate N → ℂ) : ℂ :=
  ∑ s ∈ zerosInOpenRectangleFinset (complexPhaseCoefficients a N x) N hN
    (by rwa [complexPhaseCoefficients_one]) l u T,
      s ^ k * (zeroMultiplicity (complexPhaseCoefficients a N x) N s : ℂ)

theorem eventually_ne_zero_complexPhase_compact_set (a : ℕ → ℂ) (N : ℕ)
    (x : PrimeCoordinate N → ℂ) {K : Set ℂ} (hK : IsCompact K)
    (hn : ∀ s ∈ K, complexPhaseFamily a N (x, s) ≠ 0) :
    ∀ᶠ y in 𝓝 x, ∀ s ∈ K, complexPhaseFamily a N (y, s) ≠ 0 := by
  apply hK.eventually_forall_of_forall_eventually
  intro s hs
  exact (analyticAt_complexPhaseFamily a N (x, s)).continuousAt.eventually_ne (hn s hs)

theorem analyticAt_complexPhaseZeroPowerSum {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : PrimeCoordinate N → ℂ)
    {l u T : ℝ} (hlu : l ≤ u) (hT : 0 ≤ T)
    (hn : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      complexPhaseFamily a N (x, s) ≠ 0) (k : ℕ) :
    AnalyticAt ℂ (complexPhaseZeroPowerSum a N hN ha l u T k) x := by
  have hh := analyticAt_complexPhase_rectangle_power_logDeriv a N x hlu (neg_le_self hT) hn k
  apply hh.congr
  filter_upwards [eventually_ne_zero_complexPhase_compact_set a N x
    (isCompact_rectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ)) hn] with y hy
  exact rectangleIntegral_power_logDeriv_eq_zero_power_sum hN
    (by rwa [complexPhaseCoefficients_one] : complexPhaseCoefficients a N y 1 ≠ 0) hlu hT hy k

theorem complexPhaseZeroPowerSum_zero (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u T : ℝ) (x : PrimeCoordinate N → ℂ) :
    complexPhaseZeroPowerSum a N hN ha l u T 0 x =
      (verticalZeroCount (complexPhaseCoefficients a N x) N hN
        (by rwa [complexPhaseCoefficients_one]) l u T : ℂ) := by
  simp only [complexPhaseZeroPowerSum, verticalZeroCount, pow_zero, one_mul, Nat.cast_sum]

end

end Dubon2026
