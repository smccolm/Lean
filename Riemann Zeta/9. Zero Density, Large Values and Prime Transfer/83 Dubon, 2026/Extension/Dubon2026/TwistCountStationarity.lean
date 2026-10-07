import Dubon2026.TwistCountMeasurable
import Dubon2026.TwistProducts

/-! # Stationarity of the genuine phase zero count under vertical translation -/

namespace Dubon2026

open MeasureTheory

noncomputable section

theorem twistedCoefficients_twice (a : ℕ → ℂ) (N : ℕ) (z w : PrimeTorus N) :
    twistedCoefficients (twistedCoefficients a N z) N w =
      twistedCoefficients a N (z + w) := by
  funext n
  simp only [twistedCoefficients, Pi.add_apply, fourier_one_add, bohrMonomial_mul]
  ring

theorem twistZeroCount_twice (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (ha : a 1 ≠ 0) (l u H : ℝ) (z w : PrimeTorus N) :
    twistZeroCount (twistedCoefficients a N z) N hN
      (by rwa [twistedCoefficients_one]) l u H w =
        twistZeroCount a N hN ha l u H (z + w) := by
  unfold twistZeroCount
  simp only [twistedCoefficients_twice]

theorem slidingZeroCount_twisted (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (ha : a 1 ≠ 0) (l u H τ : ℝ) (z : PrimeTorus N) :
    slidingZeroCount (twistedCoefficients a N z) N hN
      (by rwa [twistedCoefficients_one]) l u H τ =
        twistZeroCount a N hN ha l u H (z + primeTorusFlow N τ) := by
  rw [slidingZeroCount_eq_twistZeroCount, twistZeroCount_twice]

theorem integrable_twistZeroCount {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u H : ℝ) :
    Integrable (fun z => (twistZeroCount a N hN ha l u H z : ℝ)) (torusHaar N) := by
  obtain ⟨K, hK⟩ := exists_uniform_twistZeroCount_bound hN ha l u H
  have hm : Measurable (fun z => (twistZeroCount a N hN ha l u H z : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_twistZeroCount hN ha l u H)
  apply (integrable_const (K : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast hK z

theorem integral_twistZeroCount_add (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u H : ℝ) (v : PrimeTorus N) :
    (∫ z, (twistZeroCount a N hN ha l u H (z + v) : ℝ) ∂torusHaar N) =
      ∫ z, (twistZeroCount a N hN ha l u H z : ℝ) ∂torusHaar N :=
  integral_add_right_eq_self (fun z => (twistZeroCount a N hN ha l u H z : ℝ)) v

theorem integral_slidingZeroCount_twisted (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u H τ : ℝ) :
    (∫ z, (slidingZeroCount (twistedCoefficients a N z) N hN
      (by rwa [twistedCoefficients_one]) l u H τ : ℝ) ∂torusHaar N) =
        ∫ z, (twistZeroCount a N hN ha l u H z : ℝ) ∂torusHaar N := by
  calc
    _ = ∫ z, (twistZeroCount a N hN ha l u H (z + primeTorusFlow N τ) : ℝ) ∂torusHaar N := by
      apply integral_congr_ae
      filter_upwards with z
      exact congrArg (fun n : ℕ => (n : ℝ))
        (slidingZeroCount_twisted a N hN ha l u H τ z)
    _ = _ := integral_twistZeroCount_add a N hN ha l u H (primeTorusFlow N τ)

end

end Dubon2026
