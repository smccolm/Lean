import Dubon2026.LogDerivativeHalfPlane
import Dubon2026.ZeroFreeRealSign

/-! # A finite real-part crossing set controls the actual logarithmic-derivative integral

The deliberately coarse bound is exponential in the number of crossings. Its
uniformity in the height suffices for the long-contour limit.
-/

namespace Dubon2026

open MeasureTheory Set

theorem abs_im_integral_logDerivative_le_of_finite_crossings
    (f f' : ℝ → ℂ) (Z : Finset ℝ) : ∀ a b : ℝ, a ≤ b →
    (∀ x ∈ Icc a b, HasDerivAt f (f' x) x) →
    (∀ x ∈ Icc a b, f x ≠ 0) →
    IntervalIntegrable (fun x => f' x / f x) volume a b →
    (∀ x ∈ Ioo a b, (f x).re = 0 → x ∈ Z) →
    |(∫ x in a..b, f' x / f x).im| ≤ Real.pi * (2 : ℝ) ^ Z.card := by
  classical
  induction Z using Finset.induction_on with
  | empty =>
    intro a b hab hf hn hi hz
    simp only [Finset.card_empty, pow_zero, mul_one]
    have hcont : ContinuousOn f (Icc a b) :=
      fun x hx => (hf x hx).continuousAt.continuousWithinAt
    have hsign := continuousOn_constant_sign_of_no_interior_zero
      (Complex.continuous_re.comp_continuousOn hcont)
      (fun x hx hzero => Finset.notMem_empty x (hz x hx hzero))
    rcases hsign with hpos | hneg
    · exact abs_im_integral_logDerivative_le_pi_of_re_nonneg hab hf hn hpos hi
    · exact abs_im_integral_logDerivative_le_pi_of_re_nonpos hab hf hn hneg hi
  | @insert c Z hc ih =>
    intro a b hab hf hn hi hz
    rw [Finset.card_insert_of_notMem hc, pow_succ]
    by_cases hcin : c ∈ Ioo a b
    · have hsubL : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hcin.2.le
      have hsubR : Icc c b ⊆ Icc a b := Icc_subset_Icc hcin.1.le le_rfl
      have hiL : IntervalIntegrable (fun x => f' x / f x) volume a c := by
        apply hi.mono_set
        simpa only [uIcc_of_le hab, uIcc_of_le hcin.1.le] using hsubL
      have hiR : IntervalIntegrable (fun x => f' x / f x) volume c b := by
        apply hi.mono_set
        simpa only [uIcc_of_le hab, uIcc_of_le hcin.2.le] using hsubR
      have hL := ih a c hcin.1.le (fun x hx => hf x (hsubL hx))
        (fun x hx => hn x (hsubL hx)) hiL (by
          intro x hx hzero
          have hmem := hz x ⟨hx.1, hx.2.trans hcin.2⟩ hzero
          rcases Finset.mem_insert.mp hmem with he | he
          · exact False.elim (hx.2.ne he)
          · exact he)
      have hR := ih c b hcin.2.le (fun x hx => hf x (hsubR hx))
        (fun x hx => hn x (hsubR hx)) hiR (by
          intro x hx hzero
          have hmem := hz x ⟨hcin.1.trans hx.1, hx.2⟩ hzero
          rcases Finset.mem_insert.mp hmem with he | he
          · exact False.elim (hx.1.ne' he)
          · exact he)
      rw [← intervalIntegral.integral_add_adjacent_intervals hiL hiR, Complex.add_im]
      apply (abs_add_le _ _).trans
      nlinarith
    · have hb := ih a b hab hf hn hi (by
        intro x hx hzero
        rcases Finset.mem_insert.mp (hz x hx hzero) with he | he
        · exact False.elim (hcin (he ▸ hx))
        · exact he)
      have hp : 0 ≤ Real.pi * (2 : ℝ) ^ Z.card := by positivity
      nlinarith

end Dubon2026
