import GafniTao.SharpPerronSeries

/-!
# Elementary bounds for the finite sharp-Perron kernel

These estimates are the absolute-convergence side of the sharp Perron
argument.  They retain the exact kernel and make no appeal to an explicit
formula or a zero-density theorem.
-/

open scoped Interval

namespace GafniTao

@[simp] theorem sharpPerronKernel_zero_height (c x : ℝ) (n : ℕ) :
    sharpPerronKernel c 0 x n = 0 := by
  simp [sharpPerronKernel]

private theorem norm_sharpPerronKernel_integrand_le
    {c x : ℝ} {n : ℕ} (hc : 0 < c) (hx : 0 < x) (hn : 1 ≤ n)
    (t : ℝ) :
    ‖(x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
          (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
            ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (x ^ c / (n : ℝ) ^ c) / c := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hxNorm :
      ‖(x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)‖ = x ^ c := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hx
      ((c : ℂ) + (t : ℂ) * Complex.I)
  have hnNorm :
      ‖(n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)‖ =
        (n : ℝ) ^ c := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hnpos
      ((c : ℂ) + (t : ℂ) * Complex.I)
  have hsNorm : c ≤ ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := by
    have h := Complex.abs_re_le_norm ((c : ℂ) + (t : ℂ) * Complex.I)
    simpa [abs_of_pos hc] using h
  have hnpowPos : 0 < (n : ℝ) ^ c := Real.rpow_pos_of_pos hnpos c
  rw [norm_div, norm_div, hxNorm, hnNorm]
  exact div_le_div_of_nonneg_left
    (div_nonneg (Real.rpow_nonneg hx.le c) (Real.rpow_nonneg hnpos.le c))
    hc hsNorm

/-- Uniform absolute bound for the exact finite-height Perron kernel.  This is
valid for either orientation of the symmetric interval and therefore records
the height as `|T|`. -/
theorem norm_sharpPerronKernel_le
    {c T x : ℝ} {n : ℕ} (hc : 0 < c) (hx : 0 < x) (hn : 1 ≤ n) :
    ‖sharpPerronKernel c T x n‖ ≤
      (x ^ c / (n : ℝ) ^ c) * (|T| / (Real.pi * c)) := by
  have hpoint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := T)
    (C := (x ^ c / (n : ℝ) ^ c) / c)
    (f := fun t : ℝ =>
      (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
        (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
          ((c : ℂ) + (t : ℂ) * Complex.I))
    (fun t _ht => norm_sharpPerronKernel_integrand_le hc hx hn t)
  rw [sharpPerronKernel, norm_mul]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hbase : 0 ≤ x ^ c / (n : ℝ) ^ c :=
    div_nonneg (Real.rpow_nonneg hx.le c)
      (Real.rpow_nonneg (Nat.cast_nonneg n) c)
  calc
    ‖(1 / (2 * Real.pi) : ℂ)‖ *
          ‖∫ t in (-T)..T,
            (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
              (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                ((c : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ *
            (((x ^ c / (n : ℝ) ^ c) / c) * |T - (-T)|) := by
              gcongr
    _ = (x ^ c / (n : ℝ) ^ c) * (|T| / (Real.pi * c)) := by
          simp only [norm_div, norm_one]
          have hnorm : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
            simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hpi]
          rw [hnorm]
          rw [show T - -T = 2 * T by ring, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ))]
          field_simp [ne_of_gt hpi, ne_of_gt hc]

end GafniTao
