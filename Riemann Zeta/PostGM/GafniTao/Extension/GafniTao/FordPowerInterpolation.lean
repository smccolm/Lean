import GafniTao.FordExponentialSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ford's power interpolation, equation (6.6)

This module proves the elementary but repeatedly used interpolation step from
Ford's Section 6.  The two cases and the threshold `C ^ (1 / c)` are retained
literally, so later consumers can account for the numerical constant rather
than silently absorbing it.
-/

namespace GafniTao

noncomputable section

/-- Ford's equation (6.6).  A trivial bound `F N ≤ N` and a power-saving
bound `F N ≤ C N^(1-c)` imply every weaker saving `d < c`, with the exact
constant `C^(d/c)`. -/
theorem ford_equation_6_6
    {F : ℝ → ℝ} {C c d : ℝ}
    (hC : 1 ≤ C) (hc : 0 < c) (hd : 0 < d) (hdc : d < c)
    (htrivial : ∀ {N : ℝ}, 1 ≤ N → F N ≤ N)
    (hstrong : ∀ {N : ℝ}, 1 ≤ N → F N ≤ C * N ^ (1 - c)) :
    ∀ {N : ℝ}, 1 ≤ N → F N ≤ C ^ (d / c) * N ^ (1 - d) := by
  intro N hN
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hdc_nonpos : d - c ≤ 0 := sub_nonpos.mpr hdc.le
  by_cases hsmall : N ≤ C ^ (1 / c)
  · have hpow : N ^ d ≤ C ^ (d / c) := by
      have hbase := Real.rpow_le_rpow hNpos.le hsmall hd.le
      calc
        N ^ d ≤ (C ^ (1 / c)) ^ d := hbase
        _ = C ^ ((1 / c) * d) := by rw [← Real.rpow_mul hCpos.le]
        _ = C ^ (d / c) := by
          congr 1
          simp only [div_eq_mul_inv]
          ring_nf
    calc
      F N ≤ N := htrivial hN
      _ = N ^ d * N ^ (1 - d) := by
        rw [← Real.rpow_add hNpos, show d + (1 - d) = 1 by ring_nf,
          Real.rpow_one]
      _ ≤ C ^ (d / c) * N ^ (1 - d) :=
        mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hNpos.le _)
  · have hlarge : C ^ (1 / c) ≤ N := le_of_lt (lt_of_not_ge hsmall)
    have hpow : N ^ (d - c) ≤ C ^ ((d - c) / c) := by
      have hreverse := Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hCpos (1 / c)) hlarge hdc_nonpos
      calc
        N ^ (d - c) ≤ (C ^ (1 / c)) ^ (d - c) := hreverse
        _ = C ^ ((1 / c) * (d - c)) := by rw [← Real.rpow_mul hCpos.le]
        _ = C ^ ((d - c) / c) := by
          congr 1
          simp only [div_eq_mul_inv]
          ring_nf
    calc
      F N ≤ C * N ^ (1 - c) := hstrong hN
      _ = (C * N ^ (d - c)) * N ^ (1 - d) := by
        rw [mul_assoc, ← Real.rpow_add hNpos]
        congr 1
        ring_nf
      _ ≤ (C * C ^ ((d - c) / c)) * N ^ (1 - d) := by
        gcongr
      _ = C ^ (d / c) * N ^ (1 - d) := by
        congr 1
        calc
          C * C ^ ((d - c) / c) = C ^ 1 * C ^ ((d - c) / c) := by
            rw [Real.rpow_one]
          _ = C ^ (1 + (d - c) / c) :=
            (Real.rpow_add hCpos 1 ((d - c) / c)).symm
          _ = C ^ (d / c) := by
            congr 1
            field_simp [hc0]
            ring_nf

#print axioms ford_equation_6_6

end

end GafniTao
