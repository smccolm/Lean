import GafniTao.Pintz2023Equation420
import GafniTao.Pintz2023SourceScale

/-!
# Pintz (2023), equation (4.20): moving-pole residue absorption

The residue is exponentially small at the actual selected-zero separation.
This file converts that decay to the same `T^(-epsilon/k)` saving as the
main local-frequency term, retaining the exact source lambda.
-/

namespace GafniTao

noncomputable section

private theorem pintz2023_linear_exp_tail_le
    {x : ℝ} (hx : 0 ≤ x) :
    (x + 2) * Real.exp (-(Real.pi * x) / 2) ≤
      3 * Real.exp (-x) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hexponent : -(Real.pi * x) / 2 ≤ -(3 * x) / 2 := by
    nlinarith
  have hexpPi : Real.exp (-(Real.pi * x) / 2) ≤
      Real.exp (-(3 * x) / 2) := Real.exp_le_exp.mpr hexponent
  have hlinear : 1 + x / 2 ≤ Real.exp (x / 2) :=
    by simpa [add_comm] using Real.add_one_le_exp (x / 2)
  have hpoly : x + 2 ≤ 3 * Real.exp (x / 2) := by
    nlinarith [Real.exp_pos (x / 2)]
  calc
    (x + 2) * Real.exp (-(Real.pi * x) / 2) ≤
        (x + 2) * Real.exp (-(3 * x) / 2) := by gcongr
    _ ≤ (3 * Real.exp (x / 2)) * Real.exp (-(3 * x) / 2) := by
      gcongr
    _ = 3 * Real.exp (-x) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf

/-- The exact residue term is absorbed using only `N ≤ T^3` and the
source separation `3*lambda ≤ |t|`. -/
theorem pintz2023_equation420_residue_decay
    {eta target T t : ℝ} {N k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell)
    (hT : 1 ≤ T)
    (hNUpper : (N : ℝ) ≤ T ^ (3 : ℝ))
    (hSep : 3 * pintz2023SourceLambda T k ≤ |t|) :
    (N : ℝ) ^ (2 * eta) * (|t| + 2) *
        Real.exp (-(Real.pi * |t|) / 2) ≤
      3 * T ^ (-data.epsilon / (k : ℝ)) := by
  have heta : 0 < eta := pintzCell_eta_pos hcell
  have hkNat : 4 ≤ k := hcell.1
  have hk : 0 < k := lt_of_lt_of_le (by omega) hkNat
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hNNonneg : (0 : ℝ) ≤ N := by positivity
  have hNPower : (N : ℝ) ^ (2 * eta) ≤ T ^ (6 * eta) := by
    calc
      (N : ℝ) ^ (2 * eta) ≤ (T ^ (3 : ℝ)) ^ (2 * eta) :=
        Real.rpow_le_rpow hNNonneg hNUpper (by positivity)
      _ = T ^ (6 * eta) := by
        rw [← Real.rpow_mul hTPos.le]
        congr 1
        ring_nf
  have hTail :
      (|t| + 2) * Real.exp (-(Real.pi * |t|) / 2) ≤
        3 * T ^ (-6 / (k : ℝ)) := by
    calc
      (|t| + 2) * Real.exp (-(Real.pi * |t|) / 2) ≤
          3 * Real.exp (-|t|) :=
        pintz2023_linear_exp_tail_le (abs_nonneg t)
      _ ≤ 3 * Real.exp (-3 * pintz2023SourceLambda T k) := by
        gcongr
        linarith
      _ = 3 * T ^ (-6 / (k : ℝ)) := by
        rw [exp_neg_three_pintz2023SourceLambda hTPos hk]
  have hkMinus : (3 : ℝ) ≤ (k : ℝ) - 1 := by
    have hkCast : (4 : ℝ) ≤ k := by exact_mod_cast hkNat
    linarith
  have hkCell :
      eta * (k : ℝ) * ((k : ℝ) - 1) < 1 := by
    simpa using hcell.2.2.1
  have hetaK : eta * (k : ℝ) < 1 / 3 := by
    have hmul := mul_le_mul_of_nonneg_left hkMinus
      (mul_nonneg heta.le (by positivity : (0 : ℝ) ≤ k))
    nlinarith
  have hbudget : 6 * eta * (k : ℝ) + data.epsilon ≤ 6 := by
    nlinarith [data.epsilon_le_one]
  have hbudget' :
      6 * eta * (k : ℝ) - 6 ≤ -data.epsilon := by
    linarith
  have hexponent :
      6 * eta - 6 / (k : ℝ) ≤
        -data.epsilon / (k : ℝ) := by
    calc
      6 * eta - 6 / (k : ℝ) =
          (6 * eta * (k : ℝ) - 6) / (k : ℝ) := by
        field_simp
      _ ≤ (-data.epsilon) / (k : ℝ) :=
        (div_le_div_iff_of_pos_right hkReal).2 hbudget'
      _ = -data.epsilon / (k : ℝ) := rfl
  have hPowerCombine :
      T ^ (6 * eta) * T ^ (-6 / (k : ℝ)) =
        T ^ (6 * eta - 6 / (k : ℝ)) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring_nf
  calc
    (N : ℝ) ^ (2 * eta) * (|t| + 2) *
        Real.exp (-(Real.pi * |t|) / 2) =
      (N : ℝ) ^ (2 * eta) *
        ((|t| + 2) * Real.exp (-(Real.pi * |t|) / 2)) := by ring_nf
    _ ≤ T ^ (6 * eta) * (3 * T ^ (-6 / (k : ℝ))) := by
      gcongr
    _ = 3 * T ^ (6 * eta - 6 / (k : ℝ)) := by
      rw [← hPowerCombine]
      ring_nf
    _ ≤ 3 * T ^ (-data.epsilon / (k : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT hexponent) (by norm_num)

#print axioms pintz2023_equation420_residue_decay

end

end GafniTao
