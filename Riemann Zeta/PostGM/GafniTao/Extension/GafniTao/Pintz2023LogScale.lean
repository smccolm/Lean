import GafniTao.Pintz2023Equation415
import GafniTao.FordScaleAlgebra

/-!
# Pintz (2023), equations (4.15)--(4.16): physical logarithmic scale

Pintz writes `u = log U / log T` after choosing the first dyadic block.  The
formal mollifier endpoint is a natural floor, so the paper's identity
`X = T^(epsilon/(10 ell))` acquires a vanishing floor loss.  The theorem below
keeps a strict `1/11` reserve and proves it uniformly in the dyadic depth.
-/

open Filter

namespace GafniTao

noncomputable section

noncomputable def pintz2023LogScale (T : ℝ) (U : ℕ) : ℝ :=
  Real.log (U : ℝ) / Real.log T

/-- The floored source endpoint still gives the strict lower logarithmic
scale used to bound the power `h`, uniformly for every dyadic depth. -/
theorem eventually_pintz2023_dyadic_logScale_lower
    {epsilon : ℝ} {ell : ℕ} (hepsilon : 0 < epsilon) (hell : 0 < ell) :
    ∀ᶠ T : ℝ in atTop, ∀ r : ℕ,
      epsilon / (11 * (ell : ℝ)) <
        pintz2023LogScale T (2 ^ r * pintz2023SourceX T epsilon ell) := by
  let a : ℝ := epsilon / (10 * (ell : ℝ))
  let b : ℝ := epsilon / (11 * (ell : ℝ))
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  have hab : 0 < a - b := by
    dsimp only [a, b]
    field_simp
    nlinarith
  have hgap := tendsto_rpow_atTop hab
  filter_upwards [hgap.eventually (eventually_gt_atTop 2),
    eventually_gt_atTop 1] with T hgapT hT r
  have hTPos : 0 < T := zero_lt_one.trans hT
  have hTbPos : 0 < T ^ b := Real.rpow_pos_of_pos hTPos _
  have hTaPos : 0 < T ^ a := Real.rpow_pos_of_pos hTPos _
  have hproduct : T ^ b * T ^ (a - b) = T ^ a := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have htwice : 2 * T ^ b < T ^ a := by
    have hmul := mul_lt_mul_of_pos_left hgapT hTbPos
    rw [mul_comm (T ^ b) 2, hproduct] at hmul
    exact hmul
  have hTaTwo : 2 ≤ T ^ a := by
    have hTbOne : 1 ≤ T ^ b := Real.one_le_rpow hT.le hb.le
    nlinarith
  have hfloor : T ^ a / 2 ≤
      ((pintz2023SourceX T epsilon ell : ℕ) : ℝ) := by
    simpa only [pintz2023SourceX, a] using ford_natFloor_ge_half hTaTwo
  have hTbFloor : T ^ b <
      ((pintz2023SourceX T epsilon ell : ℕ) : ℝ) := by
    nlinarith
  have hpowOne : 1 ≤ 2 ^ r := one_le_pow₀ (by omega : 1 ≤ (2 : ℕ))
  have hXPos : 0 < pintz2023SourceX T epsilon ell := by
    have hXCast : (0 : ℝ) < (pintz2023SourceX T epsilon ell : ℝ) :=
      hTbPos.trans hTbFloor
    exact_mod_cast hXCast
  have hXU : pintz2023SourceX T epsilon ell ≤
      2 ^ r * pintz2023SourceX T epsilon ell := by
    calc
      pintz2023SourceX T epsilon ell =
          1 * pintz2023SourceX T epsilon ell := by omega
      _ ≤ 2 ^ r * pintz2023SourceX T epsilon ell :=
        Nat.mul_le_mul_right _ hpowOne
  have hTbU : T ^ b <
      ((2 ^ r * pintz2023SourceX T epsilon ell : ℕ) : ℝ) := by
    exact hTbFloor.trans_le (by exact_mod_cast hXU)
  have hUPos : 0 <
      ((2 ^ r * pintz2023SourceX T epsilon ell : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (pow_pos (by omega) _) hXPos
  have hlog := Real.strictMonoOn_log hTbPos hUPos hTbU
  rw [Real.log_rpow hTPos] at hlog
  unfold pintz2023LogScale
  rw [lt_div_iff₀ (Real.log_pos hT)]
  simpa only [b] using hlog

/-- Exact upper logarithmic-scale conversion.  The hypothesis
`2^c < T^delta` exposes the sole vanishing loss caused by evaluating the
critical scale at `2T` rather than `T`. -/
theorem pintz2023_logScale_upper_of_support
    {T epsilon c delta : ℝ} {ell U : ℕ}
    (hT : 1 < T) (hU : 0 < U)
    (hfactor : (2 : ℝ) ^ c < T ^ delta)
    (hsupport : (U : ℝ) <
      (pintz2023SourceX T epsilon ell : ℝ) * (2 * T) ^ c) :
    pintz2023LogScale T U <
      epsilon / (10 * (ell : ℝ)) + c + delta := by
  have hTPos : 0 < T := zero_lt_one.trans hT
  have hTwoTPos : (0 : ℝ) < 2 * T := by positivity
  have hXUpper := pintz2023SourceX_cast_le
    (T := T) (epsilon := epsilon) (ell := ell)
    (Real.rpow_nonneg hTPos.le _)
  have hcritSplit : (2 * T) ^ c = (2 : ℝ) ^ c * T ^ c := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hTPos.le]
  have hTcPos : 0 < T ^ c := Real.rpow_pos_of_pos hTPos _
  have hcritUpper : (2 * T) ^ c < T ^ (c + delta) := by
    rw [hcritSplit, Real.rpow_add hTPos]
    simpa [mul_comm] using mul_lt_mul_of_pos_right hfactor hTcPos
  have hXNonneg : 0 ≤
      (pintz2023SourceX T epsilon ell : ℝ) := by positivity
  have hproductUpper :
      (pintz2023SourceX T epsilon ell : ℝ) * (2 * T) ^ c <
        T ^ (epsilon / (10 * (ell : ℝ))) * T ^ (c + delta) := by
    calc
      (pintz2023SourceX T epsilon ell : ℝ) * (2 * T) ^ c ≤
          T ^ (epsilon / (10 * (ell : ℝ))) * (2 * T) ^ c :=
        mul_le_mul_of_nonneg_right hXUpper (Real.rpow_nonneg hTwoTPos.le _)
      _ < T ^ (epsilon / (10 * (ell : ℝ))) * T ^ (c + delta) :=
        mul_lt_mul_of_pos_left hcritUpper (Real.rpow_pos_of_pos hTPos _)
  have hpowEq :
      T ^ (epsilon / (10 * (ell : ℝ))) * T ^ (c + delta) =
        T ^ (epsilon / (10 * (ell : ℝ)) + c + delta) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hUPow : (U : ℝ) <
      T ^ (epsilon / (10 * (ell : ℝ)) + c + delta) := by
    rw [← hpowEq]
    exact hsupport.trans hproductUpper
  have hUReal : (0 : ℝ) < U := by exact_mod_cast hU
  have hPowPos : 0 <
      T ^ (epsilon / (10 * (ell : ℝ)) + c + delta) :=
    Real.rpow_pos_of_pos hTPos _
  have hlog := Real.strictMonoOn_log hUReal hPowPos hUPow
  rw [Real.log_rpow hTPos] at hlog
  unfold pintz2023LogScale
  rw [div_lt_iff₀ (Real.log_pos hT)]
  simpa [mul_assoc] using hlog

/-- For every positive reserve, the fixed factor `2^c` is eventually
absorbed into `T^delta`. -/
theorem eventually_two_rpow_lt_rpow
    {c delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ T : ℝ in atTop, (2 : ℝ) ^ c < T ^ delta :=
  (tendsto_rpow_atTop hdelta).eventually (eventually_gt_atTop ((2 : ℝ) ^ c))

#print axioms eventually_pintz2023_dyadic_logScale_lower
#print axioms pintz2023_logScale_upper_of_support
#print axioms eventually_two_rpow_lt_rpow

end

end GafniTao
