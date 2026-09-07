import GafniTao.SharpPerronGeneralZeroShell

/-!
# The compact height range for the sharp explicit formula

For `2 ≤ T < 8`, all zeros in the truncated sum lie in the single fixed
finite set `zeroSet 0 8`.  This gives a genuine compact-range proof and
completes the quantifiers in `SharpPsiTruncationBound`.
-/

open scoped BigOperators

noncomputable section

namespace GafniTao

private noncomputable def sharpPerronLowZeroConstant : ℝ :=
  ∑ rho ∈ zeroSet 0 8,
    (zeroMultiplicity rho : ℝ) / ‖rho‖

private theorem sharpPerronLowZeroConstant_nonneg :
    0 ≤ sharpPerronLowZeroConstant := by
  unfold sharpPerronLowZeroConstant
  exact Finset.sum_nonneg fun _ _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)

private theorem norm_low_zero_term_le
    {x : ℝ} (hx : 1 ≤ x) {rho : ℂ} (hrho : rho ∈ zeroSet 0 8) :
    ‖(zeroMultiplicity rho : ℂ) * ((x : ℂ) ^ rho / rho)‖ ≤
      (zeroMultiplicity rho : ℝ) * (x / ‖rho‖) := by
  have hd := mem_zeroSet_zero_data hrho
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hpow : x ^ rho.re ≤ x := by
    calc
      x ^ rho.re ≤ x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx hd.2.1
      _ = x := Real.rpow_one x
  rw [norm_mul, RCLike.norm_natCast, norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
  gcongr

private theorem norm_truncatedPsiZeroSum_low_le
    {T x : ℝ} (hT8 : T ≤ 8) (hx : 1 ≤ x) :
    ‖truncatedPsiZeroSum T x‖ ≤ sharpPerronLowZeroConstant * x := by
  unfold truncatedPsiZeroSum
  have hsubset : zeroSet 0 T ⊆ zeroSet 0 8 := zeroSet_mono_height hT8
  calc
    ‖∑ rho ∈ zeroSet 0 T,
        (zeroMultiplicity rho : ℂ) * ((x : ℂ) ^ rho / rho)‖ ≤
      ∑ rho ∈ zeroSet 0 T,
        ‖(zeroMultiplicity rho : ℂ) * ((x : ℂ) ^ rho / rho)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ zeroSet 0 T,
        (zeroMultiplicity rho : ℝ) * (x / ‖rho‖) := by
      apply Finset.sum_le_sum
      intro rho hrho
      exact norm_low_zero_term_le hx (hsubset hrho)
    _ ≤ ∑ rho ∈ zeroSet 0 8,
        (zeroMultiplicity rho : ℝ) * (x / ‖rho‖) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro rho _ _
      exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith) (norm_nonneg _))
    _ = sharpPerronLowZeroConstant * x := by
      unfold sharpPerronLowZeroConstant
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro rho _
      ring

private theorem norm_sharpPsiTruncationError_low_le
    {T x : ℝ} (hT : 2 ≤ T) (hT8 : T ≤ 8) (hTx : T ≤ x) :
    ‖sharpPsiTruncationError T x‖ ≤
      (Real.log 4 + 5 + sharpPerronLowZeroConstant) * x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hpsi := Chebyshev.psi_le_const_mul_self hx0
  have hzero := norm_truncatedPsiZeroSum_low_le hT8 hx1
  unfold sharpPsiTruncationError
  calc
    ‖(((Chebyshev.psi x - x : ℝ) : ℂ) + truncatedPsiZeroSum T x)‖ ≤
        ‖((Chebyshev.psi x - x : ℝ) : ℂ)‖ +
          ‖truncatedPsiZeroSum T x‖ := norm_add_le _ _
    _ = |Chebyshev.psi x - x| + ‖truncatedPsiZeroSum T x‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (Chebyshev.psi x + x) + ‖truncatedPsiZeroSum T x‖ := by
      gcongr
      calc
        |Chebyshev.psi x - x| ≤ |Chebyshev.psi x| + |x| := abs_sub _ _
        _ = Chebyshev.psi x + x := by
          rw [abs_of_nonneg (Chebyshev.psi_nonneg x), abs_of_nonneg hx0]
    _ ≤ ((Real.log 4 + 4) * x + x) +
          sharpPerronLowZeroConstant * x := add_le_add (add_le_add hpsi le_rfl) hzero
    _ = (Real.log 4 + 5 + sharpPerronLowZeroConstant) * x := by ring

/-- The full Davenport sharp-truncation contract, including the compact
height range. -/
theorem sharpPsiTruncationBound_native : SharpPsiTruncationBound := by
  obtain ⟨Chigh, hChigh, hhigh⟩ :=
    exists_norm_sharpPsiTruncationError_general_high_le
  let E : ℝ := Real.log 4 + 5 + sharpPerronLowZeroConstant
  let Clow : ℝ := 8 * E / (Real.log 2) ^ 2
  let C : ℝ := Chigh + Clow
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE : 0 < E := by
    dsimp [E]
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith [sharpPerronLowZeroConstant_nonneg]
  have hClow : 0 < Clow := by dsimp [Clow]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T x hT hTx hx
  by_cases hEight : 8 ≤ T
  · have hbound := hhigh hEight hTx
    refine hbound.trans ?_
    calc
      Chigh * x * Real.log x ^ 2 / T =
          Chigh * (x * Real.log x ^ 2 / T) := by ring
      _ ≤ C * (x * Real.log x ^ 2 / T) :=
        mul_le_mul_of_nonneg_right (by
          dsimp [C]
          exact le_add_of_nonneg_right hClow.le) (by positivity)
      _ = C * x * Real.log x ^ 2 / T := by ring
  · have hT8 : T ≤ 8 := le_of_not_ge hEight
    have hraw := norm_sharpPsiTruncationError_low_le hT hT8 hTx
    have hxPos : 0 < x := by linarith
    have hTpos : 0 < T := by linarith
    have hlogLower : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) hx
    have hlogSq : (Real.log 2) ^ 2 ≤ (Real.log x) ^ 2 := by
      have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
      nlinarith
    have habsorb : E * x ≤ Clow * x * Real.log x ^ 2 / T := by
      rw [le_div_iff₀ hTpos]
      have hEx : 0 ≤ E * x := mul_nonneg hE.le hxPos.le
      calc
        E * x * T ≤ E * x * 8 := mul_le_mul_of_nonneg_left hT8 hEx
        _ ≤ (8 * E / (Real.log 2) ^ 2) * x * Real.log x ^ 2 := by
          rw [show E * x * 8 = (8 * E * x / (Real.log 2) ^ 2) *
              (Real.log 2) ^ 2 by field_simp]
          have hcoef : 0 ≤ 8 * E * x / (Real.log 2) ^ 2 := by positivity
          exact (mul_le_mul_of_nonneg_left hlogSq hcoef).trans_eq (by ring)
    refine hraw.trans habsorb |>.trans ?_
    calc
      Clow * x * Real.log x ^ 2 / T =
          Clow * (x * Real.log x ^ 2 / T) := by ring
      _ ≤ C * (x * Real.log x ^ 2 / T) :=
        mul_le_mul_of_nonneg_right (by
          dsimp [C]
          exact le_add_of_nonneg_left hChigh.le) (by positivity)
      _ = C * x * Real.log x ^ 2 / T := by ring

/-- The exact source-facing short-interval explicit formula, obtained by the
proved endpoint subtraction consumer. -/
theorem sharpTruncatedExplicitFormulaBound_native :
    SharpTruncatedExplicitFormulaBound :=
  sharpTruncatedExplicitFormulaBound_of_sharpPsi sharpPsiTruncationBound_native

end GafniTao
