import GafniTao.Pintz2023MellinShift
import GafniTao.PintzGammaHorizontalSharp
import RiemannZeta.GuthMaynard.DFIProposition1

/-!
# Exponential Gamma decay for Pintz's Mellin shift

Euler reflection gives an exact norm formula on the half line.  A sharp
horizontal displacement and the Gamma recurrence then transfer that decay to
the punctured imaginary axis.  This supplies the exponential tail actually
used in Pintz Lemma 3.4, rather than a polynomial surrogate.
-/

open Complex Set

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem norm_Gamma_half_vertical_sq_le_exp (u : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
      8 * Real.exp (-Real.pi * |u|) := by
  rw [Gamma_half_add_mul_I_norm_sq]
  have hcoshPos : 0 < Real.cosh (Real.pi * u) := Real.cosh_pos _
  have hExpCosh : Real.exp (Real.pi * |u|) ≤
      2 * Real.cosh (Real.pi * u) := by
    have h := exp_le_two_mul_cosh (Real.pi * |u|)
    calc
      Real.exp (Real.pi * |u|) ≤
          2 * Real.cosh (Real.pi * |u|) := h
      _ = 2 * Real.cosh (Real.pi * u) := by
        rw [← Real.cosh_abs (Real.pi * u)]
        simp [abs_mul, abs_of_nonneg Real.pi_nonneg]
  have hHalf : (1 / 2 : ℝ) ≤
      Real.exp (-Real.pi * |u|) * Real.cosh (Real.pi * u) := by
    have hmul := mul_le_mul_of_nonneg_left hExpCosh
      (Real.exp_pos (-Real.pi * |u|)).le
    rw [← Real.exp_add] at hmul
    have hzero : -Real.pi * |u| + Real.pi * |u| = 0 := by ring
    rw [hzero, Real.exp_zero] at hmul
    linarith
  apply (div_le_iff₀ hcoshPos).2
  calc
    Real.pi ≤ 4 := Real.pi_lt_four.le
    _ = 8 * (1 / 2 : ℝ) := by norm_num
    _ ≤ 8 * (Real.exp (-Real.pi * |u|) *
        Real.cosh (Real.pi * u)) := by gcongr
    _ = 8 * Real.exp (-Real.pi * |u|) *
        Real.cosh (Real.pi * u) := by ring

theorem norm_Gamma_half_vertical_le_exp (u : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
      3 * Real.exp (-(Real.pi * |u|) / 2) := by
  have hsq := norm_Gamma_half_vertical_sq_le_exp u
  have hright : 0 ≤ 3 * Real.exp (-(Real.pi * |u|) / 2) := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  calc
    ‖Complex.Gamma ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
        8 * Real.exp (-Real.pi * |u|) := hsq
    _ ≤ 9 * Real.exp (-Real.pi * |u|) := by
      gcongr
      norm_num
    _ = (3 * Real.exp (-(Real.pi * |u|) / 2)) ^ 2 := by
      rw [mul_pow]
      norm_num
      rw [pow_two, ← Real.exp_add]
      congr 2
      ring

/-- Exponential decay on the punctured imaginary axis.  The polynomial
factor is kept visible because it is integrated explicitly in the tail of
Pintz Lemma 3.4. -/
theorem exists_norm_Gamma_imaginary_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 1 ≤ |u| →
      ‖Complex.Gamma ((u : ℂ) * I)‖ ≤
        C * (|u| + 2) * Real.exp (-(Real.pi * |u|) / 2) := by
  obtain ⟨D, hD, hShift⟩ :=
    exists_norm_Gamma_right_displacement_le
      (a := (1 / 2 : ℝ)) (b := (1 : ℝ)) (by norm_num)
  let C : ℝ := 3 * Real.exp (D / 2)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro u hu
  have huPos : 0 < |u| := zero_lt_one.trans_le hu
  have hu0 : u ≠ 0 := abs_pos.mp huPos
  let z : ℂ := (1 / 2 : ℂ) + (u : ℂ) * I
  have hDisplaced := hShift z (1 / 2)
    (by simp [z]) (by simp [z]; norm_num) (by norm_num)
  have harg : z + (1 / 2 : ℂ) = (u : ℂ) * I + 1 := by
    apply Complex.ext
    · norm_num [z]
    · simp [z, add_comm]
  have hrec := Complex.Gamma_add_one ((u : ℂ) * I)
    (mul_ne_zero (ofReal_ne_zero.mpr hu0) I_ne_zero)
  have hnormRec : |u| * ‖Complex.Gamma ((u : ℂ) * I)‖ =
      ‖Complex.Gamma (z + (1 / 2 : ℂ))‖ := by
    rw [harg, hrec, norm_mul, norm_mul, norm_real, norm_I]
    simp
  have hhalf := norm_Gamma_half_vertical_le_exp u
  have hbase : 1 ≤ |u| + 2 := by linarith [abs_nonneg u]
  have hsqrt : Real.exp (Real.log (|u| + 2) / 2) ≤ |u| + 2 := by
    rw [show Real.exp (Real.log (|u| + 2) / 2) =
        Real.sqrt (|u| + 2) by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
      congr 1
      ring]
    have hsqrtNonneg := Real.sqrt_nonneg (|u| + 2)
    have hsqrtSq := Real.sq_sqrt (show 0 ≤ |u| + 2 by positivity)
    nlinarith
  have hexpSplit :
      Real.exp ((Real.log (|u| + 2) + D) * (1 / 2)) =
        Real.exp (Real.log (|u| + 2) / 2) * Real.exp (D / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hzIm : |z.im| = |u| := by simp [z]
  rw [hzIm, hexpSplit] at hDisplaced
  have hupper :
      ‖Complex.Gamma (z + (1 / 2 : ℂ))‖ ≤
        C * (|u| + 2) * Real.exp (-(Real.pi * |u|) / 2) := by
    calc
      ‖Complex.Gamma (z + (1 / 2 : ℂ))‖ ≤
          ‖Complex.Gamma z‖ *
            (Real.exp (Real.log (|u| + 2) / 2) * Real.exp (D / 2)) :=
        by simpa using hDisplaced
      _ ≤ (3 * Real.exp (-(Real.pi * |u|) / 2)) *
            ((|u| + 2) * Real.exp (D / 2)) := by gcongr
      _ = C * (|u| + 2) *
            Real.exp (-(Real.pi * |u|) / 2) := by
        dsimp only [C]
        ring
  rw [← hnormRec] at hupper
  calc
    ‖Complex.Gamma ((u : ℂ) * I)‖ ≤
        |u| * ‖Complex.Gamma ((u : ℂ) * I)‖ := by
      exact le_mul_of_one_le_left (norm_nonneg _) hu
    _ ≤ C * (|u| + 2) * Real.exp (-(Real.pi * |u|) / 2) := hupper

#print axioms norm_Gamma_half_vertical_le_exp
#print axioms exists_norm_Gamma_imaginary_le_exp

end

end GafniTao
