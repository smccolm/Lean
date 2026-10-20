/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.SourcePeriodAxis
import Dubon2026.SourcePeriodSlash
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ModularForms.NormTrace

/-! Analytic input to the actual original Hecke period pairing.
Selected from TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5,
with Chris Birkbeck's Apache-2.0 source contributions retained.
DUB-17/18 -> modular Galois association -> integral Hecke finiteness ->
period injectivity and adjointness -> convergent, additive cusp integrals.
Only declarations needed by that dependency chain are selected.
-/

namespace Dubon2026
open Complex ModularGroup UpperHalfPlane
open scoped ModularForm MatrixGroups Pointwise

/-- **The `S`-involution on the imaginary axis**: slashing by `S` turns `t` into `1 / t`,
`(F ∣[k] S) (i t) = i ^ (-k) t ^ (-k) F (i / t)`. This is the reflection underlying the
functional equation of the L-function. -/
theorem sourceResToImagAxis_slash_S (F : ℍ → ℂ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    sourceResToImagAxis (F ∣[k] S) t =
      Complex.I ^ (-k) * (t : ℂ) ^ (-k) * sourceResToImagAxis F (1 / t) := by
  have ht' : (0 : ℝ) < 1 / t := by positivity
  have h : mk _ (⟨Complex.I * t, by simpa using ht⟩ : ℍ).im_inv_neg_coe_pos =
      (⟨Complex.I * (1 / t : ℝ), by simpa using ht'⟩ : ℍ) :=
    UpperHalfPlane.ext (by
      -- `(-(i t))⁻¹ = i / t`, since `i * i = -1`
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      push_cast
      field_simp
      linear_combination -hI)
  rw [sourceResToImagAxis_of_pos _ ht, SlashInvariantForm.slash_S_apply, h,
    sourceResToImagAxis_of_pos F ht']
  simp only [mul_zpow]
  ring

/-- **The `S`-involution in weight `2`**: `(F ∣[2] S) (i t) = -t⁻² F (i / t)`, the reflection
`t ↦ 1 / t` of the axis together with its Jacobian. -/
theorem sourceResToImagAxis_slash_two_S (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    sourceResToImagAxis (F ∣[(2 : ℤ)] S) t = -((t : ℂ) ^ 2)⁻¹ * sourceResToImagAxis F t⁻¹ := by
  rw [sourceResToImagAxis_slash_S F 2 ht, one_div]
  have hI : (Complex.I : ℂ) ^ (-(2 : ℤ)) = -1 := by
    rw [zpow_neg, zpow_two, Complex.I_mul_I]
    norm_num
  rw [hI, zpow_neg, zpow_two, sq]
  ring

open MeasureTheory Set in
/-- **Convergence at the finite end from convergence at `i∞` of the reflection.** If the
restriction of `G` to the imaginary axis is integrable near `i∞`, and so is that of the weight-`2`
reflection `G ∣[2] S`, then the restriction of `G` is integrable on the whole positive axis: the
substitution `t ↦ 1 / t` carries the tail of `G ∣[2] S` onto the initial segment of `G`. -/
theorem sourceIntegrableOn_resToImagAxis_Ioi_of_slash_S {G : ℍ → ℂ}
    (h : IntegrableOn (sourceResToImagAxis G) (Ici 1))
    (hS : IntegrableOn (sourceResToImagAxis (G ∣[(2 : ℤ)] S)) (Ici 1)) :
    IntegrableOn (sourceResToImagAxis G) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ (h.mono_set Ioi_subset_Ici_self)
  -- the tail of the reflection, as a function on the whole axis
  have hψ : IntegrableOn ((Ici 1).indicator (sourceResToImagAxis (G ∣[(2 : ℤ)] S))) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ici).mpr hS).integrableOn
  have hsub := (integrableOn_Ioi_comp_rpow_iff _ (by norm_num : (-1 : ℝ) ≠ 0)).mpr hψ
  simp only [Complex.real_smul] at hsub
  -- under `t ↦ 1 / t`, that tail becomes minus the initial segment of `G`
  have key : EqOn (fun x : ℝ ↦ ((|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1) : ℝ) : ℂ) *
      (Ici 1).indicator (sourceResToImagAxis (G ∣[(2 : ℤ)] S)) (x ^ (-1 : ℝ)))
      (-(Ioc 0 1).indicator (sourceResToImagAxis G)) (Ioi 0) := by
    intro x hx
    have hx : (0 : ℝ) < x := hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    -- the Jacobian `|p| x ^ (p - 1)` of `x ↦ x ^ p` at `p = -1` is `x⁻²`
    have hexp : (-1 : ℝ) - 1 = -2 := by norm_num
    simp only [Pi.neg_apply, indicator_apply, mem_Ici, mem_Ioc, Real.rpow_neg_one,
      one_le_inv₀ hx, hx, true_and]
    rw [hexp, Real.rpow_neg hx.le, Real.rpow_two, abs_neg, abs_one, one_mul]
    split_ifs with hx1
    · rw [sourceResToImagAxis_slash_two_S G (inv_pos.mpr hx), inv_inv]
      push_cast
      field_simp
    · simp
  have hneg := (hsub.congr_fun key measurableSet_Ioi).neg
  rw [neg_neg] at hneg
  have := (integrable_indicator_iff measurableSet_Ioc).mp hneg
  rwa [IntegrableOn, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Ioi_self] at this

/-- **A positive diagonal matrix rescales the imaginary axis**: for `d = diag(a, b) ∈ GL(2, ℚ)`
with `ab > 0`, the weight-`2` slash by `d` restricts to the axis as `(F ∣[2] d) (i t) = r F (i r t)`
with `r = a / b > 0`, the rescaling `t ↦ r t` of the axis together with its Jacobian. -/
theorem sourceResToImagAxis_slash_two_of_diagonal (F : ℍ → ℂ) {d : GL (Fin 2) ℚ} (h₁₀ : d 1 0 = 0)
    (h₀₁ : d 0 1 = 0) (hd : 0 < (d : Matrix (Fin 2) (Fin 2) ℚ).det) (t : ℝ) :
    sourceResToImagAxis (F ∣[(2 : ℤ)] d) t =
      (((d 0 0 : ℝ) / d 1 1 : ℝ) : ℂ) * sourceResToImagAxis F ((d 0 0 : ℝ) / d 1 1 * t) := by
  have hdet : (d : Matrix (Fin 2) (Fin 2) ℚ).det = d 0 0 * d 1 1 := by
    rw [Matrix.det_fin_two, h₁₀, h₀₁]
    ring
  have hd' : 0 < d 0 0 * d 1 1 := hdet ▸ hd
  -- the axis is rescaled by the positive ratio `r = d₀₀ / d₁₁`
  set r : ℝ := (d 0 0 : ℝ) / d 1 1 with hr
  have hr0 : 0 < r := by
    have : (0 : ℚ) < d 0 0 / d 1 1 := div_pos_iff.mpr (mul_pos_iff.mp hd')
    rw [hr]
    exact_mod_cast this
  rcases le_or_gt t 0 with ht | ht
  · rw [sourceResToImagAxis_of_nonpos _ ht, sourceResToImagAxis_of_nonpos _ (by nlinarith), mul_zero]
  have hrt : 0 < r * t := mul_pos hr0 ht
  have hdet_pos : 0 < ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) d).det : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact sourceDet_map_ratCast_pos hd
  have hdetd : ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) d).det : ℝ) =
      (d 0 0 : ℝ) * d 1 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_map_apply,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, eq_ratCast, Rat.cast_mul]
  rw [sourceResToImagAxis_of_pos _ ht, sourceResToImagAxis_of_pos _ hrt,
    sourceRat_slash_apply_of_det_pos _ hd]
  -- `d` fixes `∞`, so its denominator is the constant `d₁₁`
  have hden : denom (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) d)
      (⟨Complex.I * t, by simpa using ht⟩ : ℍ) = ((d 1 1 : ℝ) : ℂ) := by
    simp [denom, Matrix.GeneralLinearGroup.map_apply, h₁₀]
  -- `d` acts on the axis as the rescaling `i t ↦ i (r t)`
  have hsmul : Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) d •
      (⟨Complex.I * t, by simpa using ht⟩ : ℍ) =
        ⟨Complex.I * ((r * t : ℝ) : ℂ), by simpa using hrt⟩ := by
    ext1
    rw [coe_smul_of_det_pos hdet_pos, hden]
    simp only [num, Matrix.GeneralLinearGroup.map_apply, eq_ratCast, h₀₁, Rat.cast_zero, hr]
    push_cast
    ring
  -- the automorphy factor `det d ^ (2 - 1) · d₁₁ ^ (-2)` of `d` in weight `2` is the constant `r`
  have h21 : (2 : ℤ) - 1 = 1 := by norm_num
  have hc : ((((d 0 0 : ℝ) * (d 1 1 : ℝ) : ℝ)) : ℂ) ^ ((2 : ℤ) - 1) *
      ((d 1 1 : ℝ) : ℂ) ^ (-(2 : ℤ)) = (r : ℂ) := by
    rw [hr, h21, zpow_one, zpow_neg, zpow_two]
    push_cast
    field_simp
  rw [hsmul, hden, hdetd, abs_of_pos (by exact_mod_cast hd'), mul_assoc, hc, mul_comm]

open Asymptotics Filter in
/-- **A cusp form slashed by a rational matrix decays exponentially at `i∞`**: `f ∣[k] g` is a
cusp form on the conjugate level `g⁻¹ Γ g`, which is again arithmetic, so it has the exponential
decay of a cusp form at `i∞`, uniformly in the real part. -/
theorem sourceExists_isBigO_rat_slash_exp {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {F : Type*} [FunLike F ℍ ℂ] {k : ℤ} [CuspFormClass F Γ k] (f : F) (g : GL (Fin 2) ℚ) :
    ∃ c > 0, (f ∣[k] g) =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im) := by
  set g' : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g with hg'
  -- the conjugate level is arithmetic; `Rat.castHom ℝ` and `algebraMap ℚ ℝ` agree because ring
  -- homomorphisms out of `ℚ` are unique (`Rat.subsingleton_ringHom`)
  have : (ConjAct.toConjAct g'⁻¹ • Γ).IsArithmetic := by
    simpa [hg', Subsingleton.elim (Rat.castHom ℝ) (algebraMap ℚ ℝ), map_inv]
      using Subgroup.IsArithmetic.conj Γ g⁻¹
  obtain ⟨c, hc, hO⟩ := CuspFormClass.exp_decay_atImInfty' (CuspForm.translate f g')
  exact ⟨c, hc, hO⟩

open Asymptotics Filter in
/-- **A cusp form slashed by a rational matrix decays exponentially along the imaginary axis**,
the restriction of `sourceExists_isBigO_rat_slash_exp` to the axis. -/
theorem sourceExists_isBigO_resToImagAxis_rat_slash_exp {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {F : Type*} [FunLike F ℍ ℂ] {k : ℤ} [CuspFormClass F Γ k] (f : F) (g : GL (Fin 2) ℚ) :
    ∃ c > 0, sourceResToImagAxis (f ∣[k] g) =O[atTop] fun t ↦ Real.exp (-c * t) := by
  obtain ⟨c, hc, hO⟩ := sourceExists_isBigO_rat_slash_exp f g
  refine ⟨c, hc, (sourceIsBigO_resToImagAxis hO).congr' EventuallyEq.rfl ?_⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ofComplex_apply_of_im_pos, ht]

end Dubon2026
