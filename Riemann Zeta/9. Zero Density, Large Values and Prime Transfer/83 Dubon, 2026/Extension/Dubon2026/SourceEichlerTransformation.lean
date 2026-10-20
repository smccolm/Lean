/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.SourceEichlerIntegral
import Dubon2026.SourcePeriodCoefficientAction

/-! The exact Eichler-integral transformation law, with the original periods.
Adapted from TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5.
DUB-17/18 -> modular Galois association -> integral Hecke finiteness ->
actual period injectivity -> an Eichler primitive invariant when periods vanish.
The correction term is the genuine already constructed cusp integral; the
vertical integral identity and geometric substitution prove the transformation.
-/

namespace Dubon2026
noncomputable section
open Complex Filter Function MeasureTheory MvPolynomial Set
open Matrix.SpecialLinearGroup ModularGroup OnePoint SourceModularSymbols
open UpperHalfPlane hiding I
open scoped Real Nat Manifold MatrixGroups ModularForm

/-- For `g = !![a, b; c, d]` of positive determinant,
`(az + b) - (g • τ)(cz + d) = det g · (z - τ) / (cτ + d)`: dividing by `cz + d` gives the
difference formula `g • z - g • τ = det g · (z - τ) / ((cz + d)(cτ + d))`, in the form that
clears the denominator of `g • z`. -/
private theorem sourceNum_sub_smul_mul_denom {g : GL (Fin 2) ℝ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (τ z : ℍ) :
    num g z - (g • τ : ℍ) * denom g z =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) * ((z : ℂ) - τ) / denom g τ := by
  rw [coe_smul_of_det_pos (by rwa [Matrix.GeneralLinearGroup.val_det_apply]),
    eq_div_iff (denom_ne_zero g τ)]
  field_simp [denom_ne_zero g τ]
  simp only [num, denom, Matrix.det_fin_two, Complex.ofReal_sub, Complex.ofReal_mul]
  ring
variable {Γ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ] {k : ℤ} {n : ℕ} {h : ℝ}

/-- The binary form `(X₀ - τ X₁)ⁿ`, whose period integrand is `f(z) (z - τ)ⁿ`. -/
private def eichlerForm (n : ℕ) (τ : ℂ) : homogeneousSubmodule (Fin 2) ℂ n :=
  ⟨(X 0 - C τ * X 1) ^ n, by
    simpa using ((isHomogeneous_X ℂ (0 : Fin 2)).sub (isHomogeneous_C_mul_X τ 1)).pow n⟩

private lemma periodIntegrand_eichlerForm (f : ℍ → ℂ) (n : ℕ) (τ : ℂ) :
    periodIntegrand f (eichlerForm n τ) = fun z ↦ f z * ((z : ℂ) - τ) ^ n := by
  funext z
  simp [eichlerForm]

/-- The image of `σ ∈ SL(2, ℤ)` in `GL(2, ℚ)` has determinant `1`. -/
private lemma det_mapGL_rat (σ : SL(2, ℤ)) :
    ((mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]

/-- Slashing the integrand `f(z) (z - σ • τ)ⁿ` in weight `2` by `σ ∈ SL(2, ℤ)` gives
`(cτ + d)⁻ⁿ (f ∣[n + 2] σ)(z) (z - τ)ⁿ`. -/
private lemma periodIntegrand_eichlerForm_slash (hk : k = n + 2) (f : ℍ → ℂ) (σ : SL(2, ℤ))
    (τ z : ℍ) :
    (periodIntegrand f (eichlerForm n (σ • τ : ℍ)) ∣[(2 : ℤ)] mapGL ℚ σ) z =
      denom σ τ ^ (-(n : ℤ)) * ((f ∣[k] σ) z * ((z : ℂ) - τ) ^ n) := by
  have hdet : 0 < ((mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [det_mapGL_rat]
    exact one_pos
  rw [periodIntegrand_slash_apply hk f _ hdet, sourceRat_slash_mapGL,
    ← sourceSL_coe_eq_mapGL, ← ModularForm.SL_slash,
    Matrix.SpecialLinearGroup.map_mapGL, ← sourceSL_coe_eq_mapGL]
  simp only [det_mapGL_rat, Rat.cast_one, one_zpow, one_mul, eichlerForm, map_pow, map_sub, aeval_X,
    map_mul, aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Algebra.algebraMap_self, RingHom.id_apply]
  have hσ : ((σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.det_coe]
  rw [sl_moeb, sourceNum_sub_smul_mul_denom (hσ ▸ one_pos), hσ, Complex.ofReal_one, one_mul, div_pow,
    zpow_neg, zpow_natCast, div_eq_inv_mul]
  ring

/-- **The transformation law of the Eichler integral.** Let `f` be a cusp form of weight
`k = n + 2` on an arithmetic subgroup, `σ ∈ SL(2, ℤ)`, and `f'` a cusp form (for any subgroup
with a positive strict period `h'`) with `f' = f ∣[k] σ`. Then the Eichler integrals
`E_f = E_{n+1} f` and `E_{f'}` satisfy

`(E_f ∣[-n] σ)(τ) = E_{f'}(τ) - (-2πi)ⁿ⁺¹ / n! · ∫_{σ⁻¹ • ∞}^{i∞} f'(z) (z - τ)ⁿ dz`,

the integral taken along the geodesic between the two cusps. By
`TauCeti.ModularSymbols.sourceCuspIntegral_mul_sub_pow` the correction term is a polynomial in `τ` of
degree at most `n` whose coefficients are periods of `f'`. -/
theorem sourceCuspForm_eichlerIntegral_slash_apply [Γ.IsArithmetic] [CuspFormClass F Γ k]
    (hk : k = n + 2) (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    {Γ' : Subgroup (GL (Fin 2) ℝ)} {F' : Type*} [FunLike F' ℍ ℂ] [CuspFormClass F' Γ' k]
    (f' : F') {h' : ℝ} (hh' : 0 < h') (hΓ' : h' ∈ Γ'.strictPeriods) (σ : SL(2, ℤ))
    (hf' : ⇑f' = ⇑f ∣[k] σ) (τ : ℍ) :
    (sourceEichlerIntegral h (n + 1) f ∣[-(n : ℤ)] σ) τ =
      sourceEichlerIntegral h' (n + 1) f' τ - (-2 * π * I) ^ (n + 1) / n ! *
        sourceCuspIntegral (fun z ↦ f' z * ((z : ℂ) - τ) ^ n) (mapGL ℚ σ⁻¹ • ∞) ∞ := by
  set c : ℂ := (-2 * π * I) ^ (n + 1) / (n ! : ℂ)
  set j : ℂ := denom σ τ
  have hdet : 0 < ((mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [det_mapGL_rat]
    exact one_pos
  have hslash : periodIntegrand f (eichlerForm n (σ • τ : ℍ)) ∣[(2 : ℤ)] mapGL ℚ σ =
      j ^ (-(n : ℤ)) • fun z : ℍ ↦ f' z * ((z : ℂ) - τ) ^ n := by
    funext z
    rw [periodIntegrand_eichlerForm_slash hk, hf', Pi.smul_apply, smul_eq_mul]
  have hsmul : (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (mapGL ℚ σ) • τ : ℍ) =
      σ • τ := by
    rw [Matrix.SpecialLinearGroup.map_mapGL, ← sourceSL_coe_eq_mapGL,
      ← sl_moeb]
  -- along the vertical ray from `τ₀`, `z - τ₀ = t i`
  have hcoe (τ₀ : ℍ) {t : ℝ} (ht : t ∈ Ioi 0) :
      ((ofComplex ((τ₀ : ℂ) + t * I) : ℍ) : ℂ) - τ₀ = t * I := by
    rw [ofComplex_apply_of_im_pos (by simpa using add_pos τ₀.im_pos (show (0 : ℝ) < t from ht)),
      coe_mk, add_sub_cancel_left]
  have hA : ∫ t in Ioi (0 : ℝ),
      (j ^ (-(n : ℤ)) • fun z : ℍ ↦ f' z * ((z : ℂ) - τ) ^ n) (ofComplex (τ + t * I)) * I =
        j ^ (-(n : ℤ)) * ∫ t in Ioi (0 : ℝ), f' (ofComplex (τ + t * I)) * (t * I) ^ n * I := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul, hcoe τ ht]
    ring
  have hB : ∫ t in Ioi (0 : ℝ), (fun z : ℍ ↦ f z * ((z : ℂ) - (σ • τ : ℍ)) ^ n)
      (ofComplex ((σ • τ : ℍ) + t * I)) * I =
        ∫ t in Ioi (0 : ℝ), f (ofComplex ((σ • τ : ℍ) + t * I)) * (t * I) ^ n * I :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ by simp only [hcoe (σ • τ) ht]
  have hC : sourceCuspIntegral (fun z : ℍ ↦ f z * ((z : ℂ) - (σ • τ : ℍ)) ^ n) ∞ (mapGL ℚ σ • ∞) =
      j ^ (-(n : ℤ)) * sourceCuspIntegral (fun z ↦ f' z * ((z : ℂ) - τ) ^ n) (mapGL ℚ σ⁻¹ • ∞) ∞ := by
    rw [← sourceCuspIntegral_smul, ← hslash, sourceCuspIntegral_slash _ hdet, smul_smul, ← map_mul,
      mul_inv_cancel, map_one, one_smul, periodIntegrand_eichlerForm]
  -- the substitution `z ↦ σ • z`, by `TauCeti.sourceIntegral_Ioi_slash_eq_add_cuspIntegral`
  have key := sourceIntegral_Ioi_slash_eq_add_cuspIntegral
    (mdifferentiable_periodIntegrand (ModularFormClass.holo f) (eichlerForm n (σ • τ : ℍ)))
    (fun _ hg ↦ integrableOn_sourceResToImagAxis_periodIntegrand_slash_Ici f hk _ hg)
    (fun _ hg ↦ tendsto_periodIntegrand_slash f hk _ hg) hdet τ ?_ ?_
  · rw [hslash, hsmul, periodIntegrand_eichlerForm, hA, hB, hC, zpow_neg, zpow_natCast] at key
    rw [ModularForm.SL_slash_apply, neg_neg, zpow_natCast,
      sourceCuspForm_eichlerIntegral_eq_integral f hh hΓ,
      sourceCuspForm_eichlerIntegral_eq_integral f' hh' hΓ']
    have hj : j ^ n * (j ^ n)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero n (denom_ne_zero σ τ))
    have key' := congrArg (j ^ n * ·) key
    dsimp only at key'
    rw [mul_add, ← mul_assoc, hj, one_mul, ← mul_assoc, hj, one_mul] at key'
    linear_combination (-c) * key'
  -- the two vertical integrands are integrable, by `sourceCuspForm_integrableOn_eichlerIntegrand`
  · rw [hslash]
    refine IntegrableOn.congr_fun ((sourceCuspForm_integrableOn_eichlerIntegrand f' hh' hΓ' n
      τ).const_mul (j ^ (-(n : ℤ)) * I⁻¹)) (fun t ht ↦ ?_) measurableSet_Ioi
    simp only [Pi.smul_apply, smul_eq_mul, hcoe τ ht]
    field_simp
  · rw [hsmul, periodIntegrand_eichlerForm]
    refine IntegrableOn.congr_fun ((sourceCuspForm_integrableOn_eichlerIntegrand f hh hΓ n
      (σ • τ)).const_mul I⁻¹) (fun t ht ↦ ?_) measurableSet_Ioi
    simp only [hcoe (σ • τ) ht]
    field_simp

/-- **The transformation law of the Eichler integral in the level.** For a cusp form `f` of
weight `k = n + 2` on an arithmetic subgroup `Γ` and `σ ∈ SL(2, ℤ)` with `σ ∈ Γ`, the Eichler
integral `E_f = E_{n+1} f` transforms in weight `-n` up to the period polynomial of `f` at `σ`:

`(E_f ∣[-n] σ)(τ) = E_f(τ) - (-2πi)ⁿ⁺¹ / n! · ∫_{σ⁻¹ • ∞}^{i∞} f(z) (z - τ)ⁿ dz`. -/
theorem sourceCuspForm_eichlerIntegral_slash_apply_of_mem [Γ.IsArithmetic] [CuspFormClass F Γ k]
    (hk : k = n + 2) (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {σ : SL(2, ℤ)}
    (hσ : mapGL ℝ σ ∈ Γ) (τ : ℍ) :
    (sourceEichlerIntegral h (n + 1) f ∣[-(n : ℤ)] σ) τ =
      sourceEichlerIntegral h (n + 1) f τ - (-2 * π * I) ^ (n + 1) / n ! *
        sourceCuspIntegral (fun z ↦ f z * ((z : ℂ) - τ) ^ n) (mapGL ℚ σ⁻¹ • ∞) ∞ :=
  sourceCuspForm_eichlerIntegral_slash_apply hk f hh hΓ f hh hΓ σ (by
    rw [ModularForm.SL_slash, sourceSL_coe_eq_mapGL,
      SlashInvariantFormClass.slash_action_eq f _ hσ]) τ

/-- **Vanishing periods make the Eichler integral invariant.** For a cusp form `f` of weight
`k = n + 2` on an arithmetic subgroup `Γ` and `σ ∈ SL(2, ℤ)` with `σ ∈ Γ`, if the periods
`∫_{σ⁻¹ • ∞}^{i∞} f(z) zʲ dz` vanish for `j ≤ n`, then the Eichler integral `E_f = E_{n+1} f` is
invariant under `σ` in weight `-n`: `E_f ∣[-n] σ = E_f`. -/
theorem sourceCuspForm_eichlerIntegral_slash_eq_of_sourceCuspIntegral_eq_zero [Γ.IsArithmetic]
    [CuspFormClass F Γ k] (hk : k = n + 2) (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    {σ : SL(2, ℤ)} (hσ : mapGL ℝ σ ∈ Γ)
    (hper : ∀ j ≤ n, sourceCuspIntegral (fun z ↦ f z * (z : ℂ) ^ j) (mapGL ℚ σ⁻¹ • ∞) ∞ = 0) :
    sourceEichlerIntegral h (n + 1) f ∣[-(n : ℤ)] σ = sourceEichlerIntegral h (n + 1) f := by
  funext τ
  rw [sourceCuspForm_eichlerIntegral_slash_apply_of_mem hk f hh hΓ hσ, sourceCuspIntegral_mul_sub_pow f hk,
    Finset.sum_eq_zero fun j hj ↦ by rw [hper j (Finset.mem_range_succ_iff.mp hj), mul_zero],
    mul_zero, sub_zero]

end
end Dubon2026
