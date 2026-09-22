import TaoTrudgianYang2025.BetaBufferedJets
import TaoTrudgianYang2025.AtkinsonPhaseSecondDerivatives

/-!
# Explicit derivative budgets for a weighted Fourier carrier

Only the first two derivatives of the actual phase are used. The constant
is computed from their displayed bound, never chosen separately for each phase.
-/

noncomputable section

open Complex Set
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem intervalC2Bound_fourierChar_of_derivative_bounds
    {F : ℝ → ℝ} {a b K : ℝ} (hK : 1 ≤ K)
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (hF₁ : ∀ x ∈ Icc a b, |deriv F x| ≤ K)
    (hF₂ : ∀ x ∈ Icc a b, |iteratedDeriv 2 F x| ≤ K)
    (T : ℝ) :
    IntervalC2Bound (fun x => (𝐞 (T*F x) : ℂ)) a b
      ((2*Real.pi)^2*K^2+2*Real.pi*K+1) (1+|T|) := by
  let C := (2*Real.pi)^2*K^2+2*Real.pi*K+1
  have hK₀ : 0 ≤ K := by linarith
  have hC₀ : 0 ≤ C := by dsimp [C]; positivity
  have hE : ContDiff ℝ 2 (atkinsonPhaseExponential (2*Real.pi*T)) := by
    have hcast : ContDiff ℝ 2 (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
    unfold atkinsonPhaseExponential
    fun_prop
  have he : (fun x => (𝐞 (T*F x) : ℂ)) =
      fun x => atkinsonPhaseExponential (2*Real.pi*T) (F x) := by
    funext x
    simp only [Real.fourierChar_apply,atkinsonPhaseExponential]
    congr 1
    push_cast
    ring
  rw [he]
  refine ⟨hC₀,by positivity,fun x hx => hE.contDiffAt.comp x (hF x hx),?_,?_,?_⟩
  · intro x hx
    rw [(norm_atkinsonPhaseExponential_derivatives (2*Real.pi*T) (F x)).1]
    have hh : 0 ≤ (2*Real.pi)^2*K^2+2*Real.pi*K := by positivity
    linarith
  · intro x hx
    have hd : HasDerivAt (fun y => atkinsonPhaseExponential (2*Real.pi*T) (F y))
        (deriv F x • deriv (atkinsonPhaseExponential (2*Real.pi*T)) (F x)) x :=
      (hE.differentiable (by norm_num)).differentiableAt.hasDerivAt.scomp
        (h := F) x ((hF x hx).differentiableAt (by norm_num)).hasDerivAt
    rw [hd.deriv,norm_smul,Real.norm_eq_abs,
      (norm_atkinsonPhaseExponential_derivatives (2*Real.pi*T) (F x)).2.1,
      abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    calc
      _ ≤ K*(2*Real.pi*|T|) :=
        mul_le_mul_of_nonneg_right (hF₁ x hx) (by positivity)
      _ ≤ C*(1+|T|) := by
        have hc : 2*Real.pi*K ≤ C := by
          have hs : 0 ≤ (2*Real.pi)^2*K^2 := by positivity
          dsimp [C]
          linarith
        have hh := mul_le_mul_of_nonneg_right hc (abs_nonneg T)
        nlinarith
  · intro x hx
    rw [iteratedDeriv_two_comp_real hE.contDiffAt (hF x hx)]
    apply (norm_add_le _ _).trans
    simp only [norm_smul,Real.norm_eq_abs,abs_pow,sq_abs,
      (norm_atkinsonPhaseExponential_derivatives (2*Real.pi*T) (F x)).2.1,
      (norm_atkinsonPhaseExponential_derivatives (2*Real.pi*T) (F x)).2.2,
      abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    have hsq := pow_le_pow_left₀ (abs_nonneg (deriv F x)) (hF₁ x hx) 2
    rw [sq_abs] at hsq
    calc
      _ ≤ K^2*(2*Real.pi*T)^2+K*(2*Real.pi*|T|) :=
        add_le_add (mul_le_mul_of_nonneg_right hsq (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (hF₂ x hx) (by positivity))
      _ ≤ C*(1+|T|)^2 := by
        have hT₁ : |T| ≤ (1+|T|)^2 := by nlinarith [abs_nonneg T]
        have hT₂ : T^2 ≤ (1+|T|)^2 := by nlinarith [sq_abs T,abs_nonneg T]
        have h₁ := mul_le_mul_of_nonneg_left hT₁
          (show 0 ≤ 2*Real.pi*K by positivity)
        have h₂ := mul_le_mul_of_nonneg_left hT₂
          (show 0 ≤ (2*Real.pi)^2*K^2 by positivity)
        dsimp [C]
        nlinarith [sq_nonneg (1+|T|)]

theorem modelPhaseBufferedCutoff_uniform_c2 :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (l r η a b : ℝ), 0 < η →
      IntervalC2Bound (fun x => (modelPhaseBufferedCutoff l r η x : ℂ))
        a b M η⁻¹ := by
  obtain ⟨M,hM,hjets⟩ := modelPhaseBufferedCutoff_uniform_ordered_jets 2
  refine ⟨M,hM,?_⟩
  intro l r η a b hη
  have hχ := modelPhaseBufferedCutoff_contDiff l r η
  refine ⟨by linarith,by positivity,?_,?_,?_,?_⟩
  · intro x hx
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (hχ.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  · intro x hx
    simpa only [iteratedDeriv_zero,pow_zero,mul_one,Complex.norm_real,
      Real.norm_eq_abs] using hjets l r η x hη 0 (by norm_num)
  · intro x hx
    have he := iteratedDeriv_ofReal_fun (x := x) (hχ.contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    simp only [iteratedDeriv_one] at he
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    simpa only [iteratedDeriv_one,pow_one] using hjets l r η x hη 1 (by norm_num)
  · intro x hx
    rw [iteratedDeriv_ofReal_fun (hχ.contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),Complex.norm_real,Real.norm_eq_abs]
    exact hjets l r η x hη 2 le_rfl

end TaoTrudgianYang2025
