import TaoTrudgianYang2025.ZetaGeneralPerronEntry

/-!
# Arbitrary-order Mellin tails on a fixed zeta line

Increasing the actual cutoff derivative order makes the tail bounded
at every scale T >= N^a with a>1. The residue remains explicit.
-/

noncomputable section
open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem ZetaLargeValuePattern.cutoff_line_integrand_order_far_bound
    (P : ZetaLargeValuePattern) {a b : ℕ}
    (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {c : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1) (j : ℕ)
    {t u : ℝ} (ht : t ∈ Icc P.T (2*P.T))
    (hu : u ∉ zetaMellinSourceWindow P.T t) :
    ‖zetaCutoffLineIntegrand a b c t u‖ ≤
      (5*(1/(1-c)+2)*zetaCutoffMellinConstant (j+3) c*
        P.N^(c+(j : ℝ)+2)) * |u|^(-((j : ℝ)+2)) := by
  obtain ⟨habs,htime⟩ := zetaMellin_far_abs P.T_pos ht hu
  have huPos : 0 < |u| := (by linarith [P.T_pos] : 0 < P.T/2).trans habs
  have hweight : 1+|u+t| ≤ 5*(1+|u|) := by
    have := abs_add_le u t
    linarith
  have hz := (norm_zeta_mellin_left_boundary hc hc1 (u+t)).trans
    (mul_le_mul_of_nonneg_left hweight (by positivity))
  have hm := P.cutoff_mellin_bound hactive hne (σ := c) hc (j := j+3) (by omega) u
  have hexp : c+((j+3 : ℕ) : ℝ)-1 = c+(j : ℝ)+2 := by push_cast; ring
  rw [hexp] at hm
  have hden : 0 < 1+|u| := by positivity
  have hfactor : 0 ≤ 5*(1/(1-c)+2)*zetaCutoffMellinConstant (j+3) c*
      P.N^(c+(j : ℝ)+2) := by
    have := (zetaCutoffMellinConstant_pos (j+3) c).le
    have := (zero_lt_one.trans P.one_lt_N).le
    positivity
  rw [zetaCutoffLineIntegrand_eq,norm_mul]
  calc
    _ ≤ ((1/(1-c)+2)*(5*(1+|u|))) *
        (zetaCutoffMellinConstant (j+3) c*P.N^(c+(j : ℝ)+2)/(1+|u|)^(j+3)) :=
      mul_le_mul hz hm (norm_nonneg _) (by positivity)
    _ = (5*(1/(1-c)+2)*zetaCutoffMellinConstant (j+3) c*
        P.N^(c+(j : ℝ)+2))/(1+|u|)^(j+2) := by
      rw [show j+3 = (j+2)+1 by omega,pow_succ]
      field_simp
    _ ≤ (5*(1/(1-c)+2)*zetaCutoffMellinConstant (j+3) c*
        P.N^(c+(j : ℝ)+2))/|u|^(j+2) := by
      apply div_le_div_of_nonneg_left hfactor (pow_pos huPos _)
      exact pow_le_pow_left₀ huPos.le (by linarith) _
    _ = _ := by
      rw [div_eq_mul_inv,Real.rpow_neg huPos.le]
      norm_cast

def zetaLineTailConstant (j : ℕ) (c : ℝ) : ℝ :=
  (10*(1/(1-c)+2))*zetaCutoffMellinConstant (j+3) c*
    (2 : ℝ)^(j+1)/((j : ℝ)+1)

theorem zetaLineTailConstant_pos (j : ℕ) {c : ℝ} (hc1 : c < 1) :
    0 < zetaLineTailConstant j c := by
  unfold zetaLineTailConstant
  have := zetaCutoffMellinConstant_pos (j+3) c
  positivity

theorem ZetaLargeValuePattern.cutoff_line_order_far_integral
    (P : ZetaLargeValuePattern) {a b : ℕ}
    (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {c : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1) (j : ℕ)
    {t : ℝ} (ht : t ∈ Icc P.T (2*P.T)) :
    ‖∫ u : ℝ in (zetaMellinSourceWindow P.T t)ᶜ,
      zetaCutoffLineIntegrand a b c t u‖ ≤
      zetaLineTailConstant j c*P.N^(c+(j : ℝ)+2)/P.T^(j+1) := by
  let C : ℝ := 5*(1/(1-c)+2)*zetaCutoffMellinConstant (j+3) c*
    P.N^(c+(j : ℝ)+2)
  have hC : 0 ≤ C := by
    dsimp [C]
    have := (zetaCutoffMellinConstant_pos (j+3) c).le
    have := (zero_lt_one.trans P.one_lt_N).le
    positivity
  have hhalf : 0 < P.T/2 := by linarith [P.T_pos]
  have hneg : -((j : ℝ)+2) < -1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have htail : IntegrableOn (fun u : ℝ => C*|u|^(-((j : ℝ)+2)))
      (Icc (-(P.T/2)) (P.T/2))ᶜ :=
    (integrableOn_abs_rpow_compl_Icc hneg hhalf).const_mul C
  have hsubset := zetaMellinSourceWindow_compl_subset ht
  calc
    _ ≤ ∫ u : ℝ in (zetaMellinSourceWindow P.T t)ᶜ,
        ‖zetaCutoffLineIntegrand a b c t u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in (zetaMellinSourceWindow P.T t)ᶜ, C*|u|^(-((j : ℝ)+2)) := by
      apply integral_mono_ae
        (P.integrable_cutoff_line_integrand hactive hc hc1 t).norm.integrableOn
        (htail.mono_set hsubset)
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with u hu
      exact P.cutoff_line_integrand_order_far_bound hactive hne hc hc1 j ht hu
    _ ≤ ∫ u : ℝ in (Icc (-(P.T/2)) (P.T/2))ᶜ, C*|u|^(-((j : ℝ)+2)) :=
      setIntegral_mono_set htail (Eventually.of_forall fun u =>
        mul_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _))
        (Eventually.of_forall hsubset)
    _ = _ := by
      rw [integral_const_mul,integral_abs_rpow_compl_Icc hneg hhalf]
      have heq : -((j : ℝ)+2)+1 = -((j+1 : ℕ) : ℝ) := by push_cast; ring
      rw [heq,Real.rpow_neg hhalf.le,Real.rpow_natCast,div_pow]
      dsimp [C,zetaLineTailConstant]
      push_cast
      field_simp [P.T_pos.ne']
      ring

end TaoTrudgianYang2025
