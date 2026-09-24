import TaoTrudgianYang2025.ZetaRealMomentKernel

/-!
# Actual zeta moments on arbitrary fixed lines

These definitions retain the literal source window [T/2,3T]. The finite
consumer accepts only a pointwise convolution entry; it derives the
cardinality estimate and retains all constants and physical scales.
-/

noncomputable section
open Complex Finset MeasureTheory Set
namespace TaoTrudgianYang2025

def zetaMomentLineNorm (c t : ℝ) : ℝ := ‖riemannZeta ((c : ℂ)+(t : ℂ)*I)‖

theorem continuous_zetaMomentLineNorm {c : ℝ} (hc : c ≠ 1) :
    Continuous (zetaMomentLineNorm c) := by
  unfold zetaMomentLineNorm
  apply Continuous.norm
  rw [continuous_iff_continuousAt]
  intro t
  have hne : (c : ℂ)+(t : ℂ)*I ≠ 1 := by
    intro hh
    have hr := congrArg Complex.re hh
    apply hc
    simpa using hr
  exact (differentiableAt_riemannZeta hne).continuousAt.comp
    (f := fun u : ℝ => (c : ℂ)+(u : ℂ)*I) (by fun_prop)

def zetaLineMomentConvolution (c T t : ℝ) : ℝ :=
  ∫ u in T/2..3*T, zetaMomentKernel t u*zetaMomentLineNorm c u

def zetaLineMoment (c p T : ℝ) : ℝ :=
  ∫ u in T/2..3*T, zetaMomentLineNorm c u^p

theorem sum_zetaLineMomentConvolution_rpow
    {c p T : ℝ} (hc : c ≠ 1) (hp : 1 ≤ p)
    (W : Finset ℝ) (hT : 0 < T)
    (hSep : RiemannZeta.GuthMaynard.IsSeparated 1 W)
    (hW : ∀ t ∈ W, t ∈ Icc T (2*T)) :
    (∑ t ∈ W, zetaLineMomentConvolution c T t^p) ≤
      zetaMomentLogLoss T^p*zetaLineMoment c p T :=
  sum_convolution_realMoment_le_moment W hT hp hSep hW
    (zetaMomentLineNorm c) (continuous_zetaMomentLineNorm hc) (fun _ => norm_nonneg _)

theorem zetaLineMomentConvolution_largeValues
    {c p T V : ℝ} (hc : c ≠ 1) (hp : 1 ≤ p)
    (W : Finset ℝ) (hT : 0 < T) (hV : 0 ≤ V)
    (hSep : RiemannZeta.GuthMaynard.IsSeparated 1 W)
    (hW : ∀ t ∈ W, t ∈ Icc T (2*T))
    (hLarge : ∀ t ∈ W, V ≤ zetaLineMomentConvolution c T t) :
    (W.card : ℝ)*V^p ≤ zetaMomentLogLoss T^p*zetaLineMoment c p T := by
  apply le_trans _ (sum_zetaLineMomentConvolution_rpow hc hp W hT hSep hW)
  calc
    _ = ∑ _t ∈ W, V^p := by simp
    _ ≤ _ := Finset.sum_le_sum fun t ht =>
      Real.rpow_le_rpow hV (hLarge t ht) (by linarith)

theorem ZetaLargeValuePattern.realMoment_cardinality_of_convolution
    (P : ZetaLargeValuePattern) {c p C : ℝ} (hc : c ≠ 1) (hp : 1 ≤ p) (hC : 0 < C)
    (hEntry : ∀ t ∈ P.ordinates,
      P.V ≤ C*P.N^c*zetaLineMomentConvolution c P.T t) :
    (P.ordinates.card : ℝ)*P.V^p ≤
      C^p*P.N^(c*p)*zetaMomentLogLoss P.T^p*zetaLineMoment c p P.T := by
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hfactor : 0 < C*P.N^c := mul_pos hC (Real.rpow_pos_of_pos hN c)
  have hRange (t : ℝ) (ht : t ∈ P.ordinates) : t ∈ Icc P.T (2*P.T) := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have h := zetaLineMomentConvolution_largeValues hc hp P.ordinates P.T_pos
    (div_nonneg P.V_pos.le hfactor.le) P.ordinates_oneSeparated hRange
    (fun t ht => (div_le_iff₀ hfactor).mpr (by nlinarith [hEntry t ht]))
  have hmul := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hfactor.le p)
  have hcancel : (C*P.N^c)^p*((P.ordinates.card : ℝ)*(P.V/(C*P.N^c))^p) =
      (P.ordinates.card : ℝ)*P.V^p := by
    rw [Real.div_rpow P.V_pos.le hfactor.le]
    field_simp [(Real.rpow_pos_of_pos hfactor p).ne']
  have hnorm : (C*P.N^c)^p = C^p*P.N^(c*p) := by
    rw [Real.mul_rpow hC.le (Real.rpow_nonneg hN.le c), ← Real.rpow_mul hN.le]
  rw [hcancel,hnorm] at hmul
  simpa only [mul_assoc] using hmul

end TaoTrudgianYang2025
