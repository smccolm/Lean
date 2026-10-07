import Dubon2026.CuspTraceMellin
import Dubon2026.PeterssonStripMellin

/-! # Actual hyperbolic strip density for the finite cusp trace -/

namespace Dubon2026

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory Set
open scoped MatrixGroups ENNReal

noncomputable section

variable {N : ℕ} {H : Subgroup SL(2, ℤ)} [Fintype (SL(2, ℤ) ⧸ H)]
  (hH : Gamma N ≤ H) {k : ℤ} (f : CuspForm (H.map (mapGL ℝ)) k)

/-- The actual aggregate horizontal cusp energy is continuous at every positive height. -/
theorem continuous_cuspTrace_horizontal {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => ∑ q : SL(2, ℤ) ⧸ H,
      ‖cuspCosetFamily hH f q (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2) := by
  apply continuous_finsetSum
  intro q _
  have he : (fun x : ℝ => cuspCosetFamily hH f q (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))) =
      (fun x : ℝ => cuspCosetFamily hH f q ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩) := by
    funext x
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
  rw [show (fun x : ℝ => ‖cuspCosetFamily hH f q (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2) =
      (fun x : ℝ => ‖cuspCosetFamily hH f q ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2) by
        funext x
        rw [congrFun he x]]
  exact ((ModularFormClass.continuous (cuspCosetFamily hH f q)).comp
    ((Complex.continuous_ofReal.add continuous_const).upperHalfPlaneMk (fun _ => by simpa using hy))).norm.pow 2

/-- The nonnegative horizontal trace integral is exactly the coercion of its literal finite energy integral. -/
theorem lintegral_cuspTrace_horizontal {y : ℝ} (hy : 0 < y) :
    (∫⁻ x : ℝ in Ico 0 1, ENNReal.ofReal (∑ q : SL(2, ℤ) ⧸ H,
      ‖cuspCosetFamily hH f q (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2)) =
      ENNReal.ofReal (cuspTraceHorizontalEnergy hH f y) := by
  have hc := continuous_cuspTrace_horizontal hH f hy
  have hi := (intervalIntegrable_iff_integrableOn_Ico_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (hc.intervalIntegrable (μ := (volume : Measure ℝ)) (a := 0) (b := 1))
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x => Finset.sum_nonneg (fun q _ => sq_nonneg _))),
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rfl

/-- The true finite Petersson trace on the hyperbolic strip has the precise shifted Mellin density. -/
theorem cuspTrace_unitStrip_mellin (σ : ℝ) :
    (∫⁻ z in upperHalfPlaneUnitStrip, ENNReal.ofReal (z.im ^ σ) *
      ENNReal.ofReal (∑ q : SL(2, ℤ) ⧸ H,
        ‖petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z‖)) =
      ∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal (y ^ (σ + (k : ℝ) - 2) * cuspTraceHorizontalEnergy hH f y) := by
  have hpow : Continuous (fun z : ℍ => z.im ^ σ) :=
    UpperHalfPlane.continuous_im.rpow_const (fun z => Or.inl z.im_ne_zero)
  have htrace : Continuous (fun z : ℍ => ∑ q : SL(2, ℤ) ⧸ H,
      ‖petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z‖) :=
    continuous_finsetSum _ (fun q _ => (petersson_continuous k
      (ModularFormClass.continuous (cuspCosetFamily hH f q))
      (ModularFormClass.continuous (cuspCosetFamily hH f q))).norm)
  rw [hyperbolic_unitStrip_lintegral _ (hpow.measurable.ennreal_ofReal.mul htrace.measurable.ennreal_ofReal)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have he (x : ℝ) : ENNReal.ofReal (y ^ (-2 : ℤ)) *
      (ENNReal.ofReal ((UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I)).im ^ σ) *
        ENNReal.ofReal (∑ q : SL(2, ℤ) ⧸ H,
          ‖petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q)
            (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖)) =
      ENNReal.ofReal (y ^ (σ + (k : ℝ) - 2)) * ENNReal.ofReal (∑ q : SL(2, ℤ) ⧸ H,
        ‖cuspCosetFamily hH f q (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => norm_nonneg _), Finset.mul_sum, Finset.mul_sum]
    simp_rw [petersson_mellin_density k _ σ x y hy]
    rw [← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun q _ => sq_nonneg _)]
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_cuspTrace_horizontal hH f hy,
    ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _)]

end
end Dubon2026
