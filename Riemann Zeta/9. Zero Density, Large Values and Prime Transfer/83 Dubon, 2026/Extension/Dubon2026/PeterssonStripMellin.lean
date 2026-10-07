import Dubon2026.HyperbolicStripIntegral
import Dubon2026.CuspMellinEnergy

/-! # The exact Mellin density of the genuine Petersson strip integral -/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup MeasureTheory Set
open scoped MatrixGroups CongruenceSubgroup ENNReal

noncomputable section

/-- The norm of the true diagonal Petersson density is the literal squared cusp norm times y^k. -/
theorem norm_petersson_self (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    ‖petersson k f f z‖ = ‖f z‖ ^ 2 * z.im ^ k := by
  simp [petersson, norm_zpow, abs_of_pos z.im_pos, pow_two]

/-- The actual cusp function is continuous along every positive horizontal line. -/
theorem continuous_cusp_horizontal_ofComplex {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => f (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))) := by
  have he : (fun x : ℝ => f (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))) =
      (fun x : ℝ => f ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩) := by
    funext x
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
  rw [he]
  exact continuous_cusp_horizontal f hy

/-- The nonnegative integral over the half-open horizontal period equals the actual interval energy. -/
theorem lintegral_cusp_horizontal_energy {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) {y : ℝ} (hy : 0 < y) :
    (∫⁻ x : ℝ in Ico 0 1,
      ENNReal.ofReal (‖f (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2)) =
        ENNReal.ofReal (cuspHorizontalEnergy f y) := by
  have hc := (continuous_cusp_horizontal_ofComplex f hy).norm.pow 2
  have hi := (intervalIntegrable_iff_integrableOn_Ico_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (hc.intervalIntegrable (μ := (volume : Measure ℝ)) (a := 0) (b := 1))
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x => sq_nonneg _)),
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rfl

/-- The exact y⁻² hyperbolic density combines with the Eisenstein and modular weights. -/
theorem petersson_mellin_density (k : ℤ) (f : ℍ → ℂ) (σ x y : ℝ) (hy : 0 < y) :
    ENNReal.ofReal (y ^ (-2 : ℤ)) *
      (ENNReal.ofReal ((UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I)).im ^ σ) *
        ENNReal.ofReal ‖petersson k f f (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖) =
      ENNReal.ofReal (y ^ (σ + (k : ℝ) - 2)) *
        ENNReal.ofReal (‖f (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2) := by
  have him : (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I)).im = y := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
    simp
  rw [norm_petersson_self, him, ← ENNReal.ofReal_mul (Real.rpow_nonneg hy.le σ),
    ← ENNReal.ofReal_mul (zpow_pos hy _).le, ← ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _)]
  congr 1
  have hp : y ^ (-2 : ℤ) * y ^ σ * y ^ k = y ^ (σ + (k : ℝ) - 2) := by
    rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_add hy, ← Real.rpow_add hy]
    congr 1
    push_cast
    ring
  calc
    _ = (y ^ (-2 : ℤ) * y ^ σ * y ^ k) *
        ‖f (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2 := by ring
    _ = _ := by rw [hp]

/-- The actual Petersson strip integral equals the nonnegative Mellin integral of horizontal Fourier energy. -/
theorem petersson_unitStrip_mellin {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (σ : ℝ) :
    (∫⁻ z in upperHalfPlaneUnitStrip,
      ENNReal.ofReal (z.im ^ σ) * ENNReal.ofReal ‖petersson k f f z‖) =
      ∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal (y ^ (σ + (k : ℝ) - 2) * cuspHorizontalEnergy f y) := by
  have hpow : Continuous (fun z : ℍ => z.im ^ σ) :=
    UpperHalfPlane.continuous_im.rpow_const (fun z => Or.inl z.im_ne_zero)
  rw [hyperbolic_unitStrip_lintegral _
    (hpow.measurable.ennreal_ofReal.mul
      (petersson_continuous k (ModularFormClass.continuous f)
        (ModularFormClass.continuous f)).norm.measurable.ennreal_ofReal)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro y hy
  simp_rw [petersson_mellin_density k f σ _ y hy]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_cusp_horizontal_energy f hy, ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _)]

end
end Dubon2026
