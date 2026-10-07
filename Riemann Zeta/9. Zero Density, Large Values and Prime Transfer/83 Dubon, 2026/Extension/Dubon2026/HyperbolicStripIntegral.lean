import Dubon2026.ProjectiveTranslationStrip

/-! # The actual hyperbolic unit-strip measure in Cartesian coordinates -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory Measure Set Complex
open scoped ENNReal

noncomputable section

/-- Mathlib's total upper-half-plane retraction is measurable, including its constant lower-half-plane branch. -/
theorem measurable_upperHalfPlane_ofComplex : Measurable UpperHalfPlane.ofComplex := by
  apply UpperHalfPlane.measurableEmbedding_coe.measurable_comp_iff.mp
  have he : UpperHalfPlane.coe ∘ UpperHalfPlane.ofComplex =
      (fun w : ℂ => if 0 < w.im then w else (UpperHalfPlane.ofComplex 0 : ℂ)) := by
    funext w
    by_cases hw : 0 < w.im
    · simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw, hw]
    · simp only [Function.comp_apply, if_neg hw]
      exact congrArg UpperHalfPlane.coe
        (UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos (le_of_not_gt hw) (by simp))
  rw [he]
  exact Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im)
    measurable_id measurable_const

/-- The actual image of the hyperbolic unit strip is the Cartesian rectangle above the real axis. -/
theorem upperHalfPlaneUnitStrip_image :
    UpperHalfPlane.coe '' upperHalfPlaneUnitStrip =
      Complex.measurableEquivRealProd ⁻¹' (Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz, z.im_pos⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨w, hy⟩, hx, rfl⟩

/-- The literal hyperbolic unit-strip integral has the exact y⁻² Cartesian density. -/
theorem hyperbolic_unitStrip_lintegral (F : ℍ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in upperHalfPlaneUnitStrip, F z) =
      ∫⁻ y : ℝ in Ioi 0, ∫⁻ x : ℝ in Ico 0 1,
        ENNReal.ofReal (y ^ (-2 : ℤ)) *
          F (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I)) := by
  let G : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (w.im ^ (-2 : ℤ)) *
    F (UpperHalfPlane.ofComplex w)
  have hz : Measurable (fun w : ℂ => w.im ^ (-2 : ℤ)) := by fun_prop
  have hG : Measurable G :=
    hz.ennreal_ofReal.mul (hF.comp measurable_upperHalfPlane_ofComplex)
  have hd : Measurable (fun z : ℍ => ENNReal.ofReal (z.im ^ (-2 : ℤ))) :=
    (UpperHalfPlane.continuous_im.zpow₀ (-2)
      (fun z => Or.inl z.im_ne_zero)).measurable.ennreal_ofReal
  rw [hyperbolicVolume_eq_withDensity,
    setLIntegral_withDensity_eq_setLIntegral_mul _ hd hF measurableSet_upperHalfPlaneUnitStrip]
  have hc : MeasurePreserving UpperHalfPlane.coe
      (volume.comap UpperHalfPlane.coe) (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurableEmbedding_coe.measurable,
      UpperHalfPlane.measurableEmbedding_coe.map_comap volume⟩
  have he : (fun z : ℍ =>
      (fun z : ℍ => ENNReal.ofReal (z.im ^ (-2 : ℤ))) z * F z) =
      (fun z : ℍ => G z) := by
    funext z
    simp [G, UpperHalfPlane.ofComplex_apply]
  change (∫⁻ z in upperHalfPlaneUnitStrip,
    (fun z : ℍ => ENNReal.ofReal (z.im ^ (-2 : ℤ))) z * F z
      ∂volume.comap UpperHalfPlane.coe) = _
  rw [he, hc.setLIntegral_comp_emb UpperHalfPlane.measurableEmbedding_coe G]
  rw [Measure.restrict_restrict
    (UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr
      measurableSet_upperHalfPlaneUnitStrip), inter_eq_left.mpr (image_subset_range _ _),
    upperHalfPlaneUnitStrip_image]
  have hp := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => G (Complex.measurableEquivRealProd.symm p))
    (Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ))
  simp only [MeasurableEquiv.symm_apply_apply] at hp
  rw [hp, volume_eq_prod ℝ ℝ]
  simpa only [G, Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re,
    mul_one, mul_zero, zero_add, add_zero] using
    setLIntegral_prod_symm (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (s := Ico (0 : ℝ) 1) (t := Ioi (0 : ℝ))
      (fun p : ℝ × ℝ => G (Complex.measurableEquivRealProd.symm p))
      (hG.comp Complex.measurableEquivRealProd.symm.measurable).aemeasurable

end
end Dubon2026
