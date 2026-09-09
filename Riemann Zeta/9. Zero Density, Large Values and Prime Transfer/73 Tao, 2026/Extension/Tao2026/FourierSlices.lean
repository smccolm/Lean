import Tao2026.FourierIntegrationByParts

/-!
# Slicing two-dimensional Fourier coefficients

This module factors the actual torus coefficient used for Tao's periodic
weight into two successive one-dimensional circle coefficients.  The proof
uses the volume-preserving equivalence between a `Fin 2` product and a binary
product, followed by Fubini's theorem.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Tao2026

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The source coefficient factored as two successive circle Fourier
coefficients. -/
def iteratedTaoFourierCoeff (W : ℝ × ℝ → ℂ) (hW : IsZ2Periodic W)
    (q : ℤ × ℤ) : ℂ :=
  fourierCoeff
    (fun y : UnitAddCircle =>
      fourierCoeff (fun x : UnitAddCircle => torusLift W hW ![x, y]) q.1)
    q.2

/-- The symmetric iterated coefficient, integrating the second circle
coordinate first. -/
def iteratedTaoFourierCoeffSecond (W : ℝ × ℝ → ℂ) (hW : IsZ2Periodic W)
    (q : ℤ × ℤ) : ℂ :=
  fourierCoeff
    (fun x : UnitAddCircle =>
      fourierCoeff (fun y : UnitAddCircle => torusLift W hW ![x, y]) q.2)
    q.1

theorem taoFourierCoeff_eq_iterated
    (W : ℝ × ℝ → ℂ) (hW : IsZ2Periodic W) (hWcont : Continuous W)
    (q : ℤ × ℤ) :
    taoFourierCoeff W hW hWcont q = iteratedTaoFourierCoeff W hW q := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)
  let F : UnitAddTorus (Fin 2) → ℂ := fun z =>
    UnitAddTorus.mFourier (-pairFrequency q) z • torusLift W hW z
  let G : UnitAddCircle × UnitAddCircle → ℂ := fun z => F ![z.1, z.2]
  have hchange := (MeasureTheory.volume_preserving_piFinTwo
    (fun _ : Fin 2 => UnitAddCircle)).integral_comp' G
  have hGcont : Continuous G := by
    have hz : Continuous (fun z : UnitAddCircle × UnitAddCircle => ![z.1, z.2]) := by
      fun_prop
    exact ((UnitAddTorus.mFourier (-pairFrequency q)).continuous.comp hz).smul
      ((continuous_torusLift hWcont hW).comp hz)
  have hGint : Integrable G := by
    simpa only [integrableOn_univ] using
      hGcont.continuousOn.integrableOn_compact isCompact_univ
  rw [taoFourierCoeff, UnitAddTorus.mFourierCoeff]
  change (∫ z : UnitAddTorus (Fin 2), F z) = _
  calc
    (∫ z : UnitAddTorus (Fin 2), F z) =
        ∫ z : UnitAddCircle × UnitAddCircle, G z := by
      simpa [G, e] using hchange
    _ = ∫ y : UnitAddCircle, ∫ x : UnitAddCircle, G (x, y) :=
      MeasureTheory.integral_prod_symm G hGint
    _ = iteratedTaoFourierCoeff W hW q := by
      simp only [iteratedTaoFourierCoeff, fourierCoeff]
      congr 1
      funext y
      rw [← MeasureTheory.integral_smul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      dsimp [G, F]
      change (∏ i : Fin 2, fourier (-(pairFrequency q) i) (![x, y] i)) •
        torusLift W hW ![x, y] = _
      rw [Fin.prod_univ_two]
      simp [pairFrequency]
      ring

/-- Symmetric Fubini factorization, with the second coordinate integrated
first. -/
theorem taoFourierCoeff_eq_iterated_second
    (W : ℝ × ℝ → ℂ) (hW : IsZ2Periodic W) (hWcont : Continuous W)
    (q : ℤ × ℤ) :
    taoFourierCoeff W hW hWcont q = iteratedTaoFourierCoeffSecond W hW q := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)
  let F : UnitAddTorus (Fin 2) → ℂ := fun z =>
    UnitAddTorus.mFourier (-pairFrequency q) z • torusLift W hW z
  let G : UnitAddCircle × UnitAddCircle → ℂ := fun z => F ![z.1, z.2]
  have hchange := (MeasureTheory.volume_preserving_piFinTwo
    (fun _ : Fin 2 => UnitAddCircle)).integral_comp' G
  have hGcont : Continuous G := by
    have hz : Continuous (fun z : UnitAddCircle × UnitAddCircle => ![z.1, z.2]) := by
      fun_prop
    exact ((UnitAddTorus.mFourier (-pairFrequency q)).continuous.comp hz).smul
      ((continuous_torusLift hWcont hW).comp hz)
  have hGint : Integrable G := by
    simpa only [integrableOn_univ] using
      hGcont.continuousOn.integrableOn_compact isCompact_univ
  rw [taoFourierCoeff, UnitAddTorus.mFourierCoeff]
  change (∫ z : UnitAddTorus (Fin 2), F z) = _
  calc
    (∫ z : UnitAddTorus (Fin 2), F z) =
        ∫ z : UnitAddCircle × UnitAddCircle, G z := by
      simpa [G, e] using hchange
    _ = ∫ x : UnitAddCircle, ∫ y : UnitAddCircle, G (x, y) :=
      MeasureTheory.integral_prod G hGint
    _ = iteratedTaoFourierCoeffSecond W hW q := by
      simp only [iteratedTaoFourierCoeffSecond, fourierCoeff]
      congr 1
      funext x
      rw [← MeasureTheory.integral_smul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      dsimp [G, F]
      change (∏ i : Fin 2, fourier (-(pairFrequency q) i) (![x, y] i)) •
        torusLift W hW ![x, y] = _
      rw [Fin.prod_univ_two]
      simp [pairFrequency]
      ring

/-- A unit-circle Fourier coefficient is bounded by any pointwise norm bound
for the function. -/
theorem norm_fourierCoeff_le_of_norm_le
    (f : UnitAddCircle → ℂ) {B : ℝ} (hbound : ∀ x, ‖f x‖ ≤ B) (n : ℤ) :
    ‖fourierCoeff f n‖ ≤ B := by
  unfold fourierCoeff
  calc
    ‖∫ x : UnitAddCircle, fourier (-n) x • f x‖ ≤
        B * (volume : Measure UnitAddCircle).real Set.univ := by
      apply MeasureTheory.norm_integral_le_of_norm_le_const
      filter_upwards with x
      rw [norm_smul]
      have hfourier : ‖fourier (-n) x‖ = 1 := by
        exact Circle.norm_coe _
      rw [hfourier, one_mul]
      exact hbound x
    _ = B := by simp

/-- A torus slice represented by a real second coordinate has the same
one-dimensional coefficient as the corresponding plane slice on `[0,1]`. -/
theorem fourierCoeff_torusSlice_first_eq_fourierCoeffOn
    (W : ℝ × ℝ → ℂ) (hW : IsZ2Periodic W) (y : ℝ) (n : ℤ) :
    fourierCoeff
        (fun x : UnitAddCircle => torusLift W hW ![x, (y : UnitAddCircle)]) n =
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (fun x => W (x, y)) n := by
  have hfun :
      (fun x : UnitAddCircle => torusLift W hW ![x, (y : UnitAddCircle)]) =
        AddCircle.liftIoc 1 0 (fun x => W (x, y)) := by
    funext z
    obtain ⟨x, hx, rfl⟩ := AddCircle.eq_coe_Ioc z
    rw [AddCircle.liftIoc_coe_apply (by simpa using hx)]
    change torusLift W hW (realPairToUnitTorus (x, y)) = W (x, y)
    exact torusLift_realPairToUnitTorus W hW (x, y)
  rw [hfun]
  simpa using fourierCoeff_liftIoc_eq (T := (1 : ℝ))
    (a := 0) (fun x => W (x, y)) n

/-- The symmetric coefficient identity for a real first-coordinate
representative. -/
theorem fourierCoeff_torusSlice_second_eq_fourierCoeffOn
    (W : ℝ × ℝ → ℂ) (hW : IsZ2Periodic W) (x : ℝ) (n : ℤ) :
    fourierCoeff
        (fun y : UnitAddCircle => torusLift W hW ![(x : UnitAddCircle), y]) n =
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (fun y => W (x, y)) n := by
  have hfun :
      (fun y : UnitAddCircle => torusLift W hW ![(x : UnitAddCircle), y]) =
        AddCircle.liftIoc 1 0 (fun y => W (x, y)) := by
    funext z
    obtain ⟨y, hy, rfl⟩ := AddCircle.eq_coe_Ioc z
    rw [AddCircle.liftIoc_coe_apply (by simpa using hy)]
    change torusLift W hW (realPairToUnitTorus (x, y)) = W (x, y)
    exact torusLift_realPairToUnitTorus W hW (x, y)
  rw [hfun]
  simpa using fourierCoeff_liftIoc_eq (T := (1 : ℝ))
    (a := 0) (fun y => W (x, y)) n

/-- Cubic decay of the actual two-dimensional coefficient in the first
frequency, under source-shaped periodic slice derivatives.  This is the
Fubini/slice closure of the one-dimensional integration-by-parts estimate. -/
theorem norm_taoFourierCoeff_le_first_thirdDerivative
    (W₀ W₁ W₂ W₃ : ℝ × ℝ → ℂ)
    (hper₀ : IsZ2Periodic W₀) (hper₁ : IsZ2Periodic W₁)
    (hper₂ : IsZ2Periodic W₂)
    (hcont₀ : Continuous W₀) (hcont₁ : Continuous W₁)
    (hcont₂ : Continuous W₂) (hcont₃ : Continuous W₃)
    (hderiv₀ : ∀ x y, HasDerivAt (fun t => W₀ (t, y)) (W₁ (x, y)) x)
    (hderiv₁ : ∀ x y, HasDerivAt (fun t => W₁ (t, y)) (W₂ (x, y)) x)
    (hderiv₂ : ∀ x y, HasDerivAt (fun t => W₂ (t, y)) (W₃ (x, y)) x)
    {B : ℝ}
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ‖W₃ (x, y)‖ ≤ B)
    (q : ℤ × ℤ) (hq : q.1 ≠ 0) :
    ‖taoFourierCoeff W₀ hper₀ hcont₀ q‖ ≤
      (2 * Real.pi * |(q.1 : ℝ)|)⁻¹ ^ 3 * B := by
  rw [taoFourierCoeff_eq_iterated W₀ hper₀ hcont₀ q]
  apply norm_fourierCoeff_le_of_norm_le
  intro y
  obtain ⟨yr, hyr, rfl⟩ := AddCircle.eq_coe_Ioc y
  rw [fourierCoeff_torusSlice_first_eq_fourierCoeffOn]
  apply norm_fourierCoeffOn_zero_one_le_thirdDeriv_explicit hq
  · intro x
    exact hderiv₀ x yr
  · intro x
    exact hderiv₁ x yr
  · intro x
    exact hderiv₂ x yr
  · simpa using (hper₀ 0 yr 1 0).symm
  · simpa using (hper₁ 0 yr 1 0).symm
  · simpa using (hper₂ 0 yr 1 0).symm
  · exact (hcont₁.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
  · exact (hcont₂.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
  · exact (hcont₃.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
  · intro x hx
    exact hbound x hx yr ⟨hyr.1.le, hyr.2⟩

/-- Symmetric cubic decay in the second frequency. -/
theorem norm_taoFourierCoeff_le_second_thirdDerivative
    (W₀ W₁ W₂ W₃ : ℝ × ℝ → ℂ)
    (hper₀ : IsZ2Periodic W₀) (hper₁ : IsZ2Periodic W₁)
    (hper₂ : IsZ2Periodic W₂)
    (hcont₀ : Continuous W₀) (hcont₁ : Continuous W₁)
    (hcont₂ : Continuous W₂) (hcont₃ : Continuous W₃)
    (hderiv₀ : ∀ x y, HasDerivAt (fun t => W₀ (x, t)) (W₁ (x, y)) y)
    (hderiv₁ : ∀ x y, HasDerivAt (fun t => W₁ (x, t)) (W₂ (x, y)) y)
    (hderiv₂ : ∀ x y, HasDerivAt (fun t => W₂ (x, t)) (W₃ (x, y)) y)
    {B : ℝ}
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ‖W₃ (x, y)‖ ≤ B)
    (q : ℤ × ℤ) (hq : q.2 ≠ 0) :
    ‖taoFourierCoeff W₀ hper₀ hcont₀ q‖ ≤
      (2 * Real.pi * |(q.2 : ℝ)|)⁻¹ ^ 3 * B := by
  rw [taoFourierCoeff_eq_iterated_second W₀ hper₀ hcont₀ q]
  apply norm_fourierCoeff_le_of_norm_le
  intro x
  obtain ⟨xr, hxr, rfl⟩ := AddCircle.eq_coe_Ioc x
  rw [fourierCoeff_torusSlice_second_eq_fourierCoeffOn]
  apply norm_fourierCoeffOn_zero_one_le_thirdDeriv_explicit hq
  · intro y
    exact hderiv₀ xr y
  · intro y
    exact hderiv₁ xr y
  · intro y
    exact hderiv₂ xr y
  · simpa using (hper₀ xr 0 0 1).symm
  · simpa using (hper₁ xr 0 0 1).symm
  · simpa using (hper₂ xr 0 0 1).symm
  · exact (hcont₁.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  · exact (hcont₂.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  · exact (hcont₃.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  · intro y hy
    exact hbound xr ⟨hxr.1.le, hxr.2⟩ y hy

end

end Tao2026
