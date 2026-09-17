import Tao2026.FourierDecay
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# The periodic plane and Mathlib's two-dimensional torus

This module descends a continuous `ℤ²`-periodic function on `ℝ²` to
Mathlib's `UnitAddTorus (Fin 2)`, identifies the two conventions for Fourier
characters, and applies Mathlib's Fourier reconstruction theorem.  Thus the
coefficient envelope proved in `FourierDecay` yields uniform convergence of
the source's square partial sums to the original weight.

The remaining source-specific analytic obligation is to derive the cubic
coefficient envelope from the `C³` norm by integration by parts.
-/

open Complex Finset Filter
open scoped BigOperators ComplexConjugate Topology

namespace Tao2026

noncomputable section

/-- The coordinatewise quotient map `ℝ² → (ℝ/ℤ)²`. -/
def realPairToUnitTorus (x : ℝ × ℝ) : UnitAddTorus (Fin 2) :=
  ![(x.1 : UnitAddCircle), (x.2 : UnitAddCircle)]

theorem isOpenQuotientMap_realPairToUnitTorus :
    IsOpenQuotientMap realPairToUnitTorus := by
  let q : ℝ × ℝ → UnitAddCircle × UnitAddCircle :=
    Prod.map (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
  have hq : IsOpenQuotientMap q :=
    QuotientAddGroup.isOpenQuotientMap_mk.prodMap
      QuotientAddGroup.isOpenQuotientMap_mk
  have he : IsOpenQuotientMap
      ((Homeomorph.finTwoArrow (X := UnitAddCircle)).symm :
        UnitAddCircle × UnitAddCircle → UnitAddTorus (Fin 2)) :=
    (Homeomorph.finTwoArrow (X := UnitAddCircle)).symm.isOpenQuotientMap
  convert he.comp hq using 1

theorem periodic_second_of_isZ2Periodic
    {W : ℝ × ℝ → ℂ} (hW : IsZ2Periodic W) (x : ℝ) :
    Function.Periodic (fun y => W (x, y)) 1 := by
  intro y
  simpa using hW x y 0 1

/-- Descend the second coordinate of a `ℤ²`-periodic function. -/
def torusLiftSecond (W : ℝ × ℝ → ℂ) (hW : IsZ2Periodic W)
    (x : ℝ) (y : UnitAddCircle) : ℂ :=
  (periodic_second_of_isZ2Periodic hW x).lift y

theorem periodic_first_torusLiftSecond
    {W : ℝ × ℝ → ℂ} (hW : IsZ2Periodic W) (y : UnitAddCircle) :
    Function.Periodic (fun x => torusLiftSecond W hW x y) 1 := by
  intro x
  induction y using QuotientAddGroup.induction_on with
  | _ y =>
      simp only [torusLiftSecond, Function.Periodic.lift_coe]
      simpa using hW x y 1 0

/-- Descend both coordinates of a `ℤ²`-periodic function to the unit torus. -/
def torusLift (W : ℝ × ℝ → ℂ) (hW : IsZ2Periodic W)
    (z : UnitAddTorus (Fin 2)) : ℂ :=
  (periodic_first_torusLiftSecond hW (z 1)).lift (z 0)

@[simp]
theorem torusLift_realPairToUnitTorus
    (W : ℝ × ℝ → ℂ) (hW : IsZ2Periodic W) (x : ℝ × ℝ) :
    torusLift W hW (realPairToUnitTorus x) = W x := by
  simp [torusLift, realPairToUnitTorus, torusLiftSecond]

theorem continuous_torusLift
    {W : ℝ × ℝ → ℂ} (hWcont : Continuous W) (hW : IsZ2Periodic W) :
    Continuous (torusLift W hW) := by
  rw [← isOpenQuotientMap_realPairToUnitTorus.continuous_comp_iff]
  simpa only [Function.comp_def, torusLift_realPairToUnitTorus] using hWcont

/-- The continuous torus function induced by a continuous periodic weight. -/
def torusContinuousMap (W : ℝ × ℝ → ℂ) (hW : IsZ2Periodic W)
    (hWcont : Continuous W) : C(UnitAddTorus (Fin 2), ℂ) where
  toFun := torusLift W hW
  continuous_toFun := continuous_torusLift hWcont hW

/-- Translate the source's ordered-pair frequencies to Mathlib's finite
function convention. -/
def pairFrequency (q : ℤ × ℤ) : Fin 2 → ℤ := ![q.1, q.2]

def pairFrequencyEquiv : (ℤ × ℤ) ≃ (Fin 2 → ℤ) :=
  (finTwoArrowEquiv ℤ).symm

@[simp]
theorem pairFrequencyEquiv_apply (q : ℤ × ℤ) :
    pairFrequencyEquiv q = pairFrequency q := rfl

@[simp]
theorem mFourier_pairFrequency_realPairToUnitTorus
    (q : ℤ × ℤ) (x : ℝ × ℝ) :
    UnitAddTorus.mFourier (pairFrequency q) (realPairToUnitTorus x) =
      fourierMode2D q x := by
  change (∏ i : Fin 2, fourier (pairFrequency q i) (realPairToUnitTorus x i)) = _
  rw [Fin.prod_univ_two]
  simp only [pairFrequency, realPairToUnitTorus, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, fourier_coe_apply]
  unfold fourierMode2D standardAdditiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Fourier coefficients of a periodic function, indexed in the source's
ordered-pair convention. -/
def taoFourierCoeff (W : ℝ × ℝ → ℂ) (hW : IsZ2Periodic W)
    (hWcont : Continuous W) (q : ℤ × ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff (torusContinuousMap W hW hWcont) (pairFrequency q)

/-- The torus coefficient is the source's integral on the unit fundamental
square, written with `Fin 2` coordinates so it can feed Mathlib's
multivariate integration-by-parts infrastructure. -/
theorem taoFourierCoeff_eq_integral_fin2
    (W : ℝ × ℝ → ℂ) (hW : IsZ2Periodic W) (hWcont : Continuous W)
    (q : ℤ × ℤ) :
    taoFourierCoeff W hW hWcont q =
      ∫ (x : Fin 2 → ℝ) in {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
        conj (fourierMode2D q (x 0, x 1)) * W (x 0, x 1) := by
  rw [taoFourierCoeff, UnitAddTorus.mFourierCoeff_eq_integral
    (torusContinuousMap W hW hWcont) (pairFrequency q) (fun _ => 0)]
  simp only [zero_add]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  have hx : (fun i => (x i : UnitAddCircle)) =
      realPairToUnitTorus (x 0, x 1) := by
    funext i
    fin_cases i <;> rfl
  rw [hx, UnitAddTorus.mFourier_neg,
    mFourier_pairFrequency_realPairToUnitTorus]
  change conj (fourierMode2D q (x 0, x 1)) *
      torusLift W hW (realPairToUnitTorus (x 0, x 1)) = _
  rw [torusLift_realPairToUnitTorus]

theorem summable_mFourierCoeff_of_taoFourierDecay
    {W : ℝ × ℝ → ℂ} (hW : IsZ2Periodic W) (hWcont : Continuous W)
    {C : ℝ}
    (hc : ∀ q, ‖taoFourierCoeff W hW hWcont q‖ ≤
      C * fourierDecayWeight q) :
    Summable (UnitAddTorus.mFourierCoeff (torusContinuousMap W hW hWcont)) := by
  rw [← pairFrequencyEquiv.summable_iff]
  simpa only [Function.comp_def, pairFrequencyEquiv_apply, taoFourierCoeff] using
    summable_of_fourierDecay (taoFourierCoeff W hW hWcont) hc

/-- Once the source's coefficient decay is established, the resulting
Fourier series sums pointwise to the original periodic function. -/
theorem hasSum_taoFourierSeries_of_decay
    {W : ℝ × ℝ → ℂ} (hW : IsZ2Periodic W) (hWcont : Continuous W)
    {C : ℝ}
    (hc : ∀ q, ‖taoFourierCoeff W hW hWcont q‖ ≤
      C * fourierDecayWeight q) (x : ℝ × ℝ) :
    HasSum (fun q => taoFourierCoeff W hW hWcont q * fourierMode2D q x) (W x) := by
  have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (summable_mFourierCoeff_of_taoFourierDecay hW hWcont hc)
    (realPairToUnitTorus x)
  have hreindexed := pairFrequencyEquiv.hasSum_iff.mpr hsum
  simpa only [Function.comp_def, pairFrequencyEquiv_apply, taoFourierCoeff,
    mFourier_pairFrequency_realPairToUnitTorus, smul_eq_mul,
    torusContinuousMap, torusLift_realPairToUnitTorus] using hreindexed

/-- The square partial sums used in the source converge uniformly to the
original weight, not merely to an unspecified coefficient-series limit. -/
theorem tendstoUniformly_taoFourierPolynomial_of_decay
    {W : ℝ × ℝ → ℂ} (hW : IsZ2Periodic W) (hWcont : Continuous W)
    {C : ℝ}
    (hc : ∀ q, ‖taoFourierCoeff W hW hWcont q‖ ≤
      C * fourierDecayWeight q) :
    TendstoUniformly
      (fun R : ℕ => finiteFourierPolynomial (fourierFrequencyBox R)
        (taoFourierCoeff W hW hWcont)) W atTop := by
  have hnorm : Summable (fun q => ‖taoFourierCoeff W hW hWcont q‖) :=
    summable_norm_of_fourierDecay (taoFourierCoeff W hW hWcont) hc
  have hlim := tendstoUniformly_finiteFourierPolynomial
    (taoFourierCoeff W hW hWcont) hnorm
  convert hlim using 1
  funext x
  exact (hasSum_taoFourierSeries_of_decay hW hWcont hc x).tsum_eq.symm

/-- The pointwise error of a square Fourier truncation is bounded by the
exact outer-box `ℓ¹` coefficient tail. -/
theorem norm_taoFourierPolynomial_sub_le_coefficientTail
    {W : ℝ × ℝ → ℂ} (hW : IsZ2Periodic W) (hWcont : Continuous W)
    {C : ℝ}
    (hc : ∀ q, ‖taoFourierCoeff W hW hWcont q‖ ≤
      C * fourierDecayWeight q) (R : ℕ) (x : ℝ × ℝ) :
    ‖W x - finiteFourierPolynomial (fourierFrequencyBox R)
        (taoFourierCoeff W hW hWcont) x‖ ≤
      ∑' q : {q // q ∉ fourierFrequencyBox R},
        ‖taoFourierCoeff W hW hWcont q‖ := by
  let c := taoFourierCoeff W hW hWcont
  let f : ℤ × ℤ → ℂ := fun q => c q * fourierMode2D q x
  have hcNorm : Summable (fun q => ‖c q‖) :=
    summable_norm_of_fourierDecay c hc
  have hfNorm : Summable (fun q => ‖f q‖) := by
    simpa only [f, norm_mul, norm_fourierMode2D, mul_one] using hcNorm
  have hf : Summable f := hfNorm.of_norm
  have hseries : HasSum f (W x) := by
    simpa only [f, c] using hasSum_taoFourierSeries_of_decay hW hWcont hc x
  have hdecomp := hf.sum_add_tsum_subtype_compl (fourierFrequencyBox R)
  have hEq : W x = finiteFourierPolynomial (fourierFrequencyBox R) c x +
      ∑' q : {q // q ∉ fourierFrequencyBox R}, f q := by
    rw [← hseries.tsum_eq]
    simpa only [finiteFourierPolynomial, c] using hdecomp.symm
  calc
    ‖W x - finiteFourierPolynomial (fourierFrequencyBox R) c x‖ =
        ‖∑' q : {q // q ∉ fourierFrequencyBox R}, f q‖ := by rw [hEq]; ring_nf
    _ ≤ ∑' q : {q // q ∉ fourierFrequencyBox R}, ‖f q‖ :=
      norm_tsum_le_tsum_norm (hfNorm.subtype _)
    _ = ∑' q : {q // q ∉ fourierFrequencyBox R}, ‖c q‖ := by
      apply tsum_congr
      intro q
      simp only [f, norm_mul, norm_fourierMode2D, mul_one]

end

end Tao2026
