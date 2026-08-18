import RiemannZeta.GuthMaynard.HughesYoungEquation96DFIBridge
import RiemannZeta.GuthMaynard.HughesYoungCentralBounds
import RiemannZeta.GuthMaynard.HughesYoungFarShift

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

set_option maxHeartbeats 4000000

namespace RiemannZeta.GuthMaynard

/-!
# The complete Hughes--Young equation-(84) series on `Re w = 1`

This file performs the first complete-series consumer step after the DFI
contour shift.  Both the positive shift and the modulus are summed before
the four bilinear kernel coefficients are estimated.  Thus the arithmetic
objects below are the absolutely convergent equation-(96) series, not a
fixed-shift proxy.
-/

private theorem integrable_exp_sub_mul_sq_mul_add_abs_pow
    (A : ℝ) {B C : ℝ} (hB : 0 < B) (j : ℕ) :
    Integrable (fun u : ℝ =>
      Real.exp (A - B * u ^ 2) * (C + |u|) ^ j) := by
  have hterm : ∀ i ∈ Finset.range (j + 1), Integrable (fun u : ℝ =>
      (Real.exp A * (j.choose i : ℝ) * C ^ i) *
        (|u| ^ (j - i) * Real.exp (-B * u ^ 2))) := by
    intro i _hi
    exact (integrable_abs_pow_mul_exp_neg_mul_sq hB (j - i)).const_mul
      (Real.exp A * (j.choose i : ℝ) * C ^ i)
  have hsum : Integrable (fun u : ℝ =>
      ∑ i ∈ Finset.range (j + 1),
        (Real.exp A * (j.choose i : ℝ) * C ^ i) *
          (|u| ^ (j - i) * Real.exp (-B * u ^ 2))) :=
    integrable_finsetSum (Finset.range (j + 1)) hterm
  apply hsum.congr
  filter_upwards with u
  rw [sub_eq_add_neg, Real.exp_add, add_pow]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem integrable_of_continuous_of_norm_le_gaussian_tail
    (f : ℝ → ℂ) (hf : Continuous f) {L C A B D : ℝ} {j : ℕ}
    (hL : 0 < L) (hB : 0 < B)
    (htail : ∀ u : ℝ, L ≤ |u| →
      ‖f u‖ ≤ C * Real.exp (A - B * u ^ 2) * (D + |u|) ^ j) :
    Integrable f := by
  let g : ℝ → ℝ := fun u =>
    C * (Real.exp (A - B * u ^ 2) * (D + |u|) ^ j)
  have hg : Integrable g := by
    dsimp [g]
    simpa only [mul_assoc] using
      (integrable_exp_sub_mul_sq_mul_add_abs_pow A hB j).const_mul C
  have hPos : IntegrableOn f (Set.Ioi L) := by
    apply hg.integrableOn.mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change L < u at hu
    have hu0 : 0 < u := hL.trans hu
    simpa only [g, abs_of_pos hu0, mul_assoc] using htail u (by
      rw [abs_of_pos hu0]
      exact hu.le)
  have hNeg : IntegrableOn f (Set.Iio (-L)) := by
    apply hg.integrableOn.mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
    change u < -L at hu
    have hu0 : u < 0 := hu.trans_le (neg_nonpos.mpr hL.le)
    simpa only [g, mul_assoc] using htail u (by
      rw [abs_of_neg hu0]
      linarith)
  have hMid : IntegrableOn f (Set.Icc (-L) L) :=
    hf.continuousOn.integrableOn_Icc
  have hLeft : IntegrableOn f (Set.Iic L) := by
    have hNegClosed : IntegrableOn f (Set.Iic (-L)) :=
      (integrableOn_Iic_iff_integrableOn_Iio).mpr hNeg
    have hUnion := MeasureTheory.integrableOn_union.2 ⟨hNegClosed, hMid⟩
    have hSet : Set.Iic (-L) ∪ Set.Icc (-L) L = Set.Iic L := by
      ext u
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]
      constructor
      · intro hu
        rcases hu with hu | hu <;> linarith
      · intro hu
        by_cases hu' : u ≤ -L
        · exact Or.inl hu'
        · exact Or.inr ⟨by linarith, hu⟩
    rwa [hSet] at hUnion
  rw [← MeasureTheory.integrableOn_univ]
  have hAll := MeasureTheory.integrableOn_union.2 ⟨hLeft, hPos⟩
  have hSet : Set.Iic L ∪ Set.Ioi L = Set.univ := by
    ext u
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ, iff_true]
    exact le_or_gt u L
  rwa [hSet] at hAll

/-- At `w = 1 + iu`, the entire shift factor is exactly
`r ^ (-(2+2iu))`. -/
theorem hughesYoungCentralShiftPower_sourceLine
    {r : ℕ} (hr : 0 < r) (u : ℝ) :
    hughesYoungCentralShiftPower r
        ((1 : ℂ) + (u : ℂ) * I) =
      1 / ((r : ℂ) ^ ((2 : ℂ) + (2 * u : ℂ) * I)) := by
  rw [hughesYoungCentralShiftPower_eq_cpow hr]
  rw [show -2 * ((1 : ℂ) + (u : ℂ) * I) =
      -((2 : ℂ) + (2 * u : ℂ) * I) by ring]
  rw [Complex.cpow_neg]
  simp only [one_div]

/-- The complete positive equation-(84) source-line series, with both
positive DFI variables `(q,r)` summed. -/
noncomputable def hughesYoungEquation84CompletePositiveSourceLine
    (T t : ℝ) (h k a b : ℕ) (u : ℝ) : ℂ :=
  ∑' y : ℕ+ × ℕ+,
    hughesYoungEquation84PositiveContourTerm T t h k a b
      (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)

/-- The source-line factor independent of the DFI variables `(q,r)`. -/
noncomputable def hughesYoungEquation84CompletePositiveOuter
    (T t : ℝ) (h k a b : ℕ) (u : ℝ) : ℂ :=
  (((a : ℂ) * b)⁻¹) *
    hughesYoungReducedMellinStaticComplex T t h k
      ((1 : ℂ) + (u : ℂ) * I)

private noncomputable def hughesYoungEquation84PositiveSourceArithmeticTerm
    (a b : ℕ) (i j : Bool) (u : ℝ) (y : ℕ+ × ℕ+) : ℂ :=
  (dfiEquation27ArithmeticCoefficient a b (y.2 : ℕ) (y.1 : ℕ) /
      (((y.2 : ℕ) : ℂ) ^ ((2 : ℂ) + (2 * u : ℂ) * I))) *
    (if i then hughesYoungEquation84PositiveCX b (y.2 : ℕ) (y.1 : ℕ) else 1) *
    (if j then hughesYoungEquation84PositiveCOne a (y.2 : ℕ) (y.1 : ℕ) else 1)

private theorem hughesYoungEquation84PositiveSourceTerm_eq_fourTerms
    (T t : ℝ) (h k a b : ℕ) (u : ℝ)
    (y : ℕ+ × ℕ+) :
    hughesYoungEquation84PositiveContourTerm T t h k a b
        (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I) =
      hughesYoungEquation84CompletePositiveOuter T t h k a b u *
        (hughesYoungEquation84PositiveSourceArithmeticTerm a b false false u y *
            hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84PositiveSourceArithmeticTerm a b true false u y *
            hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84PositiveSourceArithmeticTerm a b false true u y *
            hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84PositiveSourceArithmeticTerm a b true true u y *
            hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)) := by
  unfold hughesYoungEquation84PositiveContourTerm
    hughesYoungEquation84CompletePositiveOuter
    hughesYoungEquation84PositiveSourceArithmeticTerm
    hughesYoungEquation84PositiveCX hughesYoungEquation84PositiveCOne
  have hshift := hughesYoungCentralShiftPower_sourceLine
    (r := (y.2 : ℕ)) y.2.2 u
  rw [hshift]
  rw [hughesYoungEquation84RegularizedContourKernel_eq_fourTerm]
  simp only [Bool.false_eq_true, ↓reduceIte]
  ring

/-- The complete positive source-line series is absolutely summable. -/
theorem summable_hughesYoungEquation84CompletePositiveSourceLine
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation84PositiveContourTerm T t h k a b
        (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)) := by
  let P := hughesYoungEquation84CompletePositiveOuter T t h k a b u
  let K₀₀ := hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)
  let K₁₀ := hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)
  let K₀₁ := hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)
  let K₁₁ := hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)
  have h₀₀ : Summable (hughesYoungEquation84PositiveSourceArithmeticTerm
      a b false false u) := by
    simpa only [hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm false false u ha hb hab hη hη4
  have h₁₀ : Summable (hughesYoungEquation84PositiveSourceArithmeticTerm
      a b true false u) := by
    simpa only [hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm true false u ha hb hab hη hη4
  have h₀₁ : Summable (hughesYoungEquation84PositiveSourceArithmeticTerm
      a b false true u) := by
    simpa only [hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm false true u ha hb hab hη hη4
  have h₁₁ : Summable (hughesYoungEquation84PositiveSourceArithmeticTerm
      a b true true u) := by
    simpa only [hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm true true u ha hb hab hη hη4
  have hs : Summable (fun y : ℕ+ × ℕ+ =>
      P * (hughesYoungEquation84PositiveSourceArithmeticTerm a b false false u y * K₀₀ +
        hughesYoungEquation84PositiveSourceArithmeticTerm a b true false u y * K₁₀ +
        hughesYoungEquation84PositiveSourceArithmeticTerm a b false true u y * K₀₁ +
        hughesYoungEquation84PositiveSourceArithmeticTerm a b true true u y * K₁₁)) := by
    apply Summable.mul_left
    exact (((h₀₀.mul_right K₀₀).add (h₁₀.mul_right K₁₀)).add
      (h₀₁.mul_right K₀₁)).add (h₁₁.mul_right K₁₁)
  apply hs.congr
  intro y
  simpa only [P, K₀₀, K₁₀, K₀₁, K₁₁] using
    (hughesYoungEquation84PositiveSourceTerm_eq_fourTerms T t h k a b u y).symm

/-- Exact complete-series version of equation (84) on `Re w = 1`.
This is the Hughes--Young consumer of the four absolutely convergent DFI
equation-(96) moments. -/
theorem hughesYoungEquation84CompletePositiveSourceLine_eq_fourMoments
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    hughesYoungEquation84CompletePositiveSourceLine T t h k a b u =
      hughesYoungEquation84CompletePositiveOuter T t h k a b u *
        (hughesYoungEquation84CompletePositiveMomentAt a b false false u *
            hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84CompletePositiveMomentAt a b true false u *
            hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84CompletePositiveMomentAt a b false true u *
            hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84CompletePositiveMomentAt a b true true u *
            hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)) := by
  let P := hughesYoungEquation84CompletePositiveOuter T t h k a b u
  let K₀₀ := hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)
  let K₁₀ := hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)
  let K₀₁ := hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)
  let K₁₁ := hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)
  let f : Bool → Bool → (ℕ+ × ℕ+) → ℂ := fun i j y =>
    hughesYoungEquation84PositiveSourceArithmeticTerm a b i j u y
  have h₀₀ : Summable (f false false) := by
    simpa only [f, hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm false false u ha hb hab hη hη4
  have h₁₀ : Summable (f true false) := by
    simpa only [f, hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm true false u ha hb hab hη hη4
  have h₀₁ : Summable (f false true) := by
    simpa only [f, hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm false true u ha hb hab hη hη4
  have h₁₁ : Summable (f true true) := by
    simpa only [f, hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm true true u ha hb hab hη hη4
  unfold hughesYoungEquation84CompletePositiveSourceLine
  rw [show (∑' y : ℕ+ × ℕ+,
      hughesYoungEquation84PositiveContourTerm T t h k a b
        (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)) =
      ∑' y : ℕ+ × ℕ+,
        P * (f false false y * K₀₀ + f true false y * K₁₀ +
          f false true y * K₀₁ + f true true y * K₁₁) by
    apply tsum_congr
    intro y
    simpa only [P, K₀₀, K₁₀, K₀₁, K₁₁, f] using
      hughesYoungEquation84PositiveSourceTerm_eq_fourTerms T t h k a b u y]
  simp_rw [tsum_mul_left]
  rw [(((h₀₀.mul_right K₀₀).add (h₁₀.mul_right K₁₀)).add
      (h₀₁.mul_right K₀₁)).tsum_add (h₁₁.mul_right K₁₁),
    ((h₀₀.mul_right K₀₀).add (h₁₀.mul_right K₁₀)).tsum_add
      (h₀₁.mul_right K₀₁),
    (h₀₀.mul_right K₀₀).tsum_add (h₁₀.mul_right K₁₀)]
  simp only [tsum_mul_right]
  change P * ((∑' y, f false false y) * K₀₀ +
      (∑' y, f true false y) * K₁₀ +
      (∑' y, f false true y) * K₀₁ +
      (∑' y, f true true y) * K₁₁) = _
  simp only [P, K₀₀, K₁₀, K₀₁, K₁₁]
  congr 1

/-- The complete negative, coordinate-swapped equation-(84) source-line
series. -/
noncomputable def hughesYoungEquation84CompleteNegativeSourceLine
    (T t : ℝ) (h k a b : ℕ) (u : ℝ) : ℂ :=
  ∑' y : ℕ+ × ℕ+,
    hughesYoungEquation84NegativeContourTerm T t h k a b
      (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)

noncomputable def hughesYoungEquation84CompleteNegativeOuter
    (T t : ℝ) (h k a b : ℕ) (u : ℝ) : ℂ :=
  (((b : ℂ) * a)⁻¹) *
    hughesYoungReducedMellinStaticComplex T t h k
      ((1 : ℂ) + (u : ℂ) * I)

private theorem hughesYoungEquation84NegativeSourceTerm_eq_fourTerms
    (T t : ℝ) (h k a b : ℕ) (u : ℝ)
    (y : ℕ+ × ℕ+) :
    hughesYoungEquation84NegativeContourTerm T t h k a b
        (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I) =
      hughesYoungEquation84CompleteNegativeOuter T t h k a b u *
        (hughesYoungEquation84PositiveSourceArithmeticTerm b a false false u y *
            hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84PositiveSourceArithmeticTerm b a true false u y *
            hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84PositiveSourceArithmeticTerm b a false true u y *
            hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84PositiveSourceArithmeticTerm b a true true u y *
            hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)) := by
  unfold hughesYoungEquation84NegativeContourTerm
    hughesYoungEquation84CompleteNegativeOuter
    hughesYoungEquation84PositiveSourceArithmeticTerm
    hughesYoungEquation84PositiveCX hughesYoungEquation84PositiveCOne
  have hshift := hughesYoungCentralShiftPower_sourceLine
    (r := (y.2 : ℕ)) y.2.2 u
  rw [hshift]
  rw [hughesYoungEquation84RegularizedContourKernel_eq_fourTerm]
  simp only [Bool.false_eq_true, ↓reduceIte]
  ring

theorem summable_hughesYoungEquation84CompleteNegativeSourceLine
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation84NegativeContourTerm T t h k a b
        (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)) := by
  let P := hughesYoungEquation84CompleteNegativeOuter T t h k a b u
  let K₀₀ := hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)
  let K₁₀ := hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)
  let K₀₁ := hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)
  let K₁₁ := hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)
  have h₀₀ : Summable (hughesYoungEquation84PositiveSourceArithmeticTerm
      b a false false u) := by
    simpa only [hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm false false u hb ha hab.symm hη hη4
  have h₁₀ : Summable (hughesYoungEquation84PositiveSourceArithmeticTerm
      b a true false u) := by
    simpa only [hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm true false u hb ha hab.symm hη hη4
  have h₀₁ : Summable (hughesYoungEquation84PositiveSourceArithmeticTerm
      b a false true u) := by
    simpa only [hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm false true u hb ha hab.symm hη hη4
  have h₁₁ : Summable (hughesYoungEquation84PositiveSourceArithmeticTerm
      b a true true u) := by
    simpa only [hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm true true u hb ha hab.symm hη hη4
  have hs : Summable (fun y : ℕ+ × ℕ+ =>
      P * (hughesYoungEquation84PositiveSourceArithmeticTerm b a false false u y * K₀₀ +
        hughesYoungEquation84PositiveSourceArithmeticTerm b a true false u y * K₁₀ +
        hughesYoungEquation84PositiveSourceArithmeticTerm b a false true u y * K₀₁ +
        hughesYoungEquation84PositiveSourceArithmeticTerm b a true true u y * K₁₁)) := by
    apply Summable.mul_left
    exact (((h₀₀.mul_right K₀₀).add (h₁₀.mul_right K₁₀)).add
      (h₀₁.mul_right K₀₁)).add (h₁₁.mul_right K₁₁)
  apply hs.congr
  intro y
  simpa only [P, K₀₀, K₁₀, K₀₁, K₁₁] using
    (hughesYoungEquation84NegativeSourceTerm_eq_fourTerms T t h k a b u y).symm

/-- Exact complete-series equation-(84) expansion for the negative shift. -/
theorem hughesYoungEquation84CompleteNegativeSourceLine_eq_fourMoments
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    hughesYoungEquation84CompleteNegativeSourceLine T t h k a b u =
      hughesYoungEquation84CompleteNegativeOuter T t h k a b u *
        (hughesYoungEquation84CompletePositiveMomentAt b a false false u *
            hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84CompletePositiveMomentAt b a true false u *
            hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84CompletePositiveMomentAt b a false true u *
            hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84CompletePositiveMomentAt b a true true u *
            hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)) := by
  let P := hughesYoungEquation84CompleteNegativeOuter T t h k a b u
  let K₀₀ := hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)
  let K₁₀ := hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)
  let K₀₁ := hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)
  let K₁₁ := hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)
  let f : Bool → Bool → (ℕ+ × ℕ+) → ℂ := fun i j y =>
    hughesYoungEquation84PositiveSourceArithmeticTerm b a i j u y
  have h₀₀ : Summable (f false false) := by
    simpa only [f, hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm false false u hb ha hab.symm hη hη4
  have h₁₀ : Summable (f true false) := by
    simpa only [f, hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm true false u hb ha hab.symm hη hη4
  have h₀₁ : Summable (f false true) := by
    simpa only [f, hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm false true u hb ha hab.symm hη hη4
  have h₁₁ : Summable (f true true) := by
    simpa only [f, hughesYoungEquation84PositiveSourceArithmeticTerm] using
      summable_dfiEquation84PositiveMomentAtTerm true true u hb ha hab.symm hη hη4
  unfold hughesYoungEquation84CompleteNegativeSourceLine
  rw [show (∑' y : ℕ+ × ℕ+,
      hughesYoungEquation84NegativeContourTerm T t h k a b
        (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)) =
      ∑' y : ℕ+ × ℕ+,
        P * (f false false y * K₀₀ + f true false y * K₁₀ +
          f false true y * K₀₁ + f true true y * K₁₁) by
    apply tsum_congr
    intro y
    simpa only [P, K₀₀, K₁₀, K₀₁, K₁₁, f] using
      hughesYoungEquation84NegativeSourceTerm_eq_fourTerms T t h k a b u y]
  simp_rw [tsum_mul_left]
  rw [(((h₀₀.mul_right K₀₀).add (h₁₀.mul_right K₁₀)).add
      (h₀₁.mul_right K₀₁)).tsum_add (h₁₁.mul_right K₁₁),
    ((h₀₀.mul_right K₀₀).add (h₁₀.mul_right K₁₀)).tsum_add
      (h₀₁.mul_right K₀₁),
    (h₀₀.mul_right K₀₀).tsum_add (h₁₀.mul_right K₁₀)]
  simp only [tsum_mul_right]
  change P * ((∑' y, f false false y) * K₀₀ +
      (∑' y, f true false y) * K₁₀ +
      (∑' y, f false true y) * K₀₁ +
      (∑' y, f true true y) * K₁₁) = _
  simp only [P, K₀₀, K₁₀, K₀₁, K₁₁]
  congr 1

/-- Common arithmetic majorant for all four complete equation-(96)
moments on the source line. -/
noncomputable def hughesYoungEquation84ArithmeticMomentMajorant
    (a b : ℕ) (η : ℝ) : ℝ :=
  (((a : ℝ) ^ (1 / 2 + 2 * η) * (b : ℝ) ^ (1 / 2 + 2 * η)) *
      (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
      ((a : ℝ) ^ η * (b : ℝ) ^ η)) *
    ∑' y : ℕ+ × ℕ+,
      hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y

theorem norm_hughesYoungEquation84CompletePositiveMomentAt_le_majorant
    (i j : Bool) (u : ℝ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖hughesYoungEquation84CompletePositiveMomentAt a b i j u‖ ≤
      hughesYoungEquation84ArithmeticMomentMajorant a b η := by
  exact norm_hughesYoungEquation84CompletePositiveMomentAt_le
    i j u ha hb hab hη hη4

theorem hughesYoungEquation84ArithmeticMomentMajorant_nonneg
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    0 ≤ hughesYoungEquation84ArithmeticMomentMajorant a b η := by
  exact (norm_nonneg
    (hughesYoungEquation84CompletePositiveMomentAt a b false false 0)).trans
      (norm_hughesYoungEquation84CompletePositiveMomentAt_le_majorant
        false false 0 ha hb hab hη hη4)

/-- The complete equation-(96) arithmetic moments vary continuously with
the source-line ordinate.  The proof is a uniform Weierstrass argument
using the same positive pair majorant as absolute convergence. -/
theorem continuous_hughesYoungEquation84CompletePositiveMomentAt
    (i j : Bool) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Continuous (fun u : ℝ =>
      hughesYoungEquation84CompletePositiveMomentAt a b i j u) := by
  let K : ℝ := ((a : ℝ) ^ (1 / 2 + 2 * η) *
      (b : ℝ) ^ (1 / 2 + 2 * η)) *
    (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
    ((a : ℝ) ^ η * (b : ℝ) ^ η)
  have hA : 1 < 1 + 2 * η := by linarith
  have hC : 0 < 1 - 2 * η := by linarith
  have hm : Summable (fun y : ℕ+ × ℕ+ =>
      K * hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y) :=
    (summable_hughesYoungPositivePairMajorant hA hC).mul_left K
  unfold hughesYoungEquation84CompletePositiveMomentAt
  apply continuous_tsum
  · intro y
    have hr : (((y.2 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast y.2.2.ne'
    apply Continuous.mul
    · apply Continuous.mul
      · exact continuous_const.div₀
          (continuous_const_cpow_of_ne_zero ((y.2 : ℕ) : ℂ) hr (by fun_prop))
          (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hr))
      · fun_prop
    · fun_prop
  · exact hm
  · intro y u
    rw [dfiEquation27ArithmeticCoefficient_div_vertical_cpow_eq_equation96PositiveTerm
      u hab y]
    rw [show (if i then hughesYoungEquation84PositiveCX b (y.2 : ℕ) (y.1 : ℕ) else 1) =
        hughesYoungDFIPositiveLogSelectorRight i b y by
      cases i <;> simp [hughesYoungDFIPositiveLogSelectorRight,
        hughesYoungEquation84PositiveCX_eq_dfiPositiveLogFactorRight b y] ]
    rw [show (if j then hughesYoungEquation84PositiveCOne a (y.2 : ℕ) (y.1 : ℕ) else 1) =
        hughesYoungDFIPositiveLogSelectorLeft j a y by
      cases j <;> simp [hughesYoungDFIPositiveLogSelectorLeft,
        hughesYoungEquation84PositiveCOne_eq_dfiPositiveLogFactorLeft a y] ]
    simpa only [K, mul_assoc, mul_left_comm, mul_comm] using
      norm_hughesYoungEquation96VerticalTerm_mul_logSelectors_le
        j i u ha hb hη hη4 y

private theorem continuous_hughesYoungReducedMellinStaticComplex_sourceLine
    (T t : ℝ) (h k : ℕ) :
    Continuous (fun u : ℝ =>
      hughesYoungReducedMellinStaticComplex T t h k
        ((1 : ℂ) + (u : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hline : ContinuousAt (fun v : ℝ =>
      (1 : ℂ) + (v : ℂ) * I) u := by fun_prop
  have hcomp := ContinuousAt.comp
    (f := fun v : ℝ => (1 : ℂ) + (v : ℂ) * I)
    (g := hughesYoungReducedMellinStaticComplex T t h k)
    (differentiableAt_hughesYoungReducedMellinStaticComplex T t h k
      ((1 : ℂ) + (u : ℂ) * I)).continuousAt hline
  simpa only [Function.comp_apply] using hcomp

private theorem continuous_hughesYoungEquation84Kernel00_sourceLine
    (t : ℝ) : Continuous (fun u : ℝ =>
      hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hline : ContinuousAt (fun v : ℝ =>
      (1 : ℂ) + (v : ℂ) * I) u := by fun_prop
  have hcomp := ContinuousAt.comp
    (f := fun v : ℝ => (1 : ℂ) + (v : ℂ) * I)
    (g := hughesYoungEquation84Kernel00 t)
    (differentiableAt_hughesYoungEquation84Kernel00 t
      (w := (1 : ℂ) + (u : ℂ) * I)
      (by norm_num) (by norm_num)).continuousAt hline
  simpa only [Function.comp_apply] using hcomp

private theorem continuous_hughesYoungEquation84Kernel10_sourceLine
    (t : ℝ) : Continuous (fun u : ℝ =>
      hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hline : ContinuousAt (fun v : ℝ =>
      (1 : ℂ) + (v : ℂ) * I) u := by fun_prop
  have hcomp := ContinuousAt.comp
    (f := fun v : ℝ => (1 : ℂ) + (v : ℂ) * I)
    (g := hughesYoungEquation84Kernel10 t)
    (differentiableAt_hughesYoungEquation84Kernel10 t
      (w := (1 : ℂ) + (u : ℂ) * I)
      (by norm_num) (by norm_num)).continuousAt hline
  simpa only [Function.comp_apply] using hcomp

private theorem continuous_hughesYoungEquation84Kernel01_sourceLine
    (t : ℝ) : Continuous (fun u : ℝ =>
      hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hline : ContinuousAt (fun v : ℝ =>
      (1 : ℂ) + (v : ℂ) * I) u := by fun_prop
  have hcomp := ContinuousAt.comp
    (f := fun v : ℝ => (1 : ℂ) + (v : ℂ) * I)
    (g := hughesYoungEquation84Kernel01 t)
    (differentiableAt_hughesYoungEquation84Kernel01 t
      (w := (1 : ℂ) + (u : ℂ) * I)
      (by norm_num) (by norm_num)).continuousAt hline
  simpa only [Function.comp_apply] using hcomp

private theorem continuous_hughesYoungEquation84Kernel11_sourceLine
    (t : ℝ) : Continuous (fun u : ℝ =>
      hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hline : ContinuousAt (fun v : ℝ =>
      (1 : ℂ) + (v : ℂ) * I) u := by fun_prop
  have hcomp := ContinuousAt.comp
    (f := fun v : ℝ => (1 : ℂ) + (v : ℂ) * I)
    (g := hughesYoungEquation84Kernel11 t)
    (differentiableAt_hughesYoungEquation84Kernel11 t
      (w := (1 : ℂ) + (u : ℂ) * I)
      (by norm_num) (by norm_num)).continuousAt hline
  simpa only [Function.comp_apply] using hcomp

/-- The complete positive equation-(84) source-line series is continuous.
This is the analytic regularity needed for its compact and improper
vertical integrals. -/
theorem continuous_hughesYoungEquation84CompletePositiveSourceLine
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Continuous (hughesYoungEquation84CompletePositiveSourceLine
      T t h k a b) := by
  have heq : hughesYoungEquation84CompletePositiveSourceLine T t h k a b =
      fun u => hughesYoungEquation84CompletePositiveOuter T t h k a b u *
        (hughesYoungEquation84CompletePositiveMomentAt a b false false u *
            hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84CompletePositiveMomentAt a b true false u *
            hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84CompletePositiveMomentAt a b false true u *
            hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84CompletePositiveMomentAt a b true true u *
            hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)) := by
    funext u
    exact hughesYoungEquation84CompletePositiveSourceLine_eq_fourMoments
      T t h k ha hb hab u hη hη4
  rw [heq]
  have hOuter : Continuous
      (hughesYoungEquation84CompletePositiveOuter T t h k a b) := by
    unfold hughesYoungEquation84CompletePositiveOuter
    exact continuous_const.mul
      (continuous_hughesYoungReducedMellinStaticComplex_sourceLine T t h k)
  have h₀₀ := (continuous_hughesYoungEquation84CompletePositiveMomentAt
    false false ha hb hab hη hη4).mul
      (continuous_hughesYoungEquation84Kernel00_sourceLine t)
  have h₁₀ := (continuous_hughesYoungEquation84CompletePositiveMomentAt
    true false ha hb hab hη hη4).mul
      (continuous_hughesYoungEquation84Kernel10_sourceLine t)
  have h₀₁ := (continuous_hughesYoungEquation84CompletePositiveMomentAt
    false true ha hb hab hη hη4).mul
      (continuous_hughesYoungEquation84Kernel01_sourceLine t)
  have h₁₁ := (continuous_hughesYoungEquation84CompletePositiveMomentAt
    true true ha hb hab hη hη4).mul
      (continuous_hughesYoungEquation84Kernel11_sourceLine t)
  exact hOuter.mul (((h₀₀.add h₁₀).add h₀₁).add h₁₁)

/-- The complete negative equation-(84) source-line series is continuous. -/
theorem continuous_hughesYoungEquation84CompleteNegativeSourceLine
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Continuous (hughesYoungEquation84CompleteNegativeSourceLine
      T t h k a b) := by
  have heq : hughesYoungEquation84CompleteNegativeSourceLine T t h k a b =
      fun u => hughesYoungEquation84CompleteNegativeOuter T t h k a b u *
        (hughesYoungEquation84CompletePositiveMomentAt b a false false u *
            hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84CompletePositiveMomentAt b a true false u *
            hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84CompletePositiveMomentAt b a false true u *
            hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I) +
          hughesYoungEquation84CompletePositiveMomentAt b a true true u *
            hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)) := by
    funext u
    exact hughesYoungEquation84CompleteNegativeSourceLine_eq_fourMoments
      T t h k ha hb hab u hη hη4
  rw [heq]
  have hOuter : Continuous
      (hughesYoungEquation84CompleteNegativeOuter T t h k a b) := by
    unfold hughesYoungEquation84CompleteNegativeOuter
    exact continuous_const.mul
      (continuous_hughesYoungReducedMellinStaticComplex_sourceLine T t h k)
  have h₀₀ := (continuous_hughesYoungEquation84CompletePositiveMomentAt
    false false hb ha hab.symm hη hη4).mul
      (continuous_hughesYoungEquation84Kernel00_sourceLine (-t))
  have h₁₀ := (continuous_hughesYoungEquation84CompletePositiveMomentAt
    true false hb ha hab.symm hη hη4).mul
      (continuous_hughesYoungEquation84Kernel10_sourceLine (-t))
  have h₀₁ := (continuous_hughesYoungEquation84CompletePositiveMomentAt
    false true hb ha hab.symm hη hη4).mul
      (continuous_hughesYoungEquation84Kernel01_sourceLine (-t))
  have h₁₁ := (continuous_hughesYoungEquation84CompletePositiveMomentAt
    true true hb ha hab.symm hη hη4).mul
      (continuous_hughesYoungEquation84Kernel11_sourceLine (-t))
  exact hOuter.mul (((h₀₀.add h₁₀).add h₀₁).add h₁₁)

/-- Uniform arithmetic reduction of the complete positive source-line
series.  All dependence on the vertical variable is now confined to the
explicit outer factor and the four archimedean kernels. -/
theorem norm_hughesYoungEquation84CompletePositiveSourceLine_le
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖hughesYoungEquation84CompletePositiveSourceLine T t h k a b u‖ ≤
      ‖hughesYoungEquation84CompletePositiveOuter T t h k a b u‖ *
        hughesYoungEquation84ArithmeticMomentMajorant a b η *
        (‖hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖) := by
  rw [hughesYoungEquation84CompletePositiveSourceLine_eq_fourMoments
    T t h k ha hb hab u hη hη4, norm_mul]
  let B := hughesYoungEquation84ArithmeticMomentMajorant a b η
  let K₀₀ := hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)
  let K₁₀ := hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)
  let K₀₁ := hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)
  let K₁₁ := hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)
  have hB : 0 ≤ B := hughesYoungEquation84ArithmeticMomentMajorant_nonneg ha hb hab hη hη4
  have h₀₀ := norm_hughesYoungEquation84CompletePositiveMomentAt_le_majorant
    false false u ha hb hab hη hη4
  have h₁₀ := norm_hughesYoungEquation84CompletePositiveMomentAt_le_majorant
    true false u ha hb hab hη hη4
  have h₀₁ := norm_hughesYoungEquation84CompletePositiveMomentAt_le_majorant
    false true u ha hb hab hη hη4
  have h₁₁ := norm_hughesYoungEquation84CompletePositiveMomentAt_le_majorant
    true true u ha hb hab hη hη4
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖hughesYoungEquation84CompletePositiveMomentAt a b false false u * K₀₀ +
          hughesYoungEquation84CompletePositiveMomentAt a b true false u * K₁₀ +
          hughesYoungEquation84CompletePositiveMomentAt a b false true u * K₀₁ +
          hughesYoungEquation84CompletePositiveMomentAt a b true true u * K₁₁‖ ≤
        ‖hughesYoungEquation84CompletePositiveMomentAt a b false false u‖ * ‖K₀₀‖ +
          ‖hughesYoungEquation84CompletePositiveMomentAt a b true false u‖ * ‖K₁₀‖ +
          ‖hughesYoungEquation84CompletePositiveMomentAt a b false true u‖ * ‖K₀₁‖ +
          ‖hughesYoungEquation84CompletePositiveMomentAt a b true true u‖ * ‖K₁₁‖ := by
      simpa only [norm_mul] using
        norm_add_le
          (hughesYoungEquation84CompletePositiveMomentAt a b false false u * K₀₀ +
            hughesYoungEquation84CompletePositiveMomentAt a b true false u * K₁₀ +
            hughesYoungEquation84CompletePositiveMomentAt a b false true u * K₀₁)
          (hughesYoungEquation84CompletePositiveMomentAt a b true true u * K₁₁) |>.trans
            (add_le_add (norm_add_le _ _ |>.trans
              (add_le_add (norm_add_le _ _) (le_refl _))) (le_refl _))
    _ ≤ B * ‖K₀₀‖ + B * ‖K₁₀‖ + B * ‖K₀₁‖ + B * ‖K₁₁‖ := by
      gcongr
    _ = B * (‖K₀₀‖ + ‖K₁₀‖ + ‖K₀₁‖ + ‖K₁₁‖) := by ring
    _ = _ := by rfl

/-- The identical arithmetic reduction for the negative, swapped source
series. -/
theorem norm_hughesYoungEquation84CompleteNegativeSourceLine_le
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖hughesYoungEquation84CompleteNegativeSourceLine T t h k a b u‖ ≤
      ‖hughesYoungEquation84CompleteNegativeOuter T t h k a b u‖ *
        hughesYoungEquation84ArithmeticMomentMajorant b a η *
        (‖hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)‖) := by
  rw [hughesYoungEquation84CompleteNegativeSourceLine_eq_fourMoments
    T t h k ha hb hab u hη hη4, norm_mul]
  let B := hughesYoungEquation84ArithmeticMomentMajorant b a η
  let K₀₀ := hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)
  let K₁₀ := hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)
  let K₀₁ := hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)
  let K₁₁ := hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)
  have hB : 0 ≤ B := hughesYoungEquation84ArithmeticMomentMajorant_nonneg hb ha hab.symm hη hη4
  have h₀₀ := norm_hughesYoungEquation84CompletePositiveMomentAt_le_majorant
    false false u hb ha hab.symm hη hη4
  have h₁₀ := norm_hughesYoungEquation84CompletePositiveMomentAt_le_majorant
    true false u hb ha hab.symm hη hη4
  have h₀₁ := norm_hughesYoungEquation84CompletePositiveMomentAt_le_majorant
    false true u hb ha hab.symm hη hη4
  have h₁₁ := norm_hughesYoungEquation84CompletePositiveMomentAt_le_majorant
    true true u hb ha hab.symm hη hη4
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖hughesYoungEquation84CompletePositiveMomentAt b a false false u * K₀₀ +
          hughesYoungEquation84CompletePositiveMomentAt b a true false u * K₁₀ +
          hughesYoungEquation84CompletePositiveMomentAt b a false true u * K₀₁ +
          hughesYoungEquation84CompletePositiveMomentAt b a true true u * K₁₁‖ ≤
        ‖hughesYoungEquation84CompletePositiveMomentAt b a false false u‖ * ‖K₀₀‖ +
          ‖hughesYoungEquation84CompletePositiveMomentAt b a true false u‖ * ‖K₁₀‖ +
          ‖hughesYoungEquation84CompletePositiveMomentAt b a false true u‖ * ‖K₀₁‖ +
          ‖hughesYoungEquation84CompletePositiveMomentAt b a true true u‖ * ‖K₁₁‖ := by
      simpa only [norm_mul] using
        norm_add_le
          (hughesYoungEquation84CompletePositiveMomentAt b a false false u * K₀₀ +
            hughesYoungEquation84CompletePositiveMomentAt b a true false u * K₁₀ +
            hughesYoungEquation84CompletePositiveMomentAt b a false true u * K₀₁)
          (hughesYoungEquation84CompletePositiveMomentAt b a true true u * K₁₁) |>.trans
            (add_le_add (norm_add_le _ _ |>.trans
              (add_le_add (norm_add_le _ _) (le_refl _))) (le_refl _))
    _ ≤ B * ‖K₀₀‖ + B * ‖K₁₀‖ + B * ‖K₀₁‖ + B * ‖K₁₁‖ := by
      gcongr
    _ = B * (‖K₀₀‖ + ‖K₁₀‖ + ‖K₀₁‖ + ‖K₁₁‖) := by ring
    _ = _ := by rfl

/-- The complete positive source-line series is Bochner integrable on the
whole ordinate line.  The compact part uses continuity and the tails use
the uniform equation-(84) Gaussian kernel bound after the complete DFI
series has been assembled. -/
theorem integrable_hughesYoungEquation84CompletePositiveSourceLine
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Integrable (hughesYoungEquation84CompletePositiveSourceLine
      T t h k a b) := by
  obtain ⟨K, hK, hOuter⟩ := exists_uniform_norm_hughesYoungCentralOuterFactor
    T t h k 1 (((a : ℂ) * b)⁻¹) (c₀ := 1) (c₁ := 1)
  obtain ⟨B, hB, hCoeff⟩ :=
    exists_norm_hughesYoungEquation84KernelCoefficients_horizontal_le
      t (c₀ := 1) (c₁ := 1) (by norm_num) (by norm_num) (by norm_num)
  let M := hughesYoungEquation84ArithmeticMomentMajorant a b η
  let L : ℝ := max 1 (|t| + 1)
  have hM : 0 ≤ M := by
    exact hughesYoungEquation84ArithmeticMomentMajorant_nonneg
      ha hb hab hη hη4
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply integrable_of_continuous_of_norm_le_gaussian_tail
    (hughesYoungEquation84CompletePositiveSourceLine T t h k a b)
    (continuous_hughesYoungEquation84CompletePositiveSourceLine
      T t h k ha hb hab hη hη4)
    hL (by norm_num : (0 : ℝ) < 60)
  intro u hu
  have hu1 : 1 ≤ |u| := (le_max_left 1 (|t| + 1)).trans hu
  have hut : |t| + 1 ≤ |u| := (le_max_right 1 (|t| + 1)).trans hu
  have hoRaw := hOuter u 1 (by simp)
  have ho : ‖hughesYoungEquation84CompletePositiveOuter T t h k a b u‖ ≤ K := by
    simpa only [hughesYoungEquation84CompletePositiveOuter,
      hughesYoungCentralShiftPower, Nat.cast_one,
      Real.log_one, ofReal_zero, mul_zero, Complex.exp_zero, mul_one] using hoRaw
  have hc := hCoeff u hu1 hut 1 (by simp)
  have hs := norm_hughesYoungEquation84CompletePositiveSourceLine_le
    T t h k ha hb hab u hη hη4
  let E : ℝ := Real.exp (100 - 60 * u ^ 2)
  let R : ℝ := (2 + |t| + 1 + |u|) ^ 9
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hc' :
      ‖hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖ ≤ B * E * R ∧
      ‖hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖ ≤ B * E * R ∧
      ‖hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖ ≤ B * E * R ∧
      ‖hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖ ≤ B * E * R := by
    norm_num at hc
    simpa only [E, R] using hc
  calc
    ‖hughesYoungEquation84CompletePositiveSourceLine T t h k a b u‖
        ≤ ‖hughesYoungEquation84CompletePositiveOuter T t h k a b u‖ * M *
          (‖hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖ +
           ‖hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖ +
           ‖hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖ +
           ‖hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖) := hs
    _ ≤ K * M * (4 * (B * E * R)) := by
      gcongr
      linarith [hc'.1, hc'.2.1, hc'.2.2.1, hc'.2.2.2]
    _ = (4 * K * M * B) * Real.exp (100 - 60 * u ^ 2) *
          ((2 + |t| + 1) + |u|) ^ 9 := by
      dsimp [E, R]
      ring

/-- The complete negative source-line series is Bochner integrable on the
whole ordinate line. -/
theorem integrable_hughesYoungEquation84CompleteNegativeSourceLine
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Integrable (hughesYoungEquation84CompleteNegativeSourceLine
      T t h k a b) := by
  obtain ⟨K, hK, hOuter⟩ := exists_uniform_norm_hughesYoungCentralOuterFactor
    T t h k 1 (((b : ℂ) * a)⁻¹) (c₀ := 1) (c₁ := 1)
  obtain ⟨B, hB, hCoeff⟩ :=
    exists_norm_hughesYoungEquation84KernelCoefficients_horizontal_le
      (-t) (c₀ := 1) (c₁ := 1) (by norm_num) (by norm_num) (by norm_num)
  let M := hughesYoungEquation84ArithmeticMomentMajorant b a η
  let L : ℝ := max 1 (|t| + 1)
  have hM : 0 ≤ M := by
    exact hughesYoungEquation84ArithmeticMomentMajorant_nonneg
      hb ha hab.symm hη hη4
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply integrable_of_continuous_of_norm_le_gaussian_tail
    (hughesYoungEquation84CompleteNegativeSourceLine T t h k a b)
    (continuous_hughesYoungEquation84CompleteNegativeSourceLine
      T t h k ha hb hab hη hη4)
    hL (by norm_num : (0 : ℝ) < 60)
  intro u hu
  have hu1 : 1 ≤ |u| := (le_max_left 1 (|t| + 1)).trans hu
  have hut : |-t| + 1 ≤ |u| := by
    rw [abs_neg]
    exact (le_max_right 1 (|t| + 1)).trans hu
  have hoRaw := hOuter u 1 (by simp)
  have ho : ‖hughesYoungEquation84CompleteNegativeOuter T t h k a b u‖ ≤ K := by
    simpa only [hughesYoungEquation84CompleteNegativeOuter,
      hughesYoungCentralShiftPower, Nat.cast_one,
      Real.log_one, ofReal_zero, mul_zero, Complex.exp_zero, mul_one] using hoRaw
  have hc := hCoeff u hu1 hut 1 (by simp)
  have hs := norm_hughesYoungEquation84CompleteNegativeSourceLine_le
    T t h k ha hb hab u hη hη4
  let E : ℝ := Real.exp (100 - 60 * u ^ 2)
  let R : ℝ := (2 + |t| + 1 + |u|) ^ 9
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hc' :
      ‖hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ ≤ B * E * R ∧
      ‖hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ ≤ B * E * R ∧
      ‖hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ ≤ B * E * R ∧
      ‖hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ ≤ B * E * R := by
    norm_num [abs_neg] at hc
    simpa only [E, R, abs_neg] using hc
  calc
    ‖hughesYoungEquation84CompleteNegativeSourceLine T t h k a b u‖
        ≤ ‖hughesYoungEquation84CompleteNegativeOuter T t h k a b u‖ * M *
          (‖hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
           ‖hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
           ‖hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
           ‖hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)‖) := hs
    _ ≤ K * M * (4 * (B * E * R)) := by
      gcongr
      linarith [hc'.1, hc'.2.1, hc'.2.2.1, hc'.2.2.2]
    _ = (4 * K * M * B) * Real.exp (100 - 60 * u ^ 2) *
          ((2 + |t| + 1) + |u|) ^ 9 := by
      dsimp [E, R]
      ring

end RiemannZeta.GuthMaynard
