import RiemannZeta.GuthMaynard.HughesYoungSignedCentralHeight
import RiemannZeta.GuthMaynard.HughesYoungCompleteContour

open Complex MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The signed DFI central series on the Hughes--Young source line

These are the exact fixed-shift consumer theorems joining DFI equation (27)
to Hughes--Young equations (83)--(84), followed by the pole-cancelled contour
translation to `Re w = 1`.  No absolute value is taken before the signed
source identity has been assembled.
-/

/-- A positive signed DFI central series, integrated on the original small
Mellin line, is exactly the complete equation-(84) modulus series on the
absolutely convergent source line. -/
theorem integral_dfiSignedCentralSeries_pureReduced_ofNat_eq_sourceLine
    (T t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    (∫ u : ℝ,
      dfiSignedCentralSeries a b (r : ℤ)
        (hughesYoungPureReducedMellinWeight T t c u h k)) =
      ∫ u : ℝ,
        hughesYoungEquation84PositiveContourSeries T t h k a b r
          ((1 : ℂ) + (u : ℂ) * I) := by
  have hpoint : ∀ u : ℝ,
      dfiSignedCentralSeries a b (r : ℤ)
          (hughesYoungPureReducedMellinWeight T t c u h k) =
        hughesYoungEquation84PositiveContourSeries T t h k a b r
          ((c : ℂ) + (u : ℂ) * I) := by
    intro u
    rw [dfiSignedCentralSeries_ofNat_pureReduced_eq_equation83
      T t c u a b hr]
    rw [hughesYoungEquation83PositiveCentral_eq_equation84
      T t u hc hcHalf h k a b r]
    exact hughesYoungEquation84Positive_eq_contourSeries
      T t u hcHalf h k a b hr
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  exact (integral_hughesYoungEquation84PositiveContourSeries_vertical_eq
    T t h k a b r ha hb hr hc (by norm_num) (by linarith)).symm

/-- The negative signed DFI branch obeys the coordinate-swapped source-line
identity with no loss and no premature norm. -/
theorem integral_dfiSignedCentralSeries_pureReduced_neg_eq_sourceLine
    (T t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    (∫ u : ℝ,
      dfiSignedCentralSeries a b (-(r : ℤ))
        (hughesYoungPureReducedMellinWeight T t c u h k)) =
      ∫ u : ℝ,
        hughesYoungEquation84NegativeContourSeries T t h k a b r
          ((1 : ℂ) + (u : ℂ) * I) := by
  have hpoint : ∀ u : ℝ,
      dfiSignedCentralSeries a b (-(r : ℤ))
          (hughesYoungPureReducedMellinWeight T t c u h k) =
        hughesYoungEquation84NegativeContourSeries T t h k a b r
          ((c : ℂ) + (u : ℂ) * I) := by
    intro u
    rw [dfiSignedCentralSeries_neg_pureReduced_eq_equation83
      T t c u a b hr]
    rw [hughesYoungEquation83NegativeCentral_eq_equation84
      T t u hc hcHalf h k a b r]
    exact hughesYoungEquation84Negative_eq_contourSeries
      T t u hcHalf h k a b hr
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  exact (integral_hughesYoungEquation84NegativeContourSeries_vertical_eq
    T t h k a b r ha hb hr hc (by norm_num) (by linarith)).symm

/-! ## Reassembly of the complete positive `(q,r)` source series -/

/-- The totalized natural-number modulus series is the positive-natural
modulus series: its only omitted term is the definitionally zero modulus. -/
theorem tsum_hughesYoungEquation84PositiveContourTerm_nat_eq_pnat
    (T t : ℝ) (h k a b r : ℕ) (w : ℂ) :
    (∑' q : ℕ,
      hughesYoungEquation84PositiveContourTerm T t h k a b r q w) =
      ∑' q : ℕ+,
        hughesYoungEquation84PositiveContourTerm T t h k a b r q w := by
  let f : ℕ → ℂ := fun q =>
    hughesYoungEquation84PositiveContourTerm T t h k a b r q w
  calc
    (∑' q : ℕ, f q) =
        ∑' q : ℕ, ({q : ℕ | 0 < q}.indicator f) q := by
      apply tsum_congr
      intro q
      by_cases hq : 0 < q
      · simp only [Set.mem_setOf_eq, hq, Set.indicator_of_mem]
      · have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
        subst q
        simp [f, hughesYoungEquation84PositiveContourTerm,
          dfiEquation27ArithmeticCoefficient_zero]
    _ = ∑' q : ℕ+, f q := by
      simpa only [PNat] using
        (tsum_subtype {q : ℕ | 0 < q} f).symm

/-- Negative-coordinate counterpart of zero-modulus removal. -/
theorem tsum_hughesYoungEquation84NegativeContourTerm_nat_eq_pnat
    (T t : ℝ) (h k a b r : ℕ) (w : ℂ) :
    (∑' q : ℕ,
      hughesYoungEquation84NegativeContourTerm T t h k a b r q w) =
      ∑' q : ℕ+,
        hughesYoungEquation84NegativeContourTerm T t h k a b r q w := by
  let f : ℕ → ℂ := fun q =>
    hughesYoungEquation84NegativeContourTerm T t h k a b r q w
  calc
    (∑' q : ℕ, f q) =
        ∑' q : ℕ, ({q : ℕ | 0 < q}.indicator f) q := by
      apply tsum_congr
      intro q
      by_cases hq : 0 < q
      · simp only [Set.mem_setOf_eq, hq, Set.indicator_of_mem]
      · have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
        subst q
        simp [f, hughesYoungEquation84NegativeContourTerm,
          dfiEquation27ArithmeticCoefficient_zero]
    _ = ∑' q : ℕ+, f q := by
      simpa only [PNat] using
        (tsum_subtype {q : ℕ | 0 < q} f).symm

/-- Iterating first over positive shifts and then over totalized moduli gives
the exact complete positive equation-(84) source series. -/
theorem tsum_hughesYoungEquation84PositiveContourSeries_eq_completeSourceLine
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    (∑' r : ℕ+,
      hughesYoungEquation84PositiveContourSeries T t h k a b r
        ((1 : ℂ) + (u : ℂ) * I)) =
      hughesYoungEquation84CompletePositiveSourceLine T t h k a b u := by
  let F : ℕ+ × ℕ+ → ℂ := fun y =>
    hughesYoungEquation84PositiveContourTerm T t h k a b
      (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)
  have hF : Summable F := by
    simpa only [F] using
      summable_hughesYoungEquation84CompletePositiveSourceLine
        T t h k ha hb hab u hη hη4
  have hSwap : Summable (fun y : ℕ+ × ℕ+ => F y.swap) :=
    hF.comp_injective (Equiv.prodComm ℕ+ ℕ+).injective
  calc
    (∑' r : ℕ+,
        hughesYoungEquation84PositiveContourSeries T t h k a b r
          ((1 : ℂ) + (u : ℂ) * I)) =
      ∑' r : ℕ+, ∑' q : ℕ+,
        hughesYoungEquation84PositiveContourTerm T t h k a b r q
          ((1 : ℂ) + (u : ℂ) * I) := by
        apply tsum_congr
        intro r
        unfold hughesYoungEquation84PositiveContourSeries
        exact tsum_hughesYoungEquation84PositiveContourTerm_nat_eq_pnat
          T t h k a b r ((1 : ℂ) + (u : ℂ) * I)
    _ = ∑' y : ℕ+ × ℕ+, F y.swap := hSwap.tsum_prod.symm
    _ = ∑' y : ℕ+ × ℕ+, F y :=
      (Equiv.prodComm ℕ+ ℕ+).tsum_eq F
    _ = hughesYoungEquation84CompletePositiveSourceLine T t h k a b u := by
      rfl

/-- The identical complete reassembly for the negative signed shifts. -/
theorem tsum_hughesYoungEquation84NegativeContourSeries_eq_completeSourceLine
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    (∑' r : ℕ+,
      hughesYoungEquation84NegativeContourSeries T t h k a b r
        ((1 : ℂ) + (u : ℂ) * I)) =
      hughesYoungEquation84CompleteNegativeSourceLine T t h k a b u := by
  let F : ℕ+ × ℕ+ → ℂ := fun y =>
    hughesYoungEquation84NegativeContourTerm T t h k a b
      (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)
  have hF : Summable F := by
    simpa only [F] using
      summable_hughesYoungEquation84CompleteNegativeSourceLine
        T t h k ha hb hab u hη hη4
  have hSwap : Summable (fun y : ℕ+ × ℕ+ => F y.swap) :=
    hF.comp_injective (Equiv.prodComm ℕ+ ℕ+).injective
  calc
    (∑' r : ℕ+,
        hughesYoungEquation84NegativeContourSeries T t h k a b r
          ((1 : ℂ) + (u : ℂ) * I)) =
      ∑' r : ℕ+, ∑' q : ℕ+,
        hughesYoungEquation84NegativeContourTerm T t h k a b r q
          ((1 : ℂ) + (u : ℂ) * I) := by
        apply tsum_congr
        intro r
        unfold hughesYoungEquation84NegativeContourSeries
        exact tsum_hughesYoungEquation84NegativeContourTerm_nat_eq_pnat
          T t h k a b r ((1 : ℂ) + (u : ℂ) * I)
    _ = ∑' y : ℕ+ × ℕ+, F y.swap := hSwap.tsum_prod.symm
    _ = ∑' y : ℕ+ × ℕ+, F y :=
      (Equiv.prodComm ℕ+ ℕ+).tsum_eq F
    _ = hughesYoungEquation84CompleteNegativeSourceLine T t h k a b u := by
      rfl

end RiemannZeta.GuthMaynard
