import Mathlib.NumberTheory.LSeries.Convolution
import RiemannZeta.GuthMaynard.DFIEquation26

open Complex Finset
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Hughes--Young equations (96)--(118)

This module starts the exact arithmetic evaluation of the signed DFI central
series used in Hughes--Young section 6.2.  Natural indices are represented by
`r + 1` and `l + 1`, so the source sums begin at one without adding artificial
zero terms.
-/

/-- Hughes--Young equation (96), with the paper's three complex exponent
parameters and its two fixed twisting integers. -/
noncomputable def hughesYoungEquation96
    (h k : ℕ) (a b c : ℂ) : ℂ :=
  ∑' r : ℕ, ∑' l : ℕ,
    ramanujanSum (l + 1) (r + 1) *
      ((Nat.gcd h (l + 1) : ℕ) : ℂ) ^ a *
      ((Nat.gcd k (l + 1) : ℕ) : ℂ) ^ b /
      (((l + 1 : ℕ) : ℂ) ^ (a + b) *
        ((r + 1 : ℕ) : ℂ) ^ c)

/-- Hughes--Young equation (104), using the same Ramanujan sum as the exact
DFI equation-(27) coefficient. -/
theorem hughesYoungEquation104 (l r : ℕ) [NeZero l] :
    ramanujanSum l r =
      ∑ d ∈ (Nat.gcd r l).divisors,
        (d : ℂ) * ArithmeticFunction.moebius (l / d) := by
  exact ramanujanSum_eq_dfi26 l r

/-- Equation (96) after the literal equation-(104) Möbius expansion.  This
is the first equality in Hughes--Young's proof of Lemma 6.1; no convergence
reordering has yet been used. -/
theorem hughesYoungEquation96_eq_moebiusExpansion
    (h k : ℕ) (a b c : ℂ) :
    hughesYoungEquation96 h k a b c =
      ∑' r : ℕ, ∑' l : ℕ,
        (∑ d ∈ (Nat.gcd (r + 1) (l + 1)).divisors,
            (d : ℂ) * ArithmeticFunction.moebius ((l + 1) / d)) *
          ((Nat.gcd h (l + 1) : ℕ) : ℂ) ^ a *
          ((Nat.gcd k (l + 1) : ℕ) : ℂ) ^ b /
          (((l + 1 : ℕ) : ℂ) ^ (a + b) *
            ((r + 1 : ℕ) : ℂ) ^ c) := by
  unfold hughesYoungEquation96
  apply tsum_congr
  intro r
  apply tsum_congr
  intro l
  letI : NeZero (l + 1) := ⟨Nat.succ_ne_zero l⟩
  rw [hughesYoungEquation104 (l + 1) (r + 1)]

/-- The finite Möbius factor which appears after equation (104), regarded
as an arithmetic function so that its convolution with `ζ` can be evaluated
by the L-series product theorem. -/
noncomputable def hughesYoungMoebiusDivisorCoeff (l : ℕ) :
    ArithmeticFunction ℂ :=
  ⟨fun d => if d = 0 then 0 else
      if d ∣ l then (d : ℂ) * ArithmeticFunction.moebius (l / d) else 0,
    by simp⟩

@[simp]
theorem hughesYoungMoebiusDivisorCoeff_apply_of_dvd
    {l d : ℕ} (hd0 : d ≠ 0) (hdl : d ∣ l) :
    hughesYoungMoebiusDivisorCoeff l d =
      (d : ℂ) * ArithmeticFunction.moebius (l / d) := by
  simp [hughesYoungMoebiusDivisorCoeff, hd0, hdl]

@[simp]
theorem hughesYoungMoebiusDivisorCoeff_apply_of_not_dvd
    {l d : ℕ} (hdl : ¬d ∣ l) :
    hughesYoungMoebiusDivisorCoeff l d = 0 := by
  simp [hughesYoungMoebiusDivisorCoeff, hdl]

/-- The coefficient identity underlying Hughes--Young equation (105): the
Ramanujan coefficient is the Dirichlet convolution of `ζ` with the finite
Möbius divisor factor attached to `l`. -/
theorem coe_zeta_mul_hughesYoungMoebiusDivisorCoeff_apply
    (l r : ℕ) [NeZero l] (hr : 0 < r) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        hughesYoungMoebiusDivisorCoeff l) r = ramanujanSum l r := by
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  rw [hughesYoungEquation104 l r]
  rw [Nat.gcd_comm r l]
  rw [← filter_divisors_dvd_eq_gcd_divisors l r hr]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hdDivR : d ∣ r := (Nat.mem_divisors.mp hd).1
  have hd0 : d ≠ 0 := fun hdZero => by
    subst d
    exact hr.ne' (zero_dvd_iff.mp hdDivR)
  by_cases hdl : d ∣ l
  · simp [hdl, hd0]
  · simp [hdl]

/-- The finite Möbius divisor factor has an absolutely convergent L-series
at every complex point. -/
theorem hughesYoungMoebiusDivisorCoeff_LSeriesSummable
    (l : ℕ) [NeZero l] (s : ℂ) :
    LSeriesSummable (hughesYoungMoebiusDivisorCoeff l) s := by
  unfold LSeriesSummable
  apply summable_of_hasFiniteSupport
  apply l.divisors.finite_toSet.subset
  intro d hd
  have hdTerm : LSeries.term (hughesYoungMoebiusDivisorCoeff l) s d ≠ 0 := hd
  have hd0 : d ≠ 0 := by
    intro hdZero
    subst d
    exact hdTerm (LSeries.term_zero _ _)
  have hdl : d ∣ l := by
    by_contra hnot
    rw [LSeries.term_of_ne_zero hd0,
      hughesYoungMoebiusDivisorCoeff_apply_of_not_dvd hnot,
      zero_div] at hdTerm
    exact hdTerm rfl
  exact Nat.mem_divisors.mpr ⟨hdl, NeZero.ne l⟩

/-- The finite Euler factor left after extracting the zeta function in
Hughes--Young equation (105). -/
noncomputable def hughesYoungMoebiusDivisorLSeriesFactor
    (l : ℕ) (c : ℂ) : ℂ :=
  ∑ d ∈ l.divisors,
    ((d : ℂ) * ArithmeticFunction.moebius (l / d)) / (d : ℂ) ^ c

/-- Evaluation of the finite Möbius-factor L-series. -/
theorem LSeries_hughesYoungMoebiusDivisorCoeff
    (l : ℕ) [NeZero l] (c : ℂ) :
    LSeries (hughesYoungMoebiusDivisorCoeff l) c =
      hughesYoungMoebiusDivisorLSeriesFactor l c := by
  unfold LSeries hughesYoungMoebiusDivisorLSeriesFactor
  rw [tsum_eq_sum (s := l.divisors)]
  · apply Finset.sum_congr rfl
    intro d hd
    have hdl : d ∣ l := (Nat.mem_divisors.mp hd).1
    have hd0 : d ≠ 0 := by
      intro hdZero
      subst d
      exact NeZero.ne l (zero_dvd_iff.mp hdl)
    rw [LSeries.term_of_ne_zero hd0]
    simp [hughesYoungMoebiusDivisorCoeff, hd0, hdl]
  · intro d hd
    by_cases hd0 : d = 0
    · subst d
      exact LSeries.term_zero _ _
    · have hnot : ¬d ∣ l := by
        intro hdl
        exact hd (Nat.mem_divisors.mpr ⟨hdl, NeZero.ne l⟩)
      rw [LSeries.term_of_ne_zero hd0,
        hughesYoungMoebiusDivisorCoeff_apply_of_not_dvd hnot,
        zero_div]

/-- The inner Ramanujan Dirichlet series in Hughes--Young equation (105),
before the divisor involution which produces the paper's displayed finite
Euler factor. -/
theorem hughesYoungRamanujanLSeries_eq_zeta_mul_divisorFactor
    (l : ℕ) [NeZero l] (c : ℂ) (hc : 1 < c.re) :
    LSeries (fun r : ℕ => ramanujanSum l r) c =
      riemannZeta c * hughesYoungMoebiusDivisorLSeriesFactor l c := by
  have hz : LSeriesSummable
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) c :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hc
  have hf : LSeriesSummable (hughesYoungMoebiusDivisorCoeff l) c :=
    hughesYoungMoebiusDivisorCoeff_LSeriesSummable l c
  calc
    LSeries (fun r : ℕ => ramanujanSum l r) c =
        LSeries (⇑((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
          hughesYoungMoebiusDivisorCoeff l)) c := by
      apply LSeries_congr
      intro r hr
      exact (coe_zeta_mul_hughesYoungMoebiusDivisorCoeff_apply
        l r (Nat.pos_of_ne_zero hr)).symm
    _ = LSeries (⇑(ArithmeticFunction.zeta : ArithmeticFunction ℂ)) c *
        LSeries (⇑(hughesYoungMoebiusDivisorCoeff l)) c :=
      ArithmeticFunction.LSeries_mul' hz hf
    _ = riemannZeta c *
        hughesYoungMoebiusDivisorLSeriesFactor l c := by
      have hzeta :
          LSeries (⇑(ArithmeticFunction.zeta : ArithmeticFunction ℂ)) c =
            riemannZeta c := by
        calc
          LSeries (⇑(ArithmeticFunction.zeta : ArithmeticFunction ℂ)) c =
              LSeries (fun n : ℕ =>
                (ArithmeticFunction.zeta n : ℂ)) c := by
            apply LSeries_congr
            intro n _hn
            rw [ArithmeticFunction.natCoe_apply]
          _ = riemannZeta c :=
            ArithmeticFunction.LSeries_zeta_eq_riemannZeta hc
      rw [hzeta, LSeries_hughesYoungMoebiusDivisorCoeff]

set_option maxHeartbeats 800000 in
/-- Shifted positive-index form of the preceding L-series identity.  This
is the inner `r`-sum occurring in Hughes--Young equation (105). -/
theorem tsum_ramanujanSum_div_cpow_eq_zeta_mul_divisorFactor
    (l : ℕ) [NeZero l] (c : ℂ) (hc : 1 < c.re) :
    (∑' r : ℕ, ramanujanSum l (r + 1) / ((r + 1 : ℕ) : ℂ) ^ c) =
      riemannZeta c * hughesYoungMoebiusDivisorLSeriesFactor l c := by
  have hz : LSeriesSummable
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) c :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hc
  have hf : LSeriesSummable (hughesYoungMoebiusDivisorCoeff l) c :=
    hughesYoungMoebiusDivisorCoeff_LSeriesSummable l c
  have hconv : LSeriesSummable
      (⇑((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        hughesYoungMoebiusDivisorCoeff l)) c :=
    ArithmeticFunction.LSeriesSummable_mul hz hf
  have hram : LSeriesSummable (fun r : ℕ => ramanujanSum l r) c :=
    (LSeriesSummable_congr c (fun {r} hr =>
      (coe_zeta_mul_hughesYoungMoebiusDivisorCoeff_apply
        l r (Nat.pos_of_ne_zero hr)).symm)).mpr hconv
  have hsplit := hram.sum_add_tsum_nat_add 1
  have hshift :
      (∑' r : ℕ, ramanujanSum l (r + 1) / ((r + 1 : ℕ) : ℂ) ^ c) =
        LSeries (fun r : ℕ => ramanujanSum l r) c := by
    unfold LSeries
    simpa [LSeries.term_of_ne_zero] using hsplit
  rw [hshift,
    hughesYoungRamanujanLSeries_eq_zeta_mul_divisorFactor l c hc]

/-- The finite factor in the precise form printed in Hughes--Young
equation (105). -/
noncomputable def hughesYoungEquation105FiniteFactor
    (l : ℕ) (c : ℂ) : ℂ :=
  (∑ d ∈ l.divisors,
      (d : ℂ) ^ c * ArithmeticFunction.moebius d) /
    (l : ℂ) ^ c

/-- Divisor involution written in the orientation needed below. -/
theorem sum_divisors_swap_factors
    (l : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ d ∈ l.divisors, F d (l / d)) =
      ∑ d ∈ l.divisors, F (l / d) d := by
  calc
    (∑ d ∈ l.divisors, F d (l / d)) =
        ∑ p ∈ l.divisorsAntidiagonal, F p.1 p.2 := by
      rw [Nat.sum_divisorsAntidiagonal]
    _ = ∑ d ∈ l.divisors, F (l / d) d := by
      rw [Nat.sum_divisorsAntidiagonal']

/-- The divisor involution and complex-power algebra converting the finite
factor extracted by convolution into the displayed factor in equation
(105). -/
theorem hughesYoungMoebiusDivisorLSeriesFactor_one_add
    (l : ℕ) [NeZero l] (c : ℂ) :
    hughesYoungMoebiusDivisorLSeriesFactor l (1 + c) =
      hughesYoungEquation105FiniteFactor l c := by
  unfold hughesYoungMoebiusDivisorLSeriesFactor
  unfold hughesYoungEquation105FiniteFactor
  calc
    (∑ d ∈ l.divisors,
        ((d : ℂ) * ArithmeticFunction.moebius (l / d)) /
          (d : ℂ) ^ (1 + c)) =
        ∑ d ∈ l.divisors,
          ((((l / d : ℕ) : ℂ) * ArithmeticFunction.moebius d) /
            (((l / d : ℕ) : ℂ) ^ (1 + c))) := by
      simpa using sum_divisors_swap_factors l
        (fun x y : ℕ =>
          ((x : ℂ) * ArithmeticFunction.moebius y) / (x : ℂ) ^ (1 + c))
    _ = ∑ d ∈ l.divisors,
        ((d : ℂ) ^ c * ArithmeticFunction.moebius d) /
          (l : ℂ) ^ c := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdl : d ∣ l := (Nat.mem_divisors.mp hd).1
      have hd0 : d ≠ 0 := by
        intro hdZero
        subst d
        exact NeZero.ne l (zero_dvd_iff.mp hdl)
      have hquot0 : l / d ≠ 0 := by
        intro hzero
        have hprod := Nat.div_mul_cancel hdl
        rw [hzero, zero_mul] at hprod
        exact NeZero.ne l hprod.symm
      have hquotC : (((l / d : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hquot0
      have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
      have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne l
      have hpow : (l : ℂ) ^ c =
          (((l / d : ℕ) : ℂ) ^ c) * (d : ℂ) ^ c := by
        calc
          (l : ℂ) ^ c = (((l / d) * d : ℕ) : ℂ) ^ c := by
            rw [Nat.div_mul_cancel hdl]
          _ = (((l / d : ℕ) : ℂ) ^ c) * (d : ℂ) ^ c := by
            simpa only [Nat.cast_mul] using
              Complex.natCast_mul_natCast_cpow (l / d) d c
      have hquotPow : (((l / d : ℕ) : ℂ) ^ c) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl hquotC)
      have hdPow : ((d : ℂ) ^ c) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl hdC)
      rw [Complex.cpow_add _ _ hquotC, Complex.cpow_one, hpow]
      field_simp [hquotPow, hdPow]
    _ = (∑ d ∈ l.divisors,
        (d : ℂ) ^ c * ArithmeticFunction.moebius d) /
          (l : ℂ) ^ c := by
      rw [Finset.sum_div]

/-- Hughes--Young equation (105) for the inner Ramanujan series, in the
paper's `1 + c` notation. -/
theorem hughesYoungEquation105_inner
    (l : ℕ) [NeZero l] (c : ℂ) (hc : 0 < c.re) :
    (∑' r : ℕ,
        ramanujanSum l (r + 1) /
          ((r + 1 : ℕ) : ℂ) ^ (1 + c)) =
      riemannZeta (1 + c) *
        hughesYoungEquation105FiniteFactor l c := by
  have hconv : 1 < (1 + c).re := by simpa using add_lt_add_left hc 1
  rw [tsum_ramanujanSum_div_cpow_eq_zeta_mul_divisorFactor
      l (1 + c) hconv,
    hughesYoungMoebiusDivisorLSeriesFactor_one_add]

/-- The individual summand in Hughes--Young equation (96), separated out so
that the absolute-convergence and Fubini step from (105) to (106) is visible
in the formal statement. -/
noncomputable def hughesYoungEquation96Term
    (h k : ℕ) (a b c : ℂ) (r l : ℕ) : ℂ :=
  ramanujanSum (l + 1) (r + 1) *
      ((Nat.gcd h (l + 1) : ℕ) : ℂ) ^ a *
      ((Nat.gcd k (l + 1) : ℕ) : ℂ) ^ b /
      (((l + 1 : ℕ) : ℂ) ^ (a + b) *
        ((r + 1 : ℕ) : ℂ) ^ c)

theorem hughesYoungEquation96_eq_tsum_term
    (h k : ℕ) (a b c : ℂ) :
    hughesYoungEquation96 h k a b c =
      ∑' r : ℕ, ∑' l : ℕ,
        hughesYoungEquation96Term h k a b c r l := by
  rfl

/-- The right side of Hughes--Young equation (106). -/
noncomputable def hughesYoungEquation106
    (h k : ℕ) (a b c : ℂ) : ℂ :=
  riemannZeta (1 + c) *
    ∑' l : ℕ,
      ((Nat.gcd h (l + 1) : ℕ) : ℂ) ^ a *
        ((Nat.gcd k (l + 1) : ℕ) : ℂ) ^ b *
        (∑ d ∈ (l + 1).divisors,
          ((d : ℕ) : ℂ) ^ c * ArithmeticFunction.moebius d) /
        (((l + 1 : ℕ) : ℂ) ^ (a + b + c))

set_option maxHeartbeats 1000000 in
/-- Equations (105)--(106) with the Fubini premise exposed.  The following
absolute-convergence theorem discharges this premise from exactly the
hypotheses of Hughes--Young Lemma 6.1. -/
theorem hughesYoungEquation105_106_of_summable
    (h k : ℕ) (a b c : ℂ) (hc : 0 < c.re)
    (hsum : Summable (fun p : ℕ × ℕ =>
      hughesYoungEquation96Term h k a b (1 + c) p.1 p.2)) :
    hughesYoungEquation96 h k a b (1 + c) =
      hughesYoungEquation106 h k a b c := by
  rw [hughesYoungEquation96_eq_tsum_term]
  calc
    (∑' r : ℕ, ∑' l : ℕ,
        hughesYoungEquation96Term h k a b (1 + c) r l) =
        ∑' l : ℕ, ∑' r : ℕ,
          hughesYoungEquation96Term h k a b (1 + c) r l := by
      have hcomm :
          (∑' l : ℕ, ∑' r : ℕ,
            hughesYoungEquation96Term h k a b (1 + c) r l) =
          ∑' r : ℕ, ∑' l : ℕ,
            hughesYoungEquation96Term h k a b (1 + c) r l :=
        Summable.tsum_comm hsum
      exact hcomm.symm
    _ = hughesYoungEquation106 h k a b c := by
      unfold hughesYoungEquation96Term hughesYoungEquation106
      simp_rw [div_eq_mul_inv, mul_assoc]
      have hinner : ∀ l : ℕ,
          (∑' r : ℕ,
            ramanujanSum (l + 1) (r + 1) *
              ((((r + 1 : ℕ) : ℂ) ^ (1 + c))⁻¹)) =
            riemannZeta (1 + c) *
              hughesYoungEquation105FiniteFactor (l + 1) c := by
        intro l
        letI : NeZero (l + 1) := ⟨Nat.succ_ne_zero l⟩
        simpa only [div_eq_mul_inv] using
          hughesYoungEquation105_inner (l + 1) c hc
      rw [← tsum_mul_left]
      apply tsum_congr
      intro l
      letI : NeZero (l + 1) := ⟨Nat.succ_ne_zero l⟩
      have hl0 : (((l + 1 : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero l
      have hpowa : (((l + 1 : ℕ) : ℂ) ^ (a + b)) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl hl0)
      have hpowc : (((l + 1 : ℕ) : ℂ) ^ c) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl hl0)
      let A : ℂ :=
        ((Nat.gcd h (l + 1) : ℕ) : ℂ) ^ a *
          ((Nat.gcd k (l + 1) : ℕ) : ℂ) ^ b *
          ((((l + 1 : ℕ) : ℂ) ^ (a + b))⁻¹)
      calc
        (∑' r : ℕ,
          ramanujanSum (l + 1) (r + 1) *
            (((Nat.gcd h (l + 1) : ℕ) : ℂ) ^ a *
              (((Nat.gcd k (l + 1) : ℕ) : ℂ) ^ b *
                ((((l + 1 : ℕ) : ℂ) ^ (a + b) *
                  ((r + 1 : ℕ) : ℂ) ^ (1 + c))⁻¹)))) =
            A * (∑' r : ℕ,
              ramanujanSum (l + 1) (r + 1) *
                ((((r + 1 : ℕ) : ℂ) ^ (1 + c))⁻¹)) := by
          calc
            _ = ∑' r : ℕ, A *
                (ramanujanSum (l + 1) (r + 1) *
                  ((((r + 1 : ℕ) : ℂ) ^ (1 + c))⁻¹)) := by
              apply tsum_congr
              intro r
              dsimp [A]
              rw [mul_inv]
              ring
            _ = _ := tsum_mul_left
        _ = A * (riemannZeta (1 + c) *
              hughesYoungEquation105FiniteFactor (l + 1) c) := by
          rw [hinner]
        _ = riemannZeta (1 + c) *
            (((Nat.gcd h (l + 1) : ℕ) : ℂ) ^ a *
              (((Nat.gcd k (l + 1) : ℕ) : ℂ) ^ b *
                ((∑ d ∈ (l + 1).divisors,
                    ((d : ℕ) : ℂ) ^ c * ArithmeticFunction.moebius d) *
                  ((((l + 1 : ℕ) : ℂ) ^ (a + b + c))⁻¹)))) := by
          unfold A hughesYoungEquation105FiniteFactor
          rw [Complex.cpow_add _ _ hl0]
          field_simp [hpowa, hpowc]
          rw [show a + b + c = (a + b) + c by ring]
          rw [Complex.cpow_add _ _ hl0, Complex.cpow_add _ _ hl0]
          ring

end RiemannZeta.GuthMaynard
