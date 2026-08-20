import RiemannZeta.GuthMaynard.HughesYoungEquation96Operators
import RiemannZeta.GuthMaynard.HughesYoungEquation96DFIBridge
import RiemannZeta.GuthMaynard.HughesYoungEquation98

open Complex Metric Set
open scoped BigOperators Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The two logarithmic jets of Hughes--Young equation (96)

The two logarithmic factors in DFI equation (27) must be applied to the
complete equation-(96) series before estimates are taken.  The bivariate
function below encodes both operators without separating the pole-cancelling
combination used later in the Hughes--Young contour argument.
-/

/-- Equation (96) reindexed by positive pairs throughout its full absolute-
convergence region.  The earlier one-one specialization is insufficient for
the two-variable deformation used below. -/
theorem hughesYoungEquation96_eq_positiveTsum
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    hughesYoungEquation96 h k a b (1 + c) =
      ∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k a b (1 + c) y := by
  let e : (ℕ × ℕ) ≃ (ℕ+ × ℕ+) :=
    (Equiv.prodCongr Equiv.pnatEquivNat.symm
      Equiv.pnatEquivNat.symm).trans (Equiv.prodComm _ _)
  rw [hughesYoungEquation96_eq_tsum_term]
  have hTerm : Summable (fun p : ℕ × ℕ =>
      hughesYoungEquation96Term h k a b (1 + c) p.1 p.2) :=
    summable_hughesYoungEquation96Term hh hk hA hC
  rw [← hTerm.tsum_prod]
  rw [← (e.tsum_eq
    (hughesYoungEquation96PositiveTerm h k a b (1 + c)))]
  apply tsum_congr
  intro p
  simp [e, Equiv.pnatEquivNat, Nat.succPNat_coe,
    Nat.succ_eq_add_one, hughesYoungEquation96PositiveTerm,
    hughesYoungEquation96Term]

noncomputable def hughesYoungEquation96LeftConstant (h : ℕ) : ℂ :=
  2 * Real.eulerMascheroniConstant - Complex.log (h : ℂ)

noncomputable def hughesYoungEquation96RightConstant (k : ℕ) : ℂ :=
  2 * Real.eulerMascheroniConstant - Complex.log (k : ℂ)

/-- The source-line equation-(96) summand after simultaneously exponentiating
the two DFI logarithmic operators. -/
noncomputable def hughesYoungEquation96JetTerm
    (h k : ℕ) (q z w : ℂ) (y : ℕ+ × ℕ+) : ℂ :=
  Complex.exp
      (z * hughesYoungEquation96LeftConstant h +
        w * hughesYoungEquation96RightConstant k) *
    hughesYoungEquation96PositiveTerm h k
      (1 + 2 * z) (1 + 2 * w) (2 + q - z - w) y

/-- The same jet written as the unshifted summand times the exponential of
the two exact DFI logarithmic factors. -/
theorem hughesYoungEquation96JetTerm_eq_base_mul_exp
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (q z w : ℂ) (y : ℕ+ × ℕ+) :
    hughesYoungEquation96JetTerm h k q z w y =
      hughesYoungEquation96PositiveTerm h k 1 1 (2 + q) y *
        Complex.exp
          (z * hughesYoungDFIPositiveLogFactorLeft h y +
            w * hughesYoungDFIPositiveLogFactorRight k y) := by
  have hgh : ((Nat.gcd h (y.1 : ℕ) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left (y.1 : ℕ) hh).ne'
  have hgk : ((Nat.gcd k (y.1 : ℕ) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left (y.1 : ℕ) hk).ne'
  have hl : (((y.1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast y.1.2.ne'
  have hr : (((y.2 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast y.2.2.ne'
  have exp_product_five_eq (r a b c d e f g i j l : ℂ)
      (hsum : a + b + c + d + e = f + g + i + j + l) :
      Complex.exp a * r * Complex.exp b * Complex.exp c * Complex.exp d *
          Complex.exp e =
        r * Complex.exp f * Complex.exp g * Complex.exp i * Complex.exp j *
          Complex.exp l := by
    calc
      Complex.exp a * r * Complex.exp b * Complex.exp c * Complex.exp d *
            Complex.exp e = r * Complex.exp (a + b + c + d + e) := by
              rw [Complex.exp_add (a + b + c + d) e,
                Complex.exp_add (a + b + c) d,
                Complex.exp_add (a + b) c, Complex.exp_add a b]
              ring
      _ = r * Complex.exp (f + g + i + j + l) := by rw [hsum]
      _ = r * Complex.exp f * Complex.exp g * Complex.exp i * Complex.exp j *
            Complex.exp l := by
              rw [Complex.exp_add (f + g + i + j) l,
                Complex.exp_add (f + g + i) j,
                Complex.exp_add (f + g) i, Complex.exp_add f g]
              ring
  unfold hughesYoungEquation96JetTerm
    hughesYoungEquation96PositiveTerm
    hughesYoungEquation96LeftConstant
    hughesYoungEquation96RightConstant
    hughesYoungDFIPositiveLogFactorLeft
    hughesYoungDFIPositiveLogFactorRight
    hughesYoungEquation96PositiveLogA
    hughesYoungEquation96PositiveLogB
    hughesYoungEquation96PositiveLogR
  rw [Complex.cpow_def_of_ne_zero hgh, Complex.cpow_def_of_ne_zero hgh,
    Complex.cpow_def_of_ne_zero hgk, Complex.cpow_def_of_ne_zero hgk,
    Complex.cpow_def_of_ne_zero hl, Complex.cpow_def_of_ne_zero hl,
    Complex.cpow_def_of_ne_zero hr, Complex.cpow_def_of_ne_zero hr]
  field_simp [Complex.exp_ne_zero]
  ring_nf
  apply exp_product_five_eq
  ring

/-- The complete bivariate equation-(96) jet. -/
noncomputable def hughesYoungEquation96Jet
    (h k : ℕ) (q z w : ℂ) : ℂ :=
  ∑' y : ℕ+ × ℕ+, hughesYoungEquation96JetTerm h k q z w y

/-- In the absolute-convergence bidisc, the complete jet is exactly the
elementary exponential prefactor times Hughes--Young equation (96). -/
theorem hughesYoungEquation96Jet_eq_exp_mul_equation96
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {q z w : ℂ}
    (hA : 1 < ((1 + 2 * z) + (1 + 2 * w)).re)
    (hC : 0 < (1 + q - z - w).re) :
    hughesYoungEquation96Jet h k q z w =
      Complex.exp
          (z * hughesYoungEquation96LeftConstant h +
            w * hughesYoungEquation96RightConstant k) *
        hughesYoungEquation96 h k
          (1 + 2 * z) (1 + 2 * w) (2 + q - z - w) := by
  rw [show (2 + q - z - w : ℂ) = 1 + (1 + q - z - w) by ring]
  rw [hughesYoungEquation96_eq_positiveTsum hh hk hA hC]
  unfold hughesYoungEquation96Jet hughesYoungEquation96JetTerm
  rw [tsum_mul_left]
  congr 1
  apply tsum_congr
  intro y
  congr 2
  ring

/-- Equation (98) on the exact two-variable deformation whose mixed jet is
the DFI equation-(27) logarithmic selector. -/
theorem hughesYoungEquation96Jet_eq_equation98
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : Nat.Coprime h k)
    {q z w : ℂ}
    (hA : 1 < ((1 + 2 * z) + (1 + 2 * w)).re)
    (hC : 0 < (1 + q - z - w).re)
    (hhx : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (z - w - 2 - q) ≠ 0)
    (hkx : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (w - z - 2 - q) ≠ 0) :
    hughesYoungEquation96Jet h k q z w =
      Complex.exp
          (z * hughesYoungEquation96LeftConstant h +
            w * hughesYoungEquation96RightConstant k) *
        ((riemannZeta (2 + q - z - w) * riemannZeta (3 + q + z + w) /
            riemannZeta (2 + 2 * z + 2 * w)) *
          (hughesYoungC h (-z) z (-w) w (1 + q / 2) *
            hughesYoungC k (-w) w (-z) z (1 + q / 2))) := by
  rw [hughesYoungEquation96Jet_eq_exp_mul_equation96 hh hk hA hC]
  have hAbsolute : 1 <
      (((1 : ℂ) - (-z) + z) + ((1 : ℂ) - (-w) + w)).re := by
    rw [show ((1 : ℂ) - (-z) + z) + ((1 : ℂ) - (-w) + w) =
        (1 + 2 * z) + (1 + 2 * w) by ring]
    exact hA
  have hShift : 0 < ((-z) + (-w) + 2 * (1 + q / 2) - 1).re := by
    rw [show (-z) + (-w) + 2 * (1 + q / 2) - 1 = 1 + q - z - w by ring]
    exact hC
  have hEq := hughesYoungEquation98 hh hk hhk
    (alpha := -z) (beta := z) (gamma := -w) (delta := w) (s := 1 + q / 2)
    hAbsolute hShift
    (by
      intro p hp
      convert hhx p hp using 1
      ring)
    (by
      intro p hp
      convert hkx p hp using 1
      ring)
  have hEq' :
      hughesYoungEquation96 h k
          (1 + 2 * z) (1 + 2 * w) (2 + q - z - w) =
        (riemannZeta (2 + q - z - w) * riemannZeta (3 + q + z + w) /
            riemannZeta (2 + 2 * z + 2 * w)) *
          (hughesYoungC h (-z) z (-w) w (1 + q / 2) *
            hughesYoungC k (-w) w (-z) z (1 + q / 2)) := by
    convert hEq using 1 <;> ring
  rw [hEq']

/-- A prime power with a strictly negative real exponent cannot equal one.
This discharges the finite Euler-factor regularity hypotheses in the small
Equation-(98) bidisc. -/
theorem one_sub_prime_cpow_ne_zero_of_re_neg
    (p : Nat.Primes) {s : ℂ} (hs : s.re < 0) :
    1 - (p : ℂ) ^ s ≠ 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.two_le
  have hpow : (p : ℝ) ^ s.re < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 hs
  intro hzero
  have heq : (p : ℂ) ^ s = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm := congrArg norm heq
  change ‖(((((p : ℕ) : ℝ) : ℂ)) ^ s)‖ = ‖(1 : ℂ)‖ at hnorm
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0, norm_one] at hnorm
  linarith

/-- Equation (98) for the jet with all finite Euler-factor regularity
conditions derived from explicit real-part inequalities. -/
theorem hughesYoungEquation96Jet_eq_equation98_of_re
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : Nat.Coprime h k)
    {q z w : ℂ}
    (hA : 1 < ((1 + 2 * z) + (1 + 2 * w)).re)
    (hC : 0 < (1 + q - z - w).re)
    (hhx : (z - w - 2 - q).re < 0)
    (hkx : (w - z - 2 - q).re < 0) :
    hughesYoungEquation96Jet h k q z w =
      Complex.exp
          (z * hughesYoungEquation96LeftConstant h +
            w * hughesYoungEquation96RightConstant k) *
        ((riemannZeta (2 + q - z - w) * riemannZeta (3 + q + z + w) /
            riemannZeta (2 + 2 * z + 2 * w)) *
          (hughesYoungC h (-z) z (-w) w (1 + q / 2) *
            hughesYoungC k (-w) w (-z) z (1 + q / 2))) := by
  exact hughesYoungEquation96Jet_eq_equation98 hh hk hhk hA hC
    (fun p _hp => one_sub_prime_cpow_ne_zero_of_re_neg p hhx)
    (fun p _hp => one_sub_prime_cpow_ne_zero_of_re_neg p hkx)

/-- Uniform Equation-(98) identity on a concrete closed neighborhood of the
origin.  The radius `1/8` stays strictly inside every convergence and finite
Euler-factor boundary used by the source formula. -/
theorem hughesYoungEquation96Jet_eq_equation98_of_norm_lt
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : Nat.Coprime h k)
    {q z w : ℂ} (hq : q.re = 0)
    (hz : ‖z‖ < 1 / 8) (hw : ‖w‖ < 1 / 8) :
    hughesYoungEquation96Jet h k q z w =
      Complex.exp
          (z * hughesYoungEquation96LeftConstant h +
            w * hughesYoungEquation96RightConstant k) *
        ((riemannZeta (2 + q - z - w) * riemannZeta (3 + q + z + w) /
            riemannZeta (2 + 2 * z + 2 * w)) *
          (hughesYoungC h (-z) z (-w) w (1 + q / 2) *
            hughesYoungC k (-w) w (-z) z (1 + q / 2))) := by
  have hz' := abs_lt.mp ((abs_re_le_norm z).trans_lt hz)
  have hw' := abs_lt.mp ((abs_re_le_norm w).trans_lt hw)
  apply hughesYoungEquation96Jet_eq_equation98_of_re hh hk hhk
  · norm_num [Complex.mul_re]
    linarith
  · norm_num [Complex.mul_re]
    rw [hq]
    linarith
  · norm_num [Complex.mul_re]
    rw [hq]
    linarith
  · norm_num [Complex.mul_re]
    rw [hq]
    linarith

theorem hasDerivAt_hughesYoungEquation96JetTerm_left
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (q z w : ℂ) (y : ℕ+ × ℕ+) :
    HasDerivAt (fun v => hughesYoungEquation96JetTerm h k q v w y)
      (hughesYoungEquation96JetTerm h k q z w y *
        hughesYoungDFIPositiveLogFactorLeft h y) z := by
  let A := hughesYoungEquation96PositiveTerm h k 1 1 (2 + q) y
  let L := hughesYoungDFIPositiveLogFactorLeft h y
  let R := hughesYoungDFIPositiveLogFactorRight k y
  have hfun : (fun v => hughesYoungEquation96JetTerm h k q v w y) =
      fun v => A * Complex.exp (v * L + w * R) := by
    funext v
    simpa only [A, L, R] using
      hughesYoungEquation96JetTerm_eq_base_mul_exp hh hk q v w y
  rw [hfun]
  have hlin : HasDerivAt (fun v : ℂ => v * L + w * R) L z := by
    convert ((hasDerivAt_id z).mul_const L).add_const (w * R) using 1
    ring
  have hexp : HasDerivAt (fun v : ℂ => Complex.exp (v * L + w * R))
      (Complex.exp (z * L + w * R) * L) z :=
    (Complex.hasDerivAt_exp _).comp z hlin
  have hmul := (hasDerivAt_const z A).mul hexp
  convert hmul using 1
  rw [hughesYoungEquation96JetTerm_eq_base_mul_exp hh hk]
  simp only [A, L, R, zero_mul, zero_add]
  ring

theorem hasDerivAt_hughesYoungEquation96JetTerm_right
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (q z w : ℂ) (y : ℕ+ × ℕ+) :
    HasDerivAt (fun v => hughesYoungEquation96JetTerm h k q z v y)
      (hughesYoungEquation96JetTerm h k q z w y *
        hughesYoungDFIPositiveLogFactorRight k y) w := by
  let A := hughesYoungEquation96PositiveTerm h k 1 1 (2 + q) y
  let L := hughesYoungDFIPositiveLogFactorLeft h y
  let R := hughesYoungDFIPositiveLogFactorRight k y
  have hfun : (fun v => hughesYoungEquation96JetTerm h k q z v y) =
      fun v => A * Complex.exp (z * L + v * R) := by
    funext v
    simpa only [A, L, R] using
      hughesYoungEquation96JetTerm_eq_base_mul_exp hh hk q z v y
  rw [hfun]
  have hlin : HasDerivAt (fun v : ℂ => z * L + v * R) R w := by
    convert (hasDerivAt_const w (z * L)).add
      ((hasDerivAt_id w).mul_const R) using 1
    ring
  have hexp : HasDerivAt (fun v : ℂ => Complex.exp (z * L + v * R))
      (Complex.exp (z * L + w * R) * R) w :=
    (Complex.hasDerivAt_exp _).comp w hlin
  have hmul := (hasDerivAt_const w A).mul hexp
  convert hmul using 1
  rw [hughesYoungEquation96JetTerm_eq_base_mul_exp hh hk]
  simp only [A, L, R, zero_mul, zero_add]
  ring

/-- Differentiating first in the left jet variable and then in the right
jet variable produces exactly the product of the two DFI logarithmic
selectors. -/
theorem hasDerivAt_hughesYoungEquation96JetTerm_mixed
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (q z w : ℂ) (y : ℕ+ × ℕ+) :
    HasDerivAt
      (fun v => hughesYoungEquation96JetTerm h k q z v y *
        hughesYoungDFIPositiveLogFactorLeft h y)
      (hughesYoungEquation96JetTerm h k q z w y *
        hughesYoungDFIPositiveLogFactorLeft h y *
        hughesYoungDFIPositiveLogFactorRight k y) w := by
  have hright := hasDerivAt_hughesYoungEquation96JetTerm_right hh hk q z w y
  convert hright.mul_const (hughesYoungDFIPositiveLogFactorLeft h y) using 1
  ring

/-- A single summable majorant for the vertical jet and either choice of
the two logarithmic selectors.  This is the Weierstrass estimate needed to
differentiate the complete equation-(96) series, rather than merely its
individual summands. -/
theorem norm_hughesYoungEquation96JetTerm_mul_logSelectors_le
    (i j : Bool) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {q z w : ℂ} (hq : q.re = 0)
    (hz : z ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ))
    (hw : w ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ))
    (y : ℕ+ × ℕ+) :
    ‖hughesYoungEquation96JetTerm h k q z w y *
        hughesYoungDFIPositiveLogSelectorLeft i h y *
        hughesYoungDFIPositiveLogSelectorRight j k y‖ ≤
      (Real.exp ((‖hughesYoungEquation96LeftConstant h‖ +
          ‖hughesYoungEquation96RightConstant k‖) / 32) *
        (hughesYoungGCDCPowBound h 2 * hughesYoungGCDCPowBound k 2) *
        (1 + 384 + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
        ((h : ℝ) ^ (1 / 64 : ℝ) * (k : ℝ) ^ (1 / 64 : ℝ))) *
        hughesYoungPositivePairMajorant (59 / 32) (29 / 32) y := by
  have hzNorm : ‖z‖ < (1 / 32 : ℝ) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hwNorm : ‖w‖ < (1 / 32 : ℝ) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hzRe : |z.re| < (1 / 32 : ℝ) :=
    (abs_re_le_norm z).trans_lt hzNorm
  have hwRe : |w.re| < (1 / 32 : ℝ) :=
    (abs_re_le_norm w).trans_lt hwNorm
  let a : ℂ := 1 + 2 * z
  let b : ℂ := 1 + 2 * w
  let c : ℂ := 1 + q - z - w
  let D : ℝ := 1 + 384 + 2 * |Real.eulerMascheroniConstant|
  let E : ℝ := Real.exp ((‖hughesYoungEquation96LeftConstant h‖ +
    ‖hughesYoungEquation96RightConstant k‖) / 32)
  let K : ℝ := E *
    (hughesYoungGCDCPowBound h 2 * hughesYoungGCDCPowBound k 2) * D ^ 2 *
    ((h : ℝ) ^ (1 / 64 : ℝ) * (k : ℝ) ^ (1 / 64 : ℝ))
  have haUpper : a.re ≤ 2 := by
    dsimp [a]
    norm_num [Complex.mul_re]
    linarith [le_abs_self z.re]
  have hbUpper : b.re ≤ 2 := by
    dsimp [b]
    norm_num [Complex.mul_re]
    linarith [le_abs_self w.re]
  have hA : (15 / 8 : ℝ) ≤ (a + b).re := by
    dsimp [a, b]
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hC : (15 / 16 : ℝ) ≤ c.re := by
    change (15 / 16 : ℝ) ≤ 1 + q.re - z.re - w.re
    rw [hq]
    linarith [le_abs_self z.re, le_abs_self w.re]
  have hterm :
      ‖hughesYoungEquation96PositiveTerm h k a b (1 + c) y‖ ≤
        (hughesYoungGCDCPowBound h 2 * hughesYoungGCDCPowBound k 2) *
          hughesYoungCommonDivisorMajorant (15 / 8) (15 / 16) y := by
    have hraw := norm_hughesYoungEquation96PositiveTerm_le hh hk a b c y
    have hha := hughesYoungGCDCPowBound_mono_re
      (h := h) (a := a) (b := (2 : ℂ)) haUpper
    have hkb := hughesYoungGCDCPowBound_mono_re
      (h := k) (a := b) (b := (2 : ℂ)) hbUpper
    have hmono := hughesYoungCommonDivisorMajorant_mono hA hC y
    have ha0 : 0 ≤ hughesYoungGCDCPowBound h a := by
      unfold hughesYoungGCDCPowBound
      positivity
    have hk0 : 0 ≤ hughesYoungGCDCPowBound k b := by
      unfold hughesYoungGCDCPowBound
      positivity
    have hh20 : 0 ≤ hughesYoungGCDCPowBound h (2 : ℂ) := by
      unfold hughesYoungGCDCPowBound
      positivity
    have hk20 : 0 ≤ hughesYoungGCDCPowBound k (2 : ℂ) := by
      unfold hughesYoungGCDCPowBound
      positivity
    have hm0 : 0 ≤ hughesYoungCommonDivisorMajorant (a + b).re c.re y := by
      unfold hughesYoungCommonDivisorMajorant
      positivity
    exact hraw.trans (mul_le_mul
      (mul_le_mul hha hkb hk0 hh20) hmono hm0 (mul_nonneg hh20 hk20))
  have hexp :
      ‖Complex.exp
          (z * hughesYoungEquation96LeftConstant h +
            w * hughesYoungEquation96RightConstant k)‖ ≤ E := by
    rw [Complex.norm_exp]
    change Real.exp
        (z * hughesYoungEquation96LeftConstant h +
          w * hughesYoungEquation96RightConstant k).re ≤
      Real.exp ((‖hughesYoungEquation96LeftConstant h‖ +
        ‖hughesYoungEquation96RightConstant k‖) / 32)
    apply Real.exp_le_exp.mpr
    calc
      (z * hughesYoungEquation96LeftConstant h +
          w * hughesYoungEquation96RightConstant k).re ≤
        ‖z * hughesYoungEquation96LeftConstant h +
          w * hughesYoungEquation96RightConstant k‖ := Complex.re_le_norm _
      _ ≤ ‖z‖ * ‖hughesYoungEquation96LeftConstant h‖ +
          ‖w‖ * ‖hughesYoungEquation96RightConstant k‖ := by
        simpa only [norm_mul] using norm_add_le
          (z * hughesYoungEquation96LeftConstant h)
          (w * hughesYoungEquation96RightConstant k)
      _ ≤ (1 / 32 : ℝ) * ‖hughesYoungEquation96LeftConstant h‖ +
          (1 / 32 : ℝ) * ‖hughesYoungEquation96RightConstant k‖ := by
        gcongr
      _ = (‖hughesYoungEquation96LeftConstant h‖ +
          ‖hughesYoungEquation96RightConstant k‖) / 32 := by ring
  have hleft := norm_hughesYoungDFIPositiveLogSelectorLeft_le i
    (show (0 : ℝ) < 1 / 64 by norm_num) hh y
  have hright := norm_hughesYoungDFIPositiveLogSelectorRight_le j
    (show (0 : ℝ) < 1 / 64 by norm_num) hk y
  norm_num at hleft hright
  have hleft' :
      ‖hughesYoungDFIPositiveLogSelectorLeft i h y‖ ≤
        (1 + 384 + 2 * |Real.eulerMascheroniConstant|) *
          (h : ℝ) ^ (1 / 64 : ℝ) * ((y.1 : ℕ) : ℝ) ^ (1 / 64 : ℝ) *
            ((y.2 : ℕ) : ℝ) ^ (1 / 64 : ℝ) := by
    norm_num at ⊢
    exact hleft
  have hright' :
      ‖hughesYoungDFIPositiveLogSelectorRight j k y‖ ≤
        (1 + 384 + 2 * |Real.eulerMascheroniConstant|) *
          (k : ℝ) ^ (1 / 64 : ℝ) * ((y.1 : ℕ) : ℝ) ^ (1 / 64 : ℝ) *
            ((y.2 : ℕ) : ℝ) ^ (1 / 64 : ℝ) := by
    norm_num at ⊢
    exact hright
  have hcommon0 :
      0 ≤ hughesYoungCommonDivisorMajorant (15 / 8) (15 / 16) y := by
    unfold hughesYoungCommonDivisorMajorant
    positivity
  have hh20 : 0 ≤ hughesYoungGCDCPowBound h (2 : ℂ) := by
    unfold hughesYoungGCDCPowBound
    positivity
  have hk20 : 0 ≤ hughesYoungGCDCPowBound k (2 : ℂ) := by
    unfold hughesYoungGCDCPowBound
    positivity
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  unfold hughesYoungEquation96JetTerm
  rw [show (2 + q - z - w : ℂ) = 1 + c by dsimp [c]; ring]
  rw [norm_mul, norm_mul, norm_mul]
  calc
    ‖Complex.exp
          (z * hughesYoungEquation96LeftConstant h +
            w * hughesYoungEquation96RightConstant k)‖ *
        ‖hughesYoungEquation96PositiveTerm h k a b (1 + c) y‖ *
        ‖hughesYoungDFIPositiveLogSelectorLeft i h y‖ *
        ‖hughesYoungDFIPositiveLogSelectorRight j k y‖ ≤
      E * ((hughesYoungGCDCPowBound h 2 *
          hughesYoungGCDCPowBound k 2) *
          hughesYoungCommonDivisorMajorant (15 / 8) (15 / 16) y) *
        (D * (h : ℝ) ^ (1 / 64 : ℝ) *
          ((y.1 : ℕ) : ℝ) ^ (1 / 64 : ℝ) *
          ((y.2 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) *
        (D * (k : ℝ) ^ (1 / 64 : ℝ) *
          ((y.1 : ℕ) : ℝ) ^ (1 / 64 : ℝ) *
          ((y.2 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) := by
        dsimp only [a, b, D] at hterm ⊢
        have hp0 : 0 ≤ hughesYoungGCDCPowBound h 2 *
            hughesYoungGCDCPowBound k 2 *
              hughesYoungCommonDivisorMajorant (15 / 8) (15 / 16) y := by
          positivity
        have hl0 : 0 ≤ (1 + 384 + 2 * |Real.eulerMascheroniConstant|) *
            (h : ℝ) ^ (1 / 64 : ℝ) * ((y.1 : ℕ) : ℝ) ^ (1 / 64 : ℝ) *
              ((y.2 : ℕ) : ℝ) ^ (1 / 64 : ℝ) := by positivity
        exact mul_le_mul
          (mul_le_mul (mul_le_mul hexp hterm (norm_nonneg _) hE0)
            hleft' (norm_nonneg _) (mul_nonneg hE0 hp0))
          hright' (norm_nonneg _)
          (mul_nonneg (mul_nonneg hE0 hp0) hl0)
    _ = K * (((((y.1 : ℕ) : ℝ) ^ (1 / 32 : ℝ)) *
          (((y.2 : ℕ) : ℝ) ^ (1 / 32 : ℝ))) *
          hughesYoungCommonDivisorMajorant (15 / 8) (15 / 16) y) := by
      have hl : 0 < (((y.1 : ℕ) : ℝ)) := by exact_mod_cast y.1.2
      have hr : 0 < (((y.2 : ℕ) : ℝ)) := by exact_mod_cast y.2.2
      rw [show (((y.1 : ℕ) : ℝ) ^ (1 / 32 : ℝ)) =
          (((y.1 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) *
            (((y.1 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) by
          rw [← Real.rpow_add hl]; congr 1; ring]
      rw [show (((y.2 : ℕ) : ℝ) ^ (1 / 32 : ℝ)) =
          (((y.2 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) *
            (((y.2 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) by
          rw [← Real.rpow_add hr]; congr 1; ring]
      dsimp only [K]
      ring
    _ = K * hughesYoungCommonDivisorMajorant (59 / 32) (29 / 32) y := by
      rw [mul_rpow_commonDivisorMajorant_eq]
      norm_num
    _ ≤ K * hughesYoungPositivePairMajorant (59 / 32) (29 / 32) y := by
      exact mul_le_mul_of_nonneg_left
        (hughesYoungCommonDivisorMajorant_le_pairMajorant
          (show (1 : ℝ) < 59 / 32 by norm_num)
          (show (0 : ℝ) < 29 / 32 by norm_num) y) hK0
    _ = _ := by rfl

theorem summable_hughesYoungEquation96JetTerm_mul_logSelectors_zero
    (i j : Bool) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {q : ℂ} (hq : q.re = 0) :
    Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation96JetTerm h k q 0 0 y *
        hughesYoungDFIPositiveLogSelectorLeft i h y *
        hughesYoungDFIPositiveLogSelectorRight j k y) := by
  let K : ℝ :=
    (Real.exp ((‖hughesYoungEquation96LeftConstant h‖ +
          ‖hughesYoungEquation96RightConstant k‖) / 32) *
        (hughesYoungGCDCPowBound h 2 * hughesYoungGCDCPowBound k 2) *
        (1 + 384 + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
        ((h : ℝ) ^ (1 / 64 : ℝ) * (k : ℝ) ^ (1 / 64 : ℝ)))
  have hm : Summable (fun y : ℕ+ × ℕ+ =>
      K * hughesYoungPositivePairMajorant (59 / 32) (29 / 32) y) :=
    (summable_hughesYoungPositivePairMajorant
      (show (1 : ℝ) < 59 / 32 by norm_num)
      (show (0 : ℝ) < 29 / 32 by norm_num)).mul_left K
  exact Summable.of_norm_bounded hm fun y => by
    simpa only [K] using
      norm_hughesYoungEquation96JetTerm_mul_logSelectors_le i j hh hk hq
        (by simp [Metric.mem_ball]) (by simp [Metric.mem_ball]) y

set_option maxHeartbeats 800000 in
/-- The complete vertical jet may be differentiated in its left variable at
the origin; its derivative is the complete left-logarithmic DFI series. -/
theorem hasDerivAt_hughesYoungEquation96Jet_left_zero
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {q : ℂ} (hq : q.re = 0) :
    HasDerivAt (fun z => hughesYoungEquation96Jet h k q z 0)
      (∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96JetTerm h k q 0 0 y *
          hughesYoungDFIPositiveLogFactorLeft h y) 0 := by
  let K : ℝ :=
    (Real.exp ((‖hughesYoungEquation96LeftConstant h‖ +
          ‖hughesYoungEquation96RightConstant k‖) / 32) *
        (hughesYoungGCDCPowBound h 2 * hughesYoungGCDCPowBound k 2) *
        (1 + 384 + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
        ((h : ℝ) ^ (1 / 64 : ℝ) * (k : ℝ) ^ (1 / 64 : ℝ)))
  let u : ℕ+ × ℕ+ → ℝ := fun y =>
    K * hughesYoungPositivePairMajorant (59 / 32) (29 / 32) y
  have hu : Summable u :=
    (summable_hughesYoungPositivePairMajorant
      (show (1 : ℝ) < 59 / 32 by norm_num)
      (show (0 : ℝ) < 29 / 32 by norm_num)).mul_left K
  have hpoint : Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation96JetTerm h k q 0 0 y) := by
    simpa only [hughesYoungDFIPositiveLogSelectorLeft,
      hughesYoungDFIPositiveLogSelectorRight, Bool.false_eq_true,
      ↓reduceIte, mul_one] using
      summable_hughesYoungEquation96JetTerm_mul_logSelectors_zero
        false false hh hk hq
  have hsum := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    Metric.isPreconnected_ball
    (fun y z _hz => hasDerivAt_hughesYoungEquation96JetTerm_left hh hk q z 0 y)
    (fun y z hz => by
      simpa [u, K, hughesYoungDFIPositiveLogSelectorLeft,
        hughesYoungDFIPositiveLogSelectorRight] using
        norm_hughesYoungEquation96JetTerm_mul_logSelectors_le
          true false hh hk hq hz
            (show (0 : ℂ) ∈ Metric.ball 0 (1 / 32 : ℝ) by
              simp [Metric.mem_ball]) y)
    (show (0 : ℂ) ∈ Metric.ball 0 (1 / 32 : ℝ) by
      simp [Metric.mem_ball]) hpoint
    (show (0 : ℂ) ∈ Metric.ball 0 (1 / 32 : ℝ) by
      simp [Metric.mem_ball])
  simpa only [hughesYoungEquation96Jet] using hsum

set_option maxHeartbeats 800000 in
/-- The analogous justified derivative in the right jet variable. -/
theorem hasDerivAt_hughesYoungEquation96Jet_right_zero
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {q : ℂ} (hq : q.re = 0) :
    HasDerivAt (fun w => hughesYoungEquation96Jet h k q 0 w)
      (∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96JetTerm h k q 0 0 y *
          hughesYoungDFIPositiveLogFactorRight k y) 0 := by
  let K : ℝ :=
    (Real.exp ((‖hughesYoungEquation96LeftConstant h‖ +
          ‖hughesYoungEquation96RightConstant k‖) / 32) *
        (hughesYoungGCDCPowBound h 2 * hughesYoungGCDCPowBound k 2) *
        (1 + 384 + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
        ((h : ℝ) ^ (1 / 64 : ℝ) * (k : ℝ) ^ (1 / 64 : ℝ)))
  let u : ℕ+ × ℕ+ → ℝ := fun y =>
    K * hughesYoungPositivePairMajorant (59 / 32) (29 / 32) y
  have hu : Summable u :=
    (summable_hughesYoungPositivePairMajorant
      (show (1 : ℝ) < 59 / 32 by norm_num)
      (show (0 : ℝ) < 29 / 32 by norm_num)).mul_left K
  have hpoint : Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation96JetTerm h k q 0 0 y) := by
    simpa only [hughesYoungDFIPositiveLogSelectorLeft,
      hughesYoungDFIPositiveLogSelectorRight, Bool.false_eq_true,
      ↓reduceIte, mul_one] using
      summable_hughesYoungEquation96JetTerm_mul_logSelectors_zero
        false false hh hk hq
  have hsum := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    Metric.isPreconnected_ball
    (fun y w _hw => hasDerivAt_hughesYoungEquation96JetTerm_right hh hk q 0 w y)
    (fun y w hw => by
      simpa [u, K, hughesYoungDFIPositiveLogSelectorLeft,
        hughesYoungDFIPositiveLogSelectorRight] using
        norm_hughesYoungEquation96JetTerm_mul_logSelectors_le
          false true hh hk hq
            (show (0 : ℂ) ∈ Metric.ball 0 (1 / 32 : ℝ) by
              simp [Metric.mem_ball]) hw y)
    (show (0 : ℂ) ∈ Metric.ball 0 (1 / 32 : ℝ) by
      simp [Metric.mem_ball]) hpoint
    (show (0 : ℂ) ∈ Metric.ball 0 (1 / 32 : ℝ) by
      simp [Metric.mem_ball])
  simpa only [hughesYoungEquation96Jet] using hsum

set_option maxHeartbeats 800000 in
/-- The second justified differentiation gives the exact mixed logarithmic
coefficient required by DFI equation (27). -/
theorem hasDerivAt_tsum_hughesYoungEquation96JetTerm_left_mixed_zero
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {q : ℂ} (hq : q.re = 0) :
    HasDerivAt
      (fun w => ∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96JetTerm h k q 0 w y *
          hughesYoungDFIPositiveLogFactorLeft h y)
      (∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96JetTerm h k q 0 0 y *
          hughesYoungDFIPositiveLogFactorLeft h y *
          hughesYoungDFIPositiveLogFactorRight k y) 0 := by
  let K : ℝ :=
    (Real.exp ((‖hughesYoungEquation96LeftConstant h‖ +
          ‖hughesYoungEquation96RightConstant k‖) / 32) *
        (hughesYoungGCDCPowBound h 2 * hughesYoungGCDCPowBound k 2) *
        (1 + 384 + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
        ((h : ℝ) ^ (1 / 64 : ℝ) * (k : ℝ) ^ (1 / 64 : ℝ)))
  let u : ℕ+ × ℕ+ → ℝ := fun y =>
    K * hughesYoungPositivePairMajorant (59 / 32) (29 / 32) y
  have hu : Summable u :=
    (summable_hughesYoungPositivePairMajorant
      (show (1 : ℝ) < 59 / 32 by norm_num)
      (show (0 : ℝ) < 29 / 32 by norm_num)).mul_left K
  have hpoint : Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation96JetTerm h k q 0 0 y *
        hughesYoungDFIPositiveLogFactorLeft h y) := by
    simpa [hughesYoungDFIPositiveLogSelectorLeft,
      hughesYoungDFIPositiveLogSelectorRight] using
      summable_hughesYoungEquation96JetTerm_mul_logSelectors_zero
        true false hh hk hq
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    Metric.isPreconnected_ball
    (fun y w _hw => hasDerivAt_hughesYoungEquation96JetTerm_mixed hh hk q 0 w y)
    (fun y w hw => by
      simpa [u, K, hughesYoungDFIPositiveLogSelectorLeft,
        hughesYoungDFIPositiveLogSelectorRight] using
        norm_hughesYoungEquation96JetTerm_mul_logSelectors_le
          true true hh hk hq
            (show (0 : ℂ) ∈ Metric.ball 0 (1 / 32 : ℝ) by
              simp [Metric.mem_ball]) hw y)
    (show (0 : ℂ) ∈ Metric.ball 0 (1 / 32 : ℝ) by
      simp [Metric.mem_ball]) hpoint
    (show (0 : ℂ) ∈ Metric.ball 0 (1 / 32 : ℝ) by
      simp [Metric.mem_ball])

@[simp]
theorem hughesYoungEquation96JetTerm_zero_zero
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (q : ℂ)
    (y : ℕ+ × ℕ+) :
    hughesYoungEquation96JetTerm h k q 0 0 y =
      hughesYoungEquation96PositiveTerm h k 1 1 (2 + q) y := by
  rw [hughesYoungEquation96JetTerm_eq_base_mul_exp hh hk]
  simp

/-- The mixed jet coefficient at the origin is literally the convergent
equation-(96) logarithmic-selector series used in the equation-(84) bridge. -/
theorem tsum_hughesYoungEquation96JetTerm_mixed_zero_zero
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (q : ℂ) :
    (∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96JetTerm h k q 0 0 y *
          hughesYoungDFIPositiveLogFactorLeft h y *
          hughesYoungDFIPositiveLogFactorRight k y) =
      ∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 1 (2 + q) y *
          hughesYoungDFIPositiveLogFactorLeft h y *
          hughesYoungDFIPositiveLogFactorRight k y := by
  apply tsum_congr
  intro y
  rw [hughesYoungEquation96JetTerm_zero_zero hh hk]

/-- The mixed vertical jet is the exact twice-logarithmic arithmetic moment
appearing in the complete equation-(84) source-line expansion. -/
theorem hughesYoungEquation84CompletePositiveMomentAt_true_true_eq_jet_mixed
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    (u : ℝ) :
    hughesYoungEquation84CompletePositiveMomentAt h k true true u =
      ∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96JetTerm h k ((2 * u : ℂ) * I) 0 0 y *
          hughesYoungDFIPositiveLogFactorLeft h y *
          hughesYoungDFIPositiveLogFactorRight k y := by
  rw [hughesYoungEquation84CompletePositiveMomentAt_eq_equation96
    true true u hhk]
  simp only [hughesYoungDFIPositiveLogSelectorLeft,
    hughesYoungDFIPositiveLogSelectorRight, if_true]
  rw [tsum_hughesYoungEquation96JetTerm_mixed_zero_zero hh hk]

/-- The four Taylor coefficients of the vertical jet, indexed in the same
order as the four equation-(84) arithmetic moments. -/
noncomputable def hughesYoungEquation96JetCoefficient
    (h k : ℕ) (q : ℂ) (i j : Bool) : ℂ :=
  ∑' y : ℕ+ × ℕ+,
    hughesYoungEquation96JetTerm h k q 0 0 y *
      hughesYoungDFIPositiveLogSelectorLeft j h y *
      hughesYoungDFIPositiveLogSelectorRight i k y

@[simp]
theorem hughesYoungEquation96JetCoefficient_false_false
    (h k : ℕ) (q : ℂ) :
    hughesYoungEquation96JetCoefficient h k q false false =
      hughesYoungEquation96Jet h k q 0 0 := by
  unfold hughesYoungEquation96JetCoefficient hughesYoungEquation96Jet
  simp [hughesYoungDFIPositiveLogSelectorLeft,
    hughesYoungDFIPositiveLogSelectorRight]

theorem hughesYoungEquation96JetCoefficient_false_true_eq_deriv
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {q : ℂ} (hq : q.re = 0) :
    hughesYoungEquation96JetCoefficient h k q false true =
      deriv (fun z => hughesYoungEquation96Jet h k q z 0) 0 := by
  have hd := (hasDerivAt_hughesYoungEquation96Jet_left_zero hh hk hq).deriv
  rw [hd]
  unfold hughesYoungEquation96JetCoefficient
  simp [hughesYoungDFIPositiveLogSelectorLeft,
    hughesYoungDFIPositiveLogSelectorRight]

theorem hughesYoungEquation96JetCoefficient_true_false_eq_deriv
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {q : ℂ} (hq : q.re = 0) :
    hughesYoungEquation96JetCoefficient h k q true false =
      deriv (fun w => hughesYoungEquation96Jet h k q 0 w) 0 := by
  have hd := (hasDerivAt_hughesYoungEquation96Jet_right_zero hh hk hq).deriv
  rw [hd]
  unfold hughesYoungEquation96JetCoefficient
  simp [hughesYoungDFIPositiveLogSelectorLeft,
    hughesYoungDFIPositiveLogSelectorRight]

theorem hughesYoungEquation96JetCoefficient_true_true_eq_deriv
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {q : ℂ} (hq : q.re = 0) :
    hughesYoungEquation96JetCoefficient h k q true true =
      deriv (fun w => ∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96JetTerm h k q 0 w y *
          hughesYoungDFIPositiveLogFactorLeft h y) 0 := by
  have hd :=
    (hasDerivAt_tsum_hughesYoungEquation96JetTerm_left_mixed_zero
      hh hk hq).deriv
  rw [hd]
  unfold hughesYoungEquation96JetCoefficient
  simp [hughesYoungDFIPositiveLogSelectorLeft,
    hughesYoungDFIPositiveLogSelectorRight]

/-- Every equation-(84) arithmetic moment is the matching coefficient of
the vertical Equation-(96) jet. -/
theorem hughesYoungEquation84CompletePositiveMomentAt_eq_jetCoefficient
    (i j : Bool) (u : ℝ) {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k) :
    hughesYoungEquation84CompletePositiveMomentAt h k i j u =
      hughesYoungEquation96JetCoefficient h k ((2 * u : ℂ) * I) i j := by
  rw [hughesYoungEquation84CompletePositiveMomentAt_eq_equation96 i j u hhk]
  unfold hughesYoungEquation96JetCoefficient
  apply tsum_congr
  intro y
  rw [hughesYoungEquation96JetTerm_zero_zero hh hk]

end RiemannZeta.GuthMaynard
