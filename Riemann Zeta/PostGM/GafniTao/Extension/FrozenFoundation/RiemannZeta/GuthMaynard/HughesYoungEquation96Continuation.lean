import RiemannZeta.GuthMaynard.HughesYoungEquation98Bounds

open Complex Filter Metric Set
open scoped BigOperators Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Analytic continuation of the complete Hughes--Young equation-(96) jet

The absolutely convergent equation-(96) series is available on the source
line `Re q = 0`.  Equation (98) supplies its continuation in the Mellin
variable.  The four coefficients below retain the two logarithmic operators
from DFI equation (27); they are not termwise continuations of the individual
shift summands.
-/

/-- The equation-(98) side of the complete two-variable jet, regarded as a
function of the continued Mellin variable `q`. -/
noncomputable def hughesYoungEquation96ContinuationJet
    (h k : ℕ) (q z w : ℂ) : ℂ :=
  Complex.exp
      (z * hughesYoungEquation96LeftConstant h +
        w * hughesYoungEquation96RightConstant k) *
    ((riemannZeta (2 + q - z - w) * riemannZeta (3 + q + z + w) /
        riemannZeta (2 + 2 * z + 2 * w)) *
      (hughesYoungC h (-z) z (-w) w (1 + q / 2) *
        hughesYoungC k (-w) w (-z) z (1 + q / 2)))

/-- Uniform control of the continued equation-(96) jet throughout the
closed strip needed to move the equation-(84) contour from `Re W = 1` to
`Re W = 7/8`.  The corresponding equation-(96) parameter satisfies
`Re q ≥ -1/4`; on the radius-`1/8` bidisc all three zeta arguments therefore
remain in `Re s ≥ 3/2`. -/
theorem norm_hughesYoungEquation96ContinuationJet_le_rpow
    {ε r : ℝ} (hε : 0 < ε) (hr0 : 0 ≤ r) (hr8 : r < 1 / 8)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {q z w : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re)
    (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖hughesYoungEquation96ContinuationJet h k q z w‖ ≤
      (Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
          hughesYoungZetaHalfPlaneMajorant ^ 3 *
          (divisorEpsilonConstant (ε / 5)) ^ 10) *
        ((h : ℝ) ^ (r + ε) * (k : ℝ) ^ (r + ε)) := by
  have hzRe : |z.re| ≤ r := (abs_re_le_norm z).trans hz
  have hwRe : |w.re| ≤ r := (abs_re_le_norm w).trans hw
  have hs1 : (3 / 2 : ℝ) ≤ (2 + q - z - w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [le_abs_self z.re, le_abs_self w.re]
  have hs2 : (3 / 2 : ℝ) ≤ (3 + q + z + w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hs3 : (3 / 2 : ℝ) ≤ (2 + 2 * z + 2 * w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hzeta1 := norm_riemannZeta_le_hughesYoungZetaHalfPlaneMajorant hs1
  have hzeta2 := norm_riemannZeta_le_hughesYoungZetaHalfPlaneMajorant hs2
  have hzeta3 := norm_riemannZeta_inv_le_hughesYoungZetaHalfPlaneMajorant hs3
  have hCh := norm_hughesYoungC_shiftedJet_le_const_mul_rpow
    hε hh hq (hz.trans (le_of_lt hr8)) (hw.trans (le_of_lt hr8))
  have hCk := norm_hughesYoungC_shiftedJet_le_const_mul_rpow
    hε hk hq (hw.trans (le_of_lt hr8)) (hz.trans (le_of_lt hr8))
  have hExp := norm_hughesYoungEquation96JetExponential_le hh hk hr0 hz hw
  unfold hughesYoungEquation96ContinuationJet
  rw [div_eq_mul_inv]
  simp only [norm_mul]
  have hZ0 : 0 ≤ hughesYoungZetaHalfPlaneMajorant := by
    unfold hughesYoungZetaHalfPlaneMajorant
    positivity
  have hD0 : 0 ≤ divisorEpsilonConstant (ε / 5) := by
    exact (divisorEpsilonConstant_pos _).le
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    ‖Complex.exp
          (z * hughesYoungEquation96LeftConstant h +
            w * hughesYoungEquation96RightConstant k)‖ *
        (‖riemannZeta (2 + q - z - w)‖ *
          ‖riemannZeta (3 + q + z + w)‖ *
          ‖(riemannZeta (2 + 2 * z + 2 * w))⁻¹‖ *
          (‖hughesYoungC h (-z) z (-w) w (1 + q / 2)‖ *
            ‖hughesYoungC k (-w) w (-z) z (1 + q / 2)‖)) ≤
      (Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
          (h : ℝ) ^ r * (k : ℝ) ^ r) *
        (hughesYoungZetaHalfPlaneMajorant *
          hughesYoungZetaHalfPlaneMajorant *
          hughesYoungZetaHalfPlaneMajorant *
          (((divisorEpsilonConstant (ε / 5)) ^ 5 * (h : ℝ) ^ ε) *
            ((divisorEpsilonConstant (ε / 5)) ^ 5 * (k : ℝ) ^ ε))) := by
        gcongr
    _ = (Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
          hughesYoungZetaHalfPlaneMajorant ^ 3 *
          (divisorEpsilonConstant (ε / 5)) ^ 10) *
        ((h : ℝ) ^ (r + ε) * (k : ℝ) ^ (r + ε)) := by
      rw [Real.rpow_add hhR, Real.rpow_add hkR]
      ring

private theorem differentiableAt_hughesYoungC_shiftedJet_left
    (h : ℕ) {q z w : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re)
    (hz : ‖z‖ < 1 / 8) (hw : ‖w‖ < 1 / 8) :
    DifferentiableAt ℂ
      (fun v => hughesYoungC h (-v) v (-w) w (1 + q / 2)) z := by
  have hzRe : |z.re| < (1 / 8 : ℝ) := (abs_re_le_norm z).trans_lt hz
  have hwRe : |w.re| < (1 / 8 : ℝ) := (abs_re_le_norm w).trans_lt hw
  unfold hughesYoungC
  apply DifferentiableAt.fun_finsetProd
  intro p hp
  have hp0 : ((p : Nat.Primes) : ℂ) ≠ 0 := by
    exact_mod_cast p.2.ne_zero
  have hpSlit : ((p : Nat.Primes) : ℂ) ∈ Complex.slitPlane := by
    exact Complex.natCast_mem_slitPlane.mpr p.2.ne_zero
  have hreg :
      1 - ((p : Nat.Primes) : ℂ) ^ (-2 - 2 * z - 2 * w) ≠ 0 := by
    apply one_sub_prime_cpow_ne_zero_of_re_neg p
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hx :
      1 - ((p : Nat.Primes) : ℂ) ^ (z - w - 2 - q) ≠ 0 := by
    apply one_sub_prime_cpow_ne_zero_of_re_neg p
    norm_num [Complex.mul_re]
    linarith [le_abs_self z.re, neg_abs_le w.re]
  have hden :
      (1 - (p : ℂ) ^ (-2 + -z - z + -w - w)) *
          (1 - (p : ℂ) ^ (- -z - w - 2 * (1 + q / 2))) ≠ 0 := by
    apply mul_ne_zero
    · convert hreg using 1
      ring_nf
    · convert hx using 1
      ring_nf
  unfold hughesYoungCPrimeFactor hughesYoungCPrimeNumerator
    hughesYoungC0 hughesYoungC1 hughesYoungC2
  dsimp only
  fun_prop (disch := first | exact hden | exact Or.inl hp0 | exact hpSlit)

private theorem differentiableAt_hughesYoungC_shiftedJet_right
    (h : ℕ) {q z w : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re)
    (hz : ‖z‖ < 1 / 8) (hw : ‖w‖ < 1 / 8) :
    DifferentiableAt ℂ
      (fun v => hughesYoungC h (-z) z (-v) v (1 + q / 2)) w := by
  have hzRe : |z.re| < (1 / 8 : ℝ) := (abs_re_le_norm z).trans_lt hz
  have hwRe : |w.re| < (1 / 8 : ℝ) := (abs_re_le_norm w).trans_lt hw
  unfold hughesYoungC
  apply DifferentiableAt.fun_finsetProd
  intro p hp
  have hp0 : ((p : Nat.Primes) : ℂ) ≠ 0 := by
    exact_mod_cast p.2.ne_zero
  have hpSlit : ((p : Nat.Primes) : ℂ) ∈ Complex.slitPlane := by
    exact Complex.natCast_mem_slitPlane.mpr p.2.ne_zero
  have hreg :
      1 - ((p : Nat.Primes) : ℂ) ^ (-2 - 2 * z - 2 * w) ≠ 0 := by
    apply one_sub_prime_cpow_ne_zero_of_re_neg p
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hx :
      1 - ((p : Nat.Primes) : ℂ) ^ (z - w - 2 - q) ≠ 0 := by
    apply one_sub_prime_cpow_ne_zero_of_re_neg p
    norm_num [Complex.mul_re]
    linarith [le_abs_self z.re, neg_abs_le w.re]
  have hden :
      (1 - (p : ℂ) ^ (-2 + -z - z + -w - w)) *
          (1 - (p : ℂ) ^ (- -z - w - 2 * (1 + q / 2))) ≠ 0 := by
    apply mul_ne_zero
    · convert hreg using 1
      ring_nf
    · convert hx using 1
      ring_nf
  unfold hughesYoungCPrimeFactor hughesYoungCPrimeNumerator
    hughesYoungC0 hughesYoungC1 hughesYoungC2
  dsimp only
  fun_prop (disch := first | exact hden | exact Or.inl hp0 | exact hpSlit)

private theorem differentiableAt_hughesYoungEquation96ContinuationJet_left
    {h k : ℕ} {q z w : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re)
    (hz : ‖z‖ < 1 / 8) (hw : ‖w‖ < 1 / 8) :
    DifferentiableAt ℂ
      (fun v => hughesYoungEquation96ContinuationJet h k q v w) z := by
  have hzRe : |z.re| < (1 / 8 : ℝ) := (abs_re_le_norm z).trans_lt hz
  have hwRe : |w.re| < (1 / 8 : ℝ) := (abs_re_le_norm w).trans_lt hw
  have hs1re : (3 / 2 : ℝ) < (2 + q - z - w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [le_abs_self z.re, le_abs_self w.re]
  have hs2re : (3 / 2 : ℝ) < (3 + q + z + w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hs3re : (3 / 2 : ℝ) < (2 + 2 * z + 2 * w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hs1 : 2 + q - z - w ≠ (1 : ℂ) := by
    intro heq
    rw [heq] at hs1re
    norm_num at hs1re
  have hs2 : 3 + q + z + w ≠ (1 : ℂ) := by
    intro heq
    rw [heq] at hs2re
    norm_num at hs2re
  have hs3 : 2 + 2 * z + 2 * w ≠ (1 : ℂ) := by
    intro heq
    rw [heq] at hs3re
    norm_num at hs3re
  have hz3 : riemannZeta (2 + 2 * z + 2 * w) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by linarith)
  have hExp : DifferentiableAt ℂ
      (fun v => Complex.exp
        (v * hughesYoungEquation96LeftConstant h +
          w * hughesYoungEquation96RightConstant k)) z := by
    fun_prop
  have hZ1 : DifferentiableAt ℂ
      (fun v => riemannZeta (2 + q - v - w)) z :=
    (differentiableAt_riemannZeta hs1).comp z (by fun_prop)
  have hZ2 : DifferentiableAt ℂ
      (fun v => riemannZeta (3 + q + v + w)) z :=
    (differentiableAt_riemannZeta hs2).comp z (by fun_prop)
  have hZ3 : DifferentiableAt ℂ
      (fun v => riemannZeta (2 + 2 * v + 2 * w)) z :=
    (differentiableAt_riemannZeta hs3).comp z (by fun_prop)
  have hCh := differentiableAt_hughesYoungC_shiftedJet_left
    h hq hz hw
  have hCk := differentiableAt_hughesYoungC_shiftedJet_right
    k (q := q) (z := w) (w := z) hq hw hz
  unfold hughesYoungEquation96ContinuationJet
  exact hExp.mul (((hZ1.mul hZ2).div hZ3 hz3).mul (hCh.mul hCk))

private theorem differentiableAt_hughesYoungEquation96ContinuationJet_right
    {h k : ℕ} {q z w : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re)
    (hz : ‖z‖ < 1 / 8) (hw : ‖w‖ < 1 / 8) :
    DifferentiableAt ℂ
      (fun v => hughesYoungEquation96ContinuationJet h k q z v) w := by
  have hzRe : |z.re| < (1 / 8 : ℝ) := (abs_re_le_norm z).trans_lt hz
  have hwRe : |w.re| < (1 / 8 : ℝ) := (abs_re_le_norm w).trans_lt hw
  have hs1re : (3 / 2 : ℝ) < (2 + q - z - w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [le_abs_self z.re, le_abs_self w.re]
  have hs2re : (3 / 2 : ℝ) < (3 + q + z + w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hs3re : (3 / 2 : ℝ) < (2 + 2 * z + 2 * w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hs1 : 2 + q - z - w ≠ (1 : ℂ) := by
    intro heq
    rw [heq] at hs1re
    norm_num at hs1re
  have hs2 : 3 + q + z + w ≠ (1 : ℂ) := by
    intro heq
    rw [heq] at hs2re
    norm_num at hs2re
  have hs3 : 2 + 2 * z + 2 * w ≠ (1 : ℂ) := by
    intro heq
    rw [heq] at hs3re
    norm_num at hs3re
  have hz3 : riemannZeta (2 + 2 * z + 2 * w) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by linarith)
  have hExp : DifferentiableAt ℂ
      (fun v => Complex.exp
        (z * hughesYoungEquation96LeftConstant h +
          v * hughesYoungEquation96RightConstant k)) w := by
    fun_prop
  have hZ1 : DifferentiableAt ℂ
      (fun v => riemannZeta (2 + q - z - v)) w :=
    (differentiableAt_riemannZeta hs1).comp w (by fun_prop)
  have hZ2 : DifferentiableAt ℂ
      (fun v => riemannZeta (3 + q + z + v)) w :=
    (differentiableAt_riemannZeta hs2).comp w (by fun_prop)
  have hZ3 : DifferentiableAt ℂ
      (fun v => riemannZeta (2 + 2 * z + 2 * v)) w :=
    (differentiableAt_riemannZeta hs3).comp w (by fun_prop)
  have hCh := differentiableAt_hughesYoungC_shiftedJet_right
    h (q := q) (z := z) (w := w) hq hz hw
  have hCk := differentiableAt_hughesYoungC_shiftedJet_left
    k (q := q) (z := w) (w := z) hq hw hz
  unfold hughesYoungEquation96ContinuationJet
  exact hExp.mul (((hZ1.mul hZ2).div hZ3 hz3).mul (hCh.mul hCk))

private theorem analyticAt_prod_fst (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun x : ℂ × ℂ => x.1) p :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt p

private theorem analyticAt_prod_snd (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun x : ℂ × ℂ => x.2) p :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt p

attribute [local fun_prop] analyticAt_prod_fst analyticAt_prod_snd

private theorem analyticAt_triple_fst (p : ℂ × (ℂ × ℂ)) :
    AnalyticAt ℂ (fun x : ℂ × (ℂ × ℂ) => x.1) p :=
  (ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)).analyticAt p

private theorem analyticAt_triple_snd_fst (p : ℂ × (ℂ × ℂ)) :
    AnalyticAt ℂ (fun x : ℂ × (ℂ × ℂ) => x.2.1) p :=
  ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt p.2).comp'
    (f := fun x : ℂ × (ℂ × ℂ) => x.2) (x := p)
    ((ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ)).analyticAt p)

private theorem analyticAt_triple_snd_snd (p : ℂ × (ℂ × ℂ)) :
    AnalyticAt ℂ (fun x : ℂ × (ℂ × ℂ) => x.2.2) p :=
  ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt p.2).comp'
    (f := fun x : ℂ × (ℂ × ℂ) => x.2) (x := p)
    ((ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ)).analyticAt p)

attribute [local fun_prop] analyticAt_triple_fst analyticAt_triple_snd_fst
  analyticAt_triple_snd_snd

private theorem analyticAt_hughesYoungC_shiftedJet_pair
    (h : ℕ) {q z w : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re)
    (hz : ‖z‖ < 1 / 8) (hw : ‖w‖ < 1 / 8) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ =>
        hughesYoungC h (-p.1) p.1 (-p.2) p.2 (1 + q / 2)) (z, w) := by
  have hzRe : |z.re| < (1 / 8 : ℝ) := (abs_re_le_norm z).trans_lt hz
  have hwRe : |w.re| < (1 / 8 : ℝ) := (abs_re_le_norm w).trans_lt hw
  let f : Nat.Primes → (ℂ × ℂ → ℂ) := fun p x =>
    hughesYoungCPrimeFactor (h.factorization p) p
      (-x.1) x.1 (-x.2) x.2 (1 + q / 2)
  unfold hughesYoungC
  suffices AnalyticAt ℂ (∏ p ∈ hughesYoungPrimeFactors h, f p) (z, w) by
    convert this using 1
    funext x
    simp [f]
  apply Finset.prod_induction f (fun g => AnalyticAt ℂ g (z, w))
    (fun _ _ hg₁ hg₂ => hg₁.mul hg₂) analyticAt_const
  intro p hp
  have hp0 : ((p : Nat.Primes) : ℂ) ≠ 0 := by
    exact_mod_cast p.2.ne_zero
  have hpSlit : ((p : Nat.Primes) : ℂ) ∈ Complex.slitPlane := by
    exact Complex.natCast_mem_slitPlane.mpr p.2.ne_zero
  have hreg :
      1 - ((p : Nat.Primes) : ℂ) ^ (-2 - 2 * z - 2 * w) ≠ 0 := by
    apply one_sub_prime_cpow_ne_zero_of_re_neg p
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hx :
      1 - ((p : Nat.Primes) : ℂ) ^ (z - w - 2 - q) ≠ 0 := by
    apply one_sub_prime_cpow_ne_zero_of_re_neg p
    norm_num [Complex.mul_re]
    linarith [le_abs_self z.re, neg_abs_le w.re]
  have hden :
      (1 - (p : ℂ) ^ (-2 + -z - z + -w - w)) *
          (1 - (p : ℂ) ^ (- -z - w - 2 * (1 + q / 2))) ≠ 0 := by
    apply mul_ne_zero
    · convert hreg using 1
      ring_nf
    · convert hx using 1
      ring_nf
  dsimp only [f]
  unfold hughesYoungCPrimeFactor hughesYoungCPrimeNumerator
    hughesYoungC0 hughesYoungC1 hughesYoungC2
  dsimp only
  fun_prop (disch := first | exact hden | exact Or.inl hp0 | exact hpSlit)

private theorem analyticAt_hughesYoungEquation96ContinuationJet_pair
    {h k : ℕ} {q z w : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re)
    (hz : ‖z‖ < 1 / 8) (hw : ‖w‖ < 1 / 8) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ =>
        hughesYoungEquation96ContinuationJet h k q p.1 p.2) (z, w) := by
  have hzRe : |z.re| < (1 / 8 : ℝ) := (abs_re_le_norm z).trans_lt hz
  have hwRe : |w.re| < (1 / 8 : ℝ) := (abs_re_le_norm w).trans_lt hw
  have hs1re : (3 / 2 : ℝ) < (2 + q - z - w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [le_abs_self z.re, le_abs_self w.re]
  have hs2re : (3 / 2 : ℝ) < (3 + q + z + w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hs3re : (3 / 2 : ℝ) < (2 + 2 * z + 2 * w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hs1 : 2 + q - z - w ≠ (1 : ℂ) := by
    intro heq
    rw [heq] at hs1re
    norm_num at hs1re
  have hs2 : 3 + q + z + w ≠ (1 : ℂ) := by
    intro heq
    rw [heq] at hs2re
    norm_num at hs2re
  have hs3 : 2 + 2 * z + 2 * w ≠ (1 : ℂ) := by
    intro heq
    rw [heq] at hs3re
    norm_num at hs3re
  have hz3 : riemannZeta (2 + 2 * z + 2 * w) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by linarith)
  have hExp : AnalyticAt ℂ
      (fun p : ℂ × ℂ => Complex.exp
        (p.1 * hughesYoungEquation96LeftConstant h +
          p.2 * hughesYoungEquation96RightConstant k)) (z, w) := by
    fun_prop
  have hZ1 : AnalyticAt ℂ
      (fun p : ℂ × ℂ => riemannZeta (2 + q - p.1 - p.2)) (z, w) :=
    (analyticAt_riemannZeta hs1).comp'
      (f := fun p : ℂ × ℂ => 2 + q - p.1 - p.2) (x := (z, w))
      (by fun_prop : AnalyticAt ℂ
        (fun p : ℂ × ℂ => 2 + q - p.1 - p.2) (z, w))
  have hZ2 : AnalyticAt ℂ
      (fun p : ℂ × ℂ => riemannZeta (3 + q + p.1 + p.2)) (z, w) :=
    (analyticAt_riemannZeta hs2).comp'
      (f := fun p : ℂ × ℂ => 3 + q + p.1 + p.2) (x := (z, w))
      (by fun_prop : AnalyticAt ℂ
        (fun p : ℂ × ℂ => 3 + q + p.1 + p.2) (z, w))
  have hZ3 : AnalyticAt ℂ
      (fun p : ℂ × ℂ => riemannZeta (2 + 2 * p.1 + 2 * p.2)) (z, w) :=
    (analyticAt_riemannZeta hs3).comp'
      (f := fun p : ℂ × ℂ => 2 + 2 * p.1 + 2 * p.2) (x := (z, w))
      (by fun_prop : AnalyticAt ℂ
        (fun p : ℂ × ℂ => 2 + 2 * p.1 + 2 * p.2) (z, w))
  have hCh := analyticAt_hughesYoungC_shiftedJet_pair h hq hz hw
  have hCkSwapped := analyticAt_hughesYoungC_shiftedJet_pair
    k (q := q) (z := w) (w := z) hq hw hz
  have hSwap : AnalyticAt ℂ
      (fun p : ℂ × ℂ => (p.2, p.1)) (z, w) := by
    fun_prop
  have hCk : AnalyticAt ℂ
      (fun p : ℂ × ℂ =>
        hughesYoungC k (-p.2) p.2 (-p.1) p.1 (1 + q / 2)) (z, w) :=
    hCkSwapped.comp'
      (f := fun p : ℂ × ℂ => (p.2, p.1)) (x := (z, w)) hSwap
  unfold hughesYoungEquation96ContinuationJet
  exact hExp.mul (((hZ1.mul hZ2).div hZ3 hz3).mul (hCh.mul hCk))

theorem analyticAt_hughesYoungC_shiftedJet_all
    (h : ℕ) {q z w : ℂ} (hq : -(7 / 4 : ℝ) < q.re)
    (hz : ‖z‖ < 1 / 8) (hw : ‖w‖ < 1 / 8) :
    AnalyticAt ℂ
      (fun p : ℂ × (ℂ × ℂ) =>
        hughesYoungC h (-p.2.1) p.2.1 (-p.2.2) p.2.2 (1 + p.1 / 2))
      (q, (z, w)) := by
  have hzRe : |z.re| < (1 / 8 : ℝ) := (abs_re_le_norm z).trans_lt hz
  have hwRe : |w.re| < (1 / 8 : ℝ) := (abs_re_le_norm w).trans_lt hw
  let f : Nat.Primes → (ℂ × (ℂ × ℂ) → ℂ) := fun p x =>
    hughesYoungCPrimeFactor (h.factorization p) p
      (-x.2.1) x.2.1 (-x.2.2) x.2.2 (1 + x.1 / 2)
  unfold hughesYoungC
  suffices AnalyticAt ℂ (∏ p ∈ hughesYoungPrimeFactors h, f p) (q, (z, w)) by
    convert this using 1
    funext x
    simp [f]
  apply Finset.prod_induction f (fun g => AnalyticAt ℂ g (q, (z, w)))
    (fun _ _ hg₁ hg₂ => hg₁.mul hg₂) analyticAt_const
  intro p hp
  have hp0 : ((p : Nat.Primes) : ℂ) ≠ 0 := by
    exact_mod_cast p.2.ne_zero
  have hpSlit : ((p : Nat.Primes) : ℂ) ∈ Complex.slitPlane := by
    exact Complex.natCast_mem_slitPlane.mpr p.2.ne_zero
  have hreg :
      1 - ((p : Nat.Primes) : ℂ) ^ (-2 - 2 * z - 2 * w) ≠ 0 := by
    apply one_sub_prime_cpow_ne_zero_of_re_neg p
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hx :
      1 - ((p : Nat.Primes) : ℂ) ^ (z - w - 2 - q) ≠ 0 := by
    apply one_sub_prime_cpow_ne_zero_of_re_neg p
    norm_num [Complex.mul_re]
    linarith [le_abs_self z.re, neg_abs_le w.re]
  have hden :
      (1 - (p : ℂ) ^ (-2 + -z - z + -w - w)) *
          (1 - (p : ℂ) ^ (- -z - w - 2 * (1 + q / 2))) ≠ 0 := by
    apply mul_ne_zero
    · convert hreg using 1
      ring_nf
    · convert hx using 1
      ring_nf
  dsimp only [f]
  unfold hughesYoungCPrimeFactor hughesYoungCPrimeNumerator
    hughesYoungC0 hughesYoungC1 hughesYoungC2
  dsimp only
  fun_prop (disch := first | exact hden | exact Or.inl hp0 | exact hpSlit)

theorem analyticAt_hughesYoungEquation96ContinuationJet_all
    {h k : ℕ} {q z w : ℂ} (hq : -(1 / 4 : ℝ) < q.re)
    (hz : ‖z‖ < 1 / 8) (hw : ‖w‖ < 1 / 8) :
    AnalyticAt ℂ
      (fun p : ℂ × (ℂ × ℂ) =>
        hughesYoungEquation96ContinuationJet h k p.1 p.2.1 p.2.2)
      (q, (z, w)) := by
  have hzRe : |z.re| < (1 / 8 : ℝ) := (abs_re_le_norm z).trans_lt hz
  have hwRe : |w.re| < (1 / 8 : ℝ) := (abs_re_le_norm w).trans_lt hw
  have hs1re : (3 / 2 : ℝ) < (2 + q - z - w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [le_abs_self z.re, le_abs_self w.re]
  have hs2re : (3 / 2 : ℝ) < (3 + q + z + w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hs3re : (3 / 2 : ℝ) < (2 + 2 * z + 2 * w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hs1 : 2 + q - z - w ≠ (1 : ℂ) := by
    intro heq
    rw [heq] at hs1re
    norm_num at hs1re
  have hs2 : 3 + q + z + w ≠ (1 : ℂ) := by
    intro heq
    rw [heq] at hs2re
    norm_num at hs2re
  have hs3 : 2 + 2 * z + 2 * w ≠ (1 : ℂ) := by
    intro heq
    rw [heq] at hs3re
    norm_num at hs3re
  have hz3 : riemannZeta (2 + 2 * z + 2 * w) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by linarith)
  have hqWide : -(7 / 4 : ℝ) < q.re := by linarith
  have hCh := analyticAt_hughesYoungC_shiftedJet_all h hqWide hz hw
  have hCkSwapped := analyticAt_hughesYoungC_shiftedJet_all
    k (q := q) (z := w) (w := z) hqWide hw hz
  have hSwap : AnalyticAt ℂ
      (fun p : ℂ × (ℂ × ℂ) => (p.1, (p.2.2, p.2.1)))
      (q, (z, w)) := by
    fun_prop
  have hCk : AnalyticAt ℂ
      (fun p : ℂ × (ℂ × ℂ) =>
        hughesYoungC k (-p.2.2) p.2.2 (-p.2.1) p.2.1 (1 + p.1 / 2))
      (q, (z, w)) :=
    hCkSwapped.comp' (f := fun p : ℂ × (ℂ × ℂ) =>
      (p.1, (p.2.2, p.2.1))) (x := (q, (z, w))) hSwap
  have hExp : AnalyticAt ℂ
      (fun p : ℂ × (ℂ × ℂ) => Complex.exp
        (p.2.1 * hughesYoungEquation96LeftConstant h +
          p.2.2 * hughesYoungEquation96RightConstant k)) (q, (z, w)) := by
    fun_prop
  have hZ1 : AnalyticAt ℂ
      (fun p : ℂ × (ℂ × ℂ) =>
        riemannZeta (2 + p.1 - p.2.1 - p.2.2)) (q, (z, w)) :=
    (analyticAt_riemannZeta hs1).comp'
      (f := fun p : ℂ × (ℂ × ℂ) =>
        2 + p.1 - p.2.1 - p.2.2) (x := (q, (z, w))) (by fun_prop)
  have hZ2 : AnalyticAt ℂ
      (fun p : ℂ × (ℂ × ℂ) =>
        riemannZeta (3 + p.1 + p.2.1 + p.2.2)) (q, (z, w)) :=
    (analyticAt_riemannZeta hs2).comp'
      (f := fun p : ℂ × (ℂ × ℂ) =>
        3 + p.1 + p.2.1 + p.2.2) (x := (q, (z, w))) (by fun_prop)
  have hZ3 : AnalyticAt ℂ
      (fun p : ℂ × (ℂ × ℂ) =>
        riemannZeta (2 + 2 * p.2.1 + 2 * p.2.2)) (q, (z, w)) :=
    (analyticAt_riemannZeta hs3).comp'
      (f := fun p : ℂ × (ℂ × ℂ) =>
        2 + 2 * p.2.1 + 2 * p.2.2) (x := (q, (z, w))) (by fun_prop)
  unfold hughesYoungEquation96ContinuationJet
  exact hExp.mul (((hZ1.mul hZ2).div hZ3 hz3).mul (hCh.mul hCk))

private theorem analyticAt_hughesYoungEquation96ContinuationJet_qDerivatives
    {h k : ℕ} {q : ℂ} (hq : -(1 / 4 : ℝ) < q.re) :
    AnalyticAt ℂ
      (fun p : ℂ × (ℂ × ℂ) =>
        (fderiv ℂ
          (fun x : ℂ × (ℂ × ℂ) =>
            fderiv ℂ
              (fun y : ℂ × (ℂ × ℂ) =>
                hughesYoungEquation96ContinuationJet h k y.1 y.2.1 y.2.2) x)
          p))
      (q, (0, 0)) := by
  exact (analyticAt_hughesYoungEquation96ContinuationJet_all hq
    (by norm_num) (by norm_num)).fderiv.fderiv

private theorem analyticAt_hughesYoungEquation96ContinuationJet_leftDeriv
    {h k : ℕ} {q w : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re)
    (hw : ‖w‖ < 1 / 8) :
    AnalyticAt ℂ
      (fun v => deriv
        (fun z => hughesYoungEquation96ContinuationJet h k q z v) 0) w := by
  let F : ℂ × ℂ → ℂ := fun p =>
    hughesYoungEquation96ContinuationJet h k q p.1 p.2
  have hF : AnalyticAt ℂ F (0, w) := by
    exact analyticAt_hughesYoungEquation96ContinuationJet_pair hq (by norm_num) hw
  have hEval : AnalyticAt ℂ
      (fun p : ℂ × ℂ => (fderiv ℂ F p) (1, 0)) (0, w) := by
    exact ((ContinuousLinearMap.apply ℂ ℂ ((1, 0) : ℂ × ℂ)).analyticAt _).comp'
      (f := fderiv ℂ F) (x := ((0, w) : ℂ × ℂ)) hF.fderiv
  have hRestricted : AnalyticAt ℂ
      (fun v : ℂ => (fderiv ℂ F (0, v)) (1, 0)) w :=
    hEval.curry_right
  apply hRestricted.congr
  filter_upwards [Metric.ball_mem_nhds w
      (sub_pos.mpr hw)] with v hv
  have hvNorm : ‖v‖ < 1 / 8 := by
    have hvDist : dist v w < 1 / 8 - ‖w‖ := by
      simpa [Metric.mem_ball] using hv
    calc
      ‖v‖ ≤ ‖v - w‖ + ‖w‖ := norm_le_norm_sub_add v w
      _ = dist v w + ‖w‖ := by rw [dist_eq_norm]
      _ < 1 / 8 := by linarith
  have hFv : AnalyticAt ℂ F (0, v) := by
    exact analyticAt_hughesYoungEquation96ContinuationJet_pair hq (by norm_num) hvNorm
  have hEmbed : HasDerivAt (fun z : ℂ => (z, v)) (1, 0) 0 :=
    (hasDerivAt_id (x := (0 : ℂ))).prodMk (hasDerivAt_const (x := (0 : ℂ)) v)
  have hPartial := hFv.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hEmbed
  exact hPartial.deriv.symm

/-- On the source line, the continued jet is exactly the absolutely
convergent equation-(96) jet. -/
theorem hughesYoungEquation96Jet_eq_continuationJet
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {q z w : ℂ} (hq : q.re = 0)
    (hz : ‖z‖ < 1 / 8) (hw : ‖w‖ < 1 / 8) :
    hughesYoungEquation96Jet h k q z w =
      hughesYoungEquation96ContinuationJet h k q z w := by
  exact hughesYoungEquation96Jet_eq_equation98_of_norm_lt
    hh hk hhk hq hz hw

/-- The four continued Taylor coefficients, ordered exactly as the four
equation-(84) arithmetic moments. -/
noncomputable def hughesYoungEquation96ContinuationCoefficient
    (h k : ℕ) (q : ℂ) (i j : Bool) : ℂ :=
  match i, j with
  | false, false => hughesYoungEquation96ContinuationJet h k q 0 0
  | false, true =>
      deriv (fun z => hughesYoungEquation96ContinuationJet h k q z 0) 0
  | true, false =>
      deriv (fun w => hughesYoungEquation96ContinuationJet h k q 0 w) 0
  | true, true =>
      deriv (fun w =>
        deriv (fun z => hughesYoungEquation96ContinuationJet h k q z w) 0) 0

/-- The four equation-(98) coefficients are holomorphic in the continued
Mellin parameter on the open half-plane used by the contour shift.  The
proof differentiates the jointly holomorphic three-variable jet, so the
mixed logarithmic coefficient is not treated as an independent formal
symbol. -/
theorem analyticAt_hughesYoungEquation96ContinuationCoefficient
    (h k : ℕ) (i j : Bool) {q : ℂ} (hq : -(1 / 4 : ℝ) < q.re) :
    AnalyticAt ℂ
      (fun v => hughesYoungEquation96ContinuationCoefficient h k v i j) q := by
  let F : ℂ × (ℂ × ℂ) → ℂ := fun p =>
    hughesYoungEquation96ContinuationJet h k p.1 p.2.1 p.2.2
  let eZ : ℂ × (ℂ × ℂ) := (0, (1, 0))
  let eW : ℂ × (ℂ × ℂ) := (0, (0, 1))
  let H : ℂ × (ℂ × ℂ) → ℂ := fun p =>
    (fderiv ℂ F p) eZ
  let K : ℂ × (ℂ × ℂ) → ℂ := fun p =>
    (fderiv ℂ H p) eW
  have hF : AnalyticAt ℂ F (q, (0, 0)) := by
    exact analyticAt_hughesYoungEquation96ContinuationJet_all hq
      (by norm_num) (by norm_num)
  have hH : AnalyticAt ℂ H (q, (0, 0)) := by
    exact ((ContinuousLinearMap.apply ℂ ℂ eZ).analyticAt _).comp'
      (f := fderiv ℂ F) (x := (q, (0, 0))) hF.fderiv
  have hK : AnalyticAt ℂ K (q, (0, 0)) := by
    exact ((ContinuousLinearMap.apply ℂ ℂ eW).analyticAt _).comp'
      (f := fderiv ℂ H) (x := (q, (0, 0))) hH.fderiv
  have hmargin : 0 < (q.re + 1 / 4) / 2 := by linarith
  have hqNear : ∀ᵉ v ∈ Metric.ball q ((q.re + 1 / 4) / 2),
      -(1 / 4 : ℝ) < v.re := by
    intro v hv
    have hvDist : dist v q < (q.re + 1 / 4) / 2 := by
      simpa [Metric.mem_ball] using hv
    have hre : |v.re - q.re| ≤ ‖v - q‖ := by
      simpa only [sub_re] using abs_re_le_norm (v - q)
    have hnorm : ‖v - q‖ = dist v q := by rw [dist_eq_norm]
    rw [hnorm] at hre
    linarith [neg_abs_le (v.re - q.re)]
  have left_eq (v w : ℂ) (hv : -(1 / 4 : ℝ) < v.re)
      (hw : ‖w‖ < 1 / 8) :
      deriv (fun z => F (v, (z, w))) 0 = H (v, (0, w)) := by
    have hFvw : AnalyticAt ℂ F (v, (0, w)) := by
      exact analyticAt_hughesYoungEquation96ContinuationJet_all hv
        (by norm_num) hw
    have hEmbed : HasDerivAt (fun z : ℂ => (v, (z, w))) eZ 0 := by
      dsimp only [eZ]
      convert (hasDerivAt_const (x := (0 : ℂ)) v).prodMk
        ((hasDerivAt_id (x := (0 : ℂ))).prodMk
          (hasDerivAt_const (x := (0 : ℂ)) w)) using 1
    exact (hFvw.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hEmbed).deriv
  have right_eq (v : ℂ) (hv : -(1 / 4 : ℝ) < v.re) :
      deriv (fun w => F (v, (0, w))) 0 =
        (fderiv ℂ F (v, (0, 0))) eW := by
    have hFv : AnalyticAt ℂ F (v, (0, 0)) := by
      exact analyticAt_hughesYoungEquation96ContinuationJet_all hv
        (by norm_num) (by norm_num)
    have hEmbed : HasDerivAt (fun w : ℂ => (v, (0, w))) eW 0 := by
      dsimp only [eW]
      convert (hasDerivAt_const (x := (0 : ℂ)) v).prodMk
        ((hasDerivAt_const (x := (0 : ℂ)) (0 : ℂ)).prodMk
          (hasDerivAt_id (x := (0 : ℂ)))) using 1
    exact (hFv.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hEmbed).deriv
  cases i <;> cases j
  · unfold hughesYoungEquation96ContinuationCoefficient
    exact hF.curry_left
  · have hRestricted : AnalyticAt ℂ (fun v => H (v, (0, 0))) q :=
      hH.curry_left
    apply hRestricted.congr
    filter_upwards [Metric.ball_mem_nhds q hmargin] with v hv
    unfold hughesYoungEquation96ContinuationCoefficient
    exact (left_eq v 0 (hqNear v hv) (by norm_num)).symm
  · have hRight : AnalyticAt ℂ
        (fun p : ℂ × (ℂ × ℂ) => (fderiv ℂ F p) eW)
        (q, (0, 0)) := by
      exact ((ContinuousLinearMap.apply ℂ ℂ eW).analyticAt _).comp'
        (f := fderiv ℂ F) (x := (q, (0, 0))) hF.fderiv
    have hRestricted : AnalyticAt ℂ
        (fun v => (fderiv ℂ F (v, (0, 0))) eW) q := hRight.curry_left
    apply hRestricted.congr
    filter_upwards [Metric.ball_mem_nhds q hmargin] with v hv
    unfold hughesYoungEquation96ContinuationCoefficient
    exact (right_eq v (hqNear v hv)).symm
  · have hRestricted : AnalyticAt ℂ (fun v => K (v, (0, 0))) q :=
      hK.curry_left
    apply hRestricted.congr
    filter_upwards [Metric.ball_mem_nhds q hmargin] with v hv
    have hvq := hqNear v hv
    have hInner : Filter.EventuallyEq (nhds (0 : ℂ))
        (fun w => deriv (fun z => F (v, (z, w))) 0)
        (fun w => H (v, (0, w))) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
          (by norm_num : (0 : ℝ) < 1 / 8)] with w hw
      exact left_eq v w hvq (by
        simpa [Metric.mem_ball, dist_zero_right] using hw)
    have hHv : AnalyticAt ℂ H (v, (0, 0)) := by
      have hFv : AnalyticAt ℂ F (v, (0, 0)) := by
        exact analyticAt_hughesYoungEquation96ContinuationJet_all hvq
          (by norm_num) (by norm_num)
      exact ((ContinuousLinearMap.apply ℂ ℂ eZ).analyticAt _).comp'
        (f := fderiv ℂ F) (x := (v, (0, 0))) hFv.fderiv
    have hEmbed : HasDerivAt (fun w : ℂ => (v, (0, w))) eW 0 := by
      dsimp only [eW]
      convert (hasDerivAt_const (x := (0 : ℂ)) v).prodMk
        ((hasDerivAt_const (x := (0 : ℂ)) (0 : ℂ)).prodMk
          (hasDerivAt_id (x := (0 : ℂ)))) using 1
    have hOuter : deriv (fun w => H (v, (0, w))) 0 = K (v, (0, 0)) := by
      exact (hHv.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hEmbed).deriv
    unfold hughesYoungEquation96ContinuationCoefficient
    rw [hInner.deriv_eq]
    exact hOuter.symm

theorem diffContOnCl_hughesYoungEquation96ContinuationJet_left
    {r : ℝ} (hr8 : r < 1 / 8) {h k : ℕ}
    {q w : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re) (
      hw : ‖w‖ ≤ r) :
    DiffContOnCl ℂ
      (fun z => hughesYoungEquation96ContinuationJet h k q z w)
      (Metric.ball (0 : ℂ) r) := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  have hzClosed : z ∈ Metric.closedBall (0 : ℂ) r :=
    closure_ball_subset_closedBall hz
  have hzNorm : ‖z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hzClosed
  exact (analyticAt_hughesYoungEquation96ContinuationJet_pair hq
    (hzNorm.trans_lt hr8) (hw.trans_lt hr8)).curry_left.differentiableAt.differentiableWithinAt

theorem diffContOnCl_hughesYoungEquation96ContinuationJet_right
    {r : ℝ} (hr8 : r < 1 / 8) {h k : ℕ}
    {q z : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re) (
      hz : ‖z‖ ≤ r) :
    DiffContOnCl ℂ
      (fun w => hughesYoungEquation96ContinuationJet h k q z w)
      (Metric.ball (0 : ℂ) r) := by
  apply DifferentiableOn.diffContOnCl
  intro w hw
  have hwClosed : w ∈ Metric.closedBall (0 : ℂ) r :=
    closure_ball_subset_closedBall hw
  have hwNorm : ‖w‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hwClosed
  exact (analyticAt_hughesYoungEquation96ContinuationJet_pair hq
    (hz.trans_lt hr8) (hwNorm.trans_lt hr8)).curry_right.differentiableAt.differentiableWithinAt

theorem diffContOnCl_hughesYoungEquation96ContinuationJet_leftDeriv
    {r : ℝ} (hr8 : r < 1 / 8) {h k : ℕ}
    {q : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re) :
    DiffContOnCl ℂ
      (fun w => deriv
        (fun z => hughesYoungEquation96ContinuationJet h k q z w) 0)
      (Metric.ball (0 : ℂ) r) := by
  apply DifferentiableOn.diffContOnCl
  intro w hw
  have hwClosed : w ∈ Metric.closedBall (0 : ℂ) r :=
    closure_ball_subset_closedBall hw
  have hwNorm : ‖w‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hwClosed
  exact (analyticAt_hughesYoungEquation96ContinuationJet_leftDeriv hq
    (hwNorm.trans_lt hr8)).differentiableAt.differentiableWithinAt

/-- Cauchy's inequalities applied after equation-(98) continuation.  This is
the coefficient estimate used on the shifted equation-(84) contour. -/
theorem norm_hughesYoungEquation96ContinuationCoefficient_le_rpow
    (i j : Bool) {ε r : ℝ} (hε : 0 < ε) (hr0 : 0 < r)
    (hr8 : r < 1 / 8) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {q : ℂ} (hq : -(1 / 4 : ℝ) ≤ q.re) :
    ‖hughesYoungEquation96ContinuationCoefficient h k q i j‖ ≤
      ((Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
          hughesYoungZetaHalfPlaneMajorant ^ 3 *
          (divisorEpsilonConstant (ε / 5)) ^ 10) *
        ((h : ℝ) ^ (r + ε) * (k : ℝ) ^ (r + ε))) / r ^ 2 := by
  let B : ℝ :=
    (Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
        hughesYoungZetaHalfPlaneMajorant ^ 3 *
        (divisorEpsilonConstant (ε / 5)) ^ 10) *
      ((h : ℝ) ^ (r + ε) * (k : ℝ) ^ (r + ε))
  have hB0 : 0 ≤ B := by
    have hZ0 : 0 ≤ hughesYoungZetaHalfPlaneMajorant := by
      unfold hughesYoungZetaHalfPlaneMajorant
      positivity
    have hD0 : 0 ≤ divisorEpsilonConstant (ε / 5) :=
      (divisorEpsilonConstant_pos _).le
    dsimp only [B]
    positivity
  have hr1 : r ≤ 1 := (le_of_lt hr8).trans (by norm_num)
  have hrsq_le_r : r ^ 2 ≤ r := by nlinarith
  have hrsq_le_one : r ^ 2 ≤ 1 := hrsq_le_r.trans hr1
  have hJet (z w : ℂ) (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
      ‖hughesYoungEquation96ContinuationJet h k q z w‖ ≤ B := by
    simpa only [B] using norm_hughesYoungEquation96ContinuationJet_le_rpow
      hε hr0.le hr8 hh hk hq hz hw
  have hzero : ‖(0 : ℂ)‖ ≤ r := by simp [hr0.le]
  cases i <;> cases j
  · unfold hughesYoungEquation96ContinuationCoefficient
    exact (hJet 0 0 hzero hzero).trans (by
      apply (le_div_iff₀ (sq_pos_of_pos hr0)).2
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hrsq_le_one hB0)
  · unfold hughesYoungEquation96ContinuationCoefficient
    have hCauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hr0
      (diffContOnCl_hughesYoungEquation96ContinuationJet_left hr8 hq hzero)
      (fun z hz => hJet z 0 (by
        simpa [Metric.mem_sphere, dist_zero_right] using hz.le) hzero)
    exact hCauchy.trans (by
      change B / r ≤ B / r ^ 2
      exact div_le_div_of_nonneg_left hB0 (sq_pos_of_pos hr0) hrsq_le_r)
  · unfold hughesYoungEquation96ContinuationCoefficient
    have hCauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hr0
      (diffContOnCl_hughesYoungEquation96ContinuationJet_right hr8 hq hzero)
      (fun w hw => hJet 0 w hzero (by
        simpa [Metric.mem_sphere, dist_zero_right] using hw.le))
    exact hCauchy.trans (by
      change B / r ≤ B / r ^ 2
      exact div_le_div_of_nonneg_left hB0 (sq_pos_of_pos hr0) hrsq_le_r)
  · unfold hughesYoungEquation96ContinuationCoefficient
    let g : ℂ → ℂ := fun w => deriv
      (fun z => hughesYoungEquation96ContinuationJet h k q z w) 0
    have hgBound (w : ℂ) (hw : w ∈ Metric.sphere (0 : ℂ) r) :
        ‖g w‖ ≤ B / r := by
      have hwNorm : ‖w‖ ≤ r := by
        simpa [Metric.mem_sphere, dist_zero_right] using hw.le
      exact norm_deriv_le_of_forall_mem_sphere_norm_le hr0
        (diffContOnCl_hughesYoungEquation96ContinuationJet_left
          hr8 hq hwNorm)
        (fun z hz => hJet z w (by
          simpa [Metric.mem_sphere, dist_zero_right] using hz.le) hwNorm)
    have hCauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hr0
      (diffContOnCl_hughesYoungEquation96ContinuationJet_leftDeriv
        hr8 hq) hgBound
    simpa only [g, div_div, pow_two] using hCauchy

/-- Uniform epsilon-power control of all four continued arithmetic
coefficients on the full contour-shift strip `Re q ≥ -1/4`. -/
theorem exists_uniform_norm_hughesYoungEquation96ContinuationCoefficient_le
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i j : Bool) {h k : ℕ},
      0 < h → 0 < k → ∀ {q : ℂ}, -(1 / 4 : ℝ) ≤ q.re →
      ‖hughesYoungEquation96ContinuationCoefficient h k q i j‖ ≤
        C * (h : ℝ) ^ δ * (k : ℝ) ^ δ := by
  let r : ℝ := min (δ / 4) (1 / 64)
  let η : ℝ := δ / 2
  let A : ℝ :=
    (Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
        hughesYoungZetaHalfPlaneMajorant ^ 3 *
        (divisorEpsilonConstant (η / 5)) ^ 10) / r ^ 2
  let C : ℝ := A + 1
  have hr0 : 0 < r := lt_min (div_pos hδ (by norm_num)) (by norm_num)
  have hr8 : r < 1 / 8 :=
    (min_le_right (δ / 4) (1 / 64)).trans_lt (by norm_num)
  have hη : 0 < η := div_pos hδ (by norm_num)
  have hrexp : r + η ≤ δ := by
    dsimp only [r, η]
    have hrδ : min (δ / 4) (1 / 64) ≤ δ / 4 := min_le_left _ _
    linarith
  have hA0 : 0 ≤ A := by
    have hZ0 : 0 ≤ hughesYoungZetaHalfPlaneMajorant := by
      unfold hughesYoungZetaHalfPlaneMajorant
      positivity
    have hD0 : 0 ≤ divisorEpsilonConstant (η / 5) :=
      (divisorEpsilonConstant_pos _).le
    dsimp only [A]
    positivity
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro i j h k hh hk q hq
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hhpow : (h : ℝ) ^ (r + η) ≤ (h : ℝ) ^ δ :=
    Real.rpow_le_rpow_of_exponent_le hh1 hrexp
  have hkpow : (k : ℝ) ^ (r + η) ≤ (k : ℝ) ^ δ :=
    Real.rpow_le_rpow_of_exponent_le hk1 hrexp
  calc
    ‖hughesYoungEquation96ContinuationCoefficient h k q i j‖ ≤
        ((Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
            hughesYoungZetaHalfPlaneMajorant ^ 3 *
            (divisorEpsilonConstant (η / 5)) ^ 10) *
          ((h : ℝ) ^ (r + η) * (k : ℝ) ^ (r + η))) / r ^ 2 :=
      norm_hughesYoungEquation96ContinuationCoefficient_le_rpow
        i j hη hr0 hr8 hh hk hq
    _ = A * (h : ℝ) ^ (r + η) * (k : ℝ) ^ (r + η) := by
      dsimp only [A]
      field_simp
    _ ≤ C * (h : ℝ) ^ δ * (k : ℝ) ^ δ := by
      have hAC : A ≤ C := by dsimp only [C]; linarith
      gcongr

private theorem eventuallyEq_jet_continuation_left
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {q w : ℂ} (hq : q.re = 0) (hw : ‖w‖ < 1 / 8) :
    (fun z => hughesYoungEquation96Jet h k q z w) =ᶠ[𝓝 0]
      fun z => hughesYoungEquation96ContinuationJet h k q z w := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
      (by norm_num : (0 : ℝ) < 1 / 8)] with z hz
  exact hughesYoungEquation96Jet_eq_continuationJet hh hk hhk hq
    (by simpa [Metric.mem_ball, dist_zero_right] using hz) hw

private theorem eventuallyEq_jet_continuation_right
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {q z : ℂ} (hq : q.re = 0) (hz : ‖z‖ < 1 / 8) :
    (fun w => hughesYoungEquation96Jet h k q z w) =ᶠ[𝓝 0]
      fun w => hughesYoungEquation96ContinuationJet h k q z w := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
      (by norm_num : (0 : ℝ) < 1 / 8)] with w hw
  exact hughesYoungEquation96Jet_eq_continuationJet hh hk hhk hq hz
    (by simpa [Metric.mem_ball, dist_zero_right] using hw)

/-- The continued coefficients specialize exactly to the four complete DFI
arithmetic moments on `Re q = 0`. -/
theorem hughesYoungEquation96JetCoefficient_eq_continuationCoefficient
    (i j : Bool) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hhk : h.Coprime k) {q : ℂ} (hq : q.re = 0) :
    hughesYoungEquation96JetCoefficient h k q i j =
      hughesYoungEquation96ContinuationCoefficient h k q i j := by
  cases i <;> cases j
  · rw [hughesYoungEquation96JetCoefficient_false_false]
    exact hughesYoungEquation96Jet_eq_continuationJet hh hk hhk hq
      (by norm_num) (by norm_num)
  · rw [hughesYoungEquation96JetCoefficient_false_true_eq_deriv hh hk hq]
    unfold hughesYoungEquation96ContinuationCoefficient
    exact Filter.EventuallyEq.deriv_eq
      (eventuallyEq_jet_continuation_left hh hk hhk hq (by norm_num))
  · rw [hughesYoungEquation96JetCoefficient_true_false_eq_deriv hh hk hq]
    unfold hughesYoungEquation96ContinuationCoefficient
    exact Filter.EventuallyEq.deriv_eq
      (eventuallyEq_jet_continuation_right hh hk hhk hq (by norm_num))
  · rw [hughesYoungEquation96JetCoefficient_true_true_eq_deriv hh hk hq]
    unfold hughesYoungEquation96ContinuationCoefficient
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
        (by norm_num : (0 : ℝ) < 1 / 32)] with w hw
    have hw32 : w ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ) := hw
    have hzero32 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (1 / 32 : ℝ) := by
      simp [Metric.mem_ball]
    rw [← (hasDerivAt_hughesYoungEquation96Jet_left_of_mem_ball
      hh hk hq hzero32 hw32).deriv]
    apply Filter.EventuallyEq.deriv_eq
    have hwNorm32 : ‖w‖ < (1 / 32 : ℝ) := by
      simpa [Metric.mem_ball, dist_zero_right] using hw
    exact eventuallyEq_jet_continuation_left hh hk hhk hq
      (hwNorm32.trans (by norm_num : (1 / 32 : ℝ) < 1 / 8))

end RiemannZeta.GuthMaynard
