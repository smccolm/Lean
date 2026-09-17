import Tao2026.SmoothNumberSaddleThirdShellIntegral

/-!
# An eighth-root prime alphabet for the fourth outer shell

The third-shell alphabet becomes resonant after height `6*pi/log y`.  A
third iterated natural square root has logarithmic size between one ninth
and one eighth of `log y` on an explicit tail.  Its retained CEP primes lie
above one twelfth of `log y`, keeping their phases in the nonpositive-cosine
window throughout `[6*pi/log y, 12*pi/log y]`.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval Chebyshev

namespace Tao2026

noncomputable section

def smoothSaddleFourthPrimeScale (y : ℕ) : ℕ :=
  Nat.sqrt (smoothSaddleThirdPrimeScale y)

theorem four_le_smoothSaddleSecondPrimeScale
    {y : ℕ} (hy : 16 ≤ y) :
    4 ≤ smoothSaddleSecondPrimeScale y := by
  rw [smoothSaddleSecondPrimeScale, Nat.le_sqrt']
  norm_num
  exact hy

theorem four_le_smoothSaddleThirdPrimeScale
    {y : ℕ} (hy : 256 ≤ y) :
    4 ≤ smoothSaddleThirdPrimeScale y := by
  rw [smoothSaddleThirdPrimeScale, Nat.le_sqrt']
  norm_num
  rw [smoothSaddleSecondPrimeScale, Nat.le_sqrt']
  norm_num
  exact hy

theorem smoothSaddleFourthPrimeScale_le (y : ℕ) :
    smoothSaddleFourthPrimeScale y ≤ y := by
  exact (Nat.sqrt_le_self _).trans (smoothSaddleThirdPrimeScale_le y)

theorem two_le_smoothSaddleFourthPrimeScale
    {y : ℕ} (hy : 256 ≤ y) :
    2 ≤ smoothSaddleFourthPrimeScale y := by
  rw [smoothSaddleFourthPrimeScale, Nat.le_sqrt']
  exact four_le_smoothSaddleThirdPrimeScale hy

theorem log_smoothSaddleFourthPrimeScale_le_eighth_log
    {y : ℕ} (hy : 256 ≤ y) :
    Real.log (smoothSaddleFourthPrimeScale y : ℝ) ≤
      (1 / 8 : ℝ) * Real.log (y : ℝ) := by
  have hthird : 4 ≤ smoothSaddleThirdPrimeScale y :=
    four_le_smoothSaddleThirdPrimeScale hy
  calc
    Real.log (smoothSaddleFourthPrimeScale y : ℝ) ≤
        (1 / 2 : ℝ) * Real.log (smoothSaddleThirdPrimeScale y : ℝ) := by
      simpa only [smoothSaddleFourthPrimeScale, smoothSaddleSecondPrimeScale]
        using log_smoothSaddleSecondPrimeScale_le_half_log hthird
    _ ≤ (1 / 2 : ℝ) * ((1 / 4 : ℝ) * Real.log (y : ℝ)) := by
      gcongr
      exact log_smoothSaddleThirdPrimeScale_le_quarter_log (by omega)
    _ = (1 / 8 : ℝ) * Real.log (y : ℝ) := by ring

theorem one_ninth_log_le_log_smoothSaddleFourthPrimeScale
    {y : ℕ} (hy : 256 ≤ y)
    (hlogY : 126 * Real.log 2 ≤ Real.log (y : ℝ)) :
    (1 / 9 : ℝ) * Real.log (y : ℝ) ≤
      Real.log (smoothSaddleFourthPrimeScale y : ℝ) := by
  have hsecond : 4 ≤ smoothSaddleSecondPrimeScale y :=
    four_le_smoothSaddleSecondPrimeScale (by omega)
  have hthird : 4 ≤ smoothSaddleThirdPrimeScale y :=
    four_le_smoothSaddleThirdPrimeScale hy
  have h₁ := half_log_sub_log_two_le_log_smoothSaddleSecondPrimeScale
    (show 4 ≤ y by omega)
  have h₂ := half_log_sub_log_two_le_log_smoothSaddleSecondPrimeScale hsecond
  have h₃ := half_log_sub_log_two_le_log_smoothSaddleSecondPrimeScale hthird
  change (1 / 2 : ℝ) *
      Real.log (smoothSaddleSecondPrimeScale y : ℝ) - Real.log 2 ≤
    Real.log (smoothSaddleThirdPrimeScale y : ℝ) at h₂
  change (1 / 2 : ℝ) *
      Real.log (smoothSaddleThirdPrimeScale y : ℝ) - Real.log 2 ≤
    Real.log (smoothSaddleFourthPrimeScale y : ℝ) at h₃
  nlinarith

theorem one_twelfth_log_le_log_of_mem_fourthPrimeAlphabet
    {B y : ℕ} {u : ℝ} (hB : 4 ≤ B) (hy : 256 ≤ y)
    (hlogY : 126 * Real.log 2 ≤ Real.log (y : ℝ))
    (hlogU : 12 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huN : u ≤ Real.sqrt (smoothSaddleFourthPrimeScale y))
    {p : TaoBoundedPrime (smoothSaddleFourthPrimeScale y)}
    (hp : p ∈ cepDyadicPrimeAlphabet (smoothSaddleFourthPrimeScale y)
      (cepDyadicBlockCount (smoothSaddleFourthPrimeScale y) u)) :
    (1 / 12 : ℝ) * Real.log (y : ℝ) ≤ Real.log (p : ℝ) := by
  let N := smoothSaddleFourthPrimeScale y
  have hN : 2 ≤ N := two_le_smoothSaddleFourthPrimeScale hy
  have hlogN := one_ninth_log_le_log_smoothSaddleFourthPrimeScale hy hlogY
  have hcut := one_sub_two_div_log_mul_log_le_log_cepDyadicCofactorCutoff
    hB hN (by linarith) hBu huN
  have hlogUPos : 0 < Real.log u := by linarith
  have hcoeff : (5 / 6 : ℝ) ≤ 1 - 2 / Real.log u := by
    have hdiv : 2 / Real.log u ≤ (1 / 6 : ℝ) := by
      apply (div_le_iff₀ hlogUPos).mpr
      nlinarith
    linarith
  have hlogNNonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlogYNonneg : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  have hcutPos : (0 : ℝ) < cepDyadicCofactorCutoff N u := by
    have hw := nat_le_cepDyadicCofactorCutoff_of_criticalRange
      (show 1 ≤ N by omega) (by linarith) hBu huN
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < B) hw)
  have hpCut : (cepDyadicCofactorCutoff N u : ℝ) < (p : ℝ) := by
    exact_mod_cast cepDyadicCofactorCutoff_lt_of_mem hp
  calc
    (1 / 12 : ℝ) * Real.log (y : ℝ) ≤
        (5 / 6 : ℝ) * ((1 / 9 : ℝ) * Real.log (y : ℝ)) := by
      nlinarith
    _ ≤ (5 / 6 : ℝ) * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_left (by simpa only [N] using hlogN) (by norm_num)
    _ ≤ (1 - 2 / Real.log u) * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff hlogNNonneg
    _ ≤ Real.log (cepDyadicCofactorCutoff N u : ℕ) := hcut
    _ ≤ Real.log (p : ℝ) := Real.log_le_log hcutPos hpCut.le

theorem one_le_cosineLossTerm_of_fourthPrimeAlphabet
    {B y : ℕ} {u t : ℝ} (hB : 4 ≤ B) (hy : 256 ≤ y)
    (hlogY : 126 * Real.log 2 ≤ Real.log (y : ℝ))
    (hlogU : 12 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huN : u ≤ Real.sqrt (smoothSaddleFourthPrimeScale y))
    (htLower : 6 * Real.pi / Real.log (y : ℝ) ≤ t)
    (htUpper : t ≤ 12 * Real.pi / Real.log (y : ℝ))
    {p : TaoBoundedPrime (smoothSaddleFourthPrimeScale y)}
    (hp : p ∈ cepDyadicPrimeAlphabet (smoothSaddleFourthPrimeScale y)
      (cepDyadicBlockCount (smoothSaddleFourthPrimeScale y) u)) :
    1 ≤ 1 - Real.cos (t * Real.log (p : ℝ)) := by
  have hpData := Nat.mem_primesLE.mp p.2
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpData.2.pos
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogpLower := one_twelfth_log_le_log_of_mem_fourthPrimeAlphabet
    hB hy hlogY hlogU hBu huN hp
  have hlogpUpper : Real.log (p : ℝ) ≤
      (1 / 8 : ℝ) * Real.log (y : ℝ) := by
    exact (Real.log_le_log hpPos (by exact_mod_cast hpData.1)).trans
      (log_smoothSaddleFourthPrimeScale_le_eighth_log hy)
  have htPos : 0 < t := lt_of_lt_of_le (by positivity [Real.pi_pos]) htLower
  have hphaseLower : Real.pi / 2 ≤ t * Real.log (p : ℝ) := by
    have hmul := mul_le_mul htLower hlogpLower
      (by positivity) (by positivity [Real.pi_pos])
    field_simp [hlogy.ne'] at hmul
    nlinarith [Real.pi_pos]
  have hphaseUpper : t * Real.log (p : ℝ) ≤ Real.pi + Real.pi / 2 := by
    calc
      t * Real.log (p : ℝ) ≤
          (12 * Real.pi / Real.log (y : ℝ)) *
            ((1 / 8 : ℝ) * Real.log (y : ℝ)) :=
        mul_le_mul htUpper hlogpUpper
          (Real.log_nonneg (by exact_mod_cast hpData.2.one_le))
          (by positivity [Real.pi_pos])
      _ = Real.pi + Real.pi / 2 := by field_simp [hlogy.ne']; ring
  linarith [Real.cos_nonpos_of_pi_div_two_le_of_le hphaseLower hphaseUpper]

theorem fourthOuterMultiShell_cosineLoss_lower
    {B y : ℕ} {u sigma t : ℝ} (hB : 4 ≤ B) (hy : 256 ≤ y)
    (hlogY : 126 * Real.log 2 ≤ Real.log (y : ℝ))
    (hlogU : 12 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huN : u ≤ Real.sqrt (smoothSaddleFourthPrimeScale y))
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta (n : ℝ) ∧
        Chebyshev.theta (n : ℝ) ≤ (5 / 4 : ℝ) * n)
    (hsigma1 : sigma ≤ 1)
    (htLower : 6 * Real.pi / Real.log (y : ℝ) ≤ t)
    (htUpper : t ≤ 12 * Real.pi / Real.log (y : ℝ)) :
    (cepDyadicCofactorCutoff (smoothSaddleFourthPrimeScale y) u : ℝ) ^
          (1 - sigma) / (16 * Real.log 2 * Real.log u) ≤
      smoothSaddleCosineLoss y sigma t := by
  let N := smoothSaddleFourthPrimeScale y
  let P := cepDyadicPrimeAlphabet N (cepDyadicBlockCount N u)
  let S := (Finset.Icc 2 y).filter Nat.Prime
  let f : ℕ → ℝ := fun p =>
    (p : ℝ) ^ (-sigma) * (1 - Real.cos (t * Real.log (p : ℝ)))
  have hN : 2 ≤ N := two_le_smoothSaddleFourthPrimeScale hy
  have hweight := cofactor_rpow_div_log_le_sum_rpow_neg_cepDyadicPrimeAlphabet
    hB hN (by linarith) hBu huN hpnt hsigma1
  have hphase (p : TaoBoundedPrime N) (hp : p ∈ P) :
      1 ≤ 1 - Real.cos (t * Real.log ((p : ℕ) : ℝ)) := by
    exact one_le_cosineLossTerm_of_fourthPrimeAlphabet
      hB hy hlogY hlogU hBu huN htLower htUpper hp
  have hsubset : P.image (fun p : TaoBoundedPrime N => (p : ℕ)) ⊆ S := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hqData := Nat.mem_primesLE.mp q.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hqData.2.two_le,
        hqData.1.trans (smoothSaddleFourthPrimeScale_le y)⟩, hqData.2⟩
  calc
    (cepDyadicCofactorCutoff N u : ℝ) ^ (1 - sigma) /
        (16 * Real.log 2 * Real.log u) ≤
      ∑ p ∈ P, ((p : ℕ) : ℝ) ^ (-sigma) := by
        simpa only [N, P] using hweight
    _ ≤ ∑ p ∈ P, f (p : ℕ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact le_mul_of_one_le_right (by positivity) (hphase p hp)
    _ = ∑ p ∈ P.image (fun p : TaoBoundedPrime N => (p : ℕ)), f p := by
      rw [Finset.sum_image]
      intro p hp q hq hpq
      exact Subtype.ext hpq
    _ ≤ ∑ p ∈ S, f p := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p hp hnot => mul_nonneg (by positivity)
          (by linarith [Real.cos_le_one (t * Real.log (p : ℝ))]))
    _ = smoothSaddleCosineLoss y sigma t := rfl

theorem IsTaoCriticalSmoothRegime.eventually_rankinRatio_le_sqrt_fourthPrimeScale
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop, smoothRankinRatio (X n) (y n) ≤
      Real.sqrt (smoothSaddleFourthPrimeScale (y n)) := by
  have hrankin := hregime.eventually_rankinRatio_le_y_rpow hα
    (by norm_num : (0 : ℝ) < 1 / 100)
  filter_upwards [hrankin, (hregime.tendsto_y_atTop hα).eventually
      (eventually_ge_atTop 256),
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_ge_atTop (126 * Real.log 2))] with n hu hy hlogY
  let N := smoothSaddleFourthPrimeScale (y n)
  have hN : 2 ≤ N := two_le_smoothSaddleFourthPrimeScale hy
  have hyPos : (0 : ℝ) < y n := by positivity
  have hNPos : (0 : ℝ) < N := by positivity
  have hlogN := one_ninth_log_le_log_smoothSaddleFourthPrimeScale hy hlogY
  have hlogN' : (1 / 9 : ℝ) * Real.log (y n : ℝ) ≤ Real.log (N : ℝ) := by
    simpa only [N] using hlogN
  have hlogyNonneg : 0 ≤ Real.log (y n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y n by omega))
  have hpow : (y n : ℝ) ^ (1 / 100 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hyPos, Real.rpow_def_of_pos hNPos]
    apply Real.exp_le_exp.mpr
    nlinarith [hlogN']
  calc
    smoothRankinRatio (X n) (y n) ≤ (y n : ℝ) ^ (1 / 100 : ℝ) := hu
    _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := hpow
    _ = Real.sqrt N := by rw [Real.sqrt_eq_rpow]

theorem IsTaoCriticalSmoothRegime.eventually_fourthOuterMultiShell_cosineLoss_lower
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop, ∀ t : ℝ,
      6 * Real.pi / Real.log (y n : ℝ) ≤ t →
      t ≤ 12 * Real.pi / Real.log (y n : ℝ) →
      (cepDyadicCofactorCutoff (smoothSaddleFourthPrimeScale (y n))
          (smoothRankinRatio (X n) (y n)) : ℝ) ^
            (1 - smoothSaddlePoint (X n) (y n)) /
          (16 * Real.log 2 * Real.log (smoothRankinRatio (X n) (y n))) ≤
        smoothSaddleCosineLoss (y n)
          (smoothSaddlePoint (X n) (y n)) t := by
  obtain ⟨B, hB, hpnt⟩ := exists_chebyshevTheta_quarter_threshold
  have huTop := hregime.tendsto_rankinRatio_atTop hα
  have hloguTop := Real.tendsto_log_atTop.comp huTop
  filter_upwards [(hregime.tendsto_y_atTop hα).eventually
      (eventually_ge_atTop 256),
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_ge_atTop (126 * Real.log 2)),
    hloguTop.eventually (eventually_ge_atTop (12 : ℝ)),
    huTop.eventually (eventually_ge_atTop (B : ℝ)),
    hregime.eventually_rankinRatio_le_sqrt_fourthPrimeScale hα,
    hregime.eventually_smoothSaddlePoint_lt_one hα] with
      n hy hlogY hlogU hBu huN hsigmaOne
  intro t htLower htUpper
  exact fourthOuterMultiShell_cosineLoss_lower
    hB hy hlogY hlogU hBu huN hpnt hsigmaOne.le htLower htUpper

end

end Tao2026
