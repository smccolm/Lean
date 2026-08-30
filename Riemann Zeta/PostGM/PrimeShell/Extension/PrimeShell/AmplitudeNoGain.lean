import PrimeShell.TwoBandAmplitude
import Mathlib.MeasureTheory.Function.L2Space
import Zeta23.XiPrime.Certificate.D1
import Zeta23.XiPrime.Window

namespace PrimeShell

noncomputable section

open Filter Function MeasureTheory Set intervalIntegral
open Zeta23 Zeta23.XiPrime

/-- The part of the normalized source interval left after removing the
open gap between two amplitude bands. -/
def amplitudeShellAllowedSet (leftEdge rightEdge : ℝ) : Set ℝ :=
  Icc (-(1 : ℝ) / 2) leftEdge ∪ Icc rightEdge (1 / 2)

theorem amplitudeShellAllowedSet_measure
    {leftEdge rightEdge : ℝ}
    (hleft : -(1 : ℝ) / 2 ≤ leftEdge)
    (hright : rightEdge ≤ 1 / 2)
    (horder : leftEdge < rightEdge) :
    volume.real (amplitudeShellAllowedSet leftEdge rightEdge) =
      1 - (rightEdge - leftEdge) := by
  have hdis : Disjoint (Icc (-(1 : ℝ) / 2) leftEdge)
      (Icc rightEdge (1 / 2)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    linarith [hx.2, hy.1]
  have hmeasure := measureReal_union hdis measurableSet_Icc
    (isCompact_Icc.measure_ne_top (μ := volume))
    (isCompact_Icc.measure_ne_top (μ := volume))
  unfold amplitudeShellAllowedSet
  rw [hmeasure, Real.volume_real_Icc_of_le hleft,
    Real.volume_real_Icc_of_le hright]
  ring

theorem amplitudeShellAllowedSet_measure_ne_top
    (leftEdge rightEdge : ℝ) :
    volume (amplitudeShellAllowedSet leftEdge rightEdge) ≠ ⊤ := by
  exact (isCompact_Icc.union isCompact_Icc).measure_ne_top

/-- Cauchy--Schwarz on a finite measurable support, stated in the exact
real-integral form used by the Zeta23 window functional. -/
theorem sq_setIntegral_le_measure_mul_setIntegral_sq
    {S : Set ℝ} (hS : MeasurableSet S) (hSfinite : volume S ≠ ⊤)
    {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ x ∈ S, 0 ≤ f x) (hf1 : ∀ x ∈ S, f x ≤ 1) :
    (∫ x in S, f x) ^ 2 ≤ volume.real S * ∫ x in S, f x ^ 2 := by
  let μ := volume.restrict S
  let hμ : IsFiniteMeasure μ :=
    IsFiniteMeasure.mk (by
      change (volume.restrict S) Set.univ < ⊤
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
      exact hSfinite.lt_top)
  let _ : IsFiniteMeasure μ := hμ
  have hae0 : 0 ≤ᵐ[μ] f := by
    change ∀ᵐ x ∂volume.restrict S, 0 ≤ f x
    exact ae_restrict_of_forall_mem hS fun x hx => hf0 x hx
  have hae1 : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1 := by
    change ∀ᵐ x ∂volume.restrict S, ‖f x‖ ≤ 1
    rw [ae_restrict_iff' hS]
    exact Filter.Eventually.of_forall fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x hx)]
      exact hf1 x hx
  have hmf : MemLp f (ENNReal.ofReal (2 : ℝ)) μ :=
    MemLp.of_bound hf.aestronglyMeasurable 1 hae1
  have hm1 : MemLp (fun _ : ℝ => (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) μ := by
    exact MemLp.of_bound aestronglyMeasurable_const 1
      (Filter.Eventually.of_forall fun _ => by simp)
  have hhold := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two hae0
    (Filter.Eventually.of_forall fun _ => (zero_le_one : (0 : ℝ) ≤ 1))
    hmf hm1
  change (∫ x in S, f x * 1) ≤
    (∫ x in S, f x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
      (∫ _x in S, (1 : ℝ) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) at hhold
  simp only [mul_one, Real.rpow_two] at hhold
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hhold
  have hI0 : 0 ≤ ∫ x in S, f x :=
    setIntegral_nonneg hS (fun x hx => hf0 x hx)
  have hJ0 : 0 ≤ ∫ x in S, f x ^ 2 :=
    setIntegral_nonneg hS (fun _ _ => sq_nonneg _)
  have hM0 : 0 ≤ volume.real S := measureReal_nonneg
  have hsJ := Real.sq_sqrt hJ0
  have hsM := Real.sq_sqrt hM0
  rw [MeasureTheory.integral_const] at hhold
  change (∫ x in S, f x) ≤ √(∫ x in S, f x ^ 2) *
    √((volume.restrict S).real univ • (1 : ℝ) ^ 2) at hhold
  rw [measureReal_restrict_apply MeasurableSet.univ] at hhold
  simp only [univ_inter, smul_eq_mul, mul_one, one_pow] at hhold
  have hR0 : 0 ≤ √(∫ x in S, f x ^ 2) * √(volume.real S) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [sq_nonneg ((∫ x in S, f x) -
    √(∫ x in S, f x ^ 2) * √(volume.real S))]

/-- The exact support-loss inequality for a two-band amplitude.  No
bounded-weight proxy is used: the integrands are the literal profile
`q²` and its square from `cWin`. -/
theorem amplitudeSq_integral_cauchy_of_separated_support
    {q : ℝ → ℝ} (hq : AmplitudeProfile q)
    {leftEdge rightEdge : ℝ}
    (hleft : -(1 : ℝ) / 2 ≤ leftEdge)
    (hright : rightEdge ≤ 1 / 2)
    (horder : leftEdge < rightEdge)
    (hsupport : ∀ s ∈ Icc (-(1 : ℝ) / 2) (1 / 2), q s ≠ 0 →
      s ≤ leftEdge ∨ rightEdge ≤ s) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2), amplitudeSq q s) ^ 2 ≤
      (1 - (rightEdge - leftEdge)) *
        ∫ s in (-(1 : ℝ) / 2)..(1 / 2), (amplitudeSq q s) ^ 2 := by
  let S := amplitudeShellAllowedSet leftEdge rightEdge
  let v := amplitudeSq q
  have hvcont : Continuous v := hq.contDiff.continuous.pow 2
  have hSmeas : MeasurableSet S := measurableSet_Icc.union measurableSet_Icc
  have hSsub : S ⊆ Icc (-(1 : ℝ) / 2) (1 / 2) := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨hx.1, le_trans hx.2 (le_trans horder.le hright)⟩
    · exact ⟨le_trans hleft (le_trans horder.le hx.1), hx.2⟩
  have hvzero : ∀ x ∈ Icc (-(1 : ℝ) / 2) (1 / 2) \ S, v x = 0 := by
    intro x hx
    have hqzero : q x = 0 := by
      by_contra hne
      rcases hsupport x hx.1 hne with hleft' | hright'
      · exact hx.2 (Or.inl ⟨hx.1.1, hleft'⟩)
      · exact hx.2 (Or.inr ⟨hright', hx.1.2⟩)
    simp [v, amplitudeSq, hqzero]
  have hvfull : (∫ x in Icc (-(1 : ℝ) / 2) (1 / 2), v x) =
      ∫ x in S, v x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Icc hSsub hvzero
  have hv2zero : ∀ x ∈ Icc (-(1 : ℝ) / 2) (1 / 2) \ S,
      v x ^ 2 = 0 := by
    intro x hx
    rw [hvzero x hx]
    norm_num
  have hv2full : (∫ x in Icc (-(1 : ℝ) / 2) (1 / 2), v x ^ 2) =
      ∫ x in S, v x ^ 2 :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Icc hSsub hv2zero
  have hset := sq_setIntegral_le_measure_mul_setIntegral_sq
    hSmeas (amplitudeShellAllowedSet_measure_ne_top leftEdge rightEdge)
    hvcont (fun x _ => sq_nonneg (q x)) (fun x _ => by
      unfold v amplitudeSq
      nlinarith [hq.nonneg x, hq.le_one x])
  rw [amplitudeShellAllowedSet_measure hleft hright horder] at hset
  have hvInterval : (∫ x in (-(1 : ℝ) / 2)..(1 / 2), v x) =
      ∫ x in S, v x := by
    rw [intervalIntegral.integral_of_le (by norm_num),
      ← integral_Icc_eq_integral_Ioc, hvfull]
  have hv2Interval : (∫ x in (-(1 : ℝ) / 2)..(1 / 2), v x ^ 2) =
      ∫ x in S, v x ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num),
      ← integral_Icc_eq_integral_Ioc, hv2full]
  change (∫ x in (-(1 : ℝ) / 2)..(1 / 2), v x) ^ 2 ≤
    (1 - (rightEdge - leftEdge)) *
      ∫ x in (-(1 : ℝ) / 2)..(1 / 2), v x ^ 2
  rw [hvInterval, hv2Interval]
  exact hset

/-- Positivity of the full `D1` contribution on every nonnegative
bandwidth, with no support-one upper bound on `lambda`. -/
theorem jWin_D1_nonneg_extended
    {v : ℝ → ℝ} {lam : ℝ}
    (hv : ∀ s ∈ Icc (-(1 : ℝ) / 2) (1 / 2), 0 ≤ v s)
    (hlam : 0 ≤ lam) : 0 ≤ jWin D1 lam v := by
  unfold jWin
  refine mul_nonneg (by norm_num)
    (intervalIntegral.integral_nonneg zero_le_one fun r hr => ?_)
  exact mul_nonneg (D1_nonneg (mul_nonneg hlam hr.1))
    (vConv_nonneg hv hr)

/-- A faithful separated-amplitude Prime Shell object.

The source is the actual `atV (q²)` family.  The two closed bands lie
inside the normalized source interval, both are present, each same-band
block stays within support one, while every cross-band frequency starts
strictly beyond support one.  `mass_pos` is the ordinary nonzero
normalization required by the window quotient, not an arithmetic or
zero-count hypothesis. -/
structure FaithfulAmplitudeShell where
  A : PrimeShellFullChainAdmissible
  q : ℝ → ℝ
  amplitude : AmplitudeProfile q
  leftEdge : ℝ
  rightEdge : ℝ
  left_mem : -(1 : ℝ) / 2 ≤ leftEdge
  right_mem : rightEdge ≤ 1 / 2
  edge_order : leftEdge < rightEdge
  symmetric_edges : leftEdge = -rightEdge
  support_split : ∀ s ∈ Icc (-(1 : ℝ) / 2) (1 / 2), q s ≠ 0 →
    s ≤ leftEdge ∨ rightEdge ≤ s
  left_present : ∃ s ∈ Icc (-(1 : ℝ) / 2) leftEdge, q s ≠ 0
  right_present : ∃ s ∈ Icc rightEdge (1 / 2), q s ≠ 0
  left_low_block :
    A.toPrimeShellAdmissible.P.lam * (leftEdge - (-(1 : ℝ) / 2)) ≤ 1
  right_low_block :
    A.toPrimeShellAdmissible.P.lam * ((1 / 2) - rightEdge) ≤ 1
  cross_beyond_support_one :
    1 < A.toPrimeShellAdmissible.P.lam * (rightEdge - leftEdge)
  mass_pos : 0 < ∫ s in (-(1 : ℝ) / 2)..(1 / 2), amplitudeSq q s

namespace FaithfulAmplitudeShell

/-- The source family of a faithful shell enters the extended explicit
formula through the proved amplitude bridge. -/
theorem extendedFamilyHyps (S : FaithfulAmplitudeShell) :
    ExtendedFamilyHyps
      (S.A.toPrimeShellAdmissible.P.atV (amplitudeSq S.q)) :=
  extendedFamilyHyps_atAmplitude S.A S.amplitude

/-- The exact Zeta23 second-moment constant of every faithful separated
shell is already larger than three.  This theorem is independent of the
strength of the prime-correlation input. -/
theorem kappaXi_gt_three (S : FaithfulAmplitudeShell) :
    3 < kappaXi S.A.toPrimeShellAdmissible.P.lam (amplitudeSq S.q) := by
  let lam := S.A.toPrimeShellAdmissible.P.lam
  let v := amplitudeSq S.q
  let I := ∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s
  let J := ∫ s in (-(1 : ℝ) / 2)..(1 / 2), v s ^ 2
  let W := jWin D1 lam v
  let supportMass := 1 - (S.rightEdge - S.leftEdge)
  have hC : I ^ 2 ≤ supportMass * J := by
    exact amplitudeSq_integral_cauchy_of_separated_support S.amplitude
      S.left_mem S.right_mem S.edge_order S.support_split
  have hsupportMass0 : 0 ≤ supportMass := by
    dsimp [supportMass]
    linarith [S.left_mem, S.right_mem]
  have hlam0 : 0 < lam := S.A.toPrimeShellAdmissible.lambda_pos
  have hlam4 : lam < 4 / 3 := S.A.lambda_lt_four_thirds
  have hIpos : 0 < I := S.mass_pos
  have hI2pos : 0 < I ^ 2 := sq_pos_of_pos hIpos
  have hJpos : 0 < J := by
    nlinarith
  have hthreeLamSupport : 3 * lam * supportMass < 1 := by
    dsimp [supportMass]
    nlinarith [S.cross_beyond_support_one]
  have hscaled : 3 * lam * (supportMass * J) < J := by
    have := mul_lt_mul_of_pos_right hthreeLamSupport hJpos
    nlinarith
  have hcore : 3 * (lam * I ^ 2) < J := by
    have hfac : 0 ≤ 3 * lam := mul_nonneg (by norm_num) hlam0.le
    have hmul := mul_le_mul_of_nonneg_left hC hfac
    calc
      3 * (lam * I ^ 2) ≤ 3 * lam * (supportMass * J) := by
        nlinarith
      _ < J := hscaled
  have hW0 : 0 ≤ W :=
    jWin_D1_nonneg_extended (fun _ _ => sq_nonneg _) hlam0.le
  have hdenpos : 0 < J + lam * W := by
    nlinarith [mul_nonneg hlam0.le hW0]
  have hbase : 3 * (lam * I ^ 2) < J + lam * W := by
    nlinarith [mul_nonneg hlam0.le hW0]
  have hk : kappaXi lam v = (J + lam * W) / (lam * I ^ 2) := by
    unfold kappaXi cWin
    dsimp [I, J, W]
    field_simp
  rw [hk, lt_div_iff₀ (mul_pos hlam0 hI2pos)]
  exact hbase

/-- A faithful shell cannot beat `2/3` by any positive amount through
the exact Zeta23 `2 - kappaXi` rank/inertia certificate. -/
theorem no_positive_gain (S : FaithfulAmplitudeShell)
    {delta : ℝ} (hdelta : 0 < delta) :
    ¬ ((2 / 3 : ℝ) + delta <
      2 - kappaXi S.A.toPrimeShellAdmissible.P.lam (amplitudeSq S.q)) := by
  have hk := S.kappaXi_gt_three
  linarith

end FaithfulAmplitudeShell

/-- Public universal Prime Shell verdict.  It quantifies over the whole
faithful separated-amplitude class and remains true even with perfect
arithmetic information, because the obstruction is the exact spectral
window quotient itself. -/
theorem primeShell_universal_no_gain_native :
    ∀ S : FaithfulAmplitudeShell, ∀ delta : ℝ, 0 < delta →
      ¬ ((2 / 3 : ℝ) + delta <
        2 - kappaXi S.A.toPrimeShellAdmissible.P.lam (amplitudeSq S.q)) := by
  intro S delta hdelta
  exact S.no_positive_gain hdelta

/-- The direct trusted-statement form of the proposed separated-shell
improvement: some faithful shell would have to improve the Zeta23
`2 - kappaXi` exponent beyond `2/3` by a positive amount. -/
def FaithfulSeparatedAmplitudeGain : Prop :=
  ∃ S : FaithfulAmplitudeShell, ∃ delta : ℝ, 0 < delta ∧
    (2 / 3 : ℝ) + delta <
      2 - kappaXi S.A.toPrimeShellAdmissible.P.lam (amplitudeSq S.q)

/-- Two-sided comparator for the terminal Prime Shell verdict.  The
faithful separated-amplitude gain statement is equivalent to `False`.-/
theorem faithfulSeparatedAmplitudeGain_iff_false :
    FaithfulSeparatedAmplitudeGain ↔ False := by
  constructor
  · rintro ⟨S, delta, hdelta, hgain⟩
    exact (S.no_positive_gain hdelta) hgain
  · intro hfalse
    exact False.elim hfalse

end

end PrimeShell
