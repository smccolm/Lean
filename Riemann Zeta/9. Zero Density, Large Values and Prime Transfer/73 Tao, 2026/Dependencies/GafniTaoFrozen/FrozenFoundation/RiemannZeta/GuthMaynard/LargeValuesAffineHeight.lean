import RiemannZeta.GuthMaynard.LargeValuesAffineIteration

open Complex Finset Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff FourierTransform Topology

namespace RiemannZeta.GuthMaynard

/-!
# Guth--Maynard Proposition 9.1: height-aware Fourier profiles

The source hypothesis in Proposition 9.1 is a *family* estimate: at physical
height `T`, the order-`n` Fourier decay is allowed to cost `T^n`.  It is not a
height-independent Schwartz seminorm bound.  This module records that
quantifier order without absorbing the height into a purported constant.

The extra factor `T^2` is the paper's crude conversion from the source
supremum to its positive mass.  Keeping it explicit lets the arbitrary
negative powers in Lemma 9.2 absorb it later.
-/

/-- Mass-normalized Fourier control at physical height `T`.  The coefficient
`D` is intended to be independent of `T` and of the member of the source
family. -/
def GMAffineHeightFourierMassBound
    (epsilon T : ℝ) (n : ℕ) (D : ℝ) (f : SchwartzMap ℝ ℝ) : Prop :=
  SchwartzMap.seminorm ℝ n 0 (fourier (gmAffineComplexify f)) ≤
    D * T ^ epsilon * T ^ (n + 2) * ∫ x : ℝ, f x

/-- A simultaneous height-aware profile at every Fourier order. -/
def GMAffineHeightFourierMassProfile
    (epsilon T : ℝ) (D : ℕ → ℝ) (f : SchwartzMap ℝ ℝ) : Prop :=
  ∀ n : ℕ, GMAffineHeightFourierMassBound epsilon T n (D n) f

/-- The same fixed source profile after `depth` adaptive smoothings.  Each
smoothing costs only a factor two after comparison with the growing positive
mass. -/
def GMAffineHeightFourierMassProfileAtDepth
    (epsilon T : ℝ) (D : ℕ → ℝ) (depth : ℕ)
    (f : SchwartzMap ℝ ℝ) : Prop :=
  ∀ n : ℕ,
    GMAffineHeightFourierMassBound epsilon T n
      ((2 : ℝ) ^ depth * D n) f

/-- All epsilon budgets and derivative orders required by the finite
Proposition 9.1 descent.  The coefficient family is fixed before the
physical height; the `2^depth` loss is the only cost of the adaptive
smoothings. -/
def GMAffineHeightFourierMassFamilyAtDepth
    (T : ℝ) (D : ℝ → ℕ → ℝ) (depth : ℕ)
    (f : SchwartzMap ℝ ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ n : ℕ,
    GMAffineHeightFourierMassBound epsilon T n
      ((2 : ℝ) ^ depth * D epsilon n) f

/-- The actual Section 10 source is supported on `[1/4,9/4]`; this is the
corresponding support envelope after `depth` adaptive smoothings. -/
def GMAffineWideDepthSupported
    (T : ℝ) (depth : ℕ) (f : ℝ → ℝ) : Prop :=
  GMAffineSupportedOn
    (1 / 4 - 2 * (depth : ℝ) / T)
    (9 / 4 + 2 * (depth : ℝ) / T) f

theorem GMAffineSupportedOn.wideDepthSupported_zero
    {T : ℝ} {f : ℝ → ℝ}
    (hf : GMAffineSupportedOn (1 / 4 : ℝ) (9 / 4) f) :
    GMAffineWideDepthSupported T 0 f := by
  simpa [GMAffineWideDepthSupported] using hf

theorem GMAffineWideDepthSupported.iterationSupported
    {T : ℝ} {depth : ℕ} {f : ℝ → ℝ}
    (hf : GMAffineWideDepthSupported T depth f)
    (hT : 8 * (depth : ℝ) ≤ T) (hTpos : 0 < T) :
    GMAffineIterationSupported f := by
  apply GMAffineSupportedOn.iterationSupported hf
  · have hratio : 2 * (depth : ℝ) / T ≤ 1 / 4 := by
      rw [div_le_iff₀ hTpos]
      nlinarith
    dsimp only [GMAffineWideDepthSupported] at hf ⊢
    linarith
  · have hratio : 2 * (depth : ℝ) / T ≤ 3 / 4 := by
      rw [div_le_iff₀ hTpos]
      nlinarith
    dsimp only [GMAffineWideDepthSupported] at hf ⊢
    linarith

theorem GMAffineHeightFourierMassBound.nonneg_coefficient
    {epsilon T D : ℝ} {n : ℕ} {f : SchwartzMap ℝ ℝ}
    (hbound : GMAffineHeightFourierMassBound epsilon T n D f) :
    0 ≤ D * T ^ epsilon * T ^ (n + 2) * ∫ x : ℝ, f x := by
  have hnonneg :
      0 ≤ SchwartzMap.seminorm ℝ n 0 (fourier (gmAffineComplexify f)) := by
    positivity
  exact hnonneg.trans hbound

/-- Pointwise decay obtained from the weighted Fourier seminorm while
retaining the complete physical-height factor. -/
theorem GMAffineHeightFourierMassBound.pointwise
    {epsilon T D : ℝ} {n : ℕ} {f : SchwartzMap ℝ ℝ}
    (hbound : GMAffineHeightFourierMassBound epsilon T n D f)
    {xi : ℝ} (hxi : xi ≠ 0) :
    ‖fourier (gmAffineComplexify f) xi‖ ≤
      (D * T ^ epsilon * T ^ (n + 2) * ∫ x : ℝ, f x) /
        |xi| ^ n := by
  have hseminorm :=
    SchwartzMap.le_seminorm' ℝ n 0 (fourier (gmAffineComplexify f)) xi
  rw [iteratedDeriv_zero] at hseminorm
  rw [le_div_iff₀ (pow_pos (abs_pos.mpr hxi) n)]
  simpa only [mul_comm] using hseminorm.trans hbound

/-- Convert the mass-normalized height profile into the exact pointwise
Fourier-decay interface consumed by the raw Lemma 9.2 calculation.  The
chosen constant may depend on the current positive source, but its product
with the source supremum is the uniform quantity `D * T^2 * ∫ f`; this is
the quantity retained by the corrected tail recurrence. -/
theorem exists_gmAffineHeightDecayConstant
    {epsilon T D : ℝ} {n : ℕ} {f : SchwartzMap ℝ ℝ}
    (hT : 0 < T) (hD : 0 ≤ D) (hf : ∀ x, 0 ≤ f x)
    (hbound : GMAffineHeightFourierMassBound epsilon T n D f) :
    ∃ C : ℝ, 0 ≤ C ∧
      C * SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) =
        D * T ^ 2 * ∫ x : ℝ, f x ∧
      ∀ xi : ℝ, xi ≠ 0 →
        ‖fourier (gmAffineComplexify f) xi‖ ≤
          C * T ^ epsilon * (T / |xi|) ^ n *
            SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) := by
  let S0 : ℝ := SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)
  let mass : ℝ := ∫ x : ℝ, f x
  by_cases hS0 : S0 = 0
  · have hfC : gmAffineComplexify f = 0 := by
      ext x
      have hx : ‖gmAffineComplexify f x‖ ≤ S0 := by
        simpa only [S0, pow_zero, iteratedDeriv_zero, one_mul] using
          SchwartzMap.le_seminorm' ℝ 0 0 (gmAffineComplexify f) x
      exact norm_eq_zero.mp
        (le_antisymm (by simpa only [hS0] using hx) (norm_nonneg _))
    have hfzero : f = 0 := by
      ext x
      have hx := congrArg (fun g : SchwartzMap ℝ ℂ => g x) hfC
      simpa [gmAffineComplexify] using congrArg Complex.re hx
    refine ⟨0, le_rfl, ?_, ?_⟩
    · simp [hfzero]
    · intro xi hxi
      rw [hfC]
      simp
  · have hS0pos : 0 < S0 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hS0)
    have hmass : 0 ≤ mass := by
      dsimp only [mass]
      exact integral_nonneg hf
    let C : ℝ := D * T ^ 2 * mass / S0
    have hC : 0 ≤ C := by
      dsimp only [C]
      positivity
    refine ⟨C, hC, ?_, ?_⟩
    · dsimp only [C, S0, mass]
      rw [div_mul_cancel₀ _ hS0]
    · intro xi hxi
      have hpoint := hbound.pointwise hxi
      have hxiabs : |xi| ≠ 0 := (abs_pos.mpr hxi).ne'
      apply hpoint.trans_eq
      dsimp only [C, S0, mass]
      rw [div_pow, pow_add]
      field_simp [hS0, hxiabs]
      simpa only [S0, mass] using
        (mul_div_cancel_right₀ (D * mass) hS0).symm

/-- One Section 9 smoothing preserves a height-aware profile with only the
fixed factor two.  This is the uniformity needed by the finite descent. -/
theorem gmAffineTildeSchwartz_heightFourierMassBound
    {epsilon T S D : ℝ} (hT : 0 ≤ T) (hS : 0 < S) (hD : 0 ≤ D)
    (n : ℕ) (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hbound : GMAffineHeightFourierMassBound epsilon T n D f) :
    GMAffineHeightFourierMassBound epsilon T n (2 * D)
      (gmAffineTildeSchwartz S hS f) := by
  have hfourier :=
    seminorm_fourier_gmAffineComplexify_tilde_le_four S hS f n
  have hmass :=
    two_mul_integral_le_integral_gmAffineTildeSchwartz S hS f hf
  unfold GMAffineHeightFourierMassBound at hbound ⊢
  have hscale : 0 ≤ 2 * D * T ^ epsilon * T ^ (n + 2) := by
    positivity
  calc
    SchwartzMap.seminorm ℝ n 0
        (fourier (gmAffineComplexify (gmAffineTildeSchwartz S hS f))) ≤
      4 * SchwartzMap.seminorm ℝ n 0
        (fourier (gmAffineComplexify f)) := hfourier
    _ ≤ 4 * (D * T ^ epsilon * T ^ (n + 2) * ∫ x : ℝ, f x) :=
      mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = (2 * D * T ^ epsilon * T ^ (n + 2)) *
        (2 * ∫ x : ℝ, f x) := by ring
    _ ≤ (2 * D * T ^ epsilon * T ^ (n + 2)) *
        ∫ x : ℝ, gmAffineTildeSchwartz S hS f x :=
      mul_le_mul_of_nonneg_left hmass hscale
    _ = (2 * D) * T ^ epsilon * T ^ (n + 2) *
        ∫ x : ℝ, gmAffineTildeSchwartz S hS f x := by ring

theorem gmAffineTildeSchwartz_heightFourierMassProfileAtDepth_succ
    {epsilon T S : ℝ} (hT : 0 ≤ T) (hS : 0 < S)
    (D : ℕ → ℝ) (hD : ∀ n, 0 ≤ D n) {depth : ℕ}
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hprofile : GMAffineHeightFourierMassProfileAtDepth
      epsilon T D depth f) :
    GMAffineHeightFourierMassProfileAtDepth epsilon T D (depth + 1)
      (gmAffineTildeSchwartz S hS f) := by
  intro n
  have hcurrent : 0 ≤ (2 : ℝ) ^ depth * D n :=
    mul_nonneg (pow_nonneg (by norm_num) _) (hD n)
  have hnext := gmAffineTildeSchwartz_heightFourierMassBound
    hT hS hcurrent n f hf (hprofile n)
  convert hnext using 1
  rw [pow_succ]
  ring

theorem gmAffineTildeSchwartz_heightFourierMassFamilyAtDepth_succ
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 < S)
    (D : ℝ → ℕ → ℝ) (hD : ∀ epsilon n, 0 ≤ D epsilon n)
    {depth : ℕ} (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hprofile : GMAffineHeightFourierMassFamilyAtDepth T D depth f) :
    GMAffineHeightFourierMassFamilyAtDepth T D (depth + 1)
      (gmAffineTildeSchwartz S hS f) := by
  intro epsilon hepsilon n
  have hcurrent : 0 ≤ (2 : ℝ) ^ depth * D epsilon n :=
    mul_nonneg (pow_nonneg (by norm_num) _) (hD epsilon n)
  have hnext := gmAffineTildeSchwartz_heightFourierMassBound
    hT hS hcurrent n f hf (hprofile epsilon hepsilon n)
  convert hnext using 1
  rw [pow_succ]
  ring

theorem gmAffineTildeSchwartz_wideDepthSupported_succ
    {T S : ℝ} (hT : 0 < T) (hS : 0 < S) (hTS : T ≤ S)
    {depth : ℕ} (f : SchwartzMap ℝ ℝ)
    (hsupp : GMAffineWideDepthSupported T depth f) :
    GMAffineWideDepthSupported T (depth + 1)
      (gmAffineTildeSchwartz S hS f) := by
  have hwidth : 2 / S ≤ 2 / T :=
    div_le_div_of_nonneg_left (by norm_num) hT hTS
  have hdepth :
      2 * ((depth : ℝ) + 1) / T = 2 * (depth : ℝ) / T + 2 / T := by
    field_simp [hT.ne']
  have hnext := gmAffineTildeSchwartz_supportedOn hS f hsupp
  apply hnext.mono
  · push_cast
    rw [hdepth]
    nlinarith
  · push_cast
    rw [hdepth]
    nlinarith

/-- The two powers of the source supremum in the second Region-II tail cost
`T^4` after mass normalization.  The same order choice `eta*n ≥ 31` still
absorbs this cost. -/
theorem gmAffineIterationRegionIISecondTail_height_ratio_le_one
    {delta T : ℝ} (hT : 2 ≤ T) {n : ℕ}
    (hn : (31 : ℝ) ≤ gmAffineIterationEta delta * n) :
    T ^ (4 : ℕ) *
        (T ^ (26 + 11 * gmAffineIterationEta delta) /
          ((T ^ gmAffineIterationEta delta) ^ n) ^ 2) ≤ 1 := by
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hetaUpper := gmAffineIterationEta_le_one delta
  have hexponent :
      30 + 11 * gmAffineIterationEta delta ≤
        2 * gmAffineIterationEta delta * n := by
    linarith
  have hratio := rpow_div_sq_pow_rpow_le_one hTone hexponent
  calc
    T ^ (4 : ℕ) *
        (T ^ (26 + 11 * gmAffineIterationEta delta) /
          ((T ^ gmAffineIterationEta delta) ^ n) ^ 2) =
      (T ^ (4 : ℕ) * T ^ (26 + 11 * gmAffineIterationEta delta)) /
        ((T ^ gmAffineIterationEta delta) ^ n) ^ 2 := by ring
    _ = T ^ (30 + 11 * gmAffineIterationEta delta) /
        ((T ^ gmAffineIterationEta delta) ^ n) ^ 2 := by
      congr 1
      rw [← Real.rpow_natCast T 4, ← Real.rpow_add hTpos]
      congr 1
      ring
    _ ≤ 1 := hratio

/-- Height-aware absorption of the complete Region-II omitted-frequency
tail.  Unlike the earlier fixed-Schwartz wrapper, this theorem retains and
then cancels the `T^2` supremum-to-mass loss, so its final coefficient is
uniform over a physical-height-indexed source family. -/
theorem gmAffineRegionIITailSourceBound_le_heightMass
    {delta T Cdiv Ctail D : ℝ} (hdelta : 0 < delta) (hT : 2 ≤ T)
    (hCdiv : 0 ≤ Cdiv)
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hproduct :
      Ctail * SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) =
        D * T ^ 2 * ∫ x : ℝ, f x)
    {M n : ℕ} (hMT : (M : ℝ) ≤ T ^ 4)
    (hn : (31 : ℝ) ≤ gmAffineIterationEta delta * n) :
    gmAffineRegionIITailSourceBound (gmAffineIterationEta delta) n T
        (T ^ gmAffineIterationEta delta) (T ^ (6 : ℕ))
        f M Cdiv Ctail ≤
      gmAffineRegionIITailMassConstant n Cdiv D *
        (∫ x : ℝ, f x) ^ 2 := by
  have hTone : 1 ≤ T := by linarith
  have hetaUpper := gmAffineIterationEta_le_one delta
  have hfirstExp :
      23 + 8 * gmAffineIterationEta delta ≤
        gmAffineIterationEta delta * n := by linarith
  have hhighExp :
      (30 : ℝ) ≤ 2 * gmAffineIterationEta delta * n := by linarith
  have hfirstRatio := rpow_div_pow_rpow_le_one hTone hfirstExp
  have hsecondRatio :=
    gmAffineIterationRegionIISecondTail_height_ratio_le_one hT hn
  have hhighRatio :
      T ^ (30 : ℕ) /
          ((T ^ gmAffineIterationEta delta) ^ n) ^ 2 ≤ 1 := by
    rw [← Real.rpow_natCast T 30]
    exact rpow_div_sq_pow_rpow_le_one hTone hhighExp
  have henvelope := gmAffineRegionIITailSourceBound_le_scale_ratios
    (Ctail := Ctail) hdelta hT hCdiv f hMT n
  have habs : (∫ u : ℝ, |f u|) = ∫ u : ℝ, f u := by
    apply integral_congr_ae
    filter_upwards with u
    exact abs_of_nonneg (hf u)
  have hmass : 0 ≤ ∫ x : ℝ, f x := integral_nonneg hf
  have hmiddle : 0 ≤ gmAffineMiddleFarSourceConstant n :=
    gmAffineMiddleFarSourceConstant_nonneg n
  have hA :
      0 ≤ (512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (64 * gmAffineMiddleFarSourceConstant n *
          (∫ u : ℝ, f u) ^ 2) := by positivity
  have hB :
      0 ≤ (512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (192 * 3 * (4 : ℝ) ^ n * D ^ 2 *
          (∫ u : ℝ, f u) ^ 2) := by positivity
  have hC :
      0 ≤ 4 * (gmAffineRegionIFarConstant n * (∫ x : ℝ, f x)) ^ 2 := by
    positivity
  refine henvelope.trans ?_
  unfold gmAffineRegionIITailMassConstant
  rw [habs]
  have hproductSq :
      Ctail ^ 2 *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) ^ 2 =
        D ^ 2 * T ^ (4 : ℕ) * (∫ x : ℝ, f x) ^ 2 := by
    rw [← mul_pow, hproduct]
    ring
  rw [show 192 * 3 * (4 : ℝ) ^ n * Ctail ^ 2 *
      SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) ^ 2 =
      192 * 3 * (4 : ℝ) ^ n *
        (Ctail ^ 2 * SchwartzMap.seminorm ℝ 0 0
          (gmAffineComplexify f) ^ 2) by ring,
    hproductSq]
  have hfirstTerm := mul_le_mul_of_nonneg_left hfirstRatio hA
  have hsecondTerm := mul_le_mul_of_nonneg_left hsecondRatio hB
  have hhighTerm := mul_le_mul_of_nonneg_left hhighRatio hC
  have hfirstExact :
      (512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (64 * gmAffineMiddleFarSourceConstant n *
            (∫ u : ℝ, f u) ^ 2) *
          (T ^ (23 + 8 * gmAffineIterationEta delta) /
            (T ^ gmAffineIterationEta delta) ^ n) ≤
      (512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (64 * gmAffineMiddleFarSourceConstant n *
          (∫ u : ℝ, f u) ^ 2) := by
    simpa only [mul_one] using hfirstTerm
  have hsecondExact :
      (512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (192 * 3 * (4 : ℝ) ^ n *
          (D ^ 2 * T ^ (4 : ℕ) * (∫ x : ℝ, f x) ^ 2)) *
          (T ^ (26 + 11 * gmAffineIterationEta delta) /
            ((T ^ gmAffineIterationEta delta) ^ n) ^ 2) ≤
      (512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (192 * 3 * (4 : ℝ) ^ n * D ^ 2 *
          (∫ u : ℝ, f u) ^ 2) := by
    convert hsecondTerm using 1 <;> ring
  have hhighExact :
      4 * (gmAffineRegionIFarConstant n * (∫ x : ℝ, f x)) ^ 2 *
          (T ^ (30 : ℕ) /
            ((T ^ gmAffineIterationEta delta) ^ n) ^ 2) ≤
        4 * (gmAffineRegionIFarConstant n * (∫ x : ℝ, f x)) ^ 2 := by
    simpa only [mul_one] using hhighTerm
  calc
    (512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (64 * gmAffineMiddleFarSourceConstant n *
            (∫ u : ℝ, f u) ^ 2) *
          (T ^ (23 + 8 * gmAffineIterationEta delta) /
            (T ^ gmAffineIterationEta delta) ^ n) +
      (512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (192 * 3 * (4 : ℝ) ^ n *
          (D ^ 2 * T ^ (4 : ℕ) * (∫ x : ℝ, f x) ^ 2)) *
          (T ^ (26 + 11 * gmAffineIterationEta delta) /
            ((T ^ gmAffineIterationEta delta) ^ n) ^ 2) +
      4 * (gmAffineRegionIFarConstant n * (∫ x : ℝ, f x)) ^ 2 *
        (T ^ (30 : ℕ) /
          ((T ^ gmAffineIterationEta delta) ^ n) ^ 2) ≤
      (512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (64 * gmAffineMiddleFarSourceConstant n * (∫ x : ℝ, f x) ^ 2) +
      (512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (192 * 3 * (4 : ℝ) ^ n * D ^ 2 * (∫ x : ℝ, f x) ^ 2) +
      4 * (gmAffineRegionIFarConstant n * (∫ x : ℝ, f x)) ^ 2 := by
        exact add_le_add (add_le_add hfirstExact hsecondExact) hhighExact
    _ = (512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
          (64 * gmAffineMiddleFarSourceConstant n +
            192 * 3 * (4 : ℝ) ^ n * D ^ 2) +
        4 * gmAffineRegionIFarConstant n ^ 2) *
          (∫ x : ℝ, f x) ^ 2 := by ring

/-- The physical `T^n` Fourier cost is more than cancelled by the
`Y = T^6` Region-III frequency tail. -/
theorem gmAffineIterationRegionIII_height_scale_le_one
    {delta T : ℝ} (hT : 2 ≤ T) {M n : ℕ}
    (hMT : (M : ℝ) ≤ T ^ 4) (hn : 20 ≤ n) :
    (T ^ gmAffineIterationEta delta * T ^ (n + 2)) ^ 2 *
        ((T ^ gmAffineIterationEta delta * (M : ℝ) ^ (n + 3)) ^ 2 *
          (T ^ (6 : ℕ)) ^ (1 - 2 * (n : ℝ))) ≤ 1 := by
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hMpow := gmAffineIteration_M_pow_add_three_le (n := n) hMT
  have htailNonneg : 0 ≤ (T ^ (6 : ℕ)) ^ (1 - 2 * (n : ℝ)) := by
    positivity
  have hscale :
      (T ^ gmAffineIterationEta delta * (M : ℝ) ^ (n + 3)) ^ 2 *
          (T ^ (6 : ℕ)) ^ (1 - 2 * (n : ℝ)) ≤
        (T ^ gmAffineIterationEta delta * T ^ (4 * (n + 3))) ^ 2 *
          (T ^ (6 : ℕ)) ^ (1 - 2 * (n : ℝ)) := by
    gcongr
  have hsource := gmAffineIterationRegionIII_source_scale_eq
    (delta := delta) hTpos n
  have hfront :
      (T ^ gmAffineIterationEta delta * T ^ (n + 2)) ^ 2 =
        T ^ (2 * gmAffineIterationEta delta + 2 * ((n : ℝ) + 2)) := by
    rw [mul_pow]
    have heta : (T ^ gmAffineIterationEta delta) ^ (2 : ℕ) =
        T ^ (2 * gmAffineIterationEta delta) := by
      simpa [mul_comm] using
        (Real.rpow_mul_natCast hTpos.le (gmAffineIterationEta delta) 2).symm
    have hnat : (T ^ (n + 2)) ^ (2 : ℕ) =
        T ^ (2 * ((n : ℝ) + 2)) := by
      rw [← pow_mul]
      rw [← Real.rpow_natCast T ((n + 2) * 2)]
      congr 1
      push_cast
      ring
    rw [heta, hnat, ← Real.rpow_add hTpos]
  have hetaUpper := gmAffineIterationEta_le_one delta
  have hnReal : (20 : ℝ) ≤ n := by exact_mod_cast hn
  have hexponent :
      (2 * gmAffineIterationEta delta + 2 * ((n : ℝ) + 2)) +
          (2 * gmAffineIterationEta delta + 30 - 4 * (n : ℝ)) ≤ 0 := by
    linarith
  calc
    (T ^ gmAffineIterationEta delta * T ^ (n + 2)) ^ 2 *
        ((T ^ gmAffineIterationEta delta * (M : ℝ) ^ (n + 3)) ^ 2 *
          (T ^ (6 : ℕ)) ^ (1 - 2 * (n : ℝ))) ≤
      (T ^ gmAffineIterationEta delta * T ^ (n + 2)) ^ 2 *
        ((T ^ gmAffineIterationEta delta * T ^ (4 * (n + 3))) ^ 2 *
          (T ^ (6 : ℕ)) ^ (1 - 2 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = T ^ (2 * gmAffineIterationEta delta + 2 * ((n : ℝ) + 2)) *
        T ^ (2 * gmAffineIterationEta delta + 30 - 4 * (n : ℝ)) := by
      rw [hfront, hsource]
    _ = T ^ ((2 * gmAffineIterationEta delta + 2 * ((n : ℝ) + 2)) +
        (2 * gmAffineIterationEta delta + 30 - 4 * (n : ℝ))) :=
      (Real.rpow_add hTpos _ _).symm
    _ ≤ T ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hTone hexponent
    _ = 1 := by simp

/-- Height-aware Region-III absorption.  The final coefficient is uniform
over the source family and contains no hidden physical-height dependence. -/
theorem gmAffineRegionIIISourceBound_le_heightMass
    {delta T D : ℝ} (hT : 2 ≤ T) (hD : 0 ≤ D)
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {M n : ℕ} (hMT : (M : ℝ) ≤ T ^ 4) (hn : 20 ≤ n)
    (hbound : GMAffineHeightFourierMassBound
      (gmAffineIterationEta delta) T n D f) :
    gmAffineRegionIIISourceBound n (T ^ (6 : ℕ)) f M
        (T ^ gmAffineIterationEta delta) ≤
      2 * (16 * (2 : ℝ) ^ n * D *
        gmAffineRegionIIIKernelConstant n) ^ 2 *
          (∫ x : ℝ, f x) ^ 2 := by
  have hmass : 0 ≤ ∫ x : ℝ, f x := integral_nonneg hf
  have hkernel := gmAffineRegionIIIKernelConstant_nonneg n
  have henv :
      gmAffineRegionIIIEnvelopeConstant n f ≤
        (16 * (2 : ℝ) ^ n * D * gmAffineRegionIIIKernelConstant n) *
          (T ^ gmAffineIterationEta delta * T ^ (n + 2)) *
            ∫ x : ℝ, f x := by
    unfold gmAffineRegionIIIEnvelopeConstant
    unfold GMAffineHeightFourierMassBound at hbound
    calc
      16 * (2 : ℝ) ^ n *
          SchwartzMap.seminorm ℝ n 0 (fourier (gmAffineComplexify f)) *
            gmAffineRegionIIIKernelConstant n ≤
        16 * (2 : ℝ) ^ n *
          (D * T ^ gmAffineIterationEta delta * T ^ (n + 2) *
            ∫ x : ℝ, f x) * gmAffineRegionIIIKernelConstant n := by
          gcongr
      _ = _ := by ring
  have henvNonneg := gmAffineRegionIIIEnvelopeConstant_nonneg n f
  have henvRhs :
      0 ≤ (16 * (2 : ℝ) ^ n * D * gmAffineRegionIIIKernelConstant n) *
          (T ^ gmAffineIterationEta delta * T ^ (n + 2)) *
            ∫ x : ℝ, f x := by positivity
  have henvSq := (sq_le_sq₀ henvNonneg henvRhs).2 henv
  have hscale := gmAffineIterationRegionIII_height_scale_le_one
    (delta := delta) hT hMT hn
  unfold gmAffineRegionIIISourceBound
  calc
    (gmAffineRegionIIIEnvelopeConstant n f *
          T ^ gmAffineIterationEta delta * (M : ℝ) ^ (n + 3)) ^ 2 *
        (2 * (T ^ (6 : ℕ)) ^ (1 - 2 * (n : ℝ))) ≤
      (((16 * (2 : ℝ) ^ n * D * gmAffineRegionIIIKernelConstant n) *
            (T ^ gmAffineIterationEta delta * T ^ (n + 2)) *
              ∫ x : ℝ, f x) *
          T ^ gmAffineIterationEta delta * (M : ℝ) ^ (n + 3)) ^ 2 *
        (2 * (T ^ (6 : ℕ)) ^ (1 - 2 * (n : ℝ))) := by
          gcongr
    _ = 2 * (16 * (2 : ℝ) ^ n * D *
          gmAffineRegionIIIKernelConstant n) ^ 2 *
        (∫ x : ℝ, f x) ^ 2 *
          ((T ^ gmAffineIterationEta delta * T ^ (n + 2)) ^ 2 *
            ((T ^ gmAffineIterationEta delta * (M : ℝ) ^ (n + 3)) ^ 2 *
              (T ^ (6 : ℕ)) ^ (1 - 2 * (n : ℝ)))) := by ring
    _ ≤ 2 * (16 * (2 : ℝ) ^ n * D *
          gmAffineRegionIIIKernelConstant n) ^ 2 *
        (∫ x : ℝ, f x) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

/-- The raw Lemma 9.2 components imply the same mass recurrence as the
fixed-Schwartz development, but now from the paper's height-dependent
Fourier profile.  The proof deliberately returns to the uncollapsed
Region-II and Region-III terms so that the powers of `T` are cancelled
before any coefficient is declared uniform. -/
theorem gmAffineLemma92ComponentsAt_to_heightMassRecurrence
    {delta Cdiv Ctail D T : ℝ} {n M : ℕ}
    (hdelta : 0 < delta) (hT : 2 ≤ T) (hCdiv : 0 ≤ Cdiv)
    (hD : 0 ≤ D) (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hMT : (M : ℝ) ≤ T ^ 4)
    (hn : (31 : ℝ) ≤ gmAffineIterationEta delta * n)
    (hproduct :
      Ctail * SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) =
        D * T ^ 2 * ∫ x : ℝ, f x)
    (hheight : GMAffineHeightFourierMassBound
      (gmAffineIterationEta delta) T n D f)
    (hcomponents : GMAffineLemma92ComponentsAt
      (gmAffineIterationEta delta) n Cdiv Ctail T
      (T ^ gmAffineIterationEta delta) (T ^ (6 : ℕ))
      (by linarith) (Real.rpow_pos_of_pos (by linarith) _) f M) :
    GMAffineLemma92MassRecurrenceAt delta Cdiv D n T
      (by linarith) f M := by
  have hTone : 1 ≤ T := by linarith
  unfold GMAffineLemma92ComponentsAt at hcomponents
  obtain ⟨M₁, M₂, M₃, hscale, hJ⟩ := hcomponents
  rcases mem_gmAffineScaleTriples.mp hscale with
    ⟨_hM₁, hM₁M, _hM₂, _hM₂M, hM₃, _hM₃M⟩
  have hQcube := gmAffineIterationQ_cube_le hdelta hTone
  have hregionI :
      gmAffineRegionIConstant n ^ 2 *
          (T ^ gmAffineIterationEta delta) ^ 3 * (M : ℝ) ^ 6 *
            (∫ x : ℝ, f x) ^ 2 ≤
        gmAffineRegionIConstant n ^ 2 * T ^ delta *
          (M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2 := by
    gcongr
  have hcoreScale := gmAffineIterationRegionIIScaleFactor_le
    hdelta hT hM₁M hM₃ hMT
  let Z : ℝ := (M : ℝ) ^ 2 *
    (Real.sqrt (∫ u : ℝ, f u ^ 2) *
      Real.sqrt (gmAffineJ
        (gmAffineTildeSchwartz
          (gmAffineSecondPoissonCutoff T
            (T ^ gmAffineIterationEta delta) M₂ M₃ /
            (T ^ gmAffineIterationEta delta))
          (by
            apply div_pos
            · exact gmAffineSecondPoissonCutoff_pos (by linarith)
                (Real.rpow_pos_of_pos (by linarith) _)
            · exact Real.rpow_pos_of_pos (by linarith) _) f) M₂))
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hcore :
      Cdiv * gmAffineRegionIICoreConstant *
          ((T ^ (6 : ℕ) + gmAffineFirstPoissonRadius M₁ M₃
            (T ^ gmAffineIterationEta delta)) ^
              gmAffineIterationEta delta *
            (T ^ gmAffineIterationEta delta) ^ 3) * Z ≤
        Cdiv * gmAffineRegionIICoreConstant * T ^ delta * Z := by
    have hK : 0 ≤ Cdiv * gmAffineRegionIICoreConstant :=
      mul_nonneg hCdiv gmAffineRegionIICoreConstant_nonneg
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcoreScale hZ) hK
  have htail := gmAffineRegionIITailSourceBound_le_heightMass
    (Ctail := Ctail) hdelta hT hCdiv f hf hproduct hMT hn
  have hnReal : (20 : ℝ) ≤ n := by
    have hetaUpper := gmAffineIterationEta_le_one delta
    have hnNonneg : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hnNat : 20 ≤ n := by exact_mod_cast hnReal
  have hhigh := gmAffineRegionIIISourceBound_le_heightMass
    hT hD f hf hMT hnNat hheight
  unfold GMAffineLemma92MassRecurrenceAt
  refine ⟨M₁, M₂, M₃, hscale, hJ.trans ?_⟩
  have hcore' :
      Cdiv * gmAffineRegionIICoreConstant *
          (T ^ (6 : ℕ) + gmAffineFirstPoissonRadius M₁ M₃
            (T ^ gmAffineIterationEta delta)) ^
              gmAffineIterationEta delta *
          (T ^ gmAffineIterationEta delta) ^ 3 * (M : ℝ) ^ 2 *
          (Real.sqrt (∫ u : ℝ, f u ^ 2) *
            Real.sqrt (gmAffineJ
              (gmAffineTildeSchwartz
                (gmAffineSecondPoissonCutoff T
                  (T ^ gmAffineIterationEta delta) M₂ M₃ /
                  (T ^ gmAffineIterationEta delta))
                (by
                  apply div_pos
                  · exact gmAffineSecondPoissonCutoff_pos (by linarith)
                      (Real.rpow_pos_of_pos (by linarith) _)
                  · exact Real.rpow_pos_of_pos (by linarith) _) f) M₂)) ≤
        Cdiv * gmAffineRegionIICoreConstant * T ^ delta *
          (M : ℝ) ^ 2 *
          (Real.sqrt (∫ u : ℝ, f u ^ 2) *
            Real.sqrt (gmAffineJ
              (gmAffineTildeSchwartz
                (gmAffineSecondPoissonCutoff T
                  (T ^ gmAffineIterationEta delta) M₂ M₃ /
                  (T ^ gmAffineIterationEta delta))
                (by
                  apply div_pos
                  · exact gmAffineSecondPoissonCutoff_pos (by linarith)
                      (Real.rpow_pos_of_pos (by linarith) _)
                  · exact Real.rpow_pos_of_pos (by linarith) _) f) M₂)) := by
    convert hcore using 1 <;> dsimp only [Z] <;> ring
  exact add_le_add (add_le_add hregionI (add_le_add hcore' htail)) hhigh

/-- Uniform height-aware Lemma 9.2 recurrence.  The derivative order and
divisor constant are selected before the physical height and before the
varying source in the Section 10 family. -/
theorem exists_n_Cdiv_forall_gmAffineLemma92HeightMassRecurrence
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ n : ℕ, ∃ Cdiv : ℝ,
      (31 : ℝ) ≤ gmAffineIterationEta delta * n ∧ 0 < Cdiv ∧
      ∀ {T : ℝ}, (hT : 2 ≤ T) → ∀ {D : ℝ}, 0 ≤ D →
      ∀ (f : SchwartzMap ℝ ℝ), (∀ x, 0 ≤ f x) →
        GMAffineIterationSupported f →
        GMAffineHeightFourierMassBound
          (gmAffineIterationEta delta) T n D f →
        ∀ {M : ℕ}, 0 < M → (M : ℝ) ≤ T ^ 4 →
          GMAffineLemma92MassRecurrenceAt delta Cdiv D n T
            (by linarith [hT]) f M := by
  have hetaPos := gmAffineIterationEta_pos hdelta
  obtain ⟨n, hn⟩ := exists_nat_mul_ge_of_pos
    (eta := gmAffineIterationEta delta) (A := 31) hetaPos
  have hnUpper : gmAffineIterationEta delta * n ≤ (n : ℝ) := by
    have hetaUpper := gmAffineIterationEta_le_one delta
    have hnNonneg : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hnReal : (31 : ℝ) ≤ n := hn.trans hnUpper
  have hnNat : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  obtain ⟨Cdiv, hCdiv, hcard⟩ :=
    exists_global_card_gmAffineFirstPoissonPairs_middle_real_le hetaPos
  refine ⟨n, Cdiv, hn, hCdiv, ?_⟩
  intro T hT D hD f hf hsupp hheight M hM hMT
  obtain ⟨Ctail, hCtail, hproduct, hdecay⟩ :=
    exists_gmAffineHeightDecayConstant (by linarith) hD hf hheight
  have hTone : 1 ≤ T := by linarith
  have hQ : 1 ≤ T ^ gmAffineIterationEta delta :=
    one_le_rpow_gmAffineIterationEta hdelta hTone
  have hY : 0 < T ^ (6 : ℕ) := pow_pos (by linarith) 6
  have hQMY := gmAffineIterationQ_mul_M_le_four_Y
    (delta := delta) hTone hMT
  have hcomponents : GMAffineLemma92ComponentsAt
      (gmAffineIterationEta delta) n Cdiv Ctail T
      (T ^ gmAffineIterationEta delta) (T ^ (6 : ℕ))
      (by linarith) (Real.rpow_pos_of_pos (by linarith) _) f M := by
    unfold GMAffineLemma92ComponentsAt
    apply exists_gmAffineJ_le_source_lemma92_components_of_constants
      hetaPos n hnNat hCdiv hCtail hTone hQ hY f hf hsupp hdecay
    · intro M₁ M₃ hM₁ hM₃ xi hxiLower hxiUpper
      exact hcard hM₁ hM₃ (Real.rpow_pos_of_pos (by linarith) _)
        hY.le xi hxiLower hxiUpper
    · exact hM
    · exact hMT
    · exact hQMY
  exact gmAffineLemma92ComponentsAt_to_heightMassRecurrence
    hdelta hT hCdiv.le hD f hf hMT hn hproduct hheight hcomponents

/-- Height-uniform finite natural-number descent for Proposition 9.1.
Unlike `exists_uniform_gmAffineJ_le_finite_descent`, this theorem permits
the source to vary with `T` and consumes the complete `(epsilon,n)`
Fourier family needed by the successive recursive budgets. -/
theorem exists_uniform_gmAffineJ_le_height_finite_descent
    (D₀ : ℝ → ℕ → ℝ) (hD₀ : ∀ epsilon n, 0 ≤ D₀ epsilon n)
    (r depth : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    (hhigh : (100 : ℝ) ≤ (3 / 2 : ℝ) ^ r * delta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T : ℝ}, 2 ≤ T → 8 * ((depth + r : ℕ) : ℝ) ≤ T →
      ∀ (f : SchwartzMap ℝ ℝ), (∀ x, 0 ≤ f x) →
        GMAffineWideDepthSupported T depth f →
        GMAffineHeightFourierMassFamilyAtDepth T D₀ depth f →
        ∀ {M : ℕ}, 0 < M → (M : ℝ) ≤ T ^ 4 →
          gmAffineJ f M ≤ C * T ^ delta *
            ((M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2 +
              (M : ℝ) ^ 4 * ∫ x : ℝ, f x ^ 2) := by
  induction r generalizing depth delta with
  | zero =>
      refine ⟨36992, by norm_num, ?_⟩
      intro T hT _hbudget f _hf _hsupp _hprofile M hM hMT
      simpa using gmAffineJ_le_proposition9_base
        (delta := delta) (T := T) (by simpa using hhigh) hT f hM hMT
  | succ r ih =>
      have hdeltaIH : 0 < 3 * delta / 2 := by positivity
      have hhighIH : (100 : ℝ) ≤
          (3 / 2 : ℝ) ^ r * (3 * delta / 2) := by
        convert hhigh using 1
        rw [pow_succ]
        ring
      obtain ⟨Cih, hCih, hIH⟩ :=
        ih (depth := depth + 1) hdeltaIH hhighIH
      have halpha : 0 < delta / 8 := by positivity
      obtain ⟨n, Cdiv, _hn, hCdiv, hfamily⟩ :=
        exists_n_Cdiv_forall_gmAffineLemma92HeightMassRecurrence halpha
      let Dcur : ℝ := (2 : ℝ) ^ depth *
        D₀ (gmAffineIterationEta (delta / 8)) n
      let Acoef : ℝ := gmAffineRegionIConstant n ^ 2
      let Bcoef : ℝ := Cdiv * gmAffineRegionIICoreConstant
      let Rcoef : ℝ := gmAffineRegionIITailMassConstant n Cdiv Dcur +
        2 * gmAffineRegionIIIEnvelopeMassConstant n Dcur ^ 2
      let C : ℝ := Acoef + Rcoef + 4 * Bcoef * Real.sqrt Cih + 1
      have hDcur : 0 ≤ Dcur := by
        dsimp only [Dcur]
        exact mul_nonneg (pow_nonneg (by norm_num) _)
          (hD₀ (gmAffineIterationEta (delta / 8)) n)
      have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
      have hBcoef : 0 ≤ Bcoef := by
        dsimp only [Bcoef]
        exact mul_nonneg hCdiv.le gmAffineRegionIICoreConstant_nonneg
      have hRcoef : 0 ≤ Rcoef := by
        dsimp only [Rcoef]
        exact add_nonneg
          (gmAffineRegionIITailMassConstant_nonneg n hCdiv.le) (by positivity)
      have hC : 0 < C := by dsimp only [C]; positivity
      refine ⟨C, hC, ?_⟩
      intro T hT hbudget f hf hsupp hprofile M hM hMT
      have hTpos : 0 < T := by linarith
      have hTone : 1 ≤ T := by linarith
      have hdepthBudget : 8 * (depth : ℝ) ≤ T := by
        have hle : (depth : ℝ) ≤ ((depth + Nat.succ r : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_add_right depth (Nat.succ r)
        linarith
      have hiter : GMAffineIterationSupported f :=
        hsupp.iterationSupported hdepthBudget hTpos
      have hratio : GMAffineHeightFourierMassBound
          (gmAffineIterationEta (delta / 8)) T n Dcur f := by
        simpa only [Dcur] using
          hprofile (gmAffineIterationEta (delta / 8))
            (gmAffineIterationEta_pos halpha) n
      have hmassRec := hfamily hT hDcur f hf hiter hratio hM hMT
      unfold GMAffineLemma92MassRecurrenceAt at hmassRec
      obtain ⟨M₁, M₂, M₃, hscale, hmassRec⟩ := hmassRec
      rcases mem_gmAffineScaleTriples.mp hscale with
        ⟨_hM₁, _hM₁M, hM₂, hM₂M, hM₃, _hM₃M⟩
      let Q : ℝ := T ^ gmAffineIterationEta (delta / 8)
      have hQ : 0 < Q := by
        dsimp only [Q]
        exact Real.rpow_pos_of_pos hTpos _
      let S : ℝ := gmAffineSecondPoissonCutoff T Q M₂ M₃ / Q
      have hS : 0 < S := by
        dsimp only [S]
        exact div_pos (gmAffineSecondPoissonCutoff_pos hTpos hQ) hQ
      have hTS : T ≤ S := by
        dsimp only [S]
        exact gmAffineSecondPoissonSmoothingScale_ge hQ
      let ft : SchwartzMap ℝ ℝ := gmAffineTildeSchwartz S hS f
      have hftNonneg : ∀ x, 0 ≤ ft x := by
        dsimp only [ft]
        exact gmAffineTildeSchwartz_nonneg S hS f hf
      have hftSupp : GMAffineWideDepthSupported T (depth + 1) ft := by
        dsimp only [ft]
        exact gmAffineTildeSchwartz_wideDepthSupported_succ
          hTpos hS hTS f hsupp
      have hftProfile :
          GMAffineHeightFourierMassFamilyAtDepth T D₀ (depth + 1) ft := by
        dsimp only [ft]
        exact gmAffineTildeSchwartz_heightFourierMassFamilyAtDepth_succ
          hTpos.le hS D₀ hD₀ f hf hprofile
      have hnextBudget :
          8 * (((depth + 1) + r : ℕ) : ℝ) ≤ T := by
        convert hbudget using 1
        push_cast
        ring
      have hM₂T : (M₂ : ℝ) ≤ T ^ 4 := by
        exact (by exact_mod_cast hM₂M : (M₂ : ℝ) ≤ M).trans hMT
      have hJft := hIH hT hnextBudget ft hftNonneg hftSupp hftProfile
        hM₂ hM₂T
      let W : ℝ := (M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2 +
        (M : ℝ) ^ 4 * ∫ x : ℝ, f x ^ 2
      let Wt : ℝ := (M₂ : ℝ) ^ 6 * (∫ x : ℝ, ft x) ^ 2 +
        (M₂ : ℝ) ^ 4 * ∫ x : ℝ, ft x ^ 2
      have hW : 0 ≤ W := by dsimp only [W]; positivity
      have hWtW : Wt ≤ 16 * W := by
        dsimp only [Wt, W, ft]
        exact gmAffineTildeSchwartz_weighted_norms_le_sixteen
          hS f hf hM₂M
      have hJft' : gmAffineJ ft M₂ ≤
          16 * Cih * T ^ (3 * delta / 2) * W := by
        calc
          gmAffineJ ft M₂ ≤ Cih * T ^ (3 * delta / 2) * Wt := by
            simpa only [Wt] using hJft
          _ ≤ Cih * T ^ (3 * delta / 2) * (16 * W) := by
            exact mul_le_mul_of_nonneg_left hWtW (by positivity)
          _ = 16 * Cih * T ^ (3 * delta / 2) * W := by ring
      have hsqrtJft : Real.sqrt (gmAffineJ ft M₂) ≤
          4 * Real.sqrt Cih * T ^ (3 * delta / 4) * Real.sqrt W :=
        sqrt_le_four_mul_sqrt_rpow_mul_sqrt hCih.le hTpos.le hJft'
      have hmixed : (M : ℝ) ^ 2 *
          Real.sqrt (∫ x : ℝ, f x ^ 2) * Real.sqrt W ≤ W := by
        dsimp only [W]
        exact gmAffine_mixed_weight_le f M
      have hpowSeven :
          T ^ (delta / 8) * T ^ (3 * delta / 4) =
            T ^ (7 * delta / 8) := by
        rw [← Real.rpow_add hTpos]
        congr 1
        ring
      have hpowSevenLe : T ^ (7 * delta / 8) ≤ T ^ delta :=
        Real.rpow_le_rpow_of_exponent_le hTone (by linarith)
      have hpowAlphaLe : T ^ (delta / 8) ≤ T ^ delta :=
        Real.rpow_le_rpow_of_exponent_le hTone (by linarith)
      let X : ℝ := (M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2
      let massSq : ℝ := (∫ x : ℝ, f x) ^ 2
      have hX : 0 ≤ X := by dsimp only [X]; positivity
      have hXW : X ≤ W := by
        dsimp only [X, W]
        exact le_add_of_nonneg_right (by positivity)
      have hmassX : massSq ≤ X := by
        have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
        have hMpow : (1 : ℝ) ≤ (M : ℝ) ^ 6 := by
          simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hMreal 6
        dsimp only [massSq, X]
        nlinarith [mul_le_mul_of_nonneg_right hMpow
          (sq_nonneg (∫ x : ℝ, f x))]
      have hbase :
          Acoef * T ^ (delta / 8) * X + Rcoef * massSq ≤
            (Acoef + Rcoef) * T ^ delta * W := by
        have hTpow : 1 ≤ T ^ delta := Real.one_le_rpow hTone hdelta.le
        have hXscaled : X ≤ T ^ delta * W := by
          calc
            X ≤ W := hXW
            _ = 1 * W := by ring
            _ ≤ T ^ delta * W := mul_le_mul_of_nonneg_right hTpow hW
        have hAterm : Acoef * T ^ (delta / 8) * X ≤
            Acoef * T ^ delta * W := by
          calc
            _ ≤ Acoef * T ^ delta * X := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpowAlphaLe hAcoef) hX
            _ ≤ Acoef * T ^ delta * W :=
              mul_le_mul_of_nonneg_left hXW (by positivity)
        have hRterm : Rcoef * massSq ≤ Rcoef * T ^ delta * W := by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left (hmassX.trans hXscaled) hRcoef
        calc
          _ ≤ Acoef * T ^ delta * W + Rcoef * T ^ delta * W :=
            add_le_add hAterm hRterm
          _ = _ := by ring
      have hcore :
          Bcoef * T ^ (delta / 8) * (M : ℝ) ^ 2 *
              (Real.sqrt (∫ x : ℝ, f x ^ 2) *
                Real.sqrt (gmAffineJ ft M₂)) ≤
            (4 * Bcoef * Real.sqrt Cih) * T ^ delta * W := by
        calc
          _ ≤ Bcoef * T ^ (delta / 8) * (M : ℝ) ^ 2 *
              (Real.sqrt (∫ x : ℝ, f x ^ 2) *
                (4 * Real.sqrt Cih * T ^ (3 * delta / 4) *
                  Real.sqrt W)) := by
            have hsqrtMul :
                Real.sqrt (∫ x : ℝ, f x ^ 2) *
                    Real.sqrt (gmAffineJ ft M₂) ≤
                  Real.sqrt (∫ x : ℝ, f x ^ 2) *
                    (4 * Real.sqrt Cih * T ^ (3 * delta / 4) *
                      Real.sqrt W) :=
              mul_le_mul_of_nonneg_left hsqrtJft (Real.sqrt_nonneg _)
            exact mul_le_mul_of_nonneg_left hsqrtMul (by positivity)
          _ = (4 * Bcoef * Real.sqrt Cih) * T ^ (7 * delta / 8) *
              ((M : ℝ) ^ 2 * Real.sqrt (∫ x : ℝ, f x ^ 2) *
                Real.sqrt W) := by rw [← hpowSeven]; ring
          _ ≤ (4 * Bcoef * Real.sqrt Cih) * T ^ (7 * delta / 8) * W :=
            mul_le_mul_of_nonneg_left hmixed (by positivity)
          _ ≤ (4 * Bcoef * Real.sqrt Cih) * T ^ delta * W := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpowSevenLe (by positivity)) hW
      have hrecNorm : gmAffineJ f M ≤
          Acoef * T ^ (delta / 8) * X +
            Bcoef * T ^ (delta / 8) * (M : ℝ) ^ 2 *
              (Real.sqrt (∫ x : ℝ, f x ^ 2) *
                Real.sqrt (gmAffineJ ft M₂)) + Rcoef * massSq := by
        convert hmassRec using 1
        all_goals
          dsimp only [Acoef, Bcoef, Rcoef, Dcur, Q, S, ft, X, massSq]
          ring
      calc
        gmAffineJ f M ≤ _ := hrecNorm
        _ ≤ (Acoef + Rcoef) * T ^ delta * W +
            (4 * Bcoef * Real.sqrt Cih) * T ^ delta * W := by
          linarith
        _ ≤ C * T ^ delta * W := by
          let K : ℝ := 4 * Bcoef * Real.sqrt Cih
          have hTW : 0 ≤ T ^ delta * W :=
            mul_nonneg (Real.rpow_nonneg hTpos.le _) hW
          have hcoeff : Acoef + Rcoef + K ≤ Acoef + Rcoef + K + 1 :=
            le_add_of_nonneg_right (by norm_num)
          calc
            _ = (Acoef + Rcoef + K) * (T ^ delta * W) := by
              dsimp only [K]
              ring
            _ ≤ (Acoef + Rcoef + K + 1) * (T ^ delta * W) :=
              mul_le_mul_of_nonneg_right hcoeff hTW
            _ = C * T ^ delta * W := by
              dsimp only [C, K]
              ring
        _ = C * T ^ delta *
            ((M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2 +
              (M : ℝ) ^ 4 * ∫ x : ℝ, f x ^ 2) := by
          rfl

/-- Correct height-family form of Guth--Maynard Proposition 9.1.  One
The constant works simultaneously for every physical height and every source
in the family, provided Lemma 8.4 supplies a uniform coefficient profile.
This is the quantifier order used by Proposition 10.1. -/
theorem gmAffine_proposition9_1_height_family_native
    (D₀ : ℝ → ℕ → ℝ) (hD₀ : ∀ epsilon n, 0 ≤ D₀ epsilon n)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ {T : ℝ}, T₀ ≤ T → ∀ (f : SchwartzMap ℝ ℝ),
        (∀ x, 0 ≤ f x) →
        GMAffineSupportedOn (1 / 4 : ℝ) (9 / 4) f →
        GMAffineHeightFourierMassFamilyAtDepth T D₀ 0 f →
        ∀ {M : ℕ}, 0 < M → (M : ℝ) ≤ T ^ 4 →
          gmAffineJ f M ≤ C * T ^ epsilon *
            ((M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2 +
              (M : ℝ) ^ 4 * ∫ x : ℝ, f x ^ 2) := by
  obtain ⟨j, hj⟩ := exists_nat_three_halves_pow_mul_ge_hundred hepsilon
  obtain ⟨C, hC, hdescent⟩ :=
    exists_uniform_gmAffineJ_le_height_finite_descent
      D₀ hD₀ j 0 hepsilon hj
  let T₀ : ℝ := max 2 (8 * (j : ℝ))
  have hT₀ : 2 ≤ T₀ := le_max_left _ _
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T hT f hf hsupp hprofile M hM hMT
  have hTtwo : 2 ≤ T := hT₀.trans hT
  have hjT : 8 * (j : ℝ) ≤ T := (le_max_right _ _).trans hT
  have hsupp₀ : GMAffineWideDepthSupported T 0 f :=
    hsupp.wideDepthSupported_zero
  exact hdescent hTtwo (by simpa using hjT) f hf hsupp₀ hprofile hM hMT

/-- Depth zero is definitionally the original height-aware profile. -/
theorem GMAffineHeightFourierMassProfile.atDepth_zero
    {epsilon T : ℝ} {D : ℕ → ℝ} {f : SchwartzMap ℝ ℝ}
    (hprofile : GMAffineHeightFourierMassProfile epsilon T D f) :
    GMAffineHeightFourierMassProfileAtDepth epsilon T D 0 f := by
  intro n
  simpa [GMAffineHeightFourierMassProfileAtDepth] using hprofile n

end RiemannZeta.GuthMaynard
