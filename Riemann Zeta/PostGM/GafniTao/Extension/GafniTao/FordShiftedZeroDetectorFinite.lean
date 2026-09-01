import GafniTao.FordShiftedZeroDetectorRectangle

/-!
# Finite Ford detector at `sigma + it`

This is the shifted-centre analogue of the finite physical detector.  The
zeta pole at `1` is retained explicitly with multiplicity `-1`; this is the
term omitted in the printed statement of Ford's shifted real-part lemma.
-/

open Complex Filter Set Topology Asymptotics
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def fordShiftedDetectorSingularities
    (sigma eta t R : ℝ) : Finset ℂ :=
  insert (fordShiftedDetectorCenter sigma t)
    (insert 1 (fordShiftedDetectorZeros sigma eta t R))

noncomputable def fordShiftedDetectorResidueCoefficient
    (sigma eta t : ℝ) (p : ℂ) : ℂ :=
  if p = fordShiftedDetectorCenter sigma t then
    fordDetectorZetaLogDeriv (fordShiftedDetectorCenter sigma t)
  else if p = 1 then
    -fordCotKernel eta (1 - fordShiftedDetectorCenter sigma t)
  else
    (analyticVanishingOrder riemannZeta p : ℂ) *
      fordCotKernel eta (p - fordShiftedDetectorCenter sigma t)

theorem fordShiftedDetectorRectangle_mem_nhds_iff
    {sigma eta t R : ℝ} (heta : 0 < eta) (hR : 0 < R) {z : ℂ} :
    Rectangle (fordShiftedDetectorLower sigma eta t R)
        (fordShiftedDetectorUpper sigma eta t R) ∈ 𝓝 z ↔
      |z.re - sigma| < eta ∧ |z.im - t| < R := by
  rw [rectangle_mem_nhds_iff, mem_reProdIm]
  simp only [fordShiftedDetectorLower, fordShiftedDetectorUpper, add_re,
    ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero,
    add_im, mul_im, mul_one, zero_add]
  rw [Set.uIoo_of_le (by linarith), Set.uIoo_of_le (by linarith)]
  simp only [Set.mem_Ioo, abs_lt]
  constructor
  · rintro ⟨⟨hl, hu⟩, hli, hui⟩
    constructor <;> constructor <;> linarith
  · rintro ⟨⟨hl, hu⟩, hli, hui⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem fordShiftedDetectorSingularities_mem_nhds
    {sigma eta t R : ℝ} (hsigma : 1 ≤ sigma) (heta : 0 < eta)
    (ht : 0 < t) (hPole : sigma - 1 < eta) (hR : |t| < R)
    (hboundary : ∀ rho ∈ fordShiftedDetectorZeros sigma eta t R,
      |rho.re - sigma| < eta ∧ |rho.im - t| < R) :
    ∀ p ∈ fordShiftedDetectorSingularities sigma eta t R,
      Rectangle (fordShiftedDetectorLower sigma eta t R)
        (fordShiftedDetectorUpper sigma eta t R) ∈ 𝓝 p := by
  have hRpos : 0 < R := (abs_pos.mpr (ne_of_gt ht)).trans hR
  intro p hp
  rw [fordShiftedDetectorRectangle_mem_nhds_iff heta hRpos]
  simp only [fordShiftedDetectorSingularities, Finset.mem_insert] at hp
  rcases hp with rfl | rfl | hp
  · simp [fordShiftedDetectorCenter, heta, hRpos]
  · constructor
    · rw [show ((1 : ℂ).re - sigma) = 1 - sigma by simp,
        abs_of_nonpos (by linarith)]
      linarith
    · simpa [abs_of_pos ht] using hR
  · exact hboundary p hp

theorem fordZetaShiftedDetectorIntegrand_holomorphicOn_rectangle_diff
    {sigma eta t R : ℝ} (heta : 0 < eta)
    (hR : 0 ≤ R) (hleft : -1 ≤ sigma - eta) :
    HolomorphicOn
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (Rectangle (fordShiftedDetectorLower sigma eta t R)
          (fordShiftedDetectorUpper sigma eta t R) \
        (fordShiftedDetectorSingularities sigma eta t R : Set ℂ)) := by
  intro w hw
  have hwCenter : w ≠ fordShiftedDetectorCenter sigma t := by
    intro h
    apply hw.2
    simp [h, fordShiftedDetectorSingularities]
  have hwOne : w ≠ 1 := by
    intro h
    apply hw.2
    simp [h, fordShiftedDetectorSingularities]
  have hgeom :=
    (mem_fordShiftedDetectorRectangle_iff heta.le hR).mp hw.1
  have hweight : DifferentiableAt ℂ
      (fun z : ℂ => fordCotKernel eta
        (z - fordShiftedDetectorCenter sigma t)) w := by
    have hre :
        |(w - fordShiftedDetectorCenter sigma t).re| ≤ eta := by
      simpa [fordShiftedDetectorCenter] using hgeom.1
    exact differentiableAt_fordCotKernel_translate_of_abs_re_le
      heta hre hwCenter
  have hsur : sharpZetaSurrogate w ≠ 0 := by
    intro hzero
    have hzeta : riemannZeta w = 0 :=
      (sharpZetaSurrogate_eq_zero_iff hwOne).mp hzero
    have hmem : w ∈ fordShiftedDetectorZeros sigma eta t R :=
      mem_fordShiftedDetectorZeros_of_rectangle
        heta.le hR hleft hw.1 hzeta
    apply hw.2
    simp [fordShiftedDetectorSingularities, hmem]
  have hL : DifferentiableAt ℂ fordDetectorZetaLogDeriv w := by
    unfold fordDetectorZetaLogDeriv
    exact (differentiableAt_logDeriv_sharpZetaSurrogate hsur).sub
      ((differentiableAt_const (c := (1 : ℂ))).div
        (differentiableAt_id.sub_const (1 : ℂ))
        (sub_ne_zero.mpr hwOne))
  exact (hweight.mul hL).differentiableWithinAt

theorem fordZetaShiftedDetectorIntegrand_near_singularity
    {sigma eta t R : ℝ} (hsigma : 1 ≤ sigma) (heta : 0 < eta)
    (ht : 0 < t) (hPole : sigma - 1 ≤ eta)
    {p : ℂ} (hp : p ∈
      fordShiftedDetectorSingularities sigma eta t R) :
    ((fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t)) - fun s =>
      fordShiftedDetectorResidueCoefficient sigma eta t p / (s - p))
      =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hcenterOne : fordShiftedDetectorCenter sigma t ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [fordShiftedDetectorCenter] at him
    linarith
  simp only [fordShiftedDetectorSingularities, Finset.mem_insert] at hp
  rcases hp with hcenter | hone | hp
  · subst p
    have hzeta : riemannZeta (fordShiftedDetectorCenter sigma t) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simpa using hsigma)
    simpa [fordShiftedDetectorResidueCoefficient] using
      fordZetaDetectorIntegrand_near_center heta hcenterOne hzeta
  · subst p
    have hre :
        |((1 : ℂ) - fordShiftedDetectorCenter sigma t).re| ≤ eta := by
      simp [fordShiftedDetectorCenter]
      rw [abs_of_nonpos]
      · linarith
      · linarith
    have hweight := differentiableAt_fordCotKernel_translate_of_abs_re_le
      heta hre hcenterOne.symm
    simpa [fordShiftedDetectorResidueCoefficient, hcenterOne.symm] using
      fordZetaDetectorIntegrand_near_one hweight
  · have hd := mem_fordShiftedDetectorZeros_data hp
    have hpCenter : p ≠ fordShiftedDetectorCenter sigma t := by
      intro h
      subst p
      exact (riemannZeta_ne_zero_of_one_le_re
        (by simpa using hsigma)) hd.1
    have hpOne : p ≠ 1 := by
      intro h
      subst p
      exact riemannZeta_one_ne_zero hd.1
    have hweight :=
      differentiableAt_fordCotKernel_translate_at_shiftedDetectorZero
        hsigma heta hp
    simpa [fordShiftedDetectorResidueCoefficient, hpCenter, hpOne] using
      fordZetaDetectorIntegrand_near_zero hd.1 hweight

theorem fordZetaShiftedDetector_rectangleIntegral_eq_residue_sum
    {sigma eta t R : ℝ} (hsigma : 1 ≤ sigma) (heta : 0 < eta)
    (ht : 0 < t) (hPole : sigma - 1 < eta) (hR : |t| < R)
    (hleft : -1 ≤ sigma - eta)
    (hboundary : ∀ rho ∈ fordShiftedDetectorZeros sigma eta t R,
      |rho.re - sigma| < eta ∧ |rho.im - t| < R) :
    RectangleIntegral'
        (fordZetaDetectorIntegrand eta
          (fordShiftedDetectorCenter sigma t))
        (fordShiftedDetectorLower sigma eta t R)
        (fordShiftedDetectorUpper sigma eta t R) =
      ∑ p ∈ fordShiftedDetectorSingularities sigma eta t R,
        fordShiftedDetectorResidueCoefficient sigma eta t p := by
  have hRpos : 0 < R := (abs_pos.mpr (ne_of_gt ht)).trans hR
  apply residueTheorem_finset
      (S := fordShiftedDetectorSingularities sigma eta t R)
      (A := fordShiftedDetectorResidueCoefficient sigma eta t)
  · simp [fordShiftedDetectorLower, fordShiftedDetectorUpper]
    linarith
  · simp [fordShiftedDetectorLower, fordShiftedDetectorUpper]
    linarith
  · exact fordShiftedDetectorSingularities_mem_nhds
      hsigma heta ht hPole hR hboundary
  · exact fordZetaShiftedDetectorIntegrand_holomorphicOn_rectangle_diff
      heta hRpos.le hleft
  · intro p hp
    exact fordZetaShiftedDetectorIntegrand_near_singularity
      hsigma heta ht hPole.le hp

theorem sum_fordShiftedDetectorResidueCoefficient
    {sigma eta t R : ℝ} (hsigma : 1 ≤ sigma) (ht : 0 < t) :
    (∑ p ∈ fordShiftedDetectorSingularities sigma eta t R,
        fordShiftedDetectorResidueCoefficient sigma eta t p) =
      fordDetectorZetaLogDeriv (fordShiftedDetectorCenter sigma t) -
        fordCotKernel eta (1 - fordShiftedDetectorCenter sigma t) +
        ∑ rho ∈ fordShiftedDetectorZeros sigma eta t R,
          (analyticVanishingOrder riemannZeta rho : ℂ) *
            fordCotKernel eta
              (rho - fordShiftedDetectorCenter sigma t) := by
  classical
  have hcenterOne : fordShiftedDetectorCenter sigma t ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [fordShiftedDetectorCenter] at him
    linarith
  have honeZero :
      (1 : ℂ) ∉ fordShiftedDetectorZeros sigma eta t R := by
    intro h
    exact riemannZeta_one_ne_zero
      (mem_fordShiftedDetectorZeros_data h).1
  have hcenterZero :
      fordShiftedDetectorCenter sigma t ∉
        fordShiftedDetectorZeros sigma eta t R := by
    intro h
    exact (riemannZeta_ne_zero_of_one_le_re
      (by simpa using hsigma))
      (mem_fordShiftedDetectorZeros_data h).1
  rw [fordShiftedDetectorSingularities, Finset.sum_insert]
  · rw [Finset.sum_insert honeZero]
    simp only [fordShiftedDetectorResidueCoefficient, if_pos]
    have hsum :
        (∑ p ∈ fordShiftedDetectorZeros sigma eta t R,
          if p = fordShiftedDetectorCenter sigma t then
            fordDetectorZetaLogDeriv (fordShiftedDetectorCenter sigma t)
          else if p = 1 then
            -fordCotKernel eta (1 - fordShiftedDetectorCenter sigma t)
          else (analyticVanishingOrder riemannZeta p : ℂ) *
            fordCotKernel eta
              (p - fordShiftedDetectorCenter sigma t)) =
          ∑ p ∈ fordShiftedDetectorZeros sigma eta t R,
            (analyticVanishingOrder riemannZeta p : ℂ) *
              fordCotKernel eta
                (p - fordShiftedDetectorCenter sigma t) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpCenter : p ≠ fordShiftedDetectorCenter sigma t := fun h =>
        hcenterZero (h ▸ hp)
      have hpOne : p ≠ 1 := fun h => honeZero (h ▸ hp)
      simp [hpCenter, hpOne]
    rw [hsum, if_neg hcenterOne.symm]
    ring
  · simp [hcenterOne, hcenterZero]

/-- Fully evaluated finite shifted Ford detector, with the pole contribution
visible. -/
theorem fordZetaShiftedDetector_rectangleIntegral_eq_explicit_sum
    {sigma eta t R : ℝ} (hsigma : 1 ≤ sigma) (heta : 0 < eta)
    (ht : 0 < t) (hPole : sigma - 1 < eta) (hR : |t| < R)
    (hleft : -1 ≤ sigma - eta)
    (hboundary : ∀ rho ∈ fordShiftedDetectorZeros sigma eta t R,
      |rho.re - sigma| < eta ∧ |rho.im - t| < R) :
    RectangleIntegral'
        (fordZetaDetectorIntegrand eta
          (fordShiftedDetectorCenter sigma t))
        (fordShiftedDetectorLower sigma eta t R)
        (fordShiftedDetectorUpper sigma eta t R) =
      fordDetectorZetaLogDeriv (fordShiftedDetectorCenter sigma t) -
        fordCotKernel eta (1 - fordShiftedDetectorCenter sigma t) +
        ∑ rho ∈ fordShiftedDetectorZeros sigma eta t R,
          (analyticVanishingOrder riemannZeta rho : ℂ) *
            fordCotKernel eta
              (rho - fordShiftedDetectorCenter sigma t) := by
  rw [fordZetaShiftedDetector_rectangleIntegral_eq_residue_sum
    hsigma heta ht hPole hR hleft hboundary,
    sum_fordShiftedDetectorResidueCoefficient hsigma ht]

end

end GafniTao
