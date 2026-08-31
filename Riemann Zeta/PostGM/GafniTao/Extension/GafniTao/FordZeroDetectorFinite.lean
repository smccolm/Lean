import GafniTao.FordZeroDetectorRectangle

/-!
# Ford's finite zeta zero detector

This module applies the finite-pole rectangle residue theorem to Ford's
translated cotangent weight and the actual zeta logarithmic derivative.  The
result keeps the central logarithmic derivative, the zeta pole, and every
nontrivial zero with analytic multiplicity as separate exact terms.
-/

open Complex Filter Set Topology Asymptotics
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def fordDetectorSingularities (eta t R : ℝ) : Finset ℂ :=
  insert (fordDetectorCenter t) (insert 1 (fordDetectorZeros eta t R))

noncomputable def fordDetectorResidueCoefficient
    (eta t : ℝ) (p : ℂ) : ℂ :=
  if p = fordDetectorCenter t then
    fordDetectorZetaLogDeriv (fordDetectorCenter t)
  else if p = 1 then
    -fordCotKernel eta (1 - fordDetectorCenter t)
  else
    (analyticVanishingOrder riemannZeta p : ℂ) *
      fordCotKernel eta (p - fordDetectorCenter t)

theorem fordDetectorRectangle_mem_nhds_iff
    {eta t R : ℝ} (heta : 0 < eta) (hR : 0 < R) {z : ℂ} :
    Rectangle (fordDetectorLower eta t R)
        (fordDetectorUpper eta t R) ∈ 𝓝 z ↔
      |z.re - 1| < eta ∧ |z.im - t| < R := by
  rw [rectangle_mem_nhds_iff, mem_reProdIm]
  simp only [fordDetectorLower, fordDetectorUpper, add_re, ofReal_re,
    mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero,
    add_im, mul_im, mul_one, zero_add]
  rw [Set.uIoo_of_le (by linarith), Set.uIoo_of_le (by linarith)]
  simp only [Set.mem_Ioo, abs_lt]
  constructor
  · rintro ⟨⟨hl, hu⟩, hli, hui⟩
    constructor <;> constructor <;> linarith
  · rintro ⟨⟨hl, hu⟩, hli, hui⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- With source-good strict boundary choices, every listed singularity is
strictly inside Ford's finite rectangle. -/
theorem fordDetectorSingularities_mem_nhds
    {eta t R : ℝ} (heta : 0 < eta) (ht : 0 < t) (hR : |t| < R)
    (hboundary : ∀ rho ∈ fordDetectorZeros eta t R,
      |rho.re - 1| < eta ∧ |rho.im - t| < R) :
    ∀ p ∈ fordDetectorSingularities eta t R,
      Rectangle (fordDetectorLower eta t R)
        (fordDetectorUpper eta t R) ∈ 𝓝 p := by
  have hRpos : 0 < R := (abs_pos.mpr (ne_of_gt ht)).trans hR
  intro p hp
  rw [fordDetectorRectangle_mem_nhds_iff heta hRpos]
  simp only [fordDetectorSingularities, Finset.mem_insert] at hp
  rcases hp with rfl | rfl | hp
  · simpa [fordDetectorCenter, heta] using hRpos
  · simpa [fordDetectorCenter, heta] using hR
  · exact hboundary p hp

/-- Away from the displayed finite singularities, the actual Ford detector
integrand is holomorphic on the complete closed rectangle. -/
theorem fordZetaDetectorIntegrand_holomorphicOn_rectangle_diff
    {eta t R : ℝ} (heta : 0 < eta) (hetaUpper : eta ≤ 1)
    (hR : 0 ≤ R) :
    HolomorphicOn (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
      (Rectangle (fordDetectorLower eta t R)
          (fordDetectorUpper eta t R) \
        (fordDetectorSingularities eta t R : Set ℂ)) := by
  intro w hw
  have hwCenter : w ≠ fordDetectorCenter t := by
    intro h
    apply hw.2
    simp [h, fordDetectorSingularities]
  have hwOne : w ≠ 1 := by
    intro h
    apply hw.2
    simp [h, fordDetectorSingularities]
  have hgeom :=
    (mem_fordDetectorRectangle_iff heta.le hR).mp hw.1
  have hweight : DifferentiableAt ℂ
      (fun z : ℂ => fordCotKernel eta (z - fordDetectorCenter t)) w := by
    have hre : |(w - fordDetectorCenter t).re| ≤ eta := by
      simpa [fordDetectorCenter] using hgeom.1
    exact differentiableAt_fordCotKernel_translate_of_abs_re_le
      heta hre hwCenter
  have hsur : sharpZetaSurrogate w ≠ 0 := by
    intro hzero
    have hzeta : riemannZeta w = 0 :=
      (sharpZetaSurrogate_eq_zero_iff hwOne).mp hzero
    have hmem : w ∈ fordDetectorZeros eta t R :=
      mem_fordDetectorZeros_of_rectangle heta.le hetaUpper hR hw.1 hzeta
    apply hw.2
    simp [fordDetectorSingularities, hmem]
  have hL : DifferentiableAt ℂ fordDetectorZetaLogDeriv w := by
    unfold fordDetectorZetaLogDeriv
    exact (differentiableAt_logDeriv_sharpZetaSurrogate hsur).sub
      ((differentiableAt_const (c := (1 : ℂ))).div
        (differentiableAt_id.sub_const (1 : ℂ))
        (sub_ne_zero.mpr hwOne))
  exact (hweight.mul hL).differentiableWithinAt

/-- Exact principal part at every listed detector singularity. -/
theorem fordZetaDetectorIntegrand_near_singularity
    {eta t R : ℝ} (heta : 0 < eta) (ht : 0 < t)
    {p : ℂ} (hp : p ∈ fordDetectorSingularities eta t R) :
    ((fordZetaDetectorIntegrand eta (fordDetectorCenter t)) - fun s =>
        fordDetectorResidueCoefficient eta t p / (s - p))
      =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hcenterOne : fordDetectorCenter t ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [fordDetectorCenter] at him
    linarith
  simp only [fordDetectorSingularities, Finset.mem_insert] at hp
  rcases hp with hcenter | hone | hp
  · subst p
    have hzeta : riemannZeta (fordDetectorCenter t) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simp [fordDetectorCenter])
    simpa [fordDetectorResidueCoefficient] using
      fordZetaDetectorIntegrand_near_center heta hcenterOne hzeta
  · subst p
    have hre : |((1 : ℂ) - fordDetectorCenter t).re| ≤ eta := by
      simp [fordDetectorCenter, heta.le]
    have hweight := differentiableAt_fordCotKernel_translate_of_abs_re_le
      heta hre hcenterOne.symm
    simpa [fordDetectorResidueCoefficient, hcenterOne.symm] using
      fordZetaDetectorIntegrand_near_one hweight
  · have hd := mem_fordDetectorZeros_data hp
    have hpCenter : p ≠ fordDetectorCenter t := by
      intro h
      subst p
      exact (riemannZeta_ne_zero_of_one_le_re
        (by simp [fordDetectorCenter])) hd.1
    have hpOne : p ≠ 1 := by
      intro h
      subst p
      exact riemannZeta_one_ne_zero hd.1
    have hweight :=
      differentiableAt_fordCotKernel_translate_at_detectorZero heta hp
    simpa [fordDetectorResidueCoefficient, hpCenter, hpOne] using
      fordZetaDetectorIntegrand_near_zero hd.1 hweight

/-- The exact finite-height residue identity underlying Ford's main zero
detector. -/
theorem fordZetaDetector_rectangleIntegral_eq_residue_sum
    {eta t R : ℝ} (heta : 0 < eta) (hetaUpper : eta ≤ 1)
    (ht : 0 < t) (hR : |t| < R)
    (hboundary : ∀ rho ∈ fordDetectorZeros eta t R,
      |rho.re - 1| < eta ∧ |rho.im - t| < R) :
    RectangleIntegral'
        (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (fordDetectorLower eta t R) (fordDetectorUpper eta t R) =
      ∑ p ∈ fordDetectorSingularities eta t R,
        fordDetectorResidueCoefficient eta t p := by
  have hRpos : 0 < R := (abs_pos.mpr (ne_of_gt ht)).trans hR
  apply residueTheorem_finset
      (S := fordDetectorSingularities eta t R)
      (A := fordDetectorResidueCoefficient eta t)
  · simp [fordDetectorLower, fordDetectorUpper]
    linarith
  · simp [fordDetectorLower, fordDetectorUpper]
    linarith
  · exact fordDetectorSingularities_mem_nhds heta ht hR hboundary
  · exact fordZetaDetectorIntegrand_holomorphicOn_rectangle_diff
      heta hetaUpper hRpos.le
  · intro p hp
    exact fordZetaDetectorIntegrand_near_singularity heta ht hp

/-- Evaluation of the finite residue sum in Ford's source notation. -/
theorem sum_fordDetectorResidueCoefficient
    {eta t R : ℝ} (ht : 0 < t) :
    (∑ p ∈ fordDetectorSingularities eta t R,
        fordDetectorResidueCoefficient eta t p) =
      fordDetectorZetaLogDeriv (fordDetectorCenter t) -
        fordCotKernel eta (1 - fordDetectorCenter t) +
        ∑ rho ∈ fordDetectorZeros eta t R,
          (analyticVanishingOrder riemannZeta rho : ℂ) *
            fordCotKernel eta (rho - fordDetectorCenter t) := by
  classical
  have hcenterOne : fordDetectorCenter t ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [fordDetectorCenter] at him
    linarith
  have honeZero : (1 : ℂ) ∉ fordDetectorZeros eta t R := by
    intro h
    exact riemannZeta_one_ne_zero (mem_fordDetectorZeros_data h).1
  have hcenterZero : fordDetectorCenter t ∉ fordDetectorZeros eta t R := by
    intro h
    exact (riemannZeta_ne_zero_of_one_le_re
      (by simp [fordDetectorCenter])) (mem_fordDetectorZeros_data h).1
  rw [fordDetectorSingularities, Finset.sum_insert]
  · rw [Finset.sum_insert honeZero]
    simp only [fordDetectorResidueCoefficient, if_pos]
    have hsum :
        (∑ p ∈ fordDetectorZeros eta t R,
          if p = fordDetectorCenter t then
            fordDetectorZetaLogDeriv (fordDetectorCenter t)
          else if p = 1 then -fordCotKernel eta (1 - fordDetectorCenter t)
          else (analyticVanishingOrder riemannZeta p : ℂ) *
            fordCotKernel eta (p - fordDetectorCenter t)) =
          ∑ p ∈ fordDetectorZeros eta t R,
            (analyticVanishingOrder riemannZeta p : ℂ) *
              fordCotKernel eta (p - fordDetectorCenter t) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpCenter : p ≠ fordDetectorCenter t := fun h =>
        hcenterZero (h ▸ hp)
      have hpOne : p ≠ 1 := fun h => honeZero (h ▸ hp)
      simp [hpCenter, hpOne]
    rw [hsum]
    rw [if_neg hcenterOne.symm]
    ring
  · simp [hcenterOne, hcenterZero]

/-- Fully evaluated finite Ford zero detector. -/
theorem fordZetaDetector_rectangleIntegral_eq_explicit_sum
    {eta t R : ℝ} (heta : 0 < eta) (hetaUpper : eta ≤ 1)
    (ht : 0 < t) (hR : |t| < R)
    (hboundary : ∀ rho ∈ fordDetectorZeros eta t R,
      |rho.re - 1| < eta ∧ |rho.im - t| < R) :
    RectangleIntegral'
        (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (fordDetectorLower eta t R) (fordDetectorUpper eta t R) =
      fordDetectorZetaLogDeriv (fordDetectorCenter t) -
        fordCotKernel eta (1 - fordDetectorCenter t) +
        ∑ rho ∈ fordDetectorZeros eta t R,
          (analyticVanishingOrder riemannZeta rho : ℂ) *
            fordCotKernel eta (rho - fordDetectorCenter t) := by
  rw [fordZetaDetector_rectangleIntegral_eq_residue_sum
    heta hetaUpper ht hR hboundary,
    sum_fordDetectorResidueCoefficient ht]

end

end GafniTao
