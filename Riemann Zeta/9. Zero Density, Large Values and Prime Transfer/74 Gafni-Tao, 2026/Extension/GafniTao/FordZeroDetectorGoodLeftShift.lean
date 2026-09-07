import GafniTao.FordZeroDetectorSelectedRemainders

/-!
# Good left edges arbitrarily close to Ford's prescribed shift

Ford's proof explicitly treats a shift `eta` for which the left edge contains
a zero by first using a nearby `eta' > eta` and then taking `eta' \downarrow
eta`.  On every finite physical rectangle only finitely many shifts are bad.
This file proves that finite-avoidance statement for the actual zeta-zero
finset; it does not assume a boundary-nonvanishing certificate.
-/

open Complex Set Finset
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

/-- The shifts whose Ford left line passes through a zero in the height box
`|Im rho| <= H`. -/
noncomputable def fordDetectorBadLeftShifts (H : ℝ) : Finset ℝ :=
  (zeroSet 0 H).image fun rho => 1 - rho.re

theorem mem_fordDetectorBadLeftShifts
    {H : ℝ} {rho : ℂ} (hrho : rho ∈ zeroSet 0 H) :
    1 - rho.re ∈ fordDetectorBadLeftShifts H := by
  exact Finset.mem_image.mpr ⟨rho, hrho, rfl⟩

/-- A finite subset of the real line misses some point in every nonempty open
interval.  The proof rescales the quantitative pigeonhole lemma
`exists_far_point`. -/
theorem exists_interval_point_not_mem_finset
    (S : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ x : ℝ, a < x ∧ x < b ∧ ∀ y ∈ S, x ≠ y := by
  classical
  let d : ℝ := (b - a) / 3
  let a' : ℝ := a + d
  let S' : Finset ℝ := S.image fun y => (y - a') / d
  have hd : 0 < d := by
    dsimp [d]
    linarith
  obtain ⟨q, hq0, hq1, hfar⟩ := exists_far_point S' 0
  refine ⟨a' + d * q, ?_, ?_, ?_⟩
  · dsimp [a']
    nlinarith
  · dsimp [a', d] at *
    nlinarith
  · intro y hy heq
    have hymem : (y - a') / d ∈ S' := by
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    have h := hfar ((y - a') / d) hymem
    have hq : q = (y - a') / d := by
      rw [eq_div_iff hd.ne']
      nlinarith
    rw [hq, sub_self, abs_zero] at h
    have hcard : 0 ≤ (S'.card : ℝ) := by
      exact_mod_cast Nat.zero_le S'.card
    have hden : 0 < 2 * ((S'.card : ℝ) + 1) := by nlinarith
    have hsep : 0 < 1 / (2 * (((S'.card : ℝ) + 1))) :=
      one_div_pos.mpr hden
    linarith

/-- There are arbitrarily close larger shifts which avoid every bad left edge
in a fixed finite height box. -/
theorem exists_fordDetector_shift_avoiding_zeros
    {eta etaMax H : ℝ} (heta : eta < etaMax) :
    ∃ eta' : ℝ, eta < eta' ∧ eta' < etaMax ∧
      ∀ rho ∈ zeroSet 0 H, eta' ≠ 1 - rho.re := by
  classical
  obtain ⟨eta', hetaLow, hetaHigh, havoid⟩ :=
    exists_interval_point_not_mem_finset
      (fordDetectorBadLeftShifts H) heta
  refine ⟨eta', hetaLow, hetaHigh, ?_⟩
  intro rho hrho
  have hmem := mem_fordDetectorBadLeftShifts hrho
  exact havoid (1 - rho.re) hmem

/-- The nearby shift supplied above gives an actual zero-free left edge of
the finite physical detector rectangle. -/
theorem exists_fordDetector_good_left_shift
    {eta etaMax yLower yUpper : ℝ}
    (heta : 0 ≤ eta) (hetaMax : eta < etaMax)
    (hetaMaxUpper : etaMax ≤ 1) (hy : yLower ≤ yUpper) :
    ∃ eta' : ℝ, eta < eta' ∧ eta' < etaMax ∧
      ∀ y ∈ Set.Icc yLower yUpper,
        riemannZeta (((1 - eta' : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
  let H : ℝ := max |yLower| |yUpper|
  obtain ⟨eta', hetaLow, hetaHigh, havoid⟩ :=
    exists_fordDetector_shift_avoiding_zeros
      (H := H) hetaMax
  have heta'0 : 0 ≤ eta' := by linarith
  have heta'Upper : eta' ≤ 1 := by linarith
  refine ⟨eta', hetaLow, hetaHigh, ?_⟩
  intro y hyIcc hzeta
  let rho : ℂ := ((1 - eta' : ℝ) : ℂ) + (y : ℂ) * I
  have hrhoRect : rho ∈ Rectangle
      (fordDetectorPhysicalLower eta' yLower)
      (fordDetectorPhysicalUpper eta' yUpper) := by
    rw [mem_fordDetectorPhysicalRectangle_iff heta'0 hy]
    dsimp [rho]
    simp only [ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, sub_zero, mul_im, mul_one, zero_add]
    constructor
    · simp [abs_of_nonneg heta'0]
    · simpa using hyIcc
  have hrhoMem : rho ∈ fordDetectorPhysicalZeros eta' yLower yUpper :=
    mem_fordDetectorPhysicalZeros_of_rectangle heta'0 heta'Upper hy
      hrhoRect hzeta
  have hrhoZeroSet : rho ∈ zeroSet 0 H :=
    (mem_fordDetectorPhysicalZeros_iff.mp hrhoMem).1
  apply havoid rho hrhoZeroSet
  dsimp [rho]
  simp

end

end GafniTao
