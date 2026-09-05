import GafniTao.Pintz2023DetectionEventualNative
import GafniTao.PintzWeightedSelection
import GafniTao.StripAssembly

/-!
# Pintz (2023), source-order zero selection

Pintz extracts widely separated *original* zero ordinates before applying
the equation-(4.12) displacement.  This order is quantitatively essential:
the loss is `O(lambda * log T)`, rather than the spurious
`O(lambda^2 * log T)` produced by selecting after arbitrary displacement.
Analytic multiplicity is retained in the extraction.
-/

open Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- A `7 lambda`-separated family remains `3 lambda`-separated after every
point moves by at most `2 lambda`.  The image map is consequently injective
on the family, so its cardinality is unchanged. -/
theorem pintz2023_separation_after_detector_shift
    {lambda : ℝ} (hlambda : 0 < lambda) (U : Finset ℝ)
    (shift : ℝ → ℝ) (hSep : IsSeparated (7 * lambda) U)
    (hShift : ∀ u ∈ U, |u - shift u| ≤ 2 * lambda) :
    IsSeparated (3 * lambda) (U.image shift) ∧
      (U.image shift).card = U.card := by
  have hDistance : ∀ u ∈ U, ∀ v ∈ U, u ≠ v →
      3 * lambda ≤ dist (shift u) (shift v) := by
    intro u hu v hv huv
    have hOriginal := hSep u hu v hv huv
    rw [Real.dist_eq] at hOriginal ⊢
    have hTriangle :
        |u - v| ≤ |u - shift u| + |shift u - shift v| + |shift v - v| := by
      calc
        |u - v| = |(u - shift u) + (shift u - shift v) + (shift v - v)| := by
          congr 1
          ring
        _ ≤ |u - shift u| + |shift u - shift v| + |shift v - v| := by
          exact (abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)
    have hLast : |shift v - v| ≤ 2 * lambda := by
      simpa only [abs_sub_comm] using hShift v hv
    nlinarith [hTriangle, hShift u hu, hLast]
  have hInj : Set.InjOn shift (↑U : Set ℝ) := by
    intro u hu v hv huv
    by_contra hne
    have h := hDistance u hu v hv hne
    rw [huv, dist_self] at h
    linarith
  constructor
  · intro x hx y hy hxy
    rw [Finset.mem_image] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    have huv : u ≠ v := by
      intro huv
      subst v
      exact hxy rfl
    exact hDistance u hu v hv huv
  · exact Finset.card_image_iff.mpr hInj

/-- The literal source-order selection behind Pintz (4.12).  Original zero
ordinates are extracted at spacing `7 lambda`, then displaced by at most
`2 lambda`; the final detected ordinates have spacing `3 lambda`.  The
displayed loss has one, and only one, factor of order `lambda` in addition
to the local-zero `log T` factor. -/
theorem exists_pintz2023_source_order_variable_selection_subset
    {xi T V lambda H : ℝ} {X Y : ℕ} (S : Finset ℂ)
    (hS : S ⊆ zeroSet (1 - xi) T)
    (hSourceLower : ∀ rho ∈ S, H < |rho.im|)
    (hsigma : 0 ≤ 1 - xi)
    (hT : max (Real.exp 2) 8 ≤ T)
    (hlambda : 0 < lambda)
    (hDetected : ∀ rho ∈ S,
      ∃ u : ℝ, |rho.im - u| ≤ 2 * lambda ∧
        V ≤ ‖pintz2023TruncatedPolynomial X Y
          (1 - (1 - rho.re) + 1 / lambda) u‖) :
    ∃ W : Finset ℝ, ∃ etaAt : ℝ → ℝ,
      IsSeparated (3 * lambda) W ∧
      (∑ rho ∈ S, zeroMultiplicity rho) ≤
        (2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
          (2 * (2 * Nat.ceil (7 * lambda) + 1)) * W.card ∧
      (∀ u ∈ W, etaAt u ∈ Set.Icc 0 xi) ∧
      (∀ u ∈ W, H - 2 * lambda < |u|) ∧
      (∀ u ∈ W, |u| ≤ T + 2 * lambda) ∧
      ∀ u ∈ W,
        V ≤ ‖pintz2023TruncatedPolynomial X Y
          (1 - etaAt u + 1 / lambda) u‖ := by
  classical
  let L : ℕ := Nat.ceil (globalLocalZeroLogConstant * Real.log T)
  have hLocal : ∀ z : ℤ,
      ∑ rho ∈ S.filter
          (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
        zeroMultiplicity rho ≤ L := by
    intro z
    have hSub :
        S.filter (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1) ⊆
          (zeroSet (1 - xi) T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1) := by
      intro rho hrho
      rw [Finset.mem_filter] at hrho ⊢
      exact ⟨hS hrho.1, hrho.2⟩
    have hSum :
        ∑ rho ∈ S.filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho ≤
        ∑ rho ∈ (zeroSet (1 - xi) T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSub
      intro rho hrho hnot
      exact Nat.zero_le _
    have hFullReal := zeroLocalUnitBin_multiplicity_le_global_log
      (1 - xi) T z hsigma hT
    change
      ((∑ rho ∈ (zeroSet (1 - xi) T).filter
          (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
        zeroMultiplicity rho : ℕ) : ℝ) ≤
        globalLocalZeroLogConstant * Real.log T at hFullReal
    have hCeil : globalLocalZeroLogConstant * Real.log T ≤ (L : ℝ) :=
      Nat.le_ceil _
    have hFull :
        ∑ rho ∈ (zeroSet (1 - xi) T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho ≤ L := by
      exact_mod_cast hFullReal.trans hCeil
    exact hSum.trans hFull
  obtain ⟨U, hU, hSepU, hCountU⟩ :=
    exists_pintz_scaledSeparated_shifted_weighted
      S zeroMultiplicity Complex.im Complex.im
      (H := 0) (G := 7 * lambda) (by positivity) L
      (by intro rho hrho; simp) hLocal
  have hPreimage : ∀ u ∈ U, ∃ rho ∈ S, rho.im = u := by
    intro u hu
    exact Finset.mem_image.mp (hU hu)
  let source : ℝ → ℂ := fun u =>
    if hu : u ∈ U then Classical.choose (hPreimage u hu) else 0
  have hSourceMem : ∀ u ∈ U, source u ∈ S := by
    intro u hu
    dsimp only [source]
    rw [dif_pos hu]
    exact (Classical.choose_spec (hPreimage u hu)).1
  have hSourceIm : ∀ u ∈ U, (source u).im = u := by
    intro u hu
    dsimp only [source]
    rw [dif_pos hu]
    exact (Classical.choose_spec (hPreimage u hu)).2
  let shift : ℝ → ℝ := fun u =>
    if hu : u ∈ U then Classical.choose (hDetected (source u) (hSourceMem u hu))
    else u
  have hShift : ∀ u ∈ U, |u - shift u| ≤ 2 * lambda := by
    intro u hu
    have hd := (Classical.choose_spec
      (hDetected (source u) (hSourceMem u hu))).1
    calc
      |u - shift u| = |(source u).im - shift u| := by
        rw [hSourceIm u hu]
      _ = |(source u).im - Classical.choose
          (hDetected (source u) (hSourceMem u hu))| := by
        simp only [shift, dif_pos hu]
      _ ≤ 2 * lambda := hd
  have hLargeU : ∀ u ∈ U,
      V ≤ ‖pintz2023TruncatedPolynomial X Y
        (1 - (1 - (source u).re) + 1 / lambda) (shift u)‖ := by
    intro u hu
    dsimp only [shift]
    rw [dif_pos hu]
    exact (Classical.choose_spec
      (hDetected (source u) (hSourceMem u hu))).2
  let W : Finset ℝ := U.image shift
  have hSepCard := pintz2023_separation_after_detector_shift
    hlambda U shift hSepU hShift
  have hPreW : ∀ w ∈ W, ∃ u ∈ U, shift u = w := by
    intro w hw
    exact Finset.mem_image.mp hw
  let original : ℝ → ℝ := fun w =>
    if hw : w ∈ W then Classical.choose (hPreW w hw) else w
  have hOriginalMem : ∀ w ∈ W, original w ∈ U := by
    intro w hw
    dsimp only [original]
    rw [dif_pos hw]
    exact (Classical.choose_spec (hPreW w hw)).1
  have hOriginalShift : ∀ w ∈ W, shift (original w) = w := by
    intro w hw
    dsimp only [original]
    rw [dif_pos hw]
    exact (Classical.choose_spec (hPreW w hw)).2
  let etaAt : ℝ → ℝ := fun w => 1 - (source (original w)).re
  have hEta : ∀ w ∈ W, etaAt w ∈ Set.Icc 0 xi := by
    intro w hw
    have hrho := hS (hSourceMem (original w) (hOriginalMem w hw))
    change source (original w) ∈ zerosInRect (1 - xi) 1 (-T) T at hrho
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle] at hrho
    dsimp only [etaAt]
    exact ⟨by linarith [hrho.1.2.1], by linarith [hrho.1.1]⟩
  have hHeight : ∀ w ∈ W, |w| ≤ T + 2 * lambda := by
    intro w hw
    let u := original w
    have hu : u ∈ U := hOriginalMem w hw
    have hrho := hS (hSourceMem u hu)
    change source u ∈ zerosInRect (1 - xi) 1 (-T) T at hrho
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle] at hrho
    have him : |(source u).im| ≤ T :=
      abs_le.mpr ⟨hrho.1.2.2.1, hrho.1.2.2.2⟩
    have hdisp := hShift u hu
    have huHeight : |u| ≤ T := by
      rw [← hSourceIm u hu]
      exact him
    have hwDisp : |w - u| ≤ 2 * lambda := by
      rw [abs_sub_comm, ← hOriginalShift w hw]
      exact hdisp
    calc
      |w| = |u + (w - u)| := by congr 1; ring
      _ ≤ |u| + |w - u| := abs_add_le _ _
      _ ≤ T + 2 * lambda := add_le_add huHeight hwDisp
  have hHeightLower : ∀ w ∈ W, H - 2 * lambda < |w| := by
    intro w hw
    let u := original w
    have hu : u ∈ U := hOriginalMem w hw
    have hsourceLower := hSourceLower (source u) (hSourceMem u hu)
    have hdisp := hShift u hu
    have hwShift : shift u = w := hOriginalShift w hw
    have hsourceDisp : |(source u).im - w| ≤ 2 * lambda := by
      rw [hSourceIm u hu, ← hwShift]
      exact hdisp
    have htriangle : |(source u).im| ≤ |w| + |(source u).im - w| := by
      calc
        |(source u).im| = |w + ((source u).im - w)| := by congr 1; ring
        _ ≤ |w| + |(source u).im - w| := abs_add_le _ _
    linarith
  have hLarge : ∀ w ∈ W,
      V ≤ ‖pintz2023TruncatedPolynomial X Y
        (1 - etaAt w + 1 / lambda) w‖ := by
    intro w hw
    have h := hLargeU (original w) (hOriginalMem w hw)
    rw [hOriginalShift w hw] at h
    simpa only [etaAt] using h
  refine ⟨W, etaAt, hSepCard.1, ?_, hEta, hHeightLower, hHeight, hLarge⟩
  have hCard : W.card = U.card := hSepCard.2
  dsimp only [L] at hCountU
  simpa [W, hCard] using hCountU

#print axioms pintz2023_separation_after_detector_shift
#print axioms exists_pintz2023_source_order_variable_selection_subset

end

end GafniTao
