import GafniTao.HeathBrownShiftedDifference

/-!
# Positive-shift fibers of Heath-Brown's localized count

This is the exact `m = n + d` bridge in Section 3 of Heath-Brown's paper.
It connects membership in the concrete two-variable count `𝓝₂` to the
literal one-variable nearest-integer spacing set for `g_d`.
-/

open Finset

namespace GafniTao

noncomputable section

noncomputable def heathBrownPositiveShiftFiber
    (N k H K : ℕ) (f : ℝ → ℝ) (d : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n =>
    (n + d, n) ∈ heathBrownPairCountTwo N k H K f

theorem mem_heathBrownPositiveShiftFiber
    {N k H K d n : ℕ} {f : ℝ → ℝ} :
    n ∈ heathBrownPositiveShiftFiber N k H K f d ↔
      1 ≤ n ∧ n + d ≤ N ∧
        (n + d, n) ∈ heathBrownPairCountTwo N k H K f := by
  simp only [heathBrownPositiveShiftFiber, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · intro hn
    have hp := mem_heathBrownPairCountTwo.mp hn.2
    exact ⟨hn.1.1, hp.2.1, hn.2⟩
  · intro hn
    exact ⟨⟨hn.1, le_trans (Nat.le_add_right n d) hn.2.1⟩, hn.2.2⟩

theorem heathBrownPositiveShiftFiber_subset_spacingSet
    {N k H K d : ℕ} {f : ℝ → ℝ} :
    heathBrownPositiveShiftFiber N k H K f d ⊆
      heathBrownSpacingSet (N - d)
        (heathBrownShiftedDifference f (k - 2) d)
        (4 * (((H : ℝ) ^ (k - 2))⁻¹)) := by
  intro n hn
  rw [mem_heathBrownPositiveShiftFiber] at hn
  simp only [heathBrownSpacingSet, Finset.mem_filter, Finset.mem_Icc]
  have hp := (mem_heathBrownPairCountTwo.mp hn.2.2)
  refine ⟨⟨hn.1, Nat.le_sub_of_add_le hn.2.1⟩, ?_⟩
  simpa only [heathBrownShiftedDifference_nat, Nat.cast_add] using
    hp.2.2.2.2.2.1

theorem heathBrownPositiveShiftFiber_card_le_spacingSet
    {N k H K d : ℕ} {f : ℝ → ℝ} :
    (heathBrownPositiveShiftFiber N k H K f d).card ≤
      (heathBrownSpacingSet (N - d)
        (heathBrownShiftedDifference f (k - 2) d)
        (4 * (((H : ℝ) ^ (k - 2))⁻¹))).card :=
  Finset.card_le_card heathBrownPositiveShiftFiber_subset_spacingSet

theorem heathBrown_fixedShift_spacing_exact
    {N k H d : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N - d) (hd : 1 ≤ d) (hdN : d ≤ N)
    (hlambda : 0 < lambda)
    (hcoord : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Icc 0 (N : ℝ)))
    (hcoordd : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Ioo 0 (N : ℝ)))
    (hraw : ContinuousOn (iteratedDeriv (k - 1) f)
      (Set.Icc 0 (N : ℝ)))
    (hrawd : DifferentiableOn ℝ (iteratedDeriv (k - 1) f)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda) :
    let g := heathBrownShiftedDifference f (k - 2) d
    let theta := 4 * (((H : ℝ) ^ (k - 2))⁻¹)
    let mu := lambda * d / ((k - 2).factorial : ℝ)
    (heathBrownSpacingSet (N - d) g theta).card ≤
      (⌊max 0 (2 * theta / mu)⌋₊ + 1) *
        (Finset.Icc ⌊g 1 - theta⌋
          ⌈g ((N - d : ℕ) : ℝ) + theta⌉).card := by
  dsimp only
  have hmu : 0 < lambda * (d : ℝ) / ((k - 2).factorial : ℝ) := by
    positivity
  apply heathBrown_spacing_card_le_exact hN hmu
  · exact heathBrown_shiftedDifference_continuousOn hdN hcoord
  · exact heathBrown_shiftedDifference_differentiableOn hdN hcoordd
  · intro x hx
    exact (heathBrown_shiftedDifference_deriv_bounds
      (by omega : 2 ≤ k) hdN hraw hrawd hcoordd hkBounds x hx).1

theorem heathBrownPositiveShiftFiber_card_le_exact
    {N k H K d : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N - d) (hd : 1 ≤ d) (hdN : d ≤ N)
    (hlambda : 0 < lambda)
    (hcoord : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Icc 0 (N : ℝ)))
    (hcoordd : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Ioo 0 (N : ℝ)))
    (hraw : ContinuousOn (iteratedDeriv (k - 1) f)
      (Set.Icc 0 (N : ℝ)))
    (hrawd : DifferentiableOn ℝ (iteratedDeriv (k - 1) f)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda) :
    let g := heathBrownShiftedDifference f (k - 2) d
    let theta := 4 * (((H : ℝ) ^ (k - 2))⁻¹)
    let mu := lambda * d / ((k - 2).factorial : ℝ)
    (heathBrownPositiveShiftFiber N k H K f d).card ≤
      (⌊max 0 (2 * theta / mu)⌋₊ + 1) *
        (Finset.Icc ⌊g 1 - theta⌋
          ⌈g ((N - d : ℕ) : ℝ) + theta⌉).card := by
  dsimp only
  exact (heathBrownPositiveShiftFiber_card_le_spacingSet.trans
    (heathBrown_fixedShift_spacing_exact hk hN hd hdN hlambda
      hcoord hcoordd hraw hrawd hkBounds))

#print axioms mem_heathBrownPositiveShiftFiber
#print axioms heathBrownPositiveShiftFiber_subset_spacingSet
#print axioms heathBrownPositiveShiftFiber_card_le_spacingSet
#print axioms heathBrown_fixedShift_spacing_exact
#print axioms heathBrownPositiveShiftFiber_card_le_exact

end

end GafniTao
