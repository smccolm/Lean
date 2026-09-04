import GafniTao.HeathBrownShiftDecomposition

/-!
# The finite shift range

The half-unit unwrapping of the last derivative coordinate forces every
nonempty positive-shift fiber into Heath-Brown's literal range

`1 ≤ d ≤ min(N, floor(4 (k-1)! / (lambda H^(k-1))))`.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def heathBrownShiftBound
    (N k H : ℕ) (lambda : ℝ) : ℕ :=
  min N ⌊4 * ((k - 1).factorial : ℝ) /
    (lambda * (H : ℝ) ^ (k - 1))⌋₊

theorem heathBrownShiftBound_le_N
    (N k H : ℕ) (lambda : ℝ) :
    heathBrownShiftBound N k H lambda ≤ N :=
  min_le_left _ _

theorem heathBrownPositiveShiftFiber_shift_le
    {N k H d n : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4)
    (hg : ContinuousOn
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda)
    (hn : n ∈ heathBrownPositiveShiftFiber N k H
      (heathBrownBlockParameter A lambda N) f d) :
    d ≤ heathBrownShiftBound N k H lambda := by
  have hn' := mem_heathBrownPositiveShiftFiber.mp hn
  have hp := hn'.2.2
  have hsep := heathBrown_actualBlock_pair_source_separation
    hk hA hlambda hsmall hg hgd hkBounds hp
  have hdN : d ≤ N :=
    le_trans (Nat.le_add_left d n) hn'.2.1
  have hdReal : (d : ℝ) ≤
      4 * ((k - 1).factorial : ℝ) /
        (lambda * (H : ℝ) ^ (k - 1)) := by
    simpa only [Nat.cast_add, add_sub_cancel_left, abs_of_nonneg,
      Nat.cast_nonneg] using hsep
  have hfloor : d ≤ ⌊4 * ((k - 1).factorial : ℝ) /
      (lambda * (H : ℝ) ^ (k - 1))⌋₊ := by
    exact Nat.le_floor hdReal
  exact (Nat.le_min).2 ⟨hdN, hfloor⟩

theorem heathBrownPositiveShiftFiber_eq_empty_of_shiftBound_lt
    {N k H d : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4)
    (hg : ContinuousOn
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda)
    (hd : heathBrownShiftBound N k H lambda < d) :
    heathBrownPositiveShiftFiber N k H
      (heathBrownBlockParameter A lambda N) f d = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  obtain ⟨n, hn⟩ := hne
  exact (not_le_of_gt hd) (heathBrownPositiveShiftFiber_shift_le
    hk hA hlambda hsmall hg hgd hkBounds hn)

theorem heathBrown_positiveShift_sum_restrict
    {N k H : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4)
    (hg : ContinuousOn
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda) :
    (∑ d ∈ Finset.Icc 1 N,
        (heathBrownPositiveShiftFiber N k H
          (heathBrownBlockParameter A lambda N) f d).card) =
      ∑ d ∈ Finset.Icc 1 (heathBrownShiftBound N k H lambda),
        (heathBrownPositiveShiftFiber N k H
          (heathBrownBlockParameter A lambda N) f d).card := by
  symm
  apply Finset.sum_subset
  · intro d hd
    rw [Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1, hd.2.trans (heathBrownShiftBound_le_N N k H lambda)⟩
  · intro d hdBig hdSmall
    have hdBig' := Finset.mem_Icc.mp hdBig
    have hdOut : heathBrownShiftBound N k H lambda < d := by
      by_contra hnot
      exact hdSmall (Finset.mem_Icc.mpr ⟨hdBig'.1, Nat.le_of_not_gt hnot⟩)
    rw [heathBrownPositiveShiftFiber_eq_empty_of_shiftBound_lt
      hk hA hlambda hsmall hg hgd hkBounds hdOut]
    rfl

theorem heathBrownPairCountTwo_card_le_restricted_shift_sum
    (N k H : ℕ) (f : ℝ → ℝ) {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4)
    (hg : ContinuousOn
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda) :
    (heathBrownPairCountTwo N k H
      (heathBrownBlockParameter A lambda N) f).card ≤
      N + 2 * ∑ d ∈ Finset.Icc 1 (heathBrownShiftBound N k H lambda),
        (heathBrownPositiveShiftFiber N k H
          (heathBrownBlockParameter A lambda N) f d).card := by
  rw [← heathBrown_positiveShift_sum_restrict hk hA hlambda hsmall
    hg hgd hkBounds]
  exact heathBrownPairCountTwo_card_le_shift_sum N k H
    (heathBrownBlockParameter A lambda N) f

#print axioms heathBrownShiftBound_le_N
#print axioms heathBrownPositiveShiftFiber_shift_le
#print axioms heathBrownPositiveShiftFiber_eq_empty_of_shiftBound_lt
#print axioms heathBrown_positiveShift_sum_restrict
#print axioms heathBrownPairCountTwo_card_le_restricted_shift_sum

end

end GafniTao
