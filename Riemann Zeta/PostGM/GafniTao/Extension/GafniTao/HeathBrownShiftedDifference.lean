import GafniTao.HeathBrownBlockSpread
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Fixed-shift derivative coordinate

For a positive shift `d`, Heath-Brown applies the elementary spacing lemma
to

`g_d(x) = (f^(k-2)(x+d) - f^(k-2)(x)) / (k-2)!`.

This file records the literal function, its derivative, and the derivative
bounds obtained by applying the mean-value theorem to `f^(k-1)`.  No
asymptotic notation is introduced at this layer.
-/

namespace GafniTao

noncomputable section

noncomputable def heathBrownShiftedDifference
    (f : ℝ → ℝ) (j d : ℕ) (x : ℝ) : ℝ :=
  heathBrownDerivativeCoordinate f j (x + d) -
    heathBrownDerivativeCoordinate f j x

theorem heathBrownShiftedDifference_nat
    (f : ℝ → ℝ) (j d n : ℕ) :
    heathBrownShiftedDifference f j d n =
      heathBrownDerivativeCoordinate f j (n + d) -
        heathBrownDerivativeCoordinate f j n := by
  unfold heathBrownShiftedDifference
  norm_num

theorem deriv_heathBrownShiftedDifference
    (f : ℝ → ℝ) (j d : ℕ) (x : ℝ)
    (hleft : DifferentiableAt ℝ (heathBrownDerivativeCoordinate f j) x)
    (hright : DifferentiableAt ℝ (heathBrownDerivativeCoordinate f j) (x + d)) :
    deriv (heathBrownShiftedDifference f j d) x =
      (iteratedDeriv (j + 1) f (x + d) -
        iteratedDeriv (j + 1) f x) / (j.factorial : ℝ) := by
  unfold heathBrownShiftedDifference
  have hr := hright.hasDerivAt.comp_add_const x (d : ℝ)
  have hs := hr.sub hleft.hasDerivAt
  calc
    deriv (fun y => heathBrownDerivativeCoordinate f j (y + ↑d) -
        heathBrownDerivativeCoordinate f j y) x =
        deriv (heathBrownDerivativeCoordinate f j) (x + d) -
          deriv (heathBrownDerivativeCoordinate f j) x := hs.deriv
    _ = (iteratedDeriv (j + 1) f (x + d) -
        iteratedDeriv (j + 1) f x) / (j.factorial : ℝ) := by
      rw [deriv_heathBrownDerivativeCoordinate,
        deriv_heathBrownDerivativeCoordinate]
      ring

theorem heathBrown_shiftedDifference_continuousOn
    {N j d : ℕ} {f : ℝ → ℝ}
    (hdN : d ≤ N)
    (hcoord : ContinuousOn (heathBrownDerivativeCoordinate f j)
      (Set.Icc 0 (N : ℝ))) :
    ContinuousOn (heathBrownShiftedDifference f j d)
      (Set.Icc 0 ((N - d : ℕ) : ℝ)) := by
  let s : Set ℝ := Set.Icc 0 ((N - d : ℕ) : ℝ)
  have hsub : s ⊆ Set.Icc (0 : ℝ) N := by
    intro x hx
    change x ∈ Set.Icc (0 : ℝ) ((N - d : ℕ) : ℝ) at hx
    rw [Nat.cast_sub hdN] at hx
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    exact ⟨hx.1, hx.2.trans (sub_le_self _ hd0)⟩
  have hmaps : Set.MapsTo (fun x : ℝ => x + d) s (Set.Icc 0 (N : ℝ)) := by
    intro x hx
    change x ∈ Set.Icc (0 : ℝ) ((N - d : ℕ) : ℝ) at hx
    rw [Nat.cast_sub hdN] at hx
    change x + (d : ℝ) ∈ Set.Icc (0 : ℝ) (N : ℝ)
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    constructor
    · exact add_nonneg hx.1 hd0
    · linarith only [hx.2]
  exact (hcoord.comp' (continuousOn_id.add continuousOn_const) hmaps).sub
    (hcoord.mono hsub)

theorem heathBrown_shiftedDifference_differentiableOn
    {N j d : ℕ} {f : ℝ → ℝ}
    (hdN : d ≤ N)
    (hcoord : DifferentiableOn ℝ (heathBrownDerivativeCoordinate f j)
      (Set.Ioo 0 (N : ℝ))) :
    DifferentiableOn ℝ (heathBrownShiftedDifference f j d)
      (Set.Ioo 0 ((N - d : ℕ) : ℝ)) := by
  let s : Set ℝ := Set.Ioo 0 ((N - d : ℕ) : ℝ)
  have hsub : s ⊆ Set.Ioo (0 : ℝ) N := by
    intro x hx
    change x ∈ Set.Ioo (0 : ℝ) ((N - d : ℕ) : ℝ) at hx
    rw [Nat.cast_sub hdN] at hx
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    exact ⟨hx.1, hx.2.trans_le (sub_le_self _ hd0)⟩
  have hmaps : Set.MapsTo (fun x : ℝ => x + d) s (Set.Ioo 0 (N : ℝ)) := by
    intro x hx
    change x ∈ Set.Ioo (0 : ℝ) ((N - d : ℕ) : ℝ) at hx
    rw [Nat.cast_sub hdN] at hx
    change x + (d : ℝ) ∈ Set.Ioo (0 : ℝ) (N : ℝ)
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    constructor
    · exact add_pos_of_pos_of_nonneg hx.1 hd0
    · linarith only [hx.2]
  exact (hcoord.fun_comp (differentiableOn_id.add_const (d : ℝ)) hmaps).sub
    (hcoord.mono hsub)

theorem heathBrown_shiftedDifference_deriv_bounds
    {N k d : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 2 ≤ k) (hdN : d ≤ N)
    (hraw : ContinuousOn (iteratedDeriv (k - 1) f)
      (Set.Icc 0 (N : ℝ)))
    (hrawd : DifferentiableOn ℝ (iteratedDeriv (k - 1) f)
      (Set.Ioo 0 (N : ℝ)))
    (hcoordd : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda) :
    ∀ x ∈ Set.Ioo (0 : ℝ) ((N - d : ℕ) : ℝ),
      lambda * d / ((k - 2).factorial : ℝ) ≤
          deriv (heathBrownShiftedDifference f (k - 2) d) x ∧
        deriv (heathBrownShiftedDifference f (k - 2) d) x ≤
          A * lambda * d / ((k - 2).factorial : ℝ) := by
  intro x hx
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hxI : x ∈ Set.Icc (0 : ℝ) N := by
    constructor
    · exact hx.1.le
    · rw [Nat.cast_sub hdN] at hx
      exact hx.2.le.trans (sub_le_self _ hd0)
  have hxdI : x + (d : ℝ) ∈ Set.Icc (0 : ℝ) N := by
    constructor
    · exact add_nonneg hx.1.le hd0
    · rw [Nat.cast_sub hdN] at hx
      linarith only [hx.2]
  have hxd : x ≤ x + (d : ℝ) := by
    exact le_add_of_nonneg_right hd0
  have hxOpen : x ∈ Set.Ioo (0 : ℝ) N := by
    constructor
    · exact hx.1
    · rw [Nat.cast_sub hdN] at hx
      exact hx.2.trans_le (sub_le_self _ hd0)
  have hxdOpen : x + (d : ℝ) ∈ Set.Ioo (0 : ℝ) N := by
    constructor
    · exact add_pos_of_pos_of_nonneg hx.1 hd0
    · rw [Nat.cast_sub hdN] at hx
      linarith only [hx.2]
  have hkpred : k - 1 + 1 = k := by omega
  have hrawLower : ∀ y ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ deriv (iteratedDeriv (k - 1) f) y := by
    intro y hy
    rw [← iteratedDeriv_succ]
    rw [hkpred]
    exact (hkBounds y hy).1
  have hrawUpper : ∀ y ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      deriv (iteratedDeriv (k - 1) f) y ≤ A * lambda := by
    intro y hy
    rw [← iteratedDeriv_succ]
    rw [hkpred]
    exact (hkBounds y hy).2
  have hlower := heathBrown_lower_slope hraw hrawd hrawLower hxI hxdI hxd
  have hupper := heathBrown_upper_slope hraw hrawd hrawUpper hxI hxdI hxd
  have hxdiff : x + (d : ℝ) - x = (d : ℝ) := by ring
  have hderiv :
      deriv (heathBrownShiftedDifference f (k - 2) d) x =
        (iteratedDeriv (k - 1) f (x + d) -
          iteratedDeriv (k - 1) f x) / ((k - 2).factorial : ℝ) := by
    have hkpred2 : k - 2 + 1 = k - 1 := by omega
    rw [deriv_heathBrownShiftedDifference f (k - 2) d x
      ((hcoordd x hxOpen).differentiableAt
        (isOpen_Ioo.mem_nhds hxOpen))
      ((hcoordd (x + d) hxdOpen).differentiableAt
        (isOpen_Ioo.mem_nhds hxdOpen)), hkpred2]
  rw [hderiv]
  constructor
  · apply (div_le_div_iff_of_pos_right (by positivity :
      (0 : ℝ) < (k - 2).factorial)).2
    simpa only [hxdiff] using hlower
  · apply (div_le_div_iff_of_pos_right (by positivity :
      (0 : ℝ) < (k - 2).factorial)).2
    simpa only [hxdiff] using hupper

#print axioms heathBrownShiftedDifference_nat
#print axioms deriv_heathBrownShiftedDifference
#print axioms heathBrown_shiftedDifference_continuousOn
#print axioms heathBrown_shiftedDifference_differentiableOn
#print axioms heathBrown_shiftedDifference_deriv_bounds

end

end GafniTao
