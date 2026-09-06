import GafniTao.DyadicZeroShellLocal

/-!
# Arbitrarily bounded members of the dyadic zero-shell cover

The source detector is only available beyond a fixed height.  A selected
dyadic shell below that height is not discarded: its literal outer height is
recorded, the shell is embedded into the corresponding bounded zero set, and
the exact mixed local-zero estimate is applied after a coordinate symmetry.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Literal outer ordinate height of a cover member. -/
noncomputable def dyadicZeroShellOuterHeight {T : Real}
    (i : Fin (dyadicZeroShellCount T)) : Real :=
  if i.val = 0 then 1 else 2 * ((2 ^ (i.val - 1) : Nat) : Real)

/-- Literal inner height of a cover member.  For a noncentral member this is
the `U` for which the member is exactly `absoluteDyadicZeroSlab sigma U`. -/
noncomputable def dyadicZeroShellInnerHeight {T : Real}
    (i : Fin (dyadicZeroShellCount T)) : Real :=
  if i.val = 0 then 1 else ((2 ^ (i.val - 1) : Nat) : Real)

theorem dyadicZeroShell_eq_absolute_of_ne_zero
    {sigma T : Real} {i : Fin (dyadicZeroShellCount T)}
    (hi : i.val ≠ 0) :
    dyadicZeroShell sigma T i =
      absoluteDyadicZeroSlab sigma (dyadicZeroShellInnerHeight i) := by
  simp only [dyadicZeroShell, dyadicZeroShellInnerHeight, hi, if_false]

theorem dyadicZeroShellOuterHeight_eq_two_mul_inner_of_ne_zero
    {T : Real} {i : Fin (dyadicZeroShellCount T)} (hi : i.val ≠ 0) :
    dyadicZeroShellOuterHeight i = 2 * dyadicZeroShellInnerHeight i := by
  simp only [dyadicZeroShellOuterHeight, dyadicZeroShellInnerHeight, hi,
    if_false]

theorem dyadicZeroShellInnerHeight_pos
    {T : Real} (i : Fin (dyadicZeroShellCount T)) :
    0 < dyadicZeroShellInnerHeight i := by
  by_cases hi : i.val = 0
  · simp only [dyadicZeroShellInnerHeight, hi, if_true, zero_lt_one]
  · simp only [dyadicZeroShellInnerHeight, hi, if_false]
    positivity

/-- The threshold conversion used at the detector entry: a noncentral shell
whose outer height is larger than `2 * U0` has inner height at least `U0`. -/
theorem le_dyadicZeroShellInnerHeight_of_two_mul_lt_outer
    {T U0 : Real} {i : Fin (dyadicZeroShellCount T)}
    (hi : i.val ≠ 0)
    (hOuter : 2 * U0 < dyadicZeroShellOuterHeight i) :
    U0 <= dyadicZeroShellInnerHeight i := by
  rw [dyadicZeroShellOuterHeight_eq_two_mul_inner_of_ne_zero hi] at hOuter
  linarith

theorem dyadicZeroShell_subset_own_zeroSet
    {sigma T : Real} (i : Fin (dyadicZeroShellCount T)) :
    dyadicZeroShell sigma T i <=
      zeroSet sigma (dyadicZeroShellOuterHeight i) := by
  intro rho hrho
  by_cases hi : i.val = 0
  · rw [dyadicZeroShell_eq_central hi] at hrho
    simpa only [dyadicZeroShellOuterHeight, hi, if_pos] using hrho
  · rw [dyadicZeroShell, if_neg hi] at hrho
    have hSub := absoluteDyadicZeroSlab_subset_zeroSet sigma
      (((2 ^ (i.val - 1) : Nat) : Real)) (by positivity)
    simpa only [dyadicZeroShellOuterHeight, hi, if_neg] using hSub hrho

theorem dyadicZeroShell_subset_bounded_zeroSet
    {sigma T R0 : Real} {i : Fin (dyadicZeroShellCount T)}
    (hi : dyadicZeroShellOuterHeight i <= R0) :
    dyadicZeroShell sigma T i <= zeroSet sigma R0 :=
  (dyadicZeroShell_subset_own_zeroSet i).trans (zeroSet_mono_height_sigma hi)

/-- If any selected cover member has bounded outer height, exact coordinate
symmetries reduce the mixed energy to the local-zero bound. -/
theorem weightedMixed_dyadicZeroShells_le_of_bounded
    {sigma T R0 : Real} (hsigma : 0 <= sigma)
    (hT : max (Real.exp 2) 8 <= 2 * (Nat.ceil T : Real))
    (hTone : 1 <= T)
    (label : Fin 4 -> Fin (dyadicZeroShellCount T))
    (hBounded : exists i : Fin 4,
      dyadicZeroShellOuterHeight (label i) <= R0) :
    (weightedMixedAdditiveEnergyOn
        (dyadicZeroShell sigma T (label 0))
        (dyadicZeroShell sigma T (label 1))
        (dyadicZeroShell sigma T (label 2))
        (dyadicZeroShell sigma T (label 3)) zeroMultiplicity 1 : Real) <=
      (zeroCount sigma R0 : Real) *
        (zeroCount sigma (2 * (Nat.ceil T : Real)) : Real) ^ 2 *
        (3 * globalLocalZeroLogConstant *
          Real.log (2 * (Nat.ceil T : Real))) := by
  let B : Real := 2 * (Nat.ceil T : Real)
  have hSub (i : Fin 4) :
      dyadicZeroShell sigma T (label i) <= zeroSet sigma B := by
    simpa only [B] using dyadicZeroShell_subset_common_zeroSet hTone (label i)
  rcases hBounded with ⟨i, hi⟩
  have hSmall : dyadicZeroShell sigma T (label i) <= zeroSet sigma R0 :=
    dyadicZeroShell_subset_bounded_zeroSet hi
  fin_cases i
  · exact weightedMixedAdditiveEnergyOn_le_bounded_first hsigma hT
      hSmall (hSub 1) (hSub 2) (hSub 3)
  · rw [weightedMixedAdditiveEnergyOn_swap_positive]
    exact weightedMixedAdditiveEnergyOn_le_bounded_first hsigma hT
      hSmall (hSub 0) (hSub 2) (hSub 3)
  · rw [weightedMixedAdditiveEnergyOn_swap_pairs]
    exact weightedMixedAdditiveEnergyOn_le_bounded_first hsigma hT
      hSmall (hSub 3) (hSub 0) (hSub 1)
  · rw [weightedMixedAdditiveEnergyOn_swap_pairs,
      weightedMixedAdditiveEnergyOn_swap_positive]
    exact weightedMixedAdditiveEnergyOn_le_bounded_first hsigma hT
      hSmall (hSub 2) (hSub 0) (hSub 1)

#print axioms dyadicZeroShell_subset_own_zeroSet
#print axioms dyadicZeroShell_subset_bounded_zeroSet
#print axioms dyadicZeroShell_eq_absolute_of_ne_zero
#print axioms le_dyadicZeroShellInnerHeight_of_two_mul_lt_outer
#print axioms weightedMixed_dyadicZeroShells_le_of_bounded

end

end GafniTao
