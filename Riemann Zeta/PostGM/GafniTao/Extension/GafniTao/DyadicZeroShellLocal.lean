import GafniTao.DyadicZeroShellCover
import GafniTao.WeightedMixedEnergyLocal

/-!
# The bounded branch of the dyadic zero-energy cover

Every member of the logarithmic cover is placed inside one common symmetric
zero rectangle of height `2 * ceil T`.  If any selected coordinate is the
central box, exact coordinate symmetries move that box to the first freely
summed coordinate, after which the local-zero fibre bound costs only two
full-height zero counts.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem zeroSet_mono_height_sigma
    {sigma T R : Real} (hTR : T <= R) :
    zeroSet sigma T ⊆ zeroSet sigma R := by
  change zerosInRect sigma 1 (-T) T ⊆ zerosInRect sigma 1 (-R) R
  apply zerosInRect_subset_of_rect_subset
  exact ZeroRectangle_subset sigma 1 (-T) T sigma 1 (-R) R
    le_rfl le_rfl (by linarith) hTR

/-- Analytic-multiplicity zero counts are monotone in the symmetric height. -/
theorem zeroCount_mono_height_sigma
    {sigma T R : Real} (hTR : T ≤ R) :
    zeroCount sigma T ≤ zeroCount sigma R := by
  rw [zeroCount_eq_weighted_sum, zeroCount_eq_weighted_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (zeroSet_mono_height_sigma hTR)
  intro rho _ _
  exact Nat.zero_le _

/-- Every color of the logarithmic cover lies in the common rectangle of
height `2 * ceil T`. -/
theorem dyadicZeroShell_subset_common_zeroSet
    {sigma T : Real} (hT : 1 <= T)
    (i : Fin (dyadicZeroShellCount T)) :
    dyadicZeroShell sigma T i ⊆ zeroSet sigma (2 * (Nat.ceil T : Real)) := by
  by_cases hi : i.val = 0
  · rw [dyadicZeroShell, if_pos hi]
    apply zeroSet_mono_height_sigma
    have hCeil : (1 : Nat) <= Nat.ceil T := by
      have hCeilReal : (1 : Real) <= (Nat.ceil T : Real) :=
        hT.trans (Nat.le_ceil T)
      exact_mod_cast hCeilReal
    exact_mod_cast (show (1 : Nat) <= 2 * Nat.ceil T by omega)
  · rw [dyadicZeroShell, if_neg hi]
    let r := i.val - 1
    have hr : r <= Nat.log 2 (Nat.ceil T) := by
      have hiLt := i.isLt
      unfold dyadicZeroShellCount at hiLt
      dsimp only [r]
      omega
    have hCeilPos : 0 < Nat.ceil T := by
      have hCeilReal : (1 : Real) <= (Nat.ceil T : Real) :=
        hT.trans (Nat.le_ceil T)
      exact_mod_cast (show (0 : Real) < (Nat.ceil T : Real) by linarith)
    have hPow : 2 ^ r <= Nat.ceil T := by
      exact (Nat.pow_le_pow_right (by omega) hr).trans
        (Nat.pow_log_le_self 2 hCeilPos.ne')
    have hU : 0 <= ((2 ^ r : Nat) : Real) := by positivity
    have hShell := absoluteDyadicZeroSlab_subset_zeroSet
      sigma ((2 ^ r : Nat) : Real) hU
    apply hShell.trans
    apply zeroSet_mono_height_sigma
    exact_mod_cast (Nat.mul_le_mul_left 2 hPow)

/-- Color zero is exactly the central symmetric zero set. -/
theorem dyadicZeroShell_eq_central
    {sigma T : Real} {i : Fin (dyadicZeroShellCount T)} (hi : i.val = 0) :
    dyadicZeroShell sigma T i = zeroSet sigma 1 := by
  simp only [dyadicZeroShell, hi, if_pos, zeroSet]

/-- If one selected coordinate is the central cover color, the mixed energy
has the elementary two-global-count bound. -/
theorem weightedMixed_dyadicZeroShells_le_of_central
    {sigma T : Real} (hsigma : 0 <= sigma)
    (hT : max (Real.exp 2) 8 <= 2 * (Nat.ceil T : Real))
    (hTone : 1 <= T)
    (label : Fin 4 -> Fin (dyadicZeroShellCount T))
    (hCentral : exists i : Fin 4, (label i).val = 0) :
    (weightedMixedAdditiveEnergyOn
        (dyadicZeroShell sigma T (label 0))
        (dyadicZeroShell sigma T (label 1))
        (dyadicZeroShell sigma T (label 2))
        (dyadicZeroShell sigma T (label 3)) zeroMultiplicity 1 : Real) <=
      (zeroCount sigma 1 : Real) *
        (zeroCount sigma (2 * (Nat.ceil T : Real)) : Real) ^ 2 *
        (3 * globalLocalZeroLogConstant *
          Real.log (2 * (Nat.ceil T : Real))) := by
  let B : Real := 2 * (Nat.ceil T : Real)
  have hSub (i : Fin 4) :
      dyadicZeroShell sigma T (label i) ⊆ zeroSet sigma B := by
    simpa only [B] using dyadicZeroShell_subset_common_zeroSet hTone (label i)
  rcases hCentral with ⟨i, hi⟩
  fin_cases i
  · have hi' : (label 0).val = 0 := by simpa using hi
    have hEq := dyadicZeroShell_eq_central (sigma := sigma) (T := T) hi'
    exact weightedMixedAdditiveEnergyOn_le_central_first hsigma hT
      (by rw [hEq]) (hSub 1) (hSub 2) (hSub 3)
  · rw [weightedMixedAdditiveEnergyOn_swap_positive]
    have hi' : (label 1).val = 0 := by simpa using hi
    have hEq := dyadicZeroShell_eq_central (sigma := sigma) (T := T) hi'
    exact weightedMixedAdditiveEnergyOn_le_central_first hsigma hT
      (by rw [hEq]) (hSub 0) (hSub 2) (hSub 3)
  · rw [weightedMixedAdditiveEnergyOn_swap_pairs]
    have hi' : (label 2).val = 0 := by simpa using hi
    have hEq := dyadicZeroShell_eq_central (sigma := sigma) (T := T) hi'
    exact weightedMixedAdditiveEnergyOn_le_central_first hsigma hT
      (by rw [hEq]) (hSub 3) (hSub 0) (hSub 1)
  · rw [weightedMixedAdditiveEnergyOn_swap_pairs,
      weightedMixedAdditiveEnergyOn_swap_positive]
    have hi' : (label 3).val = 0 := by simpa using hi
    have hEq := dyadicZeroShell_eq_central (sigma := sigma) (T := T) hi'
    exact weightedMixedAdditiveEnergyOn_le_central_first hsigma hT
      (by rw [hEq]) (hSub 2) (hSub 0) (hSub 1)

#print axioms zeroSet_mono_height_sigma
#print axioms zeroCount_mono_height_sigma
#print axioms dyadicZeroShell_subset_common_zeroSet
#print axioms dyadicZeroShell_eq_central
#print axioms weightedMixed_dyadicZeroShells_le_of_central

end

end GafniTao
