import GafniTao.WeightedMixedShellEnergy
import GafniTao.EnergyDetectorSharpShellLocal

/-!
# Logarithmic dyadic cover of the symmetric zero set

The first color contains ordinates of absolute value at most one.  Every
other color is a literal signed shell `[2^r,2^(r+1)]`.  The cover has
`log_2(ceil T)+2` colors, so its fourth-power pigeonhole loss is logarithmic,
not a hidden power of the height.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Number of colors in the low-height-plus-dyadic-shell cover. -/
noncomputable def dyadicZeroShellCount (T : Real) : Nat :=
  Nat.log 2 (Nat.ceil T) + 2

/-- Color zero is the bounded central rectangle; color `r+1` is the signed
absolute-ordinate shell `[2^r,2^(r+1)]`. -/
noncomputable def dyadicZeroShell (sigma T : Real)
    (i : Fin (dyadicZeroShellCount T)) : Finset Complex :=
  if i.val = 0 then zerosInRect sigma 1 (-1) 1
  else absoluteDyadicZeroSlab sigma ((2 ^ (i.val - 1) : Nat) : Real)

theorem dyadicZeroShellCount_pos (T : Real) : 0 < dyadicZeroShellCount T := by
  unfold dyadicZeroShellCount
  omega

/-- Rectangle data exposed from an arbitrary lower-real-part zero set. -/
theorem mem_zeroSet_sigma_data
    {sigma T : Real} {rho : Complex} (hrho : rho ∈ zeroSet sigma T) :
    sigma ≤ rho.re ∧ rho.re ≤ 1 ∧ -T ≤ rho.im ∧ rho.im ≤ T ∧
      riemannZeta rho = 0 := by
  change rho ∈ zerosInRect sigma 1 (-T) T at hrho
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrho
  have hrect := (mem_ZeroRectangle sigma 1 (-T) T rho).mp hrho.1
  exact ⟨hrect.1, hrect.2.1, hrect.2.2.1, hrect.2.2.2, hrho.2⟩

theorem mem_centralZeroBox_of_abs_im_le_one
    {sigma : Real} {rho : Complex}
    (hreLower : sigma ≤ rho.re) (hreUpper : rho.re ≤ 1)
    (hzero : riemannZeta rho = 0) (him : |rho.im| ≤ 1) :
    rho ∈ zerosInRect sigma 1 (-1) 1 := by
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    mem_ZeroRectangle]
  rw [abs_le] at him
  exact ⟨⟨hreLower, hreUpper, him.1, him.2⟩, hzero⟩

theorem mem_absoluteDyadicZeroSlab_of_abs_bounds
    {sigma U : Real} {rho : Complex}
    (hreLower : sigma ≤ rho.re) (hreUpper : rho.re ≤ 1)
    (hzero : riemannZeta rho = 0)
    (hLower : U ≤ |rho.im|) (hUpper : |rho.im| ≤ 2 * U) :
    rho ∈ absoluteDyadicZeroSlab sigma U := by
  rw [absoluteDyadicZeroSlab, Finset.mem_union]
  by_cases him : 0 ≤ rho.im
  · right
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle]
    rw [abs_of_nonneg him] at hLower hUpper
    exact ⟨⟨hreLower, hreUpper, hLower, hUpper⟩, hzero⟩
  · left
    have himNeg : rho.im < 0 := lt_of_not_ge him
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle]
    rw [abs_of_neg himNeg] at hLower hUpper
    exact ⟨⟨hreLower, hreUpper, by linarith, by linarith⟩, hzero⟩

/-- The logarithmic family covers every zero of symmetric height `T`. -/
theorem exists_mem_dyadicZeroShell
    {sigma T : Real} {rho : Complex}
    (hrho : rho ∈ zeroSet sigma T) :
    ∃ i : Fin (dyadicZeroShellCount T), rho ∈ dyadicZeroShell sigma T i := by
  have hd := mem_zeroSet_sigma_data hrho
  have habs : |rho.im| ≤ T := by
    rw [abs_le]
    exact ⟨hd.2.2.1, hd.2.2.2.1⟩
  by_cases hsmall : |rho.im| ≤ 1
  · let i : Fin (dyadicZeroShellCount T) :=
      ⟨0, dyadicZeroShellCount_pos T⟩
    refine ⟨i, ?_⟩
    simp only [dyadicZeroShell, i, ↓reduceIte]
    exact mem_centralZeroBox_of_abs_im_le_one hd.1 hd.2.1
      hd.2.2.2.2 hsmall
  · have habsOne : 1 < |rho.im| := lt_of_not_ge hsmall
    let n : Nat := Nat.floor |rho.im|
    have hnPos : 0 < n := Nat.floor_pos.mpr habsOne.le
    let r : Nat := Nat.log 2 n
    have hnCeil : n ≤ Nat.ceil T := by
      exact_mod_cast (show (n : Real) ≤ (Nat.ceil T : Real) from by
        calc
          (n : Real) ≤ |rho.im| := Nat.floor_le (abs_nonneg _)
          _ ≤ T := habs
          _ ≤ (Nat.ceil T : Real) := Nat.le_ceil T)
    have hrLog : r ≤ Nat.log 2 (Nat.ceil T) :=
      Nat.log_mono_right hnCeil
    let i : Fin (dyadicZeroShellCount T) := by
      refine ⟨r + 1, ?_⟩
      unfold dyadicZeroShellCount
      omega
    have hLowerNat : 2 ^ r ≤ n :=
      Nat.pow_log_le_self 2 hnPos.ne'
    have hLower : ((2 ^ r : Nat) : Real) ≤ |rho.im| := by
      exact (Nat.cast_le.mpr hLowerNat).trans
        (Nat.floor_le (abs_nonneg _))
    have hUpperNat : n < 2 ^ (r + 1) := by
      simpa only [r, Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self Nat.one_lt_two n
    have hFloorUpper : |rho.im| < (n : Real) + 1 :=
      Nat.lt_floor_add_one |rho.im|
    have hUpper : |rho.im| ≤ 2 * ((2 ^ r : Nat) : Real) := by
      have hSucc : (n : Real) + 1 ≤ ((2 ^ (r + 1) : Nat) : Real) := by
        exact_mod_cast hUpperNat
      have hPow : ((2 ^ (r + 1) : Nat) : Real) =
          2 * ((2 ^ r : Nat) : Real) := by
        rw [pow_succ]
        push_cast
        ring
      rw [← hPow]
      exact hFloorUpper.le.trans hSucc
    refine ⟨i, ?_⟩
    have hi : i.val ≠ 0 := by
      dsimp only [i]
      omega
    rw [dyadicZeroShell, if_neg hi]
    simp only [i, Nat.add_sub_cancel]
    exact mem_absoluteDyadicZeroSlab_of_abs_bounds hd.1 hd.2.1
      hd.2.2.2.2 hLower hUpper

/-- Consequently the full multiplicity-weighted zero energy localizes to
four (possibly different) members of the logarithmic shell cover. -/
theorem exists_zero_energy_dyadic_shells
    (sigma T : Real) :
    ∃ label : Fin 4 → Fin (dyadicZeroShellCount T),
      zeroAdditiveEnergyCount sigma T ≤ (dyadicZeroShellCount T) ^ 4 *
        weightedMixedAdditiveEnergyOn
          (dyadicZeroShell sigma T (label 0))
          (dyadicZeroShell sigma T (label 1))
          (dyadicZeroShell sigma T (label 2))
          (dyadicZeroShell sigma T (label 3)) zeroMultiplicity 1 := by
  exact exists_zero_energy_mixed_cover sigma T (dyadicZeroShellCount T)
    (dyadicZeroShellCount_pos T) (dyadicZeroShell sigma T)
    (fun rho hrho => exists_mem_dyadicZeroShell hrho)

#print axioms dyadicZeroShellCount
#print axioms dyadicZeroShell
#print axioms mem_zeroSet_sigma_data
#print axioms mem_absoluteDyadicZeroSlab_of_abs_bounds
#print axioms exists_mem_dyadicZeroShell
#print axioms exists_zero_energy_dyadic_shells

end

end GafniTao
