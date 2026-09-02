import GafniTao.FordLocalInverseSquareSharp
import GafniTao.SecondMoment

/-!
# Height-adaptive unit bins for Ford's global zero tail

The finite zero-set parameter is not an admissible constant in a bound that
will be sent to infinity.  This file re-bounds each ordinate bin at its own
physical height.  Consequently the multiplicity in the bin indexed by `z`
is `O(log (|z|+2))`, uniformly in the enclosing finite zero set.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- A source-safe height containing the complete half-open ordinate bin
`[z,z+1)`, and large enough for the proved local-zero theorem. -/
noncomputable def fordAdaptiveZeroBinHeight (z : ℤ) : ℝ :=
  max (Real.exp 2) (max 8 ((|z| : ℝ) + 2))

theorem fordAdaptiveZeroBinHeight_ge_exp_two (z : ℤ) :
    Real.exp 2 ≤ fordAdaptiveZeroBinHeight z :=
  le_max_left _ _

theorem fordAdaptiveZeroBinHeight_ge_eight (z : ℤ) :
    8 ≤ fordAdaptiveZeroBinHeight z :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem fordAdaptiveZeroBinHeight_ge_abs_add_two (z : ℤ) :
    (|z| : ℝ) + 2 ≤ fordAdaptiveZeroBinHeight z :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem fordAdaptiveZeroBinHeight_data (z : ℤ) :
    max (Real.exp 2) 8 ≤ fordAdaptiveZeroBinHeight z := by
  rw [max_le_iff]
  exact ⟨fordAdaptiveZeroBinHeight_ge_exp_two z,
    fordAdaptiveZeroBinHeight_ge_eight z⟩

theorem floorFiber_subset_adaptiveZeroBin
    {T : ℝ} (z : ℤ) :
    (zeroSet 0 T).filter (fun rho => ordinateBin rho = z) ⊆
      zeroLocalUnitBin 0 (fordAdaptiveZeroBinHeight z) z := by
  intro rho hrho
  rw [Finset.mem_filter] at hrho
  have hdata := mem_zeroSet_zero_data hrho.1
  have hfloorLe : ((⌊rho.im⌋ : ℤ) : ℝ) ≤ rho.im := Int.floor_le rho.im
  have hfloorUpper : rho.im < ((⌊rho.im⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one rho.im
  have hz : ⌊rho.im⌋ = z := by simpa [ordinateBin] using hrho.2
  rw [hz] at hfloorLe hfloorUpper
  have hzLower : (z : ℝ) ≤ rho.im := hfloorLe
  have hzUpper : rho.im < (z : ℝ) + 1 := hfloorUpper
  have habsZLower : -((|z| : ℝ) + 2) ≤ rho.im := by
    have hzAbs : -(|z| : ℝ) ≤ (z : ℝ) := by
      exact_mod_cast (neg_abs_le z)
    linarith
  have habsZUpper : rho.im ≤ (|z| : ℝ) + 2 := by
    have hzAbs : (z : ℝ) ≤ (|z| : ℝ) := by
      exact_mod_cast (le_abs_self z)
    linarith
  have hheight := fordAdaptiveZeroBinHeight_ge_abs_add_two z
  have hrhoAdaptive : rho ∈ zeroSet 0 (fordAdaptiveZeroBinHeight z) := by
    change rho ∈ RiemannZeta.GuthMaynard.zerosInRect
      0 1 (-fordAdaptiveZeroBinHeight z) (fordAdaptiveZeroBinHeight z)
    rw [RiemannZeta.GuthMaynard.zerosInRect,
      Set.Finite.mem_toFinset, Set.mem_inter_iff]
    constructor
    · exact (RiemannZeta.GuthMaynard.mem_ZeroRectangle
        0 1 (-fordAdaptiveZeroBinHeight z)
          (fordAdaptiveZeroBinHeight z) rho).mpr
        ⟨hdata.1, hdata.2.1,
          (neg_le_neg hheight).trans habsZLower,
          habsZUpper.trans hheight⟩
    · exact hdata.2.2.2.2
  rw [zeroLocalUnitBin, Finset.mem_filter]
  exact ⟨hrhoAdaptive, hzLower, hzUpper⟩

/-- Multiplicity in an integer ordinate bin, uniformly in the larger finite
zero rectangle.  The logarithm tracks the physical bin height rather than
the cutoff that will later tend to infinity. -/
theorem floorFiber_multiplicity_le_adaptive_log
    (T : ℝ) (z : ℤ) :
    ((∑ rho ∈ (zeroSet 0 T).filter (fun w => ordinateBin w = z),
        zeroMultiplicity rho : ℕ) : ℝ) ≤
      globalLocalZeroLogConstant *
        Real.log (fordAdaptiveZeroBinHeight z) := by
  have hNat :
      ∑ rho ∈ (zeroSet 0 T).filter (fun w => ordinateBin w = z),
          zeroMultiplicity rho ≤
        ∑ rho ∈ zeroLocalUnitBin 0 (fordAdaptiveZeroBinHeight z) z,
          zeroMultiplicity rho := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact floorFiber_subset_adaptiveZeroBin z
    · intro _ _ _
      exact Nat.zero_le _
  have hReal :
      ((∑ rho ∈ (zeroSet 0 T).filter (fun w => ordinateBin w = z),
          zeroMultiplicity rho : ℕ) : ℝ) ≤
        ((∑ rho ∈ zeroLocalUnitBin 0
            (fordAdaptiveZeroBinHeight z) z,
          zeroMultiplicity rho : ℕ) : ℝ) := by
    exact_mod_cast hNat
  exact hReal.trans (by
    simpa using zeroLocalUnitBin_multiplicity_le_global_log
      0 (fordAdaptiveZeroBinHeight z) z (by norm_num)
        (fordAdaptiveZeroBinHeight_data z))

#print axioms floorFiber_multiplicity_le_adaptive_log

end

end GafniTao
