import GafniTao.EnergyDetectorSharpShellLocal
import GafniTao.FordSingleZeroCotangentBound

/-!
# Cardinality control for sharp zero-shell representatives

The Guth--Maynard energy estimate is expressed using the cardinality of a
separated ordinate family.  This file proves the missing source bridge from
that unweighted cardinality back to the multiplicity-weighted zeta count.
The only input is positivity of the analytic order of a genuine zeta zero.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Every distinct zero in the signed dyadic shell contributes at least one
to its multiplicity-weighted shell count. -/
theorem absoluteDyadicZeroSlab_card_le_weighted_sum
    (sigma U : Real) (hU : 0 ≤ U) :
    (absoluteDyadicZeroSlab sigma U).card ≤
      ∑ rho ∈ absoluteDyadicZeroSlab sigma U, zeroMultiplicity rho := by
  classical
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro rho hrho
  have hfull : rho ∈ zeroSet sigma (2 * U) :=
    absoluteDyadicZeroSlab_subset_zeroSet sigma U hU hrho
  have hzero : riemannZeta rho = 0 := by
    change rho ∈ zerosInRect sigma 1 (-(2 * U)) (2 * U) at hfull
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hfull
    exact hfull.2
  have hone : rho ≠ 1 := by
    intro hrhoOne
    subst rho
    exact riemannZeta_one_ne_zero hzero
  exact one_le_analyticVanishingOrder_riemannZeta hone hzero

/-- The number of distinct zeros in a signed dyadic shell is bounded by the
actual multiplicity-weighted symmetric zero count at twice the shell height.
-/
theorem absoluteDyadicZeroSlab_card_le_zeroCount
    (sigma U : Real) (hU : 0 ≤ U) :
    (absoluteDyadicZeroSlab sigma U).card ≤ zeroCount sigma (2 * U) := by
  rw [zeroCount_eq_weighted_sum]
  exact (absoluteDyadicZeroSlab_card_le_weighted_sum sigma U hU).trans
    (Finset.sum_le_sum_of_subset_of_nonneg
      (absoluteDyadicZeroSlab_subset_zeroSet sigma U hU)
      (fun _ _ _ => Nat.zero_le _))

/-- Any image of a subfamily of the shell, in particular every detector
representative family, has cardinality at most the source zero count. -/
theorem image_filter_absoluteDyadicZeroSlab_card_le_zeroCount
    (sigma U : Real) (hU : 0 ≤ U)
    (P : Complex → Prop) [DecidablePred P] (f : Complex → Real) :
    (((absoluteDyadicZeroSlab sigma U).filter P).image f).card ≤
      zeroCount sigma (2 * U) := by
  calc
    (((absoluteDyadicZeroSlab sigma U).filter P).image f).card ≤
        ((absoluteDyadicZeroSlab sigma U).filter P).card :=
      Finset.card_image_le
    _ ≤ (absoluteDyadicZeroSlab sigma U).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ zeroCount sigma (2 * U) :=
      absoluteDyadicZeroSlab_card_le_zeroCount sigma U hU

#print axioms absoluteDyadicZeroSlab_card_le_weighted_sum
#print axioms absoluteDyadicZeroSlab_card_le_zeroCount
#print axioms image_filter_absoluteDyadicZeroSlab_card_le_zeroCount

end

end GafniTao
