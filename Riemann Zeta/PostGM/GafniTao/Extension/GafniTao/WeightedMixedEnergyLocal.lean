import GafniTao.WeightedMixedShellEnergy
import GafniTao.ZeroEnergyLocal

/-!
# A local-zero bound for mixed multiplicity energy

This file handles the bounded member of the logarithmic height-shell cover.
The estimate is deliberately mixed: the three freely summed coordinates may
come from different zero subfamilies, while the fourth coordinate is confined
to the literal tolerance-one local-zero fibre.  Consequently a bounded shell
costs its own multiplicity mass and only two full-height zero counts.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Fubini bound for a mixed weighted energy when the fourth-coordinate
resonant fibre has uniformly bounded weight. -/
theorem weightedMixedAdditiveEnergyOn_le_three_masses_mul_fiber
    {S0 S1 S2 S3 : Finset Complex} {weight : Complex -> Nat}
    {eta : Real} {L : Nat}
    (hFiber : forall z0, z0 ∈ S0 -> forall z1, z1 ∈ S1 ->
      forall z2, z2 ∈ S2 ->
        (∑ z3 ∈ S3.filter (fun z3 =>
          |z0.im + z1.im - z2.im - z3.im| <= eta), weight z3) <= L) :
    weightedMixedAdditiveEnergyOn S0 S1 S2 S3 weight eta <=
      (∑ z0 ∈ S0, weight z0) * (∑ z1 ∈ S1, weight z1) *
        (∑ z2 ∈ S2, weight z2) * L := by
  classical
  unfold weightedMixedAdditiveEnergyOn resonantQuadruplesOnFour
    quadrupleProductOf weightedQuadruple
  rw [Finset.sum_filter]
  have hExpand :
      (∑ q ∈ (S0.product S1).product (S2.product S3),
          if |q.1.1.im + q.1.2.im - q.2.1.im - q.2.2.im| <= eta then
            weight q.1.1 * weight q.1.2 * weight q.2.1 * weight q.2.2
          else 0) =
        ∑ z0 ∈ S0, ∑ z1 ∈ S1, ∑ z2 ∈ S2, ∑ z3 ∈ S3,
          if |z0.im + z1.im - z2.im - z3.im| <= eta then
            weight z0 * weight z1 * weight z2 * weight z3 else 0 := by
    calc
      _ = ∑ p ∈ S0.product S1, ∑ r ∈ S2.product S3,
          if |p.1.im + p.2.im - r.1.im - r.2.im| <= eta then
            weight p.1 * weight p.2 * weight r.1 * weight r.2 else 0 := by
        exact Finset.sum_product _ _ _
      _ = ∑ z0 ∈ S0, ∑ z1 ∈ S1, ∑ z2 ∈ S2, ∑ z3 ∈ S3,
          if |z0.im + z1.im - z2.im - z3.im| <= eta then
            weight z0 * weight z1 * weight z2 * weight z3 else 0 := by
        have hRight (p : Complex × Complex) :
            (∑ r ∈ S2.product S3,
              if |p.1.im + p.2.im - r.1.im - r.2.im| <= eta then
                weight p.1 * weight p.2 * weight r.1 * weight r.2 else 0) =
              ∑ z2 ∈ S2, ∑ z3 ∈ S3,
                if |p.1.im + p.2.im - z2.im - z3.im| <= eta then
                  weight p.1 * weight p.2 * weight z2 * weight z3 else 0 := by
          exact Finset.sum_product _ _ _
        simp_rw [hRight]
        exact Finset.sum_product _ _ _
  rw [hExpand]
  calc
    (∑ z0 ∈ S0, ∑ z1 ∈ S1, ∑ z2 ∈ S2, ∑ z3 ∈ S3,
        if |z0.im + z1.im - z2.im - z3.im| <= eta then
          weight z0 * weight z1 * weight z2 * weight z3 else 0) <=
      ∑ z0 ∈ S0, ∑ z1 ∈ S1, ∑ z2 ∈ S2,
        weight z0 * weight z1 * weight z2 * L := by
          apply Finset.sum_le_sum
          intro z0 hz0
          apply Finset.sum_le_sum
          intro z1 hz1
          apply Finset.sum_le_sum
          intro z2 hz2
          calc
            (∑ z3 ∈ S3,
                if |z0.im + z1.im - z2.im - z3.im| <= eta then
                  weight z0 * weight z1 * weight z2 * weight z3 else 0) =
                weight z0 * weight z1 * weight z2 *
                  (∑ z3 ∈ S3.filter (fun z3 =>
                    |z0.im + z1.im - z2.im - z3.im| <= eta), weight z3) := by
              rw [Finset.sum_filter, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro z3 hz3
              by_cases hres : |z0.im + z1.im - z2.im - z3.im| <= eta
              <;> simp [hres, mul_assoc]
            _ <= weight z0 * weight z1 * weight z2 * L :=
              Nat.mul_le_mul_left _ (hFiber z0 hz0 z1 hz1 z2 hz2)
    _ = (∑ z0 ∈ S0, weight z0) * (∑ z1 ∈ S1, weight z1) *
        (∑ z2 ∈ S2, weight z2) * L := by
      rw [Finset.sum_mul_sum]
      rw [Finset.sum_mul_sum]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z0 hz0
      rw [Finset.sum_comm]

/-- Literal four-sum expansion of mixed weighted energy. -/
theorem weightedMixedAdditiveEnergyOn_eq_four_sum
    (S0 S1 S2 S3 : Finset Complex) (weight : Complex -> Nat) (eta : Real) :
    weightedMixedAdditiveEnergyOn S0 S1 S2 S3 weight eta =
      ∑ z0 ∈ S0, ∑ z1 ∈ S1, ∑ z2 ∈ S2, ∑ z3 ∈ S3,
        if |z0.im + z1.im - z2.im - z3.im| <= eta then
          weight z0 * weight z1 * weight z2 * weight z3 else 0 := by
  classical
  unfold weightedMixedAdditiveEnergyOn resonantQuadruplesOnFour
    quadrupleProductOf weightedQuadruple
  rw [Finset.sum_filter]
  calc
    (∑ q ∈ (S0.product S1).product (S2.product S3),
        if |q.1.1.im + q.1.2.im - q.2.1.im - q.2.2.im| <= eta then
          weight q.1.1 * weight q.1.2 * weight q.2.1 * weight q.2.2
        else 0) =
      ∑ p ∈ S0.product S1, ∑ r ∈ S2.product S3,
        if |p.1.im + p.2.im - r.1.im - r.2.im| <= eta then
          weight p.1 * weight p.2 * weight r.1 * weight r.2 else 0 := by
      exact Finset.sum_product _ _ _
    _ = _ := by
      have hRight (p : Complex × Complex) :
          (∑ r ∈ S2.product S3,
            if |p.1.im + p.2.im - r.1.im - r.2.im| <= eta then
              weight p.1 * weight p.2 * weight r.1 * weight r.2 else 0) =
            ∑ z2 ∈ S2, ∑ z3 ∈ S3,
              if |p.1.im + p.2.im - z2.im - z3.im| <= eta then
                weight p.1 * weight p.2 * weight z2 * weight z3 else 0 := by
        exact Finset.sum_product _ _ _
      simp_rw [hRight]
      exact Finset.sum_product _ _ _

/-- The two positive-sign coordinates may be interchanged. -/
theorem weightedMixedAdditiveEnergyOn_swap_positive
    (S0 S1 S2 S3 : Finset Complex) (weight : Complex -> Nat) (eta : Real) :
    weightedMixedAdditiveEnergyOn S0 S1 S2 S3 weight eta =
      weightedMixedAdditiveEnergyOn S1 S0 S2 S3 weight eta := by
  rw [weightedMixedAdditiveEnergyOn_eq_four_sum,
    weightedMixedAdditiveEnergyOn_eq_four_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z1 hz1
  apply Finset.sum_congr rfl
  intro z0 hz0
  apply Finset.sum_congr rfl
  intro z2 hz2
  apply Finset.sum_congr rfl
  intro z3 hz3
  congr 1
  · congr 2
    all_goals ring_nf
  · ring

/-- The two negative-sign coordinates may be interchanged. -/
theorem weightedMixedAdditiveEnergyOn_swap_negative
    (S0 S1 S2 S3 : Finset Complex) (weight : Complex -> Nat) (eta : Real) :
    weightedMixedAdditiveEnergyOn S0 S1 S2 S3 weight eta =
      weightedMixedAdditiveEnergyOn S0 S1 S3 S2 weight eta := by
  rw [weightedMixedAdditiveEnergyOn_eq_four_sum,
    weightedMixedAdditiveEnergyOn_eq_four_sum]
  apply Finset.sum_congr rfl
  intro z0 hz0
  apply Finset.sum_congr rfl
  intro z1 hz1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z3 hz3
  apply Finset.sum_congr rfl
  intro z2 hz2
  congr 1
  · congr 2
    all_goals ring_nf
  · ring

/-- Exchanging the positive and negative pairs preserves mixed energy. -/
theorem weightedMixedAdditiveEnergyOn_swap_pairs
    (S0 S1 S2 S3 : Finset Complex) (weight : Complex -> Nat) (eta : Real) :
    weightedMixedAdditiveEnergyOn S0 S1 S2 S3 weight eta =
      weightedMixedAdditiveEnergyOn S2 S3 S0 S1 weight eta := by
  rw [weightedMixedAdditiveEnergyOn_eq_four_sum,
    weightedMixedAdditiveEnergyOn_eq_four_sum]
  calc
    (∑ z0 ∈ S0, ∑ z1 ∈ S1, ∑ z2 ∈ S2, ∑ z3 ∈ S3,
        if |z0.im + z1.im - z2.im - z3.im| <= eta then
          weight z0 * weight z1 * weight z2 * weight z3 else 0) =
      ∑ z0 ∈ S0, ∑ z2 ∈ S2, ∑ z1 ∈ S1, ∑ z3 ∈ S3,
        if |z0.im + z1.im - z2.im - z3.im| <= eta then
          weight z0 * weight z1 * weight z2 * weight z3 else 0 := by
      apply Finset.sum_congr rfl
      intro z0 hz0
      rw [Finset.sum_comm]
    _ = ∑ z2 ∈ S2, ∑ z0 ∈ S0, ∑ z1 ∈ S1, ∑ z3 ∈ S3,
        if |z0.im + z1.im - z2.im - z3.im| <= eta then
          weight z0 * weight z1 * weight z2 * weight z3 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ z2 ∈ S2, ∑ z0 ∈ S0, ∑ z3 ∈ S3, ∑ z1 ∈ S1,
        if |z0.im + z1.im - z2.im - z3.im| <= eta then
          weight z0 * weight z1 * weight z2 * weight z3 else 0 := by
      apply Finset.sum_congr rfl
      intro z2 hz2
      apply Finset.sum_congr rfl
      intro z0 hz0
      rw [Finset.sum_comm]
    _ = ∑ z2 ∈ S2, ∑ z3 ∈ S3, ∑ z0 ∈ S0, ∑ z1 ∈ S1,
        if |z0.im + z1.im - z2.im - z3.im| <= eta then
          weight z0 * weight z1 * weight z2 * weight z3 else 0 := by
      apply Finset.sum_congr rfl
      intro z2 hz2
      rw [Finset.sum_comm]
    _ = ∑ z2 ∈ S2, ∑ z3 ∈ S3, ∑ z0 ∈ S0, ∑ z1 ∈ S1,
        if |z2.im + z3.im - z0.im - z1.im| <= eta then
          weight z2 * weight z3 * weight z0 * weight z1 else 0 := by
      apply Finset.sum_congr rfl
      intro z2 hz2
      apply Finset.sum_congr rfl
      intro z3 hz3
      apply Finset.sum_congr rfl
      intro z0 hz0
      apply Finset.sum_congr rfl
      intro z1 hz1
      congr 1
      · apply propext
        have hneg : z2.im + z3.im - z0.im - z1.im =
            -(z0.im + z1.im - z2.im - z3.im) := by ring
        rw [hneg, abs_neg]
      · ring

/-- The multiplicity mass of a subfamily is bounded by the containing zero
count. -/
theorem subfamily_multiplicity_sum_le_zeroCount
    {sigma T : Real} {S : Finset Complex} (hS : S ⊆ zeroSet sigma T) :
    (∑ rho ∈ S, zeroMultiplicity rho) <= zeroCount sigma T := by
  rw [zeroCount_eq_weighted_sum]
  exact Finset.sum_le_sum_of_subset hS

/-- Mixed local-zero estimate when the first coordinate lies in a fixed
bounded height box.  The other three families may be different subfamilies
of the same full zero set. -/
theorem weightedMixedAdditiveEnergyOn_le_bounded_first
    {sigma R0 T : Real} {S0 S1 S2 S3 : Finset Complex}
    (hsigma : 0 <= sigma) (hT : max (Real.exp 2) 8 <= T)
    (h0 : S0 ⊆ zeroSet sigma R0)
    (h1 : S1 ⊆ zeroSet sigma T) (h2 : S2 ⊆ zeroSet sigma T)
    (h3 : S3 ⊆ zeroSet sigma T) :
    (weightedMixedAdditiveEnergyOn S0 S1 S2 S3 zeroMultiplicity 1 : Real) <=
      (zeroCount sigma R0 : Real) * (zeroCount sigma T : Real) ^ 2 *
        (3 * globalLocalZeroLogConstant * Real.log T) := by
  have hFiberNat : forall z0, z0 ∈ S0 -> forall z1, z1 ∈ S1 ->
      forall z2, z2 ∈ S2 ->
        (∑ z3 ∈ S3.filter (fun z3 =>
          |z0.im + z1.im - z2.im - z3.im| <= (1 : Real)),
            zeroMultiplicity z3) <=
          Nat.floor (3 * globalLocalZeroLogConstant * Real.log T) := by
    intro z0 hz0 z1 hz1 z2 hz2
    have hSubset : S3.filter (fun z3 =>
        |z0.im + z1.im - z2.im - z3.im| <= (1 : Real)) ⊆
        resonantFourthZeroFiber sigma T z0 z1 z2 := by
      intro z3 hz3
      rw [Finset.mem_filter] at hz3
      rw [resonantFourthZeroFiber, Finset.mem_filter]
      exact ⟨h3 hz3.1, hz3.2⟩
    have hReal := resonantFourthZeroFiber_multiplicity_le z0 z1 z2 hsigma hT
    have hSubNat :
        (∑ z3 ∈ S3.filter (fun z3 =>
          |z0.im + z1.im - z2.im - z3.im| <= (1 : Real)),
            zeroMultiplicity z3) <=
          ∑ z3 ∈ resonantFourthZeroFiber sigma T z0 z1 z2,
            zeroMultiplicity z3 := Finset.sum_le_sum_of_subset hSubset
    have hSumReal :
        (((∑ z3 ∈ S3.filter (fun z3 =>
          |z0.im + z1.im - z2.im - z3.im| <= (1 : Real)),
            zeroMultiplicity z3) : Nat) : Real) <=
          3 * globalLocalZeroLogConstant * Real.log T := by
      have hSubReal :
          (((∑ z3 ∈ S3.filter (fun z3 =>
            |z0.im + z1.im - z2.im - z3.im| <= (1 : Real)),
              zeroMultiplicity z3) : Nat) : Real) <=
            (((∑ z3 ∈ resonantFourthZeroFiber sigma T z0 z1 z2,
              zeroMultiplicity z3) : Nat) : Real) := by
        exact_mod_cast hSubNat
      exact hSubReal.trans hReal
    exact Nat.le_floor hSumReal
  have hFinite := weightedMixedAdditiveEnergyOn_le_three_masses_mul_fiber
    (S0 := S0) (S1 := S1) (S2 := S2) (S3 := S3)
    (weight := zeroMultiplicity) (eta := (1 : Real))
    (L := Nat.floor (3 * globalLocalZeroLogConstant * Real.log T)) hFiberNat
  have h0Mass := subfamily_multiplicity_sum_le_zeroCount h0
  have h1Mass := subfamily_multiplicity_sum_le_zeroCount h1
  have h2Mass := subfamily_multiplicity_sum_le_zeroCount h2
  have h0MassReal :
      (((∑ z0 ∈ S0, zeroMultiplicity z0) : Nat) : Real) <=
        (zeroCount sigma R0 : Real) := by exact_mod_cast h0Mass
  have h1MassReal :
      (((∑ z1 ∈ S1, zeroMultiplicity z1) : Nat) : Real) <=
        (zeroCount sigma T : Real) := by exact_mod_cast h1Mass
  have h2MassReal :
      (((∑ z2 ∈ S2, zeroMultiplicity z2) : Nat) : Real) <=
        (zeroCount sigma T : Real) := by exact_mod_cast h2Mass
  have hFloor :
      ((Nat.floor (3 * globalLocalZeroLogConstant * Real.log T) : Nat) : Real) <=
        3 * globalLocalZeroLogConstant * Real.log T := by
    apply Nat.floor_le
    have hTOne : (1 : Real) <= T := by
      exact (by norm_num : (1 : Real) <= 8) |>.trans
        ((le_max_right (Real.exp 2) 8).trans hT)
    exact mul_nonneg (mul_nonneg (by norm_num) globalLocalZeroLogConstant_pos.le)
      (Real.log_nonneg hTOne)
  have hFiniteReal :
      (weightedMixedAdditiveEnergyOn S0 S1 S2 S3 zeroMultiplicity 1 : Real) <=
        (((∑ z0 ∈ S0, zeroMultiplicity z0) : Nat) : Real) *
          (((∑ z1 ∈ S1, zeroMultiplicity z1) : Nat) : Real) *
          (((∑ z2 ∈ S2, zeroMultiplicity z2) : Nat) : Real) *
          ((Nat.floor (3 * globalLocalZeroLogConstant * Real.log T) : Nat) : Real) := by
    exact_mod_cast hFinite
  calc
    (weightedMixedAdditiveEnergyOn S0 S1 S2 S3 zeroMultiplicity 1 : Real) <=
        (((∑ z0 ∈ S0, zeroMultiplicity z0) : Nat) : Real) *
          (((∑ z1 ∈ S1, zeroMultiplicity z1) : Nat) : Real) *
          (((∑ z2 ∈ S2, zeroMultiplicity z2) : Nat) : Real) *
          ((Nat.floor (3 * globalLocalZeroLogConstant * Real.log T) : Nat) : Real) :=
      hFiniteReal
    _ <=
        (zeroCount sigma R0 : Real) * (zeroCount sigma T : Real) *
          (zeroCount sigma T : Real) *
          (3 * globalLocalZeroLogConstant * Real.log T) := by
      gcongr
    _ = (zeroCount sigma R0 : Real) * (zeroCount sigma T : Real) ^ 2 *
        (3 * globalLocalZeroLogConstant * Real.log T) := by ring

/-- The central-box form used by the original dyadic cover. -/
theorem weightedMixedAdditiveEnergyOn_le_central_first
    {sigma T : Real} {S0 S1 S2 S3 : Finset Complex}
    (hsigma : 0 <= sigma) (hT : max (Real.exp 2) 8 <= T)
    (h0 : S0 ⊆ zeroSet sigma 1)
    (h1 : S1 ⊆ zeroSet sigma T) (h2 : S2 ⊆ zeroSet sigma T)
    (h3 : S3 ⊆ zeroSet sigma T) :
    (weightedMixedAdditiveEnergyOn S0 S1 S2 S3 zeroMultiplicity 1 : Real) <=
      (zeroCount sigma 1 : Real) * (zeroCount sigma T : Real) ^ 2 *
        (3 * globalLocalZeroLogConstant * Real.log T) := by
  exact weightedMixedAdditiveEnergyOn_le_bounded_first hsigma hT h0 h1 h2 h3

#print axioms weightedMixedAdditiveEnergyOn_le_three_masses_mul_fiber
#print axioms subfamily_multiplicity_sum_le_zeroCount
#print axioms weightedMixedAdditiveEnergyOn_le_bounded_first
#print axioms weightedMixedAdditiveEnergyOn_le_central_first

end

end GafniTao
