import Dubon2026.SourceEllipticOddCharTwoPolynomialRoots

/-! Characteristic-two algebra for the actual odd quotient discriminant.
The ordinary case uses the squared-coordinate norm polynomial and its two
required coefficients. The supersingular case uses the actual unchanged
a3 coefficient. These cases are required by odd quotient ellipticity,
cyclic quotient products, inertia census and modular-curve good reduction
for DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2; characteristic two is not excluded.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Native root bounds and the
already proved denominator degree replace duplicate general foundations. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
open WeierstrassCurve Polynomial Finset
noncomputable section
variable {K : Type*} [Field K]
variable {ι : Type*} [DecidableEq ι] (I : Finset ι) (x Y : ι → K)
omit [DecidableEq ι] in
theorem one_add_sum_eq_zero (h2 : (2 : K) = 0) {ξ : K} (hξ0 : ξ ≠ 0)
    (hξx : ∀ j ∈ I, ξ ≠ x j)
    (hvan : ξ + ∑ j ∈ I, (x j / (ξ - x j) + x j ^ 2 / (ξ - x j) ^ 2) = 0) :
    1 + ∑ j ∈ I, x j / (ξ ^ 2 - x j ^ 2) = 0 := by
  have hsum : ∑ j ∈ I, (x j / (ξ - x j) + x j ^ 2 / (ξ - x j) ^ 2)
      = ξ * ∑ j ∈ I, x j / (ξ ^ 2 - x j ^ 2) := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hd : ξ - x j ≠ 0 := sub_ne_zero.mpr (hξx j hj)
    rw [← sub_sq_of_two h2 ξ (x j)]
    field_simp
    ring
  rw [hsum, ← mul_one_add] at hvan
  exact (mul_eq_zero.mp hvan).resolve_left hξ0

theorem BtP_eval_eq_zero {v : K} (hvx : ∀ j ∈ I, v - x j ^ 2 ≠ 0)
    (h : 1 + ∑ j ∈ I, x j / (v - x j ^ 2) = 0) : (BtP I x).eval v = 0 := by
  rw [BtP_eval]
  have hPe : ∀ j ∈ I, ∏ i ∈ I.erase j, (v - x i ^ 2)
      = (∏ i ∈ I, (v - x i ^ 2)) / (v - x j ^ 2) := by
    intro j hj
    rw [eq_div_iff (hvx j hj), mul_comm]
    exact mul_prod_erase I (fun i => v - x i ^ 2) hj
  have hs : ∑ j ∈ I, x j * ∏ i ∈ I.erase j, (v - x i ^ 2)
      = (∏ i ∈ I, (v - x i ^ 2)) * ∑ j ∈ I, x j / (v - x j ^ 2) := by
    rw [mul_sum]
    exact sum_congr rfl fun j hj => by rw [hPe j hj]; ring
  rw [hs, ← mul_one_add, h, mul_zero]

theorem read_zero (h2 : (2 : K) = 0) (hBR : BtP I x = ∏ k ∈ I, (X - C (Y k))) :
    ∏ i ∈ I, x i ^ 2 + ∑ j ∈ I, x j * ∏ i ∈ I.erase j, x i ^ 2 = ∏ k ∈ I, Y k := by
  have e := congrArg (eval 0) hBR
  rw [BtP_eval, eval_prod] at e
  simpa only [eval_sub, eval_X, eval_C, zero_sub, neg_eq_self_of_two h2] using e

theorem read_pred (h2 : (2 : K) = 0) (hI : I.Nonempty)
    (hBR : BtP I x = ∏ k ∈ I, (X - C (Y k))) :
    ∑ i ∈ I, x i ^ 2 + ∑ j ∈ I, x j = ∑ k ∈ I, Y k := by
  have hpos : 0 < I.card := card_pos.mpr hI
  have e := congrArg (fun p : K[X] => p.coeff (I.card - 1)) hBR
  simp only [BtP, coeff_add, finsetSum_coeff, coeff_C_mul] at e
  have c1 : (∏ i ∈ I, (X - C (x i ^ 2))).coeff (I.card - 1) = -∑ i ∈ I, x i ^ 2 :=
    prod_X_sub_C_coeff_card_pred I (fun i => x i ^ 2) hpos
  have cR : (∏ k ∈ I, (X - C (Y k))).coeff (I.card - 1) = -∑ k ∈ I, Y k :=
    prod_X_sub_C_coeff_card_pred I Y hpos
  have hlead : ∀ j ∈ I, (∏ i ∈ I.erase j, (X - C (x i ^ 2))).coeff (I.card - 1) = 1 := by
    intro j hj
    rw [← card_erase_of_mem hj, ← natDegree_prod_X_sub_C' (I.erase j) (fun i => x i ^ 2)]
    exact (monic_prod_X_sub_C' (I.erase j) (fun i => x i ^ 2)).coeff_natDegree
  have hs : ∑ j ∈ I, x j * (∏ i ∈ I.erase j, (X - C (x i ^ 2))).coeff (I.card - 1)
      = ∑ j ∈ I, x j := sum_congr rfl fun j hj => by rw [hlead j hj, mul_one]
  rw [c1, cR, hs] at e
  linear_combination -e + (∑ j ∈ I, x j) * h2


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
