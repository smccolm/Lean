import Dubon2026.SourceEllipticOddCharTwoCoefficients

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
theorem close_of_reads (h2 : (2 : K) = 0) (a₆ : K)
    (hx0 : ∀ k ∈ I, x k ≠ 0) (hY : ∀ k ∈ I, Y k = a₆ / x k ^ 2)
    (r0 : ∏ i ∈ I, x i ^ 2 + ∑ j ∈ I, x j * ∏ i ∈ I.erase j, x i ^ 2 = ∏ k ∈ I, Y k)
    (r1 : ∑ i ∈ I, x i ^ 2 + ∑ j ∈ I, x j = ∑ k ∈ I, Y k) :
    (a₆ + ∑ k ∈ I, x k + (∑ k ∈ I, x k) ^ 2) * (∏ k ∈ I, x k ^ 2) ^ 4
      = a₆ ^ (2 * I.card + 1) := by
  have hP20 : ∏ k ∈ I, x k ^ 2 ≠ 0 := prod_ne_zero_iff.mpr fun k hk => pow_ne_zero 2 (hx0 k hk)
  have hprodY : ∏ k ∈ I, Y k = a₆ ^ I.card / ∏ k ∈ I, x k ^ 2 := by
    rw [prod_congr rfl hY, prod_div_distrib, prod_const]
  have hsumY : ∑ k ∈ I, Y k = a₆ * (∑ k ∈ I, (x k)⁻¹) ^ 2 := by
    rw [sum_congr rfl hY, sum_sq_of_two h2, mul_sum]
    exact sum_congr rfl fun k _ => by rw [div_eq_mul_inv, inv_pow]
  have hmixed : ∑ j ∈ I, x j * ∏ i ∈ I.erase j, x i ^ 2
      = (∏ k ∈ I, x k ^ 2) * ∑ k ∈ I, (x k)⁻¹ := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hm : x j ^ 2 * ∏ i ∈ I.erase j, x i ^ 2 = ∏ i ∈ I, x i ^ 2 :=
      mul_prod_erase I (fun i => x i ^ 2) hj
    have hxj := hx0 j hj
    rw [← hm]
    field_simp
  have H1 : (∏ k ∈ I, x k ^ 2) ^ 2 * (1 + ∑ k ∈ I, (x k)⁻¹) = a₆ ^ I.card := by
    rw [hmixed, hprodY, eq_div_iff hP20] at r0
    linear_combination r0
  have H2 : (∑ k ∈ I, x k) ^ 2 + ∑ k ∈ I, x k = a₆ * (∑ k ∈ I, (x k)⁻¹) ^ 2 := by
    rw [← sum_sq_of_two h2 I x, hsumY] at r1
    exact r1
  linear_combination (∏ k ∈ I, x k ^ 2) ^ 4 * H2
    + a₆ * ((∏ k ∈ I, x k ^ 2) ^ 2 * (1 + ∑ k ∈ I, (x k)⁻¹) + a₆ ^ I.card) * H1
    - a₆ * (∏ k ∈ I, x k ^ 2) ^ 4 * (∑ k ∈ I, (x k)⁻¹) * h2

theorem char_two_chain (h2 : (2 : K) = 0) (ξ : ι → K) (a₆ c : K) (hc : c ^ 2 = a₆)
    (ha₆ : a₆ ≠ 0) (hx0 : ∀ k ∈ I, x k ≠ 0) (hinj : Set.InjOn x I)
    (hξ : ∀ k ∈ I, ξ k = c / x k) (hξx : ∀ k ∈ I, ∀ j ∈ I, ξ k ≠ x j)
    (hvan : ∀ k ∈ I, ξ k + ∑ j ∈ I, (x j / (ξ k - x j) + x j ^ 2 / (ξ k - x j) ^ 2) = 0) :
    (a₆ + ∑ k ∈ I, x k + (∑ k ∈ I, x k) ^ 2) * (∏ k ∈ I, x k ^ 2) ^ 4
      = a₆ ^ (2 * I.card + 1) := by
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ha₆ (by rw [← hc]; ring)
  have hY : ∀ k ∈ I, ξ k ^ 2 = a₆ / x k ^ 2 := fun k hk => by
    rw [hξ k hk, div_pow, hc]
  have hξ0 : ∀ k ∈ I, ξ k ≠ 0 := fun k hk => by
    rw [hξ k hk]
    exact div_ne_zero hc0 (hx0 k hk)
  have hYx : ∀ k ∈ I, ∀ j ∈ I, ξ k ^ 2 - x j ^ 2 ≠ 0 := fun k hk j hj => by
    rw [← sub_sq_of_two h2]
    exact pow_ne_zero 2 (sub_ne_zero.mpr (hξx k hk j hj))
  have hYinj : Set.InjOn (fun k => ξ k ^ 2) I := by
    intro k hk k' hk' hkk
    have hkk' : ξ k ^ 2 = ξ k' ^ 2 := hkk
    have h0 : (ξ k - ξ k') ^ 2 = 0 := by rw [sub_sq_of_two h2, hkk', sub_self]
    have h1 : ξ k = ξ k' := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)
    rw [hξ k hk, hξ k' hk', div_eq_mul_inv, div_eq_mul_inv] at h1
    exact hinj hk hk' (inv_inj.mp (mul_left_cancel₀ hc0 h1))
  have hroot : ∀ k ∈ I, (BtP I x).eval (ξ k ^ 2) = 0 := fun k hk =>
    BtP_eval_eq_zero I x (hYx k hk) (one_add_sum_eq_zero I x h2 (hξ0 k hk) (hξx k hk) (hvan k hk))
  have hBR := BtP_eq_prod I x (fun k => ξ k ^ 2) hI hYinj hroot
  exact close_of_reads I x (fun k => ξ k ^ 2) h2 a₆ hx0 hY (read_zero I x _ h2 hBR)
    (read_pred I x _ h2 hI hBR)


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
