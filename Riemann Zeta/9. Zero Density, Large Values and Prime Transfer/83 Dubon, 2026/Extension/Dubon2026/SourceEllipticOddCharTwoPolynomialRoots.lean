import Dubon2026.SourceEllipticOddCharTwoPolynomial

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
theorem BtP_eq_prod (hI : I.Nonempty) (hinj : Set.InjOn Y I)
    (hroot : ∀ k ∈ I, (BtP I x).eval (Y k) = 0) :
    BtP I x = ∏ k ∈ I, (X - C (Y k)) := by
  classical
  have hmon1 := monic_prod_X_sub_C' I (fun i => x i ^ 2)
  have hmonR := monic_prod_X_sub_C' I Y
  have hdeg1 := natDegree_prod_X_sub_C' I (fun i => x i ^ 2)
  have hdegR := natDegree_prod_X_sub_C' I Y
  have htail : (∑ j ∈ I, C (x j) * ∏ i ∈ I.erase j, (X - C (x i ^ 2))).natDegree
      ≤ I.card - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_prod_X_sub_C' (I.erase j) (fun i => x i ^ 2), card_erase_of_mem hj]
  have hdegree : (BtP I x - ∏ k ∈ I, (X - C (Y k))).degree < I.card := by
    have e : BtP I x - ∏ k ∈ I, (X - C (Y k))
        = (∏ i ∈ I, (X - C (x i ^ 2)) - ∏ k ∈ I, (X - C (Y k)))
          + ∑ j ∈ I, C (x j) * ∏ i ∈ I.erase j, (X - C (x i ^ 2)) := by
      rw [BtP]; ring
    rw [e]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · by_cases h0 : ∏ i ∈ I, (X - C (x i ^ 2)) - ∏ k ∈ I, (X - C (Y k)) = 0
      · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
      have := degree_sub_lt (p := ∏ i ∈ I, (X - C (x i ^ 2))) (q := ∏ k ∈ I, (X - C (Y k)))
        (by rw [degree_eq_natDegree hmon1.ne_zero, degree_eq_natDegree hmonR.ne_zero,
          hdeg1, hdegR]) hmon1.ne_zero (by rw [hmon1.leadingCoeff, hmonR.leadingCoeff])
      rwa [degree_eq_natDegree hmon1.ne_zero, hdeg1] at this
    · refine lt_of_le_of_lt (degree_le_of_natDegree_le htail) ?_
      exact_mod_cast Nat.sub_lt (card_pos.mpr hI) one_pos
  apply sub_eq_zero.mp
  by_cases hz : BtP I x - ∏ k ∈ I, (X - C (Y k)) = 0
  · exact hz
  · apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (I.image Y)
    · intro v hv
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hv
      rw [eval_sub, hroot k hk, eval_prod, prod_eq_zero hk (by simp), sub_self]
    · rw [card_image_of_injOn hinj]
      rw [degree_eq_natDegree hz] at hdegree
      exact WithBot.coe_lt_coe.mp hdegree


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
