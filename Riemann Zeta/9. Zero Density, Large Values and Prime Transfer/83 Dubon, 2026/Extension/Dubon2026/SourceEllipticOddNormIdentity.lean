import Dubon2026.SourceEllipticOddNormCoordinates

/-! Finite polynomial factorization for the explicit odd cyclic
quotient. Translated roots determine the cleared numerator; the three
two-torsion fibers then identify the quotient cubic and its discriminant.
This is the necessary algebraic step before actual-curve assembly in the
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 chain through quotient products,
cyclic-subgroup roots, inertia census, reverse genus and good reduction.
Adapted from the selected odd-order quotient discriminant proof,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Native monic polynomial root
comparison is reused. The actual-curve hypotheses are not asserted here. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open Polynomial Finset
noncomputable section
variable {K : Type*} [Field K]
variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (x t u : ι → K)
theorem norm_identity' (x₀ c : K) (τp τm : ι → K)
    (h0p : ∀ q ∈ S, x₀ ≠ τp q) (h0m : ∀ q ∈ S, x₀ ≠ τm q)
    (hpp : Set.InjOn τp S) (hmm : Set.InjOn τm S) (hpm : ∀ q ∈ S, ∀ q' ∈ S, τp q ≠ τm q')
    (hr0 : (AP S x t u).eval x₀ = c * (hP S x).eval x₀ ^ 2)
    (hrp : ∀ q ∈ S, (AP S x t u).eval (τp q) = c * (hP S x).eval (τp q) ^ 2)
    (hrm : ∀ q ∈ S, (AP S x t u).eval (τm q) = c * (hP S x).eval (τm q) ^ 2) :
    (X - C x₀) * ∏ q ∈ S, ((X - C (τp q)) * (X - C (τm q))) = AP S x t u - C c * hP S x ^ 2 := by
  classical

  set s : Finset K := insert x₀ (S.image τp ∪ S.image τm) with hs
  have hdisj : Disjoint (S.image τp) (S.image τm) := by
    rw [disjoint_iff_ne]
    rintro a ha b hb rfl
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ha
    obtain ⟨q', hq', e⟩ := mem_image.mp hb
    exact hpm q hq q' hq' e.symm
  have hx₀ : x₀ ∉ S.image τp ∪ S.image τm := by
    intro hmem
    rcases mem_union.mp hmem with h | h
    · obtain ⟨q, hq, e⟩ := mem_image.mp h; exact h0p q hq e.symm
    · obtain ⟨q, hq, e⟩ := mem_image.mp h; exact h0m q hq e.symm
  have hcard : s.card = 2 * S.card + 1 := by
    rw [hs, card_insert_of_notMem hx₀, card_union_of_disjoint hdisj, card_image_of_injOn hpp,
      card_image_of_injOn hmm]
    ring

  set M := (X - C x₀) * ∏ q ∈ S, ((X - C (τp q)) * (X - C (τm q))) with hM
  have hMmon : M.Monic := (monic_X_sub_C _).mul (monic_prod_of_monic _ _ fun q _ =>
    (monic_X_sub_C _).mul (monic_X_sub_C _))
  have hMdeg : M.natDegree = 2 * S.card + 1 := by
    rw [hM, (monic_X_sub_C _).natDegree_mul (monic_prod_of_monic _ _ fun q _ =>
      (monic_X_sub_C _).mul (monic_X_sub_C _)), natDegree_X_sub_C,
      natDegree_prod_of_monic _ _ fun q _ => (monic_X_sub_C _).mul (monic_X_sub_C _)]
    rw [sum_congr rfl fun q _ => (monic_X_sub_C (τp q)).natDegree_mul (monic_X_sub_C (τm q))]
    simp only [natDegree_X_sub_C, sum_const, smul_eq_mul]
    ring
  have hA := AP_monic S x t u
  have hAdeg := natDegree_AP S x t u
  have hdegree : (M - (AP S x t u - C c * hP S x ^ 2)).degree < s.card := by
    have e : M - (AP S x t u - C c * hP S x ^ 2) = (M - AP S x t u) + C c * hP S x ^ 2 := by ring
    rw [e, hcard]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · by_cases h0 : M - AP S x t u = 0
      · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
      have := degree_sub_lt (p := M) (q := AP S x t u)
        (by rw [degree_eq_natDegree hMmon.ne_zero, degree_eq_natDegree hA.ne_zero, hMdeg, hAdeg])
        hMmon.ne_zero (by rw [hMmon.leadingCoeff, hA.leadingCoeff])
      rwa [degree_eq_natDegree hMmon.ne_zero, hMdeg] at this
    · refine lt_of_le_of_lt (degree_le_of_natDegree_le ((natDegree_C_mul_le _ _).trans
        ((natDegree_pow_le).trans (Nat.mul_le_mul_left 2 (natDegree_hP_le S x))))) ?_
      exact_mod_cast (show 2 * S.card < 2 * S.card + 1 by omega)
  have hevals : ∀ v ∈ s, M.eval v = (AP S x t u - C c * hP S x ^ 2).eval v := by
    intro v hv
    have hR : ∀ w, (AP S x t u).eval w = c * (hP S x).eval w ^ 2 →
        (AP S x t u - C c * hP S x ^ 2).eval w = 0 := fun w hw => by
      rw [eval_sub, eval_mul, eval_C, eval_pow, hw, sub_self]
    rw [hs, mem_insert, mem_union, mem_image, mem_image] at hv
    rcases hv with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · rw [hR _ hr0, hM, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
    · rw [hR _ (hrp q hq), hM, eval_mul, eval_prod, prod_eq_zero hq (by simp), mul_zero]
    · rw [hR _ (hrm q hq), hM, eval_mul, eval_prod, prod_eq_zero hq (by simp), mul_zero]
  apply sub_eq_zero.mp
  by_cases heq : M - (AP S x t u - C c * hP S x ^ 2) = 0
  · exact heq
  · apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ s
    · intro v hv
      rw [eval_sub, hevals v hv, sub_self]
    · rw [degree_eq_natDegree heq] at hdegree
      exact WithBot.coe_lt_coe.mp hdegree


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
