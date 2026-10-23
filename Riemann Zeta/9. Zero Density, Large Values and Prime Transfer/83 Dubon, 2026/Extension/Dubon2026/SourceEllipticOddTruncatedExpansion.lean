import Dubon2026.SourceEllipticOddTruncatedIdentities

/-! Polynomial coefficient comparison on the odd cyclic quotient
discriminant chain. The exact rational numerator and denominator are reflected
and compared modulo X^4 to recover the quotient cubic coefficients. These
calculations serve odd quotient ellipticity -> prime quotient maps/products
-> cyclic-subgroup root interpretation -> inertia census -> reverse genus
and good reduction -> DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from the selected odd-order quotient discriminant proof,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Native polynomial reflection,
degree bounds, quotient rings and finite products are reused. The full
curve discriminant identity is not asserted by these conditional identities. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open Polynomial Finset
noncomputable section
variable {K : Type*} [Field K]
theorem expansion_core {ι : Type*} [DecidableEq ι] (S : Finset ι) (x d t u : ι → K)
    (b₂ b₄ b₆ b₈ c₂ c₁ c₀ : K)
    (ht : ∀ q ∈ S, t q = 6 * x q ^ 2 + b₂ * x q + b₄)
    (hu : ∀ q ∈ S, u q = 4 * x q ^ 3 + b₂ * x q ^ 2 + 2 * b₄ * x q + b₆)
    (hperm : S.val.map d = S.val.map x)
    (Ar hr fr : K[X]) (mr : ι → K[X])
    (Hhr : hr = ∏ q ∈ S, (1 - C (x q) * X))
    (HAr : Ar = hr ^ 2 + ∑ q ∈ S, (C (t q) * (1 - C (x q) * X) + C (u q) * X)
      * (∏ q' ∈ S.erase q, (1 - C (x q') * X) ^ 2) * X ^ 2)
    (Hfr : fr = C 4 + C b₂ * X + C (2 * b₄) * X ^ 2 + C b₆ * X ^ 3)
    (Hmr : ∀ q ∈ S, mr q * (1 - C (x q) * X)
      = (C 1 * X ^ 0 - C b₄ * X ^ 2 - C (2 * b₆) * X ^ 3 - C b₈ * X ^ 4)
        - C (d q) * (C 4 * X ^ 1 + C b₂ * X ^ 2 + C (2 * b₄) * X ^ 3 + C b₆ * X ^ 4))
    (R : C 4 * Ar ^ 3 + C c₂ * X * Ar ^ 2 * hr ^ 2 + C c₁ * X ^ 2 * Ar * hr ^ 4
      + C c₀ * X ^ 3 * hr ^ 6 = fr * ∏ q ∈ S, mr q ^ 2) :
    c₂ = b₂ ∧ c₁ = 2 * b₄ - 20 * ∑ q ∈ S, t q
      ∧ c₀ = b₆ - 4 * b₂ * (∑ q ∈ S, t q) - 28 * ∑ q ∈ S, (u q + x q * t q) := by
  obtain ⟨ε, hεdef⟩ : ∃ e : R4 K, e = eps K := ⟨_, rfl⟩
  have hε : ε ^ 4 = 0 := by rw [hεdef]; exact eps_pow_four
  set tK : K := ∑ q ∈ S, t q with htK
  set wK : K := ∑ q ∈ S, (u q + x q * t q) with hwK

  have Eη : π hr = ∏ q ∈ S, (1 - sc (x q) * ε) := by
    rw [Hhr, map_prod]
    refine prod_congr rfl fun q _ => ?_
    rw [map_sub, map_one, map_mul, π_C, π_X, ← hεdef]
  have Eφ : π fr = 4 + sc b₂ * ε + 2 * sc b₄ * ε ^ 2 + sc b₆ * ε ^ 3 := by
    rw [Hfr]
    simp only [map_add, map_mul, map_pow, π_C, π_X, map_ofNat, ← hεdef]
  have hηunit : IsUnit (π hr) := by
    rw [Eη]
    refine prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun q _ => ?_
    exact IsUnit.of_mul_eq_one _ (trunc_unit hε (sc (x q)))

  have eP : ∀ q ∈ S, (∏ q' ∈ S.erase q, (1 - sc (x q') * ε) ^ 2) * (1 - sc (x q) * ε) ^ 2
      = π hr ^ 2 := by
    intro q hq
    rw [Eη, ← prod_pow]
    exact prod_erase_mul S (fun q' => (1 - sc (x q') * ε) ^ 2) hq
  have Eα : π Ar = π hr ^ 2 * (1 + sc tK * ε ^ 2 + sc wK * ε ^ 3) := by
    have e0 : π Ar = π hr ^ 2 + ∑ q ∈ S, (sc (t q) * (1 - sc (x q) * ε) + sc (u q) * ε)
        * (∏ q' ∈ S.erase q, (1 - sc (x q') * ε) ^ 2) * ε ^ 2 := by
      rw [HAr]
      simp only [map_add, map_sub, map_mul, map_pow, map_sum, map_prod, map_one, π_C, π_X,
        ← hεdef]
    have e1 : ∀ q ∈ S, (sc (t q) * (1 - sc (x q) * ε) + sc (u q) * ε)
        * (∏ q' ∈ S.erase q, (1 - sc (x q') * ε) ^ 2) * ε ^ 2
        = π hr ^ 2 * (sc (t q) * ε ^ 2 + sc (u q + x q * t q) * ε ^ 3) := by
      intro q hq
      rw [trunc_alpha_summand hε, eP q hq, map_add, map_mul]
    rw [e0, sum_congr rfl e1, ← mul_sum, sum_add_distrib, ← sum_mul, ← sum_mul,
      ← map_sum, ← map_sum, ← htK, ← hwK]
    ring

  have ELHS : π (C 4) * π Ar ^ 3 + π (C c₂) * ε * π Ar ^ 2 * π hr ^ 2
      + π (C c₁) * ε ^ 2 * π Ar * π hr ^ 4 + π (C c₀) * ε ^ 3 * π hr ^ 6
      = π hr ^ 6 * (4 + sc c₂ * ε + (12 * sc tK + sc c₁) * ε ^ 2
          + (12 * sc wK + 2 * sc c₂ * sc tK + sc c₀) * ε ^ 3) := by
    rw [Eα, π_C, π_C, π_C, π_C, map_ofNat]
    exact trunc_lhs hε _ _ _ _ _ _

  have Eμ : ∀ q ∈ S, π (mr q) * (1 - sc (x q) * ε)
      = 1 - 4 * sc (d q) * ε - (sc b₄ + sc b₂ * sc (d q)) * ε ^ 2
        - (2 * sc b₆ + 2 * sc b₄ * sc (d q)) * ε ^ 3 := by
    intro q hq
    have e := congrArg π (Hmr q hq)
    simp only [map_sub, map_add, map_mul, map_pow, map_one, π_C, π_X, map_ofNat,
      ← hεdef] at e
    rw [e]
    exact trunc_num hε _ _ _ _ _
  have ERHS : (π fr * ∏ q ∈ S, π (mr q) ^ 2) * π hr ^ 2
      = π fr * π hr ^ 8 * (1 + ε ^ 2 * (-2 * sc tK - 4 * sc wK * ε)) := by
    have e1 : (∏ q ∈ S, π (mr q) ^ 2) * π hr ^ 2
        = ∏ q ∈ S, (π (mr q) * (1 - sc (x q) * ε)) ^ 2 := by
      rw [Eη, ← prod_pow, ← prod_mul_distrib]
      exact prod_congr rfl fun q _ => by ring
    have e2 : ∏ q ∈ S, (π (mr q) * (1 - sc (x q) * ε)) ^ 2
        = ∏ q ∈ S, ((1 - sc (d q) * ε) ^ 8
            * (1 + ε ^ 2 * (-2 * (6 * sc (d q) ^ 2 + sc b₂ * sc (d q) + sc b₄)
              - 4 * (10 * sc (d q) ^ 3 + 2 * sc b₂ * sc (d q) ^ 2 + 3 * sc b₄ * sc (d q) + sc b₆) * ε))) :=
      prod_congr rfl fun q hq => by rw [Eμ q hq, trunc_perq hε]
    have e3 : ∏ q ∈ S, ((1 - sc (d q) * ε) ^ 8
            * (1 + ε ^ 2 * (-2 * (6 * sc (d q) ^ 2 + sc b₂ * sc (d q) + sc b₄)
              - 4 * (10 * sc (d q) ^ 3 + 2 * sc b₂ * sc (d q) ^ 2 + 3 * sc b₄ * sc (d q) + sc b₆) * ε)))
        = π hr ^ 8 * (1 + ε ^ 2 * ∑ q ∈ S, (-2 * (6 * sc (x q) ^ 2 + sc b₂ * sc (x q) + sc b₄)
              - 4 * (10 * sc (x q) ^ 3 + 2 * sc b₂ * sc (x q) ^ 2 + 3 * sc b₄ * sc (x q) + sc b₆) * ε)) := by
      have p1 := prod_eq_of_map_eq S hperm (fun a => (1 - sc a * ε) ^ 8)
      have p2 := prod_eq_of_map_eq S hperm (fun a => 1 + ε ^ 2 * (-2 * (6 * sc (a) ^ 2 + sc b₂ * sc (a) + sc b₄)
              - 4 * (10 * sc (a) ^ 3 + 2 * sc b₂ * sc (a) ^ 2 + 3 * sc b₄ * sc (a) + sc b₆) * ε))
      rw [prod_mul_distrib, p1, p2, prod_one_add_sq_mul S ε hε, Eη, prod_pow]
    have e4 : ∑ q ∈ S, (-2 * (6 * sc (x q) ^ 2 + sc b₂ * sc (x q) + sc b₄)
              - 4 * (10 * sc (x q) ^ 3 + 2 * sc b₂ * sc (x q) ^ 2 + 3 * sc b₄ * sc (x q) + sc b₆) * ε) = -2 * sc tK - 4 * sc wK * ε := by
      have e5 : ∀ q ∈ S, (-2 * (6 * sc (x q) ^ 2 + sc b₂ * sc (x q) + sc b₄)
              - 4 * (10 * sc (x q) ^ 3 + 2 * sc b₂ * sc (x q) ^ 2 + 3 * sc b₄ * sc (x q) + sc b₆) * ε)
          = -2 * sc (t q) - 4 * sc (u q + x q * t q) * ε := by
        intro q hq
        rw [ht q hq, hu q hq]
        simp only [map_add, map_mul, map_pow, map_ofNat]
        ring
      rw [sum_congr rfl e5, sum_sub_distrib, ← mul_sum, ← sum_mul, ← mul_sum, ← map_sum,
        ← map_sum, ← htK, ← hwK]
    rw [mul_assoc, e1, e2, e3, e4]
    ring

  have Rπ := congrArg (fun z => π z * π hr ^ 2) R
  simp only [map_add, map_mul, map_pow, map_prod, π_X, ← hεdef] at Rπ
  rw [ELHS, ERHS] at Rπ
  have main : π hr ^ 8 * (4 + sc c₂ * ε + (12 * sc tK + sc c₁) * ε ^ 2
      + (12 * sc wK + 2 * sc c₂ * sc tK + sc c₀) * ε ^ 3)
      = π hr ^ 8 * (π fr * (1 + ε ^ 2 * (-2 * sc tK - 4 * sc wK * ε))) := by
    linear_combination Rπ
  have main2 := (hηunit.pow 8).mul_left_cancel main
  rw [Eφ, trunc_phi hε] at main2

  have final : π (C 4 + C c₂ * X + C (12 * tK + c₁) * X ^ 2
      + C (12 * wK + 2 * c₂ * tK + c₀) * X ^ 3)
      = π (C 4 + C b₂ * X + C (2 * b₄ - 8 * tK) * X ^ 2
      + C (b₆ - 2 * b₂ * tK - 16 * wK) * X ^ 3) := by
    simp only [map_add, map_sub, map_mul, map_pow, π_C, π_X, map_ofNat, ← hεdef]
    exact main2
  have hdeg3 : ∀ a₀ a₁ a₂ a₃ : K,
      (C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 : K[X]).natDegree ≤ 3 := by
    intro a₀ a₁ a₂ a₃
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (by simp) ?_) ?_) ?_
    · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by norm_num))
    · exact (natDegree_C_mul_le _ _).trans ((natDegree_pow_le_of_le 2 natDegree_X_le).trans
        (by norm_num))
    · exact (natDegree_C_mul_le _ _).trans (natDegree_pow_le_of_le 3 natDegree_X_le)
  have poly_eq := eq_of_π_eq (hdeg3 _ _ _ _) (hdeg3 _ _ _ _) final
  have k1 := congrArg (fun p : K[X] => p.coeff 1) poly_eq
  have k2 := congrArg (fun p : K[X] => p.coeff 2) poly_eq
  have k3 := congrArg (fun p : K[X] => p.coeff 3) poly_eq
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at k1 k2 k3
  norm_num at k1 k2 k3
  refine ⟨k1, ?_, ?_⟩
  · linear_combination k2
  · linear_combination k3 - 2 * tK * k1


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
