import Dubon2026.SourceSiegelJacobiFiniteProducts

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary existence -> literal Siegel-product
holomorphy and SL2 transformation -> Jacobi theta product identity. The
finite Gaussian identity is the source finite approximation needed to
identify the actual product with Mathlib's analytic theta function.
Native q-series multiplication and cusp limits are already proved and
will be reused. No abstract q-series generalization is introduced.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_jacobiTheta_two_eq_tprod. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.JacobiProduct
open Finset

theorem gauss_q {Q : ℂ} (hQ : ‖Q‖ < 1) (t : ℂ) (m : ℕ) :
    ∏ j ∈ Finset.range m, (1 + t * Q ^ j)
      = ∑ k ∈ Finset.range (m + 1), qbinom Q m k * Q ^ (k * (k - 1) / 2) * t ^ k := by
  induction m with
  | zero =>
    rw [Finset.prod_range_zero, Finset.sum_range_one, qbinom_zero_right hQ]
    norm_num
  | succ m ih =>
    have epow : ∀ k : ℕ, (k + 1) * ((k + 1) - 1) / 2 = k * (k - 1) / 2 + k := by
      intro k
      have h : (k + 1) * ((k + 1) - 1) = k * (k - 1) + 2 * k := by
        rcases k with _ | k'
        · norm_num
        · simp only [Nat.add_sub_cancel]
          ring
      rw [h, Nat.add_mul_div_left _ _ (by norm_num : (0 : ℕ) < 2)]
    rw [Finset.prod_range_succ, ih, mul_add, mul_one, Finset.sum_mul]

    rw [Finset.sum_range_succ' (fun k => qbinom Q (m + 1) k * Q ^ (k * (k - 1) / 2) * t ^ k) (m + 1)]

    have hterm : ∀ k ∈ Finset.range (m + 1),
        qbinom Q (m + 1) (k + 1) * Q ^ ((k + 1) * ((k + 1) - 1) / 2) * t ^ (k + 1)
          = qbinom Q m (k + 1) * Q ^ ((k + 1) * ((k + 1) - 1) / 2) * t ^ (k + 1)
            + qbinom Q m k * Q ^ (k * (k - 1) / 2) * t ^ k * (t * Q ^ m) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hkm : k ≤ m := by omega
      rw [qbinom_succ_succ hQ, add_mul, add_mul]
      congr 1

      rw [epow k]
      have hexp : Q ^ (m - k) * Q ^ (k * (k - 1) / 2 + k) = Q ^ (k * (k - 1) / 2) * Q ^ m := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      calc Q ^ (m - k) * qbinom Q m k * Q ^ (k * (k - 1) / 2 + k) * t ^ (k + 1)
          = qbinom Q m k * (Q ^ (m - k) * Q ^ (k * (k - 1) / 2 + k)) * t ^ (k + 1) := by ring
        _ = qbinom Q m k * (Q ^ (k * (k - 1) / 2) * Q ^ m) * t ^ (k + 1) := by rw [hexp]
        _ = qbinom Q m k * Q ^ (k * (k - 1) / 2) * t ^ k * (t * Q ^ m) := by
            rw [pow_succ]
            ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]

    have h1 : (qbinom Q (m + 1) 0 * Q ^ (0 * (0 - 1) / 2) * t ^ 0 : ℂ) = 1 := by
      rw [qbinom_zero_right hQ]
      norm_num
    have hfold : ∑ k ∈ Finset.range (m + 1), qbinom Q m k * Q ^ (k * (k - 1) / 2) * t ^ k
        = (∑ k ∈ Finset.range (m + 1),
            qbinom Q m (k + 1) * Q ^ ((k + 1) * ((k + 1) - 1) / 2) * t ^ (k + 1)) + 1 := by
      have key := Finset.sum_range_succ'
        (fun k => qbinom Q m k * Q ^ (k * (k - 1) / 2) * t ^ k) (m + 1)
      rw [Finset.sum_range_succ, qbinom_of_gt Q (Nat.lt_succ_self m), zero_mul, zero_mul,
        add_zero] at key
      rw [key]
      congr 1
      rw [qbinom_zero_right hQ]
      norm_num
    rw [hfold, h1]
    ring


end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.JacobiProduct
