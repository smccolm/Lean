import Tao2026.PrimeIntervals
import Tao2026.PowerfulNumbers

/-!
# Elementary restrictions on very bad intervals

This module begins the source-faithful proof of Tao's Lemma 3.1.
-/

namespace Tao2026

open scoped BigOperators

theorem prime_dvd_consecutiveProduct_exactly_once
    {N H p : ℕ} (hp : p.Prime) (hNltp : N < p)
    (hpLe : p ≤ N + H) (hsumLt : N + H < 2 * p) :
    p ∣ consecutiveProduct N H ∧ ¬p ^ 2 ∣ consecutiveProduct N H := by
  have hpMem : p ∈ consecutiveInterval N H := by
    simpa [consecutiveInterval] using ⟨hNltp, hpLe⟩
  let remainder := ((consecutiveInterval N H).erase p).prod id
  have hproduct : consecutiveProduct N H = p * remainder := by
    rw [consecutiveProduct]
    change (∏ x ∈ consecutiveInterval N H, x) =
      p * ((consecutiveInterval N H).erase p).prod id
    exact (Finset.mul_prod_erase (consecutiveInterval N H) id hpMem).symm
  have hpNotDvdRemainder : ¬p ∣ remainder := by
    change ¬p ∣ ((consecutiveInterval N H).erase p).prod id
    apply hp.prime.not_dvd_finsetProd
    intro k hk hpk
    have hkMem : k ∈ consecutiveInterval N H := Finset.mem_of_mem_erase hk
    have hkPos : 0 < k :=
      lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hkMem).1
    have hkLe : k ≤ N + H := (Finset.mem_Ioc.mp hkMem).2
    have hkLt : k < 2 * p := hkLe.trans_lt hsumLt
    have hkp : k = p := by
      rcases hpk with ⟨c, rfl⟩
      have hcPos : 0 < c := by
        by_contra hc
        have : c = 0 := Nat.eq_zero_of_not_pos hc
        subst c
        simp at hkPos
      have hcLt : c < 2 := by
        apply (Nat.mul_lt_mul_left hp.pos).mp
        simpa [mul_comm] using hkLt
      have hc : c = 1 := by omega
      simp [hc]
    exact (Finset.ne_of_mem_erase hk) hkp
  constructor
  · rw [hproduct]
    exact dvd_mul_right p remainder
  · rw [hproduct, pow_two]
    intro hdvd
    exact hpNotDvdRemainder
      ((Nat.mul_dvd_mul_iff_left hp.pos).mp hdvd)

/-- The elementary first conclusion of Tao's Lemma 3.1 (`hvin`) for positive
starting points. The source's unrestricted natural-number wording has the
exceptional interval `{1}` at `N = 0`, since the literal definition makes
`1` powerful. -/
theorem IsVeryBadInterval.length_lt_start_of_pos {N H : ℕ}
    (hN : 1 ≤ N) (hveryBad : IsVeryBadInterval N H) : H < N := by
  by_contra hnot
  have hNLeH : N ≤ H := by omega
  have hsumTwo : 2 ≤ N + H := by omega
  obtain ⟨p, hp, hpLower, hpUpper⟩ := taoProposition23i hsumTwo
  have hNltp : N < p := by omega
  have hsumLt : N + H < 2 * p := by omega
  obtain ⟨hpdvd, hpSqNotDvd⟩ :=
    prime_dvd_consecutiveProduct_exactly_once hp hNltp hpUpper hsumLt
  exact hpSqNotDvd (hveryBad.2 p hp hpdvd)

end Tao2026
