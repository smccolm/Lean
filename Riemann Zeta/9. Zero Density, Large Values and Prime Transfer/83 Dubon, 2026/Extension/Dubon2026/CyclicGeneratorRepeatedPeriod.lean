import Dubon2026.CyclicTwoCocyclePeriodSum

/-! # Repetition of literal original generator periods -/

namespace Dubon2026

open scoped BigOperators

/-- A sum of original generator values over repeated full periods is the
actual number of repetitions times the original single-period sum. -/
theorem cyclicGenerator_sum_repeated {G V : Type*} [Group G] [AddCommMonoid V]
    (g : G) (n : ℕ) (hn : g ^ n = 1) (k : ℕ) (f : G → V) :
    (∑ i ∈ Finset.range (n * k), f (g ^ i)) =
      k • ∑ i ∈ Finset.range n, f (g ^ i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add]
    simp only [pow_add, pow_mul, hn, one_pow, one_mul]
    rw [ih, succ_nsmul]

/-- The literal original two-cochain period has the same exact repetition law. -/
theorem representationCyclicTwoCochainPeriodSum_repeat
    {R G : Type} [CommRing R] [Group G] (A : Rep R G)
    (g : G) (n : ℕ) (hn : g ^ n = 1) (k : ℕ) (c : G × G → A) :
    representationCyclicTwoCochainPeriodSum A g (n * k) c =
      k • representationCyclicTwoCochainPeriodSum A g n c := by
  exact cyclicGenerator_sum_repeated g n hn k (fun x => c (x, g))

end Dubon2026
