import Dubon2026.OriginalCyclicContinuousH2CarryRepresentatives
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-! # The constructed odd prime cyclotomic Galois stage is nontrivial

Pinned cyclotomic degree and prime-power totient formulas discharge the
nontriviality premise of the original cyclic carry theorem. This applies
to the actual arithmetic cyclotomic stage in DUB-17's invariant-sum route.
-/
namespace Dubon2026
noncomputable section

/-- Every original cyclotomic extension of odd prime-power conductor has more than one actual Galois automorphism. -/
theorem oddPrimeCyclotomic_galois_card_gt_one
    (L : Type) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (q k : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    [IsCyclotomicExtension {q ^ (k + 1)} ℚ L] : 1 < Nat.card Gal(L/ℚ) := by
  letI : NeZero (q ^ (k + 1)) := ⟨pow_ne_zero _ hq.ne_zero⟩
  rw [IsGalois.card_aut_eq_finrank,
    IsCyclotomicExtension.finrank L (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (q ^ (k + 1)))),
    Nat.totient_prime_pow hq (Nat.succ_pos k)]
  have hpow : 1 ≤ q ^ k := one_le_pow₀ hq.one_le
  have hq3 : 3 ≤ q := by have h := hq.two_le; omega
  have hpred : 2 ≤ q - 1 := by omega
  simp only [Nat.succ_sub_one]
  nlinarith

end
end Dubon2026
