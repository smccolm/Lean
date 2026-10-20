import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-! # The source auxiliary prime has sufficiently large cyclotomic degree

For BLGG 3.6.1 on the DUB-17 potential-automorphy chain, the stronger
large-prime bound already used by the unitary congruence argument also
implies the source restriction [K(zeta_p):K] > n. The proof uses the
existing primitive-root degree bound and the original field tower.
-/

namespace Dubon2026
noncomputable section

/-- Any finite extension containing a primitive p-th root has the required degree once the original rational prime exceeds the source bound. -/
theorem numberField_cyclotomic_degree_gt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (p n : ℕ) (hp : p.Prime)
    (hlarge : n * Module.finrank ℚ K < p - 1)
    (z : L) (hz : IsPrimitiveRoot z p) :
    n < Module.finrank K L := by
  have hd : p - 1 ≤ Module.finrank ℚ L := by
    have h := hz.lcm_totient_le_finrank (K := ℚ) hz
      (by simpa only [Nat.lcm_self] using Polynomial.cyclotomic.irreducible_rat hp.pos)
    simpa only [Nat.lcm_self, Nat.totient_prime hp] using h
  have ht := Module.finrank_mul_finrank ℚ K L
  by_contra hn
  have hb := Nat.mul_le_mul_left (Module.finrank ℚ K) (Nat.le_of_not_gt hn)
  rw [ht] at hb
  nlinarith

end
end Dubon2026
