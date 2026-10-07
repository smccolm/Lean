import Dubon2026.PrimitiveLatticeScaling
import Dubon2026.CoprimeMobius

/-! # The exact finite coprimality sieve for congruence Eisenstein rows -/

namespace Dubon2026

open EisensteinSeries

noncomputable section

/-- Actual congruence rows with lower-left entry divisible by Q and the other entry prime to Q. -/
def gamma0SievedRows (Q : ℕ) : Set (Fin 2 → ℤ) :=
  {v | (Q : ℤ) ∣ v 0 ∧ Nat.Coprime (v 1).natAbs Q}

/-- A primitive row with Q-divisible first entry automatically has second entry coprime to Q. -/
theorem primitive_row_coprime_level (Q : ℕ) (v : gammaSet 1 1 0) (hv : (Q : ℤ) ∣ v.val 0) :
    Nat.Coprime (v.val 1).natAbs Q := by
  have hp : Nat.Coprime (v.val 0).natAbs (v.val 1).natAbs := v.property.2
  exact (hp.coprime_dvd_left (Int.natCast_dvd.mp hv)).symm

/-- On genuine primitive rows, the finite sieve recovers exactly the Gamma0 divisibility condition. -/
theorem gamma0SievedRows_primitive (Q : ℕ) (v : gammaSet 1 1 0) :
    v.val ∈ gamma0SievedRows Q ↔ (Q : ℤ) ∣ v.val 0 :=
  ⟨fun h => h.1, fun h => ⟨h, primitive_row_coprime_level Q v h⟩⟩

/-- The actual gcd dilation separates the multiplier's coprimality from primitive Gamma0 membership. -/
theorem gamma0SievedRows_nsmul (Q n : ℕ) (v : gammaSet 1 1 0) :
    n • v.val ∈ gamma0SievedRows Q ↔ Nat.Coprime n Q ∧ (Q : ℤ) ∣ v.val 0 := by
  change ((Q : ℤ) ∣ n • (v.val 0) ∧ Nat.Coprime (n • (v.val 1)).natAbs Q) ↔ _
  simp only [nsmul_eq_mul,
    Int.natAbs_mul, Int.natAbs_natCast, Nat.coprime_mul_iff_left]
  constructor
  · rintro ⟨hd, hn, _⟩
    refine ⟨hn, Int.natCast_dvd.mpr ?_⟩
    have hd' := Int.natCast_dvd.mp hd
    rw [Int.natAbs_mul, Int.natAbs_natCast] at hd'
    exact hn.symm.dvd_mul_left.mp hd'
  · rintro ⟨hn, hd⟩
    exact ⟨dvd_mul_of_dvd_right hd _, hn, primitive_row_coprime_level Q v hd⟩

/-- The finite Möbius divisor sum is the exact coprimality indicator for an actual integer coordinate. -/
theorem int_coprime_indicator_moebius (Q : ℕ) (hQ : Q ≠ 0) (m : ℤ) :
    (if Nat.Coprime m.natAbs Q then (1 : ℂ) else 0) =
      ∑ d ∈ Q.divisors, if (d : ℤ) ∣ m then (ArithmeticFunction.moebius d : ℂ) else 0 := by
  have h := sum_moebius_gcd_eq_coprimeIndicator Q m.natAbs
  rw [divisors_gcd_eq_filter_dvd Q m.natAbs hQ, Finset.sum_filter] at h
  have hc := congrArg (fun a : ℤ => (a : ℂ)) h
  push_cast at hc
  simpa only [Int.natCast_dvd] using hc.symm

/-- The literal finite sieve converts Gamma0 congruence rows into a finite sum of sublattices. -/
theorem gamma0SievedRows_indicator_moebius (Q : ℕ) (hQ : Q ≠ 0) (v : Fin 2 → ℤ) :
    (if (Q : ℤ) ∣ v 0 ∧ Nat.Coprime (v 1).natAbs Q then (1 : ℂ) else 0) =
      ∑ d ∈ Q.divisors,
        if (Q : ℤ) ∣ v 0 ∧ (d : ℤ) ∣ v 1 then (ArithmeticFunction.moebius d : ℂ) else 0 := by
  classical
  by_cases hv : (Q : ℤ) ∣ v 0
  · simpa only [hv, true_and] using
      int_coprime_indicator_moebius Q hQ (v 1)
  · simp [hv]

end
end Dubon2026
