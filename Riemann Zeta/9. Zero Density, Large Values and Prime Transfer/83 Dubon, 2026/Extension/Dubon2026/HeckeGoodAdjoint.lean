import Dubon2026.HeckePrimeAdjoint
import Dubon2026.HeckeCommutativity

/-! # Petersson self-adjointness at every index coprime to the level -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- Self-adjointness for the actual Petersson pairing on genuine cusp forms. -/
def IsCuspPeterssonSelfAdjoint {Q : ℕ} [NeZero Q] {k : ℤ}
    (A : Module.End ℂ (CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)) : Prop :=
  ∀ f g, cuspPetersson (A f) g = cuspPetersson f (A g)

/-- The identity endomorphism is self-adjoint. -/
theorem cuspPeterssonSelfAdjoint_one (Q : ℕ) [NeZero Q] (k : ℤ) :
    IsCuspPeterssonSelfAdjoint (1 : Module.End ℂ (CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)) :=
  fun _ _ => rfl

/-- The zero endomorphism is self-adjoint. -/
theorem cuspPeterssonSelfAdjoint_zero (Q : ℕ) [NeZero Q] (k : ℤ) :
    IsCuspPeterssonSelfAdjoint (0 : Module.End ℂ (CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)) := by
  intro f g
  change cuspPetersson 0 g = cuspPetersson f 0
  rw [cuspPetersson_zero_left, cuspPetersson_zero_right]

/-- Commuting actual self-adjoint endomorphisms have self-adjoint composition. -/
theorem cuspPeterssonSelfAdjoint_mul {Q : ℕ} [NeZero Q] {k : ℤ}
    {A B : Module.End ℂ (CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)}
    (hA : IsCuspPeterssonSelfAdjoint A) (hB : IsCuspPeterssonSelfAdjoint B)
    (hAB : Commute A B) : IsCuspPeterssonSelfAdjoint (A * B) := by
  intro f g
  change cuspPetersson (A (B f)) g = cuspPetersson f ((A * B) g)
  rw [hA, hB]
  exact congrArg (cuspPetersson f) (LinearMap.congr_fun hAB.eq g).symm

/-- Differences preserve actual Petersson self-adjointness. -/
theorem cuspPeterssonSelfAdjoint_sub {Q : ℕ} [NeZero Q] {k : ℤ}
    {A B : Module.End ℂ (CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)}
    (hA : IsCuspPeterssonSelfAdjoint A) (hB : IsCuspPeterssonSelfAdjoint B) :
    IsCuspPeterssonSelfAdjoint (A - B) := by
  intro f g
  change cuspPetersson (A f - B f) g = cuspPetersson f (A g - B g)
  simp only [sub_eq_add_neg, cuspPetersson_add_left, cuspPetersson_add_right,
    cuspPetersson_neg_left, cuspPetersson_neg_right]
  rw [hA f g, hB f g]

/-- Conjugation-fixed scalars preserve actual Petersson self-adjointness. -/
theorem cuspPeterssonSelfAdjoint_smul {Q : ℕ} [NeZero Q] {k : ℤ}
    {A : Module.End ℂ (CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)}
    (hA : IsCuspPeterssonSelfAdjoint A) (c : ℂ) (hc : starRingEnd ℂ c = c) :
    IsCuspPeterssonSelfAdjoint (c • A) := by
  intro f g
  change cuspPetersson (c • A f) g = cuspPetersson f (c • A g)
  rw [cuspPetersson_conj_smul_left, cuspPetersson_smul_right, hc, hA]

/-- Every good prime-power operator is self-adjoint for the actual pairing. -/
theorem cuspHeckeLinear_primePower_selfAdjoint {Q p : ℕ} [NeZero Q] [NeZero p] (k : ℤ)
    (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) (r : ℕ) :
    IsCuspPeterssonSelfAdjoint (cuspHeckeLinear Q k (p ^ r)) := by
  have hprime : IsCuspPeterssonSelfAdjoint (cuspHeckeLinear Q k p) :=
    cuspHecke_prime_selfAdjoint hp hpQ
  induction r using Nat.twoStepInduction with
  | zero => simpa only [pow_zero, cuspHeckeLinear_one] using cuspPeterssonSelfAdjoint_one Q k
  | one => simpa only [pow_one] using hprime
  | more r ih0 ih1 =>
    rw [cuspHeckeLinear_primePower_recurrence Q k hp]
    apply cuspPeterssonSelfAdjoint_sub
      (cuspPeterssonSelfAdjoint_mul hprime ih1 (cuspHeckeLinear_commute Q k p (p ^ (r + 1))))
    apply cuspPeterssonSelfAdjoint_smul ih0
    change starRingEnd ℂ (if Nat.Coprime p Q then (p : ℂ) ^ (k - 1) else 0) =
      (if Nat.Coprime p Q then (p : ℂ) ^ (k - 1) else 0)
    rw [if_pos hpQ, map_zpow₀, map_natCast]

/-- Every actual classical operator at an index coprime to the level is self-adjoint. -/
theorem cuspHeckeLinear_coprime_selfAdjoint (Q : ℕ) [NeZero Q] (k : ℤ) (n : ℕ)
    (hnQ : Nat.Coprime n Q) : IsCuspPeterssonSelfAdjoint (cuspHeckeLinear Q k n) := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => rw [cuspHeckeLinear_zero]; exact cuspPeterssonSelfAdjoint_zero Q k
  | prime_pow p r hp =>
    haveI : NeZero p := ⟨hp.ne_zero⟩
    cases r with
    | zero => simpa only [pow_zero, cuspHeckeLinear_one] using cuspPeterssonSelfAdjoint_one Q k
    | succ r =>
      apply cuspHeckeLinear_primePower_selfAdjoint k hp
      exact hnQ.of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero r))
  | coprime a b ha hb hab iha ihb =>
    rw [← cuspHeckeLinear_coprime_mul Q k (by omega) (by omega) hab]
    exact cuspPeterssonSelfAdjoint_mul (iha (Nat.coprime_mul_iff_left.mp hnQ).1) (ihb (Nat.coprime_mul_iff_left.mp hnQ).2)
      (cuspHeckeLinear_commute Q k a b)

end
end Dubon2026
