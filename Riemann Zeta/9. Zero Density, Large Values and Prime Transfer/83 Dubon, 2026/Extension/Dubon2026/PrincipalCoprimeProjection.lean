import Dubon2026.PrincipalOrbitProjection
import Mathlib.Data.Nat.PrimeFin

/-! # The actual projection onto Fourier indices coprime to the level -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- Complements of actual divisor projections commute for every pair of divisors. -/
theorem principalComplementProjection_commute {N d e : ℕ} [NeZero N]
    (hd : d ∣ N) (he : e ∣ N) (k : ℤ) :
    Commute (1 - principalDivisorProjection N k d) (1 - principalDivisorProjection N k e) := by
  letI : NeZero d := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) hd⟩
  letI : NeZero e := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) he⟩
  exact (Commute.one_left _).sub_left
    ((Commute.one_right _).sub_right (principalDivisorProjection_commute hd he k))

/-- The literal product of translation-projection complements over a finite divisor set. -/
def principalAvoidProjection (N : ℕ) [NeZero N] (k : ℤ)
    (s : Finset ℕ) (hs : ∀ d ∈ s, d ∣ N) :
    CuspForm ((Gamma N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma N).map (mapGL ℝ)) k :=
  s.noncommProd (fun d => 1 - principalDivisorProjection N k d)
    (fun _ hd _ he _ => principalComplementProjection_commute (hs _ hd) (hs _ he) k)

/-- One complement erases precisely the divisible Fourier indices. -/
theorem principalComplementProjection_coeff {N d : ℕ} [NeZero N] (hd : d ∣ N)
    (k : ℤ) (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (n : ℕ) :
    principalCuspCoefficients ((1 - principalDivisorProjection N k d) f) n =
      if d ∣ n then 0 else principalCuspCoefficients f n := by
  letI : NeZero d := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) hd⟩
  change principalCuspCoefficientLinear N k n (f - principalDivisorProjection N k d f) = _
  rw [map_sub]
  change principalCuspCoefficients f n -
    principalCuspCoefficients (principalDivisorProjection N k d f) n = _
  rw [principalDivisorProjection_coeff hd]
  split_ifs <;> simp

/-- Every Fourier coefficient of the literal product is computed exactly. -/
theorem principalAvoidProjection_coeff (N : ℕ) [NeZero N] (k : ℤ)
    (s : Finset ℕ) (hs : ∀ d ∈ s, d ∣ N)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (n : ℕ) :
    principalCuspCoefficients (principalAvoidProjection N k s hs f) n =
      if ∀ d ∈ s, ¬d ∣ n then principalCuspCoefficients f n else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [principalAvoidProjection]
  | insert d s hd ih =>
    unfold principalAvoidProjection
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hd, Module.End.mul_apply,
      principalComplementProjection_coeff (hs d (Finset.mem_insert_self d s))]
    change (if d ∣ n then 0 else principalCuspCoefficients
      (principalAvoidProjection N k s (fun e he => hs e (Finset.mem_insert_of_mem he)) f) n) = _
    rw [ih]
    by_cases hdn : d ∣ n <;> simp [hdn]

/-- Avoiding all prime factors is exactly coprimality, including index zero and level one. -/
theorem forall_primeFactors_not_dvd_iff (N : ℕ) [NeZero N] (n : ℕ) :
    (∀ p ∈ N.primeFactors, ¬p ∣ n) ↔ N.Coprime n := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨p, hp, hpN, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpN, NeZero.ne N⟩) hpn
  · intro h p hp hpn
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpN := Nat.dvd_of_mem_primeFactors hp
    exact (hprime.coprime_iff_not_dvd.mp (h.of_dvd_left hpN)) hpn

/-- The literal finite product keeps exactly the coefficients coprime to the principal level. -/
theorem principalCoprimeProjection_coeff (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (n : ℕ) :
    principalCuspCoefficients (principalAvoidProjection N k N.primeFactors
      (fun _ hp => Nat.dvd_of_mem_primeFactors hp) f) n =
      if N.Coprime n then principalCuspCoefficients f n else 0 := by
  simp only [principalAvoidProjection_coeff, forall_primeFactors_not_dvd_iff]

/-- Vanishing of all coprime coefficients annihilates the actual finite operator product. -/
theorem principalCoprimeProjection_eq_zero_iff (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    principalAvoidProjection N k N.primeFactors (fun _ hp => Nat.dvd_of_mem_primeFactors hp) f = 0 ↔
      ∀ n, N.Coprime n → principalCuspCoefficients f n = 0 := by
  constructor
  · intro hf n hn
    have he := congrArg (fun g => principalCuspCoefficients g n) hf
    dsimp only at he
    rw [principalCoprimeProjection_coeff, if_pos hn] at he
    exact he.trans ((principalCuspCoefficientLinear N k n).map_zero)
  · intro hf
    apply principalCuspCoefficients_injective N k
    funext n
    rw [principalCoprimeProjection_coeff, show principalCuspCoefficients
      (0 : CuspForm ((Gamma N).map (mapGL ℝ)) k) n = 0 from
        (principalCuspCoefficientLinear N k n).map_zero]
    by_cases hn : N.Coprime n
    · simpa only [if_pos hn] using hf n hn
    · exact if_neg hn

end
end Dubon2026
