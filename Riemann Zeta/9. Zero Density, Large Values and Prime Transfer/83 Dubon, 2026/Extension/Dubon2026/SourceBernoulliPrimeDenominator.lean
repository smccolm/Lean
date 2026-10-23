import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Rat.Lemmas

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> automorphy and residual association -> original Frobenius/inertia
-> modular-curve good reduction -> exact residue-field degree -> prime j
nonmembership. The integral Eisenstein series of weight ell - 1 supplies the
Hasse polynomial input with nonzero constant reduction. This file does not yet
construct that polynomial or prove unconditional prime nonmembership.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_eisInt_series. Reuses the pinned Mathlib
von Staudt-Clausen and Eisenstein q-expansion theorems directly. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open scoped ArithmeticFunction.sigma
open Finset

theorem eisInt_not_dvd_den_shift {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ¬ ℓ ∣ (bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)).den := by
  have hℓp : ℓ.Prime := Fact.out

  obtain ⟨m, hm⟩ := hℓp.odd_of_ne_two (by omega)
  set k₀ := (ℓ - 1) / 2 with hk₀def
  have h2k₀ : 2 * k₀ = ℓ - 1 := by omega

  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k₀

  rw [h2k₀] at hz
  have hrange : ℓ - 1 + 2 = ℓ + 1 := by omega
  rw [hrange] at hz

  set S := {p ∈ range (ℓ + 1) | p.Prime ∧ p - 1 ∣ ℓ - 1} with hSdef
  have hℓS : ℓ ∈ S := by
    simp only [hSdef, mem_filter, mem_range]
    exact ⟨Nat.lt_succ_self ℓ, hℓp, dvd_refl _⟩

  have hsplit := (add_sum_erase S (fun p => (1 : ℚ) / (p : ℚ)) hℓS).symm
  rw [hsplit] at hz

  have hz' : bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)
      = (z : ℚ) - ∑ p ∈ S.erase ℓ, (1 : ℚ) / (p : ℚ) := by
    linarith [hz]
  rw [hz', Rat.intCast_sub_den]

  have hdendvd := Rat.den_sum_dvd_prod_den (S.erase ℓ) (fun p => (1 : ℚ) / (p : ℚ))
  have hcop : (∏ p ∈ S.erase ℓ, ((1 : ℚ) / (p : ℚ)).den).Coprime ℓ := by
    refine Nat.Coprime.prod_left fun p hp => ?_
    have hpS : p ∈ S := Finset.mem_of_mem_erase hp
    have hpne : p ≠ ℓ := Finset.ne_of_mem_erase hp
    have hpp : p.Prime := (mem_filter.mp hpS).2.1
    have : ((1 : ℚ) / (p : ℚ)).den = p := by simp [hpp.ne_zero]
    rw [this]
    exact (Nat.coprime_primes hpp hℓp).mpr hpne
  intro hdvd
  exact (Nat.Prime.coprime_iff_not_dvd hℓp).mp
    (Nat.Coprime.of_dvd_left hdendvd hcop).symm hdvd



theorem eisInt_dvd_den {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ℓ ∣ (bernoulli (ℓ - 1)).den := by
  have hℓp : ℓ.Prime := Fact.out
  have hshift := eisInt_not_dvd_den_shift hℓ5

  have hℓden : ((1 : ℚ) / (ℓ : ℚ)).den = ℓ := by simp [hℓp.ne_zero]
  have hdvd : ℓ ∣ (bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)).den * (bernoulli (ℓ - 1)).den := by
    have h := Rat.sub_den_dvd (bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)) (bernoulli (ℓ - 1))
    have hsimp : bernoulli (ℓ - 1) + 1 / (ℓ : ℚ) - bernoulli (ℓ - 1) = 1 / (ℓ : ℚ) := by ring
    rw [hsimp, hℓden] at h
    exact h
  exact ((hℓp.dvd_mul).mp hdvd).resolve_left hshift


end
end Dubon2026.SourceFunctionField
