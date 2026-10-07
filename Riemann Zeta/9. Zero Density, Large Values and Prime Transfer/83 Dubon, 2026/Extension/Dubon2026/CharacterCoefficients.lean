import Dubon2026.DyadicPrimes
import Dubon2026.PotentialPointwise
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-! # Actual Dirichlet-character coefficients and the eventual ordinary prime block -/

namespace Dubon2026

open Filter

noncomputable section

/-- Values of the actual character at natural-number residue classes. -/
def characterCoefficients {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ := χ (n : ZMod q)

theorem characterCoefficients_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    characterCoefficients χ 1 = 1 := by simp only [characterCoefficients, Nat.cast_one, map_one]

theorem norm_characterCoefficients_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖characterCoefficients χ n‖ ≤ 1 := χ.norm_le_one _

theorem norm_characterCoefficients_of_coprime {q n : ℕ} (χ : DirichletCharacter ℂ q)
    (h : n.Coprime q) : ‖characterCoefficients χ n‖ = 1 := by
  have hu := (ZMod.isUnit_iff_coprime n q).mpr h
  simpa only [IsUnit.unit_spec, characterCoefficients] using χ.unit_norm_eq_one hu.unit

theorem characterCoefficients_of_not_coprime {q n : ℕ} (χ : DirichletCharacter ℂ q)
    (h : ¬ n.Coprime q) : characterCoefficients χ n = 0 := by
  exact χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime])

theorem norm_sq_characterCoefficients {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖characterCoefficients χ n‖ ^ 2 = if n.Coprime q then 1 else 0 := by
  by_cases h : n.Coprime q
  · rw [if_pos h, norm_characterCoefficients_of_coprime χ h, one_pow]
  · rw [if_neg h, characterCoefficients_of_not_coprime χ h, norm_zero, zero_pow (by norm_num)]

theorem character_coefficientEnergy_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (σ : ℝ) :
    coefficientEnergy (characterCoefficients χ) N σ =
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (n : ℝ) ^ (-2 * σ) := by
  simp only [coefficientEnergy, norm_sq_characterCoefficients, Finset.sum_filter,
    ite_mul, one_mul, zero_mul]

theorem eventually_dyadic_character_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∀ᶠ N : ℕ in atTop, ∀ p ∈ dyadicPrimes N, ‖characterCoefficients χ p‖ = 1 := by
  filter_upwards [eventually_ge_atTop (2 * q)] with N hN
  intro p hp
  obtain ⟨hpprime, hphalf, _⟩ := mem_dyadicPrimes.mp hp
  have hqp : q < p := by
    have hNr : (2 : ℝ) * q ≤ N := by exact_mod_cast hN
    have hpr : (q : ℝ) < p := by linarith
    exact_mod_cast hpr
  apply norm_characterCoefficients_of_coprime χ
  apply hpprime.coprime_iff_not_dvd.mpr
  intro hd
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  exact (not_le_of_gt hqp) (Nat.le_of_dvd hqpos hd)

theorem eventually_character_isolatedEnergy_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ∀ᶠ N : ℕ in atTop, ∀ σ : ℝ,
      isolatedPrimeEnergy (characterCoefficients χ) dyadicPrimes N σ =
        isolatedPrimeEnergy (fun _ => (1 : ℂ)) dyadicPrimes N σ := by
  filter_upwards [eventually_dyadic_character_norm χ] with N hn
  intro σ
  apply Finset.sum_congr rfl
  intro p hp
  rw [hn p hp, norm_one]

end

end Dubon2026
