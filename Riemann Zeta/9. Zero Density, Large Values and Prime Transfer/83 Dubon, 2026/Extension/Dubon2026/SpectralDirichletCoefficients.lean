import Dubon2026.EulerCoefficientAssembly
import Dubon2026.SpectralFormalEvaluation

/-! # Actual Dirichlet coefficients of arbitrary finite spectral Euler systems -/

namespace Dubon2026

noncomputable section
open scoped ComplexOrder

/-- Extend the literal spectral local coefficients to natural prime indices. -/
def spectralNatLocalCoeff {ι : Type*} [Fintype ι] (w : Nat.Primes → ι → ℂ)
    (p n : ℕ) : ℂ :=
  if hp : Nat.Prime p then PowerSeries.coeff n (spectralFormalEuler Finset.univ (w ⟨p, hp⟩))
  else if n = 0 then 1 else 0

/-- The genuine spectral Dirichlet coefficient, assembled by unique prime factorization. -/
def spectralDirichletCoefficient {ι : Type*} [Fintype ι] (w : Nat.Primes → ι → ℂ) : ℕ → ℂ :=
  assembledEulerCoefficient (spectralNatLocalCoeff w)

/-- The local coefficient of degree zero is one at every natural index. -/
theorem spectralNatLocalCoeff_zero {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (p : ℕ) : spectralNatLocalCoeff w p 0 = 1 := by
  by_cases hp : Nat.Prime p <;> simp [spectralNatLocalCoeff, hp, coeff_zero_spectralFormalEuler]

/-- The assembled spectral coefficient at one is one. -/
theorem spectralDirichletCoefficient_one {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) : spectralDirichletCoefficient w 1 = 1 :=
  assembledEulerCoefficient_one _

/-- At an actual prime power, the genuine Dirichlet coefficient recovers the literal formal Euler coefficient. -/
theorem spectralDirichletCoefficient_prime_pow {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (p : Nat.Primes) (n : ℕ) :
    spectralDirichletCoefficient w ((p : ℕ) ^ n) =
      PowerSeries.coeff n (spectralFormalEuler Finset.univ (w p)) := by
  rw [spectralDirichletCoefficient, assembledEulerCoefficient_prime_pow _
    (spectralNatLocalCoeff_zero w) p.property, spectralNatLocalCoeff, dif_pos p.property]
  rfl

/-- Nonnegative actual power traces give nonnegative actual global coefficients. -/
theorem spectralDirichletCoefficient_nonneg {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (hw : ∀ p n, 0 < n → 0 ≤ ∑ i, w p i ^ n)
    (n : ℕ) : 0 ≤ spectralDirichletCoefficient w n := by
  apply assembledEulerCoefficient_nonneg
  intro p r
  by_cases hp : Nat.Prime p
  · simpa only [spectralNatLocalCoeff, dif_pos hp] using
      spectralFormalEuler_coeff_nonneg Finset.univ (w ⟨p, hp⟩) (hw ⟨p, hp⟩) r
  · simp only [spectralNatLocalCoeff, dif_neg hp]
    split_ifs
    · exact zero_le_one
    · exact le_rfl

/-- A polynomial prime bound for the roots bounds every literal local Euler coefficient. -/
theorem spectral_local_coeff_norm_le {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (d : ℕ)
    (hw : ∀ p i, ‖w p i‖ ≤ ((p : ℕ) : ℝ) ^ d) (p : Nat.Primes) (n : ℕ) :
    ‖PowerSeries.coeff n (spectralFormalEuler Finset.univ (w p))‖ ≤
      (((p : ℕ) : ℝ) ^ n) ^ (d + Fintype.card ι + 1) := by
  let c : ℕ := Fintype.card ι + 1
  have hc : 1 ≤ (c : ℝ) := by dsimp [c]; norm_num
  have hp2 : 2 ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.property.two_le
  have hcp : (c : ℝ) ≤ ((p : ℕ) : ℝ) ^ c := by
    calc
      _ ≤ (2 : ℝ) ^ c := by exact_mod_cast c.lt_two_pow_self.le
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hp2 c
  have htrace (m : ℕ) (hm : 0 < m) :
      ‖∑ i, w p i ^ m‖ ≤ (((p : ℕ) : ℝ) ^ (d + c)) ^ m := by
    calc
      _ ≤ ∑ i, ‖w p i ^ m‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, (((p : ℕ) : ℝ) ^ d) ^ m := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hw p i) m
      _ = (Fintype.card ι : ℝ) * (((p : ℕ) : ℝ) ^ d) ^ m := by simp
      _ ≤ (c : ℝ) ^ m * (((p : ℕ) : ℝ) ^ d) ^ m := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (by dsimp [c]; norm_num : (Fintype.card ι : ℝ) ≤ c).trans (le_self_pow₀ hc (ne_of_gt hm))
      _ = ((c : ℝ) * ((p : ℕ) : ℝ) ^ d) ^ m := by rw [mul_pow]
      _ ≤ (((p : ℕ) : ℝ) ^ (d + c)) ^ m := by
        apply pow_le_pow_left₀ (by positivity)
        rw [pow_add, mul_comm]
        exact mul_le_mul_of_nonneg_left hcp (by positivity)
  have hh := norm_spectralFormalEuler_coeff_le Finset.univ (w p)
    (by positivity : 0 ≤ ((p : ℕ) : ℝ) ^ (d + c)) htrace n
  simpa only [c, ← pow_mul, Nat.add_assoc, Nat.mul_comm (d + (Fintype.card ι + 1)) n] using hh

/-- The genuine spectral coefficients have a proved finite abscissa of absolute convergence. -/
theorem spectralDirichletCoefficient_abscissa_le {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (d : ℕ)
    (hw : ∀ p i, ‖w p i‖ ≤ ((p : ℕ) : ℝ) ^ d) :
    LSeries.abscissaOfAbsConv (spectralDirichletCoefficient w) ≤
      ((d + Fintype.card ι + 1 : ℕ) : ℝ) + 1 := by
  apply assembledEulerCoefficient_abscissa_le
  intro p hp n
  simpa only [spectralNatLocalCoeff, dif_pos hp] using spectral_local_coeff_norm_le w d hw ⟨p, hp⟩ n

/-- The assembled genuine Dirichlet series has exactly its literal formal local Euler series. -/
theorem spectralDirichletCoefficient_hasProd {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) {s : ℂ} (hs : LSeriesSummable (spectralDirichletCoefficient w) s) :
    HasProd (fun p : Nat.Primes => ∑' n : ℕ,
      PowerSeries.coeff n (spectralFormalEuler Finset.univ (w p)) * ((((p : ℕ) : ℂ) ^ (-s)) ^ n))
      (LSeries (spectralDirichletCoefficient w) s) := by
  have hh := assembledEulerCoefficient_hasProd (spectralNatLocalCoeff w) (spectralNatLocalCoeff_zero w) hs
  convert hh using 1
  funext p
  congr 1
  funext n
  rw [spectralNatLocalCoeff, dif_pos p.property]
  rfl

/-- A polynomial root bound places the true local spectral coordinates inside the convergence disk. -/
theorem spectral_prime_coordinate_lt_one {ι : Type*} (w : Nat.Primes → ι → ℂ) (d : ℕ)
    (hw : ∀ p i, ‖w p i‖ ≤ ((p : ℕ) : ℝ) ^ d)
    (p : Nat.Primes) (i : ι) {s : ℂ} (hs : (d : ℝ) < s.re) :
    ‖w p i * (((p : ℕ) : ℂ) ^ (-s))‖ < 1 := by
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
  calc
    _ ≤ ((p : ℕ) : ℝ) ^ d * ((p : ℕ) : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (hw p i) (by positivity)
    _ = ((p : ℕ) : ℝ) ^ ((d : ℝ) - s.re) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hp0]
      congr 1
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt) (by linarith)

end
end Dubon2026
