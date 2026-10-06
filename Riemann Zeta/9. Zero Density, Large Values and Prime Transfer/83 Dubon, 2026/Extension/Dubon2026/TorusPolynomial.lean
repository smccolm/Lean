import Dubon2026.TorusEquidistribution

/-! # Continuous torus realization and the literal polynomial consumer -/

namespace Dubon2026

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- The source Bohr polynomial restricted to the actual product of unit circles. -/
def bohrOnTorus (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) : C(PrimeTorus N, ℂ) where
  toFun z := bohrLift a N σ (fun p => fourier 1 (z p))
  continuous_toFun := by
    unfold bohrLift bohrMonomial
    fun_prop

theorem bohrOnTorus_verticalFlow (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ) :
    bohrOnTorus a N σ (primeTorusFlow N t) =
      dirichletSum a N ((σ : ℂ) + Complex.I * t) := by
  change bohrLift a N σ (fun p => fourier 1 (primeTorusFlow N t p)) = _
  simp_rw [fourier_one_primeTorusFlow]
  exact bohrLift_verticalFlow a N σ t

theorem tendsto_vertical_polynomial_test (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (φ : C(ℂ, ℂ)) :
    Tendsto (fun T : ℝ => (2 * T)⁻¹ •
      ∫ t in -T..T, φ (dirichletSum a N ((σ : ℂ) + Complex.I * t))) atTop
      (𝓝 (∫ z, φ (bohrOnTorus a N σ z) ∂torusHaar N)) := by
  have h := tendsto_torusAverage N (φ.comp (bohrOnTorus a N σ))
  change Tendsto (fun T => symmetricAverage
    (fun t => φ (bohrOnTorus a N σ (primeTorusFlow N t))) T) atTop
      (𝓝 (∫ z, φ (bohrOnTorus a N σ z) ∂torusHaar N)) at h
  simpa only [bohrOnTorus_verticalFlow, symmetricAverage] using h

theorem fourier_nat_eq_pow (n : ℕ) (z : UnitAddCircle) :
    fourier (n : ℤ) z = (fourier 1 z) ^ n := by
  induction n with
  | zero => simp only [Nat.cast_zero, fourier_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, fourier_add, ih, pow_succ]

/-- The integer Fourier frequency vector attached to an actual positive integer. -/
def primeExponent (N n : ℕ) : PrimeCoordinate N → ℤ :=
  fun p => (n.factorization p.val : ℤ)

theorem bohrMonomial_eq_mFourier (N n : ℕ) (z : PrimeTorus N) :
    bohrMonomial N n (fun p => fourier 1 (z p)) = UnitAddTorus.mFourier (primeExponent N n) z := by
  simp only [bohrMonomial, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    primeExponent, fourier_nat_eq_pow]

theorem primeExponent_injectiveOn (N : ℕ) : Set.InjOn (primeExponent N) (Set.Icc 1 N) := by
  intro m hm n hn h
  apply prime_exponent_vector_injective hm.1 hm.2 hn.1 hn.2
  intro p
  have hp : (m.factorization p.val : ℤ) = (n.factorization p.val : ℤ) := congrFun h p
  exact_mod_cast hp

theorem primeExponent_one (N : ℕ) : primeExponent N 1 = 0 := by
  funext p
  simp [primeExponent]

theorem primeExponent_eq_zero_iff {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    primeExponent N n = 0 ↔ n = 1 := by
  constructor
  · intro h
    apply primeExponent_injectiveOn N ⟨hn,hnN⟩ ⟨le_rfl, hn.trans hnN⟩
    rw [h, primeExponent_one]
  · rintro rfl
    exact primeExponent_one N

theorem bohrOnTorus_eq_fourier_sum (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (z : PrimeTorus N) :
    bohrOnTorus a N σ z = ∑ n ∈ Finset.Icc 1 N,
      (a n * (n : ℂ) ^ (-(σ : ℂ))) * UnitAddTorus.mFourier (primeExponent N n) z := by
  simp only [bohrOnTorus, ContinuousMap.coe_mk, bohrLift, bohrMonomial_eq_mFourier]

theorem integral_bohrOnTorus (a : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) (σ : ℝ) :
    (∫ z, bohrOnTorus a N σ z ∂torusHaar N) = a 1 := by
  classical
  simp_rw [bohrOnTorus_eq_fourier_sum]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, integral_mFourier_torusHaar]
    have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
        a n * (n : ℂ) ^ (-(σ : ℂ)) * (if primeExponent N n = 0 then 1 else 0) =
          if n = 1 then a 1 else 0 := by
      simp only [primeExponent_eq_zero_iff (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2]
      split_ifs with h
      · subst n
        simp
      · simp
    rw [Finset.sum_congr rfl hterm]
    simp [hN]
  · intro n _
    exact (integrable_torusHaar N (UnitAddTorus.mFourier (primeExponent N n))).const_mul _

end

end Dubon2026
