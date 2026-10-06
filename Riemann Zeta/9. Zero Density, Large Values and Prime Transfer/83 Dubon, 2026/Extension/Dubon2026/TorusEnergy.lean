import Dubon2026.TorusPolynomial

/-! # Exact Haar quadratic energy of the finite Dirichlet polynomial -/

namespace Dubon2026

open MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The same normalized coordinate measure as in Mathlib's Fourier orthonormality theorem. -/
local instance torusEnergyCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusEnergyCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_norm_sq_fourier_sum {ι : Type*} [Fintype ι] (N : ℕ)
    (k : ι → PrimeCoordinate N → ℤ) (hk : Function.Injective k) (c : ι → ℂ) :
    (∫ z, ‖∑ i, c i * UnitAddTorus.mFourier (k i) z‖ ^ 2 ∂torusHaar N) =
      ∑ i, ‖c i‖ ^ 2 := by
  classical
  let F : C(PrimeTorus N, ℂ) := ∑ i, c i • UnitAddTorus.mFourier (k i)
  have hF : ContinuousMap.toLp 2 (volume : Measure (PrimeTorus N)) ℂ F =
      ∑ i, c i • UnitAddTorus.mFourierLp 2 (k i) := by
    simp only [F, map_sum, map_smul]
  have ho := (UnitAddTorus.orthonormal_mFourier (d := PrimeCoordinate N)).comp k hk
  have hi := ho.inner_sum c c Finset.univ
  change inner ℂ (∑ i, c i • UnitAddTorus.mFourierLp 2 (k i))
    (∑ i, c i • UnitAddTorus.mFourierLp 2 (k i)) = ∑ i, conj (c i) * c i at hi
  rw [← hF, ContinuousMap.inner_toLp (volume : Measure (PrimeTorus N)) F F] at hi
  simp only [Complex.mul_conj', Complex.conj_mul', ← Complex.ofReal_pow] at hi
  rw [integral_complex_ofReal] at hi
  have hr : (∫ z, ‖F z‖ ^ 2 ∂torusHaar N) = ∑ i, ‖c i‖ ^ 2 := by exact_mod_cast hi
  simpa only [F, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul] using hr

theorem norm_nat_cpow_neg_real (n : ℕ) (σ : ℝ) :
    ‖(n : ℂ) ^ (-(σ : ℂ))‖ = (n : ℝ) ^ (-σ) := by
  have h := Complex.ofReal_cpow (x := (n : ℝ)) (Nat.cast_nonneg n) (y := -σ)
  rw [Complex.ofReal_neg, Complex.ofReal_natCast] at h
  rw [← h, Complex.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]

theorem norm_coefficient_sq (a : ℕ → ℂ) (n : ℕ) (σ : ℝ) :
    ‖a n * (n : ℂ) ^ (-(σ : ℂ))‖ ^ 2 = ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  rw [norm_mul, mul_pow, norm_nat_cpow_neg_real,
    ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  congr 2
  ring

/-- The literal quadratic coefficient energy from hypothesis H1. -/
def coefficientEnergy (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)

theorem integral_norm_sq_bohrOnTorus (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    (∫ z, ‖bohrOnTorus a N σ z‖ ^ 2 ∂torusHaar N) = coefficientEnergy a N σ := by
  have hinj : Function.Injective (fun n : ↥(Finset.Icc 1 N) => primeExponent N n.val) := by
    intro m n h
    apply Subtype.ext
    exact primeExponent_injectiveOn N (Finset.mem_Icc.mp m.property)
      (Finset.mem_Icc.mp n.property) h
  have he := integral_norm_sq_fourier_sum N
    (fun n : ↥(Finset.Icc 1 N) => primeExponent N n.val) hinj
    (fun n => a n.val * (n.val : ℂ) ^ (-(σ : ℂ)))
  have hs (z : PrimeTorus N) := Finset.sum_coe_sort (Finset.Icc 1 N)
    (fun n : ℕ => a n * (n : ℂ) ^ (-(σ : ℂ)) * UnitAddTorus.mFourier (primeExponent N n) z)
  have hc := Finset.sum_coe_sort (Finset.Icc 1 N)
    (fun n : ℕ => ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ))
  simp only [norm_coefficient_sq, hs, hc] at he
  simpa only [bohrOnTorus_eq_fourier_sum, coefficientEnergy] using he

theorem coefficientEnergy_nonneg (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    0 ≤ coefficientEnergy a N σ := by
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem one_le_coefficientEnergy {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 = 1) (σ : ℝ) :
    1 ≤ coefficientEnergy a N σ := by
  have h := Finset.single_le_sum (fun n (_ : n ∈ Finset.Icc 1 N) =>
    mul_nonneg (sq_nonneg ‖a n‖) (Real.rpow_nonneg (Nat.cast_nonneg n) (-2 * σ)))
    (show 1 ∈ Finset.Icc 1 N by simp [hN])
  simpa only [ha, norm_one, one_pow, Nat.cast_one, Real.one_rpow, mul_one, coefficientEnergy] using h

end

end Dubon2026
