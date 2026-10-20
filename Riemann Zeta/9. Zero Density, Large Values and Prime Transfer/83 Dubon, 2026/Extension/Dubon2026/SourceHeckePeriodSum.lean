/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.SourcePeriodMap
import Dubon2026.HeckePrimeLinear

/-! The original finite prime Hecke sum inside the actual convergent period integral.
This is the analytic half of integral Hecke adjointness, which removes the last
pairing assumption from integral Hecke algebra finiteness on the DUB-17/DUB-18
modular Galois association route. All convergence inputs are derived from cusp decay.
-/

namespace Dubon2026.SourceModularSymbols
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open MvPolynomial MeasureTheory Set OnePoint
open scoped MatrixGroups ModularForm
noncomputable section

variable {R : Type*} [CommRing R] [Algebra R ℂ] {w Q : ℕ} [NeZero Q] {k : ℤ}

/-- Positivity for the rational representatives already defining the original Hecke operators. -/
theorem sourceHeckeTriangularRat_det_pos (a d : ℕ) [NeZero a] [NeZero d] (b : ℕ) :
    0 < (heckeTriangularRat a d b : Matrix (Fin 2) (Fin 2) ℚ).det := by
  change 0 < (!![(a : ℚ), b; 0, d] : Matrix (Fin 2) (Fin 2) ℚ).det
  simpa using mul_pos (Nat.cast_pos.mpr (Nat.pos_of_neZero a) : (0 : ℚ) < a)
    (Nat.cast_pos.mpr (Nat.pos_of_neZero d) : (0 : ℚ) < d)

/-- Each original Hecke summand has an integrable period along every rational geodesic. -/
theorem sourceIntegrable_triangular_period (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)
    (hk : k = w + 2) (P : homogeneousSubmodule (Fin 2) R w)
    (a d : ℕ) [NeZero a] [NeZero d] (b : ℕ) {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) :
    IntegrableOn (sourceResToImagAxis
      (periodIntegrand (⇑f ∣[k] heckeTriangularMatrix a d b) P ∣[(2 : ℤ)] g)) (Ioi 0) := by
  have hA : (heckeTriangularRat a d b : Matrix (Fin 2) (Fin 2) ℚ) =
      (!![(a : ℤ), b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heckeTriangularRat, GeneralLinearGroup.mkOfDetNeZero]
  change IntegrableOn (sourceResToImagAxis
    (periodIntegrand (⇑f ∣[k] GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (heckeTriangularRat a d b)) P ∣[(2 : ℤ)] g)) (Ioi 0)
  rw [← sourceRat_slash, ← periodIntegrand_adjugate_slash hk f P hA
    (sourceHeckeTriangularRat_det_pos a d b), ← SlashAction.slash_mul]
  apply integrableOn_sourceResToImagAxis_periodIntegrand_slash f hk
  rw [Units.val_mul, Matrix.det_mul]
  exact mul_pos (sourceHeckeTriangularRat_det_pos a d b) hg

/-- Finite original upper Hecke sums have integrable period integrands. -/
theorem sourceIntegrable_triangularSum_period
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : k = w + 2)
    (P : homogeneousSubmodule (Fin 2) R w) (a d : ℕ) [NeZero a] [NeZero d]
    {g : GL (Fin 2) ℚ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) :
    IntegrableOn (sourceResToImagAxis
      (periodIntegrand (heckeTriangularSum a d k f) P ∣[(2 : ℤ)] g)) (Ioi 0) := by
  have he : sourceResToImagAxis
      (periodIntegrand (heckeTriangularSum a d k f) P ∣[(2 : ℤ)] g) =
      ∑ b ∈ Finset.range d, sourceResToImagAxis
        (periodIntegrand (⇑f ∣[k] heckeTriangularMatrix a d b) P ∣[(2 : ℤ)] g) := by
    rw [heckeTriangularSum, periodIntegrand_sum_left, SlashAction.sum_slash]
    funext t
    rcases le_or_gt t 0 with ht | ht <;>
      simp [sourceResToImagAxis_of_pos, sourceResToImagAxis_of_nonpos, ht]
  rw [he]
  exact integrable_finsetSum' _ fun b _ => sourceIntegrable_triangular_period f hk P a d b hg

/-- The actual period commutes with the original finite upper Hecke sum. -/
theorem sourceCuspIntegral_triangularSum
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : k = w + 2)
    (P : homogeneousSubmodule (Fin 2) R w) (a d : ℕ) [NeZero a] [NeZero d]
    {g : GL (Fin 2) ℚ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) :
    sourceCuspIntegral (periodIntegrand (heckeTriangularSum a d k f) P)
        (g • ((0 : ℚ) : OnePoint ℚ)) (g • ∞) =
      ∑ b : Fin d, sourceCuspIntegral
        (periodIntegrand (⇑f ∣[k] heckeTriangularMatrix a d b.val) P)
        (g • ((0 : ℚ) : OnePoint ℚ)) (g • ∞) := by
  rw [heckeTriangularSum, periodIntegrand_sum_left,
    sourceCuspIntegral_sum _ hg (fun b _ => sourceIntegrable_triangular_period f hk P a d b hg)]
  exact (Fin.sum_univ_eq_sum_range _ d).symm

/-- The original prime operator has the exact sum of convergent periods, including bad primes. -/
theorem sourceCuspIntegral_prime {p : ℕ} [NeZero p] (hp : Nat.Prime p)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : k = w + 2)
    (P : homogeneousSubmodule (Fin 2) R w)
    {g : GL (Fin 2) ℚ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) :
    sourceCuspIntegral (periodIntegrand (cuspHeckePrime hp f) P)
        (g • ((0 : ℚ) : OnePoint ℚ)) (g • ∞) =
      (∑ b : Fin p, sourceCuspIntegral
        (periodIntegrand (⇑f ∣[k] heckeTriangularMatrix 1 p b.val) P)
        (g • ((0 : ℚ) : OnePoint ℚ)) (g • ∞)) +
      if Nat.Coprime p Q then sourceCuspIntegral
        (periodIntegrand (⇑f ∣[k] heckeTriangularMatrix p 1 0) P)
        (g • ((0 : ℚ) : OnePoint ℚ)) (g • ∞) else 0 := by
  change sourceCuspIntegral (periodIntegrand (classicalHeckeFunction Q k p f) P) _ _ = _
  rw [classicalHeckeFunction_prime Q k hp]
  by_cases h : Nat.Coprime p Q
  · simp only [if_pos h]
    rw [periodIntegrand_add_left, sourceCuspIntegral_add hg
      (sourceIntegrable_triangularSum_period f hk P 1 p hg)
      (sourceIntegrable_triangular_period f hk P p 1 0 hg),
      sourceCuspIntegral_triangularSum f hk P 1 p hg]
  · simp only [if_neg h, add_zero]
    exact sourceCuspIntegral_triangularSum f hk P 1 p hg

end
end Dubon2026.SourceModularSymbols
