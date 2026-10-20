import Dubon2026.RationalPrimeOrderEndomorphism
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Prime torsion exclusion for the original number-field matrices

Restriction of scalars retains the given matrix as an endomorphism of
its original vector space over the rationals. For DUB-17's small-level
condition, the native cyclotomic rank bound excludes residue-primary
finite arithmetic stabilizers when the chosen prime is sufficiently large.
-/

namespace Dubon2026

noncomputable section

variable (K : Type*) [Field K] [NumberField K]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The original number-field matrix acts on the same vector space after restricting scalars. -/
def numberFieldMatrixRationalEndomorphism : Matrix ι ι K →* Module.End ℚ (ι → K) :=
  ({ toFun := LinearMap.restrictScalars ℚ
     map_one' := rfl
     map_mul' := fun _ _ => rfl } : Module.End K (ι → K) →* Module.End ℚ (ι → K)).comp
       Matrix.toLinAlgEquiv'.toMonoidHom

/-- Restricting scalars preserves the original matrix faithfully. -/
theorem numberFieldMatrixRationalEndomorphism_injective :
    Function.Injective (numberFieldMatrixRationalEndomorphism K ι) := by
  intro M N h
  exact Matrix.toLinAlgEquiv'.injective (LinearMap.restrictScalars_injective ℚ h)

/-- A sufficiently large residue prime cannot occur as nontrivial original matrix torsion. -/
theorem numberFieldMatrix_prime_order_eq_one (p : ℕ) (hp : p.Prime)
    (hlarge : Fintype.card ι * Module.finrank ℚ K < p - 1)
    (M : Matrix ι ι K) (hM : M ^ p = 1) : M = 1 := by
  let e := numberFieldMatrixRationalEndomorphism K ι
  have hrank : Module.finrank ℚ (ι → K) < p - 1 := by
    simpa only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] using hlarge
  apply numberFieldMatrixRationalEndomorphism_injective K ι
  rw [map_one]
  apply rationalPrimeOrderEndomorphism_eq_one p hp hrank
  rw [← map_pow, hM, map_one]

/-- The same rank bound kills every original matrix of residue-prime-power order. -/
theorem numberFieldMatrix_primary_order_eq_one (p : ℕ) (hp : p.Prime)
    (hlarge : Fintype.card ι * Module.finrank ℚ K < p - 1)
    (M : Matrix ι ι K) (k : ℕ) (hM : M ^ (p ^ k) = 1) : M = 1 := by
  induction k with
  | zero => simpa only [pow_zero, pow_one] using hM
  | succ k ih =>
    apply ih
    apply numberFieldMatrix_prime_order_eq_one K ι p hp hlarge
    simpa only [← pow_mul, ← pow_succ] using hM

end
end Dubon2026
