import Dubon2026.FinitePlaceHeckeRepresentativeEntries
import Dubon2026.FinitePlaceGL2IntegralReduction

/-! # Literal original radial Hecke matrices after the genuine trivial scalar normalization -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The actual original Hecke summand translated by a genuine radial diagonal power and its original scalar p. -/
def finitePlaceHeckeRadialMatrix (N p : ℕ) [NeZero N] [NeZero p] (hpN : p.Coprime N)
    (v : HeightOneSpectrum ℤ) (n : ℕ) (i : Option (ZMod p)) : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) :=
  GeneralLinearGroup.scalar (Fin 2) (finitePlacePrimeUnit p v) *
    ((GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p)) ^ n *
      ((finitePlaceHeckeGamma N p hpN v i)⁻¹ *
        (GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p))⁻¹))

/-- Each original translation summand has the exact integral radial matrix with entries p, minus its original residue representative, zero and p^n. -/
theorem finitePlaceHeckeRadialMatrix_some_val (N p : ℕ) [NeZero N] [NeZero p]
    (hpN : p.Coprime N) (v : HeightOneSpectrum ℤ) (n : ℕ) (a : ZMod p) :
    (finitePlaceHeckeRadialMatrix N p hpN v n (some a)).val =
      !![(p : v.adicCompletion ℚ), -(a.val : v.adicCompletion ℚ); 0, (p : v.adicCompletion ℚ) ^ n] := by
  have hp : (p : v.adicCompletion ℚ) ≠ 0 := by
    rw [← finitePlacePrimeUnit_val p v]
    exact Units.ne_zero _
  funext i j
  rw [finitePlaceHeckeRadialMatrix, gl2Scalar_mul_entry, finitePlacePrimeUnit_val,
    Units.val_mul, Units.val_mul, finitePlaceHeckeDiagonal_pow_val,
    finitePlaceHeckeGamma_some_inv_val, finitePlaceHeckeDiagonal_inverse_val]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
      mul_comm, mul_left_comm, hp]
  rw [mul_left_comm, mul_inv_cancel₀ hp, mul_one]

/-- The original Bezout summand has precisely the original two Bezout coefficients and the next genuine prime power. -/
theorem finitePlaceHeckeRadialMatrix_none_val (N p : ℕ) [NeZero N] [NeZero p]
    (hpN : p.Coprime N) (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (finitePlaceHeckeRadialMatrix N p hpN v n none).val =
      !![(p : v.adicCompletion ℚ) * (Int.gcdA p N : v.adicCompletion ℚ),
          (Int.gcdB p N : v.adicCompletion ℚ);
        -(N : v.adicCompletion ℚ) * (p : v.adicCompletion ℚ) ^ (n + 1),
          (p : v.adicCompletion ℚ) ^ (n + 1)] := by
  have hp : (p : v.adicCompletion ℚ) ≠ 0 := by
    rw [← finitePlacePrimeUnit_val p v]
    exact Units.ne_zero _
  funext i j
  rw [finitePlaceHeckeRadialMatrix, gl2Scalar_mul_entry, finitePlacePrimeUnit_val,
    Units.val_mul, Units.val_mul, finitePlaceHeckeDiagonal_pow_val,
    finitePlaceHeckeGamma_none_inv_val, finitePlaceHeckeDiagonal_inverse_val]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ,
      mul_comm, mul_left_comm, hp]

end
end Dubon2026
