import Dubon2026.FinitePlaceHeckeDiagonalPowers
import Dubon2026.IntegralGamma0FiniteResidue
import Dubon2026.HeckeUpperCosets

/-! # Literal local matrix entries of the original integral Hecke representatives -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- Actual local evaluation of the genuine original integral Gamma0 embedding is exactly its integer-entry local matrix. -/
theorem finitePlace_integralGamma0 (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ) (γ : Gamma0 N) :
    GeneralLinearGroup.map (finiteAdelePlace v) (integralGamma0FiniteGL2Hom N γ).val =
      GeneralLinearGroup.map (Int.castRingHom (v.adicCompletion ℚ)) (toGL γ.val) := by
  apply Units.ext
  funext i j
  change finiteAdelePlace v (γ.val i j : FiniteAdeleRing ℤ ℚ) = (γ.val i j : v.adicCompletion ℚ)
  exact map_intCast _ _

/-- The genuine local integral representative underlying each original intrinsic Hecke summand. -/
def finitePlaceHeckeGamma (N p : ℕ) [NeZero N] (hpN : p.Coprime N)
    (v : HeightOneSpectrum ℤ) (i : Option (ZMod p)) : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) :=
  GeneralLinearGroup.map (finiteAdelePlace v)
    (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val

/-- The inverse original translation representative has exactly its original integer local entries. -/
theorem finitePlaceHeckeGamma_some_inv_val (N p : ℕ) [NeZero N]
    (hpN : p.Coprime N) (v : HeightOneSpectrum ℤ) (a : ZMod p) :
    ((finitePlaceHeckeGamma N p hpN v (some a))⁻¹).val =
      !![1, -(a.val : v.adicCompletion ℚ); 0, 1] := by
  rw [finitePlaceHeckeGamma, finitePlace_integralGamma0, ← map_inv, ← map_inv]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.map, toGL, heckeUpperRepresentative, heckeUpperTranslation,
      coe_inv, Matrix.adjugate_fin_two]

/-- The inverse original Bezout representative retains both genuine Bezout coefficients in its actual local entries. -/
theorem finitePlaceHeckeGamma_none_inv_val (N p : ℕ) [NeZero N]
    (hpN : p.Coprime N) (v : HeightOneSpectrum ℤ) :
    ((finitePlaceHeckeGamma N p hpN v none)⁻¹).val =
      !![(Int.gcdA p N : v.adicCompletion ℚ), (Int.gcdB p N : v.adicCompletion ℚ); -(N : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] := by
  rw [finitePlaceHeckeGamma, finitePlace_integralGamma0, ← map_inv, ← map_inv]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.map, toGL, heckeUpperRepresentative, heckeBezoutRepresentative,
      coe_inv, Matrix.adjugate_fin_two]

/-- The genuine local Hecke diagonal powers have precisely the original prime powers in their actual matrix entries. -/
theorem finitePlaceHeckeDiagonal_pow_val (p : ℕ) [NeZero p] (v : HeightOneSpectrum ℤ) (n : ℕ) :
    ((GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p)) ^ n).val =
      !![1, 0; 0, (p : v.adicCompletion ℚ) ^ n] := by
  rw [finitePlaceHeckeDiagonal_eq_pair, gl2UnitDiagonalPair_pow]
  simp only [gl2UnitDiagonalPair, one_pow, Units.val_one, Units.val_pow_eq_pow_val,
    finitePlacePrimeUnit_val]

/-- The actual inverse local Hecke diagonal is exactly the original prime-unit inverse diagonal. -/
theorem finitePlaceHeckeDiagonal_inverse_val (p : ℕ) [NeZero p] (v : HeightOneSpectrum ℤ) :
    ((GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p))⁻¹).val =
      !![1, 0; 0, (p : v.adicCompletion ℚ)⁻¹] := by
  rw [finitePlaceHeckeDiagonal_eq_pair]
  have he : (finitePlacePrimeUnit p v).inv = (p : v.adicCompletion ℚ)⁻¹ := by
    change (((finitePlacePrimeUnit p v)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = _
    rw [Units.val_inv_eq_inv_val, finitePlacePrimeUnit_val]
  change !![(1 : v.adicCompletion ℚ), 0; 0, (finitePlacePrimeUnit p v).inv] = _
  rw [he]


end
end Dubon2026
