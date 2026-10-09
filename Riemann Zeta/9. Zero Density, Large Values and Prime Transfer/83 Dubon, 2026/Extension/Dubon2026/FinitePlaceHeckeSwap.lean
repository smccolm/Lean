import Dubon2026.GL2DiagonalSwap
import Dubon2026.FinitePlaceSphericalLevel
import Dubon2026.FiniteAdelicHeckeLocalSupport

/-! # The original local Hecke diagonal and its actual integral coordinate swap -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The genuine coordinate swap belongs to every original local integral general-linear group. -/
theorem finitePlace_coordinateSwap_integral (v : HeightOneSpectrum ℤ) :
    (gl2CoordinateSwap : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) ∈
      finitePlaceGL2Gamma0 1 v := by
  constructor <;> constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [gl2CoordinateSwap]
  · simp [gl2CoordinateSwap]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [gl2CoordinateSwap]
  · simp [gl2CoordinateSwap]

/-- At a good prime the original coordinate swap is an actual member of the original local level group. -/
theorem finitePlace_coordinateSwap_good (N p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) :
    (gl2CoordinateSwap : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p hp).adicCompletion ℚ)) ∈
      finitePlaceGL2Gamma0 N (rationalPrimePlace p hp) := by
  rw [finitePlaceGL2Gamma0_good_eq_one N p hp hpN]
  exact finitePlace_coordinateSwap_integral _

/-- The original local Hecke diagonal is literally diagonal with entries one and p. -/
theorem finitePlaceHeckeDiagonal_val (p : ℕ) [NeZero p] (v : HeightOneSpectrum ℤ) :
    (GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p)).val =
      !![1, 0; 0, (p : v.adicCompletion ℚ)] := by
  change (finiteAdelicHeckeDiagonal p).val.map (finiteAdelePlace v) = _
  rw [finiteAdelicHeckeDiagonal_val]
  funext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The original local inverse Hecke diagonal is its integral-swap conjugate times the genuine inverse scalar p. -/
theorem finitePlaceHeckeDiagonal_inverse_swap (p : ℕ) [NeZero p] (v : HeightOneSpectrum ℤ) :
    (GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p))⁻¹ =
      GeneralLinearGroup.scalar (Fin 2)
        (Units.map (algebraMap ℚ (v.adicCompletion ℚ)).toMonoidHom
          (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr (NeZero.ne p))))⁻¹ *
      gl2CoordinateSwap *
        GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p) *
      gl2CoordinateSwap⁻¹ := by
  apply gl2SecondDiagonal_inverse_swap
  change (GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p)).val =
    !![1, 0; 0, algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)]
  rw [map_natCast]
  exact finitePlaceHeckeDiagonal_val p v

end
end Dubon2026
