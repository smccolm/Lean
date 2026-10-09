import Dubon2026.FiniteAdelicPlaceRemoval
import Dubon2026.RationalPrimePlace
import Dubon2026.FiniteAdelicHeckeTrace

/-! # The genuine Hecke representatives lie in the original level group away from their prime -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The original rational Hecke diagonal and its inverse are genuine local level matrices at every place distinct from their prime. -/
theorem finiteAdelicHeckeDiagonal_local_level (N p : ℕ) [NeZero p] (hp : p.Prime)
    (w : HeightOneSpectrum ℤ) (hw : w ≠ rationalPrimePlace p hp) :
    GeneralLinearGroup.map (finiteAdelePlace w) (finiteAdelicHeckeDiagonal p) ∈ finitePlaceGL2Gamma0 N w := by
  have hint : (p : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ :=
    by simp
  have hinv := finitePlace_inverse_level_integral p w (rationalPrimePlace_prime_not_mem p hp w hw)
  change finitePlaceLevelMatrix N w ((finiteAdelicHeckeDiagonal p).val.map (finiteAdelePlace w)) ∧
    finitePlaceLevelMatrix N w (((finiteAdelicHeckeDiagonal p)⁻¹).val.map (finiteAdelePlace w))
  rw [finiteAdelicHeckeDiagonal_val, finiteAdelicHeckeDiagonal_inv_val]
  constructor
  · constructor
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp_all [Matrix.map_apply]
    · simp [Matrix.map_apply]
  · constructor
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp_all [Matrix.map_apply]
    · simp [Matrix.map_apply]

/-- Each actual full finite-adelic Hecke summand has original local level membership at every place away from its prime. -/
theorem finiteAdelicHeckeRepresentative_local_level (N p : ℕ) [NeZero N] [NeZero p]
    (hp : p.Prime) (hpN : p.Coprime N) (i : Option (ZMod p))
    (w : HeightOneSpectrum ℤ) (hw : w ≠ rationalPrimePlace p hp) :
    GeneralLinearGroup.map (finiteAdelePlace w)
      ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
        (finiteAdelicHeckeDiagonal p)⁻¹) ∈ finitePlaceGL2Gamma0 N w := by
  rw [map_mul, map_inv, map_inv]
  apply (finitePlaceGL2Gamma0 N w).mul_mem
  · apply (finitePlaceGL2Gamma0 N w).inv_mem
    exact (finiteAdeleGL2Gamma0_iff_places N _).mp
      (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).property w
  · exact (finitePlaceGL2Gamma0 N w).inv_mem (finiteAdelicHeckeDiagonal_local_level N p hp w hw)

end
end Dubon2026
