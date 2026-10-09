import Dubon2026.FinitePlaceUniformizer
import Dubon2026.FinitePlaceHeckeSwap
import Dubon2026.GL2UnitDiagonalPair

/-! # Exact prime-power diagonal normal form using the original local Hecke diagonal -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The genuine local unit obtained by mapping the original nonzero rational prime integer. -/
def finitePlacePrimeUnit (p : ℕ) [NeZero p] (v : HeightOneSpectrum ℤ) : (v.adicCompletion ℚ)ˣ :=
  Units.map (algebraMap ℚ (v.adicCompletion ℚ)).toMonoidHom
    (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr (NeZero.ne p)))

/-- The original mapped prime unit has exactly the original natural-number field value. -/
theorem finitePlacePrimeUnit_val (p : ℕ) [NeZero p] (v : HeightOneSpectrum ℤ) :
    (finitePlacePrimeUnit p v : v.adicCompletion ℚ) = p := by
  change algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ) = p
  exact map_natCast _ _

/-- The genuine local Hecke diagonal is precisely the two-unit diagonal of one and the actual prime unit. -/
theorem finitePlaceHeckeDiagonal_eq_pair (p : ℕ) [NeZero p] (v : HeightOneSpectrum ℤ) :
    GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p) =
      gl2UnitDiagonalPair 1 (finitePlacePrimeUnit p v) := by
  apply Units.ext
  rw [finitePlaceHeckeDiagonal_val]
  simp only [gl2UnitDiagonalPair, Units.val_one, finitePlacePrimeUnit_val]

/-- An original integral nonzero diagonal entry factors into an actual integral-unit diagonal and a power of the genuine original local Hecke diagonal. -/
theorem finitePlace_integral_diagonal_hecke_power (p : ℕ) [NeZero p] (hp : p.Prime)
    (t : ((rationalPrimePlace p hp).adicCompletion ℚ)ˣ)
    (ht : (t : (rationalPrimePlace p hp).adicCompletion ℚ) ∈ (rationalPrimePlace p hp).adicCompletionIntegers ℚ) :
    ∃ u : ((rationalPrimePlace p hp).adicCompletionIntegers ℚ)ˣ, ∃ n : ℕ,
      gl2UnitDiagonalPair 1 t =
        GeneralLinearGroup.map ((rationalPrimePlace p hp).adicCompletionIntegers ℚ).subtype
          (gl2UnitDiagonalPair 1 u) *
        (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp)) (finiteAdelicHeckeDiagonal p)) ^ n := by
  let v := rationalPrimePlace p hp
  let x : v.adicCompletionIntegers ℚ := ⟨t.val, ht⟩
  have hx : x ≠ 0 := by
    intro h
    exact (Units.ne_zero t) (congrArg Subtype.val h)
  obtain ⟨u, n, hu⟩ := rationalPrimePlaceInteger_unit_power p hp x hx
  have he : t = Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom u * (finitePlacePrimeUnit p v) ^ n := by
    apply Units.ext
    change (t : v.adicCompletion ℚ) = (u.val : v.adicCompletion ℚ) *
      (finitePlacePrimeUnit p v : v.adicCompletion ℚ) ^ n
    rw [finitePlacePrimeUnit_val]
    exact congrArg Subtype.val hu
  refine ⟨u, n, ?_⟩
  rw [gl2UnitDiagonalPair_map, finitePlaceHeckeDiagonal_eq_pair, gl2UnitDiagonalPair_pow,
    gl2UnitDiagonalPair_mul, map_one, one_pow, one_mul, ← he]

end
end Dubon2026
