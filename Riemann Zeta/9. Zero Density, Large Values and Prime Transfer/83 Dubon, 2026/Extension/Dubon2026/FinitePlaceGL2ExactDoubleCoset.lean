import Dubon2026.FinitePlaceGL2UnitReduction
import Dubon2026.FinitePlaceIntegralDeterminant
import Dubon2026.FinitePlaceHeckeDiagonalPowers

/-! # Exact local Hecke power from a genuine unit entry and original determinant -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The original determinant exponent gives the exact Hecke double coset for an integral matrix with a genuine unit first pivot. -/
theorem finitePlaceGL2_unit_pivot_hecke_power (p : ℕ) [NeZero p] (hp : p.Prime)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p hp).adicCompletion ℚ))
    (hint : ∀ i j, g.val i j ∈ (rationalPrimePlace p hp).adicCompletionIntegers ℚ)
    (a b : ((rationalPrimePlace p hp).adicCompletionIntegers ℚ)ˣ)
    (ha : g.val 0 0 = (a.val : (rationalPrimePlace p hp).adicCompletion ℚ))
    (m : ℕ)
    (hdet : GeneralLinearGroup.det g =
      Units.map ((rationalPrimePlace p hp).adicCompletionIntegers ℚ).subtype.toMonoidHom b *
        (finitePlacePrimeUnit p (rationalPrimePlace p hp)) ^ m) :
    ∃ l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p hp),
      g = l.val * (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp))
        (finiteAdelicHeckeDiagonal p)) ^ m * r.val := by
  obtain ⟨l, r, hg⟩ := finitePlaceGL2_unit_pivot_diagonal (rationalPrimePlace p hp) g hint a ha
  let B := GeneralLinearGroup.map ((rationalPrimePlace p hp).adicCompletionIntegers ℚ).subtype
    (gl2UnitDiagonalPair 1 b)
  have hB : B ∈ finitePlaceGL2Gamma0 1 (rationalPrimePlace p hp) := finitePlaceGL2_integral_mem _ _
  have he : gl2UnitDiagonalPair 1 (GeneralLinearGroup.det g) =
      B * (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp))
        (finiteAdelicHeckeDiagonal p)) ^ m := by
    dsimp only [B]
    rw [hdet, gl2UnitDiagonalPair_map, finitePlaceHeckeDiagonal_eq_pair,
      gl2UnitDiagonalPair_pow, gl2UnitDiagonalPair_mul, map_one, one_pow, one_mul]
  refine ⟨⟨l.val * B, (finitePlaceGL2Gamma0 1 _).mul_mem l.property hB⟩, r, ?_⟩
  rw [hg, he]
  simp only [mul_assoc]

/-- A genuine integral unit in any original matrix position and its original determinant determine the exact actual Hecke double coset. -/
theorem finitePlaceGL2_unit_entry_hecke_power (p : ℕ) [NeZero p] (hp : p.Prime)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p hp).adicCompletion ℚ))
    (hint : ∀ i j, g.val i j ∈ (rationalPrimePlace p hp).adicCompletionIntegers ℚ)
    (i j : Fin 2) (a b : ((rationalPrimePlace p hp).adicCompletionIntegers ℚ)ˣ)
    (ha : g.val i j = (a.val : (rationalPrimePlace p hp).adicCompletion ℚ))
    (m : ℕ)
    (hdet : GeneralLinearGroup.det g =
      Units.map ((rationalPrimePlace p hp).adicCompletionIntegers ℚ).subtype.toMonoidHom b *
        (finitePlacePrimeUnit p (rationalPrimePlace p hp)) ^ m) :
    ∃ l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p hp),
      g = l.val * (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp))
        (finiteAdelicHeckeDiagonal p)) ^ m * r.val := by
  let v := rationalPrimePlace p hp
  let L : finitePlaceGL2Gamma0 1 v := ⟨gl2IndexSwap i, finitePlace_indexSwap_integral v i⟩
  let R : finitePlaceGL2Gamma0 1 v := ⟨gl2IndexSwap j, finitePlace_indexSwap_integral v j⟩
  let h := L.val * g * R.val
  have hh : ∀ r s, h.val r s ∈ v.adicCompletionIntegers ℚ := by
    intro r s
    obtain ⟨c, d, he⟩ := gl2IndexSwap_entry g i j r s
    change (gl2IndexSwap i * g * gl2IndexSwap j).val r s ∈ _
    rw [he]
    exact hint c d
  have hpivot : h.val 0 0 = (a.val : v.adicCompletion ℚ) := (gl2IndexSwap_pivot g i j).trans ha
  let c := finitePlaceIntegralDetUnit v L * b * finitePlaceIntegralDetUnit v R
  have hd : GeneralLinearGroup.det h = Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom c *
      (finitePlacePrimeUnit p v) ^ m := by
    simp only [h, c, map_mul, hdet, finitePlaceIntegralDetUnit_map]
    ac_rfl
  obtain ⟨l, r, he⟩ := finitePlaceGL2_unit_pivot_hecke_power p hp h hh a c hpivot m hd
  refine ⟨⟨L.val⁻¹ * l.val, (finitePlaceGL2Gamma0 1 v).mul_mem
    ((finitePlaceGL2Gamma0 1 v).inv_mem L.property) l.property⟩,
    ⟨r.val * R.val⁻¹, (finitePlaceGL2Gamma0 1 v).mul_mem r.property
      ((finitePlaceGL2Gamma0 1 v).inv_mem R.property)⟩, ?_⟩
  have he' := congrArg (fun A => L.val⁻¹ * A * R.val⁻¹) he
  simpa only [h, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using he'

end
end Dubon2026
