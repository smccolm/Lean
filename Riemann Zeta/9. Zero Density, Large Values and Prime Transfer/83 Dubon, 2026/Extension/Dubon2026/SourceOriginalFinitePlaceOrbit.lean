import Dubon2026.SourceOriginalArithmeticPlaces
import Dubon2026.SourceOriginalJCoordinatePlaces
import Mathlib.FieldTheory.Minpoly.Basic

/-! DUB-17/18 -> modular Galois association -> open stabilizers of
original divisor classes -> finite arithmetic orbits of original places.
Use the existing original j-place dichotomy and finite normalized-order
supports. A finite j value has finitely many algebraic conjugates, and the
actual arithmetic action sends its fiber to the corresponding conjugate
fiber. This avoids a separate constant-field restriction/fiber theory.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ

theorem original_place_galois_orbit_finite (N : ℕ) [NeZero N]
    (v : Place Qbar (modularFunctionFieldOver N Qbar)) :
    (Set.range fun σ : Qbar ≃ₐ[ℚ] Qbar => originalArithmeticPlace N σ v).Finite := by
  rcases original_j_place_dichotomy N Qbar v with hp | ⟨c, hc, _⟩
  · refine (finite_original_divisor_support N Qbar (jOver N Qbar)).subset ?_
    rintro _ ⟨σ, rfl⟩
    change (originalArithmeticPlace N σ v).ord (jOver N Qbar) ≠ 0
    rw [originalArithmeticPlace_ord, originalArithmeticRingAut_j]
    exact hp.ne
  · letI : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
    letI : Algebra.IsIntegral ℚ Qbar := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
    have hpoly : minpoly ℚ c ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R := ℚ) c)
    have hs := (Polynomial.rootSet_finite (minpoly ℚ c) Qbar).biUnion
      (fun a _ => finite_original_places_positive N Qbar
        (jOver N Qbar - algebraMap Qbar (modularFunctionFieldOver N Qbar) a))
    refine hs.subset ?_
    rintro _ ⟨σ, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨σ c, (Polynomial.mem_rootSet_of_ne hpoly).mpr (minpoly.aeval_algHom ℚ σ.toAlgHom c), ?_⟩
    have he : originalArithmeticRingAut N σ
        (jOver N Qbar - algebraMap Qbar (modularFunctionFieldOver N Qbar) c) =
        jOver N Qbar - algebraMap Qbar (modularFunctionFieldOver N Qbar) (σ c) := by
      rw [map_sub, originalArithmeticRingAut_j, originalArithmeticRingAut_constants]
    rw [← he, originalArithmeticPlace_ord_action]
    exact hc

end
end Dubon2026.SourceFunctionField
