import Dubon2026.SourceGammaOneArithmeticDivisors
import Dubon2026.SourceCurveCoordinateValues
import Dubon2026.SourceCurveSeparatingFunctionSupport
import Dubon2026.SourceGammaOneConstantFieldPlaces
import Mathlib.FieldTheory.Minpoly.Basic

/-! DUB-17/18 -> original all-weight arithmetic association -> continuous
finite Tate-dual Galois action -> finite Gamma1 place orbits. Reuse the
actual finite j coordinate, closed residue fields and finite function
support. Each orbit lies over finitely many conjugate j values or over
the poles of j. This is the original finite-orbit proof on the exact
Gamma1 field; no good reduction or coordinate-degree equality is used. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ

theorem gammaOne_place_galois_orbit_finite (N : ℕ) [NeZero N]
    (v : Place Qbar (functionFieldOver (Gamma1 N) Qbar)) :
    (Set.range fun σ : Qbar ≃ₐ[ℚ] Qbar => arithmeticPlace (Gamma1 N) σ v).Finite := by
  let Γ := Gamma1 N
  let F := functionFieldOver Γ Qbar
  have hT : ModularGroup.T ∈ Γ := by simp [Γ, Gamma1_mem, ModularGroup.T]
  letI := finiteDimensional_jCoordinateOver hT Qbar
  have hf (f : F) : {w : Place Qbar F | w.ord f ≠ 0}.Finite :=
    finite_function_support_of_separating_coordinate (jCoordinateOver Γ Qbar)
      (transcendental_jCoordinateOver Γ Qbar) f
  rcases lt_or_ge (v.ord (jCoordinateOver Γ Qbar)) 0 with hp | hreg
  · refine (hf (jCoordinateOver Γ Qbar)).subset ?_
    rintro _ ⟨σ, rfl⟩
    change (arithmeticPlace Γ σ v).ord (jCoordinateOver Γ Qbar) ≠ 0
    rw [arithmeticPlace_ord, arithmeticRingAut_j]
    exact hp.ne
  · obtain ⟨c, hc, _⟩ := v.exists_unique_coordinate_value
      (functionFieldOver_residue_bijective Γ hT v).surjective
      (transcendental_jCoordinateOver Γ Qbar) (v.mem_of_ord_nonneg hreg)
    letI : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
    letI : Algebra.IsIntegral ℚ Qbar := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
    have hpoly : minpoly ℚ c ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R := ℚ) c)
    have hs := (Polynomial.rootSet_finite (minpoly ℚ c) Qbar).biUnion
      (fun a _ => hf (jCoordinateOver Γ Qbar - algebraMap Qbar F a))
    refine hs.subset ?_
    rintro _ ⟨σ, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨σ c, (Polynomial.mem_rootSet_of_ne hpoly).mpr (minpoly.aeval_algHom ℚ σ.toAlgHom c), ?_⟩
    have he : arithmeticRingAut Γ σ
        (jCoordinateOver Γ Qbar - algebraMap Qbar F c) =
        jCoordinateOver Γ Qbar - algebraMap Qbar F (σ c) := by
      rw [map_sub, arithmeticRingAut_j, arithmeticRingAut_constants]
    rw [← he, arithmeticPlace_ord_action]
    exact hc.ne'

end
end Dubon2026.SourceFunctionField.GammaOne
