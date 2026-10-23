import Dubon2026.SourceModularRelationsInResidueCharacteristic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree. Before the prime nonmembership argument, denominators
must be removed. Existing integral monic relations prove integrality of
the actual substituted j series over the polynomial j algebra in every
characteristic. No exact degree or irreducibility is assumed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial

theorem coefficient_j_integral_polynomial_algebra (N : ℕ) [NeZero N]
    (K : Type*) [Field K] :
    IsIntegral (Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (qExpand K N (jqModC K)) := by
  let B := Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K))
  let j : B := ⟨jqModC K, Algebra.self_mem_adjoin_singleton K _⟩
  let ψ : Polynomial ℤ →+* B := Polynomial.eval₂RingHom (Int.castRingHom _) j
  obtain ⟨P, hPm, hP0⟩ := exists_monic_relation_coeff N K
  have hcomp : (algebraMap B (LaurentSeries K)).comp ψ =
      Polynomial.eval₂RingHom (Int.castRingHom _) (jqModC K) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    change algebraMap B (LaurentSeries K) (Polynomial.eval₂ (Int.castRingHom _) j X) =
      Polynomial.eval₂ (Int.castRingHom _) (jqModC K) X
    rw [Polynomial.eval₂_X, Polynomial.eval₂_X]
    rfl
  refine ⟨P.map ψ, hPm.map ψ, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  simpa only [relationAtSeed, Polynomial.eval_map] using hP0

end
end Dubon2026.SourceFunctionField
