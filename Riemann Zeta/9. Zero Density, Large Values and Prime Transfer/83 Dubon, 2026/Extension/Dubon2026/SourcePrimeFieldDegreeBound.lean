import Dubon2026.SourcePrimeMonicDegree

/-! DUB-17/18 -> numerical modular genus -> exact original j-map degree.
The actual integral conjugate product gives the required upper bound p+1
for the prime j-extension over every original characteristic-zero constant
field. SourcePrimeExactFieldDegree proves the matching prime lower bound,
and SourceOriginalPrimeDegree gives the actual full-field prime degree.
Composite-level generation and degree remain required.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField

theorem prime_j_extension_finrank_le (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ L] :
    let B := IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))
    Module.finrank B (IntermediateField.adjoin B
      ({coeffEmb L (qExpand ℚ p jq)} : Set (LaurentSeries L))) ≤ p + 1 := by
  let B := IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))
  let j : B := ⟨coeffEmb L jq, IntermediateField.mem_adjoin_simple_self L _⟩
  let ψ : Polynomial ℤ →+* B := Polynomial.eval₂RingHom (Int.castRingHom _) j
  obtain ⟨P, hPm, hdeg, hP0⟩ := exists_prime_monic_relation_degree p
  have hcomp : (algebraMap B (LaurentSeries L)).comp ψ = (coeffEmb L).comp evalAtJ := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, evalAtJ_X]
    change algebraMap B (LaurentSeries L) (Polynomial.eval₂ (Int.castRingHom _) j X) = _
    rw [Polynomial.eval₂_X]
    rfl
  have hroot : Polynomial.aeval (coeffEmb L (qExpand ℚ p jq)) (P.map ψ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂,
      hP0, map_zero]
  have hi : IsIntegral B (coeffEmb L (qExpand ℚ p jq)) := ⟨P.map ψ, hPm.map ψ, hroot⟩
  change Module.finrank B (IntermediateField.adjoin B
    ({coeffEmb L (qExpand ℚ p jq)} : Set (LaurentSeries L))) ≤ p + 1
  rw [IntermediateField.adjoin.finrank hi]
  calc
    _ ≤ (P.map ψ).natDegree :=
      Polynomial.natDegree_le_of_dvd (minpoly.dvd B _ hroot) (hPm.map ψ).ne_zero
    _ = p + 1 := (hPm.natDegree_map ψ).trans hdeg

end
end Dubon2026.SourceFunctionField
