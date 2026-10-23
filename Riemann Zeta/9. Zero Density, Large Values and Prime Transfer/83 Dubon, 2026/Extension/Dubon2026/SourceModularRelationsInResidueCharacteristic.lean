import Dubon2026.SourceModularFunctionFieldCoefficients
import Dubon2026.SourceAllDivisorMonicRelations

/-! DUB-17/18 -> original Frobenius/inertia -> reduction of the actual
curve -> finite residue-characteristic function field. Reuse the proved
integral monic relation for every original divisor j expansion. Equality
descends from rational coefficients to the actual integral series and
then specializes into any coefficient ring. No new modular-polynomial
existence theorem or characteristic-zero algebra on the residue is used. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial
variable (N : ℕ) [NeZero N] (P : Polynomial (Polynomial ℤ))

private theorem map_integral_j_relation {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) :
    coeffMap f ((relationAtSeed P (jqModC R)).eval (qExpand R N (jqModC R))) =
      (relationAtSeed P (jqModC S)).eval (qExpand S N (jqModC S)) := by
  have hj : coeffMap f (jqModC R) = jqModC S := map_jqModC f
  have hq : coeffMap f (qExpand R N (jqModC R)) = qExpand S N (jqModC S) := by
    rw [coeffMap_qExpand, hj]
  rw [← hq, ← hj, ← relationAtSeed_map, Polynomial.eval_map_apply]

theorem original_monic_relation_specializes (K : Type*) [CommRing K]
    (hP : P.eval₂ evalAtJ (qExpand ℚ N jq) = 0) :
    (relationAtSeed P (jqModC K)).eval (qExpand K N (jqModC K)) = 0 := by
  have hQ : coeffMap (Int.castRingHom ℚ)
      ((relationAtSeed P (jqModC ℤ)).eval (qExpand ℤ N (jqModC ℤ))) = 0 := by
    rw [map_integral_j_relation]
    exact relationAtSeed_jq_eval P hP
  have hZ : (relationAtSeed P (jqModC ℤ)).eval (qExpand ℤ N (jqModC ℤ)) = 0 := by
    ext n
    have h := congrArg (fun x : LaurentSeries ℚ => x.coeff n) hQ
    simpa using h
  rw [← map_integral_j_relation N P (Int.castRingHom K), hZ, map_zero]

theorem exists_monic_relation_coeff (K : Type*) [CommRing K] :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧
      (relationAtSeed P (jqModC K)).eval (qExpand K N (jqModC K)) = 0 := by
  obtain ⟨P, hPm, hP⟩ := exists_monic_relation N
  exact ⟨P, hPm, original_monic_relation_specializes N P K hP⟩

end
end Dubon2026.SourceFunctionField
