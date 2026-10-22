import Dubon2026.SourceOriginalHeckeBetaPlaces
import Dubon2026.SourceOriginalFinitePlaceExhaustion
import Dubon2026.SourcePrimeAdjacentRelations

/-! DUB-17/18 -> original Picard-period Hecke comparison -> analytic
divisor formula. The existing reverse monic relation proves that every
place above an analytic beta-image is analytic. This avoids introducing
polynomial symmetry or an independent cusp classification assumption.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve Polynomial
variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

omit [NeZero N] in
theorem originalHeckeBeta_reverse_relation
    (P : Polynomial (Polynomial ℤ))
    (hP : P.eval₂ ((qExpand ℚ ℓ).comp evalAtJ) jq = 0) :
    (relationAtSeed P (originalHeckeBeta ℂ N ℓ (jOver N ℂ))).eval
      (jOver (N * ℓ) ℂ) = 0 := by
  let v := (modularFunctionFieldOver (N * ℓ) ℂ).val.toRingHom
  apply v.injective
  rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, relationAtSeed_map]
  change (relationAtSeed P
    (originalHeckeBeta ℂ N ℓ (jOver N ℂ) : LaurentSeries ℂ)).eval (coeffEmb ℂ jq) = 0
  rw [originalHeckeBeta_jOver_coe]
  have h : (relationAtSeed P (qExpand ℚ ℓ jq)).eval jq = 0 := by
    simpa only [one_mul, qExpand_one_apply] using
      relationAtSeed_reverse_substitution_eval P hP 1
  rw [← relationAtSeed_map, Polynomial.eval_map, Polynomial.eval₂_hom, h, map_zero]

theorem originalHeckeBeta_j_mem_of_restrict_analytic
    (W : Place ℂ (modularFunctionFieldOver (N * ℓ) ℂ)) (τ : ℍ)
    (hW : Place.restrictAlong (originalHeckeBeta ℂ N ℓ)
      (originalHeckeBeta_finite ℂ N ℓ) W = originalAnalyticPlace N τ) :
    jOver (N * ℓ) ℂ ∈ W.toValuationSubring := by
  obtain ⟨P, hPm, -, -, hP⟩ := exists_prime_bidirectional_relation ℓ
  have hβj : originalHeckeBeta ℂ N ℓ (jOver N ℂ) ∈ W.toValuationSubring := by
    rw [← Place.mem_restrictAlong_iff _ (originalHeckeBeta_finite ℂ N ℓ), hW]
    exact originalAnalyticPlace_j_mem N τ
  apply W.mem_of_eval_monic_eq_zero (hPm.map _)
    (fun i => ?_) (originalHeckeBeta_reverse_relation N ℓ P hP)
  rw [Polynomial.coeff_map]
  change Polynomial.eval₂ (Int.castRingHom _) _ (P.coeff i) ∈ W.toValuationSubring
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum]
  exact Subring.sum_mem _ (fun j _ =>
    mul_mem (intCast_mem _ _) (pow_mem hβj j))

theorem exists_original_analytic_place_of_restrict_heckeBeta
    (W : Place ℂ (modularFunctionFieldOver (N * ℓ) ℂ)) (τ : ℍ)
    (hW : Place.restrictAlong (originalHeckeBeta ℂ N ℓ)
      (originalHeckeBeta_finite ℂ N ℓ) W = originalAnalyticPlace N τ) :
    ∃ w : ℍ, originalAnalyticPlace (N * ℓ) w = W :=
  exists_original_analytic_place_eq (N * ℓ) W
    (originalHeckeBeta_j_mem_of_restrict_analytic N ℓ W τ hW)

end
end Dubon2026.SourceFunctionField
