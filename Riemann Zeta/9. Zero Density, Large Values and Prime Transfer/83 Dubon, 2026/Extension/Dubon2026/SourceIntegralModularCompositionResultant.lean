import Dubon2026.SourceIntegralResultantCommonRoot

/-! The original integral level-ab modular polynomial divides the
composition resultant of the level-a and level-b polynomials. Reuse the
already proved integral minimal-polynomial identification and native monic
division; no new irreducibility package or splitting field is needed.
Adapted from S_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. This is the composition input to
the all-level cyclic-root bijection and DUB-17/18 inertia census. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial
noncomputable section

/-- Reindexing the actual j-coordinate evaluation gives evaluation at the reindexed j. -/
theorem qExpand_comp_evalAtJ (a : ℕ) [NeZero a] :
    (qExpand ℚ a).comp evalAtJ =
      eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) (qExpand ℚ a jq) := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  rw [RingHom.comp_apply, evalAtJ_X, coe_eval₂RingHom, eval₂_X]

/-- The actual integral modular polynomial at a product level divides the composition resultant. -/
theorem modularPolynomial_dvd_compositionResultant (a b : ℕ) [NeZero a] [NeZero b] :
    modularPolynomial (a * b) ∣
      ((modularPolynomial a).map (Polynomial.C : ℤ[X] →+* Polynomial ℤ[X])).resultant
        ((modularPolynomial b).eval₂
          (Polynomial.mapRingHom (Int.castRingHom (Polynomial ℤ[X]))) (Polynomial.C Polynomial.X)) := by
  let B := Polynomial ℤ[X]
  set f : Polynomial B := (modularPolynomial a).map (Polynomial.C : ℤ[X] →+* B) with hf
  set g : Polynomial B := (modularPolynomial b).eval₂
    (Polynomial.mapRingHom (Int.castRingHom B)) (Polynomial.C Polynomial.X) with hg
  set R : B := f.resultant g with hR
  let L := LaurentSeries ℚ
  set Ξ : B →+* L := eval₂RingHom evalAtJ (qExpand ℚ (a * b) jq) with hΞ
  have hΞC : Ξ.comp Polynomial.C = evalAtJ := RingHom.ext fun c => by
    rw [RingHom.comp_apply, hΞ, coe_eval₂RingHom, eval₂_C]
  have hΞX : Ξ Polynomial.X = qExpand ℚ (a * b) jq := by
    rw [hΞ, coe_eval₂RingHom, eval₂_X]
  set f' : Polynomial L := (modularPolynomial a).map evalAtJ with hf'
  set g' : Polynomial L := (modularPolynomial b).eval₂
    (Polynomial.mapRingHom (Int.castRingHom L)) (Polynomial.C (qExpand ℚ (a * b) jq)) with hg'
  have hff' : f.map Ξ = f' := by rw [hf, Polynomial.map_map, hΞC]
  have hgg' : g.map Ξ = g' := by
    rw [hg, ← Polynomial.coe_mapRingHom, Polynomial.hom_eval₂, hg']
    congr 1
    · refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp
    · rw [Polynomial.coe_mapRingHom, Polynomial.map_C, hΞX]
  have hf'm : f'.Monic := (modularPolynomial_monic a).map _
  have hdegf : f'.natDegree = f.natDegree := by
    rw [hf', hf, (modularPolynomial_monic a).natDegree_map, (modularPolynomial_monic a).natDegree_map]
  have hdegG : g'.natDegree ≤ g.natDegree := by rw [← hgg']; exact natDegree_map_le
  have hfz : f'.IsRoot (qExpand ℚ a jq) := by
    rw [IsRoot.def, hf', eval_map]
    exact modularPolynomial_eval a
  have hgz : g'.IsRoot (qExpand ℚ a jq) := by
    rw [IsRoot.def, hg', ← coe_evalRingHom, Polynomial.hom_eval₂, coe_evalRingHom, eval_C]
    have h1 : (evalRingHom (qExpand ℚ a jq)).comp (Polynomial.mapRingHom (Int.castRingHom L)) =
        eval₂RingHom (Int.castRingHom L) (qExpand ℚ a jq) := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp
    rw [h1, ← qExpand_comp_evalAtJ a, ← qExpand_qExpand,
      ← Polynomial.hom_eval₂, modularPolynomial_eval b, map_zero]
  have hΞR : Ξ R = 0 := by
    rw [hR, ← resultant_map_map, hff', hgg', ← hdegf]
    exact resultant_zero_of_common_root f' g' g.natDegree hdegG hf'm.ne_zero _ hfz hgz
  have hcomp : (algebraMap J L).comp evaluate = evalAtJ := by
    apply RingHom.ext
    intro c
    exact algebraMap_evaluate c
  have haeval : aeval (qExpand ℚ (a * b) jq) (R.map evaluate) = 0 := by
    rw [aeval_def, eval₂_map, hcomp]
    exact hΞR
  have hdvd : (modularPolynomial (a * b)).map evaluate ∣ R.map evaluate := by
    rw [modularPolynomial_map_coordinate]
    exact minpoly.dvd _ _ haeval
  change modularPolynomial (a * b) ∣ R
  rw [← modByMonic_eq_zero_iff_dvd (modularPolynomial_monic (a * b))]
  apply Polynomial.map_injective evaluate evaluate_injective
  rw [Polynomial.map_zero, Polynomial.map_modByMonic _ (modularPolynomial_monic (a * b)),
    modByMonic_eq_zero_iff_dvd ((modularPolynomial_monic (a * b)).map _)]
  exact hdvd

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
