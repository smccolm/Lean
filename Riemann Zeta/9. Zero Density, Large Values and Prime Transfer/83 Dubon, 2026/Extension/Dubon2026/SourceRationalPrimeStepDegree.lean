import Dubon2026.SourceMixedPrimePowerNonmembership

/-! DUB-17/18 -> numerical modular genus -> composite degree -> first
prime step over the original rational base field. The existing prime
root-cycle irreducibility theorem works after the literal coefficient
embedding into the rational algebraic closure. The expansion embedding
is injective, and its image is fixed by the root twist. This proves
degree p+1 for any actual rational Laurent subfield containing j but
not j_p, without requiring its coefficient field to be algebraically closed.
The actual mixed-level consumer supplies nonmembership from the preceding
coprime induction proof.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux

theorem rational_prime_step_finrank_eq_of_not_mem
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (hj : jq ∈ F)
    (p : ℕ) [Fact p.Prime] (hpF : qExpand ℚ p jq ∉ F) :
    Module.finrank F (IntermediateField.adjoin F
      ({qExpand ℚ p jq} : Set (LaurentSeries ℚ))) = p + 1 := by
  let K := AlgebraicClosure ℚ
  obtain ⟨ζ, P, hζ, hPm, hdeg, hP⟩ := exists_prime_product_algClosed p K
  let j : F := ⟨jq, hj⟩
  let ψ : Polynomial ℤ →+* F := Polynomial.eval₂RingHom (Int.castRingHom _) j
  let Q := P.map ψ
  let ι := (coeffEmb K).comp (qExpand ℚ p)
  let α := qExpand ℚ p jq
  have hQm : Q.Monic := hPm.map ψ
  have hQdeg : Q.natDegree = p + 1 := (hPm.natDegree_map ψ).trans hdeg
  have hcomp : (ι.comp (algebraMap F (LaurentSeries ℚ))).comp ψ =
      ((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.comp_apply]
    rw [evalAtJ_X]
    change ι (algebraMap F (LaurentSeries ℚ)
      (Polynomial.eval₂ (Int.castRingHom _) j X)) = _
    rw [Polynomial.eval₂_X]
    rfl
  have hQmap : Q.map (ι.comp (algebraMap F (LaurentSeries ℚ))) =
      PhiGen.phiProd p (PhiGen.conj p ζ) := by
    change (P.map ψ).map _ = _
    rw [Polynomial.map_map, hcomp]
    exact hP
  have he : ι α = TS K (p * p) 1 := by
    change coeffEmb K (qExpand ℚ p (qExpand ℚ p jq)) = _
    rw [qExpand_qExpand, coeffEmb_qExpand_jq_eq_TS]
  have hQroot : Polynomial.aeval α Q = 0 := by
    apply ι.injective
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂,
      ← Polynomial.eval_map, hQmap, he, ← conj_zero_eq p ζ]
    exact PhiGen.phiProd_eval_conj p _ 0
  have hα : IsIntegral F α := ⟨Q, hQm, hQroot⟩
  have hirr : Irreducible Q := by
    letI : Algebra F (LaurentSeries K) :=
      (ι.comp (algebraMap F (LaurentSeries ℚ))).toAlgebra
    have halg : ∀ a : F, algebraMap F (LaurentSeries K) a = ι a := fun _ => rfl
    have hmap : Q.map (algebraMap F (LaurentSeries K)) =
        PhiGen.phiProd p (PhiGen.conj p ζ) := hQmap
    refine irreducible_of_transitive_ringAut Q hQm ?_ (qTwistEquiv ζ) ?_
      (TS K (p * p) 1) (fun b => TS K 1 (ζ ^ b)) p ?_ ?_ ?_ ?_
    · rw [hmap, PhiGen.phiProd]
      exact Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _
    · intro a
      rw [halg, qTwistEquiv_apply]
      change qTwist ζ (coeffEmb K (qExpand ℚ p (a : LaurentSeries ℚ))) =
        coeffEmb K (qExpand ℚ p (a : LaurentSeries ℚ))
      rw [show coeffEmb K (qExpand ℚ p (a : LaurentSeries ℚ)) =
        qExpand K p (coeffEmb K (a : LaurentSeries ℚ)) from
          coeffMap_qExpand (algebraMap ℚ K) p (a : LaurentSeries ℚ)]
      exact qTwist_qExpand_of_pow_eq_one p ζ
        (units_pow_eq_one_of_isPrimitiveRoot hζ) _
    · rw [hmap, roots_phiProd_conj]
    · rw [hmap, roots_phiProd_conj]
      exact roots_phiProd_conj_nodup p ζ hζ
    · intro i _
      rw [qTwistEquiv_apply]
      exact qTwist_TS_one_cycle ζ (units_pow_eq_one_of_isPrimitiveRoot hζ) i
    · rintro ⟨a, ha⟩
      rw [halg] at ha
      have hval : (a : LaurentSeries ℚ) = α := ι.injective (ha.trans he.symm)
      apply hpF
      change α ∈ F
      rw [← hval]
      exact a.2
  have hmin : Q = minpoly F α := minpoly.eq_of_irreducible_of_monic hirr hQroot hQm
  rw [IntermediateField.adjoin.finrank hα, ← hmin, hQdeg]

end
end Dubon2026.SourceFunctionField
