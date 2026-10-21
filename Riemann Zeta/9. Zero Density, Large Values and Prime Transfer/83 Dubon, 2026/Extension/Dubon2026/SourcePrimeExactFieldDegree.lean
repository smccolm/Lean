import Dubon2026.SourcePrimeConjugateBaseChange
import Dubon2026.SourcePrimeOrbitIrreducibility
import Dubon2026.SourceJPrimeNonmembership

/-! DUB-17/18 -> numerical modular genus -> exact original j-map degree.
The actual prime conjugate product is irreducible over any intermediate
field containing j but not j(q^p). The original rational j-field consumer
derives this nonmembership from the actual coefficient obstruction.
The algebraically closed coefficient field is the one used by the original
place and canonical-genus calculation. All-level generation and degree,
ramification and fiber counts remain required.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux

theorem prime_extension_degree_of_not_mem
    (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
    (F : IntermediateField L (LaurentSeries L))
    (hj : coeffEmb L jq ∈ F) (p : ℕ) [Fact p.Prime]
    (hpF : coeffEmb L (qExpand ℚ p jq) ∉ F) :
    Module.finrank F (IntermediateField.adjoin F
      ({coeffEmb L (qExpand ℚ p jq)} : Set (LaurentSeries L))) = p + 1 := by
  obtain ⟨ζ, P, hζ, hPm, hdeg, hP⟩ := exists_prime_product_algClosed p L
  let j : F := ⟨coeffEmb L jq, hj⟩
  let ψ : Polynomial ℤ →+* F := Polynomial.eval₂RingHom (Int.castRingHom _) j
  let Q := P.map ψ
  let ι := qExpand L p
  let α := coeffEmb L (qExpand ℚ p jq)
  have hQm : Q.Monic := hPm.map ψ
  have hQdeg : Q.natDegree = p + 1 := (hPm.natDegree_map ψ).trans hdeg
  have hcomp : (ι.comp (algebraMap F (LaurentSeries L))).comp ψ =
      ((coeffEmb L).comp (qExpand ℚ p)).comp evalAtJ := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.comp_apply]
    rw [evalAtJ_X]
    change ι (algebraMap F (LaurentSeries L)
      (Polynomial.eval₂ (Int.castRingHom _) j X)) = _
    rw [Polynomial.eval₂_X]
    exact (coeffMap_qExpand (algebraMap ℚ L) p jq).symm
  have hQmap : Q.map (ι.comp (algebraMap F (LaurentSeries L))) =
      PhiGen.phiProd p (PhiGen.conj p ζ) := by
    change (P.map ψ).map _ = _
    rw [Polynomial.map_map, hcomp]
    exact hP
  have he : ι α = PhiGen.conj p ζ 0 := by
    change qExpand L p (coeffEmb L (qExpand ℚ p jq)) = _
    rw [show coeffEmb L (qExpand ℚ p jq) = qExpand L p (coeffEmb L jq) from
      coeffMap_qExpand (algebraMap ℚ L) p jq]
    rw [qExpand_qExpand, PhiGen.conj_zero]
  have hQroot : Polynomial.aeval α Q = 0 := by
    apply ι.injective
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂,
      ← Polynomial.eval_map, hQmap, he]
    exact PhiGen.phiProd_eval_conj p _ 0
  have hα : IsIntegral F α := ⟨Q, hQm, hQroot⟩
  have hirr : Irreducible Q := by
    letI : Algebra F (LaurentSeries L) :=
      (ι.comp (algebraMap F (LaurentSeries L))).toAlgebra
    have halg : ∀ a : F, algebraMap F (LaurentSeries L) a = ι a := fun _ => rfl
    have hmap : Q.map (algebraMap F (LaurentSeries L)) =
        PhiGen.phiProd p (PhiGen.conj p ζ) := hQmap
    refine irreducible_of_transitive_ringAut Q hQm ?_ (qTwistEquiv ζ) ?_
      (TS L (p * p) 1) (fun b => TS L 1 (ζ ^ b)) p ?_ ?_ ?_ ?_
    · rw [hmap, PhiGen.phiProd]
      exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _
    · intro a
      rw [halg, qTwistEquiv_apply]
      exact qTwist_qExpand_of_pow_eq_one p ζ
        (units_pow_eq_one_of_isPrimitiveRoot hζ) a
    · rw [hmap, roots_phiProd_conj]
    · rw [hmap, roots_phiProd_conj]
      exact roots_phiProd_conj_nodup p ζ hζ
    · intro i _
      rw [qTwistEquiv_apply]
      exact qTwist_TS_one_cycle ζ (units_pow_eq_one_of_isPrimitiveRoot hζ) i
    · rintro ⟨a, ha⟩
      rw [halg] at ha
      have he' : ι α = TS L (p * p) 1 := he.trans (conj_zero_eq p ζ)
      have hval : (a : LaurentSeries L) = α := ι.injective (ha.trans he'.symm)
      apply hpF
      change α ∈ F
      rw [← hval]
      exact a.2
  have hmin : Q = minpoly F α := minpoly.eq_of_irreducible_of_monic hirr hQroot hQm
  rw [IntermediateField.adjoin.finrank hα, ← hmin, hQdeg]

theorem prime_j_extension_finrank_eq
    (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
    (p : ℕ) [Fact p.Prime] :
    let B := IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))
    Module.finrank B (IntermediateField.adjoin B
      ({coeffEmb L (qExpand ℚ p jq)} : Set (LaurentSeries L))) = p + 1 :=
  prime_extension_degree_of_not_mem L _
    (IntermediateField.mem_adjoin_simple_self L _) p (prime_j_not_mem_rational_j p L)

end
end Dubon2026.SourceFunctionField
