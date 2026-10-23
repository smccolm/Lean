import Dubon2026.SourceResiduePrimePolynomialRoots
import Dubon2026.SourcePrimeJResidueNonmembership
import Dubon2026.SourcePrimeOrbitIrreducibility

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> residual association -> original Frobenius/inertia -> actual
modular-curve good reduction -> exact residue-field degree. Reuse the existing
finite-orbit irreducibility theorem with the specialized integral polynomial.
The final rational-j-field consumer discharges nonmembership by the actual
Hasse/norm/eta argument, for every prime away from the characteristic.
The intermediate-field argument adapts the existing characteristic-zero
SourcePrimeExactFieldDegree construction; no new Galois theory is needed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux

theorem prime_extension_degree_coeff_of_not_mem
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime]
    (hpK : (p : K) ≠ 0) (F : IntermediateField K (LaurentSeries K))
    (hj : jqModC K ∈ F) (hpF : qExpand K p (jqModC K) ∉ F) :
    Module.finrank F (IntermediateField.adjoin F
      ({qExpand K p (jqModC K)} : Set (LaurentSeries K))) = p + 1 := by
  haveI : NeZero (p : K) := ⟨hpK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  obtain ⟨ζ, hζval⟩ := hz.isUnit (Nat.Prime.ne_zero (Fact.out : p.Prime))
  have hζ : IsPrimitiveRoot (ζ : K) p := hζval.symm ▸ hz
  obtain ⟨P, hm, hd, hrel⟩ := exists_prime_adjacent_relations_coeff p
  let j : F := ⟨jqModC K, hj⟩
  let Q := relationAtSeed P j
  let ι := qExpand K p
  let α := qExpand K p (jqModC K)
  have hQm : Q.Monic := hm.map _
  have hQd : Q.natDegree = p + 1 := (hm.natDegree_map _).trans hd
  have hQmap : Q.map (ι.comp (algebraMap F (LaurentSeries K))) =
      relationAtSeed P (qExpand K p (jqModC K)) := by
    rw [relationAtSeed_map]
    rfl
  have hQroot : Polynomial.aeval α Q = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, relationAtSeed_map]
    change (relationAtSeed P (jqModC K)).eval α = 0
    simpa only [qExpand_one_apply, one_mul] using (hrel K 1).1
  have hα : IsIntegral F α := ⟨Q, hQm, hQroot⟩
  have hf := (hrel K p).1
  have hr : (relationAtSeed P (qExpand K p (jqModC K))).eval (jqModC K) = 0 := by
    simpa only [qExpand_one_apply, one_mul] using (hrel K 1).2
  have hirr : Irreducible Q := by
    letI : Algebra F (LaurentSeries K) :=
      (ι.comp (algebraMap F (LaurentSeries K))).toAlgebra
    have halg : ∀ a : F, algebraMap F (LaurentSeries K) a = ι a := fun _ => rfl
    have hmap : Q.map (algebraMap F (LaurentSeries K)) =
        relationAtSeed P (qExpand K p (jqModC K)) := hQmap
    refine irreducible_of_transitive_ringAut Q hQm ?_ (qTwistEquiv ζ) ?_
      (TS K (p * p) 1) (fun b => TS K 1 (ζ ^ b)) p ?_ ?_ ?_ ?_
    · rw [hmap]
      exact residue_prime_polynomial_splits K p ζ hζ P hm hd hf hr
    · intro a
      rw [halg, qTwistEquiv_apply]
      exact qTwist_qExpand_of_pow_eq_one p ζ
        (units_pow_eq_one_of_isPrimitiveRoot hζ) a
    · rw [hmap]
      exact residue_prime_polynomial_roots K p ζ hζ P hm hd hf hr
    · rw [hmap, residue_prime_polynomial_roots K p ζ hζ P hm hd hf hr]
      exact roots_phiProd_conj_nodup p ζ hζ
    · intro i _
      rw [qTwistEquiv_apply]
      exact qTwist_TS_one_cycle ζ (units_pow_eq_one_of_isPrimitiveRoot hζ) i
    · rintro ⟨a, ha⟩
      rw [halg] at ha
      have he : ι α = TS K (p * p) 1 := by
        dsimp only [ι, α]
        rw [qExpand_qExpand, TS, qTwist_one_apply]
      have hval : (a : LaurentSeries K) = α := ι.injective (ha.trans he.symm)
      apply hpF
      change α ∈ F
      rw [← hval]
      exact a.2
  have hmin : Q = minpoly F α := minpoly.eq_of_irreducible_of_monic hirr hQroot hQm
  rw [IntermediateField.adjoin.finrank hα, ← hmin, hQd]

theorem prime_j_extension_finrank_coeff_eq
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime]
    (hpK : (p : K) ≠ 0) :
    let B := IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))
    Module.finrank B (IntermediateField.adjoin B
      ({qExpand K p (jqModC K)} : Set (LaurentSeries K))) = p + 1 :=
  prime_extension_degree_coeff_of_not_mem K p hpK _
    (IntermediateField.mem_adjoin_simple_self K _)
    (prime_j_not_mem_rational_j_away_characteristic p K hpK)

end
end Dubon2026.SourceFunctionField
