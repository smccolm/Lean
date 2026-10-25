import Dubon2026.SourceIntegralPrimeLaurentRoots
import Dubon2026.SourceOriginalAllLevelDegree

/-! DUB-17/18 -> actual Hecke norm -> the Atkin-Lehner embedding census.
The existing all-level degree and coprime nonmembership identify the actual
prime minimal polynomial over the original lower field. Its reverse adjacent
Laurent relation gives the root needed for the q-expansion coefficient lift.
No polynomial-symmetry certificate is needed. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd, root-lift section. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux IntegralJCoordinate
variable (N p : ℕ) [NeZero N] [Fact p.Prime]
local notation "FF" => modularFunctionFieldFull N

/-- The original coefficient embedding given by q -> q^p. -/
def atkinBase : FF →+* LaurentSeries ℚ :=
  (qExpand ℚ p).comp (algebraMap FF (LaurentSeries ℚ))

/-- The exact integral prime polynomial evaluated at the lower field's j. -/
def atkinPrimePolynomial : Polynomial FF :=
  relationAtSeed (modularPolynomial p) (⟨jq, jq_mem_full N⟩ : FF)

theorem atkinPrime_minpoly_natDegree (hpN : ¬ p ∣ N) :
    (minpoly FF (qExpand ℚ p jq)).natDegree = p + 1 := by
  have hn := prime_j_not_mem_original_coprime_of_divisor_induction N p hpN
    (fun d _ _ => original_full_generation_and_degree d)
  rw [← IntermediateField.adjoin.finrank (original_j_substitution_isIntegral_over_full N p)]
  exact rational_prime_step_finrank_eq_of_not_mem FF (jq_mem_full N) p hn

theorem atkinPrime_minpoly_eq (hpN : ¬ p ∣ N) :
    minpoly FF (qExpand ℚ p jq) = atkinPrimePolynomial N p := by
  have hm : (atkinPrimePolynomial N p).Monic := (modularPolynomial_monic p).map _
  have hd : (atkinPrimePolynomial N p).natDegree = p + 1 :=
    ((modularPolynomial_monic p).natDegree_map _).trans (modularPolynomial_prime_natDegree p)
  have hz : Polynomial.aeval (qExpand ℚ p jq) (atkinPrimePolynomial N p) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, atkinPrimePolynomial, relationAtSeed_map]
    simpa only [qExpand_one_apply, one_mul] using
      (modularPolynomial_prime_adjacent_relations p ℚ 1).1
  symm
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (original_j_substitution_isIntegral_over_full N p)) hm (minpoly.dvd _ _ hz)
  rw [hd, atkinPrime_minpoly_natDegree N p hpN]

theorem atkinPrime_minpoly_reverse_root (hpN : ¬ p ∣ N) :
    (minpoly FF (qExpand ℚ p jq)).eval₂ (atkinBase N p) jq = 0 := by
  rw [atkinPrime_minpoly_eq N p hpN, ← Polynomial.eval_map,
    atkinPrimePolynomial, relationAtSeed_map]
  change (relationAtSeed (modularPolynomial p) (qExpand ℚ p jq)).eval jq = 0
  simpa only [qExpand_one_apply, one_mul] using
    (modularPolynomial_prime_adjacent_relations p ℚ 1).2

end
end Dubon2026.SourceFunctionField
