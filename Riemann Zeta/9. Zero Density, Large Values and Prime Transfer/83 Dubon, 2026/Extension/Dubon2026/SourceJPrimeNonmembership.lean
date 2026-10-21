import Dubon2026.SourceJPrimeNonpolynomial
import Dubon2026.SourcePrimeMonicDegree
import Dubon2026.SourceOriginalModularFunctionField
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! DUB-17/18 -> numerical modular genus -> exact original j-map degree.
The original prime monic relation gives integrality over the polynomial
j-algebra. Native integral-root descent then turns membership in the
rational j-field into a polynomial identity, contradicted by the proved
positive-coefficient orbit argument. No irreducibility or symmetry of a
modular polynomial is an input to this nonmembership theorem.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

theorem prime_j_integral_polynomial_algebra (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ L] :
    IsIntegral (Algebra.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)))
      (coeffEmb L (qExpand ℚ p jq)) := by
  let B := Algebra.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))
  let j : B := ⟨coeffEmb L jq, Algebra.self_mem_adjoin_singleton L _⟩
  let ψ : Polynomial ℤ →+* B := Polynomial.eval₂RingHom (Int.castRingHom _) j
  obtain ⟨P, hPm, _, hP0⟩ := exists_prime_monic_relation_degree p
  have hcomp : (algebraMap B (LaurentSeries L)).comp ψ = (coeffEmb L).comp evalAtJ := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, evalAtJ_X]
    change algebraMap B (LaurentSeries L) (Polynomial.eval₂ (Int.castRingHom _) j X) = _
    rw [Polynomial.eval₂_X]
    rfl
  refine ⟨P.map ψ, hPm.map ψ, ?_⟩
  rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂,
    hP0, map_zero]

theorem prime_j_not_mem_rational_j (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ L] :
    coeffEmb L (qExpand ℚ p jq) ∉
      IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  intro hmem
  let A := Algebra.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))
  let B := IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))
  have ht : Transcendental L (coeffEmb L jq) := by
    rw [coeffEmb_jq]
    exact transcendental_jqModC L
  letI : UniqueFactorizationMonoid A := ht.uniqueFactorizationMonoid_adjoin
  let x : B := ⟨coeffEmb L (qExpand ℚ p jq), hmem⟩
  have hi : IsIntegral A x :=
    (isIntegral_algebraMap_iff (algebraMap B (LaurentSeries L)).injective).mp
      (prime_j_integral_polynomial_algebra p L)
  obtain ⟨P, hPm, hP0⟩ := hi
  obtain ⟨a, ha, _⟩ := exists_integer_of_is_root_of_monic hPm hP0
  have hx : coeffEmb L (qExpand ℚ p jq) = (a : LaurentSeries L) := by
    have h := congrArg (fun t : B => (t : LaurentSeries L)) ha
    exact h.trans (IntermediateField.algebraAdjoinAdjoin.coe_algebraMap L
      ({coeffEmb L jq} : Set (LaurentSeries L)) a)
  have hm : coeffEmb L (qExpand ℚ p jq) ∈ A := by
    rw [hx]
    exact a.2
  change coeffEmb L (qExpand ℚ p jq) ∈
    Algebra.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)) at hm
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
  obtain ⟨Q, hQ⟩ := (AlgHom.mem_range _).mp hm
  have he : coeffEmb L (qExpand ℚ p jq) = jqNModC L p := by
    change coeffMap (algebraMap ℚ L) (qExpand ℚ p jq) = _
    rw [coeffMap_qExpand]
    change qExpand L p (coeffEmb L jq) = _
    rw [coeffEmb_jq]
    rfl
  rw [coeffEmb_jq, he] at hQ
  exact PrimeDegreeAux.aeval_jqModC_ne_jqNModC_charZero p Q hQ

end
end Dubon2026.SourceFunctionField
