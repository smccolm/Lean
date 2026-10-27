import Dubon2026.SourceFrickeCyclotomicFractionGerm
import Dubon2026.SourceCuspLaurentPolynomial

/-! DUB-17/18 -> actual Gamma1 differential/cusp comparison -> rational
Fourier structure -> integral base change of Fricke fractions. The existing
Laurent coefficient retraction descends an actual complex monic relation
to the original cyclotomic j-series. The Fourier representation of the
fraction is proved from its actual numerator/denominator identity. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold ModularForm MatrixGroups

theorem exists_integral_cyclotomic_laurent_of_monic {N : ℕ} [NeZero N]
    {a b f : ℍ → ℂ} (ha : a ∈ cyclotomicLevelRing N) (hb : b ∈ cyclotomicLevelRing N)
    (hb0 : b ≠ 0) (hfrac : f * b = a) (d : ℕ) (p : Fin d → Polynomial ℂ)
    (hrel : ∀ τ : ℍ, f τ ^ d +
      ∑ i : Fin d, (p i).eval (JMultiplicity.jf τ) * f τ ^ (i : ℕ) = 0) :
    ∃ X : LaurentSeries (kN N),
      CuspTaylor.Represents (coeffMap (algebraMap (kN N) ℂ) X) (cuspFunction N f) ∧
      IsIntegral (Algebra.adjoin (kN N) ({jqNModC (kN N) N} : Set (LaurentSeries (kN N)))) X := by
  obtain ⟨X, hX⟩ := exists_cyclotomic_fraction_represents ha hb hb0 hfrac
  refine ⟨X, hX, isIntegral_adjoin_of_isIntegral_coeffMap (algebraMap (kN N) ℂ) _ _ ?_⟩
  rw [coeffMap_jqNModC_kN]
  exact hX.isIntegral_of_monic_relation (represents_jqNModC N) d p hrel

theorem exists_polynomial_monic_relation_of_isIntegral {K : Type*} [Field K]
    {J X : LaurentSeries K} (hX : IsIntegral (Algebra.adjoin K ({J} : Set (LaurentSeries K))) X) :
    ∃ (d : ℕ) (p : Fin d → Polynomial K),
      X ^ d + ∑ i : Fin d, Polynomial.aeval J (p i) * X ^ (i : ℕ) = 0 := by
  classical
  obtain ⟨Q, hQ, he⟩ := hX
  have hcoeff (n : ℕ) : ∃ P : Polynomial K,
      Polynomial.aeval J P = ((Q.coeff n : _) : LaurentSeries K) :=
    (Algebra.adjoin_singleton_eq_range_aeval K J).le (Q.coeff n).property
  choose p hp using hcoeff
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hQ.coeff_natDegree,
    map_one, one_mul] at he
  change (∑ n ∈ Finset.range Q.natDegree,
    ((Q.coeff n : _) : LaurentSeries K) * X ^ n) + X ^ Q.natDegree = 0 at he
  simp only [← hp] at he
  rw [← Fin.sum_univ_eq_sum_range (fun n => Polynomial.aeval J (p n) * X ^ n)
    Q.natDegree] at he
  exact ⟨Q.natDegree, fun i => p i, by simpa only [add_comm] using he⟩

theorem coeffMap_aeval_jqNModC_kN (N : ℕ) [NeZero N] (P : Polynomial (kN N)) :
    coeffMap (algebraMap (kN N) ℂ) (Polynomial.aeval (jqNModC (kN N) N) P) =
      Polynomial.aeval (jqNModC ℂ N) (P.map (algebraMap (kN N) ℂ)) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
  have hc : (coeffMap (algebraMap (kN N) ℂ)).comp (algebraMap (kN N) (LaurentSeries (kN N))) =
      (algebraMap ℂ (LaurentSeries ℂ)).comp (algebraMap (kN N) ℂ) := by
    ext c
    simp only [RingHom.comp_apply, SourceDifferential.algebraMap_laurentSeries_apply_alt,
      coeffMap_single]
  rw [hc, coeffMap_jqNModC_kN]

end
end Dubon2026.SourceFricke