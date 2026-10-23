import Dubon2026.SourceExactIntegralModularPolynomial
import Dubon2026.SourceModularCoefficientRootEquivalence

/-! The constructed integral modular polynomial is the actual j_N minimal
polynomial over the coefficient j-field in every allowed characteristic.
The integral relation specializes from the frozen original series, and
the existing degree psi(N) proves equality of the two monic polynomials.
This discharges the polynomial-identification input in the DUB-17/18
finite exceptional-fiber orbit route. -/
namespace Dubon2026.SourceFunctionField.CoefficientPresentation
noncomputable section
open IntermediateField Polynomial
open scoped IntermediateField
variable (N : ℕ) [NeZero N] (K : Type*) [Field K]

theorem aeval_level_modularPolynomial :
    aeval (jN N K) (relationAtSeed (IntegralJCoordinate.modularPolynomial N)
      (AdjoinSimple.gen K (jCoeff N K))) = 0 := by
  apply (algebraMap (modularFunctionFieldCoeff N K) (LaurentSeries K)).injective
  rw [map_zero, aeval_def, relationAtSeed, eval₂_map, Polynomial.hom_eval₂]
  have he : ((algebraMap (modularFunctionFieldCoeff N K) (LaurentSeries K)).comp
      (algebraMap K⟮jCoeff N K⟯ (modularFunctionFieldCoeff N K))).comp
        (eval₂RingHom (Int.castRingHom K⟮jCoeff N K⟯) (AdjoinSimple.gen K (jCoeff N K))) =
          eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqModC K) :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp only
      [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_X]; rfl)
  rw [← RingHom.comp_assoc, he]
  simpa only [relationAtSeed, Polynomial.eval_map] using
    original_monic_relation_specializes N (IntegralJCoordinate.modularPolynomial N) K
      (IntegralJCoordinate.modularPolynomial_eval N)

variable [IsAlgClosed K]

theorem minpoly_level_eq_modularPolynomial (hNK : (N : K) ≠ 0) :
    minpoly K⟮jCoeff N K⟯ (jN N K) =
      relationAtSeed (IntegralJCoordinate.modularPolynomial N) (AdjoinSimple.gen K (jCoeff N K)) := by
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (level_isIntegral N K))
    ((IntegralJCoordinate.modularPolynomial_monic N).map _)
    (minpoly.dvd _ _ (aeval_level_modularPolynomial N K)) ?_).symm
  dsimp only [relationAtSeed]
  rw [(IntegralJCoordinate.modularPolynomial_monic N).natDegree_map,
    IntegralJCoordinate.modularPolynomial_natDegree, level_minpoly_natDegree N K hNK]

end
end Dubon2026.SourceFunctionField.CoefficientPresentation
