import Dubon2026.SourceOriginalCMQuadraticField
import Dubon2026.SourceOriginalSupportResidual
import Dubon2026.SourceOriginalConstructedCMProperty

/-! DUB-17/18 -> actual CM deformation input. Construct the CM field in
support 4a, retain the original cyclotomic determinant by root comparison, and
apply the existing native polarization and original finite-image kernel results.
No CM field or determinant compatibility is an extra hypothesis. -/
namespace Dubon2026.SourceDickson
noncomputable section
open NumberField Algebra Matrix
open scoped NumberField

/-- Preserve the original rational scalar structure. -/
private local instance originalConstructedCMAssemblyAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

/-- The actual odd cyclotomic determinant constructs a genuine CM residual
model on enlarged support. Its symmetric kernel consequences follow from the
original finite linear bounds; those bounds are not separately postulated on
the enlarged group or the CM kernel. -/
theorem original_cyclotomic_constructed_cm_residual
    (a : 𝓞 ℚ) (p w : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a)
    (hp3 : 3 < p) (hw : Odd w)
    {L : Type} [Field L] [Finite L] [CharP L p] [TopologicalSpace L]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) L)
    (hdet : GeneralLinearGroup.det.comp ρ =
      (sourceArithmeticCyclotomicUnitCharacter (F := L) p a hpa).toMonoidHom ^ w) :
    HasOriginalConstructedCMResidual a p ρ := by
  intro hDiscrete hρ
  letI := hDiscrete
  obtain ⟨C, hC, hComplex⟩ :=
    original_unramified_exists_cm_quadratic_of_four_dvd (4 * a) (dvd_mul_right 4 a)
  letI := hC
  letI := hComplex
  let ρs : rationalArithmeticGaloisGroup (4 * a) →ₜ* GeneralLinearGroup (Fin 2) L :=
    (show rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup (Fin 2) L from ⟨ρ, hρ⟩).comp
      (rationalArithmeticSupportRestriction a (4 * a) (dvd_mul_left a 4))
  have hp4 : (p : 𝓞 ℚ) ∣ 4 * a := hpa.trans (dvd_mul_left a 4)
  have hdets : GeneralLinearGroup.det.comp ρs.toMonoidHom =
      (sourceArithmeticCyclotomicUnitCharacter (F := L) p (4 * a) hp4).toMonoidHom ^ w :=
    original_support_residual_determinant a (4 * a) (dvd_mul_left a 4) p w hpa hp4 ρ hdet
  refine ⟨C, hC, hComplex, ?_, ?_⟩
  · intro j hj
    have hs : HasFiniteLinearSubfieldBounds p j ρs.toMonoidHom :=
      original_support_finite_linear_bounds a (4 * a) (dvd_mul_left a 4) p j ρ hj
    exact (finite_linear_bounds_original_rational_cm_consequences
      (4 * a) p j ρs.toMonoidHom hp3 hs hDiscrete ρs.continuous C hC).1
  · intro n hn
    exact original_rational_cm_exists_polarized_symmetric
      (4 * a) p w n hp4 hw hn ρs.toMonoidHom ρs.continuous hdets C

end
end Dubon2026.SourceDickson
