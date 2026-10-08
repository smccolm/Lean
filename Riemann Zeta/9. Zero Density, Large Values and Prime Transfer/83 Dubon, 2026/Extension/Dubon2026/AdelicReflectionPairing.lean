import Dubon2026.AdelicProjectiveReflection
import Dubon2026.AdelicPositiveRightAction

/-! # Actual reflection invariance of the original adelic quotient pairing -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open MeasureTheory
open scoped MatrixGroups ComplexConjugate

/-- Reflection carries the genuine original arithmetic domain to another actual arithmetic fundamental domain. -/
theorem adelicProjectiveGamma0Domain_reflection (N : ℕ) [NeZero N] :
    IsFundamentalDomain adelicProjectiveArithmetic
      (adelicProjectiveReflection '' adelicProjectiveGamma0Domain N) adelicProjectiveMeasure := by
  have hs : MeasurePreserving adelicProjectiveReflection.symm adelicProjectiveMeasure
      adelicProjectiveMeasure := by
    rw [adelicProjectiveReflection_symm]
    exact adelicProjectiveReflection_measurePreserving
  apply (adelicProjectiveGamma0Domain_isFundamental N).image_of_equiv
    adelicProjectiveReflection.toEquiv hs.quasiMeasurePreserving
    adelicProjectiveArithmeticReflection.toEquiv
  intro γ p
  change adelicProjectiveReflection (adelicProjectiveReflection γ.val * p) =
    γ.val * adelicProjectiveReflection p
  rw [map_mul, adelicProjectiveReflection_involutive]

/-- The actual arithmetic quotient integral is invariant under the original rational reflection. -/
theorem adelicProjective_integral_reflection (N : ℕ) [NeZero N]
    (F : AdelicProjectiveGroup → ℂ)
    (hF : ∀ (γ : adelicProjectiveArithmetic) p, F (γ • p) = F p) :
    (∫ p in adelicProjectiveGamma0Domain N, F (adelicProjectiveReflection p) ∂adelicProjectiveMeasure) =
      ∫ p in adelicProjectiveGamma0Domain N, F p ∂adelicProjectiveMeasure := by
  rw [← adelicProjectiveReflection_measurePreserving.setIntegral_image_emb
    adelicProjectiveReflection.toHomeomorph.toMeasurableEquiv.measurableEmbedding]
  exact (adelicProjectiveGamma0Domain_reflection N).setIntegral_eq
    (adelicProjectiveGamma0Domain_isFundamental N) hF

/-- The original rational reflection viewed in the canonical full adelic general-linear group. -/
def canonicalAdelicGL2Reflection : RationalAdelicGL2 :=
  GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) rationalGL2Reflection

/-- The actual full adelic rational reflection squares to the original identity. -/
theorem canonicalAdelicGL2Reflection_mul_self :
    canonicalAdelicGL2Reflection * canonicalAdelicGL2Reflection = 1 := by
  rw [canonicalAdelicGL2Reflection, ← map_mul, rationalGL2Reflection_mul_self, map_one]

/-- The original full adelic right reflection descends exactly to the genuine projective reflection automorphism. -/
theorem adelicCyclicProjectiveFunction_reflection_right (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) (p : AdelicProjectiveGroup) :
    adelicCyclicProjectiveFunction N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation canonicalAdelicGL2Reflection v) p =
        adelicCyclicProjectiveFunction N f v (adelicProjectiveReflection p) := by
  obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective p.1
  obtain ⟨a, ha⟩ := ProjGenLinGroup.mk_surjective p.2
  have hp : p = (QuotientGroup.mk r, ProjGenLinGroup.mk a) := Prod.ext hr.symm ha.symm
  rw [hp, adelicProjectiveReflection_mk, adelicCyclicProjectiveFunction_mk,
    adelicCyclicProjectiveFunction_mk]
  have he : rationalAdelicGL2RealFiniteEquiv.symm (toGL (realSL2Reflection r),
      rationalGL2ToFinite rationalGL2Reflection * a * rationalGL2ToFinite rationalGL2Reflection) =
      canonicalAdelicGL2Reflection * rationalAdelicGL2RealFiniteEquiv.symm (toGL r, a) *
        canonicalAdelicGL2Reflection := by
    apply rationalAdelicGL2RealFiniteEquiv.injective
    rw [MulEquiv.apply_symm_apply, map_mul, map_mul, canonicalAdelicGL2Reflection,
      rationalAdelicGL2RealFiniteEquiv_rational, MulEquiv.apply_symm_apply,
      realSL2Reflection_toGL]
    rfl
  rw [he]
  change v.val (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, a) * canonicalAdelicGL2Reflection) = _
  symm
  rw [mul_assoc]
  exact adelicLiftCyclic_rational_invariant N f v.property rationalGL2Reflection _

/-- Original full adelic rational reflection preserves the actual faithful L2 inner product. -/
theorem adelicLiftCyclic_reflection_inner (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v w : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    inner ℂ (adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation canonicalAdelicGL2Reflection v))
      (adelicProjectiveCyclicToL2 N f
        ((adelicLiftCyclicRepresentation N k f).toRepresentation canonicalAdelicGL2Reflection w)) =
      inner ℂ (adelicProjectiveCyclicToL2 N f v) (adelicProjectiveCyclicToL2 N f w) := by
  rw [adelicProjectiveCyclicToL2_inner, adelicProjectiveCyclicToL2_inner]
  unfold adelicProjectiveCyclicPairing
  simp_rw [adelicCyclicProjectiveFunction_reflection_right]
  apply adelicProjective_integral_reflection N (fun p =>
    conj (adelicCyclicProjectiveFunction N f v p) * adelicCyclicProjectiveFunction N f w p)
  intro γ p
  change conj (adelicCyclicProjectiveFunction N f v (γ.val * p)) *
    adelicCyclicProjectiveFunction N f w (γ.val * p) = _
  rw [adelicCyclicProjectiveFunction_arithmetic_invariant,
    adelicCyclicProjectiveFunction_arithmetic_invariant]

end
end Dubon2026
