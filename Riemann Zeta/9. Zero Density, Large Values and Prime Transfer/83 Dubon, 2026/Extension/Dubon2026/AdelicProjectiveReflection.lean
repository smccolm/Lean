import Dubon2026.PositiveReflectionCoordinates

/-! # The actual rational reflection preserves adelic projective Haar measure and arithmetic -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup MeasureTheory
open scoped MatrixGroups

/-- The actual finite projective image of the original rational reflection. -/
def finiteProjectiveReflectionElement : RationalFiniteProjectiveGL2 :=
  ProjGenLinGroup.mk (rationalGL2ToFinite rationalGL2Reflection)

/-- The original finite projective reflection has actual square one. -/
theorem finiteProjectiveReflectionElement_mul_self :
    finiteProjectiveReflectionElement * finiteProjectiveReflectionElement = 1 := by
  rw [finiteProjectiveReflectionElement, ← map_mul, ← map_mul,
    rationalGL2Reflection_mul_self, map_one, map_one]

/-- The original finite projective reflection is its actual own inverse. -/
theorem finiteProjectiveReflectionElement_inv :
    finiteProjectiveReflectionElement⁻¹ = finiteProjectiveReflectionElement :=
  inv_eq_of_mul_eq_one_left finiteProjectiveReflectionElement_mul_self

/-- Actual rational reflection acts by its real outer automorphism and genuine finite inner conjugation. -/
def adelicProjectiveReflection : AdelicProjectiveGroup ≃ₜ* AdelicProjectiveGroup where
  toMulEquiv := realProjectiveReflection.toMulEquiv.prodCongr
    (MulAut.conj finiteProjectiveReflectionElement)
  continuous_toFun := (realProjectiveReflection.continuous.comp continuous_fst).prodMk
    ((continuous_const.mul continuous_snd).mul_const finiteProjectiveReflectionElement⁻¹)
  continuous_invFun := (realProjectiveReflection.symm.continuous.comp continuous_fst).prodMk
    ((continuous_const.mul continuous_snd).mul_const finiteProjectiveReflectionElement)

/-- The actual adelic projective reflection is involutive on every original point. -/
theorem adelicProjectiveReflection_involutive : Function.Involutive adelicProjectiveReflection := by
  intro p
  apply Prod.ext
  · exact realProjectiveReflectionHom_involutive p.1
  · change finiteProjectiveReflectionElement *
      (finiteProjectiveReflectionElement * p.2 * finiteProjectiveReflectionElement⁻¹) *
      finiteProjectiveReflectionElement⁻¹ = p.2
    rw [finiteProjectiveReflectionElement_inv]
    calc
      _ = (finiteProjectiveReflectionElement * finiteProjectiveReflectionElement) * p.2 *
        (finiteProjectiveReflectionElement * finiteProjectiveReflectionElement) := by group
      _ = p.2 := by rw [finiteProjectiveReflectionElement_mul_self, one_mul, mul_one]

/-- The original product Haar measure is genuinely preserved by actual rational reflection. -/
theorem adelicProjectiveReflection_measurePreserving :
    MeasurePreserving adelicProjectiveReflection adelicProjectiveMeasure adelicProjectiveMeasure := by
  have hf := (measurePreserving_mul_right finiteProjectiveGL2Measure
    finiteProjectiveReflectionElement⁻¹).comp
      (measurePreserving_mul_left finiteProjectiveGL2Measure finiteProjectiveReflectionElement)
  exact realProjectiveReflection_measurePreserving.prod hf

/-- Actual rational reflection in the projective coordinates agrees exactly with conjugation of the original positive rational matrix. -/
theorem adelicProjectiveReflection_rational (γ : GL(2, ℚ)⁺) :
    adelicProjectiveReflection (rationalPositiveToAdelicProjective γ) =
      rationalPositiveToAdelicProjective (rationalPositiveReflection γ) := by
  apply Prod.ext
  · change (QuotientGroup.mk (realSL2Reflection (realPositiveNormalize
      (rationalPositiveGL2ToReal γ))) : PSL(2, ℝ)) =
      QuotientGroup.mk (realPositiveNormalize (rationalPositiveGL2ToReal (rationalPositiveReflection γ)))
    rw [rationalPositiveReflection_real, realPositiveNormalize_reflection]
  · change finiteProjectiveReflectionElement * ProjGenLinGroup.mk (rationalPositiveGL2ToFinite γ) *
      finiteProjectiveReflectionElement⁻¹ = ProjGenLinGroup.mk
        (rationalPositiveGL2ToFinite (rationalPositiveReflection γ))
    rw [finiteProjectiveReflectionElement_inv, rationalPositiveReflection_finite, map_mul, map_mul]
    rfl

/-- Reflection carries every actual rational arithmetic element to an original rational arithmetic element. -/
theorem adelicProjectiveReflection_mem_arithmetic (γ : adelicProjectiveArithmetic) :
    adelicProjectiveReflection γ.val ∈ adelicProjectiveArithmetic := by
  obtain ⟨r, hr⟩ := γ.property
  exact ⟨rationalPositiveReflection r, by rw [← hr, adelicProjectiveReflection_rational]⟩

/-- The actual rational arithmetic subgroup is preserved by its genuine involutive reflection automorphism. -/
def adelicProjectiveArithmeticReflection : adelicProjectiveArithmetic ≃* adelicProjectiveArithmetic where
  toFun γ := ⟨adelicProjectiveReflection γ.val, adelicProjectiveReflection_mem_arithmetic γ⟩
  invFun γ := ⟨adelicProjectiveReflection γ.val, adelicProjectiveReflection_mem_arithmetic γ⟩
  left_inv γ := Subtype.ext (adelicProjectiveReflection_involutive γ.val)
  right_inv γ := Subtype.ext (adelicProjectiveReflection_involutive γ.val)
  map_mul' γ δ := Subtype.ext (map_mul adelicProjectiveReflection γ.val δ.val)

/-- The original involutive adelic reflection is precisely its continuous inverse. -/
theorem adelicProjectiveReflection_symm : adelicProjectiveReflection.symm = adelicProjectiveReflection := by
  apply ContinuousMulEquiv.ext
  intro p
  apply adelicProjectiveReflection.injective
  rw [ContinuousMulEquiv.apply_symm_apply, adelicProjectiveReflection_involutive]

/-- The genuine adelic projective reflection has exactly the original matrix conjugation formula on every pair of representatives. -/
theorem adelicProjectiveReflection_mk (r : SL(2, ℝ))
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicProjectiveReflection (QuotientGroup.mk r, ProjGenLinGroup.mk a) =
      (QuotientGroup.mk (realSL2Reflection r), ProjGenLinGroup.mk
        (rationalGL2ToFinite rationalGL2Reflection * a * rationalGL2ToFinite rationalGL2Reflection)) := by
  apply Prod.ext
  · rfl
  · change finiteProjectiveReflectionElement * ProjGenLinGroup.mk a *
      finiteProjectiveReflectionElement⁻¹ = _
    rw [finiteProjectiveReflectionElement_inv, map_mul, map_mul]
    rfl

end
end Dubon2026
