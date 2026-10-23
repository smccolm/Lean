import Dubon2026.SourceCurvePoleProjection
import Dubon2026.SourceCurveTateCommutator

/-! The local finite-rank input to the residue/trace comparison is now proved
at every rational place. Bounded principal parts lie in a finite span of pure
poles. No completion, coefficient section or finite-rank premise is supplied
to the final commutator theorem. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open LinearMap Submodule ResidueTrace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- Multiplication of integral functions has a finite-dimensional principal-part image. -/
theorem finite_range_principalPart_mul
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f : F) :
    FiniteDimensional K (LinearMap.range
      ((LinearMap.id - v.tateProj) ∘ₗ Algebra.lmul K F f ∘ₗ (LinearMap.range v.tateProj).subtype)) := by
  let n := (-v.ord f).toNat
  let S := Submodule.span K (v.poleClass '' Set.Iio n)
  haveI : FiniteDimensional K S :=
    FiniteDimensional.span_of_finite K ((Set.finite_Iio n).image v.poleClass)
  haveI : FiniteDimensional K (S.map v.principalPartLift) := Module.Finite.map _ _
  refine Submodule.finiteDimensional_of_le (S₂ := S.map v.principalPartLift) ?_
  rintro y ⟨a, rfl⟩
  have ha : (a : F) ∈ v.toValuationSubring := (v.range_tateProj hres).le a.2
  have hfa : v.uniformizer ^ n * (f * (a : F)) ∈ v.toValuationSubring := by
    rw [← mul_assoc]
    exact mul_mem (v.clear_pole_mem f) ha
  refine ⟨v.integralFunctions.mkQ (f * (a : F)),
    v.poleClass_mem_span_of_clear_pole hres n _ hfa, ?_⟩
  change v.principalPart (f * (a : F)) =
    f * (a : F) - (f * (a : F) - v.principalPart (f * (a : F)))
  abel

/-- The actual local projected commutator has finite rank for every pair of field elements. -/
theorem finite_range_tate_commutator
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f g : F) :
    FiniteDimensional K (LinearMap.range
      (tateCommRestrict v.tateProj (Algebra.lmul K F f) (Algebra.lmul K F g))) := by
  haveI := v.finite_range_principalPart_mul hres f
  haveI := v.finite_range_principalPart_mul hres g
  apply finite_range_tateCommRestrict
  ext x
  change f * (g * x) = g * (f * x)
  ring

/-- The scalar Tate residue defined by the actual finite-rank commutator at a rational place. -/
def tateResidue (f g : F) : K :=
  tateCommTrace v.tateProj (Algebra.lmul K F f) (Algebra.lmul K F g)

end Dubon2026.SourceCurve.Place
