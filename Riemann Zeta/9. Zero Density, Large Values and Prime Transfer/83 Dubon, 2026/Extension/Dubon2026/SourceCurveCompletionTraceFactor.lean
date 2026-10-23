import Dubon2026.SourceCurveCompletionRetraction
import Dubon2026.SourceCurveLocalRetractionTrace

/-! Factor the completed integral commutator through the original integral
space. The reverse composite is the original commutator. Cyclicity of the
proved finite-rank trace will then compare original and completed residues,
the local bridge required for DUB-17/18 global residue vanishing. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open ResidueTrace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The actual inclusion of original integral functions into the completed integral space. -/
def completionIntegralInclusion : v.integralFunctions →ₗ[K] v.completionPlace.integralFunctions :=
  (v.completionLinearMap ∘ₗ v.integralFunctions.subtype).codRestrict _
    (fun a => (v.completion_integer_iff a).mpr a.2)

/-- The finite principal-part factor of the completed commutator, with original integral output. -/
def completionCommutatorFactor
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f g : F) :
    v.completionPlace.integralFunctions →ₗ[K] v.integralFunctions :=
  v.integralRetraction hres ∘ₗ Algebra.lmul K F g ∘ₗ v.completionOriginalPrincipalPart ∘ₗ
    Algebra.lmul K v.adicCompletion (algebraMap F v.adicCompletion f) ∘ₗ
      v.completionPlace.integralFunctions.subtype

/-- The original integral commutator has its exact principal-part factorization. -/
theorem integral_commutator_principalPart
    (f g : F)
    (hg : g ∈ v.toValuationSubring) (a : v.integralFunctions) :
    v.tateProj (f * v.tateProj (g * (a : F))) -
      v.tateProj (g * v.tateProj (f * (a : F))) =
        v.tateProj (g * v.principalPart (f * (a : F))) := by
  have hga : g * (a : F) ∈ v.toValuationSubring := mul_mem hg a.2
  rw [v.tateProj_of_mem hga, ← map_sub]
  congr 1
  change f * (g * (a : F)) - g * (f * (a : F) - v.principalPart (f * (a : F))) = _
  ring

/-- The reverse composite of the completed factor is the literal original commutator. -/
theorem completionCommutatorFactor_comp_inclusion
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f g : F)
    (hg : g ∈ v.toValuationSubring) :
    v.completionCommutatorFactor hres f g ∘ₗ v.completionIntegralInclusion =
      projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F f) ∘ₗ
        projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F g) -
      projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F g) ∘ₗ
        projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F f) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change v.tateProj (g * v.completionOriginalPrincipalPart
    (algebraMap F v.adicCompletion f * algebraMap F v.adicCompletion (a : F))) = _
  rw [← map_mul, v.completionOriginalPrincipalPart_algebraMap]
  exact (v.integral_commutator_principalPart f g hg a).symm

/-- The completed commutator factors through actual original integral functions. -/
theorem inclusion_comp_completionCommutatorFactor
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f g : F)
    (hg : g ∈ v.toValuationSubring) :
    v.completionIntegralInclusion ∘ₗ v.completionCommutatorFactor hres f g =
      projectedEnd v.completionPlace.integralFunctions (v.completionOriginalRetraction hres)
          (Algebra.lmul K v.adicCompletion (algebraMap F v.adicCompletion f)) ∘ₗ
        projectedEnd v.completionPlace.integralFunctions (v.completionOriginalRetraction hres)
          (Algebra.lmul K v.adicCompletion (algebraMap F v.adicCompletion g)) -
      projectedEnd v.completionPlace.integralFunctions (v.completionOriginalRetraction hres)
          (Algebra.lmul K v.adicCompletion (algebraMap F v.adicCompletion g)) ∘ₗ
        projectedEnd v.completionPlace.integralFunctions (v.completionOriginalRetraction hres)
          (Algebra.lmul K v.adicCompletion (algebraMap F v.adicCompletion f)) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  let α := algebraMap F v.adicCompletion
  let Q := v.completionOriginalProjection
  have hga : α g * (a : v.adicCompletion) ∈ v.adicCompletionIntegers :=
    mul_mem ((v.completion_integer_iff g).mpr hg) a.2
  change α (v.tateProj (g * v.completionOriginalPrincipalPart (α f * (a : v.adicCompletion)))) =
    Q (α f * Q (α g * (a : v.adicCompletion))) -
      Q (α g * Q (α f * (a : v.adicCompletion)))
  rw [v.completionOriginalProjection_of_mem hga]
  rw [← map_sub]
  have he : α f * (α g * (a : v.adicCompletion)) -
      α g * Q (α f * (a : v.adicCompletion)) =
        α (g * v.completionOriginalPrincipalPart (α f * (a : v.adicCompletion))) := by
    change α f * (α g * (a : v.adicCompletion)) -
      α g * (α f * (a : v.adicCompletion) -
        α (v.completionOriginalPrincipalPart (α f * (a : v.adicCompletion)))) = _
    rw [map_mul α g (v.completionOriginalPrincipalPart (α f * (a : v.adicCompletion)))]
    ring
  rw [he]
  exact (v.completionOriginalProjection_algebraMap _).symm

end Dubon2026.SourceCurve.Place
