import Dubon2026.SourceCurveRetractionTrace
import Dubon2026.SourceCurveTateCommutatorFinite

/-! The canonical local Tate trace can be computed using any retraction
onto the actual integral functions when the second multiplier is integral.
This is the exact change-of-projector input for an integral-basis proof of
residue/trace compatibility. All finite-image premises are derived here. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open ResidueTrace LinearMap

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The canonical integral projection with its actual integral subspace as codomain. -/
def integralRetraction (hres : Function.Surjective (algebraMap K v.ResidueField)) :
    F →ₗ[K] v.integralFunctions := v.tateProj.codRestrict _ (v.tateProj_mem hres)

/-- The canonical retraction fixes every integral function. -/
theorem integralRetraction_apply (hres : Function.Surjective (algebraMap K v.ResidueField))
    (a : v.integralFunctions) : v.integralRetraction hres a = a :=
  Subtype.ext (v.tateProj_of_mem a.2)

/-- Principal parts remain finite-dimensional after choosing the literal integral codomain. -/
theorem finite_range_integralRetraction_principalPart
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f : F) :
    FiniteDimensional K (LinearMap.range
      ((LinearMap.id - v.integralFunctions.subtype ∘ₗ v.integralRetraction hres) ∘ₗ
        Algebra.lmul K F f ∘ₗ v.integralFunctions.subtype)) := by
  haveI := v.finite_range_principalPart_mul hres f
  have he : LinearMap.range
      ((LinearMap.id - v.integralFunctions.subtype ∘ₗ v.integralRetraction hres) ∘ₗ
        Algebra.lmul K F f ∘ₗ v.integralFunctions.subtype) =
      LinearMap.range ((LinearMap.id - v.tateProj) ∘ₗ Algebra.lmul K F f ∘ₗ
        (LinearMap.range v.tateProj).subtype) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a, (v.range_tateProj hres).symm.le a.2⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a, (v.range_tateProj hres).le a.2⟩, rfl⟩
  rw [he]
  infer_instance

/-- The literal Tate trace is the commutator trace on the actual integral subspace. -/
theorem tateResidue_integralRetraction
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f g : F) :
    FiniteDimensional K (LinearMap.range
      (projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F f) ∘ₗ
          projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F g) -
        projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F g) ∘ₗ
          projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F f))) ∧
    v.tateResidue f g = finrankTrace
      (projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F f) ∘ₗ
          projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F g) -
        projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F g) ∘ₗ
          projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F f)) := by
  let e := LinearEquiv.ofEq (LinearMap.range v.tateProj) v.integralFunctions (v.range_tateProj hres)
  let T := tateCommRestrict v.tateProj (Algebra.lmul K F f) (Algebra.lmul K F g)
  haveI : FiniteDimensional K (LinearMap.range T) := v.finite_range_tate_commutator hres f g
  haveI : FiniteDimensional K (LinearMap.range (e.conj T)) := by
    rw [range_conj_eq_map]
    exact Module.Finite.map _ _
  have he : e.conj T =
      projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F f) ∘ₗ
          projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F g) -
        projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F g) ∘ₗ
          projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F f) := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    rfl
  refine ⟨he ▸ (inferInstance : FiniteDimensional K (LinearMap.range (e.conj T))), ?_⟩
  rw [← he, finrankTrace_conj]
  rfl

/-- Any actual integral retraction computes the same local residue for an integral second factor. -/
theorem tateResidue_eq_retraction_trace
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    (s : F →ₗ[K] v.integralFunctions) (hs : ∀ a : v.integralFunctions, s a = a)
    (f g : F) (hg : g ∈ v.toValuationSubring) :
    FiniteDimensional K (LinearMap.range
      (projectedEnd v.integralFunctions s (Algebra.lmul K F f) ∘ₗ
          projectedEnd v.integralFunctions s (Algebra.lmul K F g) -
        projectedEnd v.integralFunctions s (Algebra.lmul K F g) ∘ₗ
          projectedEnd v.integralFunctions s (Algebra.lmul K F f))) ∧
    v.tateResidue f g = finrankTrace
      (projectedEnd v.integralFunctions s (Algebra.lmul K F f) ∘ₗ
          projectedEnd v.integralFunctions s (Algebra.lmul K F g) -
        projectedEnd v.integralFunctions s (Algebra.lmul K F g) ∘ₗ
          projectedEnd v.integralFunctions s (Algebra.lmul K F f)) := by
  obtain ⟨hfin, htrace⟩ := v.tateResidue_integralRetraction hres f g
  haveI := hfin
  haveI := v.finite_range_integralRetraction_principalPart hres f
  obtain ⟨hsfin, he⟩ := retraction_commutator_trace v.integralFunctions
    (v.integralRetraction hres) s (v.integralRetraction_apply hres) hs
    (Algebra.lmul K F f) (Algebra.lmul K F g)
    (fun x ha => (show g * x ∈ v.toValuationSubring from mul_mem hg ha))
  exact ⟨hsfin, htrace.trans he⟩

end Dubon2026.SourceCurve.Place
