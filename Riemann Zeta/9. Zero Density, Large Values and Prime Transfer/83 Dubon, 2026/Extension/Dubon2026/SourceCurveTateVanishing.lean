import Dubon2026.SourceCurveLocalRetractionTrace
import Dubon2026.SourceCurveLocalTateDerivation

/-! The actual Tate pairing vanishes on two integral functions and on
a scalar second argument. These exact cases bound global support and
reduce shifted rational powers to their own coordinate. They are needed
for DUB-17/18 rational-field global residue vanishing. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open ResidueTrace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- Two actual integral functions have zero Tate residue. -/
theorem tateResidue_of_mem
    (hres : Function.Surjective (algebraMap K v.ResidueField)) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.tateResidue f g = 0 := by
  obtain ⟨_, htrace⟩ := v.tateResidue_integralRetraction hres f g
  rw [htrace]
  have he : projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F f) ∘ₗ
        projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F g) -
      projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F g) ∘ₗ
        projectedEnd v.integralFunctions (v.integralRetraction hres) (Algebra.lmul K F f) = 0 := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change v.tateProj (f * v.tateProj (g * (a : F))) -
      v.tateProj (g * v.tateProj (f * (a : F))) = 0
    rw [v.tateProj_of_mem (mul_mem hg a.2), v.tateProj_of_mem (mul_mem hf a.2),
      mul_left_comm f g, sub_self]
  rw [he, finrankTrace_zero]

/-- A constant second argument has zero residue, without any characteristic restriction. -/
theorem tateResidue_algebraMap
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f : F) (c : K) :
    v.tateResidue f (algebraMap K F c) = 0 := by
  have h := congrArg (fun φ : ResidueDual K F => residueDualLinearMap K F φ f)
    ((v.tateResidueDerivation hres).map_algebraMap c)
  exact h

/-- Adding a constant to the second argument does not change the residue. -/
theorem tateResidue_add_algebraMap
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f g : F) (c : K) :
    v.tateResidue f (g + algebraMap K F c) = v.tateResidue f g := by
  rw [v.tateResidue_add_snd hres, v.tateResidue_algebraMap hres, add_zero]

/-- The literal unit has zero differential residue. -/
theorem tateResidue_one
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f : F) :
    v.tateResidue f 1 = 0 := by
  simpa only [map_one] using v.tateResidue_algebraMap hres f 1

end Dubon2026.SourceCurve.Place
