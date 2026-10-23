import Dubon2026.SourceCurveTateUniformizerProjection
import Dubon2026.SourceCurveTateCommutatorFinite
import Dubon2026.SourceCurveFiniteRankTraceOne

/-! Exact agreement of the local finite-rank commutator trace with the
existing normalized residue for the chosen uniformizer. Multiplication by
the uniformizer makes the commutator a rank-one operator, whose trace is
the simple-pole coefficient. This is the local agreement input to the
residue/trace comparison needed for the reverse modular genus bound. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open ResidueTrace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The actual uniformizer commutator sends an integral input to its scalar residue. -/
theorem tateComm_uniformizer_apply
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f : F)
    (a : LinearMap.range v.tateProj) :
    (tateCommRestrict v.tateProj (Algebra.lmul K F f)
      (Algebra.lmul K F v.uniformizer) a : F) =
      algebraMap K F (v.localResidueScalar (f * (a : F))) := by
  have ha : (a : F) ∈ v.toValuationSubring := (v.range_tateProj hres).le a.2
  have hua : v.uniformizer * (a : F) ∈ v.toValuationSubring :=
    mul_mem v.uniformizerSubring.property ha
  have hcomm : Algebra.lmul K F f ∘ₗ Algebra.lmul K F v.uniformizer =
      Algebra.lmul K F v.uniformizer ∘ₗ Algebra.lmul K F f := by
    ext x
    change f * (v.uniformizer * x) = v.uniformizer * (f * x)
    ring
  rw [tateCommRestrict_apply, tateComm_eq_of_commute hcomm]
  change v.tateProj (v.uniformizer * (f * (a : F) - v.tateProj (f * (a : F)))) -
    v.tateProj (f * (v.uniformizer * (a : F) - v.tateProj (v.uniformizer * (a : F)))) = _
  rw [v.tateProj_of_mem hua, sub_self, mul_zero, map_zero, sub_zero]
  have h : f * (a : F) - v.tateProj (f * (a : F)) = v.principalPart (f * (a : F)) := by
    change f * (a : F) - (f * (a : F) - v.principalPart (f * (a : F))) = _
    abel
  rw [h, v.tateProj_uniformizer_mul_principalPart]

/-- The local Tate trace has exactly the existing simple-pole residue normalization. -/
theorem tateResidue_uniformizer
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f : F) :
    v.tateResidue f v.uniformizer = v.localResidueScalar f := by
  let A := LinearMap.range v.tateProj
  let χ : A →ₗ[K] K :=
    v.localResidueScalar ∘ₗ Algebra.lmul K F f ∘ₗ A.subtype
  let e : A := ⟨1, (v.range_tateProj hres).symm.le (one_mem v.toValuationSubring)⟩
  have h : tateCommRestrict v.tateProj (Algebra.lmul K F f)
      (Algebra.lmul K F v.uniformizer) = χ.smulRight e := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    rw [v.tateComm_uniformizer_apply hres]
    change algebraMap K F (v.localResidueScalar (f * (a : F))) =
      v.localResidueScalar (f * (a : F)) • (1 : F)
    rw [Algebra.smul_def, mul_one]
  change finrankTrace (tateCommRestrict v.tateProj (Algebra.lmul K F f)
    (Algebra.lmul K F v.uniformizer)) = _
  rw [h, finrankTrace_smulRight]
  change v.localResidueScalar (f * 1) = v.localResidueScalar f
  rw [mul_one]

end Dubon2026.SourceCurve.Place
