import Dubon2026.SupportedOutsideOrbitCohomology
import Dubon2026.OriginalAdicUniformizerOrder

/-! # The faithful original completion action outside the support

The original stabilizer acts through the already proved completed field
maps. Their original valuation identity preserves the original norm.
These are the fixed-field local hypotheses needed to discharge the last
outside-support H1/H2 assumptions in DUB-17's idele-class formula.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The exact outside-support orbit stabilizer acts on its original completed field. -/
@[reducible]
def supportedOutsideOrbitFieldAction :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      MulSemiringAction
        (MulAction.stabilizer Gal(L/K)
          (permutationOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω))
        (ω.out.val.adicCompletion L) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := supportedOutsidePlaceAction K L S hS
  intro ω
  exact {
    smul σ x := numberFieldGaloisLocalTransport K L σ.val ω.out.val ω.out.val
      (congrArg (fun z => z.val.val) σ.property) x
    one_smul x := numberFieldGaloisLocalTransport_one K L ω.out.val x
    mul_smul σ τ x := numberFieldGaloisLocalTransport_mul K L σ.val τ.val
      ω.out.val ω.out.val ω.out.val
      (congrArg (fun z => z.val.val) τ.property)
      (congrArg (fun z => z.val.val) σ.property)
      (congrArg (fun z => z.val.val) (σ * τ).property) x
    smul_zero σ := map_zero _
    smul_add σ := map_add _
    smul_one σ := map_one _
    smul_mul σ := map_mul _ }

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The outside-support stabilizer action on the original completion is faithful. -/
theorem supportedOutsideOrbitField_faithful :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      letI := supportedOutsideOrbitFieldAction K L S hS ω
      FaithfulSMul
        (MulAction.stabilizer Gal(L/K)
          (permutationOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω))
        (ω.out.val.adicCompletion L) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := supportedOutsidePlaceAction K L S hS
  intro ω
  letI := supportedOutsideOrbitFieldAction K L S hS ω
  change FaithfulSMul
    (MulAction.stabilizer Gal(L/K)
      (permutationOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω))
    (ω.out.val.adicCompletion L)
  refine ⟨?_⟩
  intro σ τ he
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L (ω.out.val.adicCompletion L)).injective
  have h := he (algebraMap L (ω.out.val.adicCompletion L) x)
  change numberFieldGaloisLocalTransport K L σ.val ω.out.val ω.out.val
      (congrArg (fun z => z.val.val) σ.property) (algebraMap L (ω.out.val.adicCompletion L) x) =
    numberFieldGaloisLocalTransport K L τ.val ω.out.val ω.out.val
      (congrArg (fun z => z.val.val) τ.property) (algebraMap L (ω.out.val.adicCompletion L) x) at h
  simpa only [numberFieldGaloisLocalTransport_algebraMap] using h

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The outside-support stabilizer action preserves the original completion norm. -/
theorem supportedOutsideOrbitField_norm :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      letI := supportedOutsideOrbitFieldAction K L S hS ω
      ∀ (σ : MulAction.stabilizer Gal(L/K)
          (permutationOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω))
        (x : ω.out.val.adicCompletion L), ‖σ • x‖ = ‖x‖ := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := supportedOutsidePlaceAction K L S hS
  intro ω
  letI := supportedOutsideOrbitFieldAction K L S hS ω
  change ∀ (σ : MulAction.stabilizer Gal(L/K)
    (permutationOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω))
    (x : ω.out.val.adicCompletion L), ‖σ • x‖ = ‖x‖
  intro σ x
  change ‖numberFieldGaloisLocalTransport K L σ.val ω.out.val ω.out.val _ x‖ = ‖x‖
  simp only [Valued.toNormedField.norm_def]
  rw [(Valued.v.restrict_inj).mpr
    (numberFieldGaloisLocalTransport_valuation K L σ.val ω.out.val ω.out.val _ x)]

end
end Dubon2026
