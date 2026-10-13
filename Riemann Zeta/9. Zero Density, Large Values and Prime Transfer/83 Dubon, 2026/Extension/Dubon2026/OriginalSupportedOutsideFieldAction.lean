import Dubon2026.OriginalTransportedOrbitH2
import Dubon2026.SupportedOutsideUnitRepresentation
import Dubon2026.OriginalAdicUniformizerOrder

/-! # Actual outside-support stabilizers for arbitrary finite Galois groups

The original transports already define these actions for arbitrary groups.
Their faithfulness and norm preservation allow unramified local vanishing
without assuming the entire Galois group cyclic. This discharges the local
input to global H2 detection on DUB-17's invariant sum-zero dependency.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual integer-unit coefficient at an original outside-support orbit representative. -/
def originalOutsideOrbitPointRep :
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      Rep ℤ (MulAction.stabilizer Gal(L/K)
        (originalOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω)) := by
  letI := supportedOutsidePlaceAction K L S hS
  intro ω
  exact transportedOrbitPointRep ℤ Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S}
    (fun v => Additive (v.val.adicCompletionIntegers L)ˣ)
    (supportedOutsideUnitTransport K L S hS)
    (supportedOutsideUnitTransport_one K L S hS)
    (supportedOutsideUnitTransport_mul K L S hS) ω
    (originalOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω)

/-- The exact outside-support orbit stabilizer acts on its original completed field. -/
@[reducible]
def originalOutsideOrbitFieldAction :
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      MulSemiringAction
        (MulAction.stabilizer Gal(L/K)
          (originalOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω))
        (ω.out.val.adicCompletion L) := by
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
theorem originalOutsideOrbitField_faithful :
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      letI := originalOutsideOrbitFieldAction K L S hS ω
      FaithfulSMul
        (MulAction.stabilizer Gal(L/K)
          (originalOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω))
        (ω.out.val.adicCompletion L) := by
  letI := supportedOutsidePlaceAction K L S hS
  intro ω
  letI := originalOutsideOrbitFieldAction K L S hS ω
  change FaithfulSMul
    (MulAction.stabilizer Gal(L/K)
      (originalOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω))
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
theorem originalOutsideOrbitField_norm :
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      letI := originalOutsideOrbitFieldAction K L S hS ω
      ∀ (σ : MulAction.stabilizer Gal(L/K)
          (originalOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω))
        (x : ω.out.val.adicCompletion L), ‖σ • x‖ = ‖x‖ := by
  letI := supportedOutsidePlaceAction K L S hS
  intro ω
  letI := originalOutsideOrbitFieldAction K L S hS ω
  change ∀ (σ : MulAction.stabilizer Gal(L/K)
    (originalOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω))
    (x : ω.out.val.adicCompletion L), ‖σ • x‖ = ‖x‖
  intro σ x
  change ‖numberFieldGaloisLocalTransport K L σ.val ω.out.val ω.out.val _ x‖ = ‖x‖
  simp only [Valued.toNormedField.norm_def]
  rw [(Valued.v.restrict_inj).mpr
    (numberFieldGaloisLocalTransport_valuation K L σ.val ω.out.val ω.out.val _ x)]

end
end Dubon2026
