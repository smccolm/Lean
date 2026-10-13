import Dubon2026.OriginalAdicFixedFieldDescent
import Mathlib.FieldTheory.Fixed

/-! # Actual original finite decomposition groups on original completions

The original prime stabilizer acts faithfully by the already proved
completed Galois transports. Its fixed subfield is identified with the
actual base completion. This is the local field comparison needed to
prove the component formula for the descended original idele norm, then
the norm-index upper bound on DUB-17's reciprocity/global duality chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The stabilizer of the actual original upper finite prime under the actual Galois action. -/
abbrev OriginalFiniteDecompositionGroup (w : HeightOneSpectrum (𝓞 L)) :=
  letI := numberFieldGaloisPlaceAction K L
  MulAction.stabilizer Gal(L/K) w

/-- The actual original decomposition group acts on the actual original completion by its completed transports. -/
@[reducible]
def originalAdicDecompositionAction (w : HeightOneSpectrum (𝓞 L)) :
    MulSemiringAction (OriginalFiniteDecompositionGroup K L w) (w.adicCompletion L) where
  smul σ x := numberFieldGaloisLocalTransport K L σ.val w w σ.property x
  one_smul := numberFieldGaloisLocalTransport_one K L w
  mul_smul σ τ := numberFieldGaloisLocalTransport_mul K L σ.val τ.val w w w
    τ.property σ.property (σ * τ).property
  smul_zero _ := map_zero _
  smul_add _ := map_add _
  smul_one _ := map_one _
  smul_mul _ := map_mul _

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Faithfulness on the original completion follows from faithfulness on its embedded original field. -/
theorem originalAdicDecompositionAction_faithful (w : HeightOneSpectrum (𝓞 L)) :
    letI := originalAdicDecompositionAction K L w
    FaithfulSMul (OriginalFiniteDecompositionGroup K L w) (w.adicCompletion L) := by
  letI := originalAdicDecompositionAction K L w
  refine ⟨?_⟩
  intro σ τ h
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L (w.adicCompletion L)).injective
  have hx := h (algebraMap L (w.adicCompletion L) x)
  change numberFieldGaloisLocalTransport K L σ.val w w _ (algebraMap L (w.adicCompletion L) x) =
    numberFieldGaloisLocalTransport K L τ.val w w _ (algebraMap L (w.adicCompletion L) x) at hx
  simpa only [numberFieldGaloisLocalTransport_algebraMap] using hx

variable [NumberField K] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual base completion is ring-equivalent to the fixed subfield of the actual original decomposition action. -/
def originalAdicBaseFixedEquiv :
    letI := originalAdicDecompositionAction K L w
    v.adicCompletion K ≃+* FixedPoints.subfield (OriginalFiniteDecompositionGroup K L w) (w.adicCompletion L) := by
  letI := originalAdicDecompositionAction K L w
  let f : v.adicCompletion K →+*
      FixedPoints.subfield (OriginalFiniteDecompositionGroup K L w) (w.adicCompletion L) := {
    toFun := fun x => ⟨originalAdicBaseChangeMap K L v w x,
      fun σ => originalAdicBaseChangeMap_fixed K L v w σ.val σ.property x⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' x y := Subtype.ext (map_mul _ x y)
    map_zero' := Subtype.ext (map_zero _)
    map_add' x y := Subtype.ext (map_add _ x y) }
  apply RingEquiv.ofBijective f
  constructor
  · intro x y h
    exact (originalAdicBaseChangeMap K L v w).injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨a, ha⟩ := originalAdicBaseChangeMap_surjective_fixed K L v w x.val
      (fun σ hσ => x.property ⟨σ, hσ⟩)
    exact ⟨a, Subtype.ext ha⟩

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The fixed-field comparison preserves the actual original completed base embedding literally. -/
theorem originalAdicBaseFixedEquiv_val (x : v.adicCompletion K) :
    (originalAdicBaseFixedEquiv K L v w x).val = originalAdicBaseChangeMap K L v w x := rfl

end
end Dubon2026
