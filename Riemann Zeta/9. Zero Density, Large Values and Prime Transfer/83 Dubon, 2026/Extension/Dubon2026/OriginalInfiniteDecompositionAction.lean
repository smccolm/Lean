import Dubon2026.OriginalInfiniteCompletionFixedDescent
import Mathlib.FieldTheory.Fixed

/-! # Actual original archimedean decomposition groups on original completions

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
variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- The stabilizer of the actual original upper infinite place under the actual Galois action. -/
abbrev OriginalInfiniteDecompositionGroup (w : InfinitePlace L) :=
  MulAction.stabilizer Gal(L/K) w

/-- The actual original decomposition group acts on the actual original completion by its completed transports. -/
@[reducible]
def originalInfiniteDecompositionAction (w : InfinitePlace L) :
    MulSemiringAction (OriginalInfiniteDecompositionGroup K L w) (w.Completion) where
  smul σ x := numberFieldGaloisArchimedeanTransport K L σ.val w w σ.property x
  one_smul := numberFieldGaloisArchimedeanTransport_one K L w
  mul_smul σ τ := numberFieldGaloisArchimedeanTransport_mul K L σ.val τ.val w w w
    τ.property σ.property (σ * τ).property
  smul_zero _ := map_zero _
  smul_add _ := map_add _
  smul_one _ := map_one _
  smul_mul _ := map_mul _

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Faithfulness on the original completion follows from faithfulness on its embedded original field. -/
theorem originalInfiniteDecompositionAction_faithful (w : InfinitePlace L) :
    letI := originalInfiniteDecompositionAction K L w
    FaithfulSMul (OriginalInfiniteDecompositionGroup K L w) (w.Completion) := by
  letI := originalInfiniteDecompositionAction K L w
  refine ⟨?_⟩
  intro σ τ h
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L (w.Completion)).injective
  have hx := h (algebraMap L (w.Completion) x)
  change numberFieldGaloisArchimedeanTransport K L σ.val w w _ (algebraMap L (w.Completion) x) =
    numberFieldGaloisArchimedeanTransport K L τ.val w w _ (algebraMap L (w.Completion) x) at hx
  simpa only [numberFieldGaloisArchimedeanTransport_algebraMap] using hx

variable [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
  (w : InfinitePlace L)

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual base completion is ring-equivalent to the fixed subfield of the actual original decomposition action. -/
def originalInfiniteCompletionBaseFixedEquiv :
    letI := originalInfiniteDecompositionAction K L w
    (w.comap (algebraMap K L)).Completion ≃+* FixedPoints.subfield (OriginalInfiniteDecompositionGroup K L w) (w.Completion) := by
  letI := originalInfiniteDecompositionAction K L w
  let f : (w.comap (algebraMap K L)).Completion →+*
      FixedPoints.subfield (OriginalInfiniteDecompositionGroup K L w) (w.Completion) := {
    toFun := fun x => ⟨originalInfiniteCompletionBaseChange K L w x,
      fun σ => originalInfiniteCompletionBaseChange_fixed K L w σ.val σ.property x⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' x y := Subtype.ext (map_mul _ x y)
    map_zero' := Subtype.ext (map_zero _)
    map_add' x y := Subtype.ext (map_add _ x y) }
  apply RingEquiv.ofBijective f
  constructor
  · intro x y h
    exact (originalInfiniteCompletionBaseChange K L w).injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨a, ha⟩ := originalInfiniteCompletionBaseChange_surjective_fixed K L w x.val
      (fun σ hσ => x.property ⟨σ, hσ⟩)
    exact ⟨a, Subtype.ext ha⟩

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The fixed-field comparison preserves the actual original completed base embedding literally. -/
theorem originalInfiniteCompletionBaseFixedEquiv_val (x : (w.comap (algebraMap K L)).Completion) :
    (originalInfiniteCompletionBaseFixedEquiv K L w x).val = originalInfiniteCompletionBaseChange K L w x := rfl

end
end Dubon2026
