import Dubon2026.SourceRationalCoordinateEmbeddingAction
import Mathlib.FieldTheory.Galois.Basic

/-! The fixed field of the actual coordinate-embedding action contains
all original embedding values and is normal over the rational coordinate
field. Native permutation kernels supply this exact auxiliary field for
the DUB-17/18 characteristic-three order-dividing-six argument. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F M : Type*} [Field K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M]
variable [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]

/-- The already defined coordinate action, regarded as a permutation homomorphism. -/
def coordinateEmbeddingPermHom (x : F) : (M ≃ₐ[RatFunc K] M) →*
    Equiv.Perm {ψ : F →ₐ[K] M // ψ x = algebraMap (RatFunc K) M RatFunc.X} :=
  letI := coordinateEmbeddingAction (K := K) (M := M) x
  MulAction.toPermHom _ _

/-- The actual fixed field of the kernel of coordinate-preserving embeddings. -/
def coordinateEmbeddingFixingField (x : F) : IntermediateField (RatFunc K) M :=
  IntermediateField.fixedField (coordinateEmbeddingPermHom (K := K) (M := M) x).ker

theorem mem_coordinateEmbeddingPermHom_ker_iff (x : F) (σ : M ≃ₐ[RatFunc K] M) :
    σ ∈ (coordinateEmbeddingPermHom (K := K) (M := M) x).ker ↔
      ∀ ψ : F →ₐ[K] M, ψ x = algebraMap (RatFunc K) M RatFunc.X →
        (σ.toAlgHom.restrictScalars K).comp ψ = ψ := by
  constructor
  · intro h ψ hψ
    exact congrArg (fun e => (e ⟨ψ, hψ⟩).val)
      (show coordinateEmbeddingPermHom (K := K) x σ = 1 from h)
  · intro h
    change coordinateEmbeddingPermHom (K := K) x σ = 1
    apply Equiv.ext
    intro ψ
    exact Subtype.ext (h ψ.val ψ.property)

theorem coordinateEmbedding_value_mem_fixingField (x : F) (ψ : F →ₐ[K] M)
    (hψ : ψ x = algebraMap (RatFunc K) M RatFunc.X) (a : F) :
    ψ a ∈ coordinateEmbeddingFixingField (K := K) (M := M) x := by
  rw [coordinateEmbeddingFixingField, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  exact congrArg (fun f : F →ₐ[K] M => f a)
    ((mem_coordinateEmbeddingPermHom_ker_iff x σ).mp hσ ψ hψ)

theorem coordinateEmbedding_fixingField_fixed (x : F) (σ : M ≃ₐ[RatFunc K] M)
    (hσ : ∀ ψ : F →ₐ[K] M, ψ x = algebraMap (RatFunc K) M RatFunc.X →
      (σ.toAlgHom.restrictScalars K).comp ψ = ψ)
    (a : coordinateEmbeddingFixingField (K := K) (M := M) x) : σ (a : M) = a :=
  (IntermediateField.mem_fixedField_iff _ a.val).mp a.property σ
    ((mem_coordinateEmbeddingPermHom_ker_iff x σ).mpr hσ)

theorem coordinateEmbedding_fixingField_isGalois [IsGalois (RatFunc K) M] (x : F) :
    IsGalois (RatFunc K) (coordinateEmbeddingFixingField (K := K) (M := M) x) :=
  IsGalois.of_fixedField_normal_subgroup (coordinateEmbeddingPermHom (K := K) (M := M) x).ker

end
end Dubon2026.SourceCurve
