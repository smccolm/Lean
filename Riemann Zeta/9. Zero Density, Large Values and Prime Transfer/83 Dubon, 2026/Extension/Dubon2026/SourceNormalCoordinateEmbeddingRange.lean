import Dubon2026.SourceRationalCoordinateEmbeddingTower
import Mathlib.FieldTheory.Normal.Basic

/-! A coordinate-preserving embedding of the actual normal intermediate
field lands in that same field. Native normal-field range and the existing
rational-coordinate extensionality give the exact DUB-17/18 wild-order input. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K M : Type*} [Field K] [Field M]
variable [Algebra K M] [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]

theorem normal_coordinate_embedding_mem (L : IntermediateField (RatFunc K) M)
    [Normal (RatFunc K) L] (ψ : L →ₐ[K] M)
    (hψ : ψ (algebraMap (RatFunc K) L RatFunc.X) = algebraMap (RatFunc K) M RatFunc.X)
    (a : L) : ψ a ∈ L := by
  have hc : ψ.comp (IsScalarTower.toAlgHom K (RatFunc K) L) =
      IsScalarTower.toAlgHom K (RatFunc K) M := ratFunc_algHom_ext _ _ hψ
  let f : L →ₐ[RatFunc K] M :=
    { ψ.toRingHom with
      commutes' := fun c => congrArg (fun e : RatFunc K →ₐ[K] M => e c) hc }
  have ha : ψ a ∈ f.fieldRange := ⟨a, rfl⟩
  rwa [AlgHom.fieldRange_of_normal (E := L) f] at ha

end
end Dubon2026.SourceCurve
