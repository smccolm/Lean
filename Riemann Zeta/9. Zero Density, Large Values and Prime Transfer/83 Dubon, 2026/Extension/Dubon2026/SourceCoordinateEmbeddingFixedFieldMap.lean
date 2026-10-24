import Dubon2026.SourceCoordinateEmbeddingFixingField

/-! Every actual coordinate-preserving embedding lands in the constructed
normal fixed field. Its rational coordinate is retained literally. This
is the field inclusion used in the DUB-17/18 wild order-divisibility chain. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F M : Type*} [Field K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M]
variable [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]

/-- Restrict the actual embedding to the fixed field containing all its values. -/
def coordinateEmbeddingIntoFixingField (x : F) (ψ : F →ₐ[K] M)
    (hψ : ψ x = algebraMap (RatFunc K) M RatFunc.X) :
    F →ₐ[K] coordinateEmbeddingFixingField (K := K) (M := M) x where
  toFun a := ⟨ψ a, coordinateEmbedding_value_mem_fixingField x ψ hψ a⟩
  map_one' := Subtype.ext (map_one ψ)
  map_mul' := fun a b => Subtype.ext (map_mul ψ a b)
  map_zero' := Subtype.ext (map_zero ψ)
  map_add' := fun a b => Subtype.ext (map_add ψ a b)
  commutes' := fun a => Subtype.ext (ψ.commutes a)

theorem coordinateEmbeddingIntoFixingField_coordinate (x : F) (ψ : F →ₐ[K] M)
    (hψ : ψ x = algebraMap (RatFunc K) M RatFunc.X) :
    coordinateEmbeddingIntoFixingField x ψ hψ x =
      algebraMap (RatFunc K) (coordinateEmbeddingFixingField (K := K) (M := M) x) RatFunc.X :=
  Subtype.ext hψ

end
end Dubon2026.SourceCurve
