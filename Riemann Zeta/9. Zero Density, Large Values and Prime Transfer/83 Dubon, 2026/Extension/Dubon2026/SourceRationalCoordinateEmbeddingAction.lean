import Dubon2026.SourceRationalCoordinatePlaceOrbits
import Mathlib.GroupTheory.Index

/-! DUB-17/18 -> reverse genus -> normalized exceptional-fiber counts.
Postcomposition acts on the actual embeddings preserving the fixed
rational coordinate. The action restricts to the actual inertia group;
its stabilizer will be identified with the upper decomposition group. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F M : Type*} [Field K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M]
variable [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]

/-- Postcomposition on literal embeddings at the rational coordinate. -/
@[reducible]
def coordinateEmbeddingAction (x : F) : MulAction (M ≃ₐ[RatFunc K] M)
    {ψ : F →ₐ[K] M // ψ x = algebraMap (RatFunc K) M RatFunc.X} where
  smul σ ψ := ⟨(σ.toAlgHom.restrictScalars K).comp ψ.val, by
    change σ (ψ.val x) = _
    rw [ψ.property, σ.commutes]⟩
  one_smul ψ := Subtype.ext (AlgHom.ext fun _ => rfl)
  mul_smul σ τ ψ := Subtype.ext (AlgHom.ext fun _ => rfl)

end
end Dubon2026.SourceCurve
