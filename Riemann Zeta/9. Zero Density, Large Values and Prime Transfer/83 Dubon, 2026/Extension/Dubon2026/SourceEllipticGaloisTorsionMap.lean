import Dubon2026.SourceEllipticTorsionReductionHom

/-! Restrict the original field action to the actual N-torsion group.
This is the original-action input in the inertia-equivariance consumer
for the DUB-17/18 positive-characteristic exceptional-fiber census. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
variable {F M : Type*} [Field F] [Field M] [Algebra F M] [DecidableEq M]

/-- The original automorphism acts on the actual torsion through the native point map. -/
def galoisTorsionMap (E : WeierstrassCurve F) (N : ℕ) (σ : M ≃ₐ[F] M) :
    Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) →+
      Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) where
  toFun P := ⟨Point.map (σ : M →ₐ[F] M) P, by
    have hP : (N : ℤ) • (P : (E.baseChange M).toAffine.Point) = 0 := by
      simpa only [Submodule.mem_torsionBy_iff] using P.property
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hP, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext ((Point.map (σ : M →ₐ[F] M)).map_add P.val Q.val)

theorem galoisTorsionMap_apply (E : WeierstrassCurve F) (N : ℕ) (σ : M ≃ₐ[F] M)
    (P : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ)) :
    (galoisTorsionMap E N σ P : (E.baseChange M).toAffine.Point) =
      Point.map (σ : M →ₐ[F] M) P := rfl

end
end Dubon2026.SourceEllipticReduction
