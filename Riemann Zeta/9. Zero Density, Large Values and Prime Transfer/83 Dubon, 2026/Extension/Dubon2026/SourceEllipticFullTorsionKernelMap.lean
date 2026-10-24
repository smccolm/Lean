import Dubon2026.SourceEllipticCyclicTorsionSpecialization
import Dubon2026.SourceEllipticCyclicRootBaseChange

/-! The finite Galois field in the actual specialization is not algebraically
closed. Its proved full N-squared torsion count nevertheless identifies all
cyclic kernels with those over an algebraic closure. Reuse the existing
torsion specialization equivalence to remove this obstacle before descending
the actual modular roots for the DUB-17/18 place-fiber comparison. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticReduction SourceEllipticCyclicCount
open SourceFunctionField.IntegralJCoordinate SourceEllipticVariableChange
open OddDiscriminant
noncomputable section

theorem cyclicKernelMap_bijective_of_full_torsion
    {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L] [IsAlgClosed L]
    (f : F →+* L) (W : WeierstrassCurve F) [W.IsElliptic]
    (N : ℕ) (hN : (N : F) ≠ 0)
    (hcard : Nat.card {P : W.toAffine.Point // N • P = 0} = N ^ 2) :
    Function.Bijective (primeCyclicKernelMap f W N) := by
  let A := Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ)
  let ι := A.subtype.toAddMonoidHom
  let θ := (pointMapHom f W).comp ι
  have hθ : Function.Injective θ := (pointMapHom_injective f W).comp Subtype.val_injective
  have hNL : (N : L) ≠ 0 := by simpa only [map_natCast] using (_root_.map_ne_zero f).mpr hN
  let e := ellipticCyclicSpecializationEquiv (W.map f) N hNL θ hθ hcard
  have he : (e : _ → _) = primeCyclicKernelMap f W N := by
    funext S
    apply Subtype.ext
    change (S.val.comap ι).map ((pointMapHom f W).comp ι) = S.val.map (pointMapHom f W)
    rw [← AddSubgroup.map_map]
    have hr : S.val ≤ ι.range := by
      apply le_of_card_eq_of_nsmul_mem N S.property.2
      intro P hP
      exact ⟨⟨P, by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using hP⟩, rfl⟩
    rw [AddSubgroup.map_comap_eq_self hr]
  rw [← he]
  exact e.bijective

end
end Dubon2026.SourceEllipticVelu
