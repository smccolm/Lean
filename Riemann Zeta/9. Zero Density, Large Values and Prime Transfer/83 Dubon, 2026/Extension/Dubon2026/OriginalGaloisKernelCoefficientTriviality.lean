import Dubon2026.GaloisTowerKernelCohomology

/-! # The actual restriction kernel fixes coefficients from an earlier field

DUB-17's constructed norm tower contains the original finite coefficient
stage. The pinned literal field-restriction composition proves that the
new middle-field kernel acts trivially on every coefficient inflated
from that earlier stage. No action-triviality certificate is supplied.
-/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV2

/-- Literal field restriction makes the middle-field kernel act
trivially on the original coefficient inflated from the lower field. -/
theorem originalGaloisTowerKernel_coefficient_trivial
    (K D E L : Type) [Field K] [Field D] [Field E] [Field L]
    [Algebra K D] [Algebra K E] [Algebra K L]
    [Algebra D E] [Algebra D L] [Algebra E L]
    [IsScalarTower K D L] [IsScalarTower K D E]
    [IsScalarTower K E L] [IsScalarTower D E L]
    [Normal K D] [Normal K E]
    (B : Rep ℤ Gal(D/K))
    (g : (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker)
    (b : Rep.res (AlgEquiv.restrictNormalHom D : Gal(L/K) →* Gal(D/K)) B) :
    (Rep.res (AlgEquiv.restrictNormalHom D : Gal(L/K) →* Gal(D/K)) B).ρ g.val b = b := by
  change B.ρ (AlgEquiv.restrictNormalHom D g.val) b = b
  rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply D E g.val,
    show AlgEquiv.restrictNormalHom E g.val = 1 from g.property, map_one, map_one]
  rfl

end
end Dubon2026
