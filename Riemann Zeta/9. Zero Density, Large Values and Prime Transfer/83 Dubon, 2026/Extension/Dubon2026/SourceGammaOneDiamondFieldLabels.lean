import Dubon2026.SourceGammaOneDiamondFieldHom
import Dubon2026.SourceGammaOneDiamondLabels
import Dubon2026.SourceGammaOneCuspPlaceLeftInvariance

/-! DUB-17/18 -> original all-weight association -> arithmetic Gamma1
diamond/Picard comparison -> unit-labelled diamond on the original field.
The native Gamma0 character kernel and original cusp invariance prove
lift independence. Integral SL2 reduction supplies every unit label.
Rational descent and compatibility with the arithmetic Picard action remain.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup UpperHalfPlane Filter
open scoped MatrixGroups Topology
variable (M : ℕ) [NeZero M]

theorem diamondFieldHom_lift_independent (g h : Gamma0 M)
    (hlabel : Gamma0Map M g = Gamma0Map M h) (x : functionFieldOver (Gamma1 M) ℂ) :
    diamondFieldHom M g x = diamondFieldHom M h x := by
  have hker : g * h⁻¹ ∈ Gamma1' M := by
    change Gamma0Map M (g * h⁻¹) = 1
    rw [map_mul, hlabel, ← map_mul, mul_inv_cancel, map_one]
  let u : Gamma1 M := ⟨g.val * h.val⁻¹,
    (Gamma1_mem M _).mpr ((Gamma1_to_Gamma0_mem _).mp hker)⟩
  have hu : u.val * h.val = g.val := by
    change (g.val * h.val⁻¹) * h.val = g.val
    group
  have hT : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
  have hΓ : Gamma M ≤ Gamma1 M := by
    intro A hA
    rw [Gamma_mem] at hA
    exact (Gamma1_mem M A).mpr ⟨hA.1, hA.2.2.2, hA.2.2.1⟩
  apply (fieldCuspGerm M 1).injective
  rw [diamondFieldHom_cuspGerm, diamondFieldHom_cuspGerm, mul_one, mul_one]
  apply Germ.coe_eq.mpr
  simpa only [hu] using cuspRealize_mul_left_eventuallyEq M hΓ hT x u h.val

/-- The lower-right-unit diamond automorphism of the original complex Gamma1 field. -/
def unitDiamondFieldAut (d : (ZMod M)ˣ) :
    functionFieldOver (Gamma1 M) ℂ ≃ₐ[ℂ] functionFieldOver (Gamma1 M) ℂ :=
  diamondFieldAut M (sourceGammaOneDiamondLabel_lift M d).choose

theorem unitDiamondFieldAut_eq (d : (ZMod M)ˣ) (g : Gamma0 M)
    (hg : Gamma0Map M g = (d : ZMod M)) (x : functionFieldOver (Gamma1 M) ℂ) :
    unitDiamondFieldAut M d x = diamondFieldHom M g x :=
  diamondFieldHom_lift_independent M _ g
    ((sourceGammaOneDiamondLabel_lift M d).choose_spec.trans hg.symm) x

theorem unitDiamondFieldAut_one (x : functionFieldOver (Gamma1 M) ℂ) :
    unitDiamondFieldAut M 1 x = x := by
  rw [unitDiamondFieldAut_eq M 1 1 (by simp), diamondFieldHom_one]

theorem unitDiamondFieldAut_mul (d e : (ZMod M)ˣ)
    (x : functionFieldOver (Gamma1 M) ℂ) :
    unitDiamondFieldAut M (d * e) x = unitDiamondFieldAut M d (unitDiamondFieldAut M e x) := by
  let g := (sourceGammaOneDiamondLabel_lift M d).choose
  let h := (sourceGammaOneDiamondLabel_lift M e).choose
  have hg : Gamma0Map M g = (d : ZMod M) := (sourceGammaOneDiamondLabel_lift M d).choose_spec
  have hh : Gamma0Map M h = (e : ZMod M) := (sourceGammaOneDiamondLabel_lift M e).choose_spec
  have hgh : Gamma0Map M (h * g) = ((d * e : (ZMod M)ˣ) : ZMod M) := by
    rw [map_mul, hg, hh, Units.val_mul, mul_comm]
  rw [unitDiamondFieldAut_eq M (d * e) (h * g) hgh,
    unitDiamondFieldAut_eq M d g hg, unitDiamondFieldAut_eq M e h hh, diamondFieldHom_mul]

end
end Dubon2026.SourceFunctionField.GammaOne
