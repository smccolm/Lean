import Dubon2026.SourceEllipticQuarticModel
import Dubon2026.SourceEllipticCubicModel
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! The exact exceptional j-values and actual scaling units needed to
instantiate the modular-place classifier. Native algebraic closure and
primitive-root existence supply the units; no root witness is assumed. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K]

theorem quartic_j (A : K) [(EA A).IsElliptic] : (EA A).j = 1728 := by
  have hj : (EA A).Δ * (EA A).j = (EA A).c₄ ^ 3 := by
    rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', ← mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  apply mul_left_cancel₀ (isUnit_iff_ne_zero.mp (EA A).isUnit_Δ)
  rw [hj, EA_Δ]
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem cubic_j (B : K) [(EB B).IsElliptic] : (EB B).j = 0 := by
  apply WeierstrassCurve.j_eq_zero
  simp [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

theorem exists_quartic_scaling [IsAlgClosed K] : ∃ u : Kˣ, (u : K) ^ 2 = -1 := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) (n := 2) (by norm_num)
  have hu0 : u ≠ 0 := by rintro rfl; norm_num at hu
  exact ⟨Units.mk0 u hu0, hu⟩

theorem exists_cubic_scaling [IsAlgClosed K] (h3 : (3 : K) ≠ 0) :
    ∃ u : Kˣ, (u : K) ^ 3 = 1 ∧ (u : K) ≠ 1 := by
  haveI : NeZero (3 : K) := ⟨h3⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K 3
  obtain ⟨u, rfl⟩ := hζ.isUnit (by norm_num)
  exact ⟨u, hζ.pow_eq_one, hζ.ne_one (by norm_num)⟩

end
end Dubon2026.SourceEllipticExceptional
