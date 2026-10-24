import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic

/-! DUB-17/18 -> characteristic-two good models -> faithful inertia.
The exact Deuring coordinate and flex argument is adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_variableChange_eq_deuring_of_isUnit_three.
The actual field and torsion inputs remain for the subsequent consumer. -/
namespace Dubon2026.SourceEllipticDeuring
open WeierstrassCurve
noncomputable section
section Deuring

variable {R : Type*} [CommRing R] (α : R)

lemma deuring_Δ : (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve R).Δ = α ^ 3 - 27 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

lemma deuring_c₄ : (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve R).c₄ = α * (α ^ 3 - 24) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

lemma deuring_map {S : Type*} [CommRing S] (φ : R →+* S) :
    (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve R).map φ = ⟨φ α, 0, 1, 0, 0⟩ := by
  simp only [WeierstrassCurve.map, map_zero, map_one]

lemma j_deuring_mul {F : Type*} [Field F] (α : F) [(⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve F).IsElliptic] :
    (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve F).j * (α ^ 3 - 27) = α ^ 3 * (α ^ 3 - 24) ^ 3 := by
  set V : WeierstrassCurve F := ⟨α, 0, 1, 0, 0⟩ with hV
  have hjΔ : V.j * V.Δ = V.c₄ ^ 3 := by
    rw [WeierstrassCurve.j, mul_comm, ← mul_assoc, ← WeierstrassCurve.coe_Δ', Units.mul_inv, one_mul]
  rw [deuring_Δ, deuring_c₄] at hjΔ
  linear_combination hjΔ

end Deuring

end
end Dubon2026.SourceEllipticDeuring
