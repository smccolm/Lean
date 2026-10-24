import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic

/-! The scaling coordinate determines an elliptic coordinate-change
stabilizer when 2 and 3 are nonzero. Native coefficient and invariant
formulas give a shorter route than transporting the source's short-normal-
form classification. The resulting bounds are required by the inertia
image comparison in the DUB-17/18 exceptional-fiber census.
Source comparison: anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_finite_stabilizer_and_natCard_le_of_j. -/
namespace Dubon2026.SourceEllipticStabilizer
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] (W : WeierstrassCurve K)

theorem scaling_injective (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Function.Injective (fun C : MulAction.stabilizer (VariableChange K) W => (C.val.u : K)) := by
  rintro ⟨C, hC⟩ ⟨D, hD⟩ hu
  have hCW := MulAction.mem_stabilizer_iff.mp hC
  have hDW := MulAction.mem_stabilizer_iff.mp hD
  have hu' : C.u = D.u := Units.ext hu
  have h1 := (congrArg WeierstrassCurve.a₁ hCW).trans
    (congrArg WeierstrassCurve.a₁ hDW).symm
  rw [variableChange_a₁, variableChange_a₁, hu'] at h1
  have hs : C.s = D.s := by
    have h := mul_left_cancel₀ (D.u⁻¹).ne_zero h1
    have h' : 2 * (C.s - D.s) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left h2)
  have h2' := (congrArg WeierstrassCurve.a₂ hCW).trans
    (congrArg WeierstrassCurve.a₂ hDW).symm
  rw [variableChange_a₂, variableChange_a₂, hu', hs] at h2'
  have hr : C.r = D.r := by
    have h := mul_left_cancel₀ (pow_ne_zero 2 (D.u⁻¹).ne_zero) h2'
    have h' : 3 * (C.r - D.r) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left h3)
  have h3' := (congrArg WeierstrassCurve.a₃ hCW).trans
    (congrArg WeierstrassCurve.a₃ hDW).symm
  rw [variableChange_a₃, variableChange_a₃, hu', hr] at h3'
  have ht : C.t = D.t := by
    have h := mul_left_cancel₀ (pow_ne_zero 3 (D.u⁻¹).ne_zero) h3'
    have h' : 2 * (C.t - D.t) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left h2)
  exact Subtype.ext (VariableChange.ext hu' hr hs ht)

theorem scaling_pow_of_invariant {u : Kˣ} {n : ℕ} {a : K} (ha : a ≠ 0)
    (h : ((u⁻¹ : Kˣ) : K) ^ n * a = a) : (u : K) ^ n = 1 := by
  have hi := mul_right_cancel₀ ha (h.trans (one_mul a).symm)
  rw [Units.val_inv_eq_inv_val, inv_pow] at hi
  exact inv_eq_one.mp hi

theorem scaling_pow_four (hc : W.c₄ ≠ 0) {C : VariableChange K} (hC : C • W = W) :
    (C.u : K) ^ 4 = 1 := by
  apply scaling_pow_of_invariant hc
  simpa only [variableChange_c₄] using congrArg WeierstrassCurve.c₄ hC

theorem scaling_pow_six (hc : W.c₆ ≠ 0) {C : VariableChange K} (hC : C • W = W) :
    (C.u : K) ^ 6 = 1 := by
  apply scaling_pow_of_invariant hc
  simpa only [variableChange_c₆] using congrArg WeierstrassCurve.c₆ hC

theorem scaling_pow_two (h4 : W.c₄ ≠ 0) (h6 : W.c₆ ≠ 0)
    {C : VariableChange K} (hC : C • W = W) : (C.u : K) ^ 2 = 1 := by
  have hf := scaling_pow_four W h4 hC
  have hs := scaling_pow_six W h6 hC
  calc (C.u : K) ^ 2 = (C.u : K) ^ 4 * (C.u : K) ^ 2 := by rw [hf, one_mul]
    _ = (C.u : K) ^ 6 := by ring
    _ = 1 := hs

end
end Dubon2026.SourceEllipticStabilizer
