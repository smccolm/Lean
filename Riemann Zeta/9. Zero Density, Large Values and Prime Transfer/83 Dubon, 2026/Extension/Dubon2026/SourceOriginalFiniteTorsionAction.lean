import Dubon2026.SourceOriginalComplexTorsionCardinality
import Dubon2026.SourceOriginalArithmeticPicard
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! DUB-17/18 -> arithmetic torsion surjectivity -> fixed reduced divisor.
The actual complex n-torsion is finite. Its existing coefficient action is
therefore killed by the factorial of its cardinality. Native finite-map
iteration replaces the external pigeonhole argument on translated divisor
classes; the original Pic0 representative already has degree zero.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N]
local notation "FC" => modularFunctionFieldOver N ℂ

theorem complex_torsion_action_factorial (n : ℕ) (hn : n ≠ 0) (τ : ℂ ≃ₐ[ℚ] ℂ)
    (x : Pic0 ℂ FC) (hx : x ∈ Pic0.torsion n) :
    originalArithmeticPicard N (τ ^ (Nat.card (Pic0.torsion (K := ℂ) (F := FC) n)).factorial) x = x := by
  let T := Pic0.torsion (K := ℂ) (F := FC) n
  letI : Finite T := Nat.finite_of_card_ne_zero (by
    rw [OriginalChart.original_complex_torsion_cardinality N n hn]
    exact pow_ne_zero _ hn)
  letI := Fintype.ofFinite T
  letI : MulAction (ℂ ≃ₐ[ℚ] ℂ) T := {
    smul σ y := ⟨originalArithmeticPicard N σ y.val, originalArithmeticPicard_torsion N σ n y.val y.property⟩
    one_smul y := Subtype.ext (DFunLike.congr_fun (originalArithmeticPicardRep N (L := ℂ)).map_one y.val)
    mul_smul σ υ y := Subtype.ext
      (DFunLike.congr_fun ((originalArithmeticPicardRep N (L := ℂ)).map_mul σ υ) y.val) }
  have hinj : Function.Injective (fun y : T => τ • y) := by
    intro y z h
    have he := congrArg (fun w : T => τ⁻¹ • w) h
    simpa only [inv_smul_smul] using he
  have he := congrFun (Function.injective_iff_iterate_factorial_card_eq_id.mp hinj) (⟨x, hx⟩ : T)
  rw [smul_iterate_apply] at he
  have hv := congrArg Subtype.val he
  simpa only [Nat.card_eq_fintype_card] using hv

theorem complex_torsion_divisor_factorial_principal (n : ℕ) (hn : n ≠ 0)
    (τ : ℂ ≃ₐ[ℚ] ℂ) (D : Divisor.degZero (K := ℂ) (F := FC))
    (hD : Pic0.mk D ∈ Pic0.torsion n) :
    Divisor.IsPrincipal (originalArithmeticDivisorEquiv N
      (τ ^ (Nat.card (Pic0.torsion (K := ℂ) (F := FC) n)).factorial) D.val - D.val) := by
  have h := complex_torsion_action_factorial N n hn τ (Pic0.mk D) hD
  rw [originalArithmeticPicard_mk] at h
  have hz : Pic0.mk (originalArithmeticDegZero N
      (τ ^ (Nat.card (Pic0.torsion (K := ℂ) (F := FC) n)).factorial) D - D) = 0 := by
    rw [map_sub, h, sub_self]
  exact (Pic0.mk_eq_zero_iff _).mp hz

end
end Dubon2026.SourceFunctionField.OriginalConstantField
