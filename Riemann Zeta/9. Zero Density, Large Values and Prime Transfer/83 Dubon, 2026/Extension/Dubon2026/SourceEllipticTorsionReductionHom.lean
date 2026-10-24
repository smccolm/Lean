import Dubon2026.SourceEllipticResidueIntegralAddition
import Mathlib.Algebra.Module.Torsion.Basic

/-! The actual reduction homomorphism on the required prime-to-residue torsion.
Every nonzero torsion point has integral coordinates by the already proved
division-polynomial argument. Thus the integral addition case suffices;
no full reduction map on arbitrary nonintegral points is required. -/

namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing SourceEllipticFunctionField
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
variable [DecidableEq (ResidueField A)] {W : WeierstrassCurve A}

/-- Actual reduction is additive on points killed by a unit integer. -/
theorem reducePoint_add_of_torsion (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) (P Q : (W.map A.subtype).toAffine.Point)
    (hP : N • P = 0) (hQ : N • Q = 0) :
    reducePoint hΔ (P + Q) = reducePoint hΔ P + reducePoint hΔ Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · change reducePoint hΔ (0 + Q) = reducePoint hΔ 0 + reducePoint hΔ Q
    rw [zero_add, reducePoint_zero, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · change reducePoint hΔ (Affine.Point.some x₁ y₁ h₁ + 0) =
      reducePoint hΔ (Affine.Point.some x₁ y₁ h₁) + reducePoint hΔ 0
    rw [add_zero, reducePoint_zero, add_zero]
  exact reducePoint_add_of_mem hΔ h₁ h₂
    (torsion_x_mem_valuationSubring A W h₁ N hN hP)
    (torsion_x_mem_valuationSubring A W h₂ N hN hQ)

omit [DecidableEq (ResidueField A)] in
/-- Reduction of a point killed by a unit integer is zero only for the zero point. -/
theorem reducePoint_eq_zero_of_torsion (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) (P : (W.map A.subtype).toAffine.Point)
    (hP : N • P = 0) : reducePoint hΔ P = 0 ↔ P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact iff_of_true rfl rfl
  · rw [reducePoint_some_of_mem hΔ h (torsion_x_mem_valuationSubring A W h N hN hP)]
    simp only [Affine.Point.some_ne_zero, iff_self]

/-- Reduction restricted to the original torsion subgroup is an actual group homomorphism. -/
def torsionReductionHom (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) :
    Submodule.torsionBy ℤ (W.map A.subtype).toAffine.Point (N : ℤ) →+
      (W.map (residue A)).toAffine.Point where
  toFun P := reducePoint hΔ P
  map_zero' := rfl
  map_add' P Q := reducePoint_add_of_torsion hΔ hN P Q
    (by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using P.property)
    (by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using Q.property)

/-- The actual reduction homomorphism is injective on prime-to-residue torsion. -/
theorem torsionReductionHom_injective (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) : Function.Injective (torsionReductionHom hΔ hN) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro P hP
  apply Subtype.ext
  exact (reducePoint_eq_zero_of_torsion hΔ hN P
    (by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using P.property)).mp hP

end
end Dubon2026.SourceEllipticReduction
