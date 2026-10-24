import Dubon2026.SourceEllipticTorsionReductionEquiv
import Dubon2026.SourceEllipticIntegralOddQuotientModel

/-! Exact coordinate and order compatibility of the actual torsion reduction.
These identities identify the reduced half-orbit set used in the literal
integral Velu model with the half-orbit of the reduced cyclic generator. -/

namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing SourceEllipticVelu
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
variable [DecidableEq (ResidueField A)] {W : WeierstrassCurve A}

/-- Multiplication of an actual torsion point commutes with reduction. -/
theorem reducePoint_nsmul_of_torsion (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) (P : (W.map A.subtype).toAffine.Point)
    (hP : N • P = 0) (m : ℕ) :
    reducePoint hΔ (m • P) = m • reducePoint hΔ P := by
  let P' : Submodule.torsionBy ℤ (W.map A.subtype).toAffine.Point (N : ℤ) :=
    ⟨P, by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using hP⟩
  exact map_nsmul (torsionReductionHom hΔ hN) m P'

/-- The actual order of a prime-to-residue torsion point is preserved. -/
theorem addOrderOf_reducePoint (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) (P : (W.map A.subtype).toAffine.Point)
    (hP : N • P = 0) : addOrderOf (reducePoint hΔ P) = addOrderOf P := by
  let S := Submodule.torsionBy ℤ (W.map A.subtype).toAffine.Point (N : ℤ)
  let P' : S := ⟨P, by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using hP⟩
  calc addOrderOf (reducePoint hΔ P)
      = addOrderOf P' := addOrderOf_injective _ (torsionReductionHom_injective hΔ hN) P'
    _ = addOrderOf P := (addOrderOf_injective S.subtype.toAddMonoidHom
      Subtype.val_injective P').symm

omit [DecidableEq (ResidueField A)] in
/-- The integral coordinates reduce to exactly the coordinates of the actual reduced point. -/
theorem integralTorsionCoordinates_residue (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) (P : (W.map A.subtype).toAffine.Point)
    (hP : N • P = 0) :
    Prod.map (residue A) (residue A) (integralTorsionCoordinates A W hN P hP) =
      coordsOrZero (reducePoint hΔ P) := by
  rcases P with _ | ⟨x, y, h⟩
  · change (residue A 0, residue A 0) = (0, 0)
    simp only [map_zero]
  · rw [reducePoint_some_of_mem hΔ h
      (SourceEllipticFunctionField.torsion_x_mem_valuationSubring A W h N hN hP)]
    rfl

/-- The constructed integral kernel set reduces to the actual reduced half-orbit. -/
theorem integralOddSummingSet_residue (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) (Q : (W.map A.subtype).toAffine.Point)
    (hQ : N • Q = 0) (n : ℕ) :
    (integralOddSummingSet A W hN Q hQ n).image (Prod.map (residue A) (residue A)) =
      oddOrderSummingSet (W.map (residue A)) (reducePoint hΔ Q) n := by
  simp only [integralOddSummingSet, oddOrderSummingSet, Finset.image_image]
  apply Finset.image_congr
  intro m _
  change Prod.map (residue A) (residue A) (integralTorsionCoordinates A W hN (m • Q) _) = _
  rw [integralTorsionCoordinates_residue hΔ, reducePoint_nsmul_of_torsion hΔ hN Q hQ]

end
end Dubon2026.SourceEllipticReduction
