import Dubon2026.SourceEllipticTorsionReductionHom
import Dubon2026.SourceValuationResidueAlgClosed
import Dubon2026.SourceEllipticTorsionCardinality

/-! Actual prime-to-residue torsion lifting follows from the proved reduction
injection and the existing n² torsion cardinalities. The residue field is
proved algebraically closed from the ambient field. No Hensel-lifting or
surjectivity certificate is supplied. This serves integral odd quotient
specialization on the DUB-17/18 modular-curve good-reduction chain. -/

namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
variable [DecidableEq (ResidueField A)] {W : WeierstrassCurve A}

/-- Reduction lands in the actual torsion subgroup of the reduced curve. -/
def torsionReduction (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) :
    Submodule.torsionBy ℤ (W.map A.subtype).toAffine.Point (N : ℤ) →+
      Submodule.torsionBy ℤ (W.map (residue A)).toAffine.Point (N : ℤ) where
  toFun P := ⟨torsionReductionHom hΔ hN P, by
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, Submodule.smul_torsionBy, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ P Q)

/-- Restricting the codomain preserves the proved torsion reduction injection. -/
theorem torsionReduction_injective (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) : Function.Injective (torsionReduction hΔ hN) := by
  intro P Q h
  exact torsionReductionHom_injective hΔ hN (congrArg Subtype.val h)

/-- The actual torsion reduction map is surjective over an algebraically closed ambient field. -/
theorem torsionReduction_surjective [IsAlgClosed L] (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) : Function.Surjective (torsionReduction hΔ hN) := by
  letI : W.IsElliptic := ⟨(map_residue_Δ_ne_zero_iff W).mp hΔ⟩
  letI : IsAlgClosed (ResidueField A) := residueField_isAlgClosed A
  have hNL : (N : L) ≠ 0 := by
    have h := (hN.map A.subtype).ne_zero
    simpa only [map_natCast] using h
  have hNk : (N : ResidueField A) ≠ 0 := by
    have h := (hN.map (residue A)).ne_zero
    simpa only [map_natCast] using h
  have hgen : Nat.card (Submodule.torsionBy ℤ (W.map A.subtype).toAffine.Point (N : ℤ)) =
      N ^ 2 := by
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
      using SourceEllipticTorsion.actual_torsion_cardinality (W.map A.subtype) hNL
  have hres : Nat.card (Submodule.torsionBy ℤ (W.map (residue A)).toAffine.Point (N : ℤ)) =
      N ^ 2 := by
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
      using SourceEllipticTorsion.actual_torsion_cardinality (W.map (residue A)) hNk
  have hN0 : N ≠ 0 := by intro h; apply hNL; rw [h, Nat.cast_zero]
  letI : Finite (Submodule.torsionBy ℤ (W.map (residue A)).toAffine.Point (N : ℤ)) :=
    Nat.finite_of_card_ne_zero (hres ▸ pow_ne_zero 2 hN0)
  exact ((torsionReduction_injective hΔ hN).bijective_of_nat_card_le
    (by rw [hres, hgen])).surjective

/-- The actual prime-to-residue torsion groups are identified by coordinate reduction. -/
def torsionReductionEquiv [IsAlgClosed L] (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) :
    Submodule.torsionBy ℤ (W.map A.subtype).toAffine.Point (N : ℤ) ≃+
      Submodule.torsionBy ℤ (W.map (residue A)).toAffine.Point (N : ℤ) :=
  AddEquiv.ofBijective (torsionReduction hΔ hN)
    ⟨torsionReduction_injective hΔ hN, torsionReduction_surjective hΔ hN⟩

end
end Dubon2026.SourceEllipticReduction
