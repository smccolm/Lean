import Dubon2026.SourceReductionIndependent

/-! DUB-17/18 -> Kummer power lifting -> sum-of-genera inequality ->
simultaneous residue dimension. Normalization by the same constant field
makes comparable regular prolongation valuations equal. This supplies
incomparability for finite residue approximation without field-degree
or genus assumptions. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
variable {L F Fb Fc : Type*} [Field L] {A : ValuationSubring L}
  [Field F] [Algebra L F] [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
  [Field Fc] [Algebra (IsLocalRing.ResidueField A) Fc]

theorem integers_eq_of_le (R : RegularProlongation A F Fb) (S : RegularProlongation A F Fc)
    (hle : R.integers ≤ S.integers) : R.integers = S.integers := by
  refine le_antisymm hle fun x hx => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨c, hc, hcres⟩ := R.exists_smul_mem x hx0
  have hu := R.isUnit_of_residue_ne_zero hcres
  have hSnorm := (S.integers.valuation_eq_one_iff _).mp
    (hu.map (R.integers.inclusion S.integers hle))
  change S.integers.valuation (c • x) = 1 at hSnorm
  have hc0 : c ≠ 0 := by
    intro hz
    have heq : (⟨c • x, hc⟩ : R.integers) = 0 := Subtype.ext (by simp [hz])
    exact hcres (by rw [heq, map_zero])
  have hcSmem : algebraMap L F c⁻¹ ∈ S.integers := by
    have heq : algebraMap L F c⁻¹ = x * (c • x)⁻¹ := by
      rw [Algebra.smul_def, mul_inv, ← mul_assoc, mul_right_comm,
        mul_inv_cancel₀ hx0, one_mul, map_inv₀]
    rw [heq]
    apply S.integers.mul_mem _ _ hx
    rw [← S.integers.valuation_le_one_iff, map_inv₀, hSnorm, inv_one]
  have hcRmem : algebraMap L F c⁻¹ ∈ R.integers :=
    (R.algebraMap_mem_iff _).mpr ((S.algebraMap_mem_iff _).mp hcSmem)
  have heq : x = algebraMap L F c⁻¹ * (c • x) := by
    rw [Algebra.smul_def, map_inv₀, ← mul_assoc,
      inv_mul_cancel₀ ((_root_.map_ne_zero _).mpr hc0), one_mul]
  rw [heq]
  exact R.integers.mul_mem _ _ hcRmem hc

end
end Dubon2026.SourceCurve.RegularProlongation
