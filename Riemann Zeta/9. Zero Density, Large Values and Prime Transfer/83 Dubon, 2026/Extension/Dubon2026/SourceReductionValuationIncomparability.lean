import Dubon2026.SourceReductionAlgebraicNormalization

/-! DUB-17/18 -> Picard torsion injectivity -> extending residue fields.
The already proved constant normalization makes distinct extensions
incomparable. This avoids a separate minimal-polynomial coefficient argument. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
variable {L F Fbar E : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
  [Field F] [Algebra L F] [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
  [Field E] [Algebra F E] [Algebra L E] [IsScalarTower L F E]
  [Algebra.IsAlgebraic F E]

theorem extending_valuation_eq_of_le (R : RegularProlongation A F Fbar)
    {V W : ValuationSubring E}
    (hV : V.comap (algebraMap F E) = R.integers)
    (hW : W.comap (algebraMap F E) = R.integers) (hle : V ≤ W) : V = W := by
  apply le_antisymm hle
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨c, hc⟩ := R.exists_smul_valuation_eq_one_of_isIntegral V hV hx0
    (Algebra.IsIntegral.isIntegral x)
  have hu : IsUnit (⟨c • x, (V.valuation_le_one_iff _).mp hc.le⟩ : V) :=
    (V.valuation_eq_one_iff _).mpr hc
  have hwu := (W.valuation_eq_one_iff _).mp (hu.map (V.inclusion W hle))
  change W.valuation (c • x) = 1 at hwu
  have hc0 : c ≠ 0 := by
    intro hz
    simp [hz] at hc
  have hcinv : algebraMap L E c⁻¹ ∈ W := by
    have heq : algebraMap L E c⁻¹ = x * (c • x)⁻¹ := by
      rw [Algebra.smul_def, mul_inv, ← mul_assoc, mul_right_comm,
        mul_inv_cancel₀ hx0, one_mul, map_inv₀]
    rw [heq]
    apply W.mul_mem _ _ hx
    rw [← W.valuation_le_one_iff, map_inv₀, hwu, inv_one]
  have hcinvV : algebraMap L E c⁻¹ ∈ V := by
    rw [IsScalarTower.algebraMap_apply L F E] at hcinv ⊢
    change algebraMap L F c⁻¹ ∈ V.comap (algebraMap F E)
    change algebraMap L F c⁻¹ ∈ W.comap (algebraMap F E) at hcinv
    rwa [hV, ← hW]
  have heq : x = algebraMap L E c⁻¹ * (c • x) := by
    rw [Algebra.smul_def, map_inv₀, ← mul_assoc,
      inv_mul_cancel₀ ((_root_.map_ne_zero _).mpr hc0), one_mul]
  rw [heq]
  exact V.mul_mem _ _ hcinvV ((V.valuation_le_one_iff _).mp hc.le)

end
end Dubon2026.SourceCurve.RegularProlongation
