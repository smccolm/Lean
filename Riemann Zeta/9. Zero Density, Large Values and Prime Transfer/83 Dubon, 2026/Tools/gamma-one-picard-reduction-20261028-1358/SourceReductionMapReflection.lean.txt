import Dubon2026.SourceCurveRegularProlongation

/-! DUB-17/18 -> original Gamma1 Tate Frobenius -> integral-fraction
Hecke norm reduction. Primitive normalization by a constant gives a unit
in the source valuation. A valuation-preserving constant-linear map sends
that unit to a unit, so it reflects integrality as well. This isolates the
existing normalization argument from the original field's elaboration. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
variable {L F E Fb Eb : Type*} [Field L] {A : ValuationSubring L}
  [Field F] [Algebra L F] [Field E] [Algebra L E]
  [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
  [Field Eb] [Algebra (IsLocalRing.ResidueField A) Eb]

theorem map_mem_iff_of_preserves_integers
    (R : RegularProlongation A F Fb) (S : RegularProlongation A E Eb)
    (φ : F →ₐ[L] E) (hφ : ∀ f ∈ R.integers, φ f ∈ S.integers) (f : F) :
    φ f ∈ S.integers ↔ f ∈ R.integers := by
  refine ⟨fun hf => ?_, fun hf => hφ f hf⟩
  by_cases hf0 : f = 0
  · simp [hf0]
  let ψ : R.integers →+* S.integers :=
    (φ.toRingHom.comp R.integers.subtype).codRestrict S.integers.toSubring (fun x => hφ x x.2)
  obtain ⟨c, hc, hcres⟩ := R.exists_smul_mem f hf0
  have hu := R.isUnit_of_residue_ne_zero hcres
  have hSnorm := (S.integers.valuation_eq_one_iff _).mp (hu.map ψ)
  change S.integers.valuation (φ (c • f)) = 1 at hSnorm
  have hc0 : c ≠ 0 := by
    intro hz
    have heq : (⟨c • f, hc⟩ : R.integers) = 0 := Subtype.ext (by simp [hz])
    exact hcres (by rw [heq, map_zero])
  have he : algebraMap L F c⁻¹ = f * (c • f)⁻¹ := by
    rw [Algebra.smul_def, mul_inv, ← mul_assoc, mul_right_comm,
      mul_inv_cancel₀ hf0, one_mul, map_inv₀]
  have hciS : algebraMap L E c⁻¹ ∈ S.integers := by
    have he' : algebraMap L E c⁻¹ = φ f * (φ (c • f))⁻¹ := by
      simpa only [map_mul, map_inv₀, φ.commutes] using congrArg φ he
    rw [he']
    apply S.integers.mul_mem _ _ hf
    rw [← S.integers.valuation_le_one_iff, map_inv₀, hSnorm, inv_one]
  have hciR : algebraMap L F c⁻¹ ∈ R.integers :=
    (R.algebraMap_mem_iff _).mpr ((S.algebraMap_mem_iff _).mp hciS)
  have he' : f = algebraMap L F c⁻¹ * (c • f) := by
    rw [Algebra.smul_def, map_inv₀, ← mul_assoc,
      inv_mul_cancel₀ ((_root_.map_ne_zero _).mpr hc0), one_mul]
  rw [he']
  exact R.integers.mul_mem _ _ hciR hc

end
end Dubon2026.SourceCurve.RegularProlongation
