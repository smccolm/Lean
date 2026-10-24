import Dubon2026.SourceJointChartInverseClearing

/-! DUB-17/18 -> Kummer power lifting -> finite overlap. The existing
pole-bound argument moves each lifted chart basis element into the inverse
chart. A finite maximum gives one exponent for the entire actual basis. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open IsLocalRing

theorem exists_uniform_inverse_chart_power
    {L F : Type*} [Field L] [IsAlgClosed L] [CharZero L]
    {A : ValuationSubring L} [Field F] [Algebra L F]
    {ι J : Type*} [Fintype J] {Fb : ι → Type*} [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i)) (f : F)
    (hfi : ∀ i, f⁻¹ ∈ (R i).integers) (htr : Transcendental L f)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (z : J → F) (hz : ∀ j, z j ∈ Sg R f) :
    ∃ m : ℕ, ∀ j, (f⁻¹) ^ m * z j ∈ Sg R f⁻¹ := by
  classical
  have htri : Transcendental L f⁻¹ := fun h => htr (IsAlgebraic.inv_iff.mp h)
  haveI : FiniteDimensional (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
    rw [adjoin_singleton_inv_eq]
    infer_instance
  have hex : ∀ j, ∃ m : ℕ, z j * f⁻¹ ^ m ∈ Sg R f⁻¹ := fun j =>
    exists_mul_pow_mem_Sg R f⁻¹ hfi htri (z j) (by simpa only [inv_inv] using hz j)
  choose m hm using hex
  let M := Finset.univ.sup m
  have hle (j : J) : m j ≤ M := Finset.le_sup (f := m) (Finset.mem_univ j)
  refine ⟨M, fun j => ?_⟩
  have he : f⁻¹ ^ M * z j = (z j * f⁻¹ ^ m j) * f⁻¹ ^ (M - m j) := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le (hle j), mul_comm]
  rw [he]
  exact mul_mem (hm j) (pow_mem (self_mem_Sg R hfi) _)

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
