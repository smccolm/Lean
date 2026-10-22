import Dubon2026.SourceConstantFieldLocalRing

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison -> exact constant-field place extension. These finite local combinations and their
fractions express every original complex function in a form whose order can
be computed from the original arithmetic place. This serves the conorm of
divisors and preserves the literal principal-divisor relation.
Adapted from S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Existing place orders are reused.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section

variable {K F K' : Type*} (F' : Type*) [Field K] [Field F] [Field K'] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F']
  {ι : Type*} (B : Module.Basis ι K K') (P : Place K F)

/-- Original local combinations with one original nonzero local denominator. -/
noncomputable def fracPsi : Subalgebra K' F' where
  carrier := {y | ∃ w, ∃ s : P.toValuationSubring, (s : F) ≠ 0 ∧
    y * algebraMap F F' (s : F) = Psi F' B P w}
  mul_mem' := by
    rintro y₁ y₂ ⟨w₁, s₁, hs₁, h₁⟩ ⟨w₂, s₂, hs₂, h₂⟩
    obtain ⟨w, hw⟩ := Psi_mul_mem_range F' B P w₁ w₂
    refine ⟨w, s₁ * s₂, by rw [MulMemClass.coe_mul]; exact mul_ne_zero hs₁ hs₂, ?_⟩
    rw [hw, ← h₁, ← h₂, MulMemClass.coe_mul, map_mul]
    ring
  one_mem' := ⟨pureW B P 1 1, 1, by simp, by simp [Psi_pureW]⟩
  add_mem' := by
    rintro y₁ y₂ ⟨w₁, s₁, hs₁, h₁⟩ ⟨w₂, s₂, hs₂, h₂⟩
    refine ⟨s₂ • w₁ + s₁ • w₂, s₁ * s₂, by rw [MulMemClass.coe_mul]; exact mul_ne_zero hs₁ hs₂, ?_⟩
    rw [map_add, Psi_smul, Psi_smul, ← h₁, ← h₂, MulMemClass.coe_mul, map_mul]
    ring
  zero_mem' := ⟨0, 1, by simp, by simp⟩
  algebraMap_mem' d := ⟨pureW B P d 1, 1, by simp, by simp [Psi_pureW]⟩

theorem mem_fracPsi_iff {y : F'} : y ∈ fracPsi F' B P ↔ ∃ w, ∃ s : P.toValuationSubring,
    (s : F) ≠ 0 ∧ y * algebraMap F F' (s : F) = Psi F' B P w := Iff.rfl

theorem algebraMap_mem_fracPsi (f : F) : algebraMap F F' f ∈ fracPsi F' B P := by
  rcases P.toValuationSubring.mem_or_inv_mem f with h | h
  · exact ⟨pureW B P 1 ⟨f, h⟩, 1, by simp, by simp [Psi_pureW]⟩
  · rcases eq_or_ne f 0 with rfl | hf
    · rw [map_zero]; exact (fracPsi F' B P).zero_mem
    · refine ⟨pureW B P 1 1, ⟨f⁻¹, h⟩, by simpa using hf, ?_⟩
      simp [Psi_pureW, mul_inv_cancel₀ ((map_ne_zero (algebraMap F F')).2 hf)]

theorem exists_mul_Psi_eq (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {z : F'} (hz : z ≠ 0) :
    ∃ w₁ w₂, Psi F' B P w₂ ≠ 0 ∧ z * Psi F' B P w₂ = Psi F' B P w₁ := by
  have hzmem : z ∈ IntermediateField.adjoin K' (Set.range (algebraMap F F')) := by
    rw [hgen]; trivial
  rw [IntermediateField.mem_adjoin_iff_div] at hzmem
  obtain ⟨r, hr, s, hs, rfl⟩ := hzmem
  have hle : Algebra.adjoin K' (Set.range (algebraMap F F')) ≤ fracPsi F' B P :=
    Algebra.adjoin_le (by rintro _ ⟨f, rfl⟩; exact algebraMap_mem_fracPsi F' B P f)
  obtain ⟨w₁, s₁, hs₁, h₁⟩ := hle hr
  obtain ⟨w₂, s₂, hs₂, h₂⟩ := hle hs
  have hr0 : r ≠ 0 := by rintro rfl; simp at hz
  have hs0 : s ≠ 0 := by rintro rfl; simp at hz
  refine ⟨s₂ • w₁, s₁ • w₂, ?_, ?_⟩
  · rw [Psi_smul, ← h₂]
    exact mul_ne_zero (by simpa using hs₁) (mul_ne_zero hs0 (by simpa using hs₂))
  · rw [Psi_smul, Psi_smul, ← h₁, ← h₂]
    field_simp


end
end Dubon2026.SourceCurve.ConstantField
