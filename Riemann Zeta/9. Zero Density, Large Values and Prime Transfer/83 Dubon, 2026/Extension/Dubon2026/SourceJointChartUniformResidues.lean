import Dubon2026.SourceJointChartDimensionAssembly
import Dubon2026.SourceJointChartWeightedSpans

/-! DUB-17/18 -> Kummer power lifting -> genus inequality. The constructed
Kummer reductions all have the same actual residue function field and
coordinate. Specializing the proved joint inequality to this uniform family
identifies its sum of pole-space dimensions with the number of reductions
times the dimension on that residue curve. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
noncomputable section
open IsLocalRing

theorem eventual_uniform_residue_chart_dimension
    {L F : Type*} [Field L] (A : ValuationSubring L) [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (B : Type*) [Field B] [Algebra (ResidueField A) B]
    (R : ι → RegularProlongation A F B) (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers) (hf0 : f ≠ 0)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (y : B) (hy : Transcendental (ResidueField A) y)
    (hres : ∀ i, (R i).residue ⟨f, hf i⟩ = y)
    [FiniteDimensional (IntermediateField.adjoin (ResidueField A) ({y} : Set B)) B]
    [∀ D : Divisor (ResidueField A) B, FiniteDimensional (ResidueField A) ↥(LSpace D)]
    (heq : Fintype.card ι * Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({y} : Set B)) B =
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (D D' : Divisor (ResidueField A) B)
    (hD : ∀ w : Place (ResidueField A) B, D w = max 0 (-w.ord y))
    (hD' : ∀ w : Place (ResidueField A) B, D' w = max 0 (-w.ord y⁻¹))
    (hgen : ∃ Mi : ℕ, ∀ h : B,
      (∀ w : Place (ResidueField A) B, 0 ≤ w.ord y → 0 ≤ w.ord h) →
        h ∈ Submodule.span (ResidueField A) {g : B | ∃ j : ℕ,
          ∃ z ∈ LSpace (Mi • D), g = y ^ j * z})
    (hgen' : ∃ Mi : ℕ, ∀ h : B,
      (∀ w : Place (ResidueField A) B, 0 ≤ w.ord y⁻¹ → 0 ≤ w.ord h) →
        h ∈ Submodule.span (ResidueField A) {g : B | ∃ j : ℕ,
          ∃ z ∈ LSpace (Mi • D'), g = (y⁻¹) ^ j * z}) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FiniteDimensional (ResidueField A) ↥(ST (Fb := fun _ : ι => B) R f ⊓
        weightedST (Fb := fun _ : ι => B) R f M) ∧
      Module.finrank (ResidueField A) ↥(ST (Fb := fun _ : ι => B) R f ⊓
        weightedST (Fb := fun _ : ι => B) R f M) + Fintype.card ι ≤
      Fintype.card ι * Module.finrank (ResidueField A) ↥(LSpace (M • D)) +
        Module.finrank (ResidueField A) ↥(ST (Fb := fun _ : ι => B) R f ⊓ ST R f⁻¹) := by
  classical
  letI (i : ι) : FiniteDimensional (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set B)) B := by rw [hres]; infer_instance
  have htr (i : ι) : Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩) := by
    rw [hres]; exact hy
  have heq' : ∑ i : ι, Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set B)) B =
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
    calc
      _ = ∑ _i : ι, Module.finrank
          (IntermediateField.adjoin (ResidueField A) ({y} : Set B)) B := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hres]
      _ = _ := by
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using heq
  have hD₁ (i : ι) (w : Place (ResidueField A) B) :
      D w = max 0 (-w.ord ((R i).residue ⟨f, hf i⟩)) := by rw [hres]; exact hD w
  have hD₂ (i : ι) (w : Place (ResidueField A) B) :
      D' w = max 0 (-w.ord (((R i).residue ⟨f, hf i⟩)⁻¹)) := by rw [hres]; exact hD' w
  have hgen₁ (i : ι) := hgen
  have hgen₂ (i : ι) := hgen'
  have hy0 : ∀ _i : ι, y ≠ 0 := fun _ => ne_zero_of_transcendental hy
  obtain ⟨M₀, hM₀⟩ := @eventual_residue_chart_dimension L inferInstance A F inferInstance
    inferInstance ι inferInstance (fun _ => B) (fun _ => inferInstance) (fun _ => inferInstance)
    R hR f hf inferInstance htr (fun _ => inferInstance) (fun _ _ => inferInstance) heq'
    (fun _ => D) hD₁ (fun _ => D') hD₂
    (fun i => by rw [hres]; exact hgen₁ i) (fun i => by rw [hres]; exact hgen₂ i)
    (fun _ => y) hres hy0
  refine ⟨M₀, fun M hM => ?_⟩
  have he := hM₀ M hM
  rw [← weightedST_eq_map (Fb := fun _ : ι => B) R f hf hf0 (fun _ => y) hy0 hres M] at he
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using he

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
