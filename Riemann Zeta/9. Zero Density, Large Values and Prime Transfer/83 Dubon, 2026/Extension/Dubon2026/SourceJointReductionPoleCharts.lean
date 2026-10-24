import Dubon2026.SourceReductionPoleCharts
import Mathlib.RingTheory.Valuation.Integral

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
sum-of-genera inequality -> comparison of the two coordinate charts.
The existing pole-space integrality theorem gives both chart bounds.
Native integral closedness of valuation rings replaces a separate proof
classifying every constant-trivial valuation as a discrete curve place. -/
namespace Dubon2026.SourceCurve.RegularProlongation.Joint
noncomputable section

theorem mem_valuation_of_integral_chart
    {L F : Type*} [Field L] [Field F] [Algebra L F] {f u : F}
    (hu : IsIntegral (Algebra.adjoin L ({f} : Set F)) u)
    (V : ValuationSubring F) (hV : ∀ a : L, algebraMap L F a ∈ V) (hf : f ∈ V) :
    u ∈ V := by
  let S : Subalgebra L F :=
    { V.toSubring with algebraMap_mem' := hV }
  have hle : Algebra.adjoin L ({f} : Set F) ≤ S :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hf)
  let g : Algebra.adjoin L ({f} : Set F) →+* V :=
    { toFun := fun x => ⟨x, hle x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hi : IsIntegral V u := hu.map_of_comp_eq g (RingHom.id F) rfl
  obtain ⟨x, hx⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := F)).mp hi
  exact hx ▸ x.2

theorem span_residue_pole_space_le_chart_intersection
    {L : Type*} [Field L] [CharZero L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : Transcendental L f)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (D : Divisor L F) (hD : ∀ v : Place L F, D v = max 0 (-v.ord f))
    (M : ℕ) :
    Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          u ∈ LSpace (M • D) ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ≤
      Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
            ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ⊓
        Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
              u * (f ^ M)⁻¹ ∈ V) ∧
            ∀ i, (R i).residue ⟨u, hu i⟩ = h i} := by
  refine le_inf (Submodule.span_mono ?_) (Submodule.span_mono ?_)
  · rintro h ⟨u, hu, huL, hres⟩
    exact ⟨u, hu, mem_valuation_of_integral_chart
      (integral_charts_of_pole_bound f hf D hD M huL).1, hres⟩
  · rintro h ⟨u, hu, huL, hres⟩
    exact ⟨u, hu, mem_valuation_of_integral_chart
      (integral_charts_of_pole_bound f hf D hD M huL).2, hres⟩

end
end Dubon2026.SourceCurve.RegularProlongation.Joint
