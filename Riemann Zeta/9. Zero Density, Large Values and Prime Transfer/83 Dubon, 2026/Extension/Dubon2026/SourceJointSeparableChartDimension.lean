import Dubon2026.SourceCurveSeparatingGenusMaximum
import Dubon2026.SourceJointChartUniformResidues
import Dubon2026.SourceSeparableCoordinateChartGeneration

/-! DUB-17/18 -> original Gamma1 Picard torsion injectivity -> the Kummer
residue genus inequality. Separability of the actual residue coordinate
discharges both finite chart-generation hypotheses of the native joint
dimension inequality. This isolates that mathematical composition from the
coefficient-field elaboration in its original-Gamma1 consumer. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
noncomputable section
open IsLocalRing IntermediateField

theorem eventual_chart_dimension_of_separating_residue_coordinate
    {L E : Type*} [Field L] (A : ValuationSubring L)
    [Field E] [Algebra L E] [IsAlgClosed (ResidueField A)]
    {ι : Type*} [Fintype ι] (B : Type*) [Field B] [Algebra (ResidueField A) B]
    (S : ι → RegularProlongation A E B)
    (hSinj : Function.Injective fun i => (S i).integers)
    (t : E) (ht : ∀ i, t ∈ (S i).integers) (ht0 : t ≠ 0)
    [FiniteDimensional L⟮t⟯ E]
    (y : B) (hy : Transcendental (ResidueField A) y)
    (hres : ∀ i, (S i).residue ⟨t, ht i⟩ = y)
    [FiniteDimensional (ResidueField A)⟮y⟯ B]
    [Algebra.IsSeparable (ResidueField A)⟮y⟯ B]
    (heq : Fintype.card ι * Module.finrank (ResidueField A)⟮y⟯ B =
      Module.finrank L⟮t⟯ E)
    (D : Divisor (ResidueField A) B) (hD : ∀ v, D v = max 0 (-v.ord y)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      FiniteDimensional (ResidueField A) ↥(ST (Fb := fun _ : ι => B) S t ⊓
        weightedST (Fb := fun _ : ι => B) S t m) ∧
      Module.finrank (ResidueField A) ↥(ST (Fb := fun _ : ι => B) S t ⊓
        weightedST (Fb := fun _ : ι => B) S t m) + Fintype.card ι ≤
        Fintype.card ι * Module.finrank (ResidueField A) ↥(LSpace (m • D)) +
          Module.finrank (ResidueField A) ↥(ST (Fb := fun _ : ι => B) S t ⊓ ST S t⁻¹) := by
  classical
  have hsupport := finite_function_support_of_separating_coordinate y hy y
  have heD : D = poleDivisor y hsupport := by
    ext v
    rw [hD]
    exact max_comm _ _
  have hg := exists_pole_space_generating_window_of_separating_coordinate y hy hsupport
  rw [← heD] at hg
  haveI : FiniteDimensional (ResidueField A)⟮y⁻¹⟯ B := by
    rw [adjoin_singleton_inv_eq]
    infer_instance
  haveI : Algebra.IsSeparable (ResidueField A)⟮y⁻¹⟯ B := by
    rw [adjoin_singleton_inv_eq]
    infer_instance
  have hyi : Transcendental (ResidueField A) y⁻¹ := fun h => hy (IsAlgebraic.inv_iff.mp h)
  have hsupporti := finite_function_support_of_separating_coordinate y hy y⁻¹
  let Di := poleDivisor y⁻¹ hsupporti
  have hgi := exists_pole_space_generating_window_of_separating_coordinate y⁻¹ hyi hsupporti
  haveI (D : Divisor (ResidueField A) B) := finite_lSpace_of_separating_coordinate y hy D
  exact eventual_uniform_residue_chart_dimension A B S hSinj t ht ht0 y hy hres
    heq D Di hD (fun _ => max_comm _ _) hg hgi

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
