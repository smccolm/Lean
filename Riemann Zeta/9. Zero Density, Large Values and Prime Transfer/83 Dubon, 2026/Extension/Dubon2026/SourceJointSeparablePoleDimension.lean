import Dubon2026.SourceJointSeparableConstants
import Dubon2026.SourceJointSeparableChartDimension
import Dubon2026.SourceJointReductionDimension
import Dubon2026.SourceJointReductionPoleCharts
import Dubon2026.SourceResidueClosedValuationField

/-! DUB-17/18 -> original Gamma1 Picard torsion injectivity -> Kummer
power lifting -> residue genus comparison. Separability and equality of
total coordinate degrees supply finite overlap, common constants, joint
residue dimension and finite chart generation. Their composition bounds
the actual original pole space by the residue pole spaces. None of those
four intermediate conclusions is retained as a hypothesis. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
noncomputable section
open IsLocalRing IntermediateField
local notation "Qbar" => AlgebraicClosure ℚ

theorem pole_dimension_bound_of_separating_residue_coordinate
    (A : ValuationSubring Qbar) {E : Type*} [Field E] [Algebra Qbar E]
    (q : ℕ) [NeZero q] (B : Type*) [Field B] [Algebra (ResidueField A) B]
    (S : Fin q → RegularProlongation A E B)
    (hSinj : Function.Injective fun i => (S i).integers)
    (t : E) (ht : ∀ i, t ∈ (S i).integers)
    [FiniteDimensional Qbar⟮t⟯ E]
    (y : B) (hy : Transcendental (ResidueField A) y)
    (hres : ∀ i, (S i).residue ⟨t, ht i⟩ = y)
    [FiniteDimensional (ResidueField A)⟮y⟯ B]
    [Algebra.IsSeparable (ResidueField A)⟮y⟯ B]
    (heq : q * Module.finrank (ResidueField A)⟮y⟯ B = Module.finrank Qbar⟮t⟯ E)
    (D : Divisor Qbar E) (hD : ∀ v, D v = max 0 (-v.ord t))
    (Db : Divisor (ResidueField A) B) (hDb : ∀ v, Db v = max 0 (-v.ord y)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ell (m • D) + q ≤ q * ell (m • Db) + 1 := by
  classical
  haveI := SourceFunctionField.valuation_residue_isAlgClosed A
  have htr (i : Fin q) : Transcendental (ResidueField A) ((S i).residue ⟨t, ht i⟩) := by
    rw [hres]
    exact hy
  have htrL : Transcendental Qbar t :=
    transcendental_of_residue_transcendental (S 0) ⟨t, ht 0⟩ (htr 0)
  letI (i : Fin q) : FiniteDimensional (ResidueField A)⟮(S i).residue ⟨t, ht i⟩⟯ B := by
    rw [hres]
    infer_instance
  letI (i : Fin q) : Algebra.IsSeparable (ResidueField A)⟮(S i).residue ⟨t, ht i⟩⟯ B := by
    rw [hres]
    infer_instance
  have heqS : ∑ i : Fin q, Module.finrank (ResidueField A)⟮(S i).residue ⟨t, ht i⟩⟯ B =
      Module.finrank Qbar⟮t⟯ E := by
    calc
      _ = ∑ _i : Fin q, Module.finrank (ResidueField A)⟮y⟯ B := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hres]
      _ = _ := by simpa using heq
  let U := ST (Fb := fun _ : Fin q => B) S t ⊓ ST S t⁻¹
  have hU : U ≤ Submodule.span (ResidueField A) {(1 : Fin q → B)} := by
    intro h hh
    obtain ⟨c, hc⟩ := JointChartConstants.common_constants_of_separating_residue_coordinates
      A (fun _ : Fin q => B) S hSinj t ht htr heqS h hh.1 hh.2
    have he : h = c • (1 : Fin q → B) := by
      funext i
      simp only [Pi.smul_apply, Pi.one_apply, Algebra.smul_def, mul_one, hc i]
    rw [he]
    exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  have hdimU : Module.finrank (ResidueField A) U ≤ 1 := by
    calc
      _ ≤ Module.finrank (ResidueField A) (Submodule.span (ResidueField A) {(1 : Fin q → B)}) :=
        Submodule.finrank_mono hU
      _ ≤ 1 := by simpa using (finrank_span_le_card ({(1 : Fin q → B)} : Set (Fin q → B)))
  obtain ⟨m₀, hm⟩ := eventual_chart_dimension_of_separating_residue_coordinate
    A B S hSinj t ht (ne_zero_of_transcendental htrL) y hy hres
      (by simpa only [Fintype.card_fin] using heq) Db hDb
  refine ⟨m₀, fun m hmm => ?_⟩
  obtain ⟨hfinite, hcount⟩ := hm m hmm
  letI := hfinite
  letI := finite_lSpace_of_separating_coordinate t htrL (m • D)
  have hdim := @Joint.finrank_joint_residue_span Qbar inferInstance A E
    inferInstance inferInstance (Fin q) inferInstance (fun _ => B)
    (fun _ => inferInstance) (fun _ => inferInstance)
    S hSinj t ht htr inferInstance heqS (fun _ => inferInstance) (LSpace (m • D)) inferInstance
  have hlift := @Joint.span_residue_pole_space_le_chart_intersection
    Qbar inferInstance inferInstance A E inferInstance inferInstance (Fin q)
    (fun _ => B) (fun _ => inferInstance) (fun _ => inferInstance)
    S t htrL inferInstance D hD m
  have hsmall : ell (m • D) ≤ Module.finrank (ResidueField A)
      ↥(ST (Fb := fun _ : Fin q => B) S t ⊓ weightedST (Fb := fun _ : Fin q => B) S t m) := by
    change Module.finrank Qbar (LSpace (m • D)) ≤ _
    rw [← hdim]
    exact Submodule.finrank_mono hlift
  simp only [Fintype.card_fin] at hcount
  change Module.finrank (ResidueField A)
    ↥(ST (Fb := fun _ : Fin q => B) S t ⊓ weightedST (Fb := fun _ : Fin q => B) S t m) + q ≤
      q * ell (m • Db) + Module.finrank (ResidueField A) U at hcount
  omega

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
