import Dubon2026.SourceJointReductionSurjectivity
import Dubon2026.SourceJointChartIntegralMultiple
import Dubon2026.SourceJointReductionPolynomialEvaluation
import Dubon2026.SourceJointReductionPoleCharts

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
sum-of-genera inequality -> eventual chart dimension comparison. Every
simultaneous residue vector has a monic polynomial multiple in the residue
chart span. The common lift, integral coordinate multiple, polynomial
normalization and exact residue evaluation are all constructed here. -/
namespace Dubon2026.SourceCurve.RegularProlongation.Joint
noncomputable section
open IsLocalRing Polynomial

theorem exists_monic_residue_chart_multiple
    {L F : Type*} [Field L] (A : ValuationSubring L) [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (hfin : 0 < Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (h : ∀ i, Fb i) :
    ∃ c : Polynomial (ResidueField A), c.Monic ∧
      (fun i => Polynomial.aeval ((R i).residue ⟨f, hf i⟩) c * h i) ∈
        Submodule.span (ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
            ∀ i, (R i).residue ⟨u, hu i⟩ = h i} := by
  classical
  obtain ⟨z, hzO, hzres⟩ := exists_joint_residue_lift R hR h
  obtain ⟨q, hq0, hqT⟩ := exists_integral_chart_residue_polynomial A f hfin z
  set qbar : Polynomial (ResidueField A) := q.map (IsLocalRing.residue A) with hqbar
  have hqbar0 : qbar ≠ 0 := hq0
  set qf : F := q.eval₂ ((algebraMap L F).comp A.subtype) f with hqf
  have hqfO : ∀ i, qf ∈ (R i).integers := fun i => eval₂_mem_integers (R i) q f (hf i)
  have huO : ∀ i, qf * z ∈ (R i).integers := fun i => mul_mem (hqfO i) (hzO i)
  have hures : ∀ i, (R i).residue ⟨qf * z, huO i⟩ =
      Polynomial.aeval ((R i).residue ⟨f, hf i⟩) qbar * h i := by
    intro i
    have he : (⟨qf * z, huO i⟩ : (R i).integers) = ⟨qf, hqfO i⟩ * ⟨z, hzO i⟩ := rfl
    rw [he, map_mul, hzres i, hqbar]
    congr 1
    exact residue_eval₂ (R i) q f (hf i)
  have hmem : (fun i => Polynomial.aeval ((R i).residue ⟨f, hf i⟩) qbar * h i) ∈
      Submodule.span (ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i} :=
    Submodule.subset_span ⟨qf * z, huO, mem_valuation_of_integral_chart hqT, hures⟩
  set lc := qbar.leadingCoeff
  have hlc0 : lc ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hqbar0
  refine ⟨C lc⁻¹ * qbar, ?_, ?_⟩
  · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    exact inv_mul_cancel₀ hlc0
  · have he : (fun i => aeval ((R i).residue ⟨f, hf i⟩) (C lc⁻¹ * qbar) * h i) =
        lc⁻¹ • (fun i => aeval ((R i).residue ⟨f, hf i⟩) qbar * h i) := by
      funext i
      rw [map_mul, aeval_C, Pi.smul_apply, Algebra.smul_def, mul_assoc]
    rw [he]
    exact Submodule.smul_mem _ _ hmem

end
end Dubon2026.SourceCurve.RegularProlongation.Joint
