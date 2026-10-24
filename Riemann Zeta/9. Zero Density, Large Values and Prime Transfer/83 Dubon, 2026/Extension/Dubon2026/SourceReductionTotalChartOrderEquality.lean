import Dubon2026.SourceIntegralChartCofactor
import Dubon2026.SourceReductionTotalChartOrderBound
import Dubon2026.SourceReductionFactorOrderSum

/-! DUB-17/18 -> modular good reduction -> principal-divisor pushforward ->
equality in each reduction fiber. Total original and residue chart orders
are equal for every integral chart function with nonzero reduction. The
native integral cofactor reduces the reverse inequality to normalized
coordinate factors; their exact degree totals and the proved local-fiber
inequality force equality. No total-order equality is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open scoped Classical
open IsLocalRing Polynomial
variable {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [HasPrincipalDivisors (ResidueField A) Fbar]
local notation "k" => ResidueField A

omit [IsAlgClosed L] [CharZero L] [HasPrincipalDivisors L F]
  [HasPrincipalDivisors (ResidueField A) Fbar] in
private theorem coe_multiset_prod {R : RegularProlongation A F Fbar} (m : Multiset R.integers) :
    ((m.prod : R.integers) : F) = (m.map ((↑) : R.integers → F)).prod :=
  map_multiset_prod R.integers.subtype m

theorem chartOrderSum_eq_residue_chartOrderSum (R : RegularProlongation A F Fbar) (x : R.integers)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar] (hx : Transcendental k (R.residue x))
    (hfin : 0 < Module.finrank (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin k {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hfi : IsIntegral (Algebra.adjoin L {(x : F)}) (f : F))
    (hf : R.residue f ≠ 0) :
    chartOrderSum ((ChartDomain A · (x : F))) (f : F) = chartOrderSum ((fun Q : Place k Fbar => R.residue x ∈ Q.toValuationSubring)) (R.residue f) := by
  have hf0 : (f : F) ≠ 0 := by
    intro h
    apply hf
    rw [show f = 0 from Subtype.ext h, map_zero]

  obtain ⟨g, hgi, c₀, hc₀, hfg⟩ := exists_integral_cofactor hf0 hfi
  have hc₀F : algebraMap (Algebra.adjoin L {(x : F)}) F c₀ = (c₀ : F) := rfl
  rw [hc₀F] at hfg
  obtain ⟨p₁, hp₁⟩ : ∃ p₁ : L[X], aeval (x : F) p₁ = (c₀ : F) := by
    have : (c₀ : F) ∈ (aeval (x : F) : L[X] →ₐ[L] F).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact c₀.2
    exact (AlgHom.mem_range _).mp this
  have hc₀F0 : (c₀ : F) ≠ 0 := fun h => hc₀ (Subtype.ext h)
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    exact hc₀F0 (by rw [← hp₁, map_zero])

  set Φ : R.integers := (p₁.roots.map (normalizedChartFactor R x)).prod with hΦ
  set u : L := p₁.leadingCoeff * (p₁.roots.map (chartFactorScalar A)).prod with hu
  have hu0 : u ≠ 0 := by
    refine mul_ne_zero (leadingCoeff_ne_zero.mpr hp₁0) (Multiset.prod_ne_zero ?_)
    rw [Multiset.mem_map]
    rintro ⟨r, -, hr⟩
    exact chartFactorScalar_ne_zero r hr
  have hfac : (c₀ : F) = algebraMap L F u * (Φ : F) := by
    rw [← hp₁]
    conv_lhs => rw [(IsAlgClosed.splits p₁).eq_prod_roots]
    rw [map_mul, aeval_C, map_multiset_prod, Multiset.map_map]
    have hfun : ((aeval (x : F) : L[X] →ₐ[L] F) ∘ fun r => X - C r) =
        fun r => algebraMap L F (chartFactorScalar A r) * (normalizedChartFactor R x r : F) := by
      funext r
      simp only [Function.comp_apply, map_sub, aeval_X, aeval_C]
      exact sub_eq_scalar_mul_normalizedChartFactor R x r
    rw [hfun, Multiset.prod_map_mul, hu, hΦ, coe_multiset_prod, Multiset.map_map, map_mul,
      map_multiset_prod, Multiset.map_map]
    simp only [Function.comp_def]
    ring

  have hΦ0 : (Φ : F) ≠ 0 := by
    rw [hΦ, coe_multiset_prod, Multiset.map_map]
    refine Multiset.prod_ne_zero ?_
    rw [Multiset.mem_map]
    rintro ⟨r, -, hr⟩
    exact coe_normalizedChartFactor_ne_zero R x hx r hr
  have hresΦ : R.residue Φ = (p₁.roots.map fun r => R.residue (normalizedChartFactor R x r)).prod := by
    rw [hΦ, map_multiset_prod, Multiset.map_map, Function.comp_def]
  have hresΦ0 : R.residue Φ ≠ 0 := by
    rw [hresΦ]
    refine Multiset.prod_ne_zero ?_
    rw [Multiset.mem_map]
    rintro ⟨r, -, hr⟩
    exact residue_normalizedChartFactor_ne_zero R x hx r hr

  obtain ⟨fu, hfu⟩ := R.isUnit_of_residue_ne_zero hf
  set g' : R.integers := ((fu⁻¹ : R.integersˣ) : R.integers) * Φ with hg'
  have hfg' : f * g' = Φ := by
    rw [hg', ← hfu, ← mul_assoc, Units.mul_inv, one_mul]
  have hfg'F : (f : F) * (g' : F) = (Φ : F) := by
    have := congrArg (fun z : R.integers => (z : F)) hfg'
    simpa using this
  have hg'F : (g' : F) = algebraMap L F u⁻¹ * g := by
    apply mul_left_cancel₀ hf0
    rw [hfg'F, mul_left_comm, hfg, hfac, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu0, map_one,
      one_mul]
  have hg'i : IsIntegral (Algebra.adjoin L {(x : F)}) (g' : F) := by
    rw [hg'F]
    have : IsIntegral (Algebra.adjoin L {(x : F)}) (algebraMap L F u⁻¹) := by
      rw [IsScalarTower.algebraMap_apply L (Algebra.adjoin L {(x : F)}) F]
      exact isIntegral_algebraMap
    exact this.mul hgi
  have hresg' : R.residue g' ≠ 0 := by
    intro h
    apply hresΦ0
    rw [← hfg', map_mul, h, mul_zero]
  have hg'0 : (g' : F) ≠ 0 := by
    intro h
    apply hΦ0
    rw [← hfg'F, h, mul_zero]

  have hAf := residue_chartOrderSum_le R x hx hfin hdeg hchart f hfi hf
  have hAg := residue_chartOrderSum_le R x hx hfin hdeg hchart g' hg'i hresg'

  have hΦle : chartOrderSum ((ChartDomain A · (x : F))) (Φ : F) ≤ chartOrderSum ((fun Q : Place k Fbar => R.residue x ∈ Q.toValuationSubring)) (R.residue Φ) := by
    have h1 : chartOrderSum ((ChartDomain A · (x : F))) (Φ : F) =
        (p₁.roots.map fun r => chartOrderSum ((ChartDomain A · (x : F))) (normalizedChartFactor R x r : F)).sum := by
      rw [hΦ, coe_multiset_prod, Multiset.map_map, chartOrderSum_multiset_prod, Multiset.map_map]
      · rfl
      · rw [Multiset.mem_map]
        rintro ⟨r, -, hr⟩
        exact coe_normalizedChartFactor_ne_zero R x hx r hr
    have h2 : chartOrderSum ((fun Q : Place k Fbar => R.residue x ∈ Q.toValuationSubring)) (R.residue Φ) =
        (p₁.roots.map fun r => chartOrderSum ((fun Q : Place k Fbar => R.residue x ∈ Q.toValuationSubring)) (R.residue (normalizedChartFactor R x r))).sum := by
      rw [hresΦ, chartOrderSum_multiset_prod, Multiset.map_map]
      · rfl
      · rw [Multiset.mem_map]
        rintro ⟨r, -, hr⟩
        exact residue_normalizedChartFactor_ne_zero R x hx r hr
    rw [h1, h2]
    exact Multiset.sum_map_le_sum_map _ _ fun r _ => (chartOrderSum_normalizedChartFactor_eq R x hx hfin hdeg r).le

  have hZ : chartOrderSum ((ChartDomain A · (x : F))) (f : F) + chartOrderSum ((ChartDomain A · (x : F))) (g' : F) = chartOrderSum ((ChartDomain A · (x : F))) (Φ : F) := by
    rw [← chartOrderSum_mul _ hf0 hg'0, hfg'F]
  have hZbar : chartOrderSum ((fun Q : Place k Fbar => R.residue x ∈ Q.toValuationSubring)) (R.residue f) + chartOrderSum ((fun Q : Place k Fbar => R.residue x ∈ Q.toValuationSubring)) (R.residue g') =
      chartOrderSum ((fun Q : Place k Fbar => R.residue x ∈ Q.toValuationSubring)) (R.residue Φ) := by
    rw [← chartOrderSum_mul _ hf hresg', ← map_mul, hfg']
  apply le_antisymm
  · linarith
  · exact hAf

end
end Dubon2026.SourceCurve.RegularProlongation
