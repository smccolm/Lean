import Dubon2026.SourceReductionArbitraryFiberEquality

/-! DUB-17/18 -> original Frobenius/inertia -> modular good reduction ->
principal-divisor pushforward. The proved global chart gluing and arbitrary-
function fiber identities give a map whose literal finite-support pushforward
equals the divisor of the reduced function. Finite separating degree and
surjectivity of both integral charts are the narrower geometric inputs;
the subsequent modular consumer derives them for the actual Gauss reduction.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective.
The preceding exact chart-gluing theorem replaces the external repeated
coverage and overlap proof. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
open scoped Classical

private theorem mapDomain_eq_sum_filter {ι κ : Type*} (r : ι → κ) (D : ι →₀ ℤ) (Q : κ) :
    Finsupp.mapDomain r D Q = ∑ P ∈ D.support, if r P = Q then D P else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun P _ => by simp only [Finsupp.single_apply]

theorem exists_principal_divisor_reduction_map
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [HasPrincipalDivisors (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    [Algebra.IsSeparable
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar]
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart :
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h) ∧
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (ResidueField A) {(R.residue x)⁻¹}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)⁻¹}) (f : F) ∧ R.residue f = h)) :
    ∃ r : Place L F → Place (ResidueField A) Fbar,
      ∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) →
        ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f) := by
  classical
  have hx0 : R.residue x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  obtain ⟨ux, hux⟩ := R.isUnit_of_residue_ne_zero hx0
  obtain ⟨xi, hxxi⟩ : ∃ xi : R.integers, x * xi = 1 := ⟨(ux⁻¹ : R.integersˣ), hux ▸ ux.mul_inv⟩
  have hxiF : (xi : F) = (x : F)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by exact_mod_cast congrArg Subtype.val hxxi)
  have hxires : R.residue xi = (R.residue x)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, hxxi, map_one])
  have hx' : Transcendental (ResidueField A) (R.residue xi) := by
    rw [hxires]
    exact fun h => hx (IsAlgebraic.inv_iff.mp h)
  have hadjK : IntermediateField.adjoin (ResidueField A) ({R.residue xi} : Set Fbar) =
      IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar) := by
    rw [hxires, adjoin_singleton_inv_eq]
  have hadjL : IntermediateField.adjoin L ({(xi : F)} : Set F) =
      IntermediateField.adjoin L ({(x : F)} : Set F) := by
    rw [hxiF, adjoin_singleton_inv_eq]
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin (ResidueField A) ({R.residue xi} : Set Fbar)) Fbar := by
    rw [hadjK]
    infer_instance
  have hfin' : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue xi} : Set Fbar)) Fbar := by
    rw [hadjK]
    exact hfin
  have hdeg' : Module.finrank (IntermediateField.adjoin L ({(xi : F)} : Set F)) F =
      Module.finrank (IntermediateField.adjoin (ResidueField A) ({R.residue xi} : Set Fbar)) Fbar := by
    rw [hadjK, hadjL]
    exact hdeg
  have hchart' : ∀ h : Fbar, IsIntegral (Algebra.adjoin (ResidueField A) {R.residue xi}) h →
      ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(xi : F)}) (f : F) ∧ R.residue f = h := by
    rw [hxires, hxiF]
    exact hchart.2
  haveI : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)
  have hres (P : Place L F) : Function.Surjective (algebraMap L P.ResidueField) :=
    (place_residue_bijective_of_finite_coordinate (x : F) P).surjective
  have E₁ : ∀ P : Place L F, ChartDomain A P (x : F) → ∃! Q, ChartReducesTo A R (x : F) P Q :=
    fun P hP => existsUnique_reduction_chart_place R x hx hfin hdeg hchart.1 P hP
  have E₂ : ∀ P : Place L F, ChartDomain A P (xi : F) → ∃! Q, ChartReducesTo A R (xi : F) P Q :=
    fun P hP => existsUnique_reduction_chart_place R xi hx' hfin' hdeg' hchart' P hP
  obtain ⟨r, hr₁, hr₂⟩ := exists_reduction_place_map_of_two_charts R x xi hx0 hxiF hxires hres E₁ E₂
  refine ⟨r, fun f hf D hD Q => ?_⟩
  rw [mapDomain_eq_sum_filter, ← Finset.sum_filter]
  by_cases hQ : R.residue x ∈ Q.toValuationSubring
  · apply sum_fiber_orders_eq_residue_order R x hx hfin hdeg hchart.1 f hf Q hQ D hD
    intro P
    rw [Finset.mem_filter, Finsupp.mem_support_iff, hr₁ P Q hQ]
  · have hQ' : R.residue xi ∈ Q.toValuationSubring := by
      rw [hxires]
      exact (Q.toValuationSubring.mem_or_inv_mem _).resolve_left hQ
    apply sum_fiber_orders_eq_residue_order R xi hx' hfin' hdeg' hchart' f hf Q hQ' D hD
    intro P
    rw [Finset.mem_filter, Finsupp.mem_support_iff, hr₂ P Q hQ]

end
end Dubon2026.SourceCurve.RegularProlongation
