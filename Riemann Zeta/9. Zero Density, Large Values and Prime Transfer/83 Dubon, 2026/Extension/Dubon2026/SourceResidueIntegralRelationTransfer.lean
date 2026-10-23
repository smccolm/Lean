import Dubon2026.SourceResiduePrimitiveCoefficientScale

/-! DUB-17/18 -> original Frobenius/inertia -> actual good/place reduction
-> coefficient specialization of the modular divisor field. Finite polynomial
relations are scaled so one coefficient is a unit and then reduced literally.
The all-level degree consumer will supply independence of powers of j_N,
so an integral Laurent member specializes into the residue modular field.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, coefficient specialization proof.
No specialization or independence premise is hidden in these constructions. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial

theorem integral_polynomial_relation_specializes {L : Type*} [Field L]
    (A : ValuationSubring L) {ι : Type*} [Fintype ι] (x : ι → LaurentSeries A) (c : ι → L[X])
    (hc : ∃ i, c i ≠ 0)
    (hrel : ∑ i, aeval (jqModC L) (c i) * coeffMap A.subtype (x i) = 0) :
    ∃ C : ι → (IsLocalRing.ResidueField A)[X], (∃ i, C i ≠ 0) ∧
      ∑ i, aeval (jqModC (IsLocalRing.ResidueField A)) (C i) * coeffMap (IsLocalRing.residue A) (x i) = 0 := by
  classical

  set s : Finset L := Finset.univ.biUnion (fun i => (c i).coeffs) with hs_def
  have hs : ∃ a ∈ s, a ≠ 0 := by
    obtain ⟨i, hi⟩ := hc
    obtain ⟨n, hn⟩ : ∃ n, (c i).coeff n ≠ 0 := by
      by_contra h
      push Not at h
      exact hi (Polynomial.ext (by simpa using h))
    exact ⟨(c i).coeff n, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, coeff_mem_coeffs hn⟩, hn⟩
  obtain ⟨a, has, ha0, hscale⟩ := exists_primitive_coefficient_scale A s hs

  have hcoeffA : ∀ i n, a⁻¹ * (c i).coeff n ∈ A := by
    intro i n
    by_cases h0 : (c i).coeff n = 0
    · simp [h0]
    exact hscale _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, coeff_mem_coeffs h0⟩)
  have hsub : ∀ i, (↑(Polynomial.C a⁻¹ * c i).coeffs : Set L) ⊆ (A.toSubring : Set L) := by
    intro i z hz
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp (Finset.mem_coe.mp hz)
    rw [Polynomial.coeff_C_mul]
    exact hcoeffA i n
  set Cp : ι → (A : Type _)[X] := fun i => (Polynomial.C a⁻¹ * c i).toSubring A.toSubring (hsub i)
    with hCp_def
  have hCp_map : ∀ i, (Cp i).map A.subtype = Polynomial.C a⁻¹ * c i := fun i =>
    Polynomial.map_toSubring _ _ _

  have hrelA : ∑ i, aeval (jqModC A) (Cp i) * x i = 0 := by
    apply coefficientMap_valuation_subtype_injective A
    rw [map_sum, map_zero]
    simp only [map_mul, coefficientMap_aeval_j, hCp_map, map_mul, Polynomial.aeval_C, mul_assoc]
    rw [← Finset.mul_sum, hrel, mul_zero]
  refine ⟨fun i => (Cp i).map (IsLocalRing.residue A), ?_, ?_⟩
  ·
    obtain ⟨i₀, -, hi₀⟩ := Finset.mem_biUnion.mp has
    obtain ⟨n₀, -, hn₀⟩ := mem_coeffs_iff.mp hi₀
    refine ⟨i₀, fun h => ?_⟩
    have h1 : (Cp i₀).coeff n₀ = 1 := by
      apply Subtype.val_injective
      have := congrArg (fun p : L[X] => p.coeff n₀) (hCp_map i₀)
      simp only [Polynomial.coeff_map] at this
      change ((Cp i₀).coeff n₀ : L) = _ at this
      rw [this, Polynomial.coeff_C_mul, ← hn₀, inv_mul_cancel₀ ha0]
      rfl
    have := congrArg (fun p : (IsLocalRing.ResidueField A)[X] => p.coeff n₀) h
    simp only [Polynomial.coeff_map, h1, map_one, Polynomial.coeff_zero] at this
    exact one_ne_zero this
  · have := congrArg (coeffMap (IsLocalRing.residue A)) hrelA
    rw [map_sum, map_zero] at this
    simpa only [map_mul, coefficientMap_aeval_j] using this

end
end Dubon2026.SourceFunctionField
