import Dubon2026.SourceConstantFieldOrderResidues

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> symmetric-power
continuation -> automorphy and residual association -> original weight-two
Frobenius/inertia -> modular good reduction -> reduction-place comparison.
The two proved chart comparisons are glued with their exact finite-chart
fiber descriptions, required by the subsequent principal-divisor identity.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective.
Existing finite-coordinate residue surjectivity supplies actual constant
values; no abstract curve package or place-map certificate is assumed. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

theorem valuation_algebraMap_eq_one (P : Place L F) {c : L} (hc : c ≠ 0) :
    P.toValuationSubring.valuation (algebraMap L F c) = 1 := by
  let u : (P.toValuationSubring)ˣ :=
    ⟨algebraMap L P.toValuationSubring c, algebraMap L P.toValuationSubring c⁻¹,
      by rw [← map_mul, mul_inv_cancel₀ hc, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hc, map_one]⟩
  exact P.toValuationSubring.valuation_unit u

theorem const_unique (P : Place L F) {h : F} {c c' : L}
    (hc : h - algebraMap L F c ∈ P.toValuationSubring.nonunits)
    (hc' : h - algebraMap L F c' ∈ P.toValuationSubring.nonunits) : c = c' := by
  by_contra hne
  rw [ValuationSubring.mem_nonunits_iff] at hc hc'
  have hlt : P.toValuationSubring.valuation (algebraMap L F (c' - c)) < 1 := by
    have : algebraMap L F (c' - c) = (h - algebraMap L F c) + -(h - algebraMap L F c') := by
      rw [map_sub]; ring
    rw [this]
    refine Valuation.map_add_lt _ hc ?_
    rwa [Valuation.map_neg]
  rw [valuation_algebraMap_eq_one P (sub_ne_zero.mpr (Ne.symm hne))] at hlt
  exact lt_irrefl _ hlt

theorem inv_sub_inv_mem_nonunits (P : Place L F) {x : F} {c : L} (hc0 : c ≠ 0)
    (hc : x - algebraMap L F c ∈ P.toValuationSubring.nonunits) :
    x⁻¹ - algebraMap L F c⁻¹ ∈ P.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hc ⊢
  have hvc : P.toValuationSubring.valuation (algebraMap L F c) = 1 :=
    valuation_algebraMap_eq_one P hc0
  have hvx : P.toValuationSubring.valuation x = 1 := by
    have := Valuation.map_add_eq_of_lt_left P.toValuationSubring.valuation
      (x := algebraMap L F c) (y := x - algebraMap L F c) (by rwa [hvc])
    rwa [add_sub_cancel, hvc] at this
  have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero] at hvx; exact zero_ne_one hvx
  have hc0' : algebraMap L F c ≠ 0 := by simpa using hc0
  have heq : x⁻¹ - algebraMap L F c⁻¹ =
      -(x⁻¹ * (algebraMap L F c)⁻¹ * (x - algebraMap L F c)) := by
    rw [map_inv₀]; field_simp; ring
  rw [heq, Valuation.map_neg, map_mul, map_mul, map_inv₀, map_inv₀, hvx, hvc]
  simpa using hc

theorem exists_sub_algebraMap_mem_nonunits (P : Place L F)
    (hres : Function.Surjective (algebraMap L P.ResidueField))
    {h : F} (hh : h ∈ P.toValuationSubring) :
    ∃ c : L, h - algebraMap L F c ∈ P.toValuationSubring.nonunits := by
  obtain ⟨c, hc⟩ := ConstantField.exists_sub_algebraMap_mem_maximalIdeal P hres ⟨h, hh⟩
  exact ⟨c, ValuationSubring.coe_mem_nonunits_iff.mpr hc⟩

theorem exists_inv_sub_mem_nonunits (A : ValuationSubring L)
    (P : Place L F) (hres : Function.Surjective (algebraMap L P.ResidueField)) (x : F)
    (hnot : ¬ ∃ a : A, x - algebraMap L F a ∈ P.toValuationSubring.nonunits) :
    ∃ a : A, x⁻¹ - algebraMap L F a ∈ P.toValuationSubring.nonunits := by
  by_cases hxV : x ∈ P.toValuationSubring
  · obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_nonunits P hres hxV
    have hcA : c ∉ A := fun h => hnot ⟨⟨c, h⟩, hc⟩
    have hc0 : c ≠ 0 := by rintro rfl; exact hcA A.zero_mem
    have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
    exact ⟨⟨c⁻¹, hcinv⟩, inv_sub_inv_mem_nonunits P hc0 hc⟩
  · refine ⟨0, ?_⟩
    have hxinv : x⁻¹ ∈ P.toValuationSubring :=
      (P.toValuationSubring.mem_or_inv_mem x).resolve_left hxV
    rw [show ((0 : A) : L) = 0 from rfl, map_zero, sub_zero, ValuationSubring.mem_nonunits_iff]
    rw [← P.toValuationSubring.valuation_le_one_iff, not_le] at hxV
    have hx0 : x ≠ 0 := by rintro rfl; simp at hxV
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hxV

theorem inv_const_eq (P : Place L F) {x : F} (hx0 : x ≠ 0) {a a' : L}
    (ha : x - algebraMap L F a ∈ P.toValuationSubring.nonunits)
    (ha' : x⁻¹ - algebraMap L F a' ∈ P.toValuationSubring.nonunits) : a ≠ 0 ∧ a' = a⁻¹ := by
  have hmem : x⁻¹ ∈ P.toValuationSubring := by
    have h1 : x⁻¹ - algebraMap L F a' ∈ P.toValuationSubring :=
      ValuationSubring.nonunits_subset ha'
    have h2 : algebraMap L F a' ∈ P.toValuationSubring := P.algebraMap_mem' a'
    simpa using add_mem h1 h2
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero, ValuationSubring.mem_nonunits_iff] at ha
    rw [← P.toValuationSubring.valuation_le_one_iff, map_inv₀] at hmem
    have hvx0 : 0 < P.toValuationSubring.valuation x :=
      zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0)
    exact absurd hmem (not_le.mpr ((one_lt_inv₀ hvx0).mpr ha))
  exact ⟨ha0, const_unique P ha' (inv_sub_inv_mem_nonunits P ha0 ha)⟩

end
end Dubon2026.SourceCurve.Place
