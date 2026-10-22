import Dubon2026.SourceCurvePlaceCenters
import Dubon2026.SourceCurveLocalDifferentials

/-! DUB-17/18 -> principal-divisor descent -> local order noncancellation.
These local identities use the existing exact order/unit and maximal-ideal
criteria. Surjectivity from constants to the residue field is an explicit
upstream input, supplied by the proved original residue-field bijection.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

theorem irreducible_coe_ne_zero {π : w.toValuationSubring} (hπ : Irreducible π) : (π : F) ≠ 0 :=
  fun h => hπ.ne_zero (Subtype.ext h)

theorem ord_coe_isUnit {X : w.toValuationSubring} (h : IsUnit X) : w.ord (X : F) = 0 := by
  obtain ⟨u, rfl⟩ := h
  exact w.ord_coe_unit u

theorem isUnit_of_ord_eq_zero {X : w.toValuationSubring} (h0 : X ≠ 0)
    (h : w.ord (X : F) = 0) : IsUnit X :=
  (w.adicValuation_coe_eq_one_iff X).mp
    ((w.ord_eq_zero_iff_adicValuation_eq_one (fun he => h0 (Subtype.ext he))).mp h)

theorem ord_pos_of_mem_maximalIdeal {X : w.toValuationSubring}
    (hX : X ∈ IsLocalRing.maximalIdeal w.toValuationSubring) (h0 : X ≠ 0) :
    0 < w.ord (X : F) :=
  (w.mem_maximalIdeal_iff_ord_pos (fun he => h0 (Subtype.ext he)) X.property).mp hX

theorem mem_maximalIdeal_of_ord_pos {X : w.toValuationSubring} (h : 0 < w.ord (X : F)) :
    X ∈ IsLocalRing.maximalIdeal w.toValuationSubring := by
  have h0 : (X : F) ≠ 0 := by
    intro he
    rw [he, w.ord_zero] at h
    exact (lt_irrefl 0) h
  exact (w.mem_maximalIdeal_iff_ord_pos h0 X.property).mpr h

omit w in
theorem isUnit_add_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    {X Y : R} (hX : IsUnit X) (hY : Y ∈ IsLocalRing.maximalIdeal R) : IsUnit (X + Y) := by
  by_contra h
  have h1 : X + Y ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
  have h2 : X ∈ IsLocalRing.maximalIdeal R := by simpa only [add_sub_cancel_right] using sub_mem h1 hY
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 hX

theorem exists_sub_algebraMap_mem_maximalIdeal
    (hres : Function.Surjective (algebraMap K w.ResidueField)) (X : w.toValuationSubring) :
    ∃ a : K, X - algebraMap K w.toValuationSubring a ∈ IsLocalRing.maximalIdeal w.toValuationSubring := by
  obtain ⟨a, ha⟩ := hres (IsLocalRing.residue w.toValuationSubring X)
  refine ⟨a, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← ha,
    IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]

end
end Dubon2026.SourceCurve.ConstantField
