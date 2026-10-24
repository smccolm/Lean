import Dubon2026.SourceKummerReductionCenters

/-! DUB-17/18 -> Picard torsion injectivity -> extending Kummer reductions.
The centered valuations restrict to the original valuation, and distinct
reduced roots give distinct valuations. Unit preservation and the valuation
triangle inequality suffice; no uniqueness or distinctness is assumed. -/
namespace Dubon2026.SourceCurve.RegularProlongation.KummerCenter
noncomputable section
open Polynomial
variable {L F Fbar E : Type*} [Field L] {A : ValuationSubring L}
  [Field F] [Algebra L F] [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
  [Field E] [Algebra F E]
variable {R : RegularProlongation A F Fbar} {α : E} {s : Fbar} {V : ValuationSubring E}

theorem valuation_algebraMap_isUnit (h : KummerCenter R α s V)
    {y : R.integers} (hy : IsUnit y) : V.valuation (algebraMap F E (y : F)) = 1 := by
  let ψ : R.integers →+* V := ((algebraMap F E).comp R.integers.subtype).codRestrict V
    (fun y => h.algebraMap_mem y)
  exact (V.valuation_eq_one_iff (ψ y)).mp (hy.map ψ)

theorem comap_eq (h : KummerCenter R α s V) :
    V.comap (algebraMap F E) = R.integers := by
  ext x
  rw [ValuationSubring.mem_comap]
  refine ⟨fun hx => ?_, fun hx => h.algebraMap_mem ⟨x, hx⟩⟩
  by_contra hxO
  have hxi : x⁻¹ ∈ R.integers := (R.integers.mem_or_inv_mem x).resolve_left hxO
  have hx0 : x ≠ 0 := fun hz => hxO (hz ▸ zero_mem _)
  have hres : R.residue ⟨x⁻¹, hxi⟩ = 0 := by
    by_contra hne
    obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hne
    have hmul : x⁻¹ * ((u⁻¹ : R.integersˣ) : R.integers) = (1 : F) := by
      have hh := congrArg (fun z : R.integers => (z : F)) u.mul_inv
      simpa [hu] using hh
    have hxeq : x = (((u⁻¹ : R.integersˣ) : R.integers) : F) := (inv_mul_eq_one₀ hx0).mp hmul
    exact hxO (hxeq ▸ ((u⁻¹ : R.integersˣ) : R.integers).2)
  have hlt : V.valuation (algebraMap F E x⁻¹) < 1 := by
    simpa using h.vanishes (C ⟨x⁻¹, hxi⟩) (by simpa using hres)
  have hle : V.valuation (algebraMap F E x) ≤ 1 := (V.valuation_le_one_iff _).mpr hx
  have hprod : V.valuation (algebraMap F E x⁻¹) * V.valuation (algebraMap F E x) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hx0, map_one, map_one]
  have hbad : V.valuation (algebraMap F E x⁻¹) * V.valuation (algebraMap F E x) < 1 :=
    lt_of_le_of_lt (by simpa using mul_le_mul_right hle (V.valuation (algebraMap F E x⁻¹))) hlt
  exact hbad.ne hprod

theorem ne_of_residue_ne (hV : KummerCenter R α s V)
    {t : Fbar} {W : ValuationSubring E} (hW : KummerCenter R α t W) (hst : s ≠ t) : V ≠ W := by
  intro heq
  subst W
  obtain ⟨ys, hys⟩ := R.residue_surjective s
  obtain ⟨yt, hyt⟩ := R.residue_surjective t
  have hunit : IsUnit (yt - ys) := R.isUnit_of_residue_ne_zero (by
    rw [map_sub, hyt, hys]
    exact sub_ne_zero.mpr hst.symm)
  have hone := hV.valuation_algebraMap_isUnit hunit
  have hsmall := V.valuation.map_sub_lt (hV.valuation_sub_lt_one hys) (hW.valuation_sub_lt_one hyt)
  have hd : (α - algebraMap F E (ys : F)) - (α - algebraMap F E (yt : F)) =
      algebraMap F E ((yt - ys : R.integers) : F) := by
    change _ = algebraMap F E ((yt : F) - (ys : F))
    rw [map_sub]
    ring
  rw [hd, hone] at hsmall
  exact (lt_irrefl _) hsmall

end
end Dubon2026.SourceCurve.RegularProlongation.KummerCenter
