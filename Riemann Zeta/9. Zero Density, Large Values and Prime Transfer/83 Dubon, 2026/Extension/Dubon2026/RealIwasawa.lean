import Dubon2026.RealCompactWeight

/-! # The genuine real-group Iwasawa coordinates and their topology -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

/-- The actual compact coordinate left after taking the canonical section of the original orbit point. -/
def realIwasawaCompact (g : SL(2, ℝ)) : realCompactSubgroup :=
  ⟨(g • I).toSL2R⁻¹ * g, by
    change ((g • I).toSL2R⁻¹ * g) • I = I
    rw [mul_smul, inv_smul_eq_iff, toSL2R_smul_I]⟩

/-- The explicit classical section and genuine compact coordinate recover the original group element. -/
theorem realIwasawa_reconstruct (g : SL(2, ℝ)) :
    (g • I).toSL2R * (realIwasawaCompact g).val = g := by
  simp [realIwasawaCompact]

/-- Multiplying the canonical section by a compact stabilizer has the original base point as orbit coordinate. -/
theorem realIwasawa_orbit (z : ℍ) (h : realCompactSubgroup) :
    (z.toSL2R * h.val) • I = z := by
  rw [mul_smul, show h.val • I = I from h.property, toSL2R_smul_I]

/-- The genuine Iwasawa coordinates are unique for the explicit section. -/
theorem realIwasawa_compact_section (z : ℍ) (h : realCompactSubgroup) :
    realIwasawaCompact (z.toSL2R * h.val) = h := by
  apply Subtype.ext
  change (((z.toSL2R * h.val) • I).toSL2R)⁻¹ * (z.toSL2R * h.val) = h.val
  rw [realIwasawa_orbit]
  simp

/-- The original compact coordinate depends continuously on the actual real-group element. -/
theorem realIwasawaCompact_continuous : Continuous realIwasawaCompact := by
  apply Continuous.subtype_mk
  exact ((continuous_toSL2R.comp (by fun_prop : Continuous (fun g : SL(2, ℝ) => g • I))).inv).mul
    continuous_id

/-- The actual real-group Iwasawa decomposition is a homeomorphism with the upper-half-plane and its compact stabilizer. -/
def realIwasawaHomeomorph : SL(2, ℝ) ≃ₜ ℍ × realCompactSubgroup where
  toFun g := (g • I, realIwasawaCompact g)
  invFun p := p.1.toSL2R * p.2.val
  left_inv := realIwasawa_reconstruct
  right_inv p := Prod.ext (realIwasawa_orbit p.1 p.2) (realIwasawa_compact_section p.1 p.2)
  continuous_toFun := (by fun_prop : Continuous (fun g : SL(2, ℝ) => g • I)).prodMk
    realIwasawaCompact_continuous
  continuous_invFun := (continuous_toSL2R.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

/-- The original lift in actual Iwasawa coordinates has precisely the original classical value, height and compact character. -/
theorem realWeightLift_iwasawa (k : ℤ) (f : ℍ → ℂ) (g : SL(2, ℝ)) :
    realWeightLift k f g = f (g • I) * ((Real.sqrt (g • I).im : ℝ) : ℂ) ^ k *
      (realCompactWeight k (realIwasawaCompact g) : ℂ) := by
  have hh := realWeightLift_right_stabilizer k f (g • I).toSL2R
    (realIwasawaCompact g).val (realIwasawaCompact g).property
  rw [realIwasawa_reconstruct, realWeightLift_section] at hh
  exact hh

end
end Dubon2026
