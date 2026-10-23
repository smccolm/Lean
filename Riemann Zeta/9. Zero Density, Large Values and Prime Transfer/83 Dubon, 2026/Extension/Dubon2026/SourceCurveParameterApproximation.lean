import Dubon2026.SourceCurveParameterPoles
import Dubon2026.SourceCurvePlaceCenters

/-! A specified order-one coordinate clears poles and removes one pole
coefficient by the actual residue map. These are the finite principal-part
steps needed to compute rational-field Tate residues in every characteristic,
and hence the DUB-17/18 global residue theorem. -/

namespace Dubon2026.SourceCurve.Place
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
  {t : F}

/-- Successive pure poles differ by one multiplication by the specified parameter. -/
theorem parameter_pow_mul_neg_pow (ht : v.ord t = 1) (n : ℕ) :
    t ^ n * t ^ (-(n + 1 : ℤ)) = t⁻¹ := by
  rw [← zpow_natCast, ← zpow_add₀ (v.parameter_ne_zero ht)]
  have he : (n : ℤ) + -(n + 1 : ℤ) = -1 := by omega
  rw [he, zpow_neg_one]

/-- The specified parameter clears every pole at the actual place. -/
theorem parameter_clear_pole_mem (ht : v.ord t = 1) (f : F) :
    t ^ (-v.ord f).toNat * f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  apply v.mem_of_ord_nonneg
  rw [v.ord_mul (pow_ne_zero _ (v.parameter_ne_zero ht)) hf,
    ← zpow_natCast, v.ord_zpow, ht, mul_one]
  omega

/-- The actual residue map removes the simple pole in the specified parameter. -/
theorem exists_integral_sub_parameterPole (ht : v.ord t = 1)
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    (f : F) (hf : t * f ∈ v.toValuationSubring) :
    ∃ c : K, f - c • t⁻¹ ∈ v.toValuationSubring := by
  obtain ⟨c, hc⟩ := hres (IsLocalRing.residue _ ⟨t * f, hf⟩)
  refine ⟨c, ?_⟩
  let b : v.toValuationSubring := ⟨t * f, hf⟩ - algebraMap K v.toValuationSubring c
  have hb : IsLocalRing.residue _ b = 0 := by
    change IsLocalRing.residue _ (⟨t * f, hf⟩ - algebraMap K v.toValuationSubring c) = 0
    rw [map_sub]
    change IsLocalRing.residue _ ⟨t * f, hf⟩ - algebraMap K v.ResidueField c = 0
    exact sub_eq_zero.mpr hc.symm
  have hbmem := (IsLocalRing.residue_eq_zero_iff b).mp hb
  have he : f - c • t⁻¹ = (b : F) * t⁻¹ := by
    change f - c • t⁻¹ = (t * f - algebraMap K F c) * t⁻¹
    rw [Algebra.smul_def, sub_mul, mul_right_comm t f, mul_inv_cancel₀ (v.parameter_ne_zero ht),
      one_mul]
  rw [he]
  by_cases hb0 : (b : F) = 0
  · rw [hb0, zero_mul]
    exact zero_mem _
  apply v.mem_of_ord_nonneg
  rw [v.ord_mul hb0 (inv_ne_zero (v.parameter_ne_zero ht)), v.ord_inv, ht]
  have hpos := (v.mem_maximalIdeal_iff_ord_pos hb0 b.2).mp hbmem
  omega

end
end Dubon2026.SourceCurve.Place
