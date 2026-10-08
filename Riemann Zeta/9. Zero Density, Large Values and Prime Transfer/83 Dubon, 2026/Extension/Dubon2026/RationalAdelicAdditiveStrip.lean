import Dubon2026.FiniteAdeleIntegralCompact

/-! # Actual compact additive representatives for principal rational adeles -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Set

/-- The literal half-open real unit strip with every finite coordinate integral. -/
def rationalAdeleAdditiveStrip : Set (AdeleRing ℤ ℚ) :=
  rationalAdeleRealFiniteRingEquiv ⁻¹'
    (Ico (0 : ℝ) 1 ×ˢ (finiteAdeleIntegerSubring : Set (FiniteAdeleRing ℤ ℚ)))

/-- The actual closed real unit strip times the compact finite integral adeles. -/
def rationalAdeleCompactStrip : Set (AdeleRing ℤ ℚ) :=
  rationalAdeleRealFiniteRingEquiv.symm ''
    (Icc (0 : ℝ) 1 ×ˢ (finiteAdeleIntegerSubring : Set (FiniteAdeleRing ℤ ℚ)))

/-- The original closed strip is genuinely compact in the canonical full adele topology. -/
theorem rationalAdeleCompactStrip_isCompact : IsCompact rationalAdeleCompactStrip :=
  (isCompact_Icc.prod finiteAdeleIntegerSubring_isCompact).image
    rationalAdeleRealFiniteRingEquiv_symm_continuous

/-- The literal half-open strip lies inside the actual compact strip. -/
theorem rationalAdeleAdditiveStrip_subset_compact :
    rationalAdeleAdditiveStrip ⊆ rationalAdeleCompactStrip := by
  intro x hx
  refine ⟨rationalAdeleRealFiniteRingEquiv x, ⟨⟨hx.1.1, hx.1.2.le⟩, hx.2⟩, ?_⟩
  exact rationalAdeleRealFiniteRingEquiv.symm_apply_apply x

/-- Every original adele has an actual principal rational translate in the half-open strip. -/
theorem rationalAdeleAdditiveStrip_covers (x : AdeleRing ℤ ℚ) :
    ∃ q : ℚ, x - algebraMap ℚ (AdeleRing ℤ ℚ) q ∈ rationalAdeleAdditiveStrip :=
  rationalAdele_exists_integral_representative x

/-- Two actual points in the half-open strip cannot differ by a nonzero principal rational adele. -/
theorem rationalAdeleAdditiveStrip_unique {x y : AdeleRing ℤ ℚ}
    (hx : x ∈ rationalAdeleAdditiveStrip) (hy : y ∈ rationalAdeleAdditiveStrip)
    {q : ℚ} (hxy : x - y = algebraMap ℚ (AdeleRing ℤ ℚ) q) : q = 0 := by
  have he := congrArg rationalAdeleRealFiniteRingEquiv hxy
  rw [map_sub, rationalAdeleRealFiniteRingEquiv_algebraMap] at he
  have hf := congrArg Prod.snd he
  change (rationalAdeleRealFiniteRingEquiv x).2 - (rationalAdeleRealFiniteRingEquiv y).2 =
    algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q at hf
  have hi : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q ∈ finiteAdeleIntegerSubring := by
    rw [← hf]
    exact finiteAdeleIntegerSubring.sub_mem hx.2 hy.2
  obtain ⟨n, hn⟩ := (finiteAdele_rational_integral_iff q).mp hi
  have hr := congrArg Prod.fst he
  change (rationalAdeleRealFiniteRingEquiv x).1 - (rationalAdeleRealFiniteRingEquiv y).1 =
    (q : ℝ) at hr
  have hnr : (n : ℝ) = (q : ℝ) := by exact_mod_cast hn
  have hlt : (n : ℝ) < 1 := by linarith [hx.1.2, hy.1.1]
  have hgt : (-1 : ℝ) < n := by linarith [hx.1.1, hy.1.2]
  have hnlt : n < 1 := by exact_mod_cast hlt
  have hngt : (-1 : ℤ) < n := by exact_mod_cast hgt
  have hnz : n = 0 := by omega
  simpa only [hnz, Int.cast_zero] using hn.symm

end
end Dubon2026
