import Dubon2026.RationalAdelicAdditiveStrip
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-! # The genuine compact additive quotient by principal rational adeles -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Set

/-- The actual canonical additive adele group modulo its original principal rational subgroup. -/
abbrev RationalAdelicAdditiveQuotient :=
  AdeleRing ℤ ℚ ⧸ AdeleRing.principalSubgroup ℤ ℚ

/-- The literal compact real/integral strip covers the genuine additive quotient. -/
theorem rationalAdeleCompactStrip_quotient_image :
    (QuotientAddGroup.mk : AdeleRing ℤ ℚ → RationalAdelicAdditiveQuotient) ''
      rationalAdeleCompactStrip = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨q, hq⟩ := rationalAdeleAdditiveStrip_covers x
  refine ⟨x - algebraMap ℚ (AdeleRing ℤ ℚ) q,
    rationalAdeleAdditiveStrip_subset_compact hq, ?_⟩
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change x - algebraMap ℚ (AdeleRing ℤ ℚ) q - x ∈ AdeleRing.principalSubgroup ℤ ℚ
  have he : x - algebraMap ℚ (AdeleRing ℤ ℚ) q - x =
      algebraMap ℚ (AdeleRing ℤ ℚ) (-q) := by rw [map_neg]; abel
  rw [he]
  exact ⟨-q, rfl⟩

/-- Compactness is proved for the original additive adele quotient, rather than supplied as an input. -/
theorem rationalAdelicAdditiveQuotient_compactSpace : CompactSpace RationalAdelicAdditiveQuotient := by
  apply isCompact_univ_iff.mp
  rw [← rationalAdeleCompactStrip_quotient_image]
  exact rationalAdeleCompactStrip_isCompact.image QuotientAddGroup.continuous_mk

/-- The actual principal rational subgroup is discrete in the canonical full adele topology. -/
theorem rationalAdelePrincipal_discreteTopology :
    DiscreteTopology (AdeleRing.principalSubgroup ℤ ℚ) := by
  let H := AdeleRing.principalSubgroup ℤ ℚ
  let F : H → ℝ × FiniteAdeleRing ℤ ℚ := fun x => rationalAdeleRealFiniteRingEquiv x.val
  have hc : Continuous F := rationalAdeleRealFiniteRingEquiv_continuous.comp continuous_subtype_val
  have hopen : IsOpen {x : H | (F x).1 ∈ Ioo (-1 : ℝ) 1 ∧
      (F x).2 ∈ finiteAdeleIntegerSubring} :=
    (isOpen_Ioo.preimage hc.fst).inter (finiteAdeleIntegerSubring_isOpen.preimage hc.snd)
  have he : {x : H | (F x).1 ∈ Ioo (-1 : ℝ) 1 ∧
      (F x).2 ∈ finiteAdeleIntegerSubring} = {0} := by
    ext x
    constructor
    · rintro ⟨hx, hi⟩
      obtain ⟨q, hq⟩ := x.property
      have hf : F x = ((q : ℝ), algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q) := by
        dsimp only [F]
        rw [← hq, rationalAdeleRealFiniteRingEquiv_algebraMap]
      rw [hf] at hx hi
      obtain ⟨n, hn⟩ := (finiteAdele_rational_integral_iff q).mp hi
      have hnr : (n : ℝ) = (q : ℝ) := by exact_mod_cast hn
      have hlt : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith [hx.2])
      have hgt : (-1 : ℤ) < n := by exact_mod_cast (show (-1 : ℝ) < n by linarith [hx.1])
      have hnz : n = 0 := by omega
      have hqz : q = 0 := by simpa only [hnz, Int.cast_zero] using hn.symm
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      simpa only [hqz, map_zero] using hq.symm
    · rintro rfl
      simp [F]
  rw [he] at hopen
  exact discreteTopology_of_isOpen_singleton_zero hopen

end
end Dubon2026
