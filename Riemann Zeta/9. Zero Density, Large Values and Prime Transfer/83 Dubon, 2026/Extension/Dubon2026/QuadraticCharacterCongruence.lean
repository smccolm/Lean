import Dubon2026.FiniteAdeleIntegerIdealBasis
import Dubon2026.CompactRingUnitCongruence
import Dubon2026.FiniteAdeleResidueUnits
import Mathlib.Analysis.Complex.Basic

/-! # Continuous quadratic characters of the original integral ideles have genuine finite congruence conductor -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Filter Set Topology

/-- The actual kernel of a continuous quadratic character contains an identity neighborhood. -/
theorem continuous_quadratic_character_one_nhds {G : Type*} [Group G] [TopologicalSpace G]
    (ψ : G →* ℂ) (hc : Continuous ψ) (hq : ∀ g, ψ g ^ 2 = 1) :
    {g | ψ g = 1} ∈ 𝓝 (1 : G) := by
  have h1 : {z : ℂ | z ≠ -1} ∈ 𝓝 1 :=
    isClosed_singleton.isOpen_compl.mem_nhds (by norm_num)
  have ht : ContinuousAt ψ (1 : G) := hc.continuousAt
  change Tendsto ψ (𝓝 (1 : G)) (𝓝 (ψ 1)) at ht
  rw [map_one] at ht
  have he : ∀ᶠ g in 𝓝 (1 : G), ψ g ≠ -1 := ht h1
  filter_upwards [he] with g hg
  rcases sq_eq_one_iff.mp (hq g) with hp | hn
  · exact hp
  · exact (hg hn).elim

/-- The original finite-adelic principal ideal condition on an integral element is exactly divisibility in the actual integral subring. -/
theorem finiteAdeleLevelMultiple_subring_iff (D : ℕ) (x : finiteAdeleIntegerSubring) :
    finiteAdeleLevelMultiple D x.val ↔ (D : finiteAdeleIntegerSubring) ∣ x := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩
  · rintro ⟨y, he⟩
    exact ⟨y.val, y.property, congrArg Subtype.val he⟩

/-- Continuity and genuine quadratic values force the original integral-idele character to be trivial on some actual positive residue kernel. -/
theorem integralIdele_quadratic_congruence {ψ : finiteAdeleIntegerSubringˣ →* ℂ}
    (hc : Continuous ψ) (hq : ∀ u, ψ u ^ 2 = 1) :
    ∃ D : ℕ, ∃ hD : 0 < D, ∀ u : finiteAdeleIntegerSubringˣ,
      @finiteAdeleResidue D ⟨ne_of_gt hD⟩ u.val = 1 → ψ u = 1 := by
  letI : CompactSpace finiteAdeleIntegerSubring :=
    isCompact_iff_compactSpace.mp finiteAdeleIntegerSubring_isCompact
  obtain ⟨D, hD, hsmall⟩ := compactRing_unit_congruence_small finiteAdeleIntegerSubring_int_dense
    _ (continuous_quadratic_character_one_nhds ψ hc hq)
  letI : NeZero D := ⟨ne_of_gt hD⟩
  refine ⟨D, hD, ?_⟩
  intro u hu
  apply hsmall u
  apply (finiteAdeleLevelMultiple_subring_iff D (u.val - 1)).mp
  have h := finiteAdeleResidue_eq_intCast_iff D u.val 1
  simp only [Int.cast_one] at h
  exact h.mp hu

end
end Dubon2026
