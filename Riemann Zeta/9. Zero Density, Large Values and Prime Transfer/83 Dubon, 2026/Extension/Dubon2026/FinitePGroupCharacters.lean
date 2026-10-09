import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Actual prime-order characters detect proper subgroups of finite p-groups -/

namespace Dubon2026

noncomputable section

variable {G : Type*} [Group G] [Finite G]

/-- Every original maximal subgroup of an actual finite p-group is normal. -/
theorem finitePGroup_coatom_normal (p : ℕ) (hp : p.Prime) (hG : IsPGroup p G)
    (M : Subgroup G) (hM : IsCoatom M) : M.Normal := by
  letI : Fact p.Prime := ⟨hp⟩
  letI := hG.isNilpotent
  exact Subgroup.NormalizerCondition.normal_of_coatom M
    Group.normalizerCondition_of_isNilpotent hM

/-- An original normal maximal subgroup of an actual finite p-group has a genuine prime-order quotient. -/
theorem finitePGroup_coatom_quotient_card (p : ℕ) (hp : p.Prime) (hG : IsPGroup p G)
    (M : Subgroup G) [M.Normal] (hM : IsCoatom M) : Nat.card (G ⧸ M) = p := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Nontrivial (G ⧸ M) := QuotientGroup.nontrivial_iff.mpr hM.ne_top
  letI : IsSimpleGroup (G ⧸ M) := by
    constructor
    intro U _
    rcases hM.le_iff.mp (QuotientGroup.le_comap_mk' M U) with htop | heq
    · right
      apply Subgroup.comap_injective (QuotientGroup.mk'_surjective M)
      simpa only [Subgroup.comap_top] using htop
    · left
      apply Subgroup.comap_injective (QuotientGroup.mk'_surjective M)
      change U.comap (QuotientGroup.mk' M) = (QuotientGroup.mk' M).ker
      simpa only [QuotientGroup.ker_mk'] using heq
  have hQ := hG.to_quotient M
  letI := hQ.isNilpotent
  have hprime : (Nat.card (G ⧸ M)).Prime := IsSimpleGroup.prime_card
  have hdiv : p ∣ Nat.card (G ⧸ M) :=
    hQ.card_eq_or_dvd.resolve_left hprime.ne_one
  exact ((Nat.dvd_prime hprime).mp hdiv).resolve_left hp.ne_one |>.symm

/-- Every original proper subgroup of an actual finite p-group is killed by an actual surjective prime-order character. -/
theorem finitePGroup_proper_subgroup_character (p : ℕ) (hp : p.Prime)
    (hG : IsPGroup p G) (K : Subgroup G) (hK : K ≠ ⊤) :
    ∃ f : G →* Multiplicative (ZMod p), Function.Surjective f ∧ K ≤ f.ker := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨M, hM, hKM⟩ := (eq_top_or_exists_le_coatom K).resolve_left hK
  letI : M.Normal := finitePGroup_coatom_normal p hp hG M hM
  have hcard := finitePGroup_coatom_quotient_card p hp hG M hM
  let e : G ⧸ M ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq hcard (by simp)
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' M),
    e.surjective.comp (QuotientGroup.mk'_surjective M), ?_⟩
  intro g hg
  change e (QuotientGroup.mk' M g) = 1
  have hzero : QuotientGroup.mk' M g = 1 :=
    (QuotientGroup.eq_one_iff g).mpr (hKM hg)
  rw [hzero, map_one]

end
end Dubon2026
