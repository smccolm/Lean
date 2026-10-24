import Mathlib

/-! The p-primary part of a finite inertia group lies in the kernel of
its residue-unit character. This is the exact counting input for the
DUB-17/18 Galois wild different estimate, used at p=3 and p=2.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois,
hrange and hker_card. Native group cardinality and characteristic-p
power identities supply the proof. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K G : Type*} [Field K] [Group G] [Finite G]
variable (p : ℕ) [Fact p.Prime] [CharP K p] (χ : G →* Kˣ)

theorem residue_unit_character_range_prime_to_char : ¬ p ∣ Nat.card χ.range := by
  letI : Finite χ.range := Finite.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
  intro hdvd
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := χ.range) p hdvd
  obtain ⟨hζp, hζ1⟩ := orderOf_eq_prime_iff.mp hζ
  apply hζ1
  have hval : ((ζ : Kˣ) : K) ^ p = 1 := by
    simpa using congrArg (fun u : χ.range => ((u : Kˣ) : K)) hζp
  have hsub : (((ζ : Kˣ) : K) - 1) ^ p = 0 := by
    rw [sub_pow_char, hval, one_pow, sub_self]
  have hone : ((ζ : Kˣ) : K) = 1 :=
    sub_eq_zero.mp ((pow_eq_zero_iff (Nat.Prime.ne_zero Fact.out)).mp hsub)
  exact Subtype.ext (Units.ext hone)

theorem residue_unit_character_kernel_pow_dvd (a : ℕ) (ha : p ^ a ∣ Nat.card G) :
    p ^ a ∣ Nat.card χ.ker := by
  have hcard : Nat.card χ.ker * Nat.card χ.range = Nat.card G := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hcop : (p ^ a).Coprime (Nat.card χ.range) :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
      (residue_unit_character_range_prime_to_char p χ))
  exact hcop.dvd_of_dvd_mul_right (hcard ▸ ha)

theorem residue_unit_character_kernel_pow_le (a : ℕ) (ha : p ^ a ∣ Nat.card G) :
    p ^ a ≤ Nat.card χ.ker :=
  Nat.le_of_dvd Nat.card_pos (residue_unit_character_kernel_pow_dvd p χ a ha)

end
end Dubon2026.SourceCurve
