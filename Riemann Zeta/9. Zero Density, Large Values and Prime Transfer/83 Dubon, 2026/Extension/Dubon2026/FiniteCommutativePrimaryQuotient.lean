import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.PGroup

/-! # The maximal primary quotient for the actual auxiliary family

BLGG Section 3.6 uses the maximal coefficient-primary quotient of a
finite product of original residue-unit groups. The power-image quotient
and its universal property work directly for that finite commutative
group, without choosing a decomposition into abstract cyclic models.
-/

namespace Dubon2026

noncomputable section

variable (G : Type*) [CommGroup G] [Finite G]

/-- The original group's primary-power image is the kernel of its primary quotient. -/
def finiteCommutativePrimaryKernel (q : ℕ) : Subgroup G :=
  (powMonoidHom (α := G) (q ^ (Nat.card G).factorization q)).range

/-- The literal primary-power quotient of the original auxiliary group. -/
abbrev FiniteCommutativePrimaryQuotient (q : ℕ) :=
  G ⧸ finiteCommutativePrimaryKernel G q

omit [Finite G] in
/-- Every element of the actual quotient is killed by one common coefficient-prime power. -/
theorem finiteCommutativePrimaryQuotient_isPGroup (q : ℕ) :
    IsPGroup q (FiniteCommutativePrimaryQuotient G q) := by
  intro d
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (finiteCommutativePrimaryKernel G q) d
  refine ⟨(Nat.card G).factorization q, ?_⟩
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩

/-- Every map to a coefficient-primary group factors uniquely through the actual quotient. -/
theorem finiteCommutativePrimaryQuotient_unique_factor (q : ℕ) [Fact q.Prime]
    {H : Type*} [Group H] (hH : IsPGroup q H) (θ : G →* H) :
    ∃! η : FiniteCommutativePrimaryQuotient G q →* H,
      η.comp (QuotientGroup.mk' (finiteCommutativePrimaryKernel G q)) = θ := by
  let N := finiteCommutativePrimaryKernel G q
  have hker : N ≤ θ.ker := by
    rintro y ⟨x, rfl⟩
    obtain ⟨m, hm⟩ := hH (θ (x ^ (q ^ (Nat.card G).factorization q)))
    have hN : θ (x ^ (q ^ (Nat.card G).factorization q)) ^
        (Nat.card G / q ^ (Nat.card G).factorization q) = 1 := by
      rw [← map_pow, ← pow_mul, Nat.mul_div_cancel' (Nat.ordProj_dvd (Nat.card G) q),
        pow_card_eq_one', map_one]
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes
      ((Nat.coprime_ordCompl (Fact.out : q.Prime) (Nat.card_pos.ne' : Nat.card G ≠ 0)).pow_left m)
      (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hN)
  let η := QuotientGroup.lift N θ hker
  refine ⟨η, rfl, ?_⟩
  intro η' hη'
  apply MonoidHom.ext
  intro u
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N u
  exact DFunLike.congr_fun hη' x

end
end Dubon2026
