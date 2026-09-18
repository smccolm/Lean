import Tao2026.BurgessWeilPrimeKummerOrthogonality
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The Kummer character kernel is a power subgroup

For a multiplicative character `χ` on a finite field, the kernel of its
restriction to the unit group is exactly the image of the
`orderOf χ`-power map.  This identifies the kernel fiber introduced in the
orthogonality layer with the nonzero affine fibers of the Kummer equation.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Evaluation at a generator of the finite-field unit group preserves the
order of a multiplicative character. -/
theorem orderOf_mulChar_toUnitHom_generator
    (F : Type*) [Field F] [Fintype F]
    (χ : MulChar F ℂ) :
    let hcyc : IsCyclic Fˣ := inferInstance
    let g : Fˣ := Classical.choose hcyc.exists_generator
    orderOf (χ.toUnitHom g) = orderOf χ := by
  classical
  dsimp only
  let e := MulChar.equiv_rootsOfUnity F ℂ
  simpa [e, MulChar.equiv_rootsOfUnity] using e.orderOf_eq χ

/-- The image of the unit-group character has cardinality `orderOf χ`. -/
theorem natCard_mulChar_toUnitHom_range
    (F : Type*) [Field F] [Fintype F]
    (χ : MulChar F ℂ) :
    Nat.card χ.toUnitHom.range = orderOf χ := by
  classical
  let hcyc : IsCyclic Fˣ := inferInstance
  let g : Fˣ := Classical.choose hcyc.exists_generator
  have hgmem : ∀ x : Fˣ, x ∈ Subgroup.zpowers g :=
    Classical.choose_spec hcyc.exists_generator
  have hg : Subgroup.zpowers g = ⊤ :=
    (Subgroup.eq_top_iff' (Subgroup.zpowers g)).2 hgmem
  rw [MonoidHom.range_eq_map, ← hg, MonoidHom.map_zpowers,
    Nat.card_zpowers]
  exact orderOf_mulChar_toUnitHom_generator F χ

/-- The kernel of the unit-group character has the expected quotient
cardinality. -/
theorem natCard_mulChar_toUnitHom_ker
    (F : Type*) [Field F] [Fintype F]
    (χ : MulChar F ℂ) :
    Nat.card χ.toUnitHom.ker = Nat.card Fˣ / orderOf χ := by
  have hindex : χ.toUnitHom.ker.index = orderOf χ := by
    rw [Subgroup.index_ker, natCard_mulChar_toUnitHom_range F χ]
  have hmul := χ.toUnitHom.ker.card_mul_index
  rw [hindex] at hmul
  exact Nat.eq_div_of_mul_eq_right χ.orderOf_pos.ne'
    (by simpa [mul_comm] using hmul)

/-- On finite-field units, the character kernel is precisely the image of
the power map with exponent equal to the character order. -/
theorem mulChar_powerRange_eq_ker
    (F : Type*) [Field F] [Fintype F]
    (χ : MulChar F ℂ) :
    (powMonoidHom (orderOf χ) : Fˣ →* Fˣ).range = χ.toUnitHom.ker := by
  classical
  let H := (powMonoidHom (orderOf χ) : Fˣ →* Fˣ).range
  let K := χ.toUnitHom.ker
  have hle : H ≤ K := by
    intro u hu
    rcases hu with ⟨v, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Units.ext
    have hchar := congrArg
      (fun ψ : MulChar F ℂ => ψ (v : F)) (pow_orderOf_eq_one χ)
    change (χ ^ orderOf χ) (v : F) =
      (1 : MulChar F ℂ) (v : F) at hchar
    have hval : χ (v : F) ^ orderOf χ = 1 := by
      calc
        χ (v : F) ^ orderOf χ = (χ ^ orderOf χ) (v : F) :=
          (χ.pow_apply_coe (orderOf χ) v).symm
        _ = (1 : MulChar F ℂ) (v : F) := hchar
        _ = 1 := MulChar.one_apply_coe v
    change χ ((v : F) ^ orderOf χ) = 1
    rw [map_pow]
    exact hval
  have hdiv0 : orderOf χ ∣ Fintype.card F - 1 :=
    MulChar.orderOf_dvd_card_sub_one F χ
  rw [← Fintype.card_units] at hdiv0
  have hdiv : orderOf χ ∣ Nat.card Fˣ := by
    simpa [Nat.card_eq_fintype_card] using hdiv0
  have hcardH : Nat.card H = Nat.card Fˣ / orderOf χ := by
    dsimp [H]
    rw [IsCyclic.card_powMonoidHom_range,
      Nat.gcd_eq_right_iff_dvd.mpr hdiv]
  have hcardK : Nat.card K = Nat.card Fˣ / orderOf χ := by
    exact natCard_mulChar_toUnitHom_ker F χ
  apply SetLike.coe_injective
  apply Set.eq_of_subset_of_ncard_le hle
  · change Nat.card K ≤ Nat.card H
    rw [hcardH, hcardK]

/-- Field-element form of the power-subgroup identity.  A value lies in the
character kernel exactly when it is a nonzero `orderOf χ`-th power. -/
theorem mulChar_apply_eq_one_iff_exists_nonzero_pow_eq
    (F : Type*) [Field F] [Fintype F]
    (χ : MulChar F ℂ) (a : F) :
    χ a = 1 ↔ ∃ y : F, y ≠ 0 ∧ y ^ orderOf χ = a := by
  classical
  constructor
  · intro ha
    have ha0 : a ≠ 0 := by
      intro hzero
      subst a
      rw [χ.map_zero] at ha
      exact zero_ne_one ha
    let u : Fˣ := Units.mk0 a ha0
    have huKer : u ∈ χ.toUnitHom.ker := by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      exact ha
    rw [← mulChar_powerRange_eq_ker F χ] at huKer
    rcases huKer with ⟨v, hv⟩
    refine ⟨(v : F), Units.ne_zero v, ?_⟩
    have hval := congrArg Units.val hv
    simpa [u, powMonoidHom_apply] using hval
  · rintro ⟨y, hy, rfl⟩
    calc
      χ (y ^ orderOf χ) = χ y ^ orderOf χ := map_pow χ y (orderOf χ)
      _ = (χ ^ orderOf χ) y :=
        (χ.pow_apply' χ.orderOf_pos.ne' y).symm
      _ = (1 : MulChar F ℂ) y := by rw [pow_orderOf_eq_one]
      _ = 1 := MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)

end

end Tao2026
