import Dubon2026.AdicCompleteSimpleRoot
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.Separable

/-! # Splitting of original polynomials from actual simple residue roots -/

namespace Dubon2026
noncomputable section

open Polynomial IsLocalRing

/-- Each original simple residue root lifts to an actual root in the original
complete local ring with the prescribed residue. -/
theorem adicComplete_lift_separable_residue_root
    {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (f : R[X]) (hs : (f.map (residue R)).Separable)
    (x : ResidueField R) (hx : (f.map (residue R)).IsRoot x) :
    ∃ a : R, f.IsRoot a ∧ residue R a = x := by
  obtain ⟨a₀, rfl⟩ := residue_surjective x
  have h₁ : f.eval a₀ ∈ maximalIdeal R := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    simpa only [IsRoot, eval_map_apply] using hx
  have hd : (f.map (residue R)).derivative.eval (residue R a₀) ≠ 0 := by
    simpa only [eval₂_id] using
      hs.eval₂_derivative_ne_zero (RingHom.id _) (by simpa only [eval₂_id] using hx)
  have h₂ : IsUnit (Ideal.Quotient.mk (maximalIdeal R) (f.derivative.eval a₀)) := by
    change IsUnit (residue R (f.derivative.eval a₀))
    apply isUnit_iff_ne_zero.mpr
    simpa only [derivative_map, eval_map_apply] using hd
  obtain ⟨a, ha, har⟩ := adicComplete_polynomial_simple_root
    (maximalIdeal R) f a₀ h₁ h₂
  exact ⟨a, ha, (Ideal.Quotient.mk_eq_mk_iff_sub_mem a a₀).mpr har⟩

/-- All distinct original residue roots lift distinctly. For a monic polynomial
whose residue polynomial is separable and split, their actual count equals its
degree, so the original polynomial itself splits in the original complete ring. -/
theorem adicComplete_polynomial_splits_of_residue
    {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (f : R[X]) (hf : f.Monic)
    (hs : (f.map (residue R)).Separable)
    (hsp : (f.map (residue R)).Splits) : f.Splits := by
  classical
  let S := (f.map (residue R)).roots.toFinset
  have hlift (x : S) : ∃ a : R, f.IsRoot a ∧ residue R a = x.val :=
    adicComplete_lift_separable_residue_root f hs x.val
      (isRoot_of_mem_roots (Multiset.mem_toFinset.mp x.property))
  choose l hl hr using hlift
  have hinj : Function.Injective l := by
    intro x y h
    apply Subtype.ext
    rw [← hr x, ← hr y, h]
  let e : S → f.roots.toFinset := fun x =>
    ⟨l x, Multiset.mem_toFinset.mpr ((mem_roots hf.ne_zero).mpr (hl x))⟩
  have he : Function.Injective e := by
    intro x y h
    exact hinj (congrArg Subtype.val h)
  have hc : S.card ≤ f.roots.toFinset.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective e he
  apply splits_iff_card_roots.mpr
  apply Nat.le_antisymm (card_roots' f)
  calc
    f.natDegree = (f.map (residue R)).natDegree := (hf.natDegree_map _).symm
    _ = (f.map (residue R)).roots.card := hsp.natDegree_eq_card_roots
    _ = S.card := (Multiset.toFinset_card_of_nodup (nodup_roots hs)).symm
    _ ≤ f.roots.toFinset.card := hc
    _ ≤ f.roots.card := Multiset.toFinset_card_le _

end
end Dubon2026
