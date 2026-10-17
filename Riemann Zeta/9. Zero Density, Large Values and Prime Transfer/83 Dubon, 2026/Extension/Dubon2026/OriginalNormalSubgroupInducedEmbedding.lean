/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The normal-action calculation adapts the pinned public source
P2M/Sol/S_Rep_exists_hom_ind_injective_exact_of_forall_rho_eq.lean,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2. The implementation uses
the repository's pinned Mathlib adjunction and original representations.
-/
import Mathlib.RepresentationTheory.FiniteIndex

/-! # The actual induced embedding for normal-subgroup relation reduction

DUB-17's remaining relation-extension argument embeds the finite original
coefficient into induction from the actual normal kernel. Pinned finite
index induction/coinduction supplies the map. Finiteness, prime torsion
and trivial kernel action are proved for that actual induced coefficient.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Finite G] (N : Subgroup G) (B : Rep.{0} ℤ G)

/-- The actual adjunction unit into induction from the original subgroup. -/
def originalSubgroupInducedUnit : B ⟶ Rep.ind N.subtype (Rep.res N.subtype B) := by
  classical
  exact (Rep.resIndAdjunction ℤ N).unit.app B

/-- Evaluation at the identity, after the pinned induction/coinduction
isomorphism, proves injectivity of the actual original unit. -/
theorem originalSubgroupInducedUnit_injective :
    Function.Injective (originalSubgroupInducedUnit N B).hom := by
  classical
  let e := Rep.indCoindIso (Rep.res N.subtype B)
  have hi := (Rep.mono_iff_injective e.inv).mp inferInstance
  intro x y hxy
  have h : ((Rep.resCoindAdjunction ℤ N.subtype).unit.app B).hom x =
      ((Rep.resCoindAdjunction ℤ N.subtype).unit.app B).hom y := hi hxy
  have h1 := congrArg (fun f : Rep.coind N.subtype (Rep.res N.subtype B) => f.val 1) h
  change B.ρ 1 x = B.ρ 1 y at h1
  simpa only [map_one, Module.End.one_apply] using h1

/-- Induction of the actual finite coefficient is finite. -/
theorem originalSubgroupInduced_finite [Finite B] :
    Finite (Rep.ind N.subtype (Rep.res N.subtype B)) := by
  classical
  letI : Finite (Rep.coind N.subtype (Rep.res N.subtype B)) :=
    Finite.of_injective (fun f : Rep.coind N.subtype (Rep.res N.subtype B) => f.val)
      Subtype.val_injective
  let e := Rep.indCoindIso (Rep.res N.subtype B)
  exact Finite.of_injective e.hom.hom ((Rep.mono_iff_injective e.hom).mp inferInstance)

/-- Literal prime annihilation passes to the actual induced coefficient. -/
theorem originalSubgroupInduced_nsmul_zero (p : ℕ) (hB : ∀ b : B, p • b = 0)
    (x : Rep.ind N.subtype (Rep.res N.subtype B)) : p • x = 0 := by
  classical
  let e := Rep.indCoindIso (Rep.res N.subtype B)
  apply (Rep.mono_iff_injective e.hom).mp inferInstance
  rw [map_nsmul, map_zero]
  apply Subtype.ext
  funext g
  exact hB ((e.hom.hom x).val g)

/-- A normal subgroup fixing the original coefficient also fixes its
actual induced coefficient, by the literal conjugation identity. -/
theorem originalNormalSubgroupInduced_action_trivial [N.Normal]
    (hN : ∀ g ∈ N, ∀ b : B, B.ρ g b = b)
    (n : G) (hn : n ∈ N) (x : Rep.ind N.subtype (Rep.res N.subtype B)) :
    (Rep.ind N.subtype (Rep.res N.subtype B)).ρ n x = x := by
  classical
  let e := Rep.indCoindIso (Rep.res N.subtype B)
  apply (Rep.mono_iff_injective e.hom).mp inferInstance
  rw [Rep.hom_comm_apply]
  apply Subtype.ext
  funext g
  let f := e.hom.hom x
  change f.val (g * n) = f.val g
  have hmem : g * n * g⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem n hn g
  have h := f.property ⟨g * n * g⁻¹, hmem⟩ g
  change f.val (g * n * g⁻¹ * g) = B.ρ (g * n * g⁻¹) (f.val g) at h
  rw [inv_mul_cancel_right] at h
  exact h.trans (hN _ hmem _)

end
end Dubon2026
