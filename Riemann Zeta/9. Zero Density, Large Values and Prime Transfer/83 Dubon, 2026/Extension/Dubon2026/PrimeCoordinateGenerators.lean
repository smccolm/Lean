/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the retained upstream LICENSE.
The coordinate-generation argument is adapted from ClassFieldTheory
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/SUnitKummerPrimeSelection/RestrictionKernel.lean.
-/
import Dubon2026.PrimeExponentCoordinates
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.OrderOfElement

/-! # Actual order-p coordinate generators for Kummer prime selection

The proved restriction-kernel coordinates must produce cyclic subgroups of
exact prime order and jointly generate that kernel. Those subgroups define
the prime-degree fixed extensions to which original full-decomposition prime
avoidance applies. This is required for DUB-17's selected-prime count and
S-unit localization, not a general finite-abelian classification.
-/
namespace Dubon2026
noncomputable section
variable {G : Type} [Group G] {p r : ℕ}
  (e : G ≃* (Fin r → Multiplicative (ZMod p)))

/-- The actual original group element corresponding to the i-th standard coordinate. -/
def primeCoordinateGenerator (i : Fin r) : G :=
  e.symm (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p)))

/-- Each actual coordinate generator has exactly the prescribed order. -/
theorem primeCoordinateGenerator_order (i : Fin r) :
    orderOf (primeCoordinateGenerator e i) = p := by
  rw [primeCoordinateGenerator, e.symm.orderOf_eq, orderOf_piMulSingle,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

/-- The cyclic groups of the actual standard coordinates generate the entire original group. -/
theorem primeCoordinateGenerator_iSup [NeZero p] :
    (⨆ i : Fin r, Subgroup.zpowers (primeCoordinateGenerator e i)) = ⊤ := by
  let P : Subgroup G := ⨆ i : Fin r, Subgroup.zpowers (primeCoordinateGenerator e i)
  apply top_unique
  intro g _
  have hSingle (i : Fin r) (z : Multiplicative (ZMod p)) : e.symm (Pi.mulSingle i z) ∈ P := by
    obtain ⟨m, hm⟩ := ZMod.natCast_zmod_surjective z.toAdd
    have hz : z = (Multiplicative.ofAdd (1 : ZMod p)) ^ m := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow]
      simpa using hm.symm
    have hEq : e.symm (Pi.mulSingle i z) = primeCoordinateGenerator e i ^ m := by
      rw [hz, Pi.mulSingle_pow, map_pow]
      rfl
    rw [hEq]
    exact P.pow_mem ((le_iSup (fun j : Fin r =>
      Subgroup.zpowers (primeCoordinateGenerator e j)) i) (Subgroup.mem_zpowers _)) m
  have hg : e g ∈ P.map e.toMonoidHom := by
    apply Subgroup.pi_mem_of_mulSingle_mem
    intro i
    exact ⟨e.symm (Pi.mulSingle i (e g i)), hSingle i (e g i), e.apply_symm_apply _⟩
  obtain ⟨h, hh, he⟩ := hg
  exact e.injective he ▸ hh

end
end Dubon2026
