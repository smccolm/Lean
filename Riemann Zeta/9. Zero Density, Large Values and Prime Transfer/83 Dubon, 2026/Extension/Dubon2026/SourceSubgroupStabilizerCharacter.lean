import Dubon2026.SourceModularStabilizerCharacter

/-! DUB-17/18 -> numerical modular genus -> actual normalized ramification
equals half the Gamma0 stabilizer cardinality. The stabilizer character is
the actual Mobius denominator. Its injectivity and finite cyclic image
turn invariance of meromorphic germs into divisibility of their orders.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, selected proofs from
S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer
and S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq.
-/
namespace Dubon2026.SourceFunctionField.SubgroupStabilizer
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups Topology
open scoped StabilizerCharacter
/-- Inclusion of an actual subgroup stabilizer into the full stabilizer. -/
def incl (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) :
    MulAction.stabilizer Γ τ →* MulAction.stabilizer SL(2, ℤ) τ where
  toFun g := ⟨((g : Γ) : SL(2, ℤ)), g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem incl_injective (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) : Function.Injective (incl Γ τ) := by
  intro a b h
  have h' := congrArg (fun x : MulAction.stabilizer SL(2, ℤ) τ => (x : SL(2, ℤ))) h
  exact Subtype.ext (Subtype.ext h')

scoped instance stabilizerFinite (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) :
    Finite (MulAction.stabilizer Γ τ) :=
  Finite.of_injective (incl Γ τ) (incl_injective Γ τ)

/-- The actual denominator character restricted to the subgroup stabilizer. -/
def chi (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) : MulAction.stabilizer Γ τ →* ℂ :=
  (StabilizerCharacter.chi τ).comp (incl Γ τ)

theorem chi_apply (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) (γ : MulAction.stabilizer Γ τ) :
    chi Γ τ γ = denom (((γ : Γ) : SL(2, ℤ)) : GL (Fin 2) ℝ) τ := rfl

theorem chi_injective (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) : Function.Injective (chi Γ τ) :=
  (StabilizerCharacter.chi_injective τ).comp (incl_injective Γ τ)

theorem isCyclic_stabilizer (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) :
    IsCyclic (MulAction.stabilizer Γ τ) :=
  isCyclic_of_injective_ringHom (chi Γ τ) (chi_injective Γ τ)

theorem card_dvd_of_forall_chi_zpow_eq_one (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) (n : ℤ)
    (h : ∀ γ : MulAction.stabilizer Γ τ, chi Γ τ γ ^ (2 * n) = 1) :
    (Nat.card (MulAction.stabilizer Γ τ) : ℤ) ∣ 2 * n := by
  haveI := isCyclic_stabilizer Γ τ
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := MulAction.stabilizer Γ τ)
  rw [← hg, Int.natCast_dvd]
  apply orderOf_dvd_of_pow_eq_one
  apply chi_injective Γ τ
  rw [map_pow, map_one]
  have h1 := h g
  rcases Int.natAbs_eq (2 * n) with h2 | h2
  · rw [h2, zpow_natCast] at h1; exact h1
  · rw [h2, zpow_neg, zpow_natCast, inv_eq_one] at h1; exact h1


end
end Dubon2026.SourceFunctionField.SubgroupStabilizer
