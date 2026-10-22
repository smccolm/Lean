import Dubon2026.SourceModularStabilizerCharacter
import Dubon2026.ModularDegeneracy

/-! DUB-17/18 -> numerical modular genus -> actual normalized ramification
equals half the Gamma0 stabilizer cardinality. The stabilizer character is
the actual Mobius denominator. Its injectivity and finite cyclic image
turn invariance of meromorphic germs into divisibility of their orders.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, selected proofs from
S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer
and S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq.
-/
namespace Dubon2026.SourceFunctionField.StabilizerCharacter
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups Topology
/-- Include the genuine Gamma0 stabilizer into the full modular stabilizer. -/
def incl (N : ℕ) (τ : ℍ) :
    MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ →* MulAction.stabilizer SL(2, ℤ) τ where
  toFun g := ⟨((g : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)), g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem incl_injective (N : ℕ) (τ : ℍ) : Function.Injective (incl N τ) := by
  intro a b h
  have := congrArg (fun x : MulAction.stabilizer SL(2, ℤ) τ => (x : SL(2, ℤ))) h
  exact Subtype.ext (Subtype.ext this)

theorem chi_heckeDiag_smul (N : ℕ) [NeZero N] (τ : ℍ)
    (δ : MulAction.stabilizer SL(2, ℤ) (levelRaiseMatrix N • τ)) :
    chi (levelRaiseMatrix N • τ) δ =
      (((δ : SL(2, ℤ)) 1 0 * N : ℤ) : ℂ) * τ + (((δ : SL(2, ℤ)) 1 1 : ℤ) : ℂ) := by
  rw [chi_apply, ModularGroup.denom_apply, coe_levelRaiseMatrix_smul N]
  push_cast
  ring

theorem two_mul_dvd_card_stabilizer_gamma0 (N : ℕ) [NeZero N] (τ : ℍ) (e : ℕ) (he : 0 < e)
    (h2 : e ∣ Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2)
    (h3 : e ∣ Nat.card (MulAction.stabilizer SL(2, ℤ) (levelRaiseMatrix N • τ)) / 2) :
    2 * e ∣ Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) := by
  set σ : ℍ := levelRaiseMatrix N • τ with hσ
  haveI : NeZero (2 * e) := ⟨by omega⟩
  obtain ⟨γ, hγ⟩ := exists_orderOf_eq τ (two_mul_dvd_of_dvd_div_two (two_dvd_card_stabilizer τ) h2)
  obtain ⟨δ, hδ⟩ := exists_orderOf_eq σ (two_mul_dvd_of_dvd_div_two (two_dvd_card_stabilizer σ) h3)
  have hu : IsPrimitiveRoot (chi τ γ) (2 * e) := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_chi, hγ]
  have hw : chi σ δ ^ (2 * e) = 1 := by
    rw [← hδ, ← orderOf_chi, pow_orderOf_eq_one]
  obtain ⟨i, -, hi⟩ := hu.eq_pow_of_pow_eq_one hw
  rw [← map_pow] at hi

  set γ' : MulAction.stabilizer SL(2, ℤ) τ := γ ^ i with hγ'
  have hrow : ((γ' : SL(2, ℤ)) 1 0 : ℤ) = (δ : SL(2, ℤ)) 1 0 * N ∧
      ((γ' : SL(2, ℤ)) 1 1 : ℤ) = (δ : SL(2, ℤ)) 1 1 := by
    apply bottom_row_eq τ
    have h1 := hi
    rw [chi_apply, ModularGroup.denom_apply, chi_heckeDiag_smul] at h1
    exact_mod_cast h1
  have hmem : (γ' : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem, hrow.1]
    push_cast
    simp
  have hord' : orderOf γ' = 2 * e := by
    rw [← orderOf_chi, hi, orderOf_chi, hδ]

  let G : MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ :=
    ⟨⟨(γ' : SL(2, ℤ)), hmem⟩, γ'.2⟩
  have hG : incl N τ G = γ' := rfl
  have hordG : orderOf G = 2 * e := by
    rw [← orderOf_injective (incl N τ) (incl_injective N τ) G, hG, hord']
  rw [← hordG]
  exact orderOf_dvd_natCard G


end
end Dubon2026.SourceFunctionField.StabilizerCharacter
