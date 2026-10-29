import Dubon2026.SourceIntegralDiamondEisensteinAction
import Dubon2026.SourceIntegralDiamondSignedMembership

/-! DUB-17/18 -> original Gamma1 degree/genus -> signed-index lower bound.
Consume the repository's actual integral Eisenstein separator and its
proved action formula. The first coefficient distinguishes every signed
class for levels above two in every coefficient characteristic. At levels
one and two the entire Gamma0 subgroup is already signed Gamma1. This
identifies the exact kernel, with no new lower bound on the coefficient
prime and no exceptional characteristic excluded. -/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open CongruenceSubgroup GammaOne
open scoped MatrixGroups ModularForm

theorem signed_gammaOne_small_level (N : ℕ) [NeZero N] (hN : N ≤ 2) (γ : Gamma0 N) :
    γ.val ∈ plusMinus (Gamma1 N) := by
  have hpos := NeZero.pos N
  have hcases : N = 1 ∨ N = 2 := by omega
  rcases hcases with rfl | rfl
  · exact signed_gammaOne_of_upperLeft 1 γ (Or.inl (Subsingleton.elim _ _))
  · have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc (γ.val 0 0 : ZMod 2) with h | h
    · exact False.elim ((gammaZero_upperLeft_ne_zero 2 (by decide) γ) h)
    · exact signed_gammaOne_of_upperLeft 2 γ (Or.inl h)

theorem signed_gammaOne_of_reducedFieldEquiv_eq_one (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (γ : Gamma0 N) (hγ : reducedFieldEquiv N ℓ hℓN γ = 1) :
    γ.val ∈ plusMinus (Gamma1 N) := by
  by_cases hN : N ≤ 2
  · exact signed_gammaOne_small_level N hN γ
  have hN2 : 2 < N := lt_of_not_ge hN
  letI : Fact (1 < N) := ⟨by omega⟩
  let x : qExpFunctionFieldC (ZMod ℓ) (Gamma1 N) :=
    ⟨IntegralEisenstein.ratio (ZMod ℓ) N 1,
      IntegralEisenstein.ratio_mem_original_field (ZMod ℓ) N 1 one_ne_zero⟩
  have hx : reducedFieldPull N ℓ γ x = IntegralEisenstein.ratio (ZMod ℓ) N 1 :=
    congrArg (fun e => (e x : LaurentSeries (ZMod ℓ))) hγ
  have ha : reducedFieldPull N ℓ γ x =
      IntegralEisenstein.ratio (ZMod ℓ) N (γ.val 0 0 : ZMod N) := by
    simpa only [one_mul] using reducedFieldPull_eisenstein_ratio N ℓ hℓN γ 1 one_ne_zero
      (by simpa only [one_mul] using gammaZero_upperLeft_ne_zero N (by omega) γ) x rfl
  apply signed_gammaOne_of_upperLeft
  by_cases h1 : (γ.val 0 0 : ZMod N) = 1
  · exact Or.inl h1
  by_cases hm1 : (γ.val 0 0 : ZMod N) = -1
  · exact Or.inr hm1
  exact False.elim ((IntegralEisenstein.ratio_separates_signed_identity
    (ZMod ℓ) N hN2 _ h1 hm1) (ha.symm.trans hx))

theorem reducedFieldAction_eq_one_iff (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (γ : Gamma0 N) :
    reducedFieldAction N ℓ hℓN γ = 1 ↔ γ.val ∈ plusMinus (Gamma1 N) := by
  constructor
  · intro hγ
    have hi := signed_gammaOne_of_reducedFieldEquiv_eq_one N ℓ hℓN γ⁻¹ hγ
    simpa only [Subgroup.coe_inv, inv_inv] using (plusMinus (Gamma1 N)).inv_mem hi
  · exact reducedFieldAction_eq_one_of_signed_gammaOne N ℓ hℓN γ

theorem reducedFieldAction_kernel (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) :
    (reducedFieldAction N ℓ hℓN).ker = (plusMinus (Gamma1 N)).subgroupOf (Gamma0 N) := by
  ext γ
  exact reducedFieldAction_eq_one_iff N ℓ hℓN γ

end
end Dubon2026.SourceFunctionField.IntegralDiamond
