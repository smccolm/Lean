import Dubon2026.SourceIntegralDiamondFieldIdentity

/-! DUB-17/18 -> original Gamma1 degree/genus -> signed-index lower bound.
The proved pullback composition and identity laws construct genuine
automorphisms of the original reduced field. Every scalar in ZMod is a
natural-number image, so the actual ring automorphisms are ZMod-algebra
automorphisms. Inversion of the matrix gives the covariant group action.
The signed Gamma1 subgroup acts trivially; kernel equality and fixing the
full modular base field remain subsequent degree-comparison obligations. -/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne
open scoped MatrixGroups ModularForm

/-- The actual reduced diamond pullback as an algebra automorphism. -/
def reducedFieldEquiv (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (γ : Gamma0 N) :
    qExpFunctionFieldC (ZMod ℓ) (Gamma1 N) ≃ₐ[ZMod ℓ] qExpFunctionFieldC (ZMod ℓ) (Gamma1 N) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom
    (reducedFieldPullHom N ℓ hℓN γ) (reducedFieldPullHom N ℓ hℓN γ⁻¹)
    (RingHom.ext fun x => by
      change reducedFieldPullHom N ℓ hℓN γ (reducedFieldPullHom N ℓ hℓN γ⁻¹ x) = x
      rw [reducedFieldPullHom_comp, inv_mul_cancel]
      exact reducedFieldPullHom_one_matrix N ℓ hℓN x)
    (RingHom.ext fun x => by
      change reducedFieldPullHom N ℓ hℓN γ⁻¹ (reducedFieldPullHom N ℓ hℓN γ x) = x
      rw [reducedFieldPullHom_comp, mul_inv_cancel]
      exact reducedFieldPullHom_one_matrix N ℓ hℓN x))
    (fun c => by
      change reducedFieldPullHom N ℓ hℓN γ
        (algebraMap (ZMod ℓ) (qExpFunctionFieldC (ZMod ℓ) (Gamma1 N)) c) =
        algebraMap (ZMod ℓ) (qExpFunctionFieldC (ZMod ℓ) (Gamma1 N)) c
      rw [← ZMod.natCast_zmod_val c, map_natCast, map_natCast])

theorem reducedFieldEquiv_mul (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (γ δ : Gamma0 N) :
    reducedFieldEquiv N ℓ hℓN (γ * δ) = reducedFieldEquiv N ℓ hℓN δ * reducedFieldEquiv N ℓ hℓN γ := by
  apply AlgEquiv.ext
  intro x
  exact (reducedFieldPullHom_comp N ℓ hℓN γ δ x).symm

theorem reducedFieldEquiv_one (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) :
    reducedFieldEquiv N ℓ hℓN 1 = 1 := by
  apply AlgEquiv.ext
  exact reducedFieldPullHom_one_matrix N ℓ hℓN

/-- The genuine Gamma0 action on the original reduced Gamma1 function field. -/
def reducedFieldAction (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) :
    Gamma0 N →* (qExpFunctionFieldC (ZMod ℓ) (Gamma1 N) ≃ₐ[ZMod ℓ]
      qExpFunctionFieldC (ZMod ℓ) (Gamma1 N)) where
  toFun γ := reducedFieldEquiv N ℓ hℓN γ⁻¹
  map_one' := by rw [inv_one]; exact reducedFieldEquiv_one N ℓ hℓN
  map_mul' γ δ := by rw [mul_inv_rev, reducedFieldEquiv_mul]

theorem reducedFieldAction_apply (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (γ : Gamma0 N) (x : qExpFunctionFieldC (ZMod ℓ) (Gamma1 N)) :
    (reducedFieldAction N ℓ hℓN γ x : LaurentSeries (ZMod ℓ)) =
      reducedFieldPull N ℓ γ⁻¹ x := rfl

theorem reducedFieldAction_eq_one_of_signed_gammaOne (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (γ : Gamma0 N) (hγ : γ.val ∈ plusMinus (Gamma1 N)) :
    reducedFieldAction N ℓ hℓN γ = 1 := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  exact reducedFieldPull_of_signed_gammaOne N ℓ hℓN γ⁻¹ (inv_mem hγ) x

end
end Dubon2026.SourceFunctionField.IntegralDiamond
