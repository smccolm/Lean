import Dubon2026.SourceParabolicCosetPotentials
import Dubon2026.SourceSL2CocycleExists

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi principal-divisor converse -> integral Petersson duality.
Construct the integer parabolic dual of actual period generators. This first
step uses the already proved native SL2(Z) cocycle existence; no separate
cocycle structure or modular presentation is introduced.
Adapted from anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period.lean
(Apache-2.0; retained LICENSE and NOTICE). -/
namespace Dubon2026.SourceIntegralPeriodDual
noncomputable section
open groupCohomology SourceParabolicEdgePeriod SourceModularGreenPairing
open scoped MatrixGroups
variable {Γ : Subgroup SL(2, ℤ)}
local notation "Q" => SL(2, ℤ) ⧸ Γ
local notation "q₀" => ((1 : SL(2, ℤ)) : Q)

theorem smul_identity_coset (g : SL(2, ℤ)) : g • q₀ = (g : Q) := by
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]

theorem smul_identity_coset_of_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) :
    γ • q₀ = q₀ := by
  rw [smul_identity_coset, QuotientGroup.eq, mul_one]
  exact inv_mem hγ

theorem out_smul_identity_coset (q : Q) : Quotient.out q • q₀ = q := by
  rw [smul_identity_coset, QuotientGroup.out_eq']

theorem smul_eq_of_conj_mem {M β : SL(2, ℤ)} (h : M * β * M⁻¹ ∈ Γ) :
    β • M⁻¹ • q₀ = M⁻¹ • q₀ := by
  have he : β * M⁻¹ = M⁻¹ * (M * β * M⁻¹) := by group
  rw [← mul_smul, he, mul_smul, smul_identity_coset_of_mem h]

theorem S_inv_smul (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) (q : Q) :
    ModularGroup.S⁻¹ • q = ModularGroup.S • q := by
  rw [inv_smul_eq_iff, S_smul_S_smul hΓ]

theorem ST_inv_smul_three (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) (q : Q) :
    (ModularGroup.S * ModularGroup.T)⁻¹ • (ModularGroup.S * ModularGroup.T)⁻¹ •
      (ModularGroup.S * ModularGroup.T)⁻¹ • q = q := by
  rw [← mul_smul, ← mul_smul, ← mul_inv_rev, ← mul_inv_rev, ← pow_three]
  change (SourceSL2Cocycle.U ^ 3)⁻¹ • q = q
  rw [SourceSL2Cocycle.U_pow_three, show (-1 : SL(2, ℤ))⁻¹ = -1 by simp,
    neg_one_smul hΓ]

/-- The actual integral inverse-permutation action on the subgroup cosets. -/
def coind (Γ : Subgroup SL(2, ℤ)) : Representation ℤ SL(2, ℤ) (SL(2, ℤ) ⧸ Γ → ℤ) where
  toFun M :=
    { toFun := fun f q => f (M⁻¹ • q)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext f q; simp
  map_mul' M M' := by ext f q; simp [mul_smul]

theorem coind_apply (M : SL(2, ℤ)) (f : Q → ℤ) (q : Q) :
    coind Γ M f q = f (M⁻¹ • q) := rfl

theorem exists_adapted_cocycle (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) (c : Q → ℤ) :
    ∃ Z : cocycles₁ (Rep.of (coind Γ)), Z ModularGroup.S = 0 ∧
      Z (ModularGroup.S * ModularGroup.T) =
        coind Γ (ModularGroup.S * ModularGroup.T) c - c := by
  have h3 : ∀ f : Q → ℤ, coind Γ (ModularGroup.S * ModularGroup.T)
      (coind Γ (ModularGroup.S * ModularGroup.T)
        (coind Γ (ModularGroup.S * ModularGroup.T) f)) = f := by
    intro f
    ext q
    simp only [coind_apply, ST_inv_smul_three hΓ]
  have hy : (coind Γ (ModularGroup.S * ModularGroup.T) c - c) +
      coind Γ (ModularGroup.S * ModularGroup.T) (coind Γ (ModularGroup.S * ModularGroup.T) c - c) +
      coind Γ (ModularGroup.S * ModularGroup.T)
        (coind Γ (ModularGroup.S * ModularGroup.T) (coind Γ (ModularGroup.S * ModularGroup.T) c - c)) = 0 := by
    rw [map_sub, map_sub, h3]
    abel
  exact sourceSL2Cocycle_exists (coind Γ) 0 _ (by simp) hy

variable (Z : cocycles₁ (Rep.of (coind Γ)))

theorem cocycle_mul_apply (g h : SL(2, ℤ)) (p : Q) :
    Z (g * h) p = Z g p + Z h (g⁻¹ • p) := by
  have he := congrFun (SourceCupThree.cocycle_mul Z.property g h) p
  exact he

theorem cocycle_one_apply (p : Q) : Z 1 p = 0 := by
  exact congrFun (SourceCupThree.cocycle_one Z.property) p

theorem cocycle_inv_apply (M : SL(2, ℤ)) (p : Q) :
    Z M⁻¹ p = -Z M (M • p) := by
  have h := cocycle_mul_apply Z M M⁻¹ (M • p)
  rw [mul_inv_cancel, cocycle_one_apply, inv_smul_smul] at h
  linarith

theorem cocycle_neg_one_apply (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) (p : Q) : Z (-1) p = 0 := by
  have h := cocycle_mul_apply Z (-1) (-1) p
  rw [show (-1 : SL(2, ℤ)) * -1 = 1 by simp, cocycle_one_apply,
    show (-1 : SL(2, ℤ))⁻¹ = -1 by simp, neg_one_smul hΓ] at h
  linarith

/-- Restrict the native coset cocycle and evaluate at the actual identity coset. -/
def hom : Additive Γ →+ ℤ where
  toFun a := Z ((Additive.toMul a : Γ) : SL(2, ℤ)) q₀
  map_zero' := by simp [cocycle_one_apply]
  map_add' a b := by
    simp only [toMul_add, Subgroup.coe_mul]
    rw [cocycle_mul_apply, smul_identity_coset_of_mem (inv_mem (Additive.toMul a).2)]

theorem hom_apply (γ : Γ) : hom Z (Additive.ofMul γ) = Z (γ : SL(2, ℤ)) q₀ := rfl

/-- The correction from the chosen coset representatives in the native cocycle. -/
def em (q : Q) : ℤ := -Z (Quotient.out q) q

theorem hom_transition (M : SL(2, ℤ)) (q : Q) :
    hom Z (Additive.ofMul (transition Γ M q)) = Z M (M • q) + em Z (M • q) - em Z q := by
  rw [hom_apply, coe_transition, cocycle_mul_apply, cocycle_mul_apply, cocycle_inv_apply, em, em]
  have h1 : (Quotient.out (M • q))⁻¹⁻¹ • q₀ = M • q := by
    rw [inv_inv, out_smul_identity_coset]
  have h2 : ((Quotient.out (M • q))⁻¹ * M)⁻¹ • q₀ = q := by
    rw [mul_inv_rev, inv_inv, mul_smul, out_smul_identity_coset, inv_smul_smul]
  rw [h1, h2, out_smul_identity_coset]
  ring

theorem hom_conj (M β : SL(2, ℤ)) (h : M * β * M⁻¹ ∈ Γ) :
    hom Z (Additive.ofMul (⟨M * β * M⁻¹, h⟩ : Γ)) = Z β (M⁻¹ • q₀) := by
  rw [hom_apply, Subgroup.coe_mk, cocycle_mul_apply, cocycle_mul_apply, cocycle_inv_apply]
  have h1 : (M * β)⁻¹ • q₀ = M⁻¹ • q₀ := by
    rw [mul_inv_rev, mul_smul]
    have h' : M * β⁻¹ * M⁻¹ ∈ Γ := by
      have he : M * β⁻¹ * M⁻¹ = (M * β * M⁻¹)⁻¹ := by group
      rw [he]; exact inv_mem h
    exact smul_eq_of_conj_mem h'
  rw [h1, smul_inv_smul]
  ring

end
end Dubon2026.SourceIntegralPeriodDual
