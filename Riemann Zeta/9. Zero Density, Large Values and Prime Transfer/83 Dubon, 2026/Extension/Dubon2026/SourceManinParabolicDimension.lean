import Dubon2026.SourceManinCuspPotential
import Dubon2026.SourceManinRelationDimension
import Dubon2026.SourceWeightTwoPeriodDimension

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> residual Galois association -> original parabolic Hecke
realization -> reverse period dimension inequality -> actual cusp potentials
and finite Manin relations. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_Period_six_mul_finrank_parabolicHoms_add_le_index.lean
and Definitions/Def_ModularCurve_CuspSpace.lean. The target is the existing
original complex parabolic character space; no new cohomology model or
dimension assumption is introduced.
-/
namespace Dubon2026.SourceManin
noncomputable section
open Matrix Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup OnePoint
open scoped MatrixGroups

variable {N : ℕ}

variable (N)

/-- The finite original level-coset space. -/
abbrev X : Type := SL(2, ℤ) ⧸ Gamma0 N

/-- The original elliptic involution acting on level cosets. -/
noncomputable def sig2 : Equiv.Perm (X N) := MulAction.toPerm (S : SL(2, ℤ))

/-- The original order-three elliptic action on level cosets. -/
noncomputable def sig3 : Equiv.Perm (X N) := MulAction.toPerm (S * T : SL(2, ℤ))

theorem sig2_apply (x : X N) : sig2 N x = (S : SL(2, ℤ)) • x := rfl

theorem sig3_apply (x : X N) : sig3 N x = (S * T : SL(2, ℤ)) • x := rfl

theorem mk_neg_one_mul (g : SL(2, ℤ)) : ((-1 * g : SL(2, ℤ)) : X N) = (g : X N) := by
  rw [neg_one_mul, ← mul_neg_one]
  symm
  rw [QuotientGroup.eq, inv_mul_cancel_left]
  exact neg_one_mem_Gamma0 N

theorem sig2_sq : sig2 N ^ 2 = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [sq, Equiv.Perm.mul_apply, sig2_apply, sig2_apply, MulAction.Quotient.smul_mk,
      MulAction.Quotient.smul_mk, Equiv.Perm.one_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      show (S : SL(2, ℤ)) * S = -1 by decide, mk_neg_one_mul]

theorem sig3_cube : sig3 N ^ 3 = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [pow_three, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, sig3_apply, sig3_apply, sig3_apply,
      MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk,
      Equiv.Perm.one_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc,
      ST_cube, mk_neg_one_mul]


theorem connected : Connected (sig2 N) (sig3 N) ℂ := by
  intro f h2 h3 x y
  have hS : ∀ x : X N, f ((S : SL(2, ℤ)) • x) = f x := h2
  have hSinv : ∀ x : X N, f ((S : SL(2, ℤ))⁻¹ • x) = f x := fun x => by
    rw [← hS ((S : SL(2, ℤ))⁻¹ • x), smul_inv_smul]
  have hT : ∀ x : X N, f ((T : SL(2, ℤ)) • x) = f x := fun x => by
    have : (T : SL(2, ℤ)) = S⁻¹ * (S * T) := by group
    rw [this, mul_smul, hSinv]
    exact h3 x
  have key : ∀ k : SL(2, ℤ), k ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) →
      ∀ x : X N, f (k • x) = f x := by
    intro k hk
    refine Subgroup.closure_induction (p := fun k _ => ∀ x : X N, f (k • x) = f x)
      ?_ ?_ ?_ ?_ hk
    · intro k hk x
      rcases hk with rfl | rfl
      · exact hS x
      · exact hT x
    · intro x; rw [one_smul]
    · intro a b _ _ ha hb x
      rw [mul_smul, ha, hb]
    · intro a _ ha x
      rw [← ha (a⁻¹ • x), smul_inv_smul]
  have hall : ∀ k : SL(2, ℤ), ∀ x : X N, f (k • x) = f x := fun k =>
    key k (SpecialLinearGroup.SL2Z_generators ▸ Subgroup.mem_top k)
  induction x using QuotientGroup.induction_on with
  | H g =>
    induction y using QuotientGroup.induction_on with
    | H g' =>
      have e1 := hall g ((1 : SL(2, ℤ)) : X N)
      have e2 := hall g' ((1 : SL(2, ℤ)) : X N)
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at e1 e2
      rw [e1, e2]


/-- Actual parabolic characters together with one complex value per original cusp orbit. -/
abbrev W : Type _ := ↥(SourceCuspBoundary.parabolicHoms N) × (CuspSpace N → ℂ)

/-- Map original parabolic cusp data to its actual Manin-symbol differences. -/
noncomputable def theta : W N →ₗ[ℂ] (X N → ℂ) where
  toFun w := fun x => nX N (w.1 : Additive (Gamma0 N) →+ ℂ) w.2 x
  map_add' w w' := by
    ext x
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply, nX_add]
  map_smul' r w := by
    ext x
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, nX_smul]

theorem theta_apply (w : W N) (x : X N) :
    theta N w x = nX N (w.1 : Additive (Gamma0 N) →+ ℂ) w.2 x := rfl

theorem theta_mem (w : W N) : theta N w ∈ relSpace ℂ (sig2 N) (sig3 N) := by
  have hφ : (w.1 : Additive (Gamma0 N) →+ ℂ) ∈ SourceCuspBoundary.parabolicHoms N := w.1.2
  rw [mem_relSpace]
  constructor
  · intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [sig2_apply, MulAction.Quotient.smul_mk, smul_eq_mul, theta_apply, theta_apply,
        nX_mk hφ, nX_mk hφ, add_comm]
      exact nSL_two_term _ _ g
  · intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [sig3_apply, MulAction.Quotient.smul_mk, smul_eq_mul, sig3_apply,
        MulAction.Quotient.smul_mk, smul_eq_mul, theta_apply, theta_apply, theta_apply,
        nX_mk hφ, nX_mk hφ, nX_mk hφ]
      exact nSL_three_term _ _ g

/-- Add the value at infinity to the Manin relations, fixing the constant-potential ambiguity. -/
noncomputable def thetaPlus : W N →ₗ[ℂ] ↥(relSpace ℂ (sig2 N) (sig3 N)) × ℂ :=
  (LinearMap.codRestrict _ (theta N) (theta_mem N)).prod
    ((LinearMap.proj (CuspSpace.mk N ∞)).comp (LinearMap.snd ℂ _ _))

theorem thetaPlus_injective : Function.Injective (thetaPlus N) := by
  classical
  rw [injective_iff_map_eq_zero]
  rintro ⟨⟨φ, hφmem⟩, c⟩ hw
  have hφ : φ ∈ SourceCuspBoundary.parabolicHoms N := hφmem
  have hθx : ∀ x : X N, nX N φ c x = 0 := fun x =>
    congr_arg (fun p : ↥(relSpace ℂ (sig2 N) (sig3 N)) × ℂ => (p.1 : X N → ℂ) x) hw
  have hcinf : c (CuspSpace.mk N ∞) = 0 :=
    congr_arg (fun p : ↥(relSpace ℂ (sig2 N) (sig3 N)) × ℂ => p.2) hw

  have hPS : ∀ h : SL(2, ℤ), Ppot N φ c (h * S) = Ppot N φ c h := fun h => by
    have e := hθx ((h⁻¹ : SL(2, ℤ)) : X N)
    rw [nX_mk hφ, nSL, inv_inv] at e
    linear_combination -e
  have hPT : ∀ h : SL(2, ℤ), Ppot N φ c (h * T) = Ppot N φ c h := fun h =>
    Ppot_mul_right φ c h T_lower

  have key : ∀ k : SL(2, ℤ), k ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) →
      ∀ h : SL(2, ℤ), Ppot N φ c (h * k) = Ppot N φ c h := by
    intro k hk
    refine Subgroup.closure_induction (p := fun k _ => ∀ h : SL(2, ℤ), Ppot N φ c (h * k) = Ppot N φ c h)
      ?_ ?_ ?_ ?_ hk
    · intro k hk h
      rcases hk with rfl | rfl
      · exact hPS h
      · exact hPT h
    · intro h; rw [mul_one]
    · intro a b _ _ ha hb h
      rw [← mul_assoc, hb, ha]
    · intro a _ ha h
      rw [← ha (h * a⁻¹), inv_mul_cancel_right]
  have hconst : ∀ k : SL(2, ℤ), Ppot N φ c k = Ppot N φ c 1 := fun k => by
    have := key k (SpecialLinearGroup.SL2Z_generators ▸ Subgroup.mem_top k) 1
    rwa [one_mul] at this

  have hPhi : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → Phi (Gamma0 N) φ γ = 0 := fun γ hγ => by
    have e := Ppot_mul_left hφ c hγ 1
    rw [mul_one, hconst γ] at e
    linear_combination -e
  have hφ0 : φ = 0 := AddMonoidHom.ext fun a => by
    have e := hPhi ((Additive.toMul a : Gamma0 N) : SL(2, ℤ)) (Additive.toMul a).2
    rw [Phi_of_mem] at e
    exact e

  have hcval : ∀ σ : SL(2, ℤ), c (CuspSpace.mk N (mapGL ℚ σ • ∞)) = Ppot N φ c 1 := fun σ => by
    rw [← hconst σ, Ppot, Gpot, hPhi _ (gam_mem N _), zero_add]
  have hP1 : Ppot N φ c 1 = 0 := by
    rw [← hcinf, ← hcval 1, map_one, one_smul]
  have hc0 : c = 0 := by
    funext C
    obtain ⟨a, rfl⟩ := CuspSpace.mk_surjective N C
    obtain ⟨σ, rfl⟩ := OnePoint.exists_mem_SL2 ℤ a
    rw [hcval σ, hP1, Pi.zero_apply]
  subst hφ0 hc0
  rfl

variable [NeZero N]

theorem finrank_W_le :
    Module.finrank ℂ ↥(SourceCuspBoundary.parabolicHoms N) + Nat.card (CuspSpace N) ≤
      Module.finrank ℂ ↥(relSpace ℂ (sig2 N) (sig3 N)) + 1 := by
  classical
  letI := sourceWeightTwoParabolic_finite N
  letI := Fintype.ofFinite (CuspSpace N)
  have h := LinearMap.finrank_le_finrank_of_injective (thetaPlus_injective N)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card] at h
  exact h

theorem parabolic_dimension_bound (N : ℕ) [NeZero N] :
    6 * Module.finrank ℂ (SourceCuspBoundary.parabolicHoms N)
        + 6 * Nat.card (CuspSpace N)
        + 3 * Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x}
        + 4 * Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N //
            (ModularGroup.S * ModularGroup.T) • x = x} ≤
      12 + (CongruenceSubgroup.Gamma0 N).index := by
  classical
  letI : Fintype (X N) := Fintype.ofFinite _
  have hR := relSpace_rank_bound ℂ (sig2 N) (sig3 N) (sig2_sq N) (sig3_cube N) (connected N)
  have hW := finrank_W_le N
  have hidx : (CongruenceSubgroup.Gamma0 N).index = Nat.card (X N) := rfl
  have e2 : Nat.card {x : X N // sig2 N x = x} =
      Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x} := rfl
  have e3 : Nat.card {x : X N // sig3 N x = x} =
      Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N //
        (ModularGroup.S * ModularGroup.T) • x = x} := rfl
  rw [e2, e3] at hR
  rw [hidx]
  omega

end
end Dubon2026.SourceManin
