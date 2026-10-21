import Dubon2026.SourceManinCuspStabilizer

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

variable (N : ℕ)

/-- Choose an original rational cusp representing each actual level cusp orbit. -/
noncomputable def rep (C : CuspSpace N) : OnePoint ℚ := (CuspSpace.mk_surjective N C).choose

theorem mk_rep (C : CuspSpace N) : CuspSpace.mk N (rep N C) = C :=
  (CuspSpace.mk_surjective N C).choose_spec

theorem exists_gam (a : OnePoint ℚ) :
    ∃ γ ∈ Gamma0 N, mapGL ℚ γ • rep N (CuspSpace.mk N a) = a :=
  CuspSpace.mk_eq_mk_iff.mp (mk_rep N _).symm

/-- Choose a genuine level element carrying the orbit representative to the given cusp. -/
noncomputable def gam (a : OnePoint ℚ) : SL(2, ℤ) := (exists_gam N a).choose

theorem gam_mem (a : OnePoint ℚ) : gam N a ∈ Gamma0 N := (exists_gam N a).choose_spec.1

theorem gam_smul (a : OnePoint ℚ) : mapGL ℚ (gam N a) • rep N (CuspSpace.mk N a) = a :=
  (exists_gam N a).choose_spec.2

/-- Cusp potential from the original character and one value per actual cusp orbit. -/
noncomputable def Gpot (φ : Additive (Gamma0 N) →+ ℂ) (c : CuspSpace N → ℂ) (a : OnePoint ℚ) : ℂ :=
  Phi (Gamma0 N) φ (gam N a) + c (CuspSpace.mk N a)

variable {N}

theorem Phi_eq_zero_of_fix {φ : Additive (Gamma0 N) →+ ℂ} (hφ : φ ∈ SourceCuspBoundary.parabolicHoms N)
    {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 N) {r : OnePoint ℚ} (hfix : mapGL ℚ δ • r = r) :
    Phi (Gamma0 N) φ δ = 0 := by
  classical
  obtain ⟨σ, rfl⟩ := OnePoint.exists_mem_SL2 ℤ r
  have h10 : (σ⁻¹ * δ * σ) 1 0 = 0 := by
    rw [← smul_infty_eq_iff, map_mul, map_mul, mul_smul, mul_smul, hfix, ← mul_smul, ← map_mul,
      inv_mul_cancel, map_one, one_smul]
  have htr := trace_sq_of_lower_left _ h10
  rw [trace_conj] at htr
  exact Phi_parabolic _ hφ hδ htr

theorem Gpot_smul {φ : Additive (Gamma0 N) →+ ℂ} (hφ : φ ∈ SourceCuspBoundary.parabolicHoms N)
    (c : CuspSpace N → ℂ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (a : OnePoint ℚ) :
    Gpot N φ c (mapGL ℚ γ • a) = Phi (Gamma0 N) φ γ + Gpot N φ c a := by
  have hmk : CuspSpace.mk N (mapGL ℚ γ • a) = CuspSpace.mk N a := CuspSpace.mk_smul hγ a
  unfold Gpot
  rw [hmk]
  have ha := gam_smul N a
  have hb := gam_smul N (mapGL ℚ γ • a)
  rw [hmk] at hb
  have hfix : mapGL ℚ ((gam N (mapGL ℚ γ • a))⁻¹ * γ * gam N a) • rep N (CuspSpace.mk N a) =
      rep N (CuspSpace.mk N a) := by
    rw [map_mul, map_mul, mul_smul, mul_smul, ha, map_inv, inv_smul_eq_iff]
    exact hb.symm
  have h0 := Phi_eq_zero_of_fix hφ
    (mul_mem (mul_mem (inv_mem (gam_mem N _)) hγ) (gam_mem N a)) hfix
  rw [Phi_mul _ _ (mul_mem (inv_mem (gam_mem N _)) hγ) (gam_mem N a),
    Phi_mul _ _ (inv_mem (gam_mem N _)) hγ, Phi_inv _ _ (gam_mem N _)] at h0
  linear_combination (-1 : ℂ) * h0

variable (N)

/-- Pull the actual cusp potential back along the integral action at infinity. -/
noncomputable def Ppot (φ : Additive (Gamma0 N) →+ ℂ) (c : CuspSpace N → ℂ) (g : SL(2, ℤ)) : ℂ :=
  Gpot N φ c (mapGL ℚ g • ∞)

variable {N}

theorem Ppot_mul_left {φ : Additive (Gamma0 N) →+ ℂ} (hφ : φ ∈ SourceCuspBoundary.parabolicHoms N)
    (c : CuspSpace N → ℂ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (g : SL(2, ℤ)) :
    Ppot N φ c (γ * g) = Phi (Gamma0 N) φ γ + Ppot N φ c g := by
  unfold Ppot
  rw [map_mul, mul_smul, Gpot_smul hφ c hγ]

theorem Ppot_mul_right (φ : Additive (Gamma0 N) →+ ℂ) (c : CuspSpace N → ℂ) (g : SL(2, ℤ))
    {k : SL(2, ℤ)} (hk : k 1 0 = 0) : Ppot N φ c (g * k) = Ppot N φ c g := by
  unfold Ppot
  rw [map_mul, mul_smul, (smul_infty_eq_iff k).mpr hk]

variable (N)

/-- The difference of potential values on the two endpoints of an original Manin symbol. -/
noncomputable def nSL (φ : Additive (Gamma0 N) →+ ℂ) (c : CuspSpace N → ℂ) (g : SL(2, ℤ)) : ℂ :=
  Ppot N φ c g⁻¹ - Ppot N φ c (g⁻¹ * S)

/-- The Manin-symbol difference evaluated on the chosen actual level-coset representative. -/
noncomputable def nX (φ : Additive (Gamma0 N) →+ ℂ) (c : CuspSpace N → ℂ)
    (x : SL(2, ℤ) ⧸ Gamma0 N) : ℂ :=
  nSL N φ c (Quotient.out x)

variable {N}

theorem nX_mk {φ : Additive (Gamma0 N) →+ ℂ} (hφ : φ ∈ SourceCuspBoundary.parabolicHoms N)
    (c : CuspSpace N → ℂ) (g : SL(2, ℤ)) :
    nX N φ c (g : SL(2, ℤ) ⧸ Gamma0 N) = nSL N φ c g := by
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul (Gamma0 N) g
  unfold nX
  rw [hγ]
  unfold nSL
  rw [_root_.mul_inv_rev, mul_assoc, Ppot_mul_left hφ c (inv_mem γ.2), Ppot_mul_left hφ c (inv_mem γ.2)]
  ring

theorem nSL_two_term (φ : Additive (Gamma0 N) →+ ℂ) (c : CuspSpace N → ℂ) (g : SL(2, ℤ)) :
    nSL N φ c (S * g) + nSL N φ c g = 0 := by
  unfold nSL
  rw [_root_.mul_inv_rev, inv_mul_cancel_right, S_inv_eq, ← mul_assoc,
    Ppot_mul_right φ c _ neg_one_lower]
  ring

theorem nSL_three_term (φ : Additive (Gamma0 N) →+ ℂ) (c : CuspSpace N → ℂ) (g : SL(2, ℤ)) :
    nSL N φ c g + nSL N φ c (S * T * g) + nSL N φ c (S * T * (S * T * g)) = 0 := by
  unfold nSL
  have e1 : (S * T * g)⁻¹ = g⁻¹ * (S * T)⁻¹ := by group
  have e2 : (S * T * (S * T * g))⁻¹ = g⁻¹ * (S * T)⁻¹ * (S * T)⁻¹ := by group
  have hA : Ppot N φ c (g⁻¹ * (S * T)⁻¹ * S) = Ppot N φ c g⁻¹ := by
    rw [mul_assoc, ST_inv_mul_S, Ppot_mul_right φ c _ T_inv_lower]
  have hB : Ppot N φ c (g⁻¹ * (S * T)⁻¹ * (S * T)⁻¹ * S) = Ppot N φ c (g⁻¹ * (S * T)⁻¹) := by
    rw [mul_assoc _ _ S, ST_inv_mul_S, Ppot_mul_right φ c _ T_inv_lower]
  have hC : Ppot N φ c (g⁻¹ * (S * T)⁻¹ * (S * T)⁻¹) = Ppot N φ c (g⁻¹ * S) := by
    rw [mul_assoc g⁻¹, ST_inv_mul_ST_inv, ← mul_assoc, Ppot_mul_right φ c _ neg_one_lower,
      ← mul_assoc, Ppot_mul_right φ c _ T_lower]
  rw [e1, e2, hA, hB, hC]
  ring

theorem nX_add (φ ψ : Additive (Gamma0 N) →+ ℂ) (c d : CuspSpace N → ℂ) (x : SL(2, ℤ) ⧸ Gamma0 N) :
    nX N (φ + ψ) (c + d) x = nX N φ c x + nX N ψ d x := by
  simp only [nX, nSL, Ppot, Gpot, Phi_add, Pi.add_apply]
  ring

theorem nX_smul (r : ℂ) (φ : Additive (Gamma0 N) →+ ℂ) (c : CuspSpace N → ℂ)
    (x : SL(2, ℤ) ⧸ Gamma0 N) :
    nX N (r • φ) (r • c) x = r * nX N φ c x := by
  simp only [nX, nSL, Ppot, Gpot, Phi_smul, Pi.smul_apply, smul_eq_mul]
  ring


end
end Dubon2026.SourceManin
