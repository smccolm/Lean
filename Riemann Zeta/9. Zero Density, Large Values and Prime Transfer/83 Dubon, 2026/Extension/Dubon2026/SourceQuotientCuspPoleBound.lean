import Dubon2026.SourceQuotientCuspGrowth
import Dubon2026.SourceModularNormPolynomial

/-! DUB-17/18 -> finite-place exhaustion -> bounded original functions
integral over C[j] -> a single discriminant power clears every cusp pole.
Native analytic factorization bounds each nonzero denominator below by
a q-parameter power. The actual finite Gamma0 quotient then bounds the
orders for every slash translate, while discriminant decay clears them.
No cusp-growth or finite-orbit bound is assumed in the final consumer.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_forall_isBoundedUnder_realize.
-/
namespace Dubon2026.SourceFunctionField.QuotientCuspGrowth
noncomputable section
open UpperHalfPlane Filter Function Complex ModularNormPolynomial
open scoped MatrixGroups Topology ModularForm Manifold Pointwise
variable (N : ℕ) {k : ℤ}

theorem Gamma_le_Gamma0 : CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma0 N :=
  fun A hA => by
    rw [CongruenceSubgroup.Gamma0_mem]
    exact (CongruenceSubgroup.Gamma_mem.mp hA).2.2.1

theorem Gamma_le_conj (A : SL(2, ℤ)) :
    ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ A)⁻¹ •
        ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨A * y * A⁻¹,
    Gamma_le_Gamma0 N ((CongruenceSubgroup.Gamma_normal N).conj_mem y hy A), ?_⟩
  simp [map_mul, map_inv]

/-- The actual slash translate, restricted to the principal congruence subgroup. -/
def translateSL (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (A : SL(2, ℤ)) :
    ModularForm (CongruenceSubgroup.Gamma N) k :=
  restrict (Gamma_le_conj N A) (ModularForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ A))

theorem coe_translateSL (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (A : SL(2, ℤ)) : ⇑(translateSL N f A) = ⇑f ∣[k] A := rfl

theorem natCast_mem_strictPeriods_Gamma :
    (N : ℝ) ∈ (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem natCast_pos [NeZero N] : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))

theorem exists_qParam_pow_le_slash [NeZero N] (h : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hh : h ≠ 0) (A : SL(2, ℤ)) :
    ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty,
      C * ‖Periodic.qParam N (τ : ℂ)‖ ^ n ≤ ‖(⇑h ∣[k] A) τ‖ := by
  have hne : translateSL N h A ≠ 0 := by
    intro h0
    apply hh
    have h1 : (⇑h ∣[k] A) = 0 := by
      rw [← coe_translateSL N h A, h0]; rfl
    rw [SlashAction.slash_eq_zero_iff] at h1
    exact (ModularRatios.coe_eq_zero_iff h).mp h1
  exact exists_qParam_pow_le (natCast_pos N) (natCast_mem_strictPeriods_Gamma N)
    (translateSL N h A) hne

open scoped Classical in

/-- A chosen exponent in the proved q-parameter lower bound, totalized outside its domain. -/
def cuspOrder (φ : ℍ → ℂ) : ℕ :=
  if H : ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty,
      C * ‖Periodic.qParam N (τ : ℂ)‖ ^ n ≤ ‖φ τ‖
  then H.choose else 0

theorem cuspOrder_spec (φ : ℍ → ℂ)
    (H : ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty,
      C * ‖Periodic.qParam N (τ : ℂ)‖ ^ n ≤ ‖φ τ‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty,
      C * ‖Periodic.qParam N (τ : ℂ)‖ ^ (cuspOrder N φ) ≤ ‖φ τ‖ := by
  rw [cuspOrder, dif_pos H]
  exact H.choose_spec

theorem exists_forall_cuspOrder_le [NeZero N] (h : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    ∃ m : ℕ, ∀ A : SL(2, ℤ), cuspOrder N (⇑h ∣[k] A) ≤ m := by
  classical
  haveI : Finite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.finite_quotient_of_finiteIndex
  let ψ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℕ :=
    fun q => cuspOrder N (⇑h ∣[k] (q.out)⁻¹)
  obtain ⟨m, hm⟩ := (Set.finite_range ψ).bddAbove
  refine ⟨m, fun A => ?_⟩
  set B : SL(2, ℤ) := ((A⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out with hB
  have hq : ((A⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) = (B : _) :=
    (QuotientGroup.out_eq' _).symm
  rw [QuotientGroup.eq, inv_inv] at hq
  have hslash : ⇑h ∣[k] (A * B) = ⇑h :=
    SlashInvariantFormClass.slash_action_eq h (Matrix.SpecialLinearGroup.mapGL ℝ (A * B))
      (Subgroup.mem_map_of_mem _ hq)
  have key : ⇑h ∣[k] A = ⇑h ∣[k] B⁻¹ :=
    calc ⇑h ∣[k] A = ⇑h ∣[k] ((A * B) * B⁻¹) := by rw [mul_inv_cancel_right]
      _ = (⇑h ∣[k] (A * B)) ∣[k] B⁻¹ := SlashAction.slash_mul _ _ _ _
      _ = ⇑h ∣[k] B⁻¹ := by rw [hslash]
  rw [key]
  exact hm ⟨_, rfl⟩

theorem isBoundedAtImInfty_of_mul_eq [NeZero N] (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hh : h ≠ 0) (F₀ : ℍ → ℂ) (hF : ∀ τ, F₀ τ * h τ = g τ) (A : SL(2, ℤ)) {m : ℕ}
    (hm : cuspOrder N (⇑h ∣[k] A) ≤ m) :
    IsBoundedAtImInfty (fun τ : ℍ => F₀ (A • τ) * (ModularForm.discriminant τ) ^ m) := by
  obtain ⟨C, hC, hlow⟩ := cuspOrder_spec N _ (exists_qParam_pow_le_slash N h hh A)
  have hgA : IsBoundedAtImInfty (⇑g ∣[k] A) := ModularFormClass.bdd_at_infty (translateSL N g A)
  obtain ⟨D, hD⟩ := exists_norm_discriminant_le
  rw [IsBoundedAtImInfty, BoundedAtFilter] at hgA ⊢
  obtain ⟨M, hM⟩ := hgA.bound
  refine Asymptotics.IsBigO.of_bound (max M 0 * max D 0 ^ m / C) ?_
  filter_upwards [hlow, hM, hD] with τ h1 h2 h3
  simp only [Pi.one_apply, norm_one, mul_one] at h2 ⊢
  have hq0 : 0 < ‖Periodic.qParam N (τ : ℂ)‖ := by
    rw [Periodic.norm_qParam]; exact Real.exp_pos _
  have hq1 : ‖Periodic.qParam N (τ : ℂ)‖ ≤ 1 := (norm_qParam_lt_one' (natCast_pos N) τ).le
  have hq₁ : ‖Periodic.qParam 1 (τ : ℂ)‖ ≤ ‖Periodic.qParam N (τ : ℂ)‖ :=
    norm_qParam_one_le (Nat.one_le_cast.mpr NeZero.one_le) τ
  have hab : ‖F₀ (A • τ)‖ * ‖(⇑h ∣[k] A) τ‖ = ‖(⇑g ∣[k] A) τ‖ := by
    rw [← norm_mul, ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, ← mul_assoc, hF]
  rw [norm_mul, norm_pow]
  exact key_ineq (norm_nonneg _) (norm_nonneg _) hab h1 (h2.trans (le_max_left _ _))
    (h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))) hq₁ hq1 hq0
    (norm_nonneg _) hC (le_max_right _ _) (le_max_right _ _) hm


end
end Dubon2026.SourceFunctionField.QuotientCuspGrowth
