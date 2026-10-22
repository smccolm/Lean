import Dubon2026.SourceQuotientCuspPoleBound

/-! DUB-17/18 -> finite-place exhaustion -> bounded functions integral
over the original C[j]. The actual holomorphic quotient, its proved
Gamma0 invariance and the finite cusp-order bound yield a genuine
modular form after multiplication by one discriminant power. The
exact q-expansion identity links that form to the original quotient.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_forall_isBoundedUnder_realize.
-/
namespace Dubon2026.SourceFunctionField.QuotientCuspGrowth
noncomputable section
open UpperHalfPlane Filter Function Complex
open scoped MatrixGroups Topology ModularForm Manifold Pointwise
variable (N : ℕ) [NeZero N]

/-- The literal q-expansion of a function, embedded into Laurent series. -/
abbrev qL (f : ℍ → ℂ) : LaurentSeries ℂ := ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ)

/-- The actual discriminant restricted to Gamma0(N). -/
def Δ₀ : ModularForm (CongruenceSubgroup.Gamma0 N) 12 :=
  ModularNormPolynomial.restrict (Subgroup.map_le_range _ _)
    (CuspForm.toModularFormₗ CuspForm.discriminant)

omit [NeZero N] in
theorem coe_Δ₀ : ((Δ₀ N : ModularForm _ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl

/-- The actual level-one discriminant as a modular form. -/
def Δ₁ : ModularForm 𝒮ℒ 12 := CuspForm.toModularFormₗ CuspForm.discriminant

theorem coe_Δ₁ : ((Δ₁ : ModularForm _ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl

/-- The holomorphic quotient multiplied by a discriminant power clearing every cusp. -/
def liftForm {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (F₀ : ℍ → ℂ) (hF₀ : MDiff F₀) (hF : ∀ τ, F₀ τ * h τ = g τ) (m : ℕ)
    (hm : ∀ A : SL(2, ℤ), cuspOrder N (⇑h ∣[k] A) ≤ m) :
    ModularForm (CongruenceSubgroup.Gamma0 N) ((m : ℤ) * 12) where
  toFun := F₀ * ⇑(Δ₁.pow m)
  slash_action_eq' γ hγ := by
    obtain ⟨γ, hγ', rfl⟩ := hγ
    have hΔ : (⇑(Δ₁.pow m)) ∣[((m : ℤ) * 12)] γ = ⇑(Δ₁.pow m) :=
      SlashInvariantFormClass.slash_action_eq (Δ₁.pow m)
        (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩
    have e := ModularForm.mul_slash_SL2 0 ((m : ℤ) * 12) γ F₀ ⇑(Δ₁.pow m)
    rw [zero_add] at e
    show (F₀ * ⇑(Δ₁.pow m)) ∣[((m : ℤ) * 12)] γ = F₀ * ⇑(Δ₁.pow m)
    rw [e, holomorphic_quotient_slash_zero g h hh F₀ hF₀ hF γ hγ', hΔ]
  holo' := hF₀.mul (Δ₁.pow m).holo'
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro A _
    have hΔ : (⇑(Δ₁.pow m)) ∣[((m : ℤ) * 12)] A = ⇑(Δ₁.pow m) :=
      SlashInvariantFormClass.slash_action_eq (Δ₁.pow m)
        (Matrix.SpecialLinearGroup.mapGL ℝ A) ⟨A, rfl⟩
    have e := ModularForm.mul_slash_SL2 0 ((m : ℤ) * 12) A F₀ ⇑(Δ₁.pow m)
    rw [zero_add] at e
    show IsBoundedAtImInfty ((F₀ * ⇑(Δ₁.pow m)) ∣[((m : ℤ) * 12)] A)
    rw [e, hΔ]
    have : (F₀ ∣[(0 : ℤ)] A * ⇑(Δ₁.pow m)) =
        fun τ => F₀ (A • τ) * ModularForm.discriminant τ ^ m := by
      funext τ
      simp [ModularForm.SL_slash_apply, coe_Δ₁]
    rw [this]
    exact isBoundedAtImInfty_of_mul_eq N g h hh F₀ hF A (hm A)

theorem coe_liftForm' {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (F₀ : ℍ → ℂ) (hF₀ : MDiff F₀) (hF : ∀ τ, F₀ τ * h τ = g τ) (m : ℕ)
    (hm : ∀ A : SL(2, ℤ), cuspOrder N (⇑h ∣[k] A) ≤ m) :
    ⇑(liftForm N g h hh F₀ hF₀ hF m hm) = F₀ * ⇑(Δ₁.pow m) := rfl

theorem coe_liftForm {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (F₀ : ℍ → ℂ) (hF₀ : MDiff F₀) (hF : ∀ τ, F₀ τ * h τ = g τ) (m : ℕ)
    (hm : ∀ A : SL(2, ℤ), cuspOrder N (⇑h ∣[k] A) ≤ m) :
    (⇑(liftForm N g h hh F₀ hF₀ hF m hm)) * ⇑h = ⇑g * ⇑((Δ₀ N).pow m) := by
  rw [coe_liftForm']
  funext τ
  simp only [Pi.mul_apply, ModularForm.coe_pow, Pi.pow_apply, coe_Δ₀, coe_Δ₁]
  rw [mul_right_comm, hF]

theorem qL_liftForm_mul {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (F₀ : ℍ → ℂ) (hF₀ : MDiff F₀) (hF : ∀ τ, F₀ τ * h τ = g τ) (m : ℕ)
    (hm : ∀ A : SL(2, ℤ), cuspOrder N (⇑h ∣[k] A) ≤ m) :
    qL ⇑(liftForm N g h hh F₀ hF₀ hF m hm) * qL ⇑h =
      qL ⇑g * qL (ModularForm.discriminant) ^ m := by
  have h1 := ModularForm.qExpansion_mul_coe one_pos (ModularRatios.one_mem_strictPeriods N)
    (liftForm N g h hh F₀ hF₀ hF m hm) h
  have h2 := ModularForm.qExpansion_mul_coe one_pos (ModularRatios.one_mem_strictPeriods N)
    g ((Δ₀ N).pow m)
  have h3 := ModularForm.qExpansion_pow one_pos (ModularRatios.one_mem_strictPeriods N) (Δ₀ N) m
  rw [coe_liftForm] at h1
  simp only [qL, ← PowerSeries.coe_mul, ← PowerSeries.coe_pow, ← h1, h2, h3, coe_Δ₀]


end
end Dubon2026.SourceFunctionField.QuotientCuspGrowth
