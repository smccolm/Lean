import Dubon2026.SourceIntegralCosetCocycle

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> principal-divisor converse ->
integral Petersson duality. Actual modular-generator induction constructs the
integer coset flux coefficients used to represent each period generator.
Native SL2Z_generators and the already proved coset action identities replace
any new presentation. Adapted from the pinned Apache-2.0 primary in route 957. -/
namespace Dubon2026.SourceIntegralPeriodDual
noncomputable section
open SourceParabolicEdgePeriod
open scoped MatrixGroups
variable {Γ : Subgroup SL(2, ℤ)}
local notation "Q" => SL(2, ℤ) ⧸ Γ
local notation "q₀" => ((1 : SL(2, ℤ)) : Q)

open Classical in

/-- The integral indicator of an actual coset. -/
def ind (p : Q) (q : Q) : ℤ := if q = p then 1 else 0

theorem sum_ind_mul [Fintype Q] (p : Q) (h : Q → ℂ) : ∑ q, (ind p q : ℂ) * h q = h p := by
  rw [Finset.sum_eq_single p]
  · simp [ind]
  · intro q _ hq; simp [ind, hq]
  · intro hp; exact absurd (Finset.mem_univ p) hp

theorem ind_smul (M : SL(2, ℤ)) (p q : Q) : ind (M • p) q = ind p (M⁻¹ • q) := by
  by_cases hq : q = M • p
  · subst hq; simp [ind]
  · have hq' : M⁻¹ • q ≠ p := fun h' => hq (by rw [← h', smul_inv_smul])
    simp [ind, hq, hq']

variable [Fintype (SL(2, ℤ) ⧸ Γ)]

/-- Integer coset coefficients for the cusp-limit difference of a modular word. -/
def WordProp (M : SL(2, ℤ)) : Prop :=
  ∃ a n : Q → ℤ,
    (∀ q, a (ModularGroup.S • q) - a q + n q - n (ModularGroup.T • q) =
      ind (M⁻¹ • q₀) q - ind q₀ q) ∧
    ∀ ℓ : SL(2, ℤ) → ℂ, (∀ X, ℓ (X * ModularGroup.T) = ℓ X) → (∀ X, ℓ (-X) = ℓ X) →
      (∀ γ : SL(2, ℤ), γ ∈ Γ → ∀ X,
        ℓ (γ * X * ModularGroup.S) - ℓ (γ * X) = ℓ (X * ModularGroup.S) - ℓ X) →
      ℓ M - ℓ 1 = ∑ q, (a q : ℂ) * (ℓ ((Quotient.out q)⁻¹ * ModularGroup.S) - ℓ (Quotient.out q)⁻¹)

omit [Fintype Q] in
theorem ell_out (ℓ : SL(2, ℤ) → ℂ)
    (hΓ : ∀ γ : SL(2, ℤ), γ ∈ Γ → ∀ X,
      ℓ (γ * X * ModularGroup.S) - ℓ (γ * X) = ℓ (X * ModularGroup.S) - ℓ X) (M : SL(2, ℤ)) :
    ℓ ((Quotient.out (M⁻¹ • (q₀ : Q)))⁻¹ * ModularGroup.S) - ℓ (Quotient.out (M⁻¹ • (q₀ : Q)))⁻¹ =
      ℓ (M * ModularGroup.S) - ℓ M := by
  rw [smul_identity_coset]
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Γ) M⁻¹
  rw [hh, mul_inv_rev, inv_inv]
  exact hΓ _ (inv_mem h.2) M

theorem wordProp_one : WordProp (Γ := Γ) 1 := by
  refine ⟨0, 0, fun q => by simp, fun ℓ _ _ _ => by simp⟩

theorem wordProp_mul_T {M : SL(2, ℤ)} (hM : WordProp (Γ := Γ) M) :
    WordProp (Γ := Γ) (M * ModularGroup.T) := by
  obtain ⟨a, n, h1, h2⟩ := hM
  refine ⟨a, n - ind (M⁻¹ • q₀), fun q => ?_, fun ℓ hT hneg hΓ => ?_⟩
  · simp only [Pi.sub_apply]
    rw [mul_inv_rev, mul_smul, ind_smul ModularGroup.T⁻¹ (M⁻¹ • q₀) q, inv_inv]
    linear_combination h1 q
  · rw [hT, h2 ℓ hT hneg hΓ]

theorem wordProp_mul_T_inv {M : SL(2, ℤ)} (hM : WordProp (Γ := Γ) M) :
    WordProp (Γ := Γ) (M * ModularGroup.T⁻¹) := by
  obtain ⟨a, n, h1, h2⟩ := hM
  refine ⟨a, n + ind (ModularGroup.T • M⁻¹ • q₀), fun q => ?_, fun ℓ hT hneg hΓ => ?_⟩
  · simp only [Pi.add_apply]
    rw [mul_inv_rev, inv_inv, mul_smul, ind_smul ModularGroup.T (M⁻¹ • q₀) (ModularGroup.T • q),
      inv_smul_smul]
    linear_combination h1 q
  · rw [← hT (M * ModularGroup.T⁻¹), inv_mul_cancel_right]
    exact h2 ℓ hT hneg hΓ

theorem wordProp_mul_S (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) {M : SL(2, ℤ)} (hM : WordProp (Γ := Γ) M) :
    WordProp (Γ := Γ) (M * ModularGroup.S) := by
  obtain ⟨a, n, h1, h2⟩ := hM
  refine ⟨a + ind (M⁻¹ • q₀), n, fun q => ?_, fun ℓ hT hneg hΓ => ?_⟩
  · simp only [Pi.add_apply]
    rw [mul_inv_rev, mul_smul, S_inv_smul hΓ, ind_smul ModularGroup.S (M⁻¹ • q₀) q, S_inv_smul hΓ]
    linear_combination h1 q
  · simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib, sum_ind_mul]
    linear_combination h2 ℓ hT hneg hΓ - ell_out ℓ hΓ M

theorem wordProp_mul_S_inv (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) {M : SL(2, ℤ)} (hM : WordProp (Γ := Γ) M) :
    WordProp (Γ := Γ) (M * ModularGroup.S⁻¹) := by
  obtain ⟨a, n, h1, h2⟩ := wordProp_mul_S hΓ hM
  refine ⟨a, n, fun q => ?_, fun ℓ hT hneg hΓ => ?_⟩
  · have e : (M * ModularGroup.S⁻¹)⁻¹ • (q₀ : Q) = (M * ModularGroup.S)⁻¹ • q₀ := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_smul, mul_smul, S_inv_smul hΓ]
    rw [e]; exact h1 q
  · rw [← h2 ℓ hT hneg hΓ, show M * ModularGroup.S⁻¹ = -(M * ModularGroup.S) by
      rw [show ModularGroup.S⁻¹ = -ModularGroup.S by
        rw [inv_eq_iff_mul_eq_one, mul_neg, ← pow_two, S_pow_two, neg_neg], mul_neg], hneg]

theorem wordProp (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) (M : SL(2, ℤ)) : WordProp (Γ := Γ) M := by
  have hM : M ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  induction hM using Subgroup.closure_induction_right with
  | one => exact wordProp_one
  | mul_right x _ y hy ih =>
    rcases hy with rfl | rfl
    · exact wordProp_mul_S hΓ ih
    · exact wordProp_mul_T ih
  | mul_inv_cancel x _ y hy ih =>
    rcases hy with rfl | rfl
    · exact wordProp_mul_S_inv hΓ ih
    · exact wordProp_mul_T_inv ih


end
end Dubon2026.SourceIntegralPeriodDual
