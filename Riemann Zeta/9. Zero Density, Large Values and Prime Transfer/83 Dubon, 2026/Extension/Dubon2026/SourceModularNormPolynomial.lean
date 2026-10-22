import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-! DUB-17/18 -> finite analytic-place exhaustion -> bounded original
functions integral over C[j] -> monic orbit relation for g/Delta^m.
Native modular-form norms and finite interpolation make each orbit
polynomial coefficient an actual level-one modular form. The proved
level-one polynomial reduction then places the coefficients in C[j].
This is the required integrality input; holomorphic removable singularities
and clearing cusp poles remain separate obligations. No place-exhaustion
or modular-curve genus premise is introduced.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic.
-/
namespace Dubon2026.SourceFunctionField.ModularNormPolynomial
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups

open Polynomial SlashInvariantForm

variable {ι : Type*}

theorem natDegree_prod_linear_le (s : Finset ι) (a b : ι → ℂ) :
    (∏ q ∈ s, (C (a q) - C (b q) * X)).natDegree ≤ s.card := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
    rw [Finset.prod_cons, Finset.card_cons]
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    have hfac : (C (a j) - C (b j) * X).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · simp [Polynomial.natDegree_C]
      · exact le_trans (Polynomial.natDegree_C_mul_le _ _) Polynomial.natDegree_X_le
    omega

theorem coeff_card_prod_linear (s : Finset ι) (a b : ι → ℂ) :
    (∏ q ∈ s, (C (a q) - C (b q) * X)).coeff s.card = ∏ q ∈ s, (-(b q)) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Finset.card_cons]
    have hre : (C (a j) - C (b j) * X) * (∏ q ∈ s, (C (a q) - C (b q) * X))
        = C (a j) * (∏ q ∈ s, (C (a q) - C (b q) * X))
          - C (b j) * (X * (∏ q ∈ s, (C (a q) - C (b q) * X))) := by ring
    rw [hre, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul, Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_prod_linear_le s a b) (Nat.lt_succ_self _)), ih]
    ring

theorem aux_scalar (co x y : ℂ) (hy : y ≠ 0) {r c : ℕ} (hr : r ≤ c) :
    co * x ^ r * y ^ (c - r) = co * (x / y) ^ r * y ^ c := by
  rw [div_pow, pow_sub₀ _ hy hr]
  field_simp

theorem key_vanish (s : Finset ι) (a b : ι → ℂ) (j0 : ι) (hj0 : j0 ∈ s) :
    ∑ r ∈ Finset.range (s.card + 1),
      (∏ q ∈ s, (C (a q) - C (b q) * X)).coeff r * (a j0) ^ r * (b j0) ^ (s.card - r) = 0 := by
  set p : Polynomial ℂ := ∏ q ∈ s, (C (a q) - C (b q) * X) with hp
  by_cases hy : b j0 = 0
  · refine Finset.sum_eq_zero fun r hr => ?_
    have hr' : r ≤ s.card := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rcases lt_or_eq_of_le hr' with hlt | rfl
    · rw [hy, zero_pow (by omega), mul_zero]
    · rw [hp, coeff_card_prod_linear, Finset.prod_eq_zero hj0 (by rw [hy, neg_zero]), zero_mul,
        zero_mul]
  · have hdeg : p.natDegree < s.card + 1 :=
      lt_of_le_of_lt (hp ▸ natDegree_prod_linear_le s a b) (Nat.lt_succ_self _)
    calc ∑ r ∈ Finset.range (s.card + 1), p.coeff r * (a j0) ^ r * (b j0) ^ (s.card - r)
        = ∑ r ∈ Finset.range (s.card + 1), p.coeff r * (a j0 / b j0) ^ r * (b j0) ^ s.card := by
          refine Finset.sum_congr rfl fun r hr => ?_
          exact aux_scalar _ _ _ hy (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
      _ = (∑ r ∈ Finset.range (s.card + 1), p.coeff r * (a j0 / b j0) ^ r) * (b j0) ^ s.card := by
          rw [Finset.sum_mul]
      _ = p.eval (a j0 / b j0) * (b j0) ^ s.card := by
          rw [Polynomial.eval_eq_sum_range' hdeg]
      _ = 0 := by
          rw [hp, Polynomial.eval_prod, Finset.prod_eq_zero hj0 (by
            rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C,
              Polynomial.eval_X, mul_div_cancel₀ _ hy, sub_self]), zero_mul]

/-- Restrict an actual modular form to a subgroup, preserving its function. -/
def restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {w : ℤ}
    (f : ModularForm Γ w) : ModularForm Γ' w where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (hle hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono hle)

theorem coe_restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {w : ℤ}
    (f : ModularForm Γ w) : ⇑(restrict hle f) = ⇑f := rfl

theorem sigma_eq_id {A : GL (Fin 2) ℝ} (hA : A ∈ 𝒮ℒ) (c : ℂ) : σ A c = c := by
  have hdet : (0 : ℝ) < (↑A : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Subgroup.HasDetOne.det_eq hA]
    simp
  simp [UpperHalfPlane.σ, hdet]

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)}

theorem quotientFunc_sub_smul [𝒢.HasDetOne] (c : ℂ) {w : ℤ} (g₁ h₁ : ModularForm 𝒢 w)
    (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) (τ : ℍ) :
    quotientFunc (g₁ - c • h₁) q τ = quotientFunc g₁ q τ - quotientFunc h₁ q τ * c := by
  induction q using Quotient.inductionOn with
  | h r =>
    have hA : (r.val)⁻¹ ∈ 𝒮ℒ := inv_mem r.2
    rw [quotientFunc_mk, quotientFunc_mk, quotientFunc_mk, ModularForm.coe_sub,
      ModularForm.IsGLPos.coe_smul, sub_eq_add_neg, SlashAction.add_slash,
      SlashAction.neg_slash, ModularForm.smul_slash, sigma_eq_id hA]
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem norm_apply_eq {w : ℤ} [𝒢.IsArithmetic] (f : ModularForm 𝒢 w) (τ : ℍ)
    [Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)] :
    ModularForm.norm 𝒮ℒ f τ = ∏ q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ, quotientFunc f q τ := by
  have h1 : ModularForm.norm 𝒮ℒ f τ = (∏ q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ, quotientFunc f q) τ := by
    rw [show ⇑(ModularForm.norm 𝒮ℒ f) = _ from ModularForm.coe_norm 𝒮ℒ f]
    congr!
  rw [h1, Finset.prod_apply]

theorem quotientFunc_one {w : ℤ} (f : ModularForm 𝒢 w) :
    quotientFunc f (⟦1⟧ : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) = ⇑f := by
  rw [quotientFunc_mk]
  simp

theorem one_mem_strictPeriods_inf (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) :
    (1 : ℝ) ∈ (𝒢 ⊓ 𝒮ℒ).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff] at h1 ⊢
  exact Subgroup.mem_inf.mpr ⟨h1, Subgroup.mem_strictPeriods_iff.mp one_mem_strictPeriods_SL⟩

theorem coeff_eq_sum_lagrange {n : ℕ} (p : Polynomial ℂ) (hdeg : p.natDegree < n + 1) (r : ℕ)
    (v : Fin (n + 1) → ℂ) (hv : Set.InjOn v ↑(Finset.univ : Finset (Fin (n + 1)))) :
    p.coeff r = ∑ i : Fin (n + 1), p.eval (v i) * (Lagrange.basis Finset.univ v i).coeff r := by
  have hdeg' : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt p.degree_le_natDegree (by exact_mod_cast hdeg)
  conv_lhs => rw [Lagrange.eq_interpolate hv hdeg', Lagrange.interpolate_apply]
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.coeff_C_mul]

/-- Distinct scalar nodes for recovering the modular orbit coefficients. -/
def nodes (m : ℕ) : Fin m → ℂ := fun j => ((j : ℕ) : ℂ)

theorem nodes_injOn (m : ℕ) : Set.InjOn (nodes m) ↑(Finset.univ : Finset (Fin m)) :=
  fun _ _ _ _ hij => Fin.ext (Nat.cast_injective hij)

/-- The polynomial product over actual modular translates of the numerator and denominator. -/
def Pp [Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)] {w : ℤ} (g₁ h₁ : ModularForm 𝒢 w)
    (τ : ℍ) : Polynomial ℂ :=
  ∏ q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ,
    (C (quotientFunc g₁ q τ) - C (quotientFunc h₁ q τ) * X)

theorem natDegree_Pp_le [Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)] {w : ℤ} (g₁ h₁ : ModularForm 𝒢 w)
    (τ : ℍ) : (Pp g₁ h₁ τ).natDegree ≤ Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := by
  refine le_trans (natDegree_prod_linear_le _ _ _) ?_
  rw [Finset.card_univ, Nat.card_eq_fintype_card]

theorem norm_eval_Pp [Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)] {w : ℤ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (g₁ h₁ : ModularForm 𝒢 w) (c : ℂ) (τ : ℍ) :
    ModularForm.norm 𝒮ℒ (g₁ - c • h₁) τ = (Pp g₁ h₁ τ).eval c := by
  rw [norm_apply_eq]
  unfold Pp
  rw [Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun q _ => by
    rw [quotientFunc_sub_smul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]

/-- Recover an orbit-polynomial coefficient as a level-one modular form by norm interpolation. -/
def Aform {w : ℤ} [𝒢.IsArithmetic] [𝒢.HasDetOne] (g₁ h₁ : ModularForm 𝒢 w)
    (r : ℕ) : ModularForm 𝒮ℒ (w * (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) : ℤ)) :=
  ∑ i : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1),
    ((Lagrange.basis Finset.univ (nodes (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1)) i).coeff r) •
      ModularForm.norm 𝒮ℒ (g₁ - nodes (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1) i • h₁)

theorem Aform_apply [Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)] {w : ℤ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (g₁ h₁ : ModularForm 𝒢 w) (r : ℕ) (τ : ℍ) :
    Aform g₁ h₁ r τ = (Pp g₁ h₁ τ).coeff r := by
  have hdeg : (Pp g₁ h₁ τ).natDegree < Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1 :=
    Nat.lt_succ_of_le (natDegree_Pp_le g₁ h₁ τ)
  have hcoe : ⇑(Aform g₁ h₁ r) = ∑ i : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1),
      ((Lagrange.basis Finset.univ (nodes (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1)) i).coeff r) •
        ⇑(ModularForm.norm 𝒮ℒ (g₁ - nodes (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1) i • h₁)) :=
    map_sum (show ModularForm _ _ →+ (ℍ → ℂ) from
      { toFun := fun f => (f : ℍ → ℂ), map_zero' := rfl, map_add' := fun _ _ => rfl }) _ _
  rw [show Aform g₁ h₁ r τ = ⇑(Aform g₁ h₁ r) τ from rfl, hcoe, Finset.sum_apply,
    coeff_eq_sum_lagrange (Pp g₁ h₁ τ) hdeg r _ (nodes_injOn _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_eval_Pp, mul_comm]

/-- One term of the orbit relation, homogenized using the actual denominator. -/
def Tform {K : ℕ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (g₁ h₁ : ModularForm 𝒢 (12 * (K : ℤ)))
    (r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1)) :
    ModularForm (𝒢 ⊓ 𝒮ℒ) (24 * (K : ℤ) * (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) : ℤ)) :=
  ModularForm.mcast (by rw [Nat.cast_sub (Nat.lt_succ_iff.mp r.2)]; ring)
    (((restrict inf_le_right (Aform g₁ h₁ (r : ℕ))).mul
        ((restrict inf_le_left g₁).pow (r : ℕ))).mul
      ((restrict inf_le_left h₁).pow (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) - (r : ℕ))))

theorem Tform_apply [Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)] {K : ℕ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (g₁ h₁ : ModularForm 𝒢 (12 * (K : ℤ)))
    (r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1)) (τ : ℍ) :
    Tform g₁ h₁ r τ = (Pp g₁ h₁ τ).coeff (r : ℕ) * (g₁ τ) ^ (r : ℕ)
      * (h₁ τ) ^ (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) - (r : ℕ)) := by
  show (⇑(Tform g₁ h₁ r)) τ = _
  unfold Tform
  simp only [ModularForm.coe_mcast, ModularForm.coe_mul, ModularForm.coe_pow, coe_restrict,
    Pi.mul_apply, Pi.pow_apply]
  rw [Aform_apply]

theorem qExpansion_Tform {K : ℕ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (h1' : (1 : ℝ) ∈ (𝒢 ⊓ 𝒮ℒ).strictPeriods) (g₁ h₁ : ModularForm 𝒢 (12 * (K : ℤ)))
    (r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1)) :
    qExpansion 1 (Tform g₁ h₁ r : ℍ → ℂ)
      = qExpansion 1 (Aform g₁ h₁ (r : ℕ) : ℍ → ℂ)
        * (qExpansion 1 (g₁ : ℍ → ℂ)) ^ (r : ℕ)
        * (qExpansion 1 (h₁ : ℍ → ℂ)) ^ (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) - (r : ℕ)) := by
  unfold Tform
  rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos h1',
    ModularForm.qExpansion_mul one_pos h1', ModularForm.qExpansion_pow one_pos h1',
    ModularForm.qExpansion_pow one_pos h1', coe_restrict, coe_restrict, coe_restrict]

/-- The full homogeneous orbit relation as a modular form of one common weight. -/
def Sform {K : ℕ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (g₁ h₁ : ModularForm 𝒢 (12 * (K : ℤ))) :
    ModularForm (𝒢 ⊓ 𝒮ℒ) (24 * (K : ℤ) * (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) : ℤ)) :=
  ∑ r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1), Tform g₁ h₁ r

theorem Sform_eq_zero [Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)] {K : ℕ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (g₁ h₁ : ModularForm 𝒢 (12 * (K : ℤ))) : Sform g₁ h₁ = 0 := by
  have hcard : (Finset.univ : Finset (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)).card
      = Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  ext τ
  have hcoe : ⇑(Sform g₁ h₁) = ∑ r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1),
      ⇑(Tform g₁ h₁ r) := map_sum (show ModularForm _ _ →+ (ℍ → ℂ) from
        { toFun := fun f => (f : ℍ → ℂ), map_zero' := rfl, map_add' := fun _ _ => rfl }) _ _
  rw [show Sform g₁ h₁ τ = ⇑(Sform g₁ h₁) τ from rfl, hcoe, Finset.sum_apply]
  have hkv := key_vanish (Finset.univ : Finset (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ))
    (fun q => quotientFunc g₁ q τ) (fun q => quotientFunc h₁ q τ) ⟦1⟧ (Finset.mem_univ _)
  simp only [quotientFunc_one] at hkv
  rw [hcard] at hkv
  calc ∑ r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1), Tform g₁ h₁ r τ
      = ∑ r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1),
          (Pp g₁ h₁ τ).coeff (r : ℕ) * (g₁ τ) ^ (r : ℕ)
            * (h₁ τ) ^ (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) - (r : ℕ)) :=
        Finset.sum_congr rfl fun r _ => Tform_apply g₁ h₁ r τ
    _ = ∑ r ∈ Finset.range (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1),
          (Pp g₁ h₁ τ).coeff r * (g₁ τ) ^ r
            * (h₁ τ) ^ (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) - r) :=
        Fin.sum_univ_eq_sum_range
          (fun m => (Pp g₁ h₁ τ).coeff m * (g₁ τ) ^ m
            * (h₁ τ) ^ (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) - m))
          (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1)
    _ = 0 := by
        unfold Pp
        exact hkv
    _ = (0 : ModularForm (𝒢 ⊓ 𝒮ℒ) (24 * (K : ℤ) * (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) : ℤ))) τ :=
        by simp

theorem qExpansion_Sform {K : ℕ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (h1' : (1 : ℝ) ∈ (𝒢 ⊓ 𝒮ℒ).strictPeriods) (g₁ h₁ : ModularForm 𝒢 (12 * (K : ℤ))) :
    qExpansion 1 (Sform g₁ h₁ : ℍ → ℂ)
      = ∑ r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1),
          qExpansion 1 (Aform g₁ h₁ (r : ℕ) : ℍ → ℂ)
            * (qExpansion 1 (g₁ : ℍ → ℂ)) ^ (r : ℕ)
            * (qExpansion 1 (h₁ : ℍ → ℂ)) ^ (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) - (r : ℕ)) := by
  rw [show qExpansion 1 (Sform g₁ h₁ : ℍ → ℂ)
      = ModularForm.qExpansionAddHom one_pos h1'
          (24 * (K : ℤ) * (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) : ℤ)) (Sform g₁ h₁) from rfl]
  unfold Sform
  rw [map_sum]
  exact Finset.sum_congr rfl fun r _ => qExpansion_Tform h1' g₁ h₁ r


end
end Dubon2026.SourceFunctionField.ModularNormPolynomial
