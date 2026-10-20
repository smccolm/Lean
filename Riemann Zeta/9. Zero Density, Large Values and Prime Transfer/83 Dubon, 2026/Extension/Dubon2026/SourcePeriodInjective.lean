/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.SourceEichlerTransformation
import Dubon2026.SourcePeriodMap
import Mathlib.NumberTheory.ModularForms.NormTrace

/-! Injectivity of the actual period map on the existing integral modular symbols.
Adapted from TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5.
DUB-17/18 -> modular Galois association -> integral Hecke finiteness ->
actual period injectivity. Vanishing original periods make the constructed
Eichler integral a modular form of nonpositive weight vanishing at every cusp.
Pinned negative-weight vanishing and weight-zero constancy kill that integral;
the proved derivative-recovery theorem then recovers the zero original form.
-/

namespace Dubon2026.SourceModularSymbols
noncomputable section
open Complex ConjAct Filter Function Matrix.SpecialLinearGroup MulOpposite MvPolynomial OnePoint
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm Pointwise Topology

variable {R : Type*} [CommRing R] [Algebra R ℂ]
variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {w : ℕ}

private lemma monomial_period_eq_zero (hk : k = w + 2)
    {f : CuspForm (Γ.map (mapGL ℝ)) k} (hf : periodMap R Γ hk f = 0)
    (σ : SL(2, ℤ)) {j : ℕ} (hj : j ≤ w) (α β : OnePoint ℚ) :
    sourceCuspIntegral (fun z ↦ (⇑f ∣[k] σ) z * (z : ℂ) ^ j) β α = 0 := by
  let P : homogeneousSubmodule (Fin 2) R w := ⟨X 0 ^ j * X 1 ^ (w - j), by
    simpa [Nat.add_sub_cancel' hj] using
      (isHomogeneous_X_pow (R := R) (0 : Fin 2) j).mul (isHomogeneous_X_pow 1 (w - j))⟩
  have hP : periodIntegrand (⇑f ∣[k] σ) P =
      fun z ↦ (⇑f ∣[k] σ) z * (z : ℂ) ^ j := by
    funext z
    simp [P]
  have hdet : 0 < ((mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]
    exact one_pos
  have hper := congrArg
    (fun L ↦ L (symbol (R := R) (w := w) Γ (mapGL ℚ σ • α) (mapGL ℚ σ • β)
      (sourceModularBinaryFormRep R w (op (Matrix.adjugate (σ : Matrix (Fin 2) (Fin 2) ℤ))) P))) hf
  dsimp only at hper
  rw [periodMap_symbol] at hper
  rw [← hP, ModularForm.SL_slash, sourceSL_coe_eq_mapGL,
    ← sourceRat_slash_mapGL,
    sourceCuspIntegral_periodIntegrand_slash hk f P (mapGL_coe_matrix σ) hdet]
  exact hper

private lemma isZeroAtImInfty_sourceEichlerIntegral_slash (hk : k = w + 2)
    {f : CuspForm (Γ.map (mapGL ℝ)) k} (hf : periodMap R Γ hk f = 0)
    {h : ℝ} (hh : 0 < h) (hΓ : h ∈ (Γ.map (mapGL ℝ)).strictPeriods)
    (σ : SL(2, ℤ)) :
    IsZeroAtImInfty (sourceEichlerIntegral h (w + 1) f ∣[-(w : ℤ)] σ) := by
  let Γ' := toConjAct (mapGL ℝ σ)⁻¹ • Γ.map (mapGL ℝ)
  have : Γ'.IsArithmetic := by
    have he : Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (mapGL ℚ σ) = mapGL ℝ σ := by
      rw [Subsingleton.elim (Rat.castHom ℝ) (algebraMap ℚ ℝ), map_mapGL]
    simpa only [map_inv, he] using
      Subgroup.IsArithmetic.conj (Γ.map (mapGL ℝ)) (mapGL ℚ σ)⁻¹
  let f' := _root_.CuspForm.translate f (mapGL ℝ σ)
  have hf' : ⇑f' = ⇑f ∣[k] σ := by
    change (⇑f ∣[k] (mapGL ℝ σ)) = _
    rw [ModularForm.SL_slash, sourceSL_coe_eq_mapGL]
  -- Every period of the translate is a period of the original form against an integral
  -- change of variables of a binary form, and hence vanishes.
  have hper (j : ℕ) (hj : j ≤ w) (α β : OnePoint ℚ) :
      sourceCuspIntegral (fun z ↦ f' z * (z : ℂ) ^ j) β α = 0 := by
    rw [hf']
    exact monomial_period_eq_zero hk hf σ hj α β
  have hE : sourceEichlerIntegral h (w + 1) f ∣[-(w : ℤ)] σ =
      sourceEichlerIntegral Γ'.strictWidthInfty (w + 1) f' := by
    funext τ
    rw [sourceCuspForm_eichlerIntegral_slash_apply hk f hh hΓ f'
      Γ'.strictWidthInfty_pos Γ'.strictWidthInfty_mem_strictPeriods σ hf',
      sourceCuspIntegral_mul_sub_pow f' hk,
      Finset.sum_eq_zero fun j hj ↦ by
        rw [hper j (Finset.mem_range_succ_iff.mp hj), mul_zero], mul_zero, sub_zero]
  rw [hE]
  exact isZeroAtImInfty_sourceEichlerIntegral Γ'.strictWidthInfty_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f' Γ'.strictWidthInfty_mem_strictPeriods)
    (ModularFormClass.holo f') (ModularFormClass.bdd_at_infty f') w

private lemma eichlerIntegral_eq_zero (hk : k = w + 2)
    {f : CuspForm (Γ.map (mapGL ℝ)) k} (hf : periodMap R Γ hk f = 0)
    {h : ℝ} (hh : 0 < h) (hΓ : h ∈ (Γ.map (mapGL ℝ)).strictPeriods) :
    sourceEichlerIntegral h (w + 1) f = 0 := by
  let E : ModularForm (Γ.map (mapGL ℝ)) (-(w : ℤ)) := {
    toFun := sourceEichlerIntegral h (w + 1) f
    slash_action_eq' := by
      rintro γ ⟨σ, hσ, rfl⟩
      rw [← sourceSL_coe_eq_mapGL, ← ModularForm.SL_slash]
      apply sourceCuspForm_eichlerIntegral_slash_eq_of_sourceCuspIntegral_eq_zero
        hk f hh hΓ (Subgroup.mem_map_of_mem _ hσ)
      intro j hj
      simpa using monomial_period_eq_zero hk hf 1 hj
        (∞ : OnePoint ℚ) (mapGL ℚ σ⁻¹ • ∞)
    holo' := mdifferentiable_sourceEichlerIntegral hh
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) _
    bdd_at_cusps' := by
      intro c hc
      have hc' := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
      obtain ⟨σ, hσ⟩ := isCusp_SL2Z_iff'.mp hc'
      exact (isBoundedAt_iff_exists_SL2Z hc').mpr
        ⟨σ, hσ.symm, (isZeroAtImInfty_sourceEichlerIntegral_slash hk hf hh hΓ σ).isBoundedAtImInfty⟩ }
  have hE : ⇑E = sourceEichlerIntegral h (w + 1) f := (rfl)
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero E
    have hz := isZeroAtImInfty_sourceEichlerIntegral hh
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) 0
    have hz' : Tendsto (Function.const ℍ c) atImInfty (𝓝 0) :=
      (show Tendsto (sourceEichlerIntegral h (0 + 1) f) atImInfty (𝓝 0) from hz).congr
        (fun τ => congrFun (hE.symm.trans hc) τ)
    have hc0 : c = 0 := tendsto_nhds_unique tendsto_const_nhds hz'
    simpa only [hc0, Function.const_zero] using hE.symm.trans hc
  · rw [← hE, ModularForm.isZero_of_neg_weight (by omega) E]
    exact ModularForm.coe_zero

/-- **Periods determine a cusp form.** For a finite-index subgroup of `SL(2, ℤ)` and weight
`k = w + 2 ≥ 2`, the period map into the dual of the modular symbols over `R` is injective.
In particular this applies to the integral modular symbols (`R = ℤ`). -/
theorem periodMap_injective (hk : k = w + 2) :
    Function.Injective (periodMap R Γ hk) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro f hf
  let h := (Γ.map (mapGL ℝ)).strictWidthInfty
  have hh : 0 < h := (Γ.map (mapGL ℝ)).strictWidthInfty_pos
  have hΓ : h ∈ (Γ.map (mapGL ℝ)).strictPeriods :=
    (Γ.map (mapGL ℝ)).strictWidthInfty_mem_strictPeriods
  have hderiv := sourceCuspForm_iterate_normalizedDerivOfComplex_eichlerIntegral
    f hh hΓ w
  rw [eichlerIntegral_eq_zero hk hf hh hΓ] at hderiv
  have hzero : Derivative.normalizedDerivOfComplex (0 : ℍ → ℂ) = 0 :=
    Derivative.normalizedDerivOfComplex_const 0
  rw [Function.iterate_fixed hzero] at hderiv
  exact DFunLike.coe_injective hderiv.symm

end
end Dubon2026.SourceModularSymbols
