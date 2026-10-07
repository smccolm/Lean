/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors

Adapted from the finite-coset-pairing portion of Modularforms/PeterssonLevelN.lean
at 7c41b9b1747d47298f76bdb51f07031087702198. The group here is Gamma0,
and the invariant measure is the existing Mathlib volume on the upper half-plane.
-/
import Dubon2026.ModularPeterssonDefinite
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-! # The genuine finite-coset Petersson pairing for level Gamma0

The definition integrates the actual slash-translates over the standard domain.
Its Hermitian, sesquilinear and positive-definite properties are proved here.
-/

namespace Dubon2026

noncomputable section

open scoped MatrixGroups ModularForm Pointwise
open UpperHalfPlane ModularGroup CongruenceSubgroup MeasureTheory Matrix.SpecialLinearGroup

local notation "μ_hyp" => (volume : Measure ℍ)

instance modularContinuousConstSMulSL2 : ContinuousConstSMul SL(2, ℤ) ℍ where
  continuous_const_smul g := continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ g)

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The positive-level congruence quotient is finite. -/
local instance modularGamma0QuotientFintype : Fintype (SL(2, ℤ) ⧸ Gamma0 N) := Subgroup.fintypeQuotientOfFiniteIndex

omit [NeZero N] in
/-- For `γ ∈ Γ₀(N)`, the weight-`k` slash action on a `Γ₀(N)`-cusp form is trivial. -/
theorem slash_Gamma0_eq
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    ⇑f ∣[k] γ = ⇑f := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩

/-- The level-N Petersson inner product on `S_k(Γ₀(N))`, defined as
`cuspPetersson f g = Σ_{[δ] ∈ SL₂(ℤ)/Γ₀(N)} ∫_fd petersson k (f∣δ⁻¹) (g∣δ⁻¹) dμ`. -/
def cuspPetersson (f g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) : ℂ :=
  ∑ q : SL(2, ℤ) ⧸ Gamma0 N,
    peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹)

/-- Hermitian symmetry: `conj(cuspPetersson g f) = cuspPetersson f g`. -/
theorem cuspPetersson_conj_symm
    (f g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    starRingEnd ℂ (cuspPetersson g f) = cuspPetersson f g := by
  simp only [cuspPetersson, map_sum, peterssonInner_conj_symm]

/-- `cuspPetersson f 0 = 0`. -/
theorem cuspPetersson_zero_right
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    cuspPetersson f 0 = 0 := by
  simp [cuspPetersson, peterssonInner_zero_right]

/-- `cuspPetersson 0 g = 0`. -/
theorem cuspPetersson_zero_left
    (g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    cuspPetersson 0 g = 0 := by
  simp [cuspPetersson, peterssonInner_zero_left]

/-- The Petersson integrand of slashed cusp forms is integrable on `fd`. -/
theorem integrableOn_petersson_slash
    {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    [CuspFormClass F Γ k] [ModularFormClass F' Γ k]
    (f : F) (f' : F') (δ : SL(2, ℤ)) :
    IntegrableOn (fun τ ↦ petersson k (⇑f ∣[k] δ) (⇑f' ∣[k] δ) τ) fd μ_hyp := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k Γ f f'
  rw [show (fun τ ↦ petersson k (⇑f ∣[k] δ) (⇑f' ∣[k] δ) τ) =
      fun τ ↦ petersson k (⇑f) (⇑f') (δ • τ) from
    funext fun τ ↦ petersson_slash_SL k _ _ δ τ]
  exact IntegrableOn.of_bound hyperbolicMeasure_fd_lt_top
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous f')).comp (continuous_const_smul δ)
    |>.aestronglyMeasurable.restrict)
    C (ae_of_all _ fun τ ↦ hC (δ • τ))

omit [NeZero N] in
private theorem out_one_mem_Gamma0 :
    ((⟦1⟧ : SL(2, ℤ) ⧸ Gamma0 N)).out ∈ Gamma0 N := by
  have h := Quotient.exact ((⟦1⟧ : SL(2, ℤ) ⧸ Gamma0 N).out_eq)
  change (QuotientGroup.leftRel (Gamma0 N)).r _ _ at h
  rw [QuotientGroup.leftRel_apply] at h; simpa using h

omit [NeZero N] in
private theorem identity_coset_eq_pet
    (f g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    peterssonInner k fd
      (⇑f ∣[k] (⟦(1 : SL(2, ℤ))⟧ : SL(2, ℤ) ⧸ Gamma0 N).out⁻¹)
      (⇑g ∣[k] (⟦(1 : SL(2, ℤ))⟧ : SL(2, ℤ) ⧸ Gamma0 N).out⁻¹) =
    peterssonInner k fd f g := by
  have hmem := (Gamma0 N).inv_mem out_one_mem_Gamma0
  simp only [slash_Gamma0_eq f _ hmem, slash_Gamma0_eq g _ hmem, peterssonInner]

private theorem petersson_self_ofReal (h : ℍ → ℂ) (τ : ℍ) :
    petersson k h h τ = ↑(Complex.normSq (h τ) * τ.im ^ k) := by
  simp only [petersson, ← Complex.normSq_eq_conj_mul_self]
  push_cast; ring

private theorem peterssonInner_self_real (h : ℍ → ℂ) :
    peterssonInner k fd h h =
      ↑(∫ τ in fd, Complex.normSq (h τ) * τ.im ^ k ∂(volume : Measure ℍ)) := by
  show ∫ τ in fd, petersson k h h τ ∂(volume : Measure ℍ) = _
  simp_rw [petersson_self_ofReal]
  exact integral_ofReal

private theorem measurableSet_fd' : MeasurableSet (fd : Set ℍ) :=
  ((isClosed_le continuous_const (Complex.continuous_normSq.comp continuous_coe)).inter
    (isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re)
      continuous_const)).measurableSet

omit [NeZero N] in
/-- Each summand of `cuspPetersson f f` is a non-negative real number. -/
theorem cuspPetersson_summand_nonneg
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma0 N) :
    ∃ r : ℝ, 0 ≤ r ∧
      peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑f ∣[k] (q.out)⁻¹) = ↑r := by
  set h := ⇑f ∣[k] (q.out)⁻¹
  refine ⟨∫ τ in fd, Complex.normSq (h τ) * τ.im ^ k ∂(volume : Measure ℍ),
    setIntegral_nonneg measurableSet_fd' fun τ _ ↦
      mul_nonneg (Complex.normSq_nonneg _) (zpow_nonneg (UpperHalfPlane.im_pos τ).le _),
    peterssonInner_self_real h⟩

/-- **Positive definiteness** of the level-N Petersson inner product. -/
theorem cuspPetersson_definite
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hpet : cuspPetersson f f = 0) : f = 0 := by
  apply cuspForm_eq_zero_of_peterssonIntegral f
  rw [← identity_coset_eq_pet f f]
  choose r hr_nonneg hr_eq using cuspPetersson_summand_nonneg f
  have hsum : (↑(∑ q, r q) : ℂ) = 0 := by
    rw [Complex.ofReal_sum]; simp_rw [← hr_eq]; exact hpet
  rw [hr_eq ⟦1⟧,
    (Finset.sum_eq_zero_iff_of_nonneg fun q _ ↦ hr_nonneg q).mp
      (Complex.ofReal_eq_zero.mp hsum) ⟦1⟧ (Finset.mem_univ _),
    Complex.ofReal_zero]

/-- Negation in the second argument. -/
theorem cuspPetersson_neg_right
    (f g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    cuspPetersson f (-g) = -cuspPetersson f g := by
  simp only [cuspPetersson, CuspForm.coe_neg, SlashAction.neg_slash, peterssonInner_neg_right,
    Finset.sum_neg_distrib]

/-- Negation in the first argument. -/
theorem cuspPetersson_neg_left
    (f g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    cuspPetersson (-f) g = -cuspPetersson f g := by
  simp only [cuspPetersson, CuspForm.coe_neg, SlashAction.neg_slash, peterssonInner_neg_left,
    Finset.sum_neg_distrib]

/-- Additivity in the second argument. -/
theorem cuspPetersson_add_right
    (f g₁ g₂ : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    cuspPetersson f (g₁ + g₂) = cuspPetersson f g₁ + cuspPetersson f g₂ := by
  simp only [cuspPetersson, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [show ⇑(g₁ + g₂) ∣[k] q.out⁻¹ = (⇑g₁ ∣[k] q.out⁻¹) + (⇑g₂ ∣[k] q.out⁻¹) from by
    rw [CuspForm.coe_add]; exact SlashAction.add_slash k _ _ _]
  exact peterssonInner_add_right k fd _ _ _
    (integrableOn_petersson_slash f g₁ (q.out)⁻¹)
    (integrableOn_petersson_slash f g₂ (q.out)⁻¹)

private lemma smul_slash_SL (c : ℂ) (f : ℍ → ℂ) (δ : SL(2, ℤ)) :
    (c • f) ∣[k] δ = c • (f ∣[k] δ) := by
  rw [ModularForm.SL_slash (c • f) δ, ModularForm.SL_slash f δ, ModularForm.smul_slash]
  simp [UpperHalfPlane.σ, Matrix.SpecialLinearGroup.map]

/-- Complex scalar in the second argument: `cuspPetersson f (c • g) = c * cuspPetersson f g`. -/
theorem cuspPetersson_smul_right (c : ℂ)
    (f g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    cuspPetersson f (c • g) = c * cuspPetersson f g := by
  simp only [cuspPetersson, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [show ⇑(c • g) ∣[k] q.out⁻¹ = c • (⇑g ∣[k] q.out⁻¹) from smul_slash_SL c _ _]
  exact peterssonInner_smul_right k _ c _ _

/-- Conjugate-complex scalar in the first argument:
`cuspPetersson (c • f) g = conj(c) * cuspPetersson f g`. -/
theorem cuspPetersson_conj_smul_left (c : ℂ)
    (f g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    cuspPetersson (c • f) g = starRingEnd ℂ c * cuspPetersson f g :=
  calc cuspPetersson (c • f) g
      = starRingEnd ℂ (cuspPetersson g (c • f)) := (cuspPetersson_conj_symm _ _).symm
    _ = starRingEnd ℂ (c * cuspPetersson g f) := by rw [cuspPetersson_smul_right]
    _ = starRingEnd ℂ c * starRingEnd ℂ (cuspPetersson g f) := map_mul _ _ _
    _ = starRingEnd ℂ c * cuspPetersson f g := by rw [cuspPetersson_conj_symm]

/-- Additivity in the first argument. -/
theorem cuspPetersson_add_left
    (f₁ f₂ g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    cuspPetersson (f₁ + f₂) g = cuspPetersson f₁ g + cuspPetersson f₂ g :=
  calc cuspPetersson (f₁ + f₂) g
      = starRingEnd ℂ (cuspPetersson g (f₁ + f₂)) := (cuspPetersson_conj_symm _ _).symm
    _ = starRingEnd ℂ (cuspPetersson g f₁ + cuspPetersson g f₂) := by rw [cuspPetersson_add_right]
    _ = starRingEnd ℂ (cuspPetersson g f₁) + starRingEnd ℂ (cuspPetersson g f₂) := map_add _ _ _
    _ = cuspPetersson f₁ g + cuspPetersson f₂ g := by rw [cuspPetersson_conj_symm, cuspPetersson_conj_symm]

end

end Dubon2026
