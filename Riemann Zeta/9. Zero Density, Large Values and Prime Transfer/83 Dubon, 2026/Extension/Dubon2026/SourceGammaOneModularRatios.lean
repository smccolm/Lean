import Dubon2026.SourceGammaOneRatioClosure

/-! DUB-17/18 -> arithmetic finite-character realization -> actual Picard/H1 comparison
-> regular differential/cusp comparison. Adapt the already proved equal-weight
modular ratio operations to the actual Gamma1 and Hecke correspondence subgroups.
Only translation membership is required; no new abstract analytic framework.
Local adaptation: SourceModularRatioOperations. Its Apache-2.0 upstream is
anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ModularRatios
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}

/-- The actual modular-form q-expansion embedded in Laurent series. -/
abbrev qL {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem qL_ne_zero (hT : ModularGroup.T ∈ Γ) {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (hper hT)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem qL_mul (hT : ModularGroup.T ∈ Γ) {a b : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) a)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) b) : qL (f.mul g) = qL f * qL g := by
  simp only [qL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (hper hT), PowerSeries.coe_mul]

theorem qL_add (hT : ModularGroup.T ∈ Γ) {a : ℤ} (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) a) :
    qL (f + g) = qL f + qL g := by
  simp only [qL, ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos (hper hT), PowerSeries.coe_add]

theorem qL_one : qL (1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) = 1 := by
  simp only [qL, ModularForm.qExpansion_one, PowerSeries.coe_one]

theorem qL_const (hT : ModularGroup.T ∈ Γ) (c : ℂ) :
    qL (c • (1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0)) =
      algebraMap ℂ (LaurentSeries ℂ) c := by
  rw [qL, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (hper hT), ModularForm.qExpansion_one,
    Algebra.smul_def, mul_one, HahnSeries.algebraMap_apply']

theorem one_ne_zero' : (1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) ≠ 0 := by
  intro h
  have := congrArg
    (fun F : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0 => (F : ℍ → ℂ) UpperHalfPlane.I) h
  simp [ModularForm.one_coe_eq_one] at this

theorem mul_ne_zero' (hT : ModularGroup.T ∈ Γ) {a b : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) a)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) b) (hf : f ≠ 0) (hg : g ≠ 0) :
    f.mul g ≠ 0 := by
  intro hfg
  have h := congrArg (qL (Γ := Γ)) hfg
  rw [qL_mul hT] at h
  have h0 : qL (0 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (a + b)) = 0 := by
    simp only [qL, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero (1 : ℝ), PowerSeries.coe_zero]
  rw [h0] at h
  exact (mul_ne_zero (qL_ne_zero hT f hf) (qL_ne_zero hT g hg)) h

variable (Γ) in

/-- An exact equal-weight modular quotient with a nonzero denominator. -/
def IsRatio (x : LaurentSeries ℂ) : Prop :=
  ∃ (k : ℤ) (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k), h ≠ 0 ∧ x * qL h = qL g

theorem isRatio_algebraMap (hT : ModularGroup.T ∈ Γ) (c : ℂ) : IsRatio Γ (algebraMap ℂ (LaurentSeries ℂ) c) :=
  ⟨0, c • 1, 1, one_ne_zero', by rw [qL_one, mul_one, qL_const hT]⟩

theorem IsRatio.mul (hT : ModularGroup.T ∈ Γ) {x y : LaurentSeries ℂ} (hx : IsRatio Γ x) (hy : IsRatio Γ y) :
    IsRatio Γ (x * y) := by
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  obtain ⟨b, g', h', hh', hye⟩ := hy
  refine ⟨a + b, g.mul g', h.mul h', mul_ne_zero' hT h h' hh hh', ?_⟩
  rw [qL_mul hT, qL_mul hT, ← hxe, ← hye]; ring

theorem IsRatio.add (hT : ModularGroup.T ∈ Γ) {x y : LaurentSeries ℂ} (hx : IsRatio Γ x) (hy : IsRatio Γ y) :
    IsRatio Γ (x + y) := by
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  obtain ⟨b, g', h', hh', hye⟩ := hy
  refine ⟨a + b, g.mul h' + ModularForm.mcast (add_comm b a) (g'.mul h), h.mul h',
    mul_ne_zero' hT h h' hh hh', ?_⟩
  have hc : qL (ModularForm.mcast (add_comm b a) (g'.mul h)) = qL g' * qL h := by
    rw [← qL_mul hT]; simp only [qL, ModularForm.coe_mcast]
  rw [qL_add hT, qL_mul hT, qL_mul hT, hc, ← hxe, ← hye]; ring

theorem IsRatio.inv (hT : ModularGroup.T ∈ Γ) {x : LaurentSeries ℂ} (hx : IsRatio Γ x) : IsRatio Γ x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using isRatio_algebraMap hT (Γ := Γ) 0
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  have hg : g ≠ 0 := by
    intro hg0
    have : qL g = 0 := by
      simp only [hg0, qL, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero (1 : ℝ),
        PowerSeries.coe_zero]
    rw [this] at hxe
    exact (mul_ne_zero hx0 (qL_ne_zero hT h hh)) hxe
  refine ⟨a, h, g, hg, ?_⟩
  rw [← hxe, mul_comm x, mul_comm x⁻¹, mul_assoc, mul_inv_cancel₀ hx0, mul_one]


end
end Dubon2026.SourceFunctionField.GammaOne.ModularRatios
