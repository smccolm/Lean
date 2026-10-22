import Dubon2026.SourceCuspDegeneracyLaurent

/-! DUB-17/18 -> original regular differential realization -> analytic
realization of the original field. Ratios of genuine equal-weight modular
forms are closed under the field operations. The denominator is proved
nonzero using native q-expansion injectivity. These operations will extend
the actual j and j_N representations through the already proved two-generator
field identity. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange.
-/
namespace Dubon2026.SourceFunctionField.ModularRatios
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups
variable {N : Nat}

/-- The actual modular-form q-expansion embedded in Laurent series. -/
abbrev qL {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem qL_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem qL_mul {a b : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) a)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) b) : qL (f.mul g) = qL f * qL g := by
  simp only [qL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods N), PowerSeries.coe_mul]

theorem qL_add {a : ℤ} (f g : ModularForm (CongruenceSubgroup.Gamma0 N) a) :
    qL (f + g) = qL f + qL g := by
  simp only [qL, ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N), PowerSeries.coe_add]

theorem qL_one : qL (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0) = 1 := by
  simp only [qL, ModularForm.qExpansion_one, PowerSeries.coe_one]

theorem qL_const (c : ℂ) :
    qL (c • (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0)) =
      algebraMap ℂ (LaurentSeries ℂ) c := by
  rw [qL, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N), ModularForm.qExpansion_one,
    Algebra.smul_def, mul_one, HahnSeries.algebraMap_apply']

theorem one_ne_zero' : (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0) ≠ 0 := by
  intro h
  have := congrArg
    (fun F : ModularForm (CongruenceSubgroup.Gamma0 N) 0 => (F : ℍ → ℂ) UpperHalfPlane.I) h
  simp [ModularForm.one_coe_eq_one] at this

theorem mul_ne_zero' {a b : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) a)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) b) (hf : f ≠ 0) (hg : g ≠ 0) :
    f.mul g ≠ 0 := by
  intro hfg
  have h := congrArg (qL (N := N)) hfg
  rw [qL_mul] at h
  have h0 : qL (0 : ModularForm (CongruenceSubgroup.Gamma0 N) (a + b)) = 0 := by
    simp only [qL, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero (1 : ℝ), PowerSeries.coe_zero]
  rw [h0] at h
  exact (mul_ne_zero (qL_ne_zero f hf) (qL_ne_zero g hg)) h

variable (N) in

/-- An exact equal-weight modular quotient with a nonzero denominator. -/
def IsRatio (x : LaurentSeries ℂ) : Prop :=
  ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧ x * qL h = qL g

theorem isRatio_algebraMap (c : ℂ) : IsRatio N (algebraMap ℂ (LaurentSeries ℂ) c) :=
  ⟨0, c • 1, 1, one_ne_zero', by rw [qL_one, mul_one, qL_const]⟩

theorem IsRatio.mul {x y : LaurentSeries ℂ} (hx : IsRatio N x) (hy : IsRatio N y) :
    IsRatio N (x * y) := by
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  obtain ⟨b, g', h', hh', hye⟩ := hy
  refine ⟨a + b, g.mul g', h.mul h', mul_ne_zero' h h' hh hh', ?_⟩
  rw [qL_mul, qL_mul, ← hxe, ← hye]; ring

theorem IsRatio.add {x y : LaurentSeries ℂ} (hx : IsRatio N x) (hy : IsRatio N y) :
    IsRatio N (x + y) := by
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  obtain ⟨b, g', h', hh', hye⟩ := hy
  refine ⟨a + b, g.mul h' + ModularForm.mcast (add_comm b a) (g'.mul h), h.mul h',
    mul_ne_zero' h h' hh hh', ?_⟩
  have hc : qL (ModularForm.mcast (add_comm b a) (g'.mul h)) = qL g' * qL h := by
    rw [← qL_mul]; simp only [qL, ModularForm.coe_mcast]
  rw [qL_add, qL_mul, qL_mul, hc, ← hxe, ← hye]; ring

theorem IsRatio.inv {x : LaurentSeries ℂ} (hx : IsRatio N x) : IsRatio N x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using isRatio_algebraMap (N := N) 0
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  have hg : g ≠ 0 := by
    intro hg0
    have : qL g = 0 := by
      simp only [hg0, qL, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero (1 : ℝ),
        PowerSeries.coe_zero]
    rw [this] at hxe
    exact (mul_ne_zero hx0 (qL_ne_zero h hh)) hxe
  refine ⟨a, h, g, hg, ?_⟩
  rw [← hxe, mul_comm x, mul_comm x⁻¹, mul_assoc, mul_inv_cancel₀ hx0, mul_one]


end
end Dubon2026.SourceFunctionField.ModularRatios
