import Dubon2026.CuspVerticalProfile

/-! # Entire Mellin completion of the actual cusp L-series -/

namespace Dubon2026

open UpperHalfPlane ModularGroup Filter Set Asymptotics MeasureTheory
open Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Pointwise Topology

noncomputable section

/-- The actual cusp form and its literal modular S-translate constitute a strong Mellin pair; every analytic field is proved. -/
def cuspMellinFEPair {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} (f : CuspForm Γ k) (hk : 0 < k) : StrongFEPair ℂ := by
  haveI : ((toConjAct (ModularGroup.S : GL (Fin 2) ℝ)⁻¹) • Γ).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using Subgroup.IsArithmetic.conj Γ (mapGL ℚ ModularGroup.S)⁻¹
  exact {
    f := cuspVerticalProfile f
    g := cuspVerticalProfile (CuspForm.translate f ModularGroup.S)
    k := (k : ℝ)
    ε := Complex.I ^ k
    f₀ := 0
    g₀ := 0
    hf_int := (continuousOn_cuspVerticalProfile f).locallyIntegrableOn measurableSet_Ioi
    hg_int := (continuousOn_cuspVerticalProfile (CuspForm.translate f ModularGroup.S)).locallyIntegrableOn measurableSet_Ioi
    hk := by exact_mod_cast hk
    hε := zpow_ne_zero k Complex.I_ne_zero
    h_feq := fun y hy => by simpa only [smul_eq_mul] using cuspVerticalProfile_reciprocal f hy
    hf_top := fun r => by simpa only [sub_zero] using cuspVerticalProfile_isBigO_rpow f r
    hg_top := fun r => by simpa only [sub_zero] using
      cuspVerticalProfile_isBigO_rpow (CuspForm.translate f ModularGroup.S) r
    hf₀ := rfl
    hg₀ := rfl }

/-- The literal Mellin integral of the original cusp function, with no continuation premise. -/
def cuspCompletedLFunction {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) (s : ℂ) : ℂ := mellin (cuspVerticalProfile f) s

/-- The actual cusp Mellin integral is convergent at every complex parameter. -/
theorem cuspCompletedLFunction_hasMellin {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} (f : CuspForm Γ k) (hk : 0 < k) (s : ℂ) :
    HasMellin (cuspVerticalProfile f) s (cuspCompletedLFunction f s) :=
  (cuspMellinFEPair f hk).hasMellin s

/-- The actual cusp Mellin completion is entire, proved from genuine cusp decay and the modular reciprocal identity. -/
theorem cuspCompletedLFunction_differentiable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} (f : CuspForm Γ k) (hk : 0 < k) :
    Differentiable ℂ (cuspCompletedLFunction f) :=
  (cuspMellinFEPair f hk).differentiable_Λ

/-- The original cusp Mellin completion satisfies its exact modular S-transform functional equation. -/
theorem cuspCompletedLFunction_functional_equation {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} (f : CuspForm Γ k) (hk : 0 < k) (s : ℂ) :
    cuspCompletedLFunction f ((k : ℂ) - s) =
      Complex.I ^ k * cuspCompletedLFunction (CuspForm.translate f ModularGroup.S) s := by
  simpa only [smul_eq_mul, Complex.ofReal_intCast] using (cuspMellinFEPair f hk).functional_equation s

end
end Dubon2026
