import Dubon2026.SourceSmoothProjectiveOrbitSum
import Dubon2026.SourceComplexDipoleLocalModel

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant comparison V.
Actual local product and action rules identify V's antiholomorphic logarithmic
derivative. The existing DbarFundamental.D and Dipole.dbarL operations are
reused; no second derivative operator is introduced. Adapted from the pinned
Apache-2.0 scope-889 construction. The finite product is later supplied by
proper discontinuity, rather than assumed for the whole orbit product. -/
namespace Dubon2026.SourceSmoothDivisor
noncomputable section
open UpperHalfPlane hiding I
open Complex Filter
open SourceComplexReciprocity.Dipole
open scoped MatrixGroups Topology ComplexConjugate
local notation "dbar" => SourceComplexReciprocity.DbarFundamental.D

theorem dbarL_comp_smul (T : ℂ →L[ℝ] ℂ) (d : ℂ) :
    dbarL (T.comp (d • (1 : ℂ →L[ℝ] ℂ))) = conj d * dbarL T := by
  have hlin : ∀ w : ℂ, T w = (w.re : ℂ) * T 1 + (w.im : ℂ) * T Complex.I := by
    intro w
    conv_lhs => rw [← Complex.re_add_im w]
    rw [map_add]
    have h1 : T (w.re : ℂ) = (w.re : ℂ) * T 1 := by
      rw [show ((w.re : ℂ)) = (w.re : ℝ) • (1 : ℂ) by simp, T.map_smul]; simp
    have h2 : T ((w.im : ℂ) * Complex.I) = (w.im : ℂ) * T Complex.I := by
      rw [show ((w.im : ℂ) * Complex.I) = (w.im : ℝ) • Complex.I by simp, T.map_smul]; simp
    rw [h1, h2]
  simp only [dbarL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, mul_one]
  rw [hlin d, hlin (d * Complex.I)]
  apply Complex.ext <;> simp <;> ring

theorem dbar_comp_sm (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) {f : ℂ → ℂ}
    (hf : DifferentiableAt ℝ f (sm σ z)) :
    dbar (fun u => f (sm σ u)) z = conj (dsm σ z) * dbar f (sm σ z) := by
  have h : HasFDerivAt (fun u => f (sm σ u)) ((fderiv ℝ f (sm σ z)).comp (dsm σ z • (1 : ℂ →L[ℝ] ℂ))) z :=
    hf.hasFDerivAt.comp z (hasFDerivAt_sm σ hz)
  rw [SourceComplexReciprocity.Dipole.dbar_eq, h.fderiv, dbarL_comp_smul, SourceComplexReciprocity.Dipole.dbar_eq]

theorem dbar_zpow_div {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (h0 : f z ≠ 0) (m : ℤ) :
    dbar (fun u => f u ^ m) z / f z ^ m = m * (dbar f z / f z) := by
  have h : HasFDerivAt (fun u => f u ^ m) (((m : ℂ) * f z ^ (m - 1)) • fderiv ℝ f z) z :=
    (hasDerivAt_zpow m (f z) (Or.inl h0)).comp_hasFDerivAt z hf.hasFDerivAt
  rw [SourceComplexReciprocity.Dipole.dbar_eq, h.fderiv, dbarL_smul, ← SourceComplexReciprocity.Dipole.dbar_eq]
  have : f z ^ m ≠ 0 := zpow_ne_zero _ h0
  have h1 : f z ^ (m - 1) = f z ^ m / f z := by
    rw [zpow_sub_one₀ h0]; ring
  rw [h1]; field_simp

theorem dbar_mul_div {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (hf0 : f z ≠ 0) (hg0 : g z ≠ 0) :
    dbar (fun u => f u * g u) z / (f z * g z) = dbar f z / f z + dbar g z / g z := by
  rw [SourceComplexReciprocity.Dipole.dbar_eq, fderiv_fun_mul hf hg, dbarL_add, dbarL_smul, dbarL_smul, ← SourceComplexReciprocity.Dipole.dbar_eq,
    ← SourceComplexReciprocity.Dipole.dbar_eq]
  field_simp; ring

theorem dbar_prod_div {ι : Type*} (P : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i ∈ P, DifferentiableAt ℝ (f i) z) (h0 : ∀ i ∈ P, f i z ≠ 0) :
    dbar (fun u => ∏ i ∈ P, f i u) z / (∏ i ∈ P, f i z) = ∑ i ∈ P, dbar (f i) z / f i z := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [SourceComplexReciprocity.DbarFundamental.D]
  | insert a P ha ih =>
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h0' := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    have hd : DifferentiableAt ℝ (fun u => ∏ i ∈ P, f i u) z :=
      (HasFDerivAt.finsetProd (fun i hi => (hf' i hi).hasFDerivAt)).differentiableAt
    rw [dbar_mul_div (g := fun u => ∏ i ∈ P, f i u) (hf a (Finset.mem_insert_self a P)) hd
      (h0 a (Finset.mem_insert_self a P)) (Finset.prod_ne_zero_iff.2 h0'), ← ih hf' h0']

theorem dbar_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dbar f z = dbar g z := by
  simp only [SourceComplexReciprocity.DbarFundamental.D, h.fderiv_eq]

end
end Dubon2026.SourceSmoothDivisor
