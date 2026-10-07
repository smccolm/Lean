import Dubon2026.FiniteCosetTrace
import Dubon2026.CuspCommonPeriodIntegral
import Dubon2026.PeterssonStripMellin

/-! # The genuine finite cusp family and its full-level Petersson trace -/

namespace Dubon2026

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section

local instance cuspTracePrincipalNormal (N : ℕ) : (Gamma N).Normal := Gamma_normal N

/-- Every actual coset translate is retained as a cusp form with the same principal period. -/
def cuspCosetFamily {N : ℕ} {H : Subgroup SL(2, ℤ)} (hH : Gamma N ≤ H) {k : ℤ}
    (f : CuspForm (H.map (mapGL ℝ)) k) (q : SL(2, ℤ) ⧸ H) :
    CuspForm ((Gamma N).map (mapGL ℝ)) k :=
  normalCuspAction (Gamma N) k q.out (cuspRestrictSubgroup (Subgroup.map_mono hH) f)

/-- Each family member is literally slash by the inverse coset representative. -/
theorem cuspCosetFamily_apply {N : ℕ} {H : Subgroup SL(2, ℤ)} (hH : Gamma N ≤ H) {k : ℤ}
    (f : CuspForm (H.map (mapGL ℝ)) k) (q : SL(2, ℤ) ⧸ H) :
    ⇑(cuspCosetFamily hH f q) = ⇑f ∣[k] mapGL ℝ q.out⁻¹ := rfl

/-- Petersson transport uses the genuine integral slash normalization. -/
theorem petersson_cuspCosetFamily {N : ℕ} {H : Subgroup SL(2, ℤ)} (hH : Gamma N ≤ H) {k : ℤ}
    (f : CuspForm (H.map (mapGL ℝ)) k) (q : SL(2, ℤ) ⧸ H) (z : ℍ) :
    petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z =
      petersson k f f (q.out⁻¹ • z) :=
  petersson_slash_SL k f f q.out⁻¹ z

/-- The Petersson density of a genuine integral-subgroup cusp form is invariant under that subgroup. -/
theorem cusp_petersson_integral_invariant {H : Subgroup SL(2, ℤ)} {k : ℤ}
    (f : CuspForm (H.map (mapGL ℝ)) k) (g : SL(2, ℤ)) (hg : g ∈ H) (z : ℍ) :
    petersson k f f (g • z) = petersson k f f z := by
  have hm : mapGL ℝ g ∈ H.map (mapGL ℝ) := ⟨g, hg, rfl⟩
  have hf := f.slash_action_eq' (mapGL ℝ g) hm
  change (⇑f ∣[k] g) = ⇑f at hf
  rw [← petersson_slash_SL, hf]

/-- The trace of the actual Petersson densities is invariant under the full modular group. -/
theorem cusp_petersson_trace_invariant {N : ℕ} {H : Subgroup SL(2, ℤ)}
    [Fintype (SL(2, ℤ) ⧸ H)] (hH : Gamma N ≤ H) {k : ℤ}
    (f : CuspForm (H.map (mapGL ℝ)) k) (g : SL(2, ℤ)) (z : ℍ) :
    (∑ q : SL(2, ℤ) ⧸ H, ‖petersson k (cuspCosetFamily hH f q)
      (cuspCosetFamily hH f q) (g • z)‖) =
    ∑ q : SL(2, ℤ) ⧸ H, ‖petersson k (cuspCosetFamily hH f q)
      (cuspCosetFamily hH f q) z‖ := by
  simp only [petersson_cuspCosetFamily]
  exact finiteCosetTrace_invariant H (fun z => ‖petersson k f f z‖)
    (fun g hg z => congrArg norm (cusp_petersson_integral_invariant f g hg z)) g z

/-- The aggregate horizontal square energy is genuinely one-periodic, even though each cusp expansion may have width N. -/
theorem cusp_coset_horizontal_energy_periodic {N : ℕ} {H : Subgroup SL(2, ℤ)}
    [Fintype (SL(2, ℤ) ⧸ H)] (hH : Gamma N ≤ H) {k : ℤ}
    (f : CuspForm (H.map (mapGL ℝ)) k) {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x : ℝ => ∑ q : SL(2, ℤ) ⧸ H,
      ‖cuspCosetFamily hH f q ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2) 1 := by
  intro x
  let z : ℍ := ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩
  have hz : ModularGroup.T • z =
      ⟨((x + 1 : ℝ) : ℂ) + y * Complex.I, by simpa using hy⟩ := by
    rw [modular_T_smul]
    apply UpperHalfPlane.ext
    simp [z, add_comm, add_left_comm, add_assoc]
  have ht := cusp_petersson_trace_invariant hH f ModularGroup.T z
  rw [hz] at ht
  simp only [norm_petersson_self] at ht
  have him : z.im = y := by simp [z]
  simp only [him] at ht
  have him' : (⟨((x + 1 : ℝ) : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ).im = y := by simp
  simp only [him', ← Finset.sum_mul] at ht
  exact (mul_right_cancel₀ (zpow_ne_zero _ hy.ne') ht)

/-- Parseval for the actual common-period cusp trace, on the literal full-level unit interval. -/
theorem hasSum_cusp_coset_horizontal_energy {N : ℕ} (hN : 0 < N)
    {H : Subgroup SL(2, ℤ)} [Fintype (SL(2, ℤ) ⧸ H)] (hH : Gamma N ≤ H) {k : ℤ}
    (f : CuspForm (H.map (mapGL ℝ)) k) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => (∑ q : SL(2, ℤ) ⧸ H,
      ‖(qExpansion (N : ℝ) (cuspCosetFamily hH f q)).coeff n‖ ^ 2) *
        Real.exp (-4 * Real.pi * n * y / N))
      (∫ x in (0 : ℝ)..1, ∑ q : SL(2, ℤ) ⧸ H,
        ‖cuspCosetFamily hH f q ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2) := by
  apply hasSum_cusp_common_period_energy _ hN _ hy (cusp_coset_horizontal_energy_periodic hH f hy)
  simp [strictPeriods_Gamma]

end
end Dubon2026
