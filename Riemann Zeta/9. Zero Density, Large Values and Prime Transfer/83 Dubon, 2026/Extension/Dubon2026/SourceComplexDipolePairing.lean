import Dubon2026.SourceComplexDipoleLogDerivative
import Dubon2026.SourceComplexWedgeIntegral

/-! Adapted from anthropics/fermats-last-theorem (Apache-2.0), pinned
S_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq.
DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1
Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> smooth invariant
comparison function -> compact dipole with exact integer local orders.
The existing wedge/residue identity and antiholomorphic derivative are reused.
This constructs a smooth local comparison, without assuming meromorphic
realization or the desired principal-divisor converse. -/
namespace Dubon2026.SourceComplexReciprocity.Dipole
noncomputable section
open Complex MeasureTheory Filter Set Metric DbarFundamental
open scoped Real Topology Manifold ContDiff
local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet

section Core
variable {b s : ℂ} (hb : 0 < b.im) (hs : 0 < s.im) (hbs : b ≠ s)
  {χ : ℂ → ℝ} {O K : Set ℂ}
  (hχ : ContDiff ℝ 2 χ) (hO : IsOpen O) (hSeg : segment ℝ b s ⊆ O) (hχ1 : ∀ z ∈ O, χ z = 1)
  (hOK : O ⊆ K) (hK : IsClosed K) (hχK : tsupport χ ⊆ K) (h01 : ∀ z, χ z ∈ Icc (0 : ℝ) 1)

variable {η : ℂ → ℂ} {O' : Set ℂ} (hη : ContDiff ℝ 2 η) (hηs : HasCompactSupport η)
  (hηU : tsupport η ⊆ 𝕌) (hO' : IsOpen O') (hKO' : K ⊆ O') (hη1 : ∀ z ∈ O', η z = 1)
  (hKU : K ⊆ 𝕌)

include hbs hχ hO hSeg hχ1 hOK hK hχK h01 hη hηs hηU hO' hKO' hη1 in

theorem pairing (E E' : ℂ → ℂ) (hE : ∀ z : ℂ, 0 < z.im → HasDerivAt E (E' z) z) :
    Integrable (fun z => E' z * Ffun b s χ z) ∧
      ∫ z, E' z * Ffun b s χ z = π * (E s - E b) := by
  have hbK : b ∈ K := hOK (hSeg (left_mem_segment _ _ _))
  have hsK : s ∈ K := hOK (hSeg (right_mem_segment _ _ _))
  set nd : ℂ → ℤ := fun a => (if a = s then (1 : ℤ) else 0) - (if a = b then (1 : ℤ) else 0)
    with hnd
  have hUo : IsOpen (𝕌 : Set ℂ) := Complex.continuous_im.isOpen_preimage _ isOpen_Ioi
  obtain ⟨-, hI2, hId⟩ :=
    Wedge.integral_wedge_residue_identity 𝕌 hUo (dfun b s χ) nd
      (fun τ _ => dfun_localModel hbs hχ hO hSeg hχ1 h01 τ) E E' (fun z hz => hE z hz) η hη hηs hηU

  have hW : (fun z : ℂ => E z / dfun b s χ z *
      (fderiv ℝ (dfun b s χ) z 1 * fderiv ℝ η z I - fderiv ℝ (dfun b s χ) z I * fderiv ℝ η z 1)) =
      fun _ => 0 := by
    funext z
    by_cases hz : z ∈ O'
    · have hev : η =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
        filter_upwards [hO'.mem_nhds hz] with w hw using hη1 w hw
      simp [hev.fderiv_eq]
    · have hzK : z ∉ K := fun h => hz (hKO' h)
      have hev : dfun b s χ =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
        filter_upwards [hK.isOpen_compl.mem_nhds hzK] with w hw using dfun_eq_one hχK hw hbK
      simp [hev.fderiv_eq]

  have hpt : ∑ᶠ a : ℂ, (nd a : ℂ) * E a * η a = E s - E b := by
    have hsupp : (Function.support fun a : ℂ => (nd a : ℂ) * E a * η a) ⊆ ({s, b} : Finset ℂ) := by
      intro a ha
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra h
      push Not at h
      apply ha
      simp [hnd, h.1, h.2]
    rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_pair hbs.symm]
    simp [hnd, hbs, hbs.symm, hη1 s (hKO' hsK), hη1 b (hKO' hbK)]
    ring

  have haeF : (fun z : ℂ => E' z * η z *
      ((fderiv ℝ (dfun b s χ) z 1 + I * fderiv ℝ (dfun b s χ) z I) / 2 / dfun b s χ z)) =ᵐ[volume]
      fun z => E' z * Ffun b s χ z := by
    have : ∀ᵐ z : ℂ, z ≠ b := by
      have h0 : volume ({b} : Set ℂ) = 0 := measure_singleton b
      exact measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [this] with z hz
    rw [mul_assoc, dbar_dfun_div hχ hO hSeg hχ1 h01 hz]
    congr 1
    by_cases hzK : z ∈ K
    · rw [hη1 z (hKO' hzK), one_mul]
    · have : Ffun b s χ z = 0 := by
        by_contra h
        exact hzK (support_Ffun_subset hχK (Function.mem_support.2 h))
      rw [this, mul_zero]
  refine ⟨hI2.congr haeF, ?_⟩
  rw [hW, hpt, integral_congr_ae haeF] at hId
  simp only [integral_zero, mul_zero, zero_add] at hId
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp at hId
  linear_combination -hId

end Core
end
end Dubon2026.SourceComplexReciprocity.Dipole
