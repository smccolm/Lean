import Dubon2026.SourceOriginalWeilCoverPuncturedOneFormLaw

/-! DUB-17/18 -> cover Abel converse -> meromorphic generation and residue
reciprocity -> actual cell simple-pole coefficients. Reuse finite differential
support, the existing one-form law, inverse coordinates and logarithmic reading.
The generic simple-pole pullback theorem is reused unchanged. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "PC" => placeChart N n radicand baseDivisor hRadicand hOrders
local notation "PF" => placeFamily N n radicand baseDivisor hRadicand hOrders
local notation "RD" => readDifferential N n radicand baseDivisor hRadicand hOrders
local notation "CF" => coverCoeffIn N n radicand baseDivisor hRadicand hOrders


theorem cover_inverse_tendsto_punctured :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ : OpenPartialHomeomorph (Place ℂ EE) ℂ) {Q : Place ℂ EE}, Q ∈ ζ.source →
      AnalyticAt ℂ (ζ ∘ PF Q) 0 → deriv (ζ ∘ PF Q) 0 ≠ 0 →
      Tendsto (PC Q ∘ ζ.symm) (𝓝[≠] (ζ Q)) (𝓝[≠] (0 : ℂ)) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ Q hQ ha hd
  have hinv := (cover_coordinate_inverse N n radicand baseDivisor hRadicand hOrders ζ hQ ha hd).2
  have hzero : (PC Q ∘ ζ.symm) (ζ Q) = 0 := by
    simp only [Function.comp_apply, ζ.left_inv hQ, placeChart_self]
  have ht := hinv.tendsto_nhdsNE (inv_ne_zero hd)
  rwa [hzero] at ht

theorem cover_coeff_eq_near_punctured :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ : OpenPartialHomeomorph (Place ℂ EE) ℂ) {Q : Place ℂ EE}, Q ∈ ζ.source →
      AnalyticAt ℂ (ζ ∘ PF Q) 0 → deriv (ζ ∘ PF Q) 0 ≠ 0 →
      ∀ θ : Ω[EE⁄ℂ], ∀ᶠ w in 𝓝[≠] (ζ Q),
      CF ζ θ w = RD Q θ ((PC Q ∘ ζ.symm) w) * deriv (PC Q ∘ ζ.symm) w := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ Q hQ ha hd θ
  let φ : OpenPartialHomeomorph (Place ℂ EE) ℂ :=
    (placeCore N n radicand baseDivisor hRadicand hOrders).openPartialHomeomorph (PC Q) ⟨Q, rfl⟩
  have hφQ : Q ∈ φ.source := mem_placeChart_source N n radicand baseDivisor hRadicand hOrders Q
  have hφ0 : φ Q = 0 := placeChart_self N n radicand baseDivisor hRadicand hOrders Q
  have ha' : AnalyticAt ℂ (ζ ∘ φ.symm) (φ Q) := by rw [hφ0]; exact ha
  have hd' : deriv (ζ ∘ φ.symm) (φ Q) ≠ 0 := by rw [hφ0]; exact hd
  obtain ⟨h12, hστ, _, _⟩ := SheetCover.coordinate_local_inverse φ ζ hφQ hQ ha' hd'
  let σ : ℂ → ℂ := PC Q ∘ ζ.symm
  have hσd : ∀ᶠ w in 𝓝 (ζ Q), HasDerivAt σ (deriv (ζ ∘ PF Q) (σ w))⁻¹ w :=
    hστ.mono fun _ hw => hw.2.2
  have hlaw := (cover_inverse_tendsto_punctured N n radicand baseDivisor hRadicand hOrders ζ hQ ha hd).eventually
    (cover_one_form_law_punctured N n radicand baseDivisor hRadicand hOrders Q θ)
  have hkey : ∀ᶠ w in 𝓝[≠] (ζ Q), CF ζ θ w = RD Q θ (σ w) * deriv σ w := by
    filter_upwards [hlaw, h12.filter_mono nhdsWithin_le_nhds,
      h12.eventually_nhds.filter_mono nhdsWithin_le_nhds, hσd.filter_mono nhdsWithin_le_nhds]
      with w hlaw_w h12w h12w' hσdw
    have hback : PF Q (σ w) = ζ.symm w := φ.left_inv h12w.2
    rw [hback] at hlaw_w
    let Qw := ζ.symm w
    have hT : AnalyticAt ℂ (PC Qw ∘ PF Q) (σ w) := by
      apply analyticOnNhd_placeChart_transition N n radicand baseDivisor hRadicand hOrders Q Qw
      refine ⟨φ.map_source h12w.2, ?_⟩
      change PF Q (σ w) ∈ (PC Qw).source
      rw [hback]
      exact mem_placeChart_source N n radicand baseDivisor hRadicand hOrders Qw
    have hchain : deriv (PC Qw ∘ ζ.symm) w = deriv (PC Qw ∘ PF Q) (σ w) * deriv σ w := by
      have hev : (PC Qw ∘ ζ.symm) =ᶠ[𝓝 w] (PC Qw ∘ PF Q) ∘ σ := by
        filter_upwards [h12w'] with w' hw'
        have hb : PF Q (σ w') = ζ.symm w' := φ.left_inv hw'.2
        change PC Qw (ζ.symm w') = PC Qw (PF Q (σ w'))
        rw [hb]
      rw [hev.deriv_eq, hσdw.deriv]
      exact (hT.differentiableAt.hasDerivAt.comp w hσdw).deriv
    change RD Qw θ 0 * deriv (PC Qw ∘ ζ.symm) w = RD Q θ (σ w) * deriv σ w
    rw [hlaw_w, hchain]
    ring
  exact hkey

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
