import Dubon2026.SourceOriginalWeilCoverCellCoefficient

/-! DUB-17/18 -> cover reciprocity -> actual cell coefficient calculus.
The moving centered-chart coefficient equals a fixed-chart pullback locally.
The proved one-form law and inverse coordinate calculus make it analytic at
every regular source point. Forward-coordinate conditions are exactly those
already proved for each constructed cover cell. -/
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

theorem cover_coeff_eq_near :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ : OpenPartialHomeomorph (Place ℂ EE) ℂ) {Q : Place ℂ EE}, Q ∈ ζ.source →
      AnalyticAt ℂ (ζ ∘ PF Q) 0 → deriv (ζ ∘ PF Q) 0 ≠ 0 →
      ∀ θ : Ω[EE⁄ℂ], Q.differentialCoeff θ ∈ Q.toValuationSubring →
      (∀ᶠ w in 𝓝 (ζ Q), CF ζ θ w = RD Q θ ((PC Q ∘ ζ.symm) w) * deriv (PC Q ∘ ζ.symm) w) ∧
      AnalyticAt ℂ (CF ζ θ) (ζ Q) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ Q hQ ha hd θ hθ
  let φ : OpenPartialHomeomorph (Place ℂ EE) ℂ :=
    (placeCore N n radicand baseDivisor hRadicand hOrders).openPartialHomeomorph (PC Q) ⟨Q, rfl⟩
  have hφQ : Q ∈ φ.source := mem_placeChart_source N n radicand baseDivisor hRadicand hOrders Q
  have hφ0 : φ Q = 0 := placeChart_self N n radicand baseDivisor hRadicand hOrders Q
  have ha' : AnalyticAt ℂ (ζ ∘ φ.symm) (φ Q) := by rw [hφ0]; exact ha
  have hd' : deriv (ζ ∘ φ.symm) (φ Q) ≠ 0 := by rw [hφ0]; exact hd
  obtain ⟨h12, hστ, hσcont, hσc⟩ := SheetCover.coordinate_local_inverse φ ζ hφQ hQ ha' hd'
  let σ : ℂ → ℂ := PC Q ∘ ζ.symm
  have hσ0 : σ (ζ Q) = 0 := hσc.trans hφ0
  have hσnear : Tendsto σ (𝓝 (ζ Q)) (𝓝 (0 : ℂ)) := by rw [← hσ0]; exact hσcont
  have hσa : AnalyticAt ℂ σ (ζ Q) :=
    (cover_coordinate_inverse N n radicand baseDivisor hRadicand hOrders ζ hQ ha hd).1
  have hσd : ∀ᶠ w in 𝓝 (ζ Q), HasDerivAt σ (deriv (ζ ∘ PF Q) (σ w))⁻¹ w :=
    hστ.mono fun _ hw => hw.2.2
  have hlaw := hσnear.eventually (cover_one_form_law N n radicand baseDivisor hRadicand hOrders Q θ hθ)
  have hkey : ∀ᶠ w in 𝓝 (ζ Q), CF ζ θ w = RD Q θ (σ w) * deriv σ w := by
    filter_upwards [hlaw, h12, h12.eventually_nhds, hσd] with w hw h12w h12w' hσdw
    obtain ⟨_, hlaw_w⟩ := hw
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
  refine ⟨hkey, ?_⟩
  have hRa : ∀ᶠ w in 𝓝 (ζ Q), AnalyticAt ℂ (RD Q θ) (σ w) := hlaw.mono fun _ hw => hw.1
  exact ((hRa.self_of_nhds.comp hσa).mul hσa.deriv).congr (hkey.mono fun _ hw => hw.symm)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
