import Dubon2026.SourceOriginalMeromorphicBoundaryJumps
import Dubon2026.SourceOriginalDualTreeNormalization

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
The existing exact dual-tree normalization removes logarithmic boundary jumps
by changing only cell constants. Domains and all residue-subtracted derivatives
are preserved; no new graph or integration infrastructure is introduced.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential IntegerEdgeChains DissectionTrees
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem regPrimData_add_const {D : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ]) {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) (c : D.ιC → R → ℂ) :
    RegPrimData S θ V (fun r C w => Ψ r C w + c C r) :=
  ⟨hP.hVo, hP.hVstar, hP.hKV, hP.hVgood, fun r C w hw => (hP.hΨ r C w hw).add_const _⟩

theorem hfun_add_const {D : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ]) (Ψ : R → D.ιC → ℂ → ℂ) (c : D.ιC → R → ℂ)
    (C : D.ιC) (s : ℝ) :
    hfun S θ (fun r C w => Ψ r C w + c C r) C s = hfun S θ Ψ C s + c C := by
  funext r
  simp only [hfun, Pi.add_apply]
  ring

theorem isJumpH_add_const {D : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ]) {Ψ : R → D.ιC → ℂ → ℂ} {J : D.ιE → R → ℂ}
    (hJ : IsJumpH D (hfun S θ Ψ) J) (c : D.ιC → R → ℂ) :
    IsJumpH D (hfun S θ (fun r C w => Ψ r C w + c C r))
      (fun e => J e + c (D.arcOf (e, true)).1 - c (D.arcOf (e, false)).1) := by
  intro e
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := hJ e
  refine ⟨ψ, h1, h2, h3, h4, fun t ht => ?_⟩
  simp only [hfun_add_const]
  rw [← h5 t ht]
  abel

theorem normalize_regPrimData {D : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ]) {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) (Ts : Finset D.ιE)
    (hTs : IsTree (fun e => Cside D e true) (fun e => Cside D e false) Ts)
    (C₀ : D.ιC) :
    ∃ (Ψ' : R → D.ιC → ℂ → ℂ) (J : D.ιE → R → ℂ),
      RegPrimData S θ V Ψ' ∧ IsJumpH D (hfun S θ Ψ') J ∧ ∀ e ∈ Ts, J e = 0 := by
  obtain ⟨J, hJ⟩ := exists_isJumpH S θ hP
  obtain ⟨c, _, hc⟩ := D.exists_normalising_constants Ts hTs J C₀ 0
  exact ⟨_, _, regPrimData_add_const S θ hP c, isJumpH_add_const S θ hJ c, hc⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
