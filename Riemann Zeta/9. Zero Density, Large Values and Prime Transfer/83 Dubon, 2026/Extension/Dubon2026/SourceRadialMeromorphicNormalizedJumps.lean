import Dubon2026.SourceRadialMeromorphicBoundaryJumps
import Dubon2026.SourceRadialDualTreeNormalization

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Reuse the exact dual-tree constant transport. Adding cell constants preserves
all primitive domains and derivatives and kills the dual-tree jumps. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
noncomputable section
open Set IntegerEdgeChains RadialDissectionTrees
variable {X R : Type*} [TopologicalSpace X]

theorem regPrimData_add_const {D : RadialCellDissection X} {S : Finset X}
    {f : R → D.ιC → ℂ → ℂ} {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ}
    (hP : RegPrimData D S f V Ψ) (c : D.ιC → R → ℂ) :
    RegPrimData D S f V (fun r C w => Ψ r C w + c C r) :=
  ⟨hP.hVo, hP.hVstar, hP.hKV, hP.hVgood, fun r C w hw => (hP.hΨ r C w hw).add_const _⟩

theorem hfun_add_const {D : RadialCellDissection X} (S : Finset X)
    (residue : X → R → ℂ) (Ψ : R → D.ιC → ℂ → ℂ) (c : D.ιC → R → ℂ)
    (C : D.ιC) (s : ℝ) :
    hfun S residue (fun r C w => Ψ r C w + c C r) C s = hfun S residue Ψ C s + c C := by
  funext r
  simp only [hfun, Pi.add_apply]
  ring

theorem isJumpH_add_const {D : RadialCellDissection X} (S : Finset X)
    (residue : X → R → ℂ) {Ψ : R → D.ιC → ℂ → ℂ} {J : D.ιE → R → ℂ}
    (hJ : IsJumpH D (hfun S residue Ψ) J) (c : D.ιC → R → ℂ) :
    IsJumpH D (hfun S residue (fun r C w => Ψ r C w + c C r))
      (fun e => J e + c (D.arcOf (e, true)).1 - c (D.arcOf (e, false)).1) := by
  intro e
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := hJ e
  refine ⟨ψ, h1, h2, h3, h4, fun t ht => ?_⟩
  simp only [hfun_add_const]
  rw [← h5 t ht]
  abel

theorem normalize_regPrimData {D : RadialCellDissection X} (S : Finset X)
    (residue : X → R → ℂ) {f : R → D.ιC → ℂ → ℂ}
    {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ} (hP : RegPrimData D S f V Ψ)
    {J : D.ιE → R → ℂ} (hJ : IsJumpH D (hfun S residue Ψ) J) (Ts : Finset D.ιE)
    (hTs : IsTree (fun e => Cside D e true) (fun e => Cside D e false) Ts) (C₀ : D.ιC) :
    ∃ (Ψ' : R → D.ιC → ℂ → ℂ) (J' : D.ιE → R → ℂ),
      RegPrimData D S f V Ψ' ∧ IsJumpH D (hfun S residue Ψ') J' ∧ ∀ e ∈ Ts, J' e = 0 := by
  obtain ⟨c, _, hc⟩ := D.exists_normalising_constants Ts hTs J C₀ 0
  exact ⟨_, _, regPrimData_add_const hP c, isJumpH_add_const S residue hJ c, hc⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
