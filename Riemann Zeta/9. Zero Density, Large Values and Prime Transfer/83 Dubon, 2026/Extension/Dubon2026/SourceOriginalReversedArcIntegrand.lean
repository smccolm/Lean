import Dubon2026.SourceOriginalCellCoefficientTransition
import Dubon2026.SourceOriginalCellBoundaryIntegrability

/-! DUB-17/18 -> raw reciprocity -> cancellation of paired boundary integrals.
The exact coefficient transition and derivative uniqueness transport the actual
original differential integrand under a reversed source arc. No regularity or
integral-transformation premise is used in this pointwise identity.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Topology
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem Cell.reversed_arc_integrand (C C' : Cell N) (k : Fin C.R.N) (k' : Fin C'.R.N)
    (ψ : ℝ → ℝ) (hanti : StrictAntiOn ψ (C'.R.arcIcc k'))
    (ha : ψ (C'.R.φs k'.castSucc) = C.R.φs k.succ)
    (hb : ψ (C'.R.φs k'.succ) = C.R.φs k.castSucc)
    (hbd : ∀ u ∈ C'.R.arcIcc k', C'.bdry u = C.bdry (ψ u))
    (θ : Ω[F⁄ℂ]) {t d : ℝ}
    (ht : t ∈ Ioo (C'.R.φs k'.castSucc) (C'.R.φs k'.succ))
    (hd : HasDerivAt ψ d t) :
    C'.bdryIntegrand θ t = C.bdryIntegrand θ (ψ t) * d := by
  have hab' : C'.R.φs k'.castSucc < C'.R.φs k'.succ := C'.R.hmono Fin.castSucc_lt_succ
  have htI : t ∈ C'.R.arcIcc k' := ⟨ht.1.le, ht.2.le⟩
  have hψt : ψ t ∈ Ioo (C.R.φs k.castSucc) (C.R.φs k.succ) := by
    constructor
    · rw [← hb]
      exact hanti htI (right_mem_Icc.mpr hab'.le) ht.2
    · rw [← ha]
      exact hanti (left_mem_Icc.mpr hab'.le) htI ht.1
  let Q := C'.bdry t
  have hQ : Q = C.bdry (ψ t) := hbd t htI
  have hs' : Q ∈ C'.ζ.source := (C'.bdry_coordinates t).1
  have hs : Q ∈ C.ζ.source := hQ ▸ (C.bdry_coordinates (ψ t)).1
  have hz' : C'.ζ Q = C'.R.loop t := (C'.bdry_coordinates t).2
  have hz : C.ζ Q = C.R.loop (ψ t) := by rw [hQ]; exact (C.bdry_coordinates (ψ t)).2
  have hT := (C'.toAnalyticCoord.analyticAt_transition C.toAnalyticCoord hs' hs).differentiableAt.hasDerivAt
  rw [hz'] at hT
  have hleft := hT.comp t (C'.R.hasDerivAt_loop k' ht)
  have hright := (C.R.hasDerivAt_loop k hψt).scomp t hd
  have he : (C.ζ ∘ C'.ζ.symm) ∘ C'.R.loop =ᶠ[𝓝 t] C.R.loop ∘ ψ := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    change C.ζ (C'.bdry u) = C.R.loop (ψ u)
    rw [hbd u ⟨hu.1.le, hu.2.le⟩, (C.bdry_coordinates (ψ u)).2]
  have hder := hleft.unique (hright.congr_of_eventuallyEq he)
  have hcoeff := C'.toAnalyticCoord.coeff_transition C.toAnalyticCoord hs' hs θ
  rw [hz', hz] at hcoeff
  change coeffIn C'.ζ θ (C'.R.loop t) * C'.R.loop' t =
    (coeffIn C.ζ θ (C.R.loop (ψ t)) * C.R.loop' (ψ t)) * d
  rw [hcoeff, mul_assoc, hder, Complex.real_smul]
  ring

end
end Dubon2026.SourceFunctionField.CellGeometry
