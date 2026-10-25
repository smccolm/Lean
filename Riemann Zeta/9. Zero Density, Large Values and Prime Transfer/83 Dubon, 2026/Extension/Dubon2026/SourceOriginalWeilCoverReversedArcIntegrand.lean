import Dubon2026.SourceOriginalWeilCoverBoundaryCoefficient
import Dubon2026.SourceOriginalWeilCoverCellCoefficientTransition
import Dubon2026.SourceOriginalWeilCoverCoordinateTransition

/-! DUB-17/18 -> cover Abel converse -> bilinear/third-kind reciprocity ->
weighted paired-edge cancellation. Reuse native continuous arc extension,
derivative uniqueness and reversed C1 integration on the actual cover cells.
The actual dissection supplies forward coordinate and paired-overlap inputs. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
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

local notation "BI" => coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders

theorem cover_reversed_arc_integrand :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (C C' : RadialCell (Place ℂ EE)),
      (∀ P ∈ C.ζ.source, AnalyticAt ℂ (C.ζ ∘ PF P) 0 ∧ deriv (C.ζ ∘ PF P) 0 ≠ 0) →
      (∀ P ∈ C'.ζ.source, AnalyticAt ℂ (C'.ζ ∘ PF P) 0 ∧ deriv (C'.ζ ∘ PF P) 0 ≠ 0) →
      ∀ (k : Fin C.R.N) (k' : Fin C'.R.N) (ψ : ℝ → ℝ),
      StrictAntiOn ψ (C'.R.arcIcc k') →
      ψ (C'.R.φs k'.castSucc) = C.R.φs k.succ →
      ψ (C'.R.φs k'.succ) = C.R.φs k.castSucc →
      (∀ u ∈ C'.R.arcIcc k', C'.bdry u = C.bdry (ψ u)) →
      ∀ (θ : Ω[EE⁄ℂ]) {t d : ℝ},
      t ∈ Ioo (C'.R.φs k'.castSucc) (C'.R.φs k'.succ) → HasDerivAt ψ d t →
      BI C' θ t = BI C θ (ψ t) * d := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro C C' hC hC' k k' ψ hanti ha hb hbd θ t d ht hd
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
  have hT := (cover_analyticAt_coordinate_transition N n radicand baseDivisor hRadicand hOrders C'.ζ C.ζ hs'
    (hC' Q hs').1 (hC' Q hs').2 (hC Q hs).1).differentiableAt.hasDerivAt
  rw [hz'] at hT
  have hleft := hT.comp t (C'.R.hasDerivAt_loop k' ht)
  have hright := (C.R.hasDerivAt_loop k hψt).scomp t hd
  have he : (C.ζ ∘ C'.ζ.symm) ∘ C'.R.loop =ᶠ[𝓝 t] C.R.loop ∘ ψ := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    change C.ζ (C'.bdry u) = C.R.loop (ψ u)
    rw [hbd u ⟨hu.1.le, hu.2.le⟩, (C.bdry_coordinates (ψ u)).2]
  have hder := hleft.unique (hright.congr_of_eventuallyEq he)
  have hcoeff := cover_coeff_transition N n radicand baseDivisor hRadicand hOrders C'.ζ C.ζ hs' hs (hC' Q hs').1 (hC' Q hs').2 (hC Q hs).1 (hC Q hs).2 θ
  rw [hz', hz] at hcoeff
  change CF C'.ζ θ (C'.R.loop t) * C'.R.loop' t =
    (CF C.ζ θ (C.R.loop (ψ t)) * C.R.loop' (ψ t)) * d
  rw [hcoeff, mul_assoc, hder, Complex.real_smul]
  ring

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
