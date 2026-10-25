import Dubon2026.SourceOriginalWeilCoverCoordinateTransition
import Dubon2026.SourceOriginalWeilCoverCellCoefficientTransition
import Dubon2026.SourceRadialCellBoundaryCoordinates

/-! DUB-17/18 -> cover reciprocity -> actual cell coefficient calculus.
The actual coefficient transformation cancels the derivative of the primitive
difference along a shared edge. Native interval FTC extends the constant jump
through both endpoints; no jump-existence assumption is used. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry MeasureTheory
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

theorem cover_primitive_jump_on_arc :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (C C' : RadialCell (Place ℂ EE)),
      (∀ P ∈ C.ζ.source, AnalyticAt ℂ (C.ζ ∘ PF P) 0 ∧ deriv (C.ζ ∘ PF P) 0 ≠ 0) →
      (∀ P ∈ C'.ζ.source, AnalyticAt ℂ (C'.ζ ∘ PF P) 0 ∧ deriv (C'.ζ ∘ PF P) 0 ≠ 0) →
      ∀ (k : Fin C.R.N),
      (∀ s ∈ C.R.arcIcc k, C.bdry s ∈ C'.ζ.source ∧ C'.ζ (C.bdry s) ∈ C'.R.K) →
      ∀ (η : Ω[EE⁄ℂ]) (Ψ Ψ' : ℂ → ℂ),
      (∀ w ∈ C.R.K, HasDerivAt Ψ (CF C.ζ η w) w) →
      (∀ w ∈ C'.R.K, HasDerivAt Ψ' (CF C'.ζ η w) w) →
      ∃ J : ℂ, ∀ s ∈ C.R.arcIcc k,
        Ψ (C.R.loop s) - Ψ' (C'.ζ (C.bdry s)) = J := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro C C' hC hC' k hover η Ψ Ψ' hΨ hΨ'
  let a := C.R.φs k.castSucc
  let b := C.R.φs k.succ
  let D : ℝ → ℂ := fun s => Ψ (C.R.loop s) - Ψ' (C'.ζ (C.bdry s))
  have hDc : ContinuousOn D (Icc a b) := by
    intro s hs
    have h1 := (hΨ _ (C.R.loop_mem_K s)).continuousAt.comp C.R.continuous_loop.continuousAt
    have h2 := ((hΨ' _ (hover s hs).2).continuousAt.comp
      (C'.ζ.continuousAt (hover s hs).1)).comp C.continuous_bdry.continuousAt
    exact (h1.sub h2).continuousWithinAt
  have hDd : ∀ s ∈ Ioo a b, HasDerivAt D 0 s := by
    intro s hs
    have hsI : s ∈ C.R.arcIcc k := ⟨hs.1.le, hs.2.le⟩
    have hsrc := (C.bdry_coordinates s).1
    have hval := (C.bdry_coordinates s).2
    have hsrc' := (hover s hsI).1
    have hγ := C.R.hasDerivAt_loop k hs
    have h1 := (hΨ _ (C.R.loop_mem_K s)).comp s hγ
    have hTa := cover_analyticAt_coordinate_transition N n radicand baseDivisor hRadicand hOrders
      C.ζ C'.ζ hsrc (hC _ hsrc).1 (hC _ hsrc).2 (hC' _ hsrc').1
    have hTd : HasDerivAt (C'.ζ ∘ C.ζ.symm)
        (deriv (C'.ζ ∘ C.ζ.symm) (C.ζ (C.bdry s))) (C.R.loop s) := by
      rw [← hval]
      exact hTa.differentiableAt.hasDerivAt
    have hz : HasDerivAt (fun s => C'.ζ (C.bdry s))
        (deriv (C'.ζ ∘ C.ζ.symm) (C.ζ (C.bdry s)) * C.R.loop' s) s := hTd.comp s hγ
    have h2 := (hΨ' _ (hover s hsI).2).comp s hz
    have he := cover_coeff_transition N n radicand baseDivisor hRadicand hOrders C.ζ C'.ζ
      hsrc hsrc' (hC _ hsrc).1 (hC _ hsrc).2 (hC' _ hsrc').1 (hC' _ hsrc').2 η
    rw [hval] at he
    have hc : CF C.ζ η (C.R.loop s) * C.R.loop' s =
        CF C'.ζ η (C'.ζ (C.bdry s)) *
          (deriv (C'.ζ ∘ C.ζ.symm) (C.ζ (C.bdry s)) * C.R.loop' s) := by
      rw [he, hval]
      ring
    have hsub := h1.sub h2
    rw [hc, sub_self] at hsub
    exact hsub
  refine ⟨D a, ?_⟩
  intro s hs
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
    (hDc.mono (Icc_subset_Icc le_rfl hs.2))
    (fun u hu => hDd u ⟨hu.1, hu.2.trans_le hs.2⟩)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume a s)
  rw [intervalIntegral.integral_zero] at he
  exact sub_eq_zero.mp he.symm

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
