import Dubon2026.SourceOriginalWeilCoverOnePole
import Dubon2026.SourceOriginalWeilCoverEvaluationContinuity
import Dubon2026.SourceOriginalWeilCoverCompact
import Mathlib.Analysis.Complex.AbsMax

/-! DUB-17/18 -> auxiliary connectedness -> the actual clopen obstruction.
Reuse the original curve's short maximum-modulus argument with the literal
cover place set and genuine residue evaluation. Compactness forces an
interior maximum; local constancy contradicts the proved finite normalized
order of a nonzero field element minus its constant value.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial Set Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])
variable (D : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hf : f ≠ 0)
variable (hfD : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord f = (n : ℤ) * D v)
include D hf hfD

theorem false_of_proper_clopen :
    letI := placeTopology N n f D hf hfD
    ∀ U : Set (Place ℂ EE), IsClopen U → ∀ v ∈ U, Uᶜ.Nonempty → False := by
  letI := placeTopology N n f D hf hfD
  letI := place_compactSpace N n f D hf hfD
  intro U hU v hv hne
  obtain ⟨a, hac, hareg⟩ := exists_cover_nonconstant_regular_away N n f v
  let ev : Place ℂ EE → ℂ := fun w =>
    w.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f w) a
  have hreg : ∀ w ∈ Uᶜ, a ∈ w.toValuationSubring :=
    fun w hw => hareg w (fun h => hw (h ▸ hv))
  have hcont : ContinuousOn (fun w => ‖ev w‖) Uᶜ :=
    fun w hw => ((continuousAt_place_eval N n f D hf hfD w (hreg w hw)).norm).continuousWithinAt
  obtain ⟨w, hw, hmax⟩ := hU.compl.isClosed.isCompact.exists_isMaxOn hne hcont
  have hloc : IsLocalMax (fun w => ‖ev w‖) w :=
    hmax.isLocalMax (hU.compl.isOpen.mem_nhds hw)
  let G : ℂ → ℂ := fun z => ev (placeFamily N n f D hf hfD w z)
  have hloc' : IsLocalMax (norm ∘ G) 0 := by
    have h : IsLocalMax (fun w => ‖ev w‖) (placeFamily N n f D hf hfD w 0) := by
      rw [(place_spec N n f D hf hfD w).2.1]
      exact hloc
    exact h.comp_tendsto (placeFamily_continuousAt_zero N n f D hf hfD w)
  have han : AnalyticAt ℂ G 0 := analyticAt_place_reading N n f D hf hfD w (hreg w hw)
  have hconst := Complex.eventually_eq_of_isLocalMax_norm
    (han.eventually_analyticAt.mono fun z hz => hz.differentiableAt) hloc'
  have hdiff : a - algebraMap ℂ EE (G 0) ≠ 0 :=
    fun h => hac ⟨G 0, (sub_eq_zero.mp h).symm⟩
  have hreg0 : a ∈ (placeFamily N n f D hf hfD w 0).toValuationSubring := by
    rw [(place_spec N n f D hf hfD w).2.1]
    exact hreg w hw
  have ho := (place_spec N n f D hf hfD w).2.2.1.meromorphicOrderAt_sub_const
    (ball_mem_nhds 0 (place_spec N n f D hf hfD w).1) hreg0 (G 0) hdiff
  have htop : meromorphicOrderAt (fun z => G z - G 0) 0 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [hconst.filter_mono nhdsWithin_le_nhds] with z hz
    exact sub_eq_zero.mpr hz
  change meromorphicOrderAt (fun z => G z - G 0) 0 = _ at ho
  rw [htop] at ho
  exact WithTop.top_ne_coe ho

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
