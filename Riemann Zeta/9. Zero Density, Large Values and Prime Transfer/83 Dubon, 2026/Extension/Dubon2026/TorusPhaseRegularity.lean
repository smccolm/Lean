import Dubon2026.VerticalLineCountRegularity
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Transfer of almost-everywhere phase regularity from real coordinates to Haar measure -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

/-- The actual quotient by integral prime phases is an open quotient map. -/
theorem isOpenQuotientMap_realPhase (N : ℕ) :
    IsOpenQuotientMap (fun x : PrimeCoordinate N → ℝ =>
      (fun p => (x p : UnitAddCircle))) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

/-- The unit cube pushes forward to the normalized product Haar probability. -/
theorem measurePreserving_realPhase_unitCube (N : ℕ) :
    MeasurePreserving (fun x : PrimeCoordinate N → ℝ =>
      (fun p => (x p : UnitAddCircle)))
      (volume.restrict (Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1))) (torusHaar N) := by
  have hcircle : MeasurePreserving (fun t : ℝ => (t : UnitAddCircle))
      (volume.restrict (Ioc (0 : ℝ) 1)) AddCircle.haarAddCircle := by
    have hv : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
      simpa only [ENNReal.ofReal_one, one_smul] using
        (AddCircle.volume_eq_smul_haarAddCircle (T := 1))
    simpa only [zero_add, hv] using AddCircle.measurePreserving_mk (1 : ℝ) 0
  have hp := measurePreserving_pi
    (fun _ : PrimeCoordinate N => volume.restrict (Ioc (0 : ℝ) 1))
    (fun _ : PrimeCoordinate N => AddCircle.haarAddCircle) (fun _ => hcircle)
  simpa only [← Measure.restrict_pi_pi, ← volume_pi, torusHaar] using hp

theorem ae_torus_continuousAt_of_realPhase {N : ℕ} (f : PrimeTorus N → ℕ)
    (hf : ∀ᵐ x ∂(volume : Measure (PrimeCoordinate N → ℝ)),
      ContinuousAt (fun y => f (fun p => (y p : UnitAddCircle))) x) :
    ∀ᵐ z ∂torusHaar N, ContinuousAt f z := by
  have hq := isOpenQuotientMap_realPhase N
  have hm := measurePreserving_realPhase_unitCube N
  rw [← hm.map_eq]
  apply (ae_map_iff hm.aemeasurable (measurableSet_of_continuousAt f)).mpr
  filter_upwards [ae_restrict_of_ae hf] with x hx
  change Tendsto f (𝓝 (fun p => (x p : UnitAddCircle)))
    (𝓝 (f (fun p => (x p : UnitAddCircle))))
  rw [← hq.map_nhds_eq x]
  simpa only [Tendsto, Filter.map_map, Function.comp_def] using hx

theorem ae_torus_vertical_count_continuous {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u σ : ℝ} (hl : l < σ) (hu : σ < u) (H : ℝ) :
    ∀ᵐ z ∂torusHaar N, ContinuousAt (twistVerticalLineZeroCount a N hN ha l u H σ) z := by
  apply ae_torus_continuousAt_of_realPhase
  filter_upwards [ae_real_phase_vertical_count_locally_constant hN ha hl hu H] with x hx
  exact continuousAt_const.congr (hx.mono fun _ h => h.symm)

end

end Dubon2026
