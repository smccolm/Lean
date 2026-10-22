import Dubon2026.SourceOriginalBranchedCells

/-! DUB-17/18 -> original Abel-Jacobi -> actual exterior pole cells.
The proved normal-fiber charts for inverse j and exact power-pullback regions
construct all original cells above a sufficiently small radial neighborhood
of zero. This is consumed by reciprocal exterior-window geometry.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Metric
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_j_inverse_cells :
    ∃ ε > 0, ∀ R : RadialRegion, R.q = 0 → 2 ≤ R.N → R.K ⊆ ball 0 ε →
      ∃ C : originalPositiveFiber N (jOver N ℂ)⁻¹ 0 → Cell N,
        (∀ v : originalPositiveFiber N (jOver N ℂ)⁻¹ 0,
          (v : Place ℂ F) ∈ (C v).interior' ∧ (C v).ζ v = 0 ∧
          PowPullback.PowerGeometry R
            ((v : Place ℂ F).ord ((jOver N ℂ)⁻¹)).toNat (C v).R ∧
          ∀ P ∈ (C v).ζ.source, (jOver N ℂ)⁻¹ ∈ P.toValuationSubring ∧
            originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ = (C v).ζ P ^
              ((v : Place ℂ F).ord (jOver N ℂ)⁻¹).toNat) ∧
        (Pairwise fun v w => Disjoint (C v).carrier (C w).carrier) ∧
        ∀ P : Place ℂ F,
          ((jOver N ℂ)⁻¹ ∈ P.toValuationSubring ∧ originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ ∈ R.K) ↔
          ∃ v, P ∈ (C v).carrier := by
  classical
  have hi : ∀ c : ℂ, (jOver N ℂ)⁻¹ ≠ algebraMap ℂ F c := by
    intro c h
    have ha : IsAlgebraic ℂ ((jOver N ℂ)⁻¹) := h ▸ isAlgebraic_algebraMap c
    exact transcendental_jOver N ℂ (by simpa only [inv_inv] using ha.inv)
  obtain ⟨A, r, ε, hε, hA, hd, hr, hx⟩ := exists_original_normal_fiber_neighborhoods hi
  refine ⟨ε, hε, ?_⟩
  intro R hq hN hK
  let e := fun v : originalPositiveFiber N (jOver N ℂ)⁻¹ 0 =>
    ((v : Place ℂ F).ord ((jOver N ℂ)⁻¹)).toNat
  have he : ∀ v, e v ≠ 0 := fun v => Nat.ne_of_gt (hA v).2.2.2.2.2.1
  have hgeom : ∀ v, ∃ R', PowPullback.PowerGeometry R (e v) R' :=
    fun v => PowPullback.exists_pow_pullback_laps R hN (e v) (he v)
  choose S hS using hgeom
  have htarget : ∀ v, (S v).K ⊆ (A v).ζ.target := by
    intro v u hu
    have hbase := (hS v).2.2.1 u |>.mp hu
    have hn : ‖u‖ ^ e v < ε := by
      have hh := hK hbase
      rw [mem_ball, dist_eq_norm, hq, zero_add, sub_zero, norm_pow] at hh
      exact hh
    have hlt : ‖u‖ < r v := by
      by_contra hnot
      have hh := pow_le_pow_left₀ (hA v).1.le (le_of_not_gt hnot) (e v)
      exact (not_lt_of_ge hh) (hn.trans (hr v))
    rw [(hA v).2.2.2.1]
    simpa only [mem_ball, dist_zero_right] using hlt
  let C : originalPositiveFiber N (jOver N ℂ)⁻¹ 0 → Cell N := fun v =>
    { toAnalyticCoord := A v, R := S v, hKt := htarget v }
  have hc (v) (P : Place ℂ F) :
      P ∈ (C v).carrier ↔ P ∈ (A v).ζ.source ∧ (A v).ζ P ∈ (S v).K :=
    (C v).mem_carrier_iff_coordinate P
  refine ⟨C, ?_, ?_, ?_⟩
  · intro v
    have hzero : (0 : ℂ) ∈ (S v).Kint := by
      rw [(hS v).2.2.2.1 0, zero_pow (he v), add_zero]
      change ‖R.q - R.q‖ < R.r (Complex.arg (R.q - R.q))
      simpa only [sub_self, norm_zero] using R.hpos (Complex.arg (0 : ℂ))
    refine ⟨?_, (hA v).2.2.1, hS v, (hA v).2.2.2.2.2.2⟩
    refine ⟨0, hzero, ?_⟩
    have hv := (A v).ζ.left_inv (hA v).2.1
    rwa [(hA v).2.2.1] at hv
  · intro v w hvw
    exact (hd hvw).mono (fun P hP => ((hc v P).mp hP).1)
      (fun P hP => ((hc w P).mp hP).1)
  · intro P
    constructor
    · rintro ⟨hreg, hP⟩
      have hn : ‖originalPlaceEval N ℂ P (jOver N ℂ)⁻¹‖ < ε := by
        simpa only [mem_ball, dist_zero_right] using hK hP
      obtain ⟨v, hv⟩ := hx P hreg hn
      refine ⟨v, (hc v P).mpr ⟨hv, ?_⟩⟩
      rw [(hS v).2.2.1 ((A v).ζ P), hq, zero_add]
      rwa [← ((hA v).2.2.2.2.2.2 P hv).2]
    · rintro ⟨v, hv⟩
      obtain ⟨hsrc, hcoord⟩ := (hc v P).mp hv
      obtain ⟨hreg, hval⟩ := (hA v).2.2.2.2.2.2 P hsrc
      refine ⟨hreg, ?_⟩
      have hbase := ((hS v).2.2.1 ((A v).ζ P)).mp hcoord
      rw [hq, zero_add] at hbase
      exact hval.symm ▸ hbase

end
end Dubon2026.SourceFunctionField.CellGeometry
