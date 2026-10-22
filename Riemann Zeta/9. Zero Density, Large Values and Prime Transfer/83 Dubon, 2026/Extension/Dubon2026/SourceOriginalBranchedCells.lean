import Dubon2026.SourceOriginalJBranchNeighborhoods
import Dubon2026.SourceCellPowerSeparatedArcs
import Dubon2026.SourceOriginalOrdinarySquareCells

/-! DUB-17/18 -> original Abel-Jacobi -> actual ramified dissection cells.
The proved original j normal coordinates and exact power-pullback geometry
construct all branch-fiber cells for sufficiently small radial base regions.
Their carriers cover precisely the full original j preimage. No normal chart,
ramification exponent, power geometry or fiber exhaustion is assumed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Metric
open scoped Real
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- Exact power-pullback geometry, including the bijective arc laps and separated branches. -/
def PowPullback.PowerGeometry (R : RadialRegion) (e : ℕ) (R' : RadialRegion) : Prop :=
      R'.q = 0 ∧ R'.N = e * R.N ∧
      (∀ u : ℂ, u ∈ R'.K ↔ R.q + u ^ e ∈ R.K) ∧
      (∀ u : ℂ, u ∈ R'.Kint ↔ R.q + u ^ e ∈ R.Kint) ∧
      (∀ ψ : ℝ, R.q + R'.loop ψ ^ e = R.loop ((e : ℝ) * ψ)) ∧
      ∃ lap : Fin e → Fin R.N → Fin R'.N,
        Function.Bijective (fun jk : Fin e × Fin R.N => lap jk.1 jk.2) ∧
        (∀ (j : Fin e) (k : Fin R.N),
          R'.arcIcc (lap j k) = (fun t : ℝ => (2 * π * ((j : ℕ) : ℝ) + t) / (e : ℝ)) '' R.arcIcc k) ∧
        (∀ (j : Fin e) (k : Fin R.N),
          (fun u : ℂ => R.q + u ^ e) '' R'.arcSet (lap j k) = R.arcSet k) ∧
        (∀ (j : Fin e) (k : Fin R.N), Set.InjOn (fun u : ℂ => R.q + u ^ e) (R'.arcSet (lap j k))) ∧
        (∀ k : Fin R.N, ∃ U : Fin e → Set ℂ, (∀ j, IsOpen (U j)) ∧
          Pairwise (fun j j' => Disjoint (U j) (U j')) ∧ ∀ j, R'.arcSet (lap j k) ⊆ U j)

theorem exists_original_j_branch_cells (b : ℂ) :
    ∃ ε > 0, ∀ R : RadialRegion, R.q = b → 2 ≤ R.N → R.K ⊆ ball b ε →
      ∃ C : originalPositiveFiber N (jOver N ℂ) b → Cell N,
        (∀ v : originalPositiveFiber N (jOver N ℂ) b,
          (v : Place ℂ F) ∈ (C v).interior' ∧ (C v).ζ v = 0 ∧
          PowPullback.PowerGeometry R
            ((v : Place ℂ F).ord (jOver N ℂ - algebraMap ℂ F b)).toNat (C v).R ∧
          ∀ P ∈ (C v).ζ.source, jOver N ℂ ∈ P.toValuationSubring ∧
            originalPlaceEval N ℂ P (jOver N ℂ) = b + (C v).ζ P ^
              ((v : Place ℂ F).ord (jOver N ℂ - algebraMap ℂ F b)).toNat) ∧
        (Pairwise fun v w => Disjoint (C v).carrier (C w).carrier) ∧
        ∀ P : Place ℂ F,
          (jOver N ℂ ∈ P.toValuationSubring ∧ originalPlaceEval N ℂ P (jOver N ℂ) ∈ R.K) ↔
          ∃ v, P ∈ (C v).carrier := by
  classical
  obtain ⟨A, r, ε, hε, hA, hd, hr, hx⟩ := exists_original_j_branch_neighborhoods N b
  refine ⟨ε, hε, ?_⟩
  intro R hq hN hK
  let e := fun v : originalPositiveFiber N (jOver N ℂ) b =>
    ((v : Place ℂ F).ord (jOver N ℂ - algebraMap ℂ F b)).toNat
  have he : ∀ v, e v ≠ 0 := fun v => Nat.ne_of_gt (hA v).2.2.2.2.2.1
  have hgeom : ∀ v, ∃ R', PowPullback.PowerGeometry R (e v) R' :=
    fun v => PowPullback.exists_pow_pullback_laps R hN (e v) (he v)
  choose S hS using hgeom
  have htarget : ∀ v, (S v).K ⊆ (A v).ζ.target := by
    intro v u hu
    have hbase := (hS v).2.2.1 u |>.mp hu
    have hn : ‖u‖ ^ e v < ε := by
      have hh := hK hbase
      rw [mem_ball, dist_eq_norm, hq, add_sub_cancel_left, norm_pow] at hh
      exact hh
    have hlt : ‖u‖ < r v := by
      by_contra hnot
      have hh := pow_le_pow_left₀ (hA v).1.le (le_of_not_gt hnot) (e v)
      exact (not_lt_of_ge hh) (hn.trans (hr v))
    rw [(hA v).2.2.2.1]
    simpa only [mem_ball, dist_zero_right] using hlt
  let C : originalPositiveFiber N (jOver N ℂ) b → Cell N := fun v =>
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
      have hn : ‖originalPlaceEval N ℂ P (jOver N ℂ) - b‖ < ε := by
        simpa only [mem_ball, dist_eq_norm] using hK hP
      obtain ⟨v, hv⟩ := hx P hreg hn
      refine ⟨v, (hc v P).mpr ⟨hv, ?_⟩⟩
      rw [(hS v).2.2.1 ((A v).ζ P), hq]
      rwa [← ((hA v).2.2.2.2.2.2 P hv).2]
    · rintro ⟨v, hv⟩
      obtain ⟨hsrc, hcoord⟩ := (hc v P).mp hv
      obtain ⟨hreg, hval⟩ := (hA v).2.2.2.2.2.2 P hsrc
      refine ⟨hreg, ?_⟩
      have hbase := ((hS v).2.2.1 ((A v).ζ P)).mp hcoord
      rw [hq] at hbase
      exact hval.symm ▸ hbase

end
end Dubon2026.SourceFunctionField.CellGeometry
