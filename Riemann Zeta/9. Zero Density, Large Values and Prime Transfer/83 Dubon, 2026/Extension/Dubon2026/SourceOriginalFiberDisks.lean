import Dubon2026.SourceOriginalFiberLocalData

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel -> weighted fiber contour. This finite collection of actual
chart disks records only local geometric and analytic inputs. The producer
derives every field from the original local fiber theorem and Hausdorff
separation. The data contain no fiber sum, period-kernel or constancy claim.
Adapted from S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ
attribute [local instance] placeTopology

/-- Actual disjoint original chart disks with primitives and exact local orders. -/
structure OriginalFiberDisks {n : ℕ} (bb : Fin n → Ω[F⁄ℂ])
    (P₀ : Place ℂ F) (f : F) (h : Fin n → F) (t₀ : ℂ) (Z₀ : Finset (Place ℂ F)) where
  /-- Pairwise disjoint neighborhoods of the places in the central fiber. -/
  O : Place ℂ F → Set (Place ℂ F)
  /-- Positive coordinate radii on which the local fiber identities hold. -/
  ρ : Place ℂ F → ℝ
  /-- Local holomorphic primitives of the original regular differentials. -/
  Φ : Place ℂ F → Fin n → ℂ → ℂ
  hρ : ∀ v, 0 < ρ v
  hOdisj : (Z₀ : Set (Place ℂ F)).PairwiseDisjoint O
  htar : ∀ v ∈ Z₀, Metric.ball ((0 : ℂ)) (ρ v) ⊆
      (placeChart N v).target
  hOf : ∀ v ∈ Z₀, ∀ z ∈ Metric.ball ((0 : ℂ)) (ρ v),
      (placeChart N v).symm z ∈ O v ∧
        f ∈ ((placeChart N v).symm z).toValuationSubring
  hΦd : ∀ v ∈ Z₀, ∀ i, ∀ z ∈ Metric.ball ((0 : ℂ)) (ρ v),
      HasDerivAt (Φ v i) (readDifferential N v (bb i) z) z
  hAJloc : ∀ v ∈ Z₀, ∀ z ∈ Metric.ball ((0 : ℂ)) (ρ v),
      abelJacobiVec N bb P₀ ((placeChart N v).symm z) - abelJacobiVec N bb P₀ v -
        (fun i => Φ v i z - Φ v i ((0 : ℂ))) ∈ pathPeriodLattice N bb
  hRan : ∀ v ∈ Z₀, ∀ z ∈ Metric.ball ((0 : ℂ)) (ρ v),
      AnalyticAt ℂ (chartRead N v f) z
  hRc : ∀ v ∈ Z₀, chartRead N v f ((0 : ℂ)) = t₀
  hpunct : ∀ v ∈ Z₀, ∀ z ∈ Metric.ball ((0 : ℂ)) (ρ v),
      z ≠ (0 : ℂ) →
        chartRead N v f z ≠ t₀ ∧ deriv (chartRead N v f) z ≠ 0 ∧
          ∀ i, readDifferential N v (bb i) z = chartRead N v (h i) z * deriv (chartRead N v f) z

theorem exists_originalFiberDisks {n : ℕ} (bb : Fin n → Ω[F⁄ℂ])
    (hbb : ∀ i, bb i ∈ regularDifferentials ℂ F) (P₀ : Place ℂ F)
    (f : F) (h : Fin n → F) (hh : ∀ i, bb i = h i • D ℂ F f)
    (hfc : ∀ a : ℂ, f ≠ algebraMap ℂ F a) (t₀ : ℂ) (Z₀ : Finset (Place ℂ F))
    (hZ₀ : ∀ v, v ∈ Z₀ ↔ 0 < v.ord (f - algebraMap ℂ F t₀)) :
    Nonempty (OriginalFiberDisks N bb P₀ f h t₀ Z₀) := by
  classical
  letI := place_t2Space N
  obtain ⟨O, hO, hOdisj⟩ := (Z₀ : Set (Place ℂ F)).toFinite.t2_separation

  have hloc : ∀ v : Place ℂ F, ∃ ρ : ℝ, ∃ Φ : Fin n → ℂ → ℂ, 0 < ρ ∧ (v ∈ Z₀ →
      Metric.ball ((0 : ℂ)) ρ ⊆ (placeChart N v).target ∧
      (∀ z ∈ Metric.ball ((0 : ℂ)) ρ,
        (placeChart N v).symm z ∈ O v ∧
          f ∈ ((placeChart N v).symm z).toValuationSubring) ∧
      (∀ i, ∀ z ∈ Metric.ball ((0 : ℂ)) ρ,
        HasDerivAt (Φ i) (readDifferential N v (bb i) z) z) ∧
      (∀ z ∈ Metric.ball ((0 : ℂ)) ρ,
        abelJacobiVec N bb P₀ ((placeChart N v).symm z) - abelJacobiVec N bb P₀ v -
            (fun i => Φ i z - Φ i ((0 : ℂ))) ∈ pathPeriodLattice N bb) ∧
      (∀ z ∈ Metric.ball ((0 : ℂ)) ρ, AnalyticAt ℂ (chartRead N v f) z) ∧
      chartRead N v f ((0 : ℂ)) = t₀ ∧
      (∀ z ∈ Metric.ball ((0 : ℂ)) ρ, z ≠ (0 : ℂ) →
        chartRead N v f z ≠ t₀ ∧ deriv (chartRead N v f) z ≠ 0 ∧
          ∀ i, readDifferential N v (bb i) z =
            chartRead N v (h i) z * deriv (chartRead N v f) z)) := by
    intro v
    by_cases hv : v ∈ Z₀
    · obtain ⟨ρ, Φ, hρ, hrest⟩ := original_fiber_local_data N bb hbb P₀ h hh hfc t₀ v ((hZ₀ v).1 hv)
        (O v) (hO v).2 (hO v).1
      exact ⟨ρ, Φ, hρ, fun _ => hrest⟩
    · exact ⟨1, fun _ _ => 0, one_pos, fun h' => absurd h' hv⟩
  choose ρ Φ hρ hLD using hloc
  have htar : ∀ v ∈ Z₀, Metric.ball ((0 : ℂ)) (ρ v) ⊆
      (placeChart N v).target := fun v hv => (hLD v hv).1
  have hOf : ∀ v ∈ Z₀, ∀ z ∈ Metric.ball ((0 : ℂ)) (ρ v),
      (placeChart N v).symm z ∈ O v ∧
        f ∈ ((placeChart N v).symm z).toValuationSubring := fun v hv => (hLD v hv).2.1
  have hΦd : ∀ v ∈ Z₀, ∀ i, ∀ z ∈ Metric.ball ((0 : ℂ)) (ρ v),
      HasDerivAt (Φ v i) (readDifferential N v (bb i) z) z := fun v hv => (hLD v hv).2.2.1
  have hAJloc : ∀ v ∈ Z₀, ∀ z ∈ Metric.ball ((0 : ℂ)) (ρ v),
      abelJacobiVec N bb P₀ ((placeChart N v).symm z) - abelJacobiVec N bb P₀ v -
        (fun i => Φ v i z - Φ v i ((0 : ℂ))) ∈ pathPeriodLattice N bb :=
    fun v hv => (hLD v hv).2.2.2.1
  have hRan : ∀ v ∈ Z₀, ∀ z ∈ Metric.ball ((0 : ℂ)) (ρ v),
      AnalyticAt ℂ (chartRead N v f) z := fun v hv => (hLD v hv).2.2.2.2.1
  have hRc : ∀ v ∈ Z₀, chartRead N v f ((0 : ℂ)) = t₀ :=
    fun v hv => (hLD v hv).2.2.2.2.2.1
  have hpunct : ∀ v ∈ Z₀, ∀ z ∈ Metric.ball ((0 : ℂ)) (ρ v),
      z ≠ (0 : ℂ) →
        chartRead N v f z ≠ t₀ ∧ deriv (chartRead N v f) z ≠ 0 ∧
          ∀ i, readDifferential N v (bb i) z = chartRead N v (h i) z * deriv (chartRead N v f) z :=
    fun v hv => (hLD v hv).2.2.2.2.2.2

  exact ⟨⟨O, ρ, Φ, hρ, hOdisj, htar, hOf, hΦd, hAJloc, hRan, hRc, hpunct⟩⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
