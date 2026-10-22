import Dubon2026.SourceOriginalFiberContourComparison
import Dubon2026.SourceOriginalFiberContourDifferentiation
import Dubon2026.SourceOriginalFiberContourVanishing
import Dubon2026.SourceOriginalFiberLocalData
import Dubon2026.SourceOriginalChartFiberMultiplicity
import Dubon2026.SourceOriginalSimpleFiberSum
import Dubon2026.SourceOriginalFiberCoefficients
import Dubon2026.SourceOriginalFiberDisks
import Dubon2026.SourceOriginalFiberContours
import Dubon2026.SourceOriginalFiberIndexing
import Dubon2026.SourceComplexWeightedFiberContour
import Dubon2026.SourceComplexFiberContourDerivative
import Dubon2026.SourceComplexSimpleFiberContour
import Dubon2026.SourceComplexFiberConstancy

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel. The Abel-Jacobi sum of each fiber, with its actual original
divisor multiplicities, is locally constant modulo actual loop periods.
All chart, compactness, primitive, derivative and residue inputs are proved
for the original function field. The analytic contour retains every zero
multiplicity, including at the central ramified fiber.
Adapted from S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential ComplexFiberContour
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ
attribute [local instance] placeTopology

theorem eventually_original_abelJacobiDiv_fiber_sub_mem {n : ℕ}
    (b : Fin n → regularDifferentials ℂ F) (P₀ : Place ℂ F)
    (f : F) (Z : ℂ → Divisor ℂ F)
    (hZ : ∀ (t : ℂ) (v : Place ℂ F), Z t v = max (v.ord (f - algebraMap ℂ F t)) 0)
    (t₀ : ℂ) :
    ∀ᶠ t in 𝓝 t₀,
      abelJacobiDiv N (fun i => (b i : Ω[F⁄ℂ])) P₀ (Z t) -
        abelJacobiDiv N (fun i => (b i : Ω[F⁄ℂ])) P₀ (Z t₀) ∈
          pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ])) := by
  classical
  letI := place_t2Space N
  set bb : Fin n → Ω[F⁄ℂ] := fun i => (b i : Ω[F⁄ℂ]) with hbbdef
  set Λ := pathPeriodLattice N bb with hΛ

  by_cases hfc : ∃ a : ℂ, f = algebraMap ℂ F a
  · obtain ⟨a, rfl⟩ := hfc
    have hZ0 : ∀ t, Z t = 0 := fun t => by
      ext v
      rw [hZ t v, ← map_sub, Place.ord_algebraMap]
      simp
    exact Filter.Eventually.of_forall fun t => by simp [hZ0, Λ.zero_mem]
  push Not at hfc

  have hbb : ∀ i, bb i ∈ regularDifferentials ℂ F := fun i => (b i).2
  have hne : ∀ t : ℂ, f - algebraMap ℂ F t ≠ 0 := fun t h0 => hfc t (sub_eq_zero.mp h0)
  obtain ⟨h, hh, hhreg⟩ := original_regular_fiber_coefficients N b hfc

  set Z₀ : Finset (Place ℂ F) := (Z t₀).support with hZ₀def
  have hsupp : ∀ (t : ℂ) (w : Place ℂ F), w ∈ (Z t).support ↔ 0 < w.ord (f - algebraMap ℂ F t) := by
    intro t w
    rw [Finsupp.mem_support_iff, hZ t w]
    omega
  have hZ₀ : ∀ v, v ∈ Z₀ ↔ 0 < v.ord (f - algebraMap ℂ F t₀) := hsupp t₀
  obtain ⟨d⟩ := exists_originalFiberDisks N bb hbb P₀ f h hh hfc t₀ Z₀ hZ₀
  obtain ⟨c⟩ := exists_originalFiberContours N bb P₀ f h t₀ Z₀ hZ₀ hne d
  obtain ⟨j⟩ := exists_originalFiberIndexing N bb P₀ f h t₀ Z₀ Z hZ hne c
  let L := originalFiberContourSum N bb P₀ f h t₀ Z₀ Z j
  let L' := originalFiberContourDerivative N bb P₀ f h t₀ Z₀ Z j
  let ε := j.ε
  have hε : 0 < ε := j.hε
  have hAJL : ∀ t ∈ ball t₀ ε, abelJacobiDiv N bb P₀ (Z t) - L t ∈ Λ :=
    fun t ht => original_fiber_sub_contour_mem N bb P₀ f h t₀ Z₀ Z j ht
  have hLder : ∀ t ∈ ball t₀ ε, HasDerivAt L (L' t) t :=
    fun t ht => hasDerivAt_originalFiberContourSum N bb P₀ f h t₀ Z₀ Z j ht
  have hLder0 : ∀ t ∈ ball t₀ ε, t ≠ t₀ → L' t = 0 :=
    fun t ht htne => originalFiberContourDerivative_eq_zero N bb P₀ f h t₀ Z₀ Z j hhreg hZ ht htne

  have hLconst : ∀ t ∈ Metric.ball t₀ ε, L t = L t₀ :=
    eq_of_hasDerivAt_zero_off_center hLder hLder0
  filter_upwards [Metric.ball_mem_nhds t₀ hε] with t ht
  have h1 := hAJL t ht
  have h0 := hAJL t₀ (Metric.mem_ball_self hε)
  have hEq : abelJacobiDiv N bb P₀ (Z t) - abelJacobiDiv N bb P₀ (Z t₀) =
      (abelJacobiDiv N bb P₀ (Z t) - L t) - (abelJacobiDiv N bb P₀ (Z t₀) - L t₀) := by
    rw [hLconst t ht]; abel
  rw [hEq]
  exact Λ.sub_mem h1 h0

end
end Dubon2026.SourceFunctionField.OriginalChart
