import Dubon2026.SourceOriginalExponentialChartDerivative
import Dubon2026.SourceOriginalLocalExponentialModel
import Dubon2026.SourceMeromorphicLogDerivativeComparison

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse.
The actual global exponential transport function is meromorphic and has
exactly the prescribed integer chart orders. Finite-support avoidance gives
a punctured chart disk; native logarithmic-derivative comparison identifies
the function there with a nonzero multiple of the proved local model.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Manifold ContDiff Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_meromorphic_orders_of_exponential_transport (D : Divisor ℂ F) (η : Ω[F⁄ℂ])
    (hη : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (g : Place ℂ F → ℂ) (hgn : ∀ P, D P = 0 → g P ≠ 0)
    (htrans : ∀ (P Q : Place ℂ F) (σ : Path P Q), D P = 0 → D Q = 0 →
      (∀ t, D (σ t) = 0) → g Q = g P * Complex.exp (pathIntegral N η σ)) :
    ∀ v : Place ℂ F, MeromorphicAt (fun z => g (placeFamily N v z)) 0 ∧
      meromorphicOrderAt (fun z => g (placeFamily N v z)) 0 = (D v : WithTop ℤ) := by
  letI := placeChartedSpace N
  letI := place_t2Space N
  intro v
  obtain ⟨r₁, hr₁, hrR, M, hM0, hMo, hM⟩ :=
    exists_original_local_exponential_model N v η (hη v) (D v) (hres v)
  have havoid : ∀ᶠ z in 𝓝[≠] (0 : ℂ), D (placeFamily N v z) = 0 := by
    have h := OriginalExpTopology.eventually_pf_of_eventually_nhdsWithin v
      (OriginalExpTopology.eventually_nhdsWithin_compl_not_mem D.support.finite_toSet v)
    simpa only [MeromorphicCompact.ctr, MeromorphicCompact.φ,
      extPlaceChart_self, extPlaceChart_symm_apply, Finset.mem_coe,
      Finsupp.notMem_support_iff] using h
  rw [eventually_nhdsWithin_iff] at havoid
  obtain ⟨r₂, hr₂, hball⟩ := Metric.eventually_nhds_iff_ball.mp havoid
  let r := min r₁ r₂ / 2
  have hr : 0 < r := half_pos (lt_min hr₁ hr₂)
  have hsub₁ : ball (0 : ℂ) r ⊆ ball 0 r₁ :=
    ball_subset_ball ((half_le_self (le_of_lt (lt_min hr₁ hr₂))).trans (min_le_left _ _))
  have hsub₂ : ball (0 : ℂ) r ⊆ ball 0 r₂ :=
    ball_subset_ball ((half_le_self (le_of_lt (lt_min hr₁ hr₂))).trans (min_le_right _ _))
  have hsubR : ball (0 : ℂ) r ⊆ ball 0 (placeRadius N v) :=
    hsub₁.trans (ball_subset_ball hrR.le)
  have hf : ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 →
      g (placeFamily N v z) ≠ 0 ∧ HasDerivAt (fun z => g (placeFamily N v z))
        (readDifferential N v η z * g (placeFamily N v z)) z := by
    intro z hz hn
    have hD := hball z (hsub₂ hz) hn
    exact ⟨hgn _ hD, hasDerivAt_original_exponential_chart N D η hη hres g htrans v (hsubR hz) hD⟩
  obtain ⟨hm, ho⟩ := OriginalExpTopology.meromorphicAt_of_same_logarithmic_derivative hr
    (fun z => g (placeFamily N v z)) M (readDifferential N v η) hM0 hf
    (fun z hz hn => hM z (hsub₁ hz) hn)
  exact ⟨hm, ho.trans hMo⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
