import Dubon2026.SourceOriginalWeilCoverExponentialChartDerivative
import Dubon2026.SourceOriginalWeilCoverLocalExponentialModel
import Dubon2026.SourceMeromorphicLogDerivativeComparison

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> integral-period principality. The native exponential argument is applied to the actual cover with constructed residue data, paths and local models. Integral loop periods remain an explicit upstream hypothesis; their correction and the full Abel converse are not asserted here. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Manifold ContDiff Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * A v)
include A hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders)


theorem cover_meromorphic_orders_of_exponential_transport (D : Divisor ℂ EE) (η : Ω[EE⁄ℂ])
    (hη : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (g : Place ℂ EE → ℂ) (hgn : ∀ P, D P = 0 → g P ≠ 0)
    (htrans : ∀ (P Q : Place ℂ EE) (σ : CoverPath P Q), D P = 0 → D Q = 0 →
      (∀ t, D (σ t) = 0) → g Q = g P * Complex.exp (pathIntegral N n radicand A hRadicand hOrders η σ)) :
    ∀ v : Place ℂ EE, MeromorphicAt (fun z => g (placeFamily N n radicand A hRadicand hOrders v z)) 0 ∧
      meromorphicOrderAt (fun z => g (placeFamily N n radicand A hRadicand hOrders v z)) 0 = (D v : WithTop ℤ) := by
  letI := placeTopology N n radicand A hRadicand hOrders
  letI := placeChartedSpace N n radicand A hRadicand hOrders
  letI := place_t2Space N n radicand A hRadicand hOrders
  intro v
  obtain ⟨r₁, hr₁, hrR, M, hM0, hMo, hM⟩ :=
    exists_cover_local_exponential_model N n radicand A hRadicand hOrders v η (hη v) (D v) (hres v)
  have havoid : ∀ᶠ z in 𝓝[≠] (0 : ℂ), D (placeFamily N n radicand A hRadicand hOrders v z) = 0 := by
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
  have hsubR : ball (0 : ℂ) r ⊆ ball 0 (placeRadius N n radicand A hRadicand hOrders v) :=
    hsub₁.trans (ball_subset_ball hrR.le)
  have hf : ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 →
      g (placeFamily N n radicand A hRadicand hOrders v z) ≠ 0 ∧ HasDerivAt (fun z => g (placeFamily N n radicand A hRadicand hOrders v z))
        (readDifferential N n radicand A hRadicand hOrders v η z * g (placeFamily N n radicand A hRadicand hOrders v z)) z := by
    intro z hz hn
    have hD := hball z (hsub₂ hz) hn
    exact ⟨hgn _ hD, hasDerivAt_cover_exponential_chart N n radicand A hRadicand hOrders D η hη hres g htrans v (hsubR hz) hD⟩
  obtain ⟨hm, ho⟩ := OriginalExpTopology.meromorphicAt_of_same_logarithmic_derivative hr
    (fun z => g (placeFamily N n radicand A hRadicand hOrders v z)) M (readDifferential N n radicand A hRadicand hOrders v η) hM0 hf
    (fun z hz hn => hM z (hsub₁ hz) hn)
  exact ⟨hm, ho.trans hMo⟩


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
