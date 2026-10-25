import Dubon2026.SourceOriginalWeilCoverMeromorphicLocalPrimitives
import Dubon2026.SourceRadialMeromorphicLocalAtlasData
import Dubon2026.SourceOriginalWeilCoverCoordinatePrimitiveComparison

/-! DUB-17/18 -> cover Abel converse -> arbitrary pole-avoiding paths.
The actual logarithmic cell primitives pull back to the same fixed-chart
differential reading. Existing primitive uniqueness makes their differences
locally constant at every point outside the marked poles. -/
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



open RadialMeromorphicPeriods
open MeromorphicPeriods (Lg)

theorem cover_eventually_logPrimitive_sub {R : Type*} [Finite R] :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)) (θ : R → Ω[EE⁄ℂ]),
      (∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r))) →
      PolePos D S → ∀ {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ},
      RegPrimData D S (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ →
      ∀ {y : Place ℂ EE}, y ∉ S → ∀ {C C' : D.ιC},
        y ∈ (D.cell C).carrier → y ∈ (D.cell C').carrier →
      let residue : Place ℂ EE → R → ℂ := fun v r =>
        v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
          (v.uniformizer * v.differentialCoeff (θ r))
      ∀ᶠ z in 𝓝 y, Φloc S residue Ψ C y z - Φloc S residue Ψ C' y z =
        Φloc S residue Ψ C y y - Φloc S residue Ψ C' y y := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD S θ hθ hS V Ψ hP y hyS C C' hC hC'
  let residue : Place ℂ EE → R → ℂ := fun v r =>
    v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
      (v.uniformizer * v.differentialCoeff (θ r))
  change ∀ᶠ z in 𝓝 y, Φloc S residue Ψ C y z - Φloc S residue Ψ C' y z =
    Φloc S residue Ψ C y y - Φloc S residue Ψ C' y y
  have hsrc : ∀ {E : D.ιC}, y ∈ (D.cell E).carrier →
      y ∈ (D.cell E).ζ.source ∧ (D.cell E).ζ y ∈ V E := by
    rintro E ⟨z, hz, rfl⟩
    have ht := (D.cell E).hKt hz
    exact ⟨(D.cell E).ζ.map_target ht, by rw [(D.cell E).ζ.right_inv ht]; exact hP.hKV E hz⟩
  have hreg : ∀ r, 0 ≤ y.ordDifferential (θ r) := fun r => (hθ r y).2 hyS
  have key : ∀ r, ∀ᶠ z in 𝓝 y, Φloc S residue Ψ C y z r - Φloc S residue Ψ C' y z r =
      Φloc S residue Ψ C y y r - Φloc S residue Ψ C' y y r := by
    intro r
    have hloc : ∀ {E : D.ιC}, y ∈ (D.cell E).carrier →
        ∀ᶠ z in 𝓝 (0 : ℂ),
          HasDerivAt ((fun w => Ψ r E w + ρ D S residue E r * Lg (D.cell E).R.q ((D.cell E).ζ y) w) ∘
            (D.cell E).ζ ∘ PF y) (RD y (θ r) z) z := by
      intro E hE
      obtain ⟨W, hWo, hcW, hW⟩ := cover_exists_logPrimitive N n radicand baseDivisor hRadicand hOrders
        D hD S θ hθ hS hP r E (hsrc hE).2
        (fun hρ => ζ_ne_q S residue hS hyS hE (fun h => hρ (by rw [h]; rfl)))
      exact cover_hasDerivAt_coordPrimitive N n radicand baseDivisor hRadicand hOrders
        (D.cell E).ζ (hsrc hE).1 (hD E y (hsrc hE).1).1 (hD E y (hsrc hE).1).2
        hWo hcW hW (y.mem_of_ord_nonneg (hreg r))
    have h3 := cover_eventually_coordPrimitive_sub_eq N n radicand baseDivisor hRadicand hOrders
      (hloc hC) (hloc hC')
    have hin := placeChart_source_mem_nhds N n radicand baseDivisor hRadicand hOrders y
    filter_upwards [h3, hin] with z hz hzs
    have hback : PF y (PC y z) = z := (PC y).left_inv hzs
    simp only [Function.comp_apply, hback,
      (place_spec N n radicand baseDivisor hRadicand hOrders y).2.1] at hz
    exact hz
  filter_upwards [Filter.eventually_all.2 key] with z hz
  funext r
  exact hz r

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
