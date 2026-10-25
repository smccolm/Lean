import Dubon2026.SourceOriginalWeilCoverMeromorphicLocalAtlas
import Dubon2026.SourceOriginalWeilCoverPathIntegral

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Every actual path primitive agrees locally with the constructed logarithmic
cell primitive up to a constant. Reuse fixed-chart primitive uniqueness and
the proved inverse-chart identities, with regularity only along the path. -/
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



open RadialMeromorphicPeriods RadialDissectionPeriods

theorem cover_logPrimitive_along_path {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)) (θ : R → Ω[EE⁄ℂ]),
      (∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r))) →
      PolePos D S → ∀ {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ},
      RegPrimData D S (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ →
      ∀ {P P' : Place ℂ EE} (δ : Path P P'), (∀ t, δ t ∉ S) →
      ∀ (g : R → unitInterval → ℂ),
        (∀ r, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (θ r) δ (g r)) →
      let residue : Place ℂ EE → R → ℂ := fun v r =>
        v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
          (v.uniformizer * v.differentialCoeff (θ r))
      ∀ r (t₀ : unitInterval), ∃ c : ℂ, ∀ᶠ t in 𝓝 t₀,
        g r t = Φloc S residue Ψ (cellOf D (δ t₀)) (δ t₀) (δ t) r + c := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD S θ hθ hS V Ψ hP P P' δ hδ g hg
  dsimp only
  intro r t₀
  let residue : Place ℂ EE → R → ℂ := fun v r =>
    v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
      (v.uniformizer * v.differentialCoeff (θ r))
  let E₀ := cellOf D (δ t₀)
  change ∃ c : ℂ, ∀ᶠ t in 𝓝 t₀, g r t = Φloc S residue Ψ E₀ (δ t₀) (δ t) r + c
  have hsrc : δ t₀ ∈ (D.cell E₀).ζ.source ∧ (D.cell E₀).ζ (δ t₀) ∈ V E₀ := by
    obtain ⟨z, hz, hyz⟩ := mem_cellOf D (δ t₀)
    have ht := (D.cell E₀).hKt hz
    rw [← hyz]
    exact ⟨(D.cell E₀).ζ.map_target ht,
      by rw [(D.cell E₀).ζ.right_inv ht]; exact hP.hKV E₀ hz⟩
  obtain ⟨Φ₁, hΦ₁, hgΦ⟩ := hg r t₀
  rw [placeChart_self] at hΦ₁
  obtain ⟨W, hWo, hcW, hW⟩ := cover_exists_logPrimitive N n radicand baseDivisor hRadicand hOrders
    D hD S θ hθ hS hP r E₀ hsrc.2
    (fun hρ => ζ_ne_q S residue hS (hδ t₀) (mem_cellOf D _) (fun h => hρ (by rw [h]; rfl)))
  have hcoord := hD E₀ (δ t₀) hsrc.1
  have hΦ := cover_hasDerivAt_coordPrimitive N n radicand baseDivisor hRadicand hOrders
    (D.cell E₀).ζ hsrc.1 hcoord.1 hcoord.2 hWo hcW hW
      ((δ t₀).mem_of_ord_nonneg ((hθ r _).2 (hδ t₀)))
  have hdiff := cover_eventually_coordPrimitive_sub_eq N n radicand baseDivisor hRadicand hOrders hΦ₁ hΦ
  refine ⟨Φ₁ 0 - Φloc S residue Ψ E₀ (δ t₀) (δ t₀) r, ?_⟩
  have h1 := δ.continuous.continuousAt (x := t₀) |>.eventually hdiff
  have h2 : ∀ᶠ t in 𝓝 t₀, δ t ∈ (PC (δ t₀)).source :=
    δ.continuous.continuousAt.preimage_mem_nhds
      (placeChart_source_mem_nhds N n radicand baseDivisor hRadicand hOrders (δ t₀))
  filter_upwards [h1, h2, hgΦ] with t ht hts hgt
  rw [hgt]
  change Φ₁ (PC (δ t₀) (δ t)) = _
  have hback : PF (δ t₀) (PC (δ t₀) (δ t)) = δ t := (PC (δ t₀)).left_inv hts
  simp only [Function.comp_apply, hback,
    (place_spec N n radicand baseDivisor hRadicand hOrders (δ t₀)).2.1] at ht
  simp only [Φloc]
  linear_combination ht

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
