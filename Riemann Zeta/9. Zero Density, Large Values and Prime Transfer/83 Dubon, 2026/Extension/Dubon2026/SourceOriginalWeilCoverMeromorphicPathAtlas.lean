import Dubon2026.SourceOriginalWeilCoverMeromorphicPathComparison
import Dubon2026.SourceOriginalWeilCoverMeromorphicBoundaryValues
import Dubon2026.SourceRadialMeromorphicAtlasOverlap
import Dubon2026.SourceRadialMeromorphicAtlasLocality
import Dubon2026.SourcePathAtlasJumpClosure

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
The unchanged connected-path atlas theorem combines the proved actual local
logarithmic comparisons and residue/jump overlap identities. This proves the
endpoint formula modulo jumps and residues for every pole-avoiding path. -/
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

theorem cover_meromorphic_path_sub_mem {R : Type*} [Finite R] :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)) (θ : R → Ω[EE⁄ℂ]),
      (∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r))) →
      PolePos D S → ∀ {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ},
      RegPrimData D S (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ →
      ∀ {J : D.ιE → R → ℂ}, IsJumpH D
        (coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S θ Ψ) J →
      ∀ {P P' : Place ℂ EE} (δ : Path P P'), (∀ t, δ t ∉ S) →
      ∀ (g : R → unitInterval → ℂ),
        (∀ r, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (θ r) δ (g r)) →
      let residue : Place ℂ EE → R → ℂ := fun v r =>
        v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
          (v.uniformizer * v.differentialCoeff (θ r))
      (fun r => g r 1 - g r 0) -
        (pval S residue Ψ (cellOf D P') P' - pval S residue Ψ (cellOf D P) P) ∈ ΛJ D S residue J := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  letI := place_t2Space N n radicand baseDivisor hRadicand hOrders
  intro D hD S θ hθ hS V Ψ hP J hJ P P' δ hδ g hg
  let residue : Place ℂ EE → R → ℂ := fun v r =>
    v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
      (v.uniformizer * v.differentialCoeff (θ r))
  change (fun r => g r 1 - g r 0) -
    (pval S residue Ψ (cellOf D P') P' - pval S residue Ψ (cellOf D P) P) ∈ ΛJ D S residue J
  have hP0 : P ∉ S := by rw [← δ.source]; exact hδ 0
  have hP1 : P' ∉ S := by rw [← δ.target]; exact hδ 1
  have key := CellGeometry.DissectionPeriods.sub_sub_mem_of_atlas
    (ΛJ D S residue J) (Uset D S) (Gθ S residue Ψ)
    ?_ δ.continuous (fun t r => g r t) ?_ (j₀ := P) (j₁ := P')
    (by rw [δ.source]; exact mem_Uset_self D S hP0)
    (by rw [δ.target]; exact mem_Uset_self D S hP1)
  · rw [δ.source, δ.target, Gθ_self, Gθ_self] at key
    exact key
  · rintro x x' y ⟨hy, hy'⟩
    exact Gθ_sub_mem S residue hS hJ hy hy'
  · intro t₀
    refine ⟨δ t₀, isOpen_Uset D S (δ t₀), mem_Uset_self D S (hδ t₀), ?_⟩
    have hG := eventually_Gθ_eq_Φloc S residue Ψ δ δ.continuous (hδ t₀)
      (fun E hE => cover_eventually_logPrimitive_sub N n radicand baseDivisor hRadicand hOrders
        D hD S θ hθ hS hP (hδ t₀) hE (mem_cellOf D (δ t₀)))
    have hcomp := fun r => cover_logPrimitive_along_path N n radicand baseDivisor hRadicand hOrders
      D hD S θ hθ hS hP δ hδ g hg r t₀
    choose c hc using hcomp
    refine ⟨c, ?_⟩
    filter_upwards [hG, Filter.eventually_all.2 hc] with t htG htc
    rw [htG]
    funext r
    exact htc r

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
