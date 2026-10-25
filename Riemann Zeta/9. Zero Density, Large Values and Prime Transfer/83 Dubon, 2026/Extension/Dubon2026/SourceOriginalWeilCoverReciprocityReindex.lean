import Dubon2026.SourceFiniteThirdKindReindex
import Dubon2026.SourceOriginalWeilCoverGenerationReindex

/-! DUB-17/18 -> cover Abel converse -> final prescribed 2g indexing.
Reuse the existing finite reindexing proof directly on the constructed word
matrix. Actual loops, common integer coefficients, determinant and both
reciprocity identities are transported together, with no intermediate basis. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand baseDivisor hRadicand hOrders)


open CellGeometry RadialDissectionPeriods

theorem reindex_cover_reciprocity {kDim : ℕ} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (η : Fin kDim → Ω[EE⁄ℂ])
      (P₀ : Place ℂ EE) (S : Finset (Place ℂ EE)) (T Ts : Finset D.ιE)
      (Ψ : Fin kDim → D.ιC → ℂ → ℂ) (J : D.ιE → Fin kDim → ℂ)
      (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)),
      (T ∪ Ts)ᶜ.card = 2 * kDim → (∀ j t, γ j t ∉ S) →
      CoverRegularCycleGeneration N n radicand baseDivisor hRadicand hOrders D η T Ts γ →
      CoverMeromorphicCycleGeneration N n radicand baseDivisor hRadicand hOrders D S T Ts γ →
      CoverThirdKindCyclePeriodPolygonConclusion N n radicand baseDivisor hRadicand hOrders
        D η T Ts J γ P₀ S Ψ →
      CoverRawReciprocityData N n radicand baseDivisor hRadicand hOrders η P₀ S := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  classical
  intro D η P₀ S T Ts Ψ J γ hcount hγavoid hR hG hB
  obtain ⟨hm, wd, hw₁, hw₃, hwjump, hrow, hcl, hskew, hu, hri, hweighted, hrec⟩ := hB
  letI := hm
  let Q := complementaryWordMatrix T Ts wd
  have hcard : Fintype.card (Fin kDim ⊕ Fin kDim) = Fintype.card {l // l ∈ (T ∪ Ts)ᶜ} := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hcount]
    ring
  let e : Fin kDim ⊕ Fin kDim ≃ {l // l ∈ (T ∪ Ts)ᶜ} := Fintype.equivOfCardEq hcard
  have hre : ∀ f : D.ιE → ℂ,
      (∑ k, f (e k).1) = ∑ l ∈ (T ∪ Ts)ᶜ, f l := by
    intro f
    rw [Equiv.sum_comp e (fun l => f l.1)]
    exact Finset.sum_coe_sort _ f
  have hdouble : ∀ f : D.ιE → D.ιE → ℂ,
      (∑ k, ∑ l, f (e k).1 (e l).1) = ∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ, f j l := by
    intro f
    rw [hre (fun j => ∑ l, f j (e l).1)]
    exact Finset.sum_congr rfl fun j _ => hre (f j)
  refine ⟨fun k => D.vert (D.ends (e k).1).1,
    fun k => γ (e k).1, Q.submatrix e e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun k t => hγavoid (e k).1 t
  · funext k l
    exact congrFun (congrFun hskew (e k)) (e l)
  · rw [Matrix.det_submatrix_equiv_self]
    exact hu
  · exact cover_regular_generation_reindex N n radicand baseDivisor hRadicand hOrders D η T Ts γ e hR
  · exact cover_meromorphic_generation_reindex N n radicand baseDivisor hRadicand hOrders D S T Ts γ e hG
  · intro i i'
    change (∑ k, ∑ l, (wordMatrix wd (e k).1 (e l).1 : ℂ) *
      pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ (e k).1) *
      pathIntegral N n radicand baseDivisor hRadicand hOrders (η i') (γ (e l).1)) = 0
    rw [hdouble (fun j l => (wordMatrix wd j l : ℂ) *
      pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ j) *
      pathIntegral N n radicand baseDivisor hRadicand hOrders (η i') (γ l))]
    calc _ = ∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
          pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ j) * (wordMatrix wd j l : ℂ) *
            pathIntegral N n radicand baseDivisor hRadicand hOrders (η i') (γ l) := by
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
      _ = 0 := hri i' i
  · exact reindex_third_kind_reciprocity (X := Divisor ℂ EE) (R := Ω[EE⁄ℂ])
      (T ∪ Ts)ᶜ e (wordMatrix wd)
      (fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l))
      (fun l θ => pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ l))
      (fun E i => abelJacobiDiv N n radicand baseDivisor hRadicand hOrders η P₀ E i)
      (2 * Real.pi * Complex.I)
      (fun θ => ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential θ)
      (fun E θ => ∀ v : Place ℂ EE,
        v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
          (v.uniformizer * v.differentialCoeff θ) = (E v : ℂ))
      (fun E => E.support ⊆ S) hrec

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
