import Dubon2026.SourcePeriodRawCorrection
import Dubon2026.SourceOriginalWeilCoverLoopPeriodInjectivity
import Dubon2026.SourceOriginalWeilCoverPathIntegralLinearCombination

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse. The native integer-period correction and actual cover integral-period principality consume the geometric loop-generation and bilinear/third-kind reciprocity clauses explicitly. These raw geometric clauses remain open, so this is a conditional Abel converse. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential Matrix
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand baseDivisor hRadicand hOrders)

theorem exists_cover_generator_period_correction {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ EE))
    (P₀ : Place ℂ EE) (D : Divisor ℂ EE) (η : Ω[EE⁄ℂ])
    (hD : abelJacobiDiv N n radicand baseDivisor hRadicand hOrders (fun i => (b i : Ω[EE⁄ℂ])) P₀ D ∈
      pathPeriodLattice N n radicand baseDivisor hRadicand hOrders (fun i => (b i : Ω[EE⁄ℂ])))
    (Pz : Fin kDim ⊕ Fin kDim → Place ℂ EE) (Z : ∀ k, CoverPath (Pz k) (Pz k))
    (Q : Matrix (Fin kDim ⊕ Fin kDim) (Fin kDim ⊕ Fin kDim) ℤ) (hQ : IsUnit Q.det)
    (hgen : ∀ (P : Place ℂ EE) (γ : CoverPath P P), ∃ κ : Fin kDim ⊕ Fin kDim → ℤ,
      ∀ i, pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) γ =
        ∑ k, (κ k : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (Z k))
    (hRR : ∀ i j : Fin kDim, ∑ k, ∑ l, (Q k l : ℂ) *
      pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (Z k) * pathIntegral N n radicand baseDivisor hRadicand hOrders (b j : Ω[EE⁄ℂ]) (Z l) = 0)
    (hrec : ∃ κ : Fin kDim ⊕ Fin kDim → ℤ, ∀ i : Fin kDim,
      ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (Z k) *
        pathIntegral N n radicand baseDivisor hRadicand hOrders η (Z l) = 2 * Real.pi * Complex.I *
          (abelJacobiDiv N n radicand baseDivisor hRadicand hOrders (fun i => (b i : Ω[EE⁄ℂ])) P₀ D i +
            ∑ k, (κ k : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (Z k))) :
    ∃ ζ ∈ regularDifferentials ℂ EE, ∃ m : Fin kDim ⊕ Fin kDim → ℤ,
      ∀ k, pathIntegral N n radicand baseDivisor hRadicand hOrders η (Z k) - pathIntegral N n radicand baseDivisor hRadicand hOrders ζ (Z k) =
        2 * Real.pi * Complex.I * (m k : ℂ) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  classical
  let A : Matrix (Fin kDim ⊕ Fin kDim) (Fin kDim) ℂ := fun k i =>
    pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (Z k)
  have hAm : Function.Injective A.mulVecLin :=
    cover_loop_period_matrix_injective N n radicand baseDivisor hRadicand hOrders b Pz Z hgen
  have hcoord := exists_cover_period_coordinates N n radicand baseDivisor hRadicand hOrders
    (fun i => (b i : Ω[EE⁄ℂ])) Pz Z hgen hD
  obtain ⟨μ, hμ⟩ := hcoord
  obtain ⟨κ, hκ⟩ := hrec
  have hraw : ∀ i, ∑ k, ∑ l, (Q k l : ℂ) * A k i *
      pathIntegral N n radicand baseDivisor hRadicand hOrders η (Z l) =
      (2 * Real.pi * Complex.I) * ((∑ k, (μ k : ℂ) * A k i) + ∑ k, (κ k : ℂ) * A k i) := by
    intro i
    exact (hκ i).trans (congrArg
      (fun z : ℂ => (2 * Real.pi * Complex.I) * (z + ∑ k, (κ k : ℂ) * A k i))
      (congrFun hμ i))
  have hcor := PeriodCorrection.exists_integer_correction_of_raw_reciprocity A Q hAm hQ hRR
    (fun k => pathIntegral N n radicand baseDivisor hRadicand hOrders η (Z k))
    (2 * Real.pi * Complex.I) μ κ hraw
  obtain ⟨c, m, hm⟩ := hcor
  refine ⟨∑ i, c i • (b i : Ω[EE⁄ℂ]),
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (b i).2), m, ?_⟩
  intro k
  rw [pathIntegral_sum_smul N n radicand baseDivisor hRadicand hOrders c
    (fun i => (b i : Ω[EE⁄ℂ])) (fun i => (b i).2)]
  exact hm k

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
