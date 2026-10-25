import Dubon2026.SourceOriginalWeilCoverMeromorphicBasisExtensionV2
import Dubon2026.SourceOriginalWeilCoverThirdKindPolygonData
import Dubon2026.SourceOriginalWeilCoverRegularLoopGeneration

/-! DUB-17/18 -> cover Abel converse. These are the exact finite-index
geometric inputs consumed by the existing raw-reciprocity theorem.
The following reindexing and existence modules derive all clauses. -/
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

/-- Exact cover geometric inputs to the existing Abel converse on a fixed 2g cycle index. -/
def CoverRawReciprocityData {kDim : ℕ} (η : Fin kDim → Ω[EE⁄ℂ])
    (P₀ : Place ℂ EE) (S : Finset (Place ℂ EE)) : Prop :=
    ∃ (Pz : Fin kDim ⊕ Fin kDim → Place ℂ EE) (Z : ∀ k, CoverPath (Pz k) (Pz k))
      (Q : Matrix (Fin kDim ⊕ Fin kDim) (Fin kDim ⊕ Fin kDim) ℤ),
      (∀ k t, Z k t ∉ S) ∧ Q.transpose = -Q ∧ IsUnit Q.det ∧
      (∀ (P : Place ℂ EE) (δ : CoverPath P P), ∃ κ : Fin kDim ⊕ Fin kDim → ℤ, ∀ i,
        pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) δ = ∑ k, (κ k : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (Z k)) ∧
      (∀ (P : Place ℂ EE) (δ : CoverPath P P), (∀ t, δ t ∉ S) →
        ∃ (κ : Fin kDim ⊕ Fin kDim → ℤ) (w : Place ℂ EE → ℤ), ∀ θ : Ω[EE⁄ℂ],
          (∀ v : Place ℂ EE, -1 ≤ v.ordDifferential θ) →
          (∀ v : Place ℂ EE, v ∉ S → 0 ≤ v.ordDifferential θ) →
          pathIntegral N n radicand baseDivisor hRadicand hOrders θ δ = ∑ k, (κ k : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders θ (Z k) +
            2 * Real.pi * Complex.I * ∑ v ∈ S,
              (w v : ℂ) * v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff θ)) ∧
      (∀ i i', (∑ k, ∑ l, (Q k l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (Z k) *
        pathIntegral N n radicand baseDivisor hRadicand hOrders (η i') (Z l)) = 0) ∧
      (∀ (E : Divisor ℂ EE) (θ : Ω[EE⁄ℂ]), (∀ v : Place ℂ EE, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ EE,
          v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff θ) = (E v : ℂ)) →
        E.support ⊆ S → ∃ κ : Fin kDim ⊕ Fin kDim → ℤ, ∀ i,
          (∑ k, ∑ l, (Q k l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (Z k) *
            pathIntegral N n radicand baseDivisor hRadicand hOrders θ (Z l)) = 2 * Real.pi * Complex.I *
              (abelJacobiDiv N n radicand baseDivisor hRadicand hOrders η P₀ E i +
                ∑ k, (κ k : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (Z k)))


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
