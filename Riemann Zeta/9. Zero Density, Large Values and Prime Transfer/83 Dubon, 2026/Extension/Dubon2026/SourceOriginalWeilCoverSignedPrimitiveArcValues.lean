import Dubon2026.SourceOriginalWeilCoverPrimitiveArcIntegral
import Dubon2026.SourceOriginalWeilCoverEdgePathIntegral
import Dubon2026.SourceRadialPrimitiveEndpointReversal

/-! DUB-17/18 -> cover reciprocity -> actual cell coefficient calculus.
For regular cell primitives the positive endpoint difference follows from
FTC. The constant jump and actual paired endpoints give the negative sign
directly, without the general weighted meromorphic reversal argument. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
open scoped Topology Interval
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

theorem cover_signed_primitive_arc_values :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source → AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧
        deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (θ : Ω[EE⁄ℂ]) (V : D.ιC → Set ℂ) (Ψ : D.ιC → ℂ → ℂ),
      (∀ C, (D.cell C).R.K ⊆ V C) →
      (∀ C w, w ∈ V C → HasDerivAt (Ψ C) (CF (D.cell C).ζ θ w) w) →
      (∀ v : Place ℂ EE, 0 ≤ v.ordDifferential θ) →
      ∀ (J : D.ιE → ℂ),
      (∀ e, ∀ s ∈ (D.cell (D.arcOf (e, true)).1).R.arcIcc (D.arcOf (e, true)).2,
        Ψ (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.loop s) -
          Ψ (D.arcOf (e, false)).1 ((D.cell (D.arcOf (e, false)).1).ζ
            ((D.cell (D.arcOf (e, true)).1).bdry s)) = J e) →
      ∀ q : D.ιE × Bool,
        Ψ (D.arcOf q).1 ((D.cell (D.arcOf q).1).R.loop ((D.cell (D.arcOf q).1).R.φs (D.arcOf q).2.succ)) -
          Ψ (D.arcOf q).1 ((D.cell (D.arcOf q).1).R.loop ((D.cell (D.arcOf q).1).R.φs (D.arcOf q).2.castSucc)) =
        (if q.2 then (1 : ℂ) else -1) * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ q.1 := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD θ V Ψ hKV hΨ hθ J hJ
  have hp (e : D.ιE) :
      Ψ (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.loop
        ((D.cell (D.arcOf (e, true)).1).R.φs (D.arcOf (e, true)).2.succ)) -
      Ψ (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.loop
        ((D.cell (D.arcOf (e, true)).1).R.φs (D.arcOf (e, true)).2.castSucc)) =
      coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e := by
    exact (cover_primitive_arc_integral N n radicand baseDivisor hRadicand hOrders
      (D.cell (D.arcOf (e, true)).1) (hD _) (D.arcOf (e, true)).2 θ
      (hKV _) (hΨ _) (fun s _ => hθ _)).symm
  rintro ⟨e, b⟩
  cases b
  · simp only [Bool.false_eq_true, if_false, neg_one_mul]
    exact (D.primitive_endpoint_reversal Ψ e (J e) (hJ e)).trans (congrArg Neg.neg (hp e))
  · simpa only [if_true, one_mul] using hp e

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
