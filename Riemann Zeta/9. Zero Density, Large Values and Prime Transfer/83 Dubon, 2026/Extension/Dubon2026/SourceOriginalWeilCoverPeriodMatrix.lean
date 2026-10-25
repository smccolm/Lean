import Dubon2026.SourceOriginalWeilCoverPrimitivePolygon
import Dubon2026.SourceRadialCyclePeriodMatrixAssembly

/-! DUB-17/18 -> actual cover Abel converse -> geometric cycle integrals.
The literal coordinate edge sums equal the actual constructed loop periods.
Combine this proved identification with the integer subword matrix and exact
primitive-jump formula to obtain actual jump-to-loop-period generation. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
universe u
noncomputable section
open SourceCurve Set CellGeometry CellGeometry.RadialEdgePaths KaehlerDifferential
open CellGeometry.IntegerEdgeChains CellGeometry.RadialDissectionTrees
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders

theorem cover_period_matrix_of_primitive_word {κ : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (η : κ → Ω[EE⁄ℂ]),
      (∀ i, η i ∈ regularDifferentials ℂ EE) →
      ∀ (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ) (J : D.ιE → κ → ℂ)
        (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)),
      (∀ f : D.ιE → ULift.{u} ℤ,
        (∀ w, (∑ e with (D.ends e).2 = w, f e) = ∑ e with (D.ends e).1 = w, f e) →
        ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j) →
      (∀ j (θ : Ω[EE⁄ℂ]), (∀ v ∈ D.skeleton, 0 ≤ v.ordDifferential θ) →
        (∃ g, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders θ (γ j) g) ∧
        pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j) =
          ∑ e, (Z j e : ℂ) * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e) →
      (AddSubgroup.closure (range J) ≤ AddSubgroup.closure (J '' ((T ∪ Ts)ᶜ : Finset D.ιE))) →
      RadialDissectionPeriods.PrimitivePolygonConclusion D
        (fun e i => coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D (η i) e) Ts J →
      RadialDissectionPeriods.CyclePeriodPolygonConclusion D
        (fun e i => coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D (η i) e) T Ts J
        (fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η hη T Ts Z J γ hdec hγi hgen hW
  apply RadialDissectionPeriods.period_matrix_of_primitive_word D
    (fun e i => coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D (η i) e)
    T Ts Z J (fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) hdec
    ?_ hgen hW
  intro l
  funext i
  have hi := (hγi l (η i) (fun v _ =>
    (mem_cover_regularDifferentials_iff_ord_nonneg N n radicand (η i)).mp (hη i) v)).2
  simpa only [RadialDissectionPeriods.zv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hi.symm

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
