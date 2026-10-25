import Dubon2026.SourceOriginalWeilCoverCellResidueReciprocity
import Dubon2026.SourceRadialUnimodularPeriodPolygon

/-! DUB-17/18 -> cover Abel converse -> exact third-kind reciprocity.
Retain the same actual word, matrix, loops, jumps and bilinear identities,
and attach the actual Abel-divisor correction on the complementary edges.
This avoids an intermediate subtype reindexing before the final 2g indexing. -/
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

local notation "BI" => coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders

open MeasureTheory

open scoped Real

open RadialDissectionPeriods
variable {kDim : ℕ}

/-- The same actual polygon, periods and unimodular matrix with regular and residue bilinear identities. -/
def CoverThirdKindCyclePeriodPolygonConclusion :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → (Fin kDim → Ω[EE⁄ℂ]) →
      Finset D.ιE → Finset D.ιE → (D.ιE → Fin kDim → ℂ) →
      ((j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)) →
      Place ℂ EE → Finset (Place ℂ EE) → (Fin kDim → D.ιC → ℂ → ℂ) → Prop := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun D η T Ts J γ P₀ S Ψ =>
    let Cside : D.ιE → Bool → D.ιC :=
      fun e s => (Function.surjInv D.side_bij.surjective (e, s)).1
    let startV : D.ιE × Bool → D.ιV := fun q => if q.2 then (D.ends q.1).1 else (D.ends q.1).2
    let endV : D.ιE × Bool → D.ιV := fun q => if q.2 then (D.ends q.1).2 else (D.ends q.1).1
    let L := {q : D.ιE × Bool // q.1 ∉ Ts}
    let m := Fintype.card L
    ∃ (_ : NeZero m) (wd : ZMod m ≃ L),
      (∀ i : ZMod m, endV (wd i).1 = startV (wd (i + 1)).1 ∧
        ∃ cs : List D.ιC, cs.head? = some (Cside (wd i).1.1 (wd i).1.2) ∧
          cs.getLast? = some (Cside (wd (i + 1)).1.1 (wd (i + 1)).1.2) ∧
          cs.IsChain (fun A B => ∃ g ∈ Ts,
            ((Cside g true = A ∧ Cside g false = B) ∨
             (Cside g true = B ∧ Cside g false = A)) ∧
            (endV (wd i).1 = (D.ends g).1 ∨ endV (wd i).1 = (D.ends g).2))) ∧
      (∀ (e : D.ιE) (he : e ∉ Ts),
        let αe : ZMod m := wd.symm ⟨(e, true), he⟩
        let βe : ZMod m := wd.symm ⟨(e, false), he⟩
        let pe : D.ιE → ℤ := fun e' =>
          ∑ i ∈ Finset.univ.filter
              (fun i : ZMod m => i ≠ αe ∧ (i - αe).val < (βe - αe).val),
            (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
        ∀ w : D.ιV,
          (∑ f with (D.ends f).2 = w, pe f) = (∑ f with (D.ends f).1 = w, pe f)) ∧
      (∀ (j : D.ιE) (hj : j ∉ Ts),
        J j = -∑ i ∈ Finset.univ.filter
            (fun i : ZMod m => i ≠ wd.symm ⟨(j, true), hj⟩ ∧
              (i - wd.symm ⟨(j, true), hj⟩).val <
                (wd.symm ⟨(j, false), hj⟩ - wd.symm ⟨(j, true), hj⟩).val),
          (if (wd i).1.2 then (1 : ℂ) else -1) • (fun e i => coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D (η i) e) (wd i).1.1) ∧
      (∀ j ∉ Ts, J j = -∑ l ∈ (T ∪ Ts)ᶜ,
        (wordMatrix wd j l : ℂ) • (fun i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l))) ∧
      AddSubgroup.closure (Set.range J) ≤
        AddSubgroup.closure ((fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) ''
          ((T ∪ Ts)ᶜ : Finset D.ιE)) ∧
      (complementaryWordMatrix T Ts wd).transpose = -complementaryWordMatrix T Ts wd ∧
      IsUnit (complementaryWordMatrix T Ts wd).det ∧
      (∀ i i', (∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
        pathIntegral N n radicand baseDivisor hRadicand hOrders (η i') (γ j) * (wordMatrix wd j l : ℂ) *
          pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) = 0) ∧
      (∀ (θ : Ω[EE⁄ℂ]), (∀ v ∈ S, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ EE, v ∉ S → 0 ≤ v.ordDifferential θ) → ∀ i,
        (∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
          pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j) * (wordMatrix wd j l : ℂ) *
            pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) =
          -(2 * π * Complex.I * ∑ v ∈ S,
            v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff θ) *
              Ψ i (cellOf D v) ((D.cell (cellOf D v)).ζ v))) ∧
      ∀ (E : Divisor ℂ EE) (θ : Ω[EE⁄ℂ]), (∀ v : Place ℂ EE, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ EE, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
          (v.uniformizer * v.differentialCoeff θ) = (E v : ℂ)) → E.support ⊆ S →
        ∃ c : D.ιE → ℤ, ∀ i,
          (∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
            (wordMatrix wd j l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ j) *
              pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ l)) =
            2 * Real.pi * Complex.I * (abelJacobiDiv N n radicand baseDivisor hRadicand hOrders η P₀ E i +
              ∑ l ∈ (T ∪ Ts)ᶜ, (c l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l))

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
