import Dubon2026.SourceOriginalCellPairingLiftIndices
import Dubon2026.SourceOriginalWeilCoverArcSheetTransport

/-! DUB-17/18 -> actual paired lifted dissection.
The original positive-edge reversal supplies its exact C1 reparameterization.
Actual boundary-fiber equivalences lift it to a sheet equivalence. These
simultaneous transports define an involutive, orientation-reversing pairing
on the lifted arc indices, with the full actual boundary reversal identity. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Topology CellGeometry
attribute [local instance] OriginalChart.placeTopology restrictionIntegral
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders

theorem exists_lifted_pairing_transports {ι : Type} (cell : ι → Cell N)
    (P : CellPairing cell) (J : ι → Type) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ : (c : ι) → J c → OpenPartialHomeomorph (Place ℂ EE) ℂ),
      (∀ c j, (cell c).R.K ⊆ (ζ c j).target) →
      (∀ c j z, z ∈ (ζ c j).target → ((ζ c j).symm z).restrict FF = (cell c).ζ.symm z) →
      (∀ c, Pairwise fun i j => Disjoint (ζ c i).source (ζ c j).source) →
      (∀ c w, w.restrict FF ∈ (cell c).carrier → ∃ j, w ∈ (ζ c j).symm '' (cell c).R.K) →
      ∃ T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1,
        Function.Involutive (P.liftedPair J T) ∧
        (∀ a, (P.liftedPair J T a).1 = P.pair a.1) ∧
        (∀ a, P.orient (P.liftedPair J T a).1 = !P.orient a.1) ∧
        (∀ e j, P.liftedPair J T ⟨e.1, j⟩ = ⟨P.pair e.1, T e j⟩) ∧
        ∀ e : P.Edge, ∃ ψ : ℝ → ℝ,
          StrictAntiOn ψ ((cell (P.pair e.1).1).R.arcIcc (P.pair e.1).2) ∧
          ContDiffOn ℝ 1 ψ ((cell (P.pair e.1).1).R.arcIcc (P.pair e.1).2) ∧
          ψ ((cell (P.pair e.1).1).R.φs (P.pair e.1).2.castSucc) = (cell e.1.1).R.φs e.1.2.succ ∧
          ψ ((cell (P.pair e.1).1).R.φs (P.pair e.1).2.succ) = (cell e.1.1).R.φs e.1.2.castSucc ∧
          ∀ j t, t ∈ (cell (P.pair e.1).1).R.arcIcc (P.pair e.1).2 →
            (ζ (P.pair e.1).1 (T e j)).symm ((cell (P.pair e.1).1).R.loop t) =
              (ζ e.1.1 j).symm ((cell e.1.1).R.loop (ψ t)) := by
  classical
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ hK hp hd hx
  choose ψ ha hc hs he hbase using (fun e : P.Edge => P.reverse e.1 (P.pair e.1) rfl e.2)
  have hex (e : P.Edge) : ∃ T : J e.1.1 ≃ J (P.pair e.1).1,
      ∀ j t, t ∈ (cell (P.pair e.1).1).R.arcIcc (P.pair e.1).2 →
        (ζ (P.pair e.1).1 (T j)).symm ((cell (P.pair e.1).1).R.loop t) =
          (ζ e.1.1 j).symm ((cell e.1.1).R.loop (ψ e t)) := by
    let b := P.pair e.1
    let R := (cell b.1).R
    have ht : R.φs b.2.castSucc ∈ R.arcIcc b.2 :=
      ⟨le_rfl, (R.hmono (Fin.castSucc_lt_succ (i := b.2))).le⟩
    exact exists_boundary_sheet_equiv N n radicand baseDivisor hRadicand hOrders
      (cell e.1.1) (cell b.1) (J e.1.1) (J b.1) (ζ e.1.1) (ζ b.1)
      (hK e.1.1) (hK b.1) (hp e.1.1) (hp b.1) (hd e.1.1) (hd b.1) (hx e.1.1) (hx b.1)
      (R.φs b.2.castSucc) (R.φs b.2.succ) (R.φs b.2.castSucc) (ψ e)
      (hc e).continuousOn (hbase e) ht
  choose T hT using hex
  exact ⟨T, P.liftedPair_involutive J T, P.liftedPair_base J T,
    P.liftedPair_orientation J T, fun e j => P.liftedPair_positive J T e.1 e.2 j,
    fun e => ⟨ψ e, ha e, hc e, hs e, he e, hT e⟩⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
