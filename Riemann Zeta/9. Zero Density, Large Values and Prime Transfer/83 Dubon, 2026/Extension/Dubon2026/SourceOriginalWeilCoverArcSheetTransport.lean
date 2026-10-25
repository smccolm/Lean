import Dubon2026.SourceOriginalWeilCoverCellFiberEquiv
import Dubon2026.SourceOriginalWeilCoverLiftedArcEquality

/-! DUB-17/18 -> actual arc-pairing involution -> inverse sheet transport.
Two actual cell sheet sets are equivalent over a common boundary point.
This equivalence preserves the entire original reversed arc by covering
uniqueness, so its inverse can supply the reverse pairing without a new choice. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Topology
attribute [local instance] OriginalChart.placeTopology restrictionIntegral
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders

theorem exists_boundary_sheet_equiv (C C' : CellGeometry.Cell N) (J J' : Type*) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ : J → OpenPartialHomeomorph (Place ℂ EE) ℂ)
      (η : J' → OpenPartialHomeomorph (Place ℂ EE) ℂ),
      (∀ j, C.R.K ⊆ (ζ j).target) → (∀ j, C'.R.K ⊆ (η j).target) →
      (∀ j z, z ∈ (ζ j).target → ((ζ j).symm z).restrict FF = C.ζ.symm z) →
      (∀ j z, z ∈ (η j).target → ((η j).symm z).restrict FF = C'.ζ.symm z) →
      (Pairwise fun i j => Disjoint (ζ i).source (ζ j).source) →
      (Pairwise fun i j => Disjoint (η i).source (η j).source) →
      (∀ w, w.restrict FF ∈ C.carrier → ∃ j, w ∈ (ζ j).symm '' C.R.K) →
      (∀ w, w.restrict FF ∈ C'.carrier → ∃ j, w ∈ (η j).symm '' C'.R.K) →
      ∀ (a b t₀ : ℝ) (ψ : ℝ → ℝ), ContinuousOn ψ (Icc a b) →
        (∀ t ∈ Icc a b, C'.bdry t = C.bdry (ψ t)) → t₀ ∈ Icc a b →
        ∃ T : J ≃ J', ∀ j t, t ∈ Icc a b →
          (η (T j)).symm (C'.R.loop t) = (ζ j).symm (C.R.loop (ψ t)) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ η hK hK' hp hp' hd hd' hx hx' a b t₀ ψ hψ hbase ht₀
  have h1 := exists_cell_sheet_fiber_equiv N n radicand baseDivisor hRadicand hOrders
    C J ζ hK (fun j z hz => hp j z (hK j hz)) hd hx (C.R.loop (ψ t₀)) (C.R.loop_mem_K _)
  have h2 := exists_cell_sheet_fiber_equiv N n radicand baseDivisor hRadicand hOrders
    C' J' η hK' (fun j z hz => hp' j z (hK' j hz)) hd' hx' (C'.R.loop t₀) (C'.R.loop_mem_K _)
  obtain ⟨e, he⟩ := h1
  obtain ⟨e', he'⟩ := h2
  have hpt : C.ζ.symm (C.R.loop (ψ t₀)) = C'.ζ.symm (C'.R.loop t₀) := (hbase t₀ ht₀).symm
  let q : {w : Place ℂ EE // w.restrict FF = C.ζ.symm (C.R.loop (ψ t₀))} ≃
      {w : Place ℂ EE // w.restrict FF = C'.ζ.symm (C'.R.loop t₀)} :=
    Equiv.subtypeEquivRight (fun w => by rw [hpt])
  let T := e.trans (q.trans e'.symm)
  have hT (j : J) : (η (T j)).symm (C'.R.loop t₀) = (ζ j).symm (C.R.loop (ψ t₀)) := by
    have hval : e' (T j) = q (e j) := e'.apply_symm_apply (q (e j))
    exact (he' (T j)).symm.trans ((congrArg Subtype.val hval).trans (he j))
  refine ⟨T, fun j => ?_⟩
  exact lifted_boundary_arcs_eq_of_endpoint N n radicand baseDivisor hRadicand hOrders C C'
    (ζ j) (η (T j)) (hK j) (hK' (T j)) (hp j) (hp' (T j)) a b t₀ ψ hψ hbase ht₀ (hT j)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
