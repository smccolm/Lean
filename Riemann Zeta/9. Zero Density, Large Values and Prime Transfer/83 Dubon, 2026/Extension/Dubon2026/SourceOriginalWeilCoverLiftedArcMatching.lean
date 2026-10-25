import Dubon2026.SourceOriginalWeilCoverLiftedArcEquality

/-! DUB-17/18 -> actual lifted dissection -> unique matching boundary sheet.
A whole base arc has exactly one matching lifted sheet on the adjacent cell.
Existence uses the proved exhaustive cell lifts; uniqueness uses their disjoint
coordinate domains and the actual common endpoint. Arc reversal is retained. -/
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

theorem existsUnique_lifted_boundary_arc (C C' : CellGeometry.Cell N) (J : Type*) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ : OpenPartialHomeomorph (Place ℂ EE) ℂ)
      (η : J → OpenPartialHomeomorph (Place ℂ EE) ℂ),
      C.R.K ⊆ ζ.target → (∀ j, C'.R.K ⊆ (η j).target) →
      (∀ z ∈ ζ.target, (ζ.symm z).restrict FF = C.ζ.symm z) →
      (∀ j z, z ∈ (η j).target → ((η j).symm z).restrict FF = C'.ζ.symm z) →
      (∀ w, w.restrict FF ∈ C'.carrier → ∃ j, w ∈ (η j).symm '' C'.R.K) →
      (Pairwise fun i j => Disjoint (η i).source (η j).source) →
      ∀ (a b t₀ : ℝ) (ψ : ℝ → ℝ), ContinuousOn ψ (Icc a b) →
        (∀ t ∈ Icc a b, C'.bdry t = C.bdry (ψ t)) → t₀ ∈ Icc a b →
        ∃! j, ∀ t ∈ Icc a b, (η j).symm (C'.R.loop t) = ζ.symm (C.R.loop (ψ t)) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ η hK hK' hp hp' hx hd a b t₀ ψ hψ hbase ht₀
  let w := ζ.symm (C.R.loop (ψ t₀))
  have hpw : w.restrict FF = C'.ζ.symm (C'.R.loop t₀) :=
    (hp _ (hK (C.R.loop_mem_K (ψ t₀)))).trans (hbase t₀ ht₀).symm
  have hmem : w.restrict FF ∈ C'.carrier :=
    ⟨C'.R.loop t₀, C'.R.loop_mem_K t₀, hpw.symm⟩
  obtain ⟨j, z, hz, he⟩ := hx w hmem
  have hz0 : z = C'.R.loop t₀ := C'.ζ.symm.injOn (C'.hKt hz) (C'.hKt (C'.R.loop_mem_K t₀))
    ((hp' j z (hK' j hz)).symm.trans ((congrArg (fun P : Place ℂ EE => P.restrict FF) he).trans hpw))
  have hj0 : (η j).symm (C'.R.loop t₀) = w := by simpa only [hz0] using he
  have hj := lifted_boundary_arcs_eq_of_endpoint N n radicand baseDivisor hRadicand hOrders
    C C' ζ (η j) hK (hK' j) hp (hp' j) a b t₀ ψ hψ hbase ht₀ hj0
  refine ⟨j, hj, ?_⟩
  intro k hk
  by_contra hkj
  have hjm : w ∈ (η j).source := hj0 ▸ (η j).map_target (hK' j (C'.R.loop_mem_K t₀))
  have hk0 : (η k).symm (C'.R.loop t₀) = w := hk t₀ ht₀
  have hkm : w ∈ (η k).source := hk0 ▸ (η k).map_target (hK' k (C'.R.loop_mem_K t₀))
  exact Set.disjoint_left.mp (hd hkj) hkm hjm

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
