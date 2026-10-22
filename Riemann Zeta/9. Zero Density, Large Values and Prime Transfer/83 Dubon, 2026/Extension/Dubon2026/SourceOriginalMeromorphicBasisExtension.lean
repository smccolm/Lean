import Dubon2026.SourceOriginalMeromorphicLoopPeriods
import Dubon2026.SourceOriginalPathIntegralFiniteRegularity
import Dubon2026.SourceOriginalSimplePoleBasis

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
The common integer coefficients for the actual simple-pole basis extend to
all differentials in exactly that space. Original path-integral linearity
requires regularity only along the paths; the already linear actual residue
map supplies the source's literal uniformizer residue. Coefficients are chosen
before the differential and are shared by the entire simple-pole space.
Adapted from S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
noncomputable section
open SourceCurve Set Complex KaehlerDifferential OriginalChart
open scoped Real
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- Integer coefficients chosen once per pole-avoiding loop, for all allowed differentials. -/
def MeromorphicCycleGeneration (D : CellDissection N) (S : Finset (Place ℂ F))
    (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)) : Prop :=
  ∀ (P : Place ℂ F) (δ : Path P P), (∀ t, δ t ∉ S) →
    ∃ (a : D.ιE → ℤ) (w : Place ℂ F → ℤ), ∀ ϑ : Ω[F⁄ℂ],
      (∀ v : Place ℂ F, -1 ≤ v.ordDifferential ϑ) →
      (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential ϑ) →
      pathIntegral N ϑ δ =
        ∑ l ∈ (T ∪ Ts)ᶜ, (a l : ℂ) * pathIntegral N ϑ (γ l) +
        2 * Real.pi * Complex.I * ∑ v ∈ S, (w v : ℂ) * res v ϑ

theorem meromorphic_cycle_generation_of_basis {𝒟 : CellDissection N}
    (S : Finset (Place ℂ F)) (hS : PolePos 𝒟 S) {d : ℕ}
    (bT : Module.Basis (Fin d) ℂ (originalSimplePoleSpace N S))
    (T Ts : Finset 𝒟.ιE)
    (γ : (j : 𝒟.ιE) → Path (𝒟.vert (𝒟.ends j).1) (𝒟.vert (𝒟.ends j).1))
    (hγs : ∀ j t, γ j t ∈ 𝒟.skeleton)
    (hfamily : MeromorphicFamilyGeneration 𝒟 S (fun r => (bT r : Ω[F⁄ℂ])) T Ts γ) :
    MeromorphicCycleGeneration 𝒟 S T Ts γ := by
  classical
  intro Pt δ hδ
  set θ : Fin d → Ω[F⁄ℂ] := fun r => (bT r : Ω[F⁄ℂ]) with hθdef
  have hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)) :=
    fun r v => (bT r).2 v
  have hsk : ∀ r, OriginalEdgePaths.RegOnSkeleton 𝒟 (θ r) := fun r =>
    𝒟.regular_on_skeleton S (fun v hv => ⟨_, (hS.hd5 v hv).choose_spec.1⟩) (θ r)
      (fun v hv => (hθ r v).2 hv)
  obtain ⟨c, m, hcm⟩ := hfamily Pt δ hδ
  refine ⟨c, fun v => ∑ D, if v ∈ (𝒟.cell D).interior' then m D else 0, fun ϑ h1 h2 => ?_⟩
  have hϑ : ϑ ∈ originalSimplePoleSpace N S := fun v => ⟨h1 v, h2 v⟩
  set a := bT.repr ⟨ϑ, hϑ⟩ with ha
  have hexp : ϑ = ∑ r, a r • θ r := by
    have h := congrArg Subtype.val (bT.sum_repr ⟨ϑ, hϑ⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  have hδsum : pathIntegral N ϑ δ = ∑ r, a r * pathIntegral N (θ r) δ := by
    conv_lhs => rw [hexp]
    exact pathIntegral_sum_smul_of_coeff_mem N a θ δ
      (fun r t => (δ t).mem_of_ord_nonneg ((hθ r (δ t)).2 (hδ t)))
  have hγsum : ∀ l, pathIntegral N ϑ (γ l) = ∑ r, a r * pathIntegral N (θ r) (γ l) := by
    intro l
    conv_lhs => rw [hexp]
    exact pathIntegral_sum_smul_of_coeff_mem N a θ (γ l)
      (fun r t => (γ l t).mem_of_ord_nonneg (hsk r _ (hγs l t)))
  have hres : ∀ v, res v ϑ = ∑ r, a r * res v (θ r) := by
    intro v
    calc res v ϑ = originalDifferentialResidue N v ϑ :=
          (originalDifferentialResidue_simplePole N v ϑ (h1 v)).symm
      _ = ∑ r, a r * originalDifferentialResidue N v (θ r) := by
          rw [hexp, map_sum]
          simp only [map_smul, smul_eq_mul]
      _ = ∑ r, a r * res v (θ r) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [originalDifferentialResidue_simplePole N v (θ r) (hθ r v).1]
          rfl
  rw [hδsum]
  simp_rw [hcm]
  have h1 : ∑ r, a r * ∑ l ∈ (T ∪ Ts)ᶜ, (c l : ℂ) * pathIntegral N (θ r) (γ l) =
      ∑ l ∈ (T ∪ Ts)ᶜ, (c l : ℂ) * pathIntegral N ϑ (γ l) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hγsum l, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  have h2 : ∑ r, a r * ∑ D, (m D : ℂ) * (2 * π * I * ρ 𝒟 S θ D r) =
      2 * Real.pi * Complex.I * ∑ v ∈ S,
        ((∑ D, if v ∈ (𝒟.cell D).interior' then m D else 0 : ℤ) : ℂ) *
          res v ϑ := by

    have hρ : ∀ D, ∑ r, a r * ρ 𝒟 S θ D r =
        ∑ v ∈ S.filter (fun v => v ∈ (𝒟.cell D).interior'),
          res v ϑ := by
      intro D
      simp only [ρ, Finset.sum_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hres v]
    calc ∑ r, a r * ∑ D, (m D : ℂ) * (2 * π * I * ρ 𝒟 S θ D r)
        = 2 * π * I * ∑ D, (m D : ℂ) * ∑ r, a r * ρ 𝒟 S θ D r := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun D _ => Finset.sum_congr rfl fun r _ => by ring
      _ = 2 * π * I * ∑ D, (m D : ℂ) * ∑ v ∈ S.filter (fun v => v ∈ (𝒟.cell D).interior'),
            res v ϑ := by
          simp_rw [hρ]
      _ = 2 * Real.pi * Complex.I * ∑ v ∈ S,
            ((∑ D, if v ∈ (𝒟.cell D).interior' then m D else 0 : ℤ) : ℂ) *
              res v ϑ := by
          congr 1
          simp_rw [Finset.sum_filter, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => ?_
          push_cast
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun D _ => ?_
          split_ifs <;> simp
  rw [Finset.sum_congr rfl fun r _ => mul_add (a r) _ _, Finset.sum_add_distrib, h1, h2]

end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
