import Dubon2026.CompactDiscreteFiniteQuotient
import Dubon2026.ContinuousRepresentationCocycles

/-! # Common normal periods fix the actual values of an original two-cocycle -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G)

/-- The original two-cocycle identity forces each common normal period to fix
every original coefficient value. No normalization at the identity is required. -/
theorem twoCocycle_normal_periods_fix_values (c : groupCohomology.cocycles₂ A)
    (U : Subgroup G) [U.Normal]
    (hp : ∀ g h u v, u ∈ U → v ∈ U → c (g * u, h * v) = c (g, h))
    (u : G) (hu : u ∈ U) (g h : G) : A.ρ u (c (g, h)) = c (g, h) := by
  have hfirst : ∀ t, c (u, t) = c (1, 1) := by
    intro t
    have he := hp 1 t u 1 hu U.one_mem
    simpa only [one_mul, mul_one, groupCohomology.cocycles₂_map_one_fst] using he
  have hconj : g⁻¹ * u * g ∈ U := by
    simpa only [inv_inv] using
      (Subgroup.Normal.conj_mem (inferInstance : U.Normal) u hu g⁻¹)
  have hprod : c (u * g, h) = c (g, h) := by
    calc
      c (u * g, h) = c (g * (g⁻¹ * u * g), h * 1) := by
        congr 1
        ext <;> simp only [mul_one]
        group
      _ = c (g, h) := hp g h (g⁻¹ * u * g) 1 hconj U.one_mem
  have hc : c (u * g, h) + c (u, g) = A.ρ u (c (g, h)) + c (u, g * h) :=
    (groupCohomology.mem_cocycles₂_iff _).mp c.property u g h
  rw [hprod, hfirst, hfirst] at hc
  exact (add_right_cancel hc).symm

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]

/-- Joint continuity into the actual discrete coefficient module gives one
open normal subgroup that is a period in both variables and fixes every value. -/
theorem continuousTwoCocycle_exists_openNormal_periods_and_fixed
    (c : continuousRepresentationCocyclesTwo A) :
    ∃ U : OpenNormalSubgroup G,
      (∀ g h u v, u ∈ U → v ∈ U → c.val (g * u, h * v) = c.val (g, h)) ∧
      (∀ u, u ∈ U → ∀ g h, A.ρ u (c.val (g, h)) = c.val (g, h)) := by
  let f : C(G × G, A) := ⟨fun z => c.val z, c.property⟩
  obtain ⟨U, hU⟩ := compactDiscreteTwoFunction_exists_commonPeriods f
  refine ⟨U, hU, ?_⟩
  intro u hu g h
  exact twoCocycle_normal_periods_fix_values A c.val U.toSubgroup hU u hu g h

end
end Dubon2026
