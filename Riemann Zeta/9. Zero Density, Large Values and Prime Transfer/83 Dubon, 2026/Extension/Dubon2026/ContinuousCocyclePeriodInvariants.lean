import Dubon2026.CompactDiscreteFunctionPeriods
import Dubon2026.ContinuousRepresentationCocycles

/-! # Normal periods of actual cocycles fix their original coefficient values -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G)

/-- An actual normal period subgroup of an original one-cocycle fixes every
original cocycle value under the original coefficient action. This follows from
the original cocycle identity, not from an assumption of trivial action. -/
theorem cocycle_normal_periods_fix_values (c : groupCohomology.cocycles₁ A)
    (U : Subgroup G) [U.Normal]
    (hp : ∀ g u, u ∈ U → c (g * u) = c g) (u : G) (hu : u ∈ U) (g : G) :
    A.ρ u (c g) = c g := by
  have hcu : c u = 0 := by
    have h := hp 1 u hu
    simpa only [one_mul, groupCohomology.cocycles₁_map_one] using h
  have hconj : g⁻¹ * u * g ∈ U := by
    simpa only [inv_inv] using
      (Subgroup.Normal.conj_mem (inferInstance : U.Normal) u hu g⁻¹)
  have hprod : c (u * g) = c g := by
    calc
      c (u * g) = c (g * (g⁻¹ * u * g)) := by congr 1; group
      _ = c g := hp g (g⁻¹ * u * g) hconj
  have hc : c (u * g) = A.ρ u (c g) + c u :=
    (groupCohomology.mem_cocycles₁_iff _).mp c.property u g
  rw [hcu, add_zero, hprod] at hc
  exact hc.symm

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]

/-- Every original continuous cocycle of a compact group with actual discrete
coefficients has a genuine open normal period subgroup, and this same subgroup
fixes all its original coefficient values. No finite-image field is postulated. -/
theorem continuousCocycle_exists_openNormal_periods_and_fixed
    (c : continuousRepresentationCocyclesOne A) :
    ∃ U : OpenNormalSubgroup G,
      (∀ g u, u ∈ U → c.val (g * u) = c.val g) ∧
      (∀ u, u ∈ U → ∀ g, A.ρ u (c.val g) = c.val g) := by
  let f : C(G, A) := ⟨fun g => c.val g, c.property⟩
  obtain ⟨U, hU⟩ := compactDiscreteFunction_exists_openNormalPeriods f
  refine ⟨U, hU, ?_⟩
  intro u hu g
  exact cocycle_normal_periods_fix_values A c.val U.toSubgroup hU u hu g

end
end Dubon2026
