import Dubon2026.IntegralAdelicProjectiveFaithfulness

/-! # Actual general-level adelic projective integration regions -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Set MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Pointwise

/-- The original real Gamma0 region times the genuine finite projective level subgroup. -/
def adelicProjectiveGamma0Domain (N : ℕ) : Set AdelicProjectiveGroup :=
  realProjectiveGamma0Domain N ×ˢ finiteProjectiveGL2Level N

/-- The actual general-level region is open in the original product topology. -/
theorem adelicProjectiveGamma0Domain_isOpen (N : ℕ) [NeZero N] :
    IsOpen (adelicProjectiveGamma0Domain N) :=
  (realProjectiveGamma0Domain_isOpen N).prod (finiteProjectiveGL2Level_compact_open N).2

/-- The genuine finite projective level subgroup has positive finite Haar volume. -/
theorem finiteProjectiveGL2Level_volume (N : ℕ) [NeZero N] :
    0 < finiteProjectiveGL2Measure (finiteProjectiveGL2Level N) ∧
      finiteProjectiveGL2Measure (finiteProjectiveGL2Level N) < ⊤ := by
  constructor
  · exact (finiteProjectiveGL2Level_compact_open N).2.measure_pos
      finiteProjectiveGL2Measure ⟨1, (finiteProjectiveGL2Level N).one_mem⟩
  · exact (finiteProjectiveGL2Level_compact_open N).1.measure_lt_top

/-- The original general-level region has the exact product of real and finite Haar volumes. -/
theorem adelicProjectiveGamma0Domain_volume (N : ℕ) :
    adelicProjectiveMeasure (adelicProjectiveGamma0Domain N) =
      realProjectiveMeasure (realProjectiveGamma0Domain N) *
        finiteProjectiveGL2Measure (finiteProjectiveGL2Level N) :=
  Measure.prod_prod _ _

/-- Every actual original general-level adelic integration region has finite volume. -/
theorem adelicProjectiveGamma0Domain_volume_lt_top (N : ℕ) [NeZero N] :
    adelicProjectiveMeasure (adelicProjectiveGamma0Domain N) < ⊤ := by
  rw [adelicProjectiveGamma0Domain_volume]
  exact ENNReal.mul_lt_top (realProjectiveGamma0Domain_volume_lt_top N)
    (finiteProjectiveGL2Level_volume N).2

/-- The original integral projective level embeds in the actual rational arithmetic subgroup. -/
def integralProjectiveLevelToArithmetic (N : ℕ) : projectiveGamma0 N →* adelicProjectiveArithmetic :=
  (integralToAdelicProjective.codRestrict adelicProjectiveArithmetic
    integralToAdelicProjective_mem_arithmetic).comp (projectiveGamma0 N).subtype

/-- The original integral projective level has its actual finite component in the same finite level. -/
theorem integralProjectiveLevelToArithmetic_finite_level (N : ℕ) [NeZero N]
    (σ : projectiveGamma0 N) :
    (integralProjectiveLevelToArithmetic N σ).val.2 ∈ finiteProjectiveGL2Level N := by
  obtain ⟨a, ha, he⟩ := σ.property
  change (integralToAdelicProjective σ.val).2 ∈ finiteProjectiveGL2Level N
  rw [← he]
  exact integralToAdelicProjective_finite_level N ⟨a, ha⟩

/-- The actual finite projective coordinate factors through an original positive rational matrix and genuine level element. -/
theorem rationalProjectiveFinite_level_factorization (N : ℕ) [NeZero N]
    (a : RationalFiniteProjectiveGL2) :
    ∃ r : GL(2, ℚ)⁺, ∃ u : finiteProjectiveGL2Level N,
      a = (rationalPositiveToAdelicProjective r).2 * u.val := by
  obtain ⟨b, rfl⟩ := ProjGenLinGroup.mk_surjective a
  obtain ⟨r, u, hu⟩ := rationalGL2_finiteAdeles_gamma0_factorization N b
  refine ⟨r, ⟨ProjGenLinGroup.mk u.val, ⟨u.val, u.property, rfl⟩⟩, ?_⟩
  rw [hu, map_mul]
  rfl

end
end Dubon2026
