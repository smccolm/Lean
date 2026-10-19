import Dubon2026.ContinuousUnramifiedFirstOrder
import Dubon2026.ContinuousTraceZeroRestriction

/-! Compare the original trace-zero inertia kernel with the actual
fixed-determinant local deformation subspace. The subgroup form supplies
the missing comparison for the original prime-local groups in DUB-17. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace G] [TopologicalSpace K] [IsTopologicalRing K]

/-- The actual trace-zero inclusion restricts to the original unramified
fixed-determinant local subspace. -/
def continuousUnramifiedTraceToFixedDeterminant
    (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ) (N : Subgroup G) :
    (continuousTraceZeroH1Restriction ρ hρ N.subtype continuous_subtype_val).ker →ₗ[K]
      continuousUnramifiedFixedDeterminantClasses ρ hρ N where
  toFun x := ⟨continuousTraceZeroH1Inclusion ρ hρ x.val, by
    refine ⟨continuousTraceZeroH1Inclusion_mem ρ hρ x.val, ?_⟩
    change continuousMatrixAdjointH1Restriction ρ hρ N.subtype continuous_subtype_val
      (continuousTraceZeroH1Inclusion ρ hρ x.val) = 0
    rw [← continuousTraceZeroH1Restriction_inclusion, x.property, map_zero]⟩
  map_add' x y := Subtype.ext (map_add (continuousTraceZeroH1Inclusion ρ hρ) x.val y.val)
  map_smul' r x := Subtype.ext (map_smul (continuousTraceZeroH1Inclusion ρ hρ) r x.val)

/-- The same inclusion is injective for the actual invertible matrix rank. -/
theorem continuousUnramifiedTraceToFixedDeterminant_injective
    (hn : (Fintype.card ι : K) ≠ 0)
    (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ) (N : Subgroup G) :
    Function.Injective (continuousUnramifiedTraceToFixedDeterminant ρ hρ N) := by
  intro x y h
  apply Subtype.ext
  apply continuousTraceZeroH1ToFixedDeterminant_injective hn ρ hρ
  apply Subtype.ext
  exact congrArg (fun z : continuousUnramifiedFixedDeterminantClasses ρ hρ N => z.val) h

/-- Every actual simultaneous determinant and inertia class is represented
by an original trace-zero inertia class. -/
theorem continuousUnramifiedTraceToFixedDeterminant_surjective
    (hn : (Fintype.card ι : K) ≠ 0)
    (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ) (N : Subgroup G) :
    Function.Surjective (continuousUnramifiedTraceToFixedDeterminant ρ hρ N) := by
  intro y
  obtain ⟨x, hx⟩ := continuousTraceZeroH1ToFixedDeterminant_surjective ρ hρ
    ⟨y.val, y.property.1⟩
  have hxval : continuousTraceZeroH1Inclusion ρ hρ x = y.val := congrArg Subtype.val hx
  have hI : continuousTraceZeroH1Restriction ρ hρ N.subtype continuous_subtype_val x = 0 := by
    apply (continuousTraceZeroH1Restriction_eq_zero_iff hn ρ hρ
      N.subtype continuous_subtype_val x).mpr
    rw [hxval]
    exact y.property.2
  exact ⟨⟨x, hI⟩, Subtype.ext hxval⟩

/-- The actual trace-zero restriction kernel and the genuine local
fixed-determinant first-order subspace have identical linear structure. -/
def continuousUnramifiedTraceFixedDeterminantEquiv
    (hn : (Fintype.card ι : K) ≠ 0)
    (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ) (N : Subgroup G) :
    (continuousTraceZeroH1Restriction ρ hρ N.subtype continuous_subtype_val).ker ≃ₗ[K]
      continuousUnramifiedFixedDeterminantClasses ρ hρ N :=
  LinearEquiv.ofBijective (continuousUnramifiedTraceToFixedDeterminant ρ hρ N)
    ⟨continuousUnramifiedTraceToFixedDeterminant_injective hn ρ hρ N,
      continuousUnramifiedTraceToFixedDeterminant_surjective hn ρ hρ N⟩

end
end Dubon2026
