import Dubon2026.ArithmeticClassQuotientTransitionInjectivity

/-! # Fixed original arithmetic colimit coefficients are already fixed at their stage

Faithful finite-stage inclusions and surjective actual Galois restriction
reflect invariance. This gives the finite invariant representative needed
for the global arithmetic class-formation coefficient in DUB-17.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The original finite class coefficient is invariant exactly when its actual arithmetic colimit image is invariant. -/
theorem arithmeticClassesModOutsideColimitOf_fixed_iff
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : arithmeticGlobalClassesModOutsideStageRep K Ω a ha E) :
    (∀ g, (arithmeticClassesModOutsideColimitRep K Ω a ha).ρ g
      ((coefficientRepresentationColimitOf
        (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
        (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom x) =
      (coefficientRepresentationColimitOf
        (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
        (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom x) ↔
      ∀ σ, (arithmeticClassesModOutsideStageRep K Ω a ha E).ρ σ x = x := by
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    originalUnramifiedGaloisUnion_isGalois a
  let i := coefficientRepresentationColimitOf
    (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E
  constructor
  · intro hx σ
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective
      (originalUnramifiedGaloisUnion (Ω := Ω) a) σ
    apply arithmeticClassesModOutsideColimitOf_injective K Ω a ha E
    exact (Rep.hom_comm_apply i g x).trans (hx g)
  · intro hx g
    exact (Rep.hom_comm_apply i g x).symm.trans
      (congrArg i.hom (hx (AlgEquiv.restrictNormalHom E g)))

/-- Every actual invariant arithmetic class-colimit coefficient has an invariant representative at an original finite Galois stage. -/
theorem arithmeticClassesModOutsideColimit_fixed_exists_stage
    (x : arithmeticClassesModOutsideColimitRep K Ω a ha)
    (hx : ∀ g, (arithmeticClassesModOutsideColimitRep K Ω a ha).ρ g x = x) :
    ∃ (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
      (y : (arithmeticClassesModOutsideStageRep K Ω a ha E).ρ.invariants),
      (coefficientRepresentationColimitOf
        (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
        (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom y.val = x := by
  obtain ⟨E, y, hy⟩ := Module.DirectLimit.exists_of x
  have hfixed : ∀ σ, (arithmeticClassesModOutsideStageRep K Ω a ha E).ρ σ y = y := by
    apply (arithmeticClassesModOutsideColimitOf_fixed_iff K Ω a ha E y).mp
    intro g
    change (arithmeticClassesModOutsideColimitRep K Ω a ha).ρ g
      (Module.DirectLimit.of ℤ _ _ _ E y) = Module.DirectLimit.of ℤ _ _ _ E y
    rw [hy]
    exact hx g
  exact ⟨E, ⟨y, hfixed⟩, hy⟩

end
end Dubon2026
