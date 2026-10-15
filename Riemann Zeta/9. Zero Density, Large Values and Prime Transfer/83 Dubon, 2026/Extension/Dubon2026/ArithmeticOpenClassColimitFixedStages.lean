import Dubon2026.ArithmeticClassQuotientTransitionInjectivity

/-! # Original open-subgroup fixed coefficients at a prescribed finite stage

Faithful original class-colimit inclusions reflect invariance without any
cohomology comparison theorem. Enlarging a representative above a specified
stage permits finite fixed-field descent, the remaining coefficient input
to the arithmetic class formation serving DUB-17.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))

/-- An original finite class is fixed by the actual open subgroup exactly when its literal colimit image is fixed. -/
theorem arithmeticClassesModOutsideColimitOf_open_fixed_iff
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : arithmeticGlobalClassesModOutsideStageRep K Ω a ha E) :
    (∀ g : H, (arithmeticClassesModOutsideColimitRep K Ω a ha).ρ g.val
      ((coefficientRepresentationColimitOf
        (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
        (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom x) =
      (coefficientRepresentationColimitOf
        (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
        (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom x) ↔
      ∀ g : H, (arithmeticGlobalClassesModOutsideStageRep K Ω a ha E).ρ g.val x = x := by
  let i := coefficientRepresentationColimitOf
    (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E
  constructor
  · intro hx g
    apply arithmeticClassesModOutsideColimitOf_injective K Ω a ha E
    exact (Rep.hom_comm_apply i g.val x).trans (hx g)
  · intro hx g
    exact (Rep.hom_comm_apply i g.val x).symm.trans (congrArg i.hom (hx g))

/-- Every original open-subgroup invariant class coefficient has a fixed representative above any prescribed arithmetic stage. -/
theorem arithmeticClassesModOutsideColimit_open_fixed_exists_stage_above
    (E₀ : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : arithmeticClassesModOutsideColimitRep K Ω a ha)
    (hx : ∀ g : H, (arithmeticClassesModOutsideColimitRep K Ω a ha).ρ g.val x = x) :
    ∃ (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)),
      E₀ ≤ F ∧ ∃ y :
        (Rep.res H.toSubgroup.subtype (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)).ρ.invariants,
        (coefficientRepresentationColimitOf
          (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
          (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) F).hom y.val = x := by
  obtain ⟨E, y, hy⟩ := Module.DirectLimit.exists_of x
  let F := E ⊔ E₀
  let z := (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F le_sup_left).hom y
  have hz : (coefficientRepresentationColimitOf
      (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
      (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) F).hom z = x := by
    have he := Module.DirectLimit.of_f
      (R := ℤ) (G := fun D => arithmeticGlobalClassesModOutsideStageRep K Ω a ha D)
      (f := fun D E h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha D E h).hom.toLinearMap)
      (hij := (le_sup_left : E ≤ F)) (x := y)
    exact he.trans hy
  have hfixed : ∀ g : H, (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F).ρ g.val z = z := by
    apply (arithmeticClassesModOutsideColimitOf_open_fixed_iff K Ω a ha H F z).mp
    intro g
    rw [hz]
    exact hx g
  exact ⟨F, le_sup_right, ⟨z, hfixed⟩, hz⟩

end
end Dubon2026
