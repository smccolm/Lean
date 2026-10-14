import Dubon2026.ArithmeticFiniteLocalRestrictionSquare
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! # Cyclicity of the literal arithmetic local compositum

The two already constructed field images generate the actual local stage.
Consequently its restriction to the original global field is injective.
For DUB-17's invariant-sum route this discharges local cyclicity from the
constructed global cyclic stage, without assuming a local comparison model.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] DivisionRing.toRatAlgebra SubfieldClass.instSMulRat

/-- Generation by the base and the actual embedded normal field makes original Galois restriction injective. -/
theorem embeddedNormalGaloisRestriction_injective_of_ranges
    {k E F K : Type*} [Field k] [Field E] [Field F] [Field K]
    [Algebra k E] [Normal k E] [Algebra k F] [Algebra F K] [Algebra k K]
    [IsScalarTower k F K] (e : E →ₐ[k] K)
    (hgen : (algebraMap F K).fieldRange ⊔ e.toRingHom.fieldRange = ⊤) :
    Function.Injective (embeddedNormalGaloisRestriction (F := F) e) := by
  intro g h hgh
  have hs : (algebraMap F K).fieldRange ⊔ e.toRingHom.fieldRange ≤
      g.toRingHom.eqLocusField h.toRingHom := by
    apply sup_le
    · rintro x ⟨y, rfl⟩
      exact (g.commutes y).trans (h.commutes y).symm
    · rintro x ⟨y, rfl⟩
      change g (e y) = h (e y)
      rw [← embeddedNormalGaloisRestriction_commutes,
        ← embeddedNormalGaloisRestriction_commutes, hgh]
  rw [hgen] at hs
  apply AlgEquiv.ext
  intro x
  exact hs (Subfield.mem_top x)

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

/-- The actual local compositum of a cyclic original arithmetic stage is cyclic; its restriction is injective by the proved field generation identity. -/
theorem rationalArithmeticFiniteLocalStage_isCyclic
    (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)] (p : ℕ) (hp : p.Prime) :
    IsCyclic Gal(rationalArithmeticFiniteLocalStage a F p hp / rationalPrimeLocalField p hp) := by
  let A₀ : Algebra ℚ F := inferInstance
  have h₀ : letI := A₀; IsCyclic Gal(F/ℚ) := inferInstance
  have hc : ∀ A : Algebra ℚ F, letI := A; IsCyclic Gal(F/ℚ) := by
    intro A
    have hA : A = A₀ := Subsingleton.elim _ _
    cases hA
    exact h₀
  refine @isCyclic_of_injective _ _ _ _ ?_
    (rationalArithmeticFiniteLocalRestriction a F p hp) ?_
  · exact hc _
  · exact embeddedNormalGaloisRestriction_injective_of_ranges
      (rationalArithmeticFiniteLocalStageInclusion a F p hp)
      (rationalArithmeticFiniteLocalStage_ranges a F p hp)

end
end Dubon2026
