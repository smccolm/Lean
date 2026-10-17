import Dubon2026.UnramifiedNormalClosure
import Dubon2026.ArithmeticExceptionalSUnitSupport

/-! # Placing the prescribed-support norm field in the original arithmetic union

The existing unramified tower and normal-closure theorems turn the
constructed relative index-one property into membership in an actual
finite Galois stage of the original union. This is the placement step
needed before DUB-17's enlarged-stage invariant norm roots.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain IntermediateField
open scoped NumberField
variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
  (E : IntermediateField K Ω) [FiniteDimensional K E] [NumberField E]
  (hE : E ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
  (L : Type) [Field L] [NumberField L] [Algebra E L] [FiniteDimensional E L]

include ha hE in
/-- Any actual embedded finite extension with the prescribed relative
ramification support lies in a constructed original finite Galois stage.
The containing stage includes the same original base field. -/
theorem originalNormField_exists_unramified_stage
    (i : L →ₐ[E] Ω)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 L),
      algebraMap (𝓞 E) (𝓞 L) (algebraMap (𝓞 K) (𝓞 E) a) ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 E)).ramificationIdx w.asIdeal = 1) :
    ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      E ≤ N.val.toIntermediateField ∧ ∀ x : L, i x ∈ N.val.toIntermediateField := by
  letI : Algebra K L := Algebra.compHom L (algebraMap K E)
  letI : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional K L := Module.Finite.trans E L
  have hL := numberField_unramified_tower (K := K) (L := E) (M := L) a
    (originalUnramifiedUnion_ambient_finite_ramification a ha E hE) hUnram
  letI : IsGalois K (normalClosure K L Ω) := {}
  let N : FiniteGaloisIntermediateField K Ω := ⟨normalClosure K L Ω⟩
  have hN := numberField_normalClosure_unramified (Ω := Ω) a ha hL
  have hi (x : L) : i x ∈ N.toIntermediateField :=
    (i.restrictScalars K).fieldRange_le_normalClosure ⟨x, rfl⟩
  refine ⟨⟨N, hN⟩, ?_, hi⟩
  intro x hx
  have h := hi (algebraMap E L (⟨x, hx⟩ : E))
  rw [i.commutes] at h
  exact h

include ha hE in
/-- The embedding and a containing stage can be constructed while
retaining any prescribed original finite Galois stage. The conclusion
asserts no relative degree or primary-group bound. -/
theorem originalNormField_exists_unramified_stage_above
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 L),
      algebraMap (𝓞 E) (𝓞 L) (algebraMap (𝓞 K) (𝓞 E) a) ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 E)).ramificationIdx w.asIdeal = 1) :
    ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      E ≤ N.val.toIntermediateField ∧ P.val.toIntermediateField ≤ N.val.toIntermediateField ∧
      ∃ i : L →ₐ[E] Ω, ∀ x : L, i x ∈ N.val.toIntermediateField := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let i : L →ₐ[E] Ω := IsAlgClosed.lift
  obtain ⟨N, hEN, hi⟩ := originalNormField_exists_unramified_stage K Ω a ha E hE L i hUnram
  let M : FiniteGaloisIntermediateField K Ω := N.val ⊔ P.val
  have hM := finiteGalois_sup_unramified a ha N.val P.val N.property P.property
  exact ⟨⟨M, hM⟩, hEN.trans le_sup_left, le_sup_right, i,
    fun x => (show N.val.toIntermediateField ≤ M.toIntermediateField from le_sup_left) (hi x)⟩

end
end Dubon2026
