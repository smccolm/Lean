import Dubon2026.OriginalNormFieldStageNormRoots

/-! # Enlarged-stage norm roots with the original embedded base field

Arithmetic stages are nested intermediate-field types. Retaining their
given embedding, instead of replacing them by an isomorphic field,
keeps the actual coefficient maps in DUB-17's norm-root construction.
The existing unramified normal closure and literal norm tower provide
the same containing stage and norm roots for that original base type.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain IntermediateField
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable (K E L Ω : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Field Ω]
  [Algebra K E] [Algebra E L] [Algebra K Ω] [Algebra E Ω]
  [IsScalarTower K E Ω] [FiniteDimensional K E] [FiniteDimensional E L]
  [IsGalois E L] [IsAlgClosure K Ω]

/-- The original base embedding and a finite norm field with the
required ramification construct an actual enlarged arithmetic stage
with invariant roots of all quotient norms. No primary-degree bound
or construction of the input norm field is asserted. -/
theorem originalEmbeddedNormField_exists_stage_invariant_norm_roots
    (a : 𝓞 K) (ha : a ≠ 0) (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ (σ : Gal(E/E)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv E E σ v ∈ S) (n : ℕ)
    (hBase : ∀ v : HeightOneSpectrum (𝓞 E), algebraMap (𝓞 K) (𝓞 E) a ∉ v.asIdeal →
      (v.asIdeal.under (𝓞 K)).ramificationIdx v.asIdeal = 1)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 L),
      algebraMap (𝓞 E) (𝓞 L) (algebraMap (𝓞 K) (𝓞 E) a) ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 E)).ramificationIdx w.asIdeal = 1)
    (hNorm : (originalIdeleClassNormLinear E L).range ≤
      LinearMap.range ((n : ℤ) • (LinearMap.id :
        originalIdeleClassRep E E →ₗ[ℤ] originalIdeleClassRep E E)) ⊔
      LinearMap.range (originalOutsideIdeleClassRepHom E E S hS).hom.toLinearMap) :
    ∃ (N : OriginalUnramifiedGaloisStage (Ω := Ω) a) (j : E →ₐ[K] N.val),
      (∀ x : E, (j x : Ω) = algebraMap E Ω x) ∧
      P.val.toIntermediateField ≤ N.val.toIntermediateField ∧
      letI : Algebra E N.val := j.toRingHom.toAlgebra
      letI : IsScalarTower K E N.val := IsScalarTower.of_algHom j
      letI : FiniteDimensional E N.val := FiniteDimensional.right K E N.val
      OriginalOutsideQuotientInvariantNormRoots E N.val S n := by
  letI : Algebra K L := Algebra.compHom L (algebraMap K E)
  letI : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional K L := Module.Finite.trans E L
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let i : L →ₐ[E] Ω := IsAlgClosed.lift
  have hL := numberField_unramified_tower (K := K) (L := E) (M := L) a hBase hUnram
  letI : IsGalois K (normalClosure K L Ω) := {}
  let R : FiniteGaloisIntermediateField K Ω := ⟨normalClosure K L Ω⟩
  have hR := numberField_normalClosure_unramified (Ω := Ω) a ha hL
  let M := R ⊔ P.val
  have hM := finiteGalois_sup_unramified a ha R P.val hR P.property
  have hi (x : L) : i x ∈ M.toIntermediateField :=
    (show R.toIntermediateField ≤ M.toIntermediateField from le_sup_left)
      ((i.restrictScalars K).fieldRange_le_normalClosure ⟨x, rfl⟩)
  have hE (x : E) : algebraMap E Ω x ∈ M.toIntermediateField := by
    have h := hi (algebraMap E L x)
    rw [i.commutes] at h
    exact h
  let j : E →ₐ[K] M := {
    toFun := fun x => ⟨algebraMap E Ω x, hE x⟩
    map_one' := Subtype.ext (map_one (algebraMap E Ω))
    map_mul' := fun x y => Subtype.ext (map_mul (algebraMap E Ω) x y)
    map_zero' := Subtype.ext (map_zero (algebraMap E Ω))
    map_add' := fun x y => Subtype.ext (map_add (algebraMap E Ω) x y)
    commutes' := fun x => Subtype.ext (IsScalarTower.algebraMap_apply K E Ω x).symm }
  refine ⟨⟨M, hM⟩, j, fun _ => rfl, le_sup_right, ?_⟩
  letI : Algebra E M := j.toRingHom.toAlgebra
  letI : IsScalarTower K E M := IsScalarTower.of_algHom j
  letI : FiniteDimensional E M := FiniteDimensional.right K E M
  letI : IsGalois E M := IsGalois.tower_top_of_isGalois K E M
  let f : L →ₐ[E] M := {
    toFun := fun x => ⟨i x, hi x⟩
    map_one' := Subtype.ext i.map_one
    map_mul' := fun x y => Subtype.ext (i.map_mul x y)
    map_zero' := Subtype.ext i.map_zero
    map_add' := fun x y => Subtype.ext (i.map_add x y)
    commutes' := fun x => Subtype.ext (i.commutes x) }
  letI : Algebra L M := f.toRingHom.toAlgebra
  letI : IsScalarTower E L M := IsScalarTower.of_algHom f
  letI : FiniteDimensional L M := FiniteDimensional.right E L M
  letI : IsGalois L M := IsGalois.tower_top_of_isGalois E L M
  exact originalOutsideQuotientInvariantNormRoots_of_tower E L M S hS n hNorm

end
end Dubon2026
