import Dubon2026.OriginalFinitePrimeRelationConnecting

/-! The constructed finite relation has no coordinate, and hence no
connecting class, above a base prime outside its specified family. This
is the support obligation for DUB-17's finite local-pairing total. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
attribute [local instance 1100] Rep.hV2
attribute [local instance] finitePrimeRelationCosets
variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (T : Finset (HeightOneSpectrum (𝓞 K))) (w : T → S)
  (B : Rep.{0} ℤ Gal(L/K))

omit [NumberField K] in
/-- Every finite coordinate outside the actual base-prime family is zero. -/
theorem originalFinitePrimeSPlaceRelation_outside_base
    (hw : ∀ v : T, originalFinitePrimeBelow K L (w v).val = v.val)
    (φ : ∀ v : T,
      Rep.res (OriginalFiniteDecompositionGroup K L (w v).val).subtype (originalRelationModule B) ⟶
        originalAdicUnitRep K L (w v).val)
    (v : HeightOneSpectrum (𝓞 L)) (hv : originalFinitePrimeBelow K L v ∉ T)
    (x : originalRelationModule B) :
    (originalFullIdeleAdicRepHom K L v).hom
      ((originalSPlaceFullIdeleInclusion K L S hS).hom
        ((originalFinitePrimeSPlaceRelation K L S hS T w B φ).hom x)) = 0 := by
  by_cases hvS : v ∈ S
  · rw [originalSPlaceFullIdeleInclusion_finite K L S hS _ ⟨v, hvS⟩]
    let f (u : T) : originalRelationModule B →ₗ[ℤ] supportedUnrestrictedUnitRep K L S hS :=
      (originalSinglePrimeSPlaceRelation K L S hS (w u).val B (φ u)).hom.toLinearMap
    change (LinearMap.proj (R := ℤ) (Sum.inr (⟨v, hvS⟩ : S))) ((∑ u : T, f u) x) = 0
    rw [LinearMap.sum_apply]
    refine (map_sum (LinearMap.proj (R := ℤ) (Sum.inr (⟨v, hvS⟩ : S)))
      (fun u : T => f u x) Finset.univ).trans ?_
    apply Finset.sum_eq_zero
    intro u _
    apply originalSinglePrimeSPlaceRelation_outside_orbit K L S hS (w u).val B ⟨v, hvS⟩
    intro σ hσ
    have he := congrArg (originalFinitePrimeBelow K L) hσ
    rw [originalFinitePrimeBelow_galois, hw] at he
    exact hv (he ▸ u.property)
  · exact originalSPlaceFullIdeleInclusion_outside K L S hS _ v hvS

omit [NumberField K] in
/-- The corresponding original full-idele connecting class vanishes at
every upper prime whose contraction lies outside the constructed family. -/
theorem originalFinitePrimeSPlaceRelation_adic_zero
    (hw : ∀ v : T, originalFinitePrimeBelow K L (w v).val = v.val)
    (φ : ∀ v : T,
      Rep.res (OriginalFiniteDecompositionGroup K L (w v).val).subtype (originalRelationModule B) ⟶
        originalAdicUnitRep K L (w v).val)
    (v : HeightOneSpectrum (𝓞 L)) (hv : originalFinitePrimeBelow K L v ∉ T)
    (y : groupCohomology B 1) :
    originalFullIdeleAdicH2 K L v
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSPlaceFullIdeleInclusion K L S hS)
        (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep K L S hS)
          (originalFinitePrimeSPlaceRelation K L S hS T w B φ) y)) = 0 := by
  let π := (OriginalFiniteDecompositionGroup K L v).subtype
  let Φ := originalFinitePrimeSPlaceRelation K L S hS T w B φ
  let inc := originalSPlaceFullIdeleInclusion K L S hS
  let j := originalFullIdeleAdicRepHom K L v
  let jS : Rep.res π (supportedUnrestrictedUnitRep K L S hS) ⟶ originalAdicUnitRep K L v :=
    (Rep.resFunctor π).map inc ≫ j
  have he : (Rep.resFunctor π).map Φ ≫ jS = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact originalFinitePrimeSPlaceRelation_outside_base K L S hS T w B hw φ v hv x
  have h := originalRestrictedRelation_obstruction_inflation π B
    (supportedUnrestrictedUnitRep K L S hS) (originalAdicUnitRep K L v) Φ jS
  erw [he] at h
  have hzero : (groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L v) 2).map
      (0 : Rep.res π (originalRelationModule B) ⟶ originalAdicUnitRep K L v) = 0 :=
    Functor.map_zero _ _ _
  erw [hzero] at h
  have hz := congrArg (fun m => m.hom y) h
  have hm := groupCohomology.map_comp
    (A := supportedUnrestrictedUnitRep K L S hS) (B := originalFullIdeleRep K L)
    (C := originalAdicUnitRep K L v) (MonoidHom.id Gal(L/K)) π inc j 2
  have hc := congrArg (fun m => m.hom
    (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep K L S hS) Φ y)) hm
  exact hc.symm.trans hz

end
end Dubon2026
