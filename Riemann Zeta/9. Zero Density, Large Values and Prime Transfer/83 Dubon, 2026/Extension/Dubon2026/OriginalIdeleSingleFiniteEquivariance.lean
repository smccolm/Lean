import Dubon2026.OriginalIdeleSingleFinite
import Dubon2026.OriginalIdeleAdicH2

/-! # The actual single-prime insertion respects the decomposition action

This supplies the coefficient section needed to lift a local H2 class at
the already proved full-decomposition prime on DUB-17's full-order class
route. The local and global actions are the original completed actions.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- Insertion of a single original local unit intertwines the actual stabilizer and full-idele actions. -/
theorem originalIdeleSingleFinite_galois (w : HeightOneSpectrum (𝓞 L))
    (σ : OriginalFiniteDecompositionGroup K L w) (u : (w.adicCompletion L)ˣ) :
    numberFieldIdeleGaloisMap K L σ.val (originalIdeleSingleFinite L w u) =
      originalIdeleSingleFinite L w
        (Units.map (numberFieldGaloisLocalTransport K L σ.val w w σ.property).toMonoidHom u) := by
  apply originalIdele_eq_of_components L
  · intro v
    by_cases hv : v = w
    · subst v
      rw [originalIdeleSingleFinite_same]
      apply Units.ext
      change numberFieldFiniteAdeleGaloisMap K L σ.val (originalIdeleSingleFinite L w u).val.2 w = _
      rw [numberFieldFiniteAdeleGaloisMap_apply K L σ.val _ w w σ.property]
      exact congrArg (numberFieldGaloisLocalTransport K L σ.val w w σ.property)
        (congrArg Units.val (originalIdeleSingleFinite_same L w u))
    · rw [originalIdeleSingleFinite_ne L w v hv]
      apply Units.ext
      let e := numberFieldGaloisPlaceEquiv K L σ.val
      have he : e.symm v ≠ w := by
        intro h
        have hh : v = w := (e.apply_symm_apply v).symm.trans
          ((congrArg e h).trans σ.property)
        exact hv hh
      change numberFieldFiniteAdeleGaloisMap K L σ.val (originalIdeleSingleFinite L w u).val.2 v = 1
      rw [numberFieldFiniteAdeleGaloisMap_apply K L σ.val _ (e.symm v) v (e.apply_symm_apply v)]
      have hc := congrArg Units.val (originalIdeleSingleFinite_ne L w (e.symm v) he u)
      change (originalIdeleSingleFinite L w u).val.2 (e.symm v) = 1 at hc
      rw [hc, map_one]
  · intro v
    rw [originalIdeleSingleFinite_infinite]
    apply Units.ext
    change numberFieldInfiniteAdeleGaloisMap K L σ.val (originalIdeleSingleFinite L w u).val.1 v = 1
    rw [numberFieldInfiniteAdeleGaloisMap_apply K L σ.val _ (σ.val⁻¹ • v) v
      (smul_inv_smul σ.val v)]
    have hc := congrArg Units.val (originalIdeleSingleFinite_infinite L w u (σ.val⁻¹ • v))
    change (originalIdeleSingleFinite L w u).val.1 (σ.val⁻¹ • v) = 1 at hc
    rw [hc, map_one]

/-- The single-prime inclusion is a morphism of the original decomposition representations. -/
def originalIdeleSingleFiniteRepHom (w : HeightOneSpectrum (𝓞 L)) :
    originalAdicUnitRep K L w ⟶
      Rep.res (OriginalFiniteDecompositionGroup K L w).subtype (originalFullIdeleRep K L) :=
  Rep.ofHom ⟨(originalIdeleSingleFiniteHom L w).toAdditive.toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro u
    exact congrArg Additive.ofMul (originalIdeleSingleFinite_galois K L w σ u.toMul).symm⟩

/-- The actual original local evaluation has the single-prime insertion as a coefficient section. -/
theorem originalIdeleSingleFiniteRepHom_section (w : HeightOneSpectrum (𝓞 L)) :
    originalIdeleSingleFiniteRepHom K L w ≫ originalFullIdeleAdicRepHom K L w =
      𝟙 (originalAdicUnitRep K L w) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  exact congrArg Additive.ofMul (originalIdeleSingleFinite_same L w u.toMul)

end
end Dubon2026
