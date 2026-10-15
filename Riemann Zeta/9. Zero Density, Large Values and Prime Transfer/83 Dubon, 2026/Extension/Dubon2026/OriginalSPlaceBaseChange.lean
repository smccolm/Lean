import Dubon2026.ArithmeticSUnitIdeleBaseChange
import Dubon2026.OriginalSPlaceClassComparison

/-! # Literal base change on the source S-place idele factors

The source product has outside coordinates equal to one. Restricting the
original supported-idele base change to these factors, and proving that it
commutes with the actual projection, supplies the transition needed for the
fixed-support source class colimit in DUB-17's global-duality route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K L w ∈ S)

private def supportedMap : Additive (numberFieldSupportedIdeles K S) →ₗ[ℤ]
    Additive (numberFieldSupportedIdeles L T) :=
  (originalSupportedIdeleBaseChangeMap K L S T
    (fun w hw hv => hw ((hST w).mpr hv))).toAdditive.toIntLinearMap

private theorem projected_map_congr
    (x y : Additive (numberFieldSupportedIdeles K S))
    (h : (supportedIdeleLocalFactorLinearEquiv K S x).1 =
      (supportedIdeleLocalFactorLinearEquiv K S y).1) :
    (supportedIdeleLocalFactorLinearEquiv L T (supportedMap K L S T hST x)).1 =
      (supportedIdeleLocalFactorLinearEquiv L T (supportedMap K L S T hST y)).1 := by
  funext p
  cases p with
  | inl w =>
    apply Additive.toMul.injective
    apply Units.ext
    have hw := congrArg
      (fun z => (z (Sum.inl (w.comap (algebraMap K L)))).toMul.val) h
    exact congrArg (originalInfiniteCompletionBaseChange K L w) hw
  | inr w =>
    apply Additive.toMul.injective
    apply Units.ext
    let v : S := ⟨originalFinitePrimeBelow K L w.val, (hST w.val).mp w.property⟩
    have hv := congrArg (fun z => (z (Sum.inr v)).toMul.val) h
    exact congrArg (originalFiniteCompletionBaseChange K L w.val) hv

/-- The actual source S-place transition is induced by original full-idele base change and the original local-factor split. -/
def originalSPlaceBaseChange :
    (∀ p : SUnitLogPlace K S, supportedUnrestrictedUnitModule K S p) →ₗ[ℤ]
      (∀ p : SUnitLogPlace L T, supportedUnrestrictedUnitModule L T p) :=
  ((AddMonoidHom.fst _ _).comp ((supportedIdeleLocalFactorLinearEquiv L T).toAddMonoidHom.comp
    ((supportedMap K L S T hST).toAddMonoidHom.comp
      ((supportedIdeleLocalFactorLinearEquiv K S).symm.toAddMonoidHom.comp
        (AddMonoidHom.inl _ _))))).toIntLinearMap

/-- Projection to the source S-place factors commutes with the original supported-idele transition at the same pulled-back support. -/
theorem originalSPlaceBaseChange_projection
    (x : Additive (numberFieldSupportedIdeles K S)) :
    originalSPlaceBaseChange K L S T hST (supportedIdeleLocalFactorLinearEquiv K S x).1 =
      (supportedIdeleLocalFactorLinearEquiv L T
        (Additive.ofMul (originalSupportedIdeleBaseChangeMap K L S T
          (fun w hw hv => hw ((hST w).mpr hv)) x.toMul))).1 := by
  exact projected_map_congr K L S T hST
    ((supportedIdeleLocalFactorLinearEquiv K S).symm
      ((supportedIdeleLocalFactorLinearEquiv K S x).1, 0)) x
    (by
      have he := (supportedIdeleLocalFactorLinearEquiv K S).apply_symm_apply
        ((supportedIdeleLocalFactorLinearEquiv K S x).1, 0)
      have hp := congrArg Prod.fst he
      exact hp)

/-- The original diagonal S-unit map commutes with source S-place base change. -/
theorem originalSPlaceBaseChange_principal
    (u : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    originalSPlaceBaseChange K L S T hST
      (supportedIdeleLocalFactorLinearEquiv K S
        (Additive.ofMul (numberFieldSupportedPrincipalIdele K S u))).1 =
      (supportedIdeleLocalFactorLinearEquiv L T
        (Additive.ofMul (numberFieldSupportedPrincipalIdele L T
          (originalValuationSUnitBaseChangeMap K L S T
            (fun w hw hv => hw ((hST w).mpr hv)) u)))).1 := by
  exact (originalSPlaceBaseChange_projection K L S T hST _).trans
    (congrArg (fun v => (supportedIdeleLocalFactorLinearEquiv L T (Additive.ofMul v)).1)
      (originalSupportedIdeleBaseChangeMap_principal K L S T
        (fun w hw hv => hw ((hST w).mpr hv)) u))

end
end Dubon2026
