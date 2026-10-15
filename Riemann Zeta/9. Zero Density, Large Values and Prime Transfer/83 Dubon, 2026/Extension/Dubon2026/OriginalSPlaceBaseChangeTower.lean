import Dubon2026.OriginalSPlaceBaseChange
import Dubon2026.OriginalIdeleBaseChangeTower

/-! # Tower laws for the original source S-place idele transitions

The proved projection square transfers the existing full-idele tower law
to the fixed-support source local products. This is needed to form their
actual coefficient colimit on the DUB-17 global-duality dependency chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K E L : Type) [Field K] [Field E] [Field L]
  [NumberField K] [NumberField E] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 E)))
  (U : Finset (HeightOneSpectrum (𝓞 L)))
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K E w ∈ S)
  (hTU : ∀ w, w ∈ U ↔ originalFinitePrimeBelow E L w ∈ T)
  (hSU : ∀ w, w ∈ U ↔ originalFinitePrimeBelow K L w ∈ S)

/-- Actual source S-place base change composes along the same original field tower. -/
theorem originalSPlaceBaseChange_tower
    (x : ∀ p : SUnitLogPlace K S, supportedUnrestrictedUnitModule K S p) :
    originalSPlaceBaseChange E L T U hTU (originalSPlaceBaseChange K E S T hST x) =
      originalSPlaceBaseChange K L S U hSU x := by
  let y := (supportedIdeleLocalFactorLinearEquiv K S).symm (x, 0)
  have hy : (supportedIdeleLocalFactorLinearEquiv K S y).1 = x := by
    have he := (supportedIdeleLocalFactorLinearEquiv K S).apply_symm_apply (x, 0)
    have hp := congrArg Prod.fst he
    exact hp
  let bKE := originalSupportedIdeleBaseChangeMap K E S T
    (fun w hw hv => hw ((hST w).mpr hv))
  let bEL := originalSupportedIdeleBaseChangeMap E L T U
    (fun w hw hv => hw ((hTU w).mpr hv))
  let bKL := originalSupportedIdeleBaseChangeMap K L S U
    (fun w hw hv => hw ((hSU w).mpr hv))
  have hb : bEL (bKE y.toMul) = bKL y.toMul := by
    apply Subtype.ext
    exact originalIdeleBaseChangeMap_tower K E L y.toMul.val
  calc
    _ = originalSPlaceBaseChange E L T U hTU
        (supportedIdeleLocalFactorLinearEquiv E T (Additive.ofMul (bKE y.toMul))).1 :=
      congrArg (originalSPlaceBaseChange E L T U hTU)
        ((congrArg (originalSPlaceBaseChange K E S T hST) hy.symm).trans
          (originalSPlaceBaseChange_projection K E S T hST y))
    _ = (supportedIdeleLocalFactorLinearEquiv L U
        (Additive.ofMul (bEL (bKE y.toMul)))).1 :=
      originalSPlaceBaseChange_projection E L T U hTU (Additive.ofMul (bKE y.toMul))
    _ = (supportedIdeleLocalFactorLinearEquiv L U (Additive.ofMul (bKL y.toMul))).1 :=
      congrArg (fun z => (supportedIdeleLocalFactorLinearEquiv L U (Additive.ofMul z)).1) hb
    _ = originalSPlaceBaseChange K L S U hSU x :=
      (originalSPlaceBaseChange_projection K L S U hSU y).symm.trans
        (congrArg (originalSPlaceBaseChange K L S U hSU) hy)

omit [Field E] [Field L] [NumberField E] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L] in
/-- The original source S-place transition over the same field is the identity. -/
theorem originalSPlaceBaseChange_self
    (hSS : ∀ w, w ∈ S ↔ originalFinitePrimeBelow K K w ∈ S)
    (x : ∀ p : SUnitLogPlace K S, supportedUnrestrictedUnitModule K S p) :
    originalSPlaceBaseChange K K S S hSS x = x := by
  let y := (supportedIdeleLocalFactorLinearEquiv K S).symm (x, 0)
  have hy : (supportedIdeleLocalFactorLinearEquiv K S y).1 = x := by
    have he := (supportedIdeleLocalFactorLinearEquiv K S).apply_symm_apply (x, 0)
    have hp := congrArg Prod.fst he
    exact hp
  have hb : originalSupportedIdeleBaseChangeMap K K S S
      (fun w hw hv => hw ((hSS w).mpr hv)) y.toMul = y.toMul := by
    apply Subtype.ext
    apply originalIdeleBaseChangeMap_injective K K
    exact originalIdeleBaseChangeMap_tower K K K y.toMul.val
  exact (congrArg (originalSPlaceBaseChange K K S S hSS) hy.symm).trans
    ((originalSPlaceBaseChange_projection K K S S hSS y).trans
      ((congrArg (fun z => (supportedIdeleLocalFactorLinearEquiv K S (Additive.ofMul z)).1) hb).trans hy))

end
end Dubon2026
