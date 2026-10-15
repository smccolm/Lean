import Dubon2026.FiniteGaloisUnramifiedSup
import Dubon2026.UnramifiedUnionFiniteFieldCriterion
import Mathlib.FieldTheory.Normal.Closure

/-! # Unramifiedness of the original finite normal closure

The localized-unit root step in DUB-17's global duality route needs roots in
the actual unramified Galois union, not only nonnormal unramified extensions.
Transport through integral closures and the existing compositum theorem give
the required normal-closure step for the original primewise condition.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain IntermediateField
open scoped NumberField

variable {K L M Ω : Type*} [Field K] [Field L] [Field M] [Field Ω]
  [NumberField K] [NumberField L] [NumberField M]
  [Algebra K L] [Algebra K M]

/-- A genuine base-field equivalence transports the original primewise
unramifiedness condition, through the actual localized integral closures. -/
theorem numberField_unramified_of_algEquiv (a : 𝓞 K) (ha : a ≠ 0) (e : L ≃ₐ[K] M)
    (hL : ∀ w : HeightOneSpectrum (𝓞 L), algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1) :
    ∀ w : HeightOneSpectrum (𝓞 M), algebraMap (𝓞 K) (𝓞 M) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  let R := originalLocalizedIntegers K a ha
  let S := originalLocalizedIntegers L (algebraMap (𝓞 K) (𝓞 L) a)
    (originalIntegerMap_ne_zero (L := L) a ha)
  let T := originalLocalizedIntegers M (algebraMap (𝓞 K) (𝓞 M) a)
    (originalIntegerMap_ne_zero (L := M) a ha)
  letI : Algebra R S := (originalLocalizedIntegersMap (L := L) a ha).toRingHom.toAlgebra
  letI : Algebra R T := (originalLocalizedIntegersMap (L := M) a ha).toRingHom.toAlgebra
  letI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower R T M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower R K M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hS := canonicalLocalizedIntegerAlgebra_data (L := L) a ha
  have hT := canonicalLocalizedIntegerAlgebra_data (L := M) a ha
  letI : IsIntegralClosure S R L := hS.2.1
  letI : IsIntegralClosure T R M := hT.2.1
  letI : Algebra.FormallyUnramified R S := hS.2.2.mpr hL
  let j : S ≃ₐ[R] T := (IsIntegralClosure.equiv R S L (integralClosure R L)).trans
    ((e.restrictScalars R).mapIntegralClosure.trans
      (IsIntegralClosure.equiv R (integralClosure R M) M T))
  exact hT.2.2.mp (Algebra.FormallyUnramified.of_equiv j)

variable [Algebra K Ω]

/-- The literal supremum of two actual finite intermediate fields preserves
the original primewise unramifiedness condition without a normality premise. -/
theorem intermediateField_sup_unramified (a : 𝓞 K) (ha : a ≠ 0)
    (E F : IntermediateField K Ω) [FiniteDimensional K E] [FiniteDimensional K F]
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), algebraMap (𝓞 K) (𝓞 E) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1)
    (hF : ∀ w : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 K) (𝓞 F) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1) :
    ∀ w : HeightOneSpectrum (𝓞 (E ⊔ F : IntermediateField K Ω)),
      algebraMap (𝓞 K) (𝓞 (E ⊔ F : IntermediateField K Ω)) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  let H := E ⊔ F
  letI : NumberField E := NumberField.of_module_finite K E
  letI : NumberField F := NumberField.of_module_finite K F
  letI : NumberField H := NumberField.of_module_finite K H
  let f := IntermediateField.inclusion (show E ≤ H from le_sup_left)
  let g := IntermediateField.inclusion (show F ≤ H from le_sup_right)
  letI : Algebra E H := f.toRingHom.toAlgebra
  letI : Algebra F H := g.toRingHom.toAlgebra
  letI : IsScalarTower K E H := IsScalarTower.of_algHom f
  letI : IsScalarTower K F H := IsScalarTower.of_algHom g
  exact numberField_unramified_compositum (L := E) (M := F) (Ω := H) a ha hE hF
    (intermediateField_sup_inclusion_ranges E F)

/-- A finite family of actual unramified intermediate fields has an unramified
literal supremum. The existing binary compositum theorem supplies the induction. -/
theorem intermediateField_finite_iSup_unramified {ι : Type*} [Finite ι]
    (a : 𝓞 K) (ha : a ≠ 0) (E : ι → IntermediateField K Ω)
    [∀ i, FiniteDimensional K (E i)]
    (hE : ∀ i, ∀ w : HeightOneSpectrum (𝓞 (E i)),
      algebraMap (𝓞 K) (𝓞 (E i)) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1) :
    ∀ w : HeightOneSpectrum (𝓞 (⨆ i, E i : IntermediateField K Ω)),
      algebraMap (𝓞 K) (𝓞 (⨆ i, E i : IntermediateField K Ω)) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hs (s : Finset ι) :
      ∀ w : HeightOneSpectrum (𝓞 (⨆ i ∈ s, E i : IntermediateField K Ω)),
        algebraMap (𝓞 K) (𝓞 (⨆ i ∈ s, E i : IntermediateField K Ω)) a ∉ w.asIdeal →
          (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
    induction s using Finset.induction_on with
    | empty =>
      rw [show (⨆ i ∈ (∅ : Finset ι), E i) = ⊥ by simp]
      letI : NumberField (⊥ : IntermediateField K Ω) := NumberField.of_module_finite K _
      intro w _
      exact numberField_ramificationIdx_one_of_baseEquiv (botEquiv K Ω).symm w
    | @insert i s _ ih =>
      rw [Finset.iSup_insert]
      exact intermediateField_sup_unramified a ha (E i) (⨆ j ∈ s, E j) (hE i) ih
  have h := hs Finset.univ
  rw [show (⨆ i ∈ (Finset.univ : Finset ι), E i) = ⨆ i, E i by simp] at h
  exact h

omit [NumberField K] in
/-- Original primewise unramifiedness composes in an actual number-field tower.
This transfers the localized-unit root extension over a finite arithmetic stage
back to the original base field. -/
theorem numberField_unramified_tower [Algebra L M] [IsScalarTower K L M]
    (a : 𝓞 K)
    (hL : ∀ w : HeightOneSpectrum (𝓞 L), algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1)
    (hM : ∀ w : HeightOneSpectrum (𝓞 M),
      algebraMap (𝓞 L) (𝓞 M) (algebraMap (𝓞 K) (𝓞 L) a) ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 L)).ramificationIdx w.asIdeal = 1) :
    ∀ w : HeightOneSpectrum (𝓞 M), algebraMap (𝓞 K) (𝓞 M) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  intro w hw
  let v := w.under (𝓞 L)
  have hv : algebraMap (𝓞 K) (𝓞 L) a ∉ v.asIdeal := by
    intro h
    apply hw
    change algebraMap (𝓞 L) (𝓞 M) (algebraMap (𝓞 K) (𝓞 L) a) ∈ w.asIdeal at h
    simpa only [← IsScalarTower.algebraMap_apply] using h
  have hw' : algebraMap (𝓞 L) (𝓞 M) (algebraMap (𝓞 K) (𝓞 L) a) ∉ w.asIdeal := by
    simpa only [← IsScalarTower.algebraMap_apply] using hw
  letI : w.asIdeal.LiesOver v.asIdeal :=
    inferInstanceAs (w.asIdeal.LiesOver (w.asIdeal.under (𝓞 L)))
  have hM' : v.asIdeal.ramificationIdx w.asIdeal = 1 := hM w hw'
  have h := Ideal.ramificationIdx_algebra_tower' (v.asIdeal.under (𝓞 K)) v.asIdeal w.asIdeal
  rw [hL v hv, hM', one_mul] at h
  change ((w.asIdeal.under (𝓞 L)).under (𝓞 K)).ramificationIdx w.asIdeal = 1 at h
  simpa only [Ideal.under_under] using h

variable [FiniteDimensional K L]

/-- The actual finite normal closure of an original unramified extension is
unramified at the same original finite primes. No normal-closure premise is assumed. -/
theorem numberField_normalClosure_unramified (a : 𝓞 K) (ha : a ≠ 0)
    (hL : ∀ w : HeightOneSpectrum (𝓞 L), algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1) :
    ∀ w : HeightOneSpectrum (𝓞 (normalClosure K L Ω)),
      algebraMap (𝓞 K) (𝓞 (normalClosure K L Ω)) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  letI (f : L →ₐ[K] Ω) : FiniteDimensional K f.fieldRange :=
    f.toLinearMap.finiteDimensional_range
  letI (f : L →ₐ[K] Ω) : NumberField f.fieldRange := NumberField.of_module_finite K _
  exact intermediateField_finite_iSup_unramified a ha (fun f : L →ₐ[K] Ω => f.fieldRange)
    (fun f => numberField_unramified_of_algEquiv a ha (AlgEquiv.ofInjectiveField f) hL)

/-- In a normal ambient extension, every actual finite intermediate field belongs
to the original unramified Galois union exactly when its original primes are
unramified outside the exceptional integer. The containing finite Galois stage
is constructed using its proved unramified normal closure. -/
theorem originalUnramifiedUnion_finite_le_iff [Normal K Ω]
    (a : 𝓞 K) (ha : a ≠ 0) (E : IntermediateField K Ω) [FiniteDimensional K E] :
    E ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ↔
      ∀ w : HeightOneSpectrum (𝓞 E), algebraMap (𝓞 K) (𝓞 E) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsGalois K (normalClosure K E Ω) := {}
  constructor
  · exact originalUnramifiedUnion_ambient_finite_ramification a ha E
  · intro hE
    let N : FiniteGaloisIntermediateField K Ω := ⟨normalClosure K E Ω⟩
    have hN := numberField_normalClosure_unramified (Ω := Ω) a ha hE
    exact (le_normalClosure E).trans (originalUnramifiedGaloisStage_le_union a ⟨N, hN⟩)

end
end Dubon2026
