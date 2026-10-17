import Dubon2026.OriginalPrescribedNormInertiaField
import Dubon2026.OriginalFixedFieldInertiaUnramified
import Dubon2026.HeightOnePrimeLifting

/-! # Actual prescribed norm fields with the required ramification support

Prime lifting and the proved inertia containment give index one at every
fixed-field prime outside the original support. The field has exactly
the prescribed literal class-norm submodule. This closes the finite
support-control obligation in DUB-17; constructing and placing the
required Kummer stage remains separate.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField IsMulCommutative
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K L w ∈ S)

include hT hST in
/-- An actual normalized abelian prime-power stage realizes every
submodule containing its norm range and the base outside-unit classes
as the exact norm range of a normal field unramified outside the support. -/
theorem originalFullClass_exists_prescribed_support_norm_field
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))
    (hsys : OriginalFiniteNormalizedClassSystem K L)
    (U : Submodule ℤ (Additive (OriginalNumberFieldIdeleClassGroup K)))
    (hU : (originalIdeleClassNormLinear K L).range ≤ U)
    (hOutside : ∀ z, (originalOutsideIdeleClassRepHom K K S hS).hom z ∈ U) :
    ∃ (H : Subgroup Gal(L/K)) (hH : H.Normal),
      letI : H.Normal := hH
      (originalIdeleClassNormLinear K (IntermediateField.fixedField H)).range = U ∧
      ∀ q : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)),
        originalFinitePrimeBelow K (IntermediateField.fixedField H) q ∉ S →
        (q.asIdeal.under (𝓞 K)).ramificationIdx q.asIdeal = 1 := by
  obtain ⟨H, hH, hNorm, hInertia⟩ := originalFullClass_exists_prescribed_norm_inertia_subfield
    K L S T hS hT hST p hG hsys U hU hOutside
  letI : H.Normal := hH
  refine ⟨H, hH, hNorm, ?_⟩
  intro q hq
  let F := IntermediateField.fixedField H
  let v := originalFinitePrimeBelow K F q
  letI : q.asIdeal.LiesOver v.asIdeal := originalFinitePrimeBelow_liesOver K F q
  obtain ⟨w, hw⟩ := heightOnePrime_exists_liesOver (S := 𝓞 L) q
  letI : w.asIdeal.LiesOver q.asIdeal := hw
  letI : w.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans w.asIdeal q.asIdeal v.asIdeal
  have hBelow : originalFinitePrimeBelow K L w = v :=
    HeightOneSpectrum.ext (w.asIdeal.over_def v.asIdeal).symm
  have hwT : w ∉ T := by
    intro h
    apply hq
    change v ∈ S
    rw [← hBelow]
    exact (hST w).mp h
  exact originalFixedField_ramification_one_of_inertia_le w H (hInertia w hwT) v q

/-- The actual inverse-image support is finite and stable, so no upper
support or support-comparison premise is needed to construct the field. -/
theorem originalFullClass_exists_prescribed_support_norm_field_of_base_support
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))
    (hsys : OriginalFiniteNormalizedClassSystem K L)
    (U : Submodule ℤ (Additive (OriginalNumberFieldIdeleClassGroup K)))
    (hU : (originalIdeleClassNormLinear K L).range ≤ U)
    (hOutside : ∀ z, (originalOutsideIdeleClassRepHom K K S hS).hom z ∈ U) :
    ∃ (H : Subgroup Gal(L/K)) (hH : H.Normal),
      letI : H.Normal := hH
      (originalIdeleClassNormLinear K (IntermediateField.fixedField H)).range = U ∧
      ∀ q : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)),
        originalFinitePrimeBelow K (IntermediateField.fixedField H) q ∉ S →
        (q.asIdeal.under (𝓞 K)).ramificationIdx q.asIdeal = 1 := by
  let hFin := originalFinitePrimeBelow_preimage_finite K L (S : Set _) S.finite_toSet
  let T' := hFin.toFinset
  have hST' (w : HeightOneSpectrum (𝓞 L)) :
      w ∈ T' ↔ originalFinitePrimeBelow K L w ∈ S := hFin.mem_toFinset
  have hT' (σ : Gal(L/K)) (w : HeightOneSpectrum (𝓞 L)) :
      w ∈ T' ↔ numberFieldGaloisPlaceEquiv K L σ w ∈ T' := by
    rw [hST', hST', originalFinitePrimeBelow_galois]
  exact originalFullClass_exists_prescribed_support_norm_field
    K L S T' hS hT' hST' p hG hsys U hU hOutside

end
end Dubon2026
