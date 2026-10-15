import Dubon2026.CanonicalLocalizedIntegerAlgebras
import Dubon2026.MonicSeparableAdjoinRootEtale
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Unramified.Dedekind
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # The actual finite étale root algebra of a localized integer unit

For the S-unit coefficient step in DUB-17's global duality route, adjoining a
qth root of an actual localized unit is finite étale when q divides the
exceptional integer. This reuses the pinned separability theorem and the
existing root-algebra comparison. Containment in the original unramified
Galois union still requires the field and normal-closure comparisons.
-/

namespace Dubon2026
noncomputable section
open Polynomial
open scoped NumberField

variable (K : Type) [Field K] [NumberField K]
  (a : 𝓞 K) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]

omit [Fact q.Prime] in
/-- The actual auxiliary prime is a unit in the original localized integer ring. -/
theorem originalLocalizedIntegers_coefficientPrime_isUnit (hqa : (q : 𝓞 K) ∣ a) :
    IsUnit (q : originalLocalizedIntegers K a ha) := by
  simpa only [map_natCast] using
    (IsLocalization.Away.isUnit_of_dvd (S := originalLocalizedIntegers K a ha) a hqa)

/-- The literal quotient polynomial adjoins a root of the prescribed original localized unit. -/
abbrev OriginalLocalizedUnitKummerAlgebra (u : (originalLocalizedIntegers K a ha)ˣ) :=
  AdjoinRoot (X ^ q - C u.val)

/-- The original unit-root quotient is finite and étale, with both properties derived. -/
theorem originalLocalizedUnitKummerAlgebra_finite_etale (hqa : (q : 𝓞 K) ∣ a)
    (u : (originalLocalizedIntegers K a ha)ˣ) :
    Module.Finite (originalLocalizedIntegers K a ha) (OriginalLocalizedUnitKummerAlgebra K a ha q u) ∧
      Algebra.Etale (originalLocalizedIntegers K a ha) (OriginalLocalizedUnitKummerAlgebra K a ha q u) := by
  have hq : q.Prime := Fact.out
  have hf := monic_X_pow_sub_C u.val hq.ne_zero
  exact ⟨hf.finite_adjoinRoot,
    monic_separable_adjoinRoot_etale _ hf
      (separable_X_pow_sub_C_unit u
        (originalLocalizedIntegers_coefficientPrime_isUnit K a ha q hqa))⟩

/-- The original adjoined element is a unit and its qth power is the original coefficient image. -/
theorem originalLocalizedUnitKummerAlgebra_root
    (u : (originalLocalizedIntegers K a ha)ˣ) :
    let f : (originalLocalizedIntegers K a ha)[X] := X ^ q - C u.val
    (AdjoinRoot.root f) ^ q = algebraMap _ (AdjoinRoot f) u.val ∧
      IsUnit (AdjoinRoot.root f) := by
  dsimp only
  let f : (originalLocalizedIntegers K a ha)[X] := X ^ q - C u.val
  have he : (AdjoinRoot.root f) ^ q = algebraMap _ (AdjoinRoot f) u.val := by
    have h := AdjoinRoot.aeval_eq (f := f) f
    rw [AdjoinRoot.mk_self] at h
    exact sub_eq_zero.mp (by simpa only [f, map_sub, map_pow, aeval_X, aeval_C] using h)
  refine ⟨he, ?_⟩
  apply (isUnit_pow_iff (Fact.out : q.Prime).ne_zero).mp
  rw [he]
  exact u.isUnit.map (algebraMap _ (AdjoinRoot f))

variable (Ω : Type) [Field Ω] [Algebra K Ω]

/-- The localized coefficient map is the original number-field embedding on literal fractions. -/
local instance localizedUnitAmbientAlgebra : Algebra (originalLocalizedIntegers K a ha) Ω :=
  (originalLocalizedIntegers K a ha).toAlgebra

/-- The actual localized and field coefficient maps form their original scalar tower. -/
local instance localizedUnitAmbientTower :
    @IsScalarTower (originalLocalizedIntegers K a ha) K Ω
      (inferInstance : Algebra (originalLocalizedIntegers K a ha) K).toSMul
      (inferInstance : Algebra K Ω).toSMul
      (inferInstance : Algebra (originalLocalizedIntegers K a ha) Ω).toSMul :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (u : (originalLocalizedIntegers K a ha)ˣ) (β : Ω)
  (hβ : β ^ q = algebraMap (originalLocalizedIntegers K a ha) Ω u.val)

/-- Evaluate the literal unit-root quotient at an actual root in the original ambient field. -/
def originalLocalizedUnitKummerMap :
    OriginalLocalizedUnitKummerAlgebra K a ha q u →ₐ[originalLocalizedIntegers K a ha] Ω :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId (originalLocalizedIntegers K a ha) Ω) β
    (by simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, Algebra.ofId_apply] using
      sub_eq_zero.mpr hβ)

omit [Fact q.Prime] in
/-- Evaluation sends the original adjoined root to precisely the prescribed field root. -/
theorem originalLocalizedUnitKummerMap_root :
    originalLocalizedUnitKummerMap K a ha q Ω u β hβ (AdjoinRoot.root _) = β := by
  simp only [originalLocalizedUnitKummerMap, AdjoinRoot.liftAlgHom_root]

/-- The actual field image is finite and formally unramified over the original localized
integer ring, and is a Dedekind domain. No integral-closure or ramification premise is assumed. -/
theorem originalLocalizedUnitKummerMap_range_properties (hqa : (q : 𝓞 K) ∣ a) :
    let I := (originalLocalizedUnitKummerMap K a ha q Ω u β hβ).range
    Module.Finite (originalLocalizedIntegers K a ha) I ∧
      Algebra.FormallyUnramified (originalLocalizedIntegers K a ha) I ∧ IsDedekindDomain I := by
  let R := originalLocalizedIntegers K a ha
  let f := originalLocalizedUnitKummerMap K a ha q Ω u β hβ
  let I := f.range
  have h := originalLocalizedUnitKummerAlgebra_finite_etale K a ha q hqa u
  letI := h.1
  letI := h.2
  letI : Module.Finite R I := Module.Finite.of_surjective
    f.rangeRestrict.toLinearMap f.rangeRestrict_surjective
  letI : Algebra.FormallyUnramified R I :=
    Algebra.FormallyUnramified.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  letI : IsDedekindDomain R := IsLocalization.isDedekindDomain (𝓞 K)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ha) R
  exact ⟨inferInstance, inferInstance, isDedekindDomain.of_formallyUnramified R I⟩

/-- The actual root image's fraction field embeds in the prescribed ambient field. -/
def originalLocalizedUnitKummerFractionMap :
    FractionRing (originalLocalizedUnitKummerMap K a ha q Ω u β hβ).range →ₐ[
      originalLocalizedIntegers K a ha] Ω :=
  IsFractionRing.liftAlgHom
    (g := (originalLocalizedUnitKummerMap K a ha q Ω u β hβ).range.val) Subtype.val_injective

omit [Fact q.Prime] in
/-- If the actual root generates the ambient field over the original number field,
the original root image has precisely that ambient fraction field. -/
theorem originalLocalizedUnitKummerFractionMap_surjective
    (hgen : IntermediateField.adjoin K {β} = ⊤) :
    Function.Surjective (originalLocalizedUnitKummerFractionMap K a ha q Ω u β hβ) := by
  let R := originalLocalizedIntegers K a ha
  let I := (originalLocalizedUnitKummerMap K a ha q Ω u β hβ).range
  let j := originalLocalizedUnitKummerFractionMap K a ha q Ω u β hβ
  letI : IsFractionRing R K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (.powers a) R K
  have hbase (k : K) : algebraMap K Ω k ∈ j.toRingHom.fieldRange := by
    obtain ⟨r, s, _, rfl⟩ := IsFractionRing.div_surjective R k
    rw [map_div₀, ← IsScalarTower.algebraMap_apply (originalLocalizedIntegers K a ha) K Ω,
      ← IsScalarTower.algebraMap_apply (originalLocalizedIntegers K a ha) K Ω]
    exact j.toRingHom.fieldRange.div_mem
      ⟨algebraMap R (FractionRing I) r, j.commutes r⟩
      ⟨algebraMap R (FractionRing I) s, j.commutes s⟩
  let E : IntermediateField K Ω :=
    { j.toRingHom.fieldRange with algebraMap_mem' := hbase }
  have hroot : β ∈ E := by
    let z : I := ⟨β, ⟨AdjoinRoot.root _, originalLocalizedUnitKummerMap_root K a ha q Ω u β hβ⟩⟩
    exact ⟨algebraMap I (FractionRing I) z, IsFractionRing.lift_algebraMap Subtype.val_injective z⟩
  have hE : E = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hroot)
  exact RingHom.fieldRange_eq_top_iff.mp (congrArg IntermediateField.toSubfield hE)

/-- The actual unramified root image is the integral closure in its generated field.
Thus normalization adds no unproved ramification hypothesis. -/
theorem originalLocalizedUnitKummerMap_isIntegralClosure
    (hqa : (q : 𝓞 K) ∣ a) (hgen : IntermediateField.adjoin K {β} = ⊤) :
    IsIntegralClosure (originalLocalizedUnitKummerMap K a ha q Ω u β hβ).range
      (originalLocalizedIntegers K a ha) Ω := by
  let R := originalLocalizedIntegers K a ha
  let I := (originalLocalizedUnitKummerMap K a ha q Ω u β hβ).range
  let j := originalLocalizedUnitKummerFractionMap K a ha q Ω u β hβ
  have h := originalLocalizedUnitKummerMap_range_properties K a ha q Ω u β hβ hqa
  letI := h.1
  letI := h.2.2
  letI : IsIntegralClosure I R (FractionRing I) :=
    IsIntegralClosure.of_isIntegrallyClosed I R (FractionRing I)
  refine { algebraMap_injective := Subtype.val_injective, isIntegral_iff := ?_ }
  intro x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := originalLocalizedUnitKummerFractionMap_surjective K a ha q Ω u β hβ hgen x
    have hy := (isIntegral_algHom_iff j j.injective).mp hx
    obtain ⟨z, hz⟩ := (IsIntegralClosure.isIntegral_iff (A := I) (R := R)
      (B := FractionRing I)).mp hy
    refine ⟨z, ?_⟩
    exact (IsFractionRing.lift_algebraMap Subtype.val_injective z).symm.trans (congrArg j hz)
  · rintro ⟨z, rfl⟩
    exact IsIntegral.map_of_comp_eq (RingHom.id R) I.val.toRingHom
      (by ext r; rfl) (IsIntegral.of_finite R z)

include hβ in
/-- The original number-field extension generated by the prescribed unit root is
unramified at every original finite prime away from the exceptional integer.
Its integral closure and local ramification indices are the original ones. -/
theorem originalLocalizedUnitKummer_unramifiedAway [NumberField Ω]
    (hqa : (q : 𝓞 K) ∣ a) (hgen : IntermediateField.adjoin K {β} = ⊤) :
    ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 Ω),
      algebraMap (𝓞 K) (𝓞 Ω) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  let R := originalLocalizedIntegers K a ha
  let S := originalLocalizedIntegers Ω (algebraMap (𝓞 K) (𝓞 Ω) a)
    (originalIntegerMap_ne_zero (L := Ω) a ha)
  let I := (originalLocalizedUnitKummerMap K a ha q Ω u β hβ).range
  letI : Algebra R S := (originalLocalizedIntegersMap (L := Ω) a ha).toRingHom.toAlgebra
  letI : @IsScalarTower R S Ω (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S Ω).toSMul (inferInstance : Algebra R Ω).toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hS := canonicalLocalizedIntegerAlgebra_data (L := Ω) a ha
  letI : IsIntegralClosure S R Ω := hS.2.1
  letI : IsIntegralClosure I R Ω :=
    originalLocalizedUnitKummerMap_isIntegralClosure K a ha q Ω u β hβ hqa hgen
  letI : Algebra.FormallyUnramified R I :=
    (originalLocalizedUnitKummerMap_range_properties K a ha q Ω u β hβ hqa).2.1
  exact hS.2.2.mp (Algebra.FormallyUnramified.of_equiv (IsIntegralClosure.equiv R I Ω S))

end
end Dubon2026
