import Dubon2026.SourceCurvePrimePlaces
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison -> exact constant-field place extension. A proper valuation ring containing the scalar
field on a finite one-variable function field is an actual discrete place.
The original curve already supplies the transcendental finite coordinate;
the algebraic-coordinate branch of the external result is unnecessary here.
Existing integral-closure prime places and native valuation-ring maximality
are reused. This removes discreteness as a premise of the place construction.
Adapted from S_AlgebraicCurve_Place_exists_of_valuationSubring,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section
open IsDedekindDomain
open scoped IntermediateField.algebraAdjoinAdjoin

section Crux

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
variable (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
variable (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hA : A ≠ ⊤)
variable (hx : Transcendental K x) (hxA : x ∈ A)

local notation "Kx" => Algebra.adjoin K (Set.singleton x : Set F)
local notation "Kxfield" => IntermediateField.adjoin K (Set.singleton x : Set F)

omit [CharZero K] [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] in
include hx in
private theorem isDedekindDomain_Kx : IsDedekindDomain (Kx) := by
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hrange : (Polynomial.aeval x : Polynomial K →ₐ[K] F).range = Kx :=
    (Algebra.adjoin_singleton_eq_range_aeval K x).symm
  let e : Polynomial K ≃ₐ[K] Kx :=
    (AlgEquiv.ofInjective _ hinj).trans (Subalgebra.equivOfEq _ _ hrange)
  haveI : IsPrincipalIdealRing (Kx) :=
    IsPrincipalIdealRing.of_surjective (e : Polynomial K →+* Kx) e.surjective
  infer_instance

include hx in
private theorem isDedekindDomain_integralClosure :
    IsDedekindDomain (integralClosure (Kx) F) := by
  haveI := isDedekindDomain_Kx x hx
  haveI : Algebra.IsSeparable (Kxfield) F := Algebra.IsSeparable.of_integral _ _
  exact integralClosure.isDedekindDomain (Kx) (Kxfield) F

omit [CharZero K] in
private theorem isFractionRing_integralClosure :
    IsFractionRing (integralClosure (Kx) F) F :=
  integralClosure.isFractionRing_of_finite_extension (A := Kx) (Kxfield) F

omit [CharZero K] [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] in
include hxA hAK in
private theorem Kx_le_A : (Kx).toSubring ≤ A.toSubring := by
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem z hz => obtain rfl : z = x := hz; exact hxA
  | algebraMap a => exact hAK a
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

private scoped instance : IsFractionRing (A : ValuationSubring F).toSubring F := by
  rw [← A.integer_valuation]; infer_instance

private scoped instance : IsFractionRing (A : ValuationSubring F) F :=
  inferInstanceAs (IsFractionRing A.toSubring F)

omit [CharZero K] [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] in
include hxA hAK in
private theorem integralClosure_Kx_le_A :
    (integralClosure (Kx) F).toSubring ≤ A.toSubring := by
  intro y hy
  have hyI : IsIntegral (Kx) y := hy
  letI : Algebra (Kx) A :=
    (Subring.inclusion (Kx_le_A x A hAK hxA)).toAlgebra
  haveI : IsScalarTower (Kx) A F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hyA : IsIntegral A y := hyI.tower_top
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff F).mp inferInstance hyA
  exact hz ▸ z.2

omit [CharZero K] [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] in
include hxA hAK in
private theorem inv_mem_of_notMem_maximalIdeal {b : integralClosure (Kx) F}
    (hb : Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA) b
        ∉ IsLocalRing.maximalIdeal A) :
    ((b : F))⁻¹ ∈ A := by
  have hbA : (b : F) ∈ A := integralClosure_Kx_le_A x A hAK hxA b.2
  have hbU : IsUnit (⟨(b : F), hbA⟩ : A) := IsLocalRing.notMem_maximalIdeal.mp hb
  obtain ⟨u, hu⟩ := hbU
  have hcoe : (((u⁻¹ : Aˣ) : A) : F) * (b : F) = 1 := by
    have h1 : ((u⁻¹ : Aˣ) : A) * ⟨(b : F), hbA⟩ = 1 := by rw [← hu]; exact u.inv_mul
    have := congrArg (Subtype.val : A → F) h1; simpa using this
  exact (eq_inv_of_mul_eq_one_left hcoe) ▸ ((u⁻¹ : Aˣ) : A).2

omit [CharZero K] in
include hxA hAK hA in
private theorem idealOfA_ne_bot :
    (IsLocalRing.maximalIdeal A).comap
        (Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA)) ≠ ⊥ := by
  haveI : IsFractionRing (integralClosure (Kx) F) F := isFractionRing_integralClosure x
  intro hP
  apply hA
  rw [eq_top_iff]
  intro y _
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := integralClosure (Kx) F) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have haA : (a : F) ∈ A := integralClosure_Kx_le_A x A hAK hxA a.2
  have hbm : Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA) b
      ∉ IsLocalRing.maximalIdeal A := by
    intro hbm
    have hmem : b ∈ (IsLocalRing.maximalIdeal A).comap
        (Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA)) := hbm
    rw [hP, Ideal.mem_bot] at hmem
    exact hb0 hmem
  rw [← hab, div_eq_mul_inv]
  exact mul_mem haA (inv_mem_of_notMem_maximalIdeal x A hAK hxA hbm)

omit [CharZero K] [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] in
include hxA hAK in
private theorem place_of_idealOfA_le (P : HeightOneSpectrum (integralClosure (Kx) F))
    [IsDedekindDomain (integralClosure (Kx) F)] [IsFractionRing (integralClosure (Kx) F) F]
    (hP : P.asIdeal = (IsLocalRing.maximalIdeal A).comap
        (Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA))) :
    (Place.ofHeightOneSpectrum (K := K) (F := F) P).toValuationSubring ≤ A := by
  change (P.valuation F).valuationSubring ≤ A
  rw [    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rintro y ⟨a, s, hs, rfl⟩
  have haA : (a : F) ∈ A := integralClosure_Kx_le_A x A hAK hxA a.2
  have hsm : Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA) s
      ∉ IsLocalRing.maximalIdeal A := by
    intro h
    exact hs (hP ▸ h : s ∈ P.asIdeal)
  exact mul_mem haA (inv_mem_of_notMem_maximalIdeal x A hAK hxA hsm)

include hx hxA hAK hA in
private theorem exists_place_of_mem :
    ∃ v : Place K F, v.toValuationSubring = A := by
  haveI := isDedekindDomain_integralClosure x hx
  haveI : IsFractionRing (integralClosure (Kx) F) F := isFractionRing_integralClosure x
  let P : HeightOneSpectrum (integralClosure (Kx) F) :=
    ⟨(IsLocalRing.maximalIdeal A).comap
        (Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA)),
      inferInstance, idealOfA_ne_bot x A hAK hA hxA⟩
  let V : Place K F := Place.ofHeightOneSpectrum P
  have hVA : V.toValuationSubring ≤ A := place_of_idealOfA_le x A hAK hxA P rfl
  exact ⟨V, ValuationSubring.eq_of_le_of_ne_top _ hVA hA⟩

end Crux

theorem exists_place_of_finite_coordinate
    {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hA : A ≠ ⊤) :
    ∃ v : Place K F, v.toValuationSubring = A := by
  rcases A.mem_or_inv_mem x with hxA | hxiA
  · exact exists_place_of_mem x A hAK hA hx hxA
  · have hxinv : Transcendental K x⁻¹ := by
      rw [Transcendental, IsAlgebraic.inv_iff]
      exact hx
    have hadj : IntermediateField.adjoin K ({x⁻¹} : Set F) =
        IntermediateField.adjoin K ({x} : Set F) := by
      refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
        (IntermediateField.adjoin_le_iff.mpr ?_)
      · intro z hz
        rw [show z = x⁻¹ from hz]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self K x)
      · intro z hz
        rw [show z = x from hz]
        have h : x⁻¹⁻¹ ∈ IntermediateField.adjoin K ({x⁻¹} : Set F) :=
          inv_mem (IntermediateField.mem_adjoin_simple_self K x⁻¹)
        rwa [inv_inv] at h
    haveI : FiniteDimensional (IntermediateField.adjoin K ({x⁻¹} : Set F)) F := by
      rw [hadj]
      infer_instance
    exact exists_place_of_mem x⁻¹ A hAK hA hxinv hxiA

end
end Dubon2026.SourceCurve.ConstantField
