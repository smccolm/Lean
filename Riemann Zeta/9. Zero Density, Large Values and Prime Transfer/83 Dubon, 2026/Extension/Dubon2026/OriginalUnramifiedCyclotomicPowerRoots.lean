import Dubon2026.CyclotomicUnramifiedPrimes
import Dubon2026.UnramifiedGaloisStageUnion
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Actual prime-power cyclotomic roots in the original unramified union

DUB-17 cyclic splitting needs arbitrarily large auxiliary-prime power
conductors with the original fixed exceptional integer. Prime-ideal
radicality removes the unnecessary conductor-divisibility restriction. -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {Ω : Type*} [Field Ω] [CharZero Ω] [Algebra ℚ Ω]

omit [CharZero Ω] in
/-- The actual primitive root belongs to the original rational unramified union when the base of its power conductor divides the original exceptional integer. The stage is constructed from that same root. -/
theorem originalQUnramifiedUnion_mem_of_powerRoot
    (a : 𝓞 ℚ) (q r : ℕ) [NeZero q] (hqa : (q : 𝓞 ℚ) ∣ a)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (q ^ r)) :
    ζ ∈ originalUnramifiedGaloisUnion (Ω := Ω) a := by
  let F := IntermediateField.adjoin ℚ ({ζ} : Set Ω)
  letI : Algebra ℚ F := F.algebra'
  letI : IsCyclotomicExtension {q ^ r} ℚ F :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin (q ^ r) ℚ Ω F hζ).mpr rfl
  letI : FiniteDimensional ℚ F := IsCyclotomicExtension.finiteDimensional {q ^ r} ℚ F
  letI : IsGalois ℚ F := IsCyclotomicExtension.isGalois {q ^ r} ℚ F
  let L : FiniteGaloisIntermediateField ℚ Ω := ⟨F⟩
  letI : Algebra ℚ L := L.algebra'
  letI : NumberField L := NumberField.of_module_finite ℚ L
  have hcyc : @IsCyclotomicExtension {q ^ r} ℚ L _ _ L.algebra' :=
    inferInstanceAs (@IsCyclotomicExtension {q ^ r} ℚ F _ _ F.algebra')
  have hrat : (L.algebra' : Algebra ℚ L) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  letI : @IsCyclotomicExtension {q ^ r} ℚ L _ _ DivisionRing.toRatAlgebra := hrat ▸ hcyc
  have hstage : ∀ w : HeightOneSpectrum (𝓞 L),
      algebraMap (𝓞 ℚ) (𝓞 L) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1 := by
    intro w hw
    have hm : (q ^ r : 𝓞 L) ∉ w.asIdeal := by
      intro hm
      have hq : (q : 𝓞 L) ∈ w.asIdeal := w.isPrime.mem_of_pow_mem r hm
      obtain ⟨b, hb⟩ := hqa
      apply hw
      rw [hb, map_mul, map_natCast]
      exact w.asIdeal.mul_mem_right (algebraMap (𝓞 ℚ) (𝓞 L) b) hq
    have h := rationalCyclotomic_originalBase_ramificationIdx_one (q ^ r) w (by simpa only [Nat.cast_pow] using hm)
    let P : Algebra ℚ L → Prop := fun inst =>
      letI := inst
      (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1
    have hP : P DivisionRing.toRatAlgebra := h
    change P L.algebra'
    exact hrat.symm ▸ hP
  apply originalUnramifiedGaloisStage_le_union a ⟨L, hstage⟩
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)

/-- A separably closed original ambient field supplies an actual primitive root in the constructed rational unramified union for every power conductor whose base divides the fixed exceptional integer. -/
theorem originalQUnramifiedUnion_exists_powerRoot [IsSepClosed Ω]
    (a : 𝓞 ℚ) (q r : ℕ) [NeZero q] (hqa : (q : 𝓞 ℚ) ∣ a) :
    ∃ ζ : originalUnramifiedGaloisUnion (Ω := Ω) a, IsPrimitiveRoot ζ (q ^ r) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (q ^ r)
  refine ⟨⟨ζ, originalQUnramifiedUnion_mem_of_powerRoot a q r hqa ζ hζ⟩, ?_⟩
  exact IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ

end
end Dubon2026
