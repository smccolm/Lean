import Dubon2026.CyclotomicUnramifiedPrimes
import Dubon2026.UnramifiedGaloisStageUnion
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Actual cyclotomic roots inside the original rational unramified union -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {Ω : Type*} [Field Ω] [CharZero Ω] [Algebra ℚ Ω]

omit [CharZero Ω] in
/-- The actual primitive root belongs to the original rational unramified union when its conductor divides the original exceptional integer. The finite cyclotomic stage is constructed from that same root. -/
theorem originalQUnramifiedUnion_mem_of_primitiveRoot
    (a : 𝓞 ℚ) (m : ℕ) [NeZero m] (hma : (m : 𝓞 ℚ) ∣ a)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ m) :
    ζ ∈ originalUnramifiedGaloisUnion (Ω := Ω) a := by
  let F := IntermediateField.adjoin ℚ ({ζ} : Set Ω)
  letI : Algebra ℚ F := F.algebra'
  letI : IsCyclotomicExtension {m} ℚ F :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin m ℚ Ω F hζ).mpr rfl
  letI : FiniteDimensional ℚ F := IsCyclotomicExtension.finiteDimensional {m} ℚ F
  letI : IsGalois ℚ F := IsCyclotomicExtension.isGalois {m} ℚ F
  let L : FiniteGaloisIntermediateField ℚ Ω := ⟨F⟩
  letI : Algebra ℚ L := L.algebra'
  letI : NumberField L := NumberField.of_module_finite ℚ L
  have hcyc : @IsCyclotomicExtension {m} ℚ L _ _ L.algebra' :=
    inferInstanceAs (@IsCyclotomicExtension {m} ℚ F _ _ F.algebra')
  have hrat : (L.algebra' : Algebra ℚ L) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  letI : @IsCyclotomicExtension {m} ℚ L _ _ DivisionRing.toRatAlgebra := hrat ▸ hcyc
  have hstage : ∀ w : HeightOneSpectrum (𝓞 L),
      algebraMap (𝓞 ℚ) (𝓞 L) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1 := by
    intro w hw
    have hm : (m : 𝓞 L) ∉ w.asIdeal := by
      intro hm
      obtain ⟨b, hb⟩ := hma
      apply hw
      rw [hb, map_mul, map_natCast]
      exact w.asIdeal.mul_mem_right (algebraMap (𝓞 ℚ) (𝓞 L) b) hm
    have h := rationalCyclotomic_originalBase_ramificationIdx_one m w hm
    let P : Algebra ℚ L → Prop := fun inst =>
      letI := inst
      (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1
    have hP : P DivisionRing.toRatAlgebra := h
    change P L.algebra'
    exact hrat.symm ▸ hP
  apply originalUnramifiedGaloisStage_le_union a ⟨L, hstage⟩
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)

/-- A separably closed original ambient field supplies an actual primitive root in the constructed rational unramified union whenever the conductor divides the exceptional integer. -/
theorem originalQUnramifiedUnion_exists_primitiveRoot [IsSepClosed Ω]
    (a : 𝓞 ℚ) (m : ℕ) [NeZero m] (hma : (m : 𝓞 ℚ) ∣ a) :
    ∃ ζ : originalUnramifiedGaloisUnion (Ω := Ω) a, IsPrimitiveRoot ζ m := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  refine ⟨⟨ζ, originalQUnramifiedUnion_mem_of_primitiveRoot a m hma ζ hζ⟩, ?_⟩
  exact IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ

end
end Dubon2026
