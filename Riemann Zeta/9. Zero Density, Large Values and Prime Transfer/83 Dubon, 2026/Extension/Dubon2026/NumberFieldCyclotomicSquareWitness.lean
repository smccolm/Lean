import Dubon2026.OriginalCyclotomicPrimeStage
import Dubon2026.NumberFieldCyclotomicDegreeLowerBound
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! The actual cyclotomic character has a value whose square is nontrivial.
The source large-prime bound supplies the degree condition; no character
surjectivity over the original number field is assumed. -/

namespace Dubon2026
noncomputable section

/-- The actual root character over the original number field has a nontrivial square at a sufficiently large prime. -/
theorem numberField_primitiveRoot_exists_character_square_ne_one
    (K Ω : Type) [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω]
    (l : ℕ) [Fact l.Prime] {z : Ω} (hz : IsPrimitiveRoot z l)
    (hlarge : 2 * Module.finrank ℚ K < l - 1) :
    ∃ g : Gal(Ω/K), hz.autToPow K g ^ 2 ≠ 1 := by
  let F := originalPrimitiveRootStage K Ω hz
  letI : NumberField F := NumberField.of_module_finite K F
  let zF : F := originalPrimitiveRootStageRoot K Ω hz
  have hzF : IsPrimitiveRoot zF l := originalPrimitiveRootStageRoot_isPrimitive K Ω hz
  have hdegree : 2 < Module.finrank K F :=
    numberField_cyclotomic_degree_gt K F l 2 Fact.out hlarge zF hzF
  letI : IsCyclic Gal(F/K) := isCyclic_of_injective (hzF.autToPow K) (hzF.autToPow_injective K)
  have hex : ∃ gF : Gal(F/K), hzF.autToPow K gF ^ 2 ≠ 1 := by
    by_contra h
    push Not at h
    have hdiv : Monoid.exponent Gal(F/K) ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        hzF.autToPow_injective K (by simpa only [map_pow, map_one] using h g)
    rw [IsCyclic.exponent_eq_card, IsGalois.card_aut_eq_finrank] at hdiv
    exact (not_le_of_gt hdegree) (Nat.le_of_dvd (by decide) hdiv)
  obtain ⟨gF, hgF⟩ := hex
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective Ω gF
  refine ⟨g, ?_⟩
  have he : hz.autToPow K g = hzF.autToPow K gF := by
    apply Units.ext
    apply ZMod.val_injective
    apply hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    rw [hz.autToPow_spec K]
    have hroot : (AlgEquiv.restrictNormalHom F g) zF =
        zF ^ (hzF.autToPow K gF : ZMod l).val := by
      rw [hg]
      exact (hzF.autToPow_spec K gF).symm
    simpa only [AlgEquiv.restrictNormalHom_apply, map_pow] using
      congrArg (fun x : F => (x : Ω)) hroot
  rwa [he]

end
end Dubon2026
