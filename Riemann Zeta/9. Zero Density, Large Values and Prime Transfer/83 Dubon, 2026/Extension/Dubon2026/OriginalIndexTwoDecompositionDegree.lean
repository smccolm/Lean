import Dubon2026.OriginalDecompositionRestriction
import Mathlib.GroupTheory.Coset.Card

/-! # Retaining two-power local degrees in the cyclic subfield

The actual prime-stabilizer restriction is already surjective. Its kernel
embeds in the relative Galois group. Thus a subfield of relative degree
at most two loses at most one factor of two in the local degree. This is
the local-degree transfer needed after the totally complex cyclic field
construction in DUB-17's full-order arithmetic class dependency.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- Restriction to an actual Galois subfield of relative degree at most
two retains all but at most one factor of two in the prime stabilizer. -/
theorem originalFiniteDecomposition_two_power_divisibility
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : IntermediateField K L) [IsGalois K E] (hE : Module.finrank E L ≤ 2)
    (w : HeightOneSpectrum (𝓞 L)) (r : ℕ)
    (hw : 2 ^ (r + 1) ∣ Nat.card (OriginalFiniteDecompositionGroup K L w)) :
    2 ^ r ∣ Nat.card
      (OriginalFiniteDecompositionGroup K E (originalFinitePrimeBelow E L w)) := by
  let D := OriginalFiniteDecompositionGroup K L w
  let D' := OriginalFiniteDecompositionGroup K E (originalFinitePrimeBelow E L w)
  let f : D →* D' := {
    toFun := fun σ => ⟨AlgEquiv.restrictNormalHom E σ.val, by
      change numberFieldGaloisPlaceEquiv K E (AlgEquiv.restrictNormalHom E σ.val)
        (originalFinitePrimeBelow E L w) = originalFinitePrimeBelow E L w
      rw [← originalFinitePrimeBelow_restrictNormal K L E]
      exact congrArg (originalFinitePrimeBelow E L) σ.property⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun σ τ => Subtype.ext (map_mul _ σ.val τ.val) }
  have hf : Function.Surjective f := by
    intro τ
    obtain ⟨σ, hσ, he⟩ := originalFiniteDecomposition_restrict_surjective K L E w τ.val τ.property
    exact ⟨⟨σ, hσ⟩, Subtype.ext he⟩
  let i : f.ker → (AlgEquiv.restrictNormalHom E).ker := fun σ =>
    ⟨σ.val.val, congrArg Subtype.val (MonoidHom.mem_ker.mp σ.property)⟩
  have hi : Function.Injective i := by
    intro σ τ h
    have hv : σ.val.val = τ.val.val :=
      congrArg (fun x : (AlgEquiv.restrictNormalHom E).ker => x.val) h
    exact Subtype.ext (Subtype.ext hv)
  have hker : Nat.card f.ker ≤ 2 := by
    have h := Nat.card_le_card_of_injective i hi
    rw [IntermediateField.restrictNormalHom_ker,
      IsGalois.card_fixingSubgroup_eq_finrank] at h
    exact h.trans hE
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at hcard
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have hk : Nat.card f.ker = 1 ∨ Nat.card f.ker = 2 := by omega
  rcases hk with hk | hk
  · rw [hk, mul_one] at hcard
    rw [show Nat.card (OriginalFiniteDecompositionGroup K L w) = Nat.card D' from hcard] at hw
    exact (pow_dvd_pow 2 (Nat.le_succ r)).trans hw
  · change 2 ^ (r + 1) ∣ Nat.card D at hw
    rw [hcard, hk, pow_succ] at hw
    exact Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 2) hw

end
end Dubon2026
