/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.TwoPowerCyclotomicCharacter
import Dubon2026.RationalCircleFiniteSubgroup
import Dubon2026.CyclotomicConjugationPower
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

/-! # The actual totally complex cyclic two-power subfield

Adapted from Tau Ceti revision 5f93ad556efb2f77494162e13d1e0c7ac37d5ff2,
`TauCeti/NumberTheory/NumberField/Cyclotomic/CyclicSubextension.lean`.
Pinned infinite-place conjugation and native rational-circle cyclicity
replace the external auxiliary frameworks. The fixed field has relative
degree at most two. It supplies the missing two-primary cyclic field
input for DUB-17's full-order arithmetic class; local-degree transfer and
global cohomology killing remain subsequent obligations.
-/
namespace Dubon2026
noncomputable section
open NumberField NumberField.InfinitePlace
open scoped NumberField

variable (K L : Type*) [Field K] [NumberField K] [Field L]
  [Algebra K L]

/-- A `2^(n+3)`-cyclotomic extension of a number field contains a totally complex cyclic
extension of the base whose relative index in the full extension is at most two. No
irreducibility assumption on the cyclotomic polynomial over the base is required. -/
theorem originalTwoPowerCyclotomic_exists_complex_cyclic_subfield (n : ℕ)
    [IsCyclotomicExtension {2 ^ (n + 3)} K L] :
    ∃ E : IntermediateField K L,
      IsGalois K E ∧ IsCyclic (Gal(E/K)) ∧ Module.finrank E L ≤ 2 ∧ IsTotallyComplex E := by
  let : NeZero (2 ^ (n + 3)) := ⟨by positivity⟩
  have : NumberField L := IsCyclotomicExtension.numberField {2 ^ (n + 3)} K L
  let : IsGalois K L := IsCyclotomicExtension.isGalois {2 ^ (n + 3)} K L
  let ζ := IsCyclotomicExtension.zeta (2 ^ (n + 3)) K L
  have hζ : IsPrimitiveRoot ζ (2 ^ (n + 3)) := IsCyclotomicExtension.zeta_spec _ K L
  obtain ⟨χ, _, hχneg, hχker⟩ := originalTwoPowerUnits_exists_character n
  let f := χ.toMultiplicativeRight.comp (hζ.autToPow K)
  let E := IntermediateField.fixedField f.ker
  have hgal : IsGalois K E := inferInstance
  -- The cyclotomic character embeds the new kernel into the modular character's kernel.
  let i : f.ker → χ.ker := fun σ ↦ ⟨Additive.ofMul (hζ.autToPow K σ), by
    have hs : f σ.val = 1 := MonoidHom.mem_ker.mp σ.property
    simpa only [f, MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply,
      ofAdd_eq_one, AddMonoidHom.mem_ker] using hs⟩
  have hi : Function.Injective i := by
    intro σ τ h
    apply Subtype.ext
    exact hζ.autToPow_injective K (Additive.ofMul.injective (congrArg Subtype.val h))
  have hdegree : Module.finrank E L ≤ 2 := by
    rw [IntermediateField.finrank_fixedField_eq_card]
    exact (Nat.card_le_card_of_injective i hi).trans hχker
  -- A finite subgroup of ℚ/ℤ is cyclic; the first isomorphism theorem transfers this to E/K.
  have : IsAddCyclic χ.range := originalRationalCircle_finite_subgroup_cyclic χ.range
  let j : f.range →* Multiplicative χ.range := {
    toFun := fun y ↦ Multiplicative.ofAdd ⟨y.val.toAdd, by
      obtain ⟨σ, hσ⟩ := y.property
      exact ⟨Additive.ofMul (hζ.autToPow K σ), by
        simpa [f] using congrArg Multiplicative.toAdd hσ⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl }
  have hj : Function.Injective j := by
    intro y z h
    apply Subtype.ext
    have he : y.val.toAdd = z.val.toAdd :=
      congrArg (fun t : Multiplicative χ.range ↦ (t.toAdd : AddCircle (1 : ℚ))) h
    exact Multiplicative.toAdd.injective he
  have : IsCyclic f.range := isCyclic_of_injective j hj
  have : IsCyclic ((Gal(L/K)) ⧸ f.ker) :=
    isCyclic_of_injective (QuotientGroup.quotientKerEquivRange f).toMonoidHom
      (QuotientGroup.quotientKerEquivRange f).injective
  have hcyclic : IsCyclic (Gal(E/K)) :=
    isCyclic_of_surjective (IsGalois.normalAutEquivQuotient f.ker).toMonoidHom
      (IsGalois.normalAutEquivQuotient f.ker).surjective
  -- A real place of E would make complex conjugation belong to the kernel, contradicting χ(-1).
  have : IsTotallyComplex L := nrRealPlaces_eq_zero_iff.mp
    (hζ.nrRealPlaces_eq_zero_of_two_lt (by
      have : 2 ^ 3 ≤ 2 ^ (n + 3) := Nat.pow_le_pow_right (by decide) (by omega)
      omega))
  have hcomplex : IsTotallyComplex E := ⟨fun v ↦ by
    rw [← not_isReal_iff_isComplex]
    intro hv
    obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (K := L) v
    have hwreal : (w.comap (algebraMap E L)).IsReal := by simpa only [hw] using hv
    have hbase : (w.comap (algebraMap K L)).IsReal := by
      simpa only [InfinitePlace.comap_comp, IsScalarTower.algebraMap_eq K E L] using
        hwreal.comap (algebraMap K E)
    have hram : w.IsRamified K := isRamified_iff.mpr ⟨IsTotallyComplex.isComplex w, hbase⟩
    obtain ⟨c, hcconj⟩ := exists_isConj_of_isRamified
      (show (InfinitePlace.mk w.embedding).IsRamified K by simpa using hram)
    have hc : c ∈ f.ker := by
      rw [← IntermediateField.fixingSubgroup_fixedField f.ker]
      change c ∈ E.fixingSubgroup
      apply (IntermediateField.mem_fixingSubgroup_iff E c).mpr
      intro x hx
      apply w.embedding.injective
      rw [hcconj.eq]
      have hr : ComplexEmbedding.IsReal (w.embedding.comp (algebraMap E L)) := by
        rw [← comap_embedding_of_isReal _ hwreal]
        exact isReal_iff.mp hwreal
      exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp hr) (⟨x, hx⟩ : E)
    have hzero : χ (Additive.ofMul (hζ.autToPow K c)) = 0 := by
      have he : f c = 1 := MonoidHom.mem_ker.mp hc
      simpa only [f, MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply,
        ofAdd_eq_one] using he
    rw [originalCyclotomicConjugation_power hζ w.embedding c hcconj] at hzero
    exact hχneg hzero⟩
  exact ⟨E, hgal, hcyclic, hdegree, hcomplex⟩


end
end Dubon2026
