import Dubon2026.OriginalClassTorsionValuationWitness

/-! A prime multiple in the actual S-place class image supplies the same
outside valuation correction as a torsion class. This is the precise
Kummer input needed to bring DUB-17's constructed full-class extension
back to the original S-place sequence. -/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- A multiple of the original full class lying in the S-place image
gives a principal correction with the exact outside power valuations. -/
theorem originalSourceClassPower_exists_valuation_witness
    (q : ℕ) (x : (AdeleRing (𝓞 L) L)ˣ)
    (z : originalSPlaceIdeleClassRep K L S hS)
    (hx : q • (originalIdeleClassesModOutsideRepHom K L S hS).hom
      (Additive.ofMul (QuotientGroup.mk' (numberFieldPrincipalIdele L).range x)) =
        (originalSPlaceClassComparison K L S hS).hom z) :
    ∃ u : Lˣ, ∀ v : HeightOneSpectrum (𝓞 L), v ∉ S →
      v.valuation L (u : L) = Valued.v (numberFieldIdeleFiniteComponent L v x).val ^ q := by
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    let s := (originalSPlaceSupportedInclusion K L S hS).hom z
    let c := QuotientGroup.mk' (numberFieldPrincipalIdele L).range
    let cx : originalIdeleClassRep K L := Additive.ofMul (c x)
    have hx' : Submodule.Quotient.mk
        (q • cx - (originalSupportedClassRepHom K L S hS).hom s) =
          (0 : originalIdeleClassesModOutsideRep K L S hS) := by
      change (originalIdeleClassesModOutsideRepHom K L S hS).hom
        (q • cx - (originalSupportedClassRepHom K L S hS).hom s) = 0
      rw [map_sub, map_nsmul]
      exact sub_eq_zero.mpr hx
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero (p :=
      LinearMap.range (originalOutsideIdeleClassRepHom K L S hS).hom.toLinearMap)).mp hx'
    change (originalOutsideIdeleClassRepHom K L S hS).hom y =
      q • cx - (originalSupportedClassRepHom K L S hS).hom s at hy
    let t := (originalOutsideSupportedInclusion K L S hS).hom y + s
    have htclass : (originalSupportedClassRepHom K L S hS).hom t = q • cx := by
      change (originalSupportedClassRepHom K L S hS).hom
        ((originalOutsideSupportedInclusion K L S hS).hom y + s) = _
      rw [map_add]
      change (originalOutsideIdeleClassRepHom K L S hS).hom y +
        (originalSupportedClassRepHom K L S hS).hom s = _
      rw [hy, sub_add_cancel]
    have he : c t.toMul.val = c (x ^ q) := by
      rw [map_pow]
      exact congrArg Additive.toMul htclass
    have hz : c (x ^ q / t.toMul.val) = 1 := by
      rw [map_div, ← he]
      exact div_self' _
    obtain ⟨u, hu⟩ := (QuotientGroup.eq_one_iff _).mp hz
    refine ⟨u, ?_⟩
    intro v hv
    have ht := t.toMul.property
    simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap,
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one] at ht
    have hval := congrArg (fun y => Valued.v (numberFieldIdeleFiniteComponent L v y).val) hu
    dsimp only at hval
    have hp : Valued.v (numberFieldIdeleFiniteComponent L v (numberFieldPrincipalIdele L u)).val =
        v.valuation L (u : L) := by
      change Valued.v (algebraMap L (v.adicCompletion L) u.val) = _
      simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self, RingHom.id_apply, Valued.valuedCompletion_apply]
      rfl
    rw [hp, map_div, map_pow, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
      map_div₀, map_pow, ht v hv, div_one] at hval
    exact hval

/-- The same source-image correction has outside valuations represented
by powers of actual base-field units, as required by the native root-stage theorem. -/
theorem originalSourceClassPower_exists_base_valuation_witness
    (q : ℕ) (x : (AdeleRing (𝓞 L) L)ˣ)
    (z : originalSPlaceIdeleClassRep K L S hS)
    (hx : q • (originalIdeleClassesModOutsideRepHom K L S hS).hom
      (Additive.ofMul (QuotientGroup.mk' (numberFieldPrincipalIdele L).range x)) =
        (originalSPlaceClassComparison K L S hS).hom z) :
    ∃ u : Lˣ,
      (∀ v : HeightOneSpectrum (𝓞 L), v ∉ S →
        v.valuation L (u : L) = Valued.v (numberFieldIdeleFiniteComponent L v x).val ^ q) ∧
      (∀ v : HeightOneSpectrum (𝓞 L), v ∉ S →
        ∃ c : Lˣ, v.valuation L (u : L) = v.valuation L (c : L) ^ q) := by
  obtain ⟨u, hu⟩ := originalSourceClassPower_exists_valuation_witness K L S hS q x z hx
  refine ⟨u, hu, ?_⟩
  intro v hv
  obtain ⟨c, hc⟩ := v.valuation_surjective L
    (Valued.v (numberFieldIdeleFiniteComponent L v x).val)
  have hc0 : c ≠ 0 := by
    intro h
    have he := hc
    rw [h, map_zero] at he
    have hz : Valued.v (numberFieldIdeleFiniteComponent L v x).val ≠ 0 := by simp
    exact hz he.symm
  refine ⟨Units.mk0 c hc0, ?_⟩
  change v.valuation L (u : L) = v.valuation L c ^ q
  rw [hc]
  exact hu v hv

end
end Dubon2026
