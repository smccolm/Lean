import Dubon2026.OriginalSPlaceClassComparison

/-! # Original valuation witnesses for full-class quotient torsion

A q-torsion representative modulo original outside units has a principal
qth-power correction. At every outside prime the correction has the exact
qth-power valuation of the original idele component. This is the actual
input to the root construction for DUB-17's prime-field Hom comparison.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- Torsion of the actual full-class quotient supplies a literal principal correction with q-power outside valuations. -/
theorem originalClassTorsion_exists_valuation_witness
    (q : ℕ) (x : (AdeleRing (𝓞 L) L)ˣ)
    (hx : q • (originalIdeleClassesModOutsideRepHom K L S hS).hom
      (Additive.ofMul (QuotientGroup.mk' (numberFieldPrincipalIdele L).range x)) = 0) :
    ∃ u : Lˣ, ∀ v : HeightOneSpectrum (𝓞 L), v ∉ S →
      v.valuation L (u : L) = Valued.v (numberFieldIdeleFiniteComponent L v x).val ^ q := by
  have hx' : Submodule.Quotient.mk
      (q • Additive.ofMul (QuotientGroup.mk' (numberFieldPrincipalIdele L).range x)) =
        (0 : originalIdeleClassesModOutsideRep K L S hS) := by
    exact hx
  have hm : q • Additive.ofMul (QuotientGroup.mk' (numberFieldPrincipalIdele L).range x) ∈
      LinearMap.range (originalOutsideIdeleClassRepHom K L S hS).hom.toLinearMap :=
    (Submodule.Quotient.mk_eq_zero (p :=
      LinearMap.range (originalOutsideIdeleClassRepHom K L S hS).hom.toLinearMap)).mp hx'
  obtain ⟨y, hy⟩ := hm
  let t := (originalOutsideSupportedInclusion K L S hS).hom y
  let c := QuotientGroup.mk' (numberFieldPrincipalIdele L).range
  have he : c t.toMul.val = c (x ^ q) := by
    rw [map_pow]
    exact congrArg Additive.toMul hy
  have hz : c (x ^ q / t.toMul.val) = 1 := by
    rw [map_div, ← he]
    exact div_self' _
  obtain ⟨u, hu⟩ := (QuotientGroup.eq_one_iff _).mp hz
  refine ⟨u, ?_⟩
  intro v hv
  have ht := t.toMul.property
  simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one] at ht
  have hval := congrArg (fun z => Valued.v (numberFieldIdeleFiniteComponent L v z).val) hu
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

/-- The actual torsion correction has outside valuations represented by qth powers of genuine base-field units. -/
theorem originalClassTorsion_exists_base_valuation_witness
    (q : ℕ) (x : (AdeleRing (𝓞 L) L)ˣ)
    (hx : q • (originalIdeleClassesModOutsideRepHom K L S hS).hom
      (Additive.ofMul (QuotientGroup.mk' (numberFieldPrincipalIdele L).range x)) = 0) :
    ∃ u : Lˣ,
      (∀ v : HeightOneSpectrum (𝓞 L), v ∉ S →
        v.valuation L (u : L) = Valued.v (numberFieldIdeleFiniteComponent L v x).val ^ q) ∧
      (∀ v : HeightOneSpectrum (𝓞 L), v ∉ S →
        ∃ c : Lˣ, v.valuation L (u : L) = v.valuation L (c : L) ^ q) := by
  obtain ⟨u, hu⟩ := originalClassTorsion_exists_valuation_witness K L S hS q x hx
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
