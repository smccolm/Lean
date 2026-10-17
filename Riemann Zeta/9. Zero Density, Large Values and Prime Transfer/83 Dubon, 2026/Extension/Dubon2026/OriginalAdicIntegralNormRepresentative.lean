import Dubon2026.OriginalAdicGroupNormValuation

/-! # Integral representatives modulo actual totally ramified local norms

Original fixed-completion descent and the ramification valuation formula,
together with pinned valuation surjectivity, adjust any invariant unit by
an actual group norm to an integral unit. The equality of ramification
index and decomposition order is retained explicitly for its later
inertia fixed-field instantiation in DUB-17's prescribed-support chain.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
  [Fintype (OriginalFiniteDecompositionGroup K L w)]

include v in
/-- When the actual local ramification index is the full decomposition
order, every invariant completion unit has an integral representative
modulo a literal completion group norm. -/
theorem originalAdicUnit_exists_integral_mod_norm
    (hram : v.asIdeal.ramificationIdx w.asIdeal =
      Nat.card (OriginalFiniteDecompositionGroup K L w))
    (x : (originalAdicUnitRep K L w).ρ.invariants) :
    ∃ b : originalAdicUnitRep K L w,
      (x.val - (originalAdicUnitRep K L w).ρ.norm b).toMul ∈
        (w.adicCompletionIntegers L).units := by
  let C := originalAdicUnitRep K L w
  let D := OriginalFiniteDecompositionGroup K L w
  have hx (σ : Gal(L/K)) (hσ : numberFieldGaloisPlaceEquiv K L σ w = w) :
      numberFieldGaloisLocalTransport K L σ w w hσ x.val.toMul.val = x.val.toMul.val :=
    congrArg (fun y : C => y.toMul.val) (x.property ⟨σ, hσ⟩)
  obtain ⟨a, ha⟩ := originalAdicBaseChangeMap_surjective_fixed K L v w x.val.toMul.val hx
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact Units.ne_zero x.val.toMul ha.symm
  have hva0 : (Valued.v a : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ha0
  obtain ⟨b, hb⟩ := w.valuedAdicCompletion_surjective L (Valued.v a)
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, map_zero] at hb
    exact hva0 hb.symm
  let z : C := Additive.ofMul (Units.mk0 b hb0)
  have hvx : (Valued.v x.val.toMul.val : WithZero (Multiplicative ℤ)) =
      Valued.v a ^ Fintype.card D := by
    rw [← ha, originalAdicBaseChangeMap_valuation, hram, Nat.card_eq_fintype_card]
  have hn := originalAdicUnit_restricted_norm_valuation K L w (MonoidHom.id D) z
  change Valued.v ((C.ρ.norm z).toMul.val) =
    (Valued.v b : WithZero (Multiplicative ℤ)) ^ Fintype.card D at hn
  rw [hb, ← hvx] at hn
  refine ⟨z, ?_⟩
  apply HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
  change Valued.v (((show (w.adicCompletion L)ˣ from x.val.toMul) /
    (show (w.adicCompletion L)ˣ from (C.ρ.norm z).toMul)).val) = 1
  rw [Units.val_div_eq_div_val, map_div₀, hn]
  exact div_self ((Valuation.ne_zero_iff _).mpr (Units.ne_zero x.val.toMul))

end
end Dubon2026
