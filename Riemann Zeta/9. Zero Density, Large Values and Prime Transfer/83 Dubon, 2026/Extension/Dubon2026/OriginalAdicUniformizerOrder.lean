import Dubon2026.OriginalAdicIntegerNormComparison
import Dubon2026.OriginalUnramifiedIntegerUniformizer

/-! # Original adic uniformizers have the required normalized order

The original discrete valuation generator gives an irreducible in the
actual completion integer ring. The identity-on-values ring comparison
then feeds the existing normalized-order theorem, preserving the actual
integer chosen outside the ramification support for DUB-17.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField WithZero
variable (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))

/-- An element of original adic valuation minus one is irreducible in the original integer ring. -/
theorem originalAdicInteger_irreducible_of_uniformizer
    (x : w.adicCompletionIntegers L) (hx : Valued.v x.val = WithZero.exp (-1 : ℤ)) :
    Irreducible x := by
  have hu : (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰).IsUniformizer x.val := by
    rw [Valuation.IsUniformizer.iff, hx,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range ⟨x.val, hx⟩]
    rfl
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer x).mpr hu.is_generator

/-- The original completed unit of valuation minus one has normalized norm-valuation order one. -/
theorem originalAdicUnitOrder_of_uniformizer
    (π : (w.adicCompletion L)ˣ) (hπ : Valued.v π.val = WithZero.exp (-1 : ℤ)) :
    letI : ProperSpace (w.adicCompletion L) := original_adicCompletion_properSpace L w
    letI : NontriviallyNormedField (w.adicCompletion L) :=
      Valued.toNontriviallyNormedField (w.adicCompletion L) ℤᵐ⁰
    letI : ValuativeRel (w.adicCompletion L) :=
      ValuativeRel.ofValuation (NormedField.valuation (K := w.adicCompletion L))
    letI : IsNonarchimedeanLocalField (w.adicCompletion L) :=
      normValuation_isNonarchimedeanLocalField (w.adicCompletion L)
    localFieldUnitOrder (w.adicCompletion L) (Additive.ofMul π) = 1 := by
  letI : ProperSpace (w.adicCompletion L) := original_adicCompletion_properSpace L w
  letI : NontriviallyNormedField (w.adicCompletion L) :=
    Valued.toNontriviallyNormedField (w.adicCompletion L) ℤᵐ⁰
  letI : ValuativeRel (w.adicCompletion L) :=
    ValuativeRel.ofValuation (NormedField.valuation (K := w.adicCompletion L))
  letI : IsNonarchimedeanLocalField (w.adicCompletion L) :=
    normValuation_isNonarchimedeanLocalField (w.adicCompletion L)
  let x : w.adicCompletionIntegers L := ⟨π.val, by
    change Valued.v π.val ≤ 1
    rw [hπ]
    exact le_of_lt (by decide : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) < 1)⟩
  have hx : Irreducible x := originalAdicInteger_irreducible_of_uniformizer L w x hπ
  let q := originalAdicIntegerNormEquiv L w x
  have hq : Irreducible q := (MulEquiv.irreducible_iff
    (originalAdicIntegerNormEquiv L w)).mpr hx
  have hp := localFieldUnitOrder_irreducible (w.adicCompletion L) q hq
  have he : Units.mk0 (algebraMap _ (w.adicCompletion L) q)
      (show (q : w.adicCompletion L) ≠ 0 from π.ne_zero) = π :=
    Units.ext rfl
  rwa [he] at hp

end
end Dubon2026
