import Dubon2026.SourceLaurentDegreeTransportFields

/-! DUB-17/18 -> numerical modular genus -> exact all-level j-map degree
-> transport from the rational original field to its geometric coefficient
extension. Literal Laurent coefficients preserve linear independence.
Polynomial denominator clearing and the existing finite original extension
then preserve the coordinate degree, allowing rational prime-power proofs
to serve the actual algebraically closed coefficient field.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_GeometricBaseChange.lean and
P2M/Sol/S_ModularCurve_relfinrank_laurentBaseChange.lean.
Only the finite degree-transport chain is selected; external global instance
changes, proof options and the infinite-dimensional generalization are omitted.
-/
namespace Dubon2026.SourceFunctionField.DegreeTransport
noncomputable section
open IntermediateField Polynomial

variable (L : Type*) [Field L] [Algebra ℚ L]
variable {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} {t : LaurentSeries ℚ}

section Finite

variable (ht : t ∈ F₀) [FiniteDimensional (K₀ t) (E₀ F₀ t ht)]
include ht

theorem mem_span_image (x : LaurentSeries L) (hx : x ∈ laurentBaseChange L F₀) :
    x ∈ Submodule.span (K L t) (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ))) := by
  have hx' : x ∈ IntermediateField.adjoin (K L t) (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ))) := by
    rw [← mem_restrictScalars L, restrictScalars_adjoin_K L ht]; exact hx
  have halg : ∀ y ∈ coeffEmb L '' (F₀ : Set (LaurentSeries ℚ)), IsAlgebraic (K L t) y := by
    rintro _ ⟨f, hf, rfl⟩; exact isAlgebraic_coeffEmb L ht f hf
  rw [← mem_toSubalgebra, adjoin_toSubalgebra_of_isAlgebraic halg] at hx'
  have hx'' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin (K L t) (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ)))) := hx'
  rw [Algebra.adjoin_eq_span] at hx''
  rwa [closure_image_eq] at hx''

theorem mem_span_range {ι : Type*} (b : Module.Basis ι (K₀ t) (E₀ F₀ t ht)) (x : LaurentSeries L)
    (hx : x ∈ laurentBaseChange L F₀) :
    x ∈ Submodule.span (K L t) (Set.range fun i => ((ψ L ht (b i) : E L F₀ t ht) : LaurentSeries L)) := by
  refine Submodule.span_le.mpr ?_ (mem_span_image L ht x hx)
  rintro _ ⟨f, hf, rfl⟩
  have hrepr := b.linearCombination_repr ⟨f, (mem_extendScalars _).mpr hf⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hrepr
  have : coeffEmb L f = ∑ i ∈ (b.repr ⟨f, (mem_extendScalars _).mpr hf⟩).support,
      (φ L (b.repr ⟨f, (mem_extendScalars _).mpr hf⟩ i)) • ((ψ L ht (b i) : E L F₀ t ht) : LaurentSeries L) := by
    have h2 := congrArg (fun z : E₀ F₀ t ht => coeffEmb L (z : LaurentSeries ℚ)) hrepr
    dsimp only at h2
    rw [← h2, AddSubmonoidClass.coe_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.coe_smul, Algebra.smul_def, map_mul, Algebra.smul_def]
    rfl
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem finite_and_finrank_le :
    Module.Finite (K L t) (E L F₀ t ht) ∧
      Module.finrank (K L t) (E L F₀ t ht) ≤ Module.finrank (K₀ t) (E₀ F₀ t ht) := by
  classical
  let b := Module.Free.chooseBasis (K₀ t) (E₀ F₀ t ht)
  let y : Module.Free.ChooseBasisIndex (K₀ t) (E₀ F₀ t ht) → E L F₀ t ht := fun i => ψ L ht (b i)
  have htop : ∀ x : E L F₀ t ht, x ∈ Submodule.span (K L t) (Set.range y) := fun x => by
    have hx := mem_span_range L ht b (x : LaurentSeries L) ((mem_extendScalars _).mp x.2)
    have hr : (Set.range fun i => ((ψ L ht (b i) : E L F₀ t ht) : LaurentSeries L))
        = (E L F₀ t ht).val.toLinearMap '' (Set.range y) := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image] at hx
    obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx
    have hzx' : z = x := Subtype.ext hzx
    exact hzx' ▸ hz
  have hspan : Submodule.span (K L t) (Set.range y) = ⊤ := eq_top_iff.mpr fun x _ => htop x
  have hfin : Module.Finite (K L t) (E L F₀ t ht) :=
    ⟨by rw [← hspan]; exact Submodule.fg_span (Set.finite_range y)⟩
  refine ⟨hfin, ?_⟩
  conv_rhs => rw [Module.finrank_eq_card_chooseBasisIndex]
  conv_lhs => rw [← finrank_top, ← hspan]
  calc Module.finrank (K L t) (Submodule.span (K L t) (Set.range y))
        ≤ (Set.range y).toFinset.card := finrank_span_le_card _
    _ ≤ Fintype.card (Module.Free.ChooseBasisIndex (K₀ t) (E₀ F₀ t ht)) := by
        rw [Set.toFinset_range]; exact Finset.card_image_le.trans (by rw [Finset.card_univ])

end Finite
end
end Dubon2026.SourceFunctionField.DegreeTransport
