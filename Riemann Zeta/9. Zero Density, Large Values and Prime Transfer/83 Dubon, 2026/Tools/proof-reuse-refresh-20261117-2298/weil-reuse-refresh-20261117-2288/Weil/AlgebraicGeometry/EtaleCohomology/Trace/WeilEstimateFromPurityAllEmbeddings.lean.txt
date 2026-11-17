module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPoincarePairing
public import Weil.FieldTheory.IsAlgClosed.Classification

/-!
# Weil estimates from purity along every complex embedding

Let `V` be a finite-dimensional `ℚ_[ℓ]`-vector space, `φ` an endomorphism of `V`, `Q` a
natural number and `w` an integer, and suppose that `φ` is `ι`-pure of weight `w` relative to
`Q` for every ring homomorphism `ι : ℚ_[ℓ] →+* ℂ`. Let `L` be an algebraic closure of
`ℚ_[ℓ]`. Then every eigenvalue `λ ∈ L` of `φ` (a root in `L` of the characteristic polynomial
of `φ`) is algebraic over `ℚ`, and `|ι' λ| = Q ^ (w / 2)` for every field embedding
`ι' : ℚ⟮λ⟯ → ℂ`.

For a ring homomorphism `ι~ : L →+* ℂ`, `ι~ λ` is a root of the characteristic polynomial of
`φ` read along `ι := ι~ ∘ algebraMap ℚ_[ℓ] L`, so it is algebraic over `ℚ` of absolute value
`Q ^ (w / 2)` by hypothesis. Such an `ι~` exists, and every embedding of `ℚ⟮λ⟯` into `ℂ`
extends to one once `λ` is known to be algebraic
(`IsAlgClosure.exists_ringHom_padic_complex_extending`); algebraicity of `λ` follows from that
of `ι~ λ` because `ι~` is injective.

## Main results

* `Stacks.EtaleCohomology.isAlgebraic_and_norm_eq_of_forall_isCharpolyPureOfWeight`: the
  statement above.
* `Stacks.EtaleCohomology.isWeilNumber_of_forall_isCharpolyPureOfWeight`: for every ring
  homomorphism `ι~ : L →+* ℂ`, the image `ι~ λ` of an eigenvalue is a `Q`-Weil number of
  weight `w`.

## Implementation notes

The source assumes `Q ≥ 2`; the argument does not use it, and the results are stated for every
natural number `Q`. The algebraic closure is any field `L` with `IsAlgClosure ℚ_[ℓ] L`; it is
also assumed `CharZero`, which follows from the embedding of `ℚ_[ℓ]` and supplies the
`ℚ`-algebra structure on `L` that `ℚ⟮λ⟯` is formed with.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §4.
-/

@[expose] public section

open IntermediateField

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[ℓ] V]
  [FiniteDimensional ℚ_[ℓ] V] {L : Type*} [Field L] [Algebra ℚ_[ℓ] L]

/-- If `φ` is `ι`-pure of weight `w` relative to `Q` along `ι := ι~ ∘ algebraMap ℚ_[ℓ] L`, then
`ι~` sends every root in `L` of the characteristic polynomial of `φ` to a `Q`-Weil number of
weight `w`. -/
theorem isWeilNumber_of_isCharpolyPureOfWeight_comp {Q : ℕ} {w : ℤ} {φ : Module.End ℚ_[ℓ] V}
    (ι : L →+* ℂ) (h : IsCharpolyPureOfWeight Q (ι.comp (algebraMap ℚ_[ℓ] L)) w φ) {x : L}
    (hx : Polynomial.aeval x φ.charpoly = 0) : IsWeilNumber Q w (ι x) := by
  refine h (ι x) ?_
  rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
    hx, map_zero]

/-- If `φ` is `ι`-pure of weight `w` relative to `Q` for every `ι : ℚ_[ℓ] →+* ℂ`, then every
ring homomorphism `L →+* ℂ` sends every eigenvalue of `φ` in `L` to a `Q`-Weil number of
weight `w`. -/
theorem isWeilNumber_of_forall_isCharpolyPureOfWeight {Q : ℕ} {w : ℤ}
    {φ : Module.End ℚ_[ℓ] V} (h : ∀ ι : ℚ_[ℓ] →+* ℂ, IsCharpolyPureOfWeight Q ι w φ)
    (ι : L →+* ℂ) {x : L} (hx : Polynomial.aeval x φ.charpoly = 0) : IsWeilNumber Q w (ι x) :=
  isWeilNumber_of_isCharpolyPureOfWeight_comp ι (h _) hx

variable [CharZero L] [IsAlgClosure ℚ_[ℓ] L]

/-- **Weil estimate from purity along every embedding.** Let `φ` be an endomorphism of a
finite-dimensional `ℚ_[ℓ]`-vector space which is `ι`-pure of weight `w` relative to `Q` for
every ring homomorphism `ι : ℚ_[ℓ] →+* ℂ`, and let `L` be an algebraic closure of `ℚ_[ℓ]`.
Then every eigenvalue `λ ∈ L` of `φ` is algebraic over `ℚ`, and `|ι' λ| = Q ^ (w / 2)` for
every field embedding `ι' : ℚ⟮λ⟯ → ℂ`. -/
@[weil "lem_fk404_weil_estimate_from_purity_all_embeddings"]
theorem isAlgebraic_and_norm_eq_of_forall_isCharpolyPureOfWeight {Q : ℕ} {w : ℤ}
    {φ : Module.End ℚ_[ℓ] V} (h : ∀ ι : ℚ_[ℓ] →+* ℂ, IsCharpolyPureOfWeight Q ι w φ)
    {x : L} (hx : Polynomial.aeval x φ.charpoly = 0) :
    IsAlgebraic ℚ x ∧
      ∀ ι' : ℚ⟮x⟯ →+* ℂ, ‖ι' ⟨x, mem_adjoin_simple_self ℚ x⟩‖ = (Q : ℝ) ^ ((w : ℝ) / 2) := by
  -- some ring homomorphism `L →+* ℂ`, extending the unique one on the prime field
  have : Algebra.IsAlgebraic ℚ (⊥ : IntermediateField ℚ L).toSubfield :=
    Algebra.IsAlgebraic.of_finite ℚ (⊥ : IntermediateField ℚ L)
  obtain ⟨ι₀, -⟩ := IsAlgClosure.exists_ringHom_padic_complex_extending_of_isAlgebraic_rat ℓ
    (⊥ : IntermediateField ℚ L).toSubfield
    ((algebraMap ℚ ℂ).comp (IntermediateField.botEquiv ℚ L).toRingEquiv.toRingHom)
  have hx' : IsAlgebraic ℚ x :=
    (isAlgebraic_algHom_iff ι₀.toRatAlgHom ι₀.injective).1
      (isWeilNumber_of_forall_isCharpolyPureOfWeight h ι₀ hx).isAlgebraic
  refine ⟨hx', fun ι' => ?_⟩
  have : Algebra.IsAlgebraic ℚ (ℚ⟮x⟯.toSubfield) :=
    IntermediateField.isAlgebraic_adjoin_simple hx'.isIntegral
  obtain ⟨ι, hι⟩ := IsAlgClosure.exists_ringHom_padic_complex_extending_of_isAlgebraic_rat ℓ
    ℚ⟮x⟯.toSubfield ι'
  have := congrArg (fun g => g ⟨x, mem_adjoin_simple_self ℚ x⟩) hι
  simp only [RingHom.coe_comp, Function.comp_apply] at this
  rw [← this]
  exact (isWeilNumber_of_forall_isCharpolyPureOfWeight h ι hx).norm_eq

end Stacks.EtaleCohomology

end
