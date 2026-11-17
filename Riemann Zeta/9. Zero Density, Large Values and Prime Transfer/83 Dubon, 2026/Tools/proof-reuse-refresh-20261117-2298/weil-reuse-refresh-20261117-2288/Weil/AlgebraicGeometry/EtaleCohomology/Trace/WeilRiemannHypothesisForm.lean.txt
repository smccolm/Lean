module

public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.DeligneWeilConjecture
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyIntegrality
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTraceFormulaFinal
public import Weil.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityConstantSystem
public import Weil.FieldTheory.IsAlgClosed.Classification
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Weil.Attr

/-!
# The Weil conjectures in the form of the Riemann hypothesis for the zeta series

Let `X` be a smooth, geometrically irreducible scheme proper over the finite field `k` with `q`
elements, of dimension `d`, and `f_X ∈ ℚ⟦t⟧` its zeta series. There are polynomials
`f_0, …, f_{2d} ∈ ℤ[t]` with `f_j(0) = 1`, `f_0 = 1 - t`, `f_{2d} = 1 - q^d t`, all complex
reciprocal roots of `f_j` of absolute value `q ^ (j / 2)`, and
`f_X · f_0 f_2 ⋯ f_{2d} = f_1 f_3 ⋯ f_{2d-1}`.

## Main results

* `Weil.exists_zetaSeries_mul_prod_even_eq_prod_odd`: the Weil conjectures in this form.

## Implementation notes

[FK] state the theorem for `X` projective; it is stated here for `X` proper. The polynomials are
`f_j = P_j = det(1 - t F_j | H^j(X_k̄, ℚ_ℓ))` for any prime `ℓ ≠ char k`, with the cohomology
computed in the big étale site `BigEtaleSite.containing X`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Introduction, IV.1.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology Stacks.Frobenius IntermediateField
  Polynomial

universe u

namespace Weil

variable {k : Type u} [Field k] [Fintype k]

omit [Fintype k] in
/-- A geometrically irreducible scheme over `k` has a connected base change to `k̄`. -/
theorem connectedSpace_fieldBaseChange_of_geometricallyIrreducible {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [GeometricallyIrreducible f] (K : Type u) [Field K] [Algebra k K] :
    ConnectedSpace (fieldBaseChange (Over.mk f) K) := by
  have : GeometricallyIrreducible (Over.mk f).hom := ‹_›
  have : IrreducibleSpace (fieldBaseChange (Over.mk f) K) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (IsPullback.of_hasPullback _ _)
  exact IrreducibleSpace.connectedSpace _

/-- A complex reciprocal root of an integer polynomial `P` whose image `P_ℚ̄ℓ` in `ℚ_ℓ[t]` has all
its reciprocal roots in `ℚ̄_ℓ` of absolute value `Q ^ (w / 2)` along every embedding, has absolute
value `Q ^ (w / 2)`. -/
theorem norm_eq_of_aeval_inv_eq_zero_of_map {ℓ : ℕ} [Fact ℓ.Prime] (P : ℤ[X]) (Q : ℕ) (w : ℝ)
    (hP : ∀ μ : AlgebraicClosure ℚ_[ℓ], aeval μ⁻¹ (P.map (Int.castRingHom ℚ_[ℓ])) = 0 →
      ∀ ι : ℚ⟮μ⟯ →+* ℂ, ‖ι (AdjoinSimple.gen ℚ μ)‖ = (Q : ℝ) ^ w)
    (hP0 : P ≠ 0) {z : ℂ} (hz : aeval z⁻¹ P = 0) : ‖z‖ = (Q : ℝ) ^ w := by
  set y : ℂ := z⁻¹
  have hPq : aeval y (P.map (Int.castRingHom ℚ)) = 0 := by
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
    exact hz
  have hyint : IsIntegral ℚ y :=
    (isAlgebraic_iff_isIntegral).1
      ⟨P.map (Int.castRingHom ℚ), (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hP0, hPq⟩
  -- a root `λ'` of the minimal polynomial of `y` in `ℚ̄_ℓ`
  obtain ⟨l', hl'⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure ℚ_[ℓ])
    (minpoly ℚ y) (minpoly.degree_pos hyint).ne'
  have hl'int : IsIntegral ℚ l' := ⟨minpoly ℚ y, minpoly.monic hyint, hl'⟩
  have hmin : minpoly ℚ l' = minpoly ℚ y :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hyint) hl' (minpoly.monic hyint)).symm
  -- the embedding `ℚ(λ') → ℂ`, `λ' ↦ y`, extended to `ℚ̄_ℓ`
  have hy : y ∈ (minpoly ℚ l').aroots ℂ := by
    rw [mem_aroots, hmin]
    exact ⟨(minpoly.ne_zero hyint), minpoly.aeval ℚ y⟩
  let ι' : ℚ⟮l'⟯ →ₐ[ℚ] ℂ := (algHomAdjoinIntegralEquiv ℚ hl'int).symm ⟨y, hy⟩
  have hι' : ι' (AdjoinSimple.gen ℚ l') = y := algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hl'int _
  have : Algebra.IsAlgebraic ℚ (ℚ⟮l'⟯.toSubfield) :=
    IntermediateField.isAlgebraic_adjoin_simple hl'int
  obtain ⟨Φ, hΦ⟩ := IsAlgClosure.exists_ringHom_padic_complex_extending_of_isAlgebraic_rat ℓ
    ℚ⟮l'⟯.toSubfield ι'.toRingHom
  have hΦl : Φ l' = y := by
    have := congrArg (fun g => g (AdjoinSimple.gen ℚ l')) hΦ
    exact this.trans hι'
  -- `μ = λ'⁻¹` is a reciprocal root of `P` in `ℚ̄_ℓ`
  have hroot : aeval (l'⁻¹)⁻¹ (P.map (Int.castRingHom ℚ_[ℓ])) = 0 := by
    rw [inv_inv, ← algebraMap_int_eq, aeval_map_algebraMap]
    have hdvd : minpoly ℚ l' ∣ P.map (Int.castRingHom ℚ) := by
      rw [hmin]; exact minpoly.dvd ℚ y hPq
    have h0 : aeval l' (P.map (Int.castRingHom ℚ)) = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      rw [hc, map_mul, minpoly.aeval, zero_mul]
    rwa [← algebraMap_int_eq, aeval_map_algebraMap] at h0
  have := hP (l'⁻¹) hroot (Φ.comp (ℚ⟮l'⁻¹⟯.val.toRingHom))
  rw [RingHom.comp_apply] at this
  have hval : ℚ⟮l'⁻¹⟯.val (AdjoinSimple.gen ℚ l'⁻¹) = l'⁻¹ := rfl
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hval, map_inv₀, hΦl, norm_inv] at this
  simpa [y] using this

/-- The conclusion of the Weil conjectures for the zeta series `Z` of a scheme of dimension `d`
over a field with `q` elements: polynomials `f_0, …, f_{2d} ∈ ℤ[t]` with `f_j(0) = 1`,
`f_0 = 1 - t`, `f_{2d} = 1 - q^d t`, every `λ ∈ ℂ^×` with `f_j(λ⁻¹) = 0` of absolute value
`q ^ (j / 2)`, and `Z · f_0 f_2 ⋯ f_{2d} = f_1 f_3 ⋯ f_{2d-1}` in `ℚ⟦t⟧`. -/
def IsWeilZetaFactorization (q d : ℕ) (Z : PowerSeries ℚ) (P : ℕ → ℤ[X]) : Prop :=
  (∀ j ≤ 2 * d, (P j).coeff 0 = 1) ∧ P 0 = 1 - Polynomial.X ∧
    P (2 * d) = 1 - C ((q : ℤ) ^ d) * Polynomial.X ∧
    (∀ j ≤ 2 * d, ∀ z : ℂ, z ≠ 0 → aeval z⁻¹ (P j) = 0 → ‖z‖ = (q : ℝ) ^ ((j : ℝ) / 2)) ∧
    Z * ∏ j ∈ (Finset.range (2 * d + 1)).filter Even, (((P j).map (Int.castRingHom ℚ) : ℚ[X]) :
        PowerSeries ℚ) =
      ∏ j ∈ (Finset.range (2 * d + 1)).filter (¬ Even ·),
        (((P j).map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ)

variable (B : BigEtaleSite.{u}) (S : B.Scheme) (f : S.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ)
  [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar k)]

/-- **Grothendieck's formula for the zeta series.** Let `S` be proper over the finite field `k`, of
dimension at most `d`, `f_S ∈ ℚ⟦t⟧` its zeta series and `ℓ ≠ char k` a prime. Then, in `ℚ_ℓ⟦t⟧`,
`f_S(t) = ∏_{ν = 0}^{2d} P_ν(t) ^ ((-1) ^ (ν + 1))`, where
`P_ν(t) = det(1 - t F_ν | H^ν(S_k̄, ℚ_ℓ))`. -/
@[weil "thm_fk0_grothendieck_formula_zeta"]
theorem map_zetaSeries_eq_prod_rationalFrobeniusCharpolyReverse (d : ℕ)
    (hd : topologicalKrullDim S.1 ≤ d) :
    PowerSeries.map (algebraMap ℚ ℚ_[ℓ]) (zetaSeries f) =
      ∏ ν ∈ Finset.range (2 * d + 1),
        if Even ν then ((rationalFrobeniusCharpolyReverse B S f ℓ ν : Polynomial ℚ_[ℓ]) :
            PowerSeries ℚ_[ℓ])⁻¹
        else ((rationalFrobeniusCharpolyReverse B S f ℓ ν : Polynomial ℚ_[ℓ]) :
            PowerSeries ℚ_[ℓ]) := by
  have := isNoetherian_of_isProper f
  have := quasiSeparatedSpace_of_isProper f
  rw [← zetaFunction_eq_map_zetaSeries]
  exact zetaFunction_eq_prod_rationalFrobeniusCharpolyReverse B S f ℓ d hd

/-- **The Weil conjectures for the zeta series, from the integrality of the `P_j`.** For `S`
smooth of relative dimension `d`, proper and geometrically irreducible over `k`, if every
`P_j = det(1 - t F_j | H^j(S_k̄, ℚ_ℓ))` comes from `ℤ[t]`, those integer polynomials satisfy the
Weil conjectures for the zeta series of `S`. -/
theorem isWeilZetaFactorization_of_map_int (d : ℕ) [SmoothOfRelativeDimension d f]
    [GeometricallyIrreducible f] (P : ℕ → ℤ[X])
    (hP : ∀ j, (P j).map (Int.castRingHom ℚ_[ℓ]) = rationalFrobeniusCharpolyReverse B S f ℓ j) :
    IsWeilZetaFactorization (Fintype.card k) d (zetaSeries f) P := by
  have := isNoetherian_of_isProper f
  have := quasiSeparatedSpace_of_isProper f
  have hp : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  obtain ⟨e, -, hcard⟩ := FiniteField.card k (ringChar k)
  have hconn := connectedSpace_fieldBaseChange_of_geometricallyIrreducible f (AlgebraicClosure k)
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have hinj : Function.Injective (Polynomial.map (Int.castRingHom ℚ_[ℓ])) :=
    Polynomial.map_injective _ (RingHom.injective_int _)
  have hcoeff : ∀ j, (P j).coeff 0 = 1 := by
    intro j
    have h := congrArg (fun p => p.coeff 0) (hP j)
    simp only [coeff_map, rationalFrobeniusCharpolyReverse, coeff_zero_reverse,
      (LinearMap.charpoly_monic _).leadingCoeff] at h
    exact Int.cast_injective (α := ℚ_[ℓ]) (by simpa using h)
  have hS : Nonempty S.1 := by
    have : Surjective f := inferInstance
    obtain ⟨x, -⟩ := f.surjective (Classical.arbitrary _)
    exact ⟨x⟩
  refine ⟨fun j _ => hcoeff j, hinj ?_, hinj ?_, fun j _ z hz0 hz => ?_, ?_⟩
  · -- `P_0 = 1 - t`
    rw [hP 0, rationalFrobeniusCharpolyReverse,
      ← rationalGeometricCompactlySupportedFrobenius_eq_rationalFrobenius B S f ℓ (ringChar k) e
        hcard 0]
    rw [LAdicSheaf.charpoly_reverse_rationalGeometricCompactlySupportedFrobenius_constant_zero B S ℓ
      f (AlgebraicClosure k) (ringChar k) e hcard]
    simp
  · -- `P_{2d} = 1 - q^d t`
    rw [hP, rationalFrobeniusCharpolyReverse_two_mul_eq B S f ℓ d]
    simp
  · -- the absolute values
    refine norm_eq_of_aeval_inv_eq_zero_of_map (ℓ := ℓ) (P j) (Fintype.card k) _
      (fun μ hμ ι => ?_) ?_ hz
    · rw [hP] at hμ
      exact (isAlgebraic_and_norm_eq_of_aeval_inv_rationalFrobeniusCharpolyReverse_eq_zero B S f j μ
        hμ).2 ι
    · intro h0
      have := hcoeff j
      rw [h0, coeff_zero] at this
      exact zero_ne_one this
  · -- the product formula, from the one in `ℚ_ℓ⟦t⟧`
    have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field d f
    have h := zetaFunction_mul_prod_even_eq_prod_odd B S f ℓ d hdim.le
    rw [zetaFunction_eq_map_zetaSeries] at h
    apply PowerSeries.map_injective (algebraMap ℚ ℚ_[ℓ]) (algebraMap ℚ ℚ_[ℓ]).injective
    have hmap : ∀ j, PowerSeries.map (algebraMap ℚ ℚ_[ℓ])
        (((P j).map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) =
        ((rationalFrobeniusCharpolyReverse B S f ℓ j : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) := by
      intro j
      rw [← Polynomial.polynomial_map_coe, Polynomial.map_map, ← hP j]
      congr 2
    simp only [map_mul, map_prod, hmap]
    exact h

omit [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar k)] in
/-- **The Weil conjectures** (FK, Introduction). Let `X` be a smooth, geometrically irreducible
scheme of dimension `d`, proper over the finite field `k` with `q` elements, and `f_X ∈ ℚ⟦t⟧` its
zeta series. There are polynomials `f_0, …, f_{2d} ∈ ℤ[t]` with `f_j(0) = 1`, `f_0 = 1 - t`,
`f_{2d} = 1 - q^d t`, such that every `λ ∈ ℂ^×` with `f_j(λ⁻¹) = 0` has `|λ| = q ^ (j / 2)`, and
`f_X · f_0 f_2 ⋯ f_{2d} = f_1 f_3 ⋯ f_{2d-1}` in `ℚ⟦t⟧`. -/
@[weil "thm_fk0_weil_riemann_hypothesis_form"]
theorem exists_zetaSeries_mul_prod_even_eq_prod_odd {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (d : ℕ) [IsProper f] [SmoothOfRelativeDimension d f] [GeometricallyIrreducible f] :
    ∃ P : ℕ → ℤ[X],
      (∀ j ≤ 2 * d, (P j).coeff 0 = 1) ∧ P 0 = 1 - Polynomial.X ∧
      P (2 * d) = 1 - C ((Fintype.card k : ℤ) ^ d) * Polynomial.X ∧
      (∀ j ≤ 2 * d, ∀ z : ℂ, z ≠ 0 → aeval z⁻¹ (P j) = 0 →
        ‖z‖ = (Fintype.card k : ℝ) ^ ((j : ℝ) / 2)) ∧
      zetaSeries f * ∏ j ∈ (Finset.range (2 * d + 1)).filter Even,
          (((P j).map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) =
        ∏ j ∈ (Finset.range (2 * d + 1)).filter (¬ Even ·),
          (((P j).map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) := by
  let B := BigEtaleSite.containing X
  let S : B.Scheme := ⟨X, BigEtaleSite.contains_containing X⟩
  -- a prime `ℓ ≠ char k`
  obtain ⟨ℓ, hℓle, hℓ⟩ := Nat.exists_infinite_primes (ringChar k + 1)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact (ℓ ≠ ringChar k) := ⟨by omega⟩
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  choose P hP using exists_map_int_eq_rationalFrobeniusCharpolyReverse B S (f := f) ℓ
  exact ⟨P, isWeilZetaFactorization_of_map_int B S f ℓ d P hP⟩

end Weil
