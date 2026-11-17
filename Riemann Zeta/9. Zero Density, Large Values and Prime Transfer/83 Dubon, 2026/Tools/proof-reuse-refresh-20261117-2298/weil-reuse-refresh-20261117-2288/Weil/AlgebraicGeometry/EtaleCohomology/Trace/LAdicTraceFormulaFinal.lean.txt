module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTraceFormulaFinal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GradedCharSeriesRational
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionRationalSheaf
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.RationalCohomologyFrobenius
public import Weil.LinearAlgebra.Charpoly.Reverse

/-!
# The L-function of a `ℚ_ℓ`-sheaf is rational

Let `X` be a separated scheme of finite type over a finite field `k`, admitting a
compactification, `ℓ` a prime different from the characteristic of `k`, and `F` a `ℚ_ℓ`-sheaf
on `X`. Grothendieck's formula expresses the L-function as
`L(X, F) = ∏_ν det(1 - π_X^* T | H^ν_c(X_k̄, F))^{(-1)^{ν+1}}`, a finite product since only
finitely many `H^ν_c` are nonzero. Hence `L(X, F)` is a rational function: there are polynomials
`P, Q ∈ ℚ_ℓ[T]` with `Q(0) = 1` and `Q · L(X, F) = P`, namely
`P = ∏_{ν odd} det(1 - π_X^* T | H^ν_c)` and `Q = ∏_{ν even} det(1 - π_X^* T | H^ν_c)`.

## Main results

* `Weil.exists_rationalLFunction_mul_eq_polynomial`: the rationality of the
  L-function of a `ℚ_ℓ`-sheaf.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Ch. II, §4.
* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry PowerSeries Stacks.EtaleCohomology

universe u

namespace Weil

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime] [IsNoetherian X.1]
  {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f]

/-- **The L-function of a `ℚ_ℓ`-sheaf is rational.** Let `X` be a separated scheme of finite
type over a finite field `k` with a compactification `j`, `ℓ` a prime different from the
characteristic of `k` and `F` a `ℚ_ℓ`-sheaf on `X`. Then there are polynomials `P, Q ∈ ℚ_ℓ[T]`
with `Q(0) = 1` and `L(X, F) · Q = P` in `ℚ_ℓ⟦T⟧`. -/
@[weil "lem_fk204_ladic_l_series_rational"]
theorem exists_rationalLFunction_mul_eq_polynomial (j : CompactificationOf (Over.mk f))
    (hℓ : ℓ ≠ ringChar k)
    (F : SmallEtale.LAdicSheaf.{u, u + 1} B X ℓ) :
    ∃ P Q : Polynomial ℚ_[ℓ], Q.eval 0 = 1 ∧
      LAdicSheaf.rationalLFunction B X ℓ F f * (Q : ℚ_[ℓ]⟦X⟧) =
        (P : ℚ_[ℓ]⟦X⟧) := by
  have := Fintype.ofFinite k
  obtain ⟨q, hp, hcard⟩ := FiniteField.card k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hp⟩
  have hfin := (LAdicSheaf.traceFormula B X ℓ f j (AlgebraicClosure k)
    (ringChar k) q hcard hℓ F)
  have := hfin.1
  have hsupp : {i : ℤ | Nontrivial
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
        (AlgebraicClosure k) F i)}.Finite := by
    obtain ⟨d, hd⟩ : ∃ d : ℕ, ∀ i : ℤ, Nontrivial
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          j (AlgebraicClosure k) F i) → 0 ≤ i ∧ i ≤ 2 * (d : ℤ) := by
      by_cases h : ∃ i : ℤ, Nontrivial
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
            f j (AlgebraicClosure k) F i)
      · obtain ⟨i, hi⟩ := h
        obtain ⟨-, d, hd, -⟩ := hfin.2.1 i hi
        refine ⟨d, fun i' hi' => ?_⟩
        obtain ⟨h0, d', hd', hle⟩ := hfin.2.1 i' hi'
        have : d' = d := by exact_mod_cast hd'.symm.trans hd
        exact ⟨h0, this ▸ hle⟩
      · exact ⟨0, fun i hi => (h ⟨i, hi⟩).elim⟩
    exact (Set.finite_Icc (0 : ℤ) (2 * d)).subset fun i hi => hd i hi
  obtain ⟨P, Q, hQ, hPQ⟩ := exists_gradedCharSeries_mul_eq_polynomial _
    (fun i => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X
      ℓ f j (AlgebraicClosure k) (ringChar k) q hcard F i).hom) hsupp
  rw [← LAdicSheaf.rationalLFunction_eq_gradedCharSeries_compactSupportFrobenius
    B X ℓ f j (AlgebraicClosure k) (ringChar k) q hcard hℓ F] at hPQ
  refine ⟨Polynomial.C (Q.eval 0)⁻¹ * P, Polynomial.C (Q.eval 0)⁻¹ * Q, ?_, ?_⟩
  · rw [Polynomial.eval_mul, Polynomial.eval_C, inv_mul_cancel₀ hQ]
  · rw [Polynomial.coe_mul, Polynomial.coe_mul, ← hPQ]
    ring

end Weil

end

/-! ### The zeta function of a proper scheme as a product of characteristic polynomials -/

/-!
# The zeta function of a proper scheme as a product of characteristic polynomials

Let `k` be a finite field, `ℓ ≠ char k` a prime and `X` a proper scheme over `k` of dimension at
most `n`. Write `P_ν(t) = det(1 - t F_ν | H^ν(X_k̄, ℚ_ℓ))` for the reversed characteristic
polynomial of the Frobenius `F_ν` on the `ℓ`-adic cohomology. Then the zeta function of `X` is

`Z_X(t) = ∏_{ν = 0}^{2n} P_ν(t) ^ ((-1) ^ (ν + 1))` in `ℚ_ℓ⟦t⟧`.

This is Grothendieck's formula for the `L`-function of the constant sheaf `ℚ_ℓ`, computed with the
compactification `id_X` of the proper scheme `X`: the compactly supported cohomology is the
ordinary cohomology, and it vanishes outside the degrees `0, …, 2 dim X`.

## Main results

* `Weil.zetaFunction_eq_prod_rationalFrobeniusCharpolyReverse`: the formula above.
* `Weil.zetaFunction_mul_prod_even_eq_prod_odd`: the same with denominators cleared,
  `Z_X(t) ∏_{ν even} P_ν(t) = ∏_{ν odd} P_ν(t)`.

## Implementation notes

The dimension hypothesis is `topologicalKrullDim X ≤ n`, slightly more general than FK's
`dim X = n`; the factors with `ν > 2 dim X` are `1`. The inverse of a power series is the field
inverse `PowerSeries.instInv` of `ℚ_ℓ⟦t⟧` (each `P_ν` has constant coefficient `1`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1.
* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology

universe u

namespace Weil

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar k)]

/-- The factor of the alternating product in degree `ν` is `P_ν ^ ((-1) ^ (ν + 1))`. -/
theorem gradedCharFactor_rationalFrobenius (ν : ℕ) :
    haveI := isNoetherian_of_isProper f
    haveI := quasiSeparatedSpace_of_isProper f
    haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
    gradedCharFactor
        (fun i => LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) (AlgebraicClosure k) (LAdicSheaf.constantSystem B X ℓ) i)
        (fun i => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
          (CompactificationOf.ofProper f) (AlgebraicClosure k) (ringChar k)
          (FiniteField.card k (ringChar k)).choose
          (FiniteField.card k (ringChar k)).choose_spec.2 (LAdicSheaf.constantSystem B X ℓ) i).hom)
        (ν : ℤ) =
      if Even ν then ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) :
          PowerSeries ℚ_[ℓ])⁻¹
      else ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) :
          PowerSeries ℚ_[ℓ]) := by
  have hφ : charPowerSeries (rationalFrobenius B X f ℓ ν) 1 =
      ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) : PowerSeries ℚ_[ℓ]) :=
    charPowerSeries_one_eq_reverse_charpoly_of_free _
  simp only [gradedCharFactor, Int.even_coe_nat]
  change (if Even ν then PowerSeries.invOfUnit (charPowerSeries (rationalFrobenius B X f ℓ ν) 1) 1
    else charPowerSeries (rationalFrobenius B X f ℓ ν) 1) = _
  rw [hφ]
  split_ifs
  · refine PowerSeries.invOfUnit_eq' _ _ ?_
    rw [← hφ, constantCoeff_charPowerSeries _ one_ne_zero]
    rfl
  · rfl

/-- **The zeta function of a proper scheme** (FK IV.1). Let `X` be proper over the finite field
`k`, of dimension at most `n`, and `ℓ ≠ char k`. Then
`Z_X(t) = ∏_{ν = 0}^{2n} P_ν(t) ^ ((-1) ^ (ν + 1))` in `ℚ_ℓ⟦t⟧`, where
`P_ν(t) = det(1 - t F_ν | H^ν(X_k̄, ℚ_ℓ))`. -/
@[weil "lem_fk401_zeta_equals_char_poly_product"]
theorem zetaFunction_eq_prod_rationalFrobeniusCharpolyReverse (n : ℕ)
    (hn : topologicalKrullDim X.1 ≤ n) :
    zetaFunction B X ℓ f =
      ∏ ν ∈ Finset.range (2 * n + 1),
        if Even ν then ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) :
            PowerSeries ℚ_[ℓ])⁻¹
        else ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) :
            PowerSeries ℚ_[ℓ]) := by
  have := isNoetherian_of_isProper f
  have := quasiSeparatedSpace_of_isProper f
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have hℓ : ℓ ≠ ringChar k := Fact.out
  have hTF := LAdicSheaf.traceFormula B X ℓ f (CompactificationOf.ofProper f) (AlgebraicClosure k)
    (ringChar k) (FiniteField.card k (ringChar k)).choose
    (FiniteField.card k (ringChar k)).choose_spec.2 hℓ (LAdicSheaf.constantSystem B X ℓ)
  have := hTF.1
  rw [zetaFunction_def,
    LAdicSheaf.rationalLFunction_eq_gradedCharSeries_compactSupportFrobenius B X ℓ f
      (CompactificationOf.ofProper f) (AlgebraicClosure k) (ringChar k)
      (FiniteField.card k (ringChar k)).choose
      (FiniteField.card k (ringChar k)).choose_spec.2 hℓ (LAdicSheaf.constantSystem B X ℓ),
    gradedCharSeries_eq_prod _ _ ((Finset.range (2 * n + 1)).map Nat.castEmbedding),
    Finset.prod_map]
  · exact Finset.prod_congr rfl fun ν _ => gradedCharFactor_rationalFrobenius B X f ℓ ν
  · intro i hi
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    obtain ⟨h0, d, hd, hid⟩ := hTF.2.1 i hnt
    apply hi
    have hdn : d ≤ n := by
      have := hd ▸ hn
      exact_mod_cast this
    lift i to ℕ using h0
    simp only [Finset.mem_map, Finset.mem_range, Nat.castEmbedding_apply, Nat.cast_inj,
      exists_eq_right]
    omega

/-- The formula for the zeta function with denominators cleared:
`Z_X(t) ∏_{ν even} P_ν(t) = ∏_{ν odd} P_ν(t)`, the products over `0 ≤ ν ≤ 2n`. -/
theorem zetaFunction_mul_prod_even_eq_prod_odd (n : ℕ) (hn : topologicalKrullDim X.1 ≤ n) :
    zetaFunction B X ℓ f *
        ∏ ν ∈ (Finset.range (2 * n + 1)).filter Even,
          ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) : PowerSeries ℚ_[ℓ]) =
      ∏ ν ∈ (Finset.range (2 * n + 1)).filter (¬ Even ·),
        ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) : PowerSeries ℚ_[ℓ]) := by
  have hc : ∀ ν, PowerSeries.constantCoeff
      ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) : PowerSeries ℚ_[ℓ]) ≠
        0 := by
    intro ν
    rw [rationalFrobeniusCharpolyReverse, ← charPowerSeries_one_eq_reverse_charpoly_of_free,
      constantCoeff_charPowerSeries _ one_ne_zero]
    exact one_ne_zero
  rw [zetaFunction_eq_prod_rationalFrobeniusCharpolyReverse B X f ℓ n hn, Finset.prod_ite,
    mul_comm, ← mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun ν _ => PowerSeries.mul_inv_cancel _ (hc ν), Finset.prod_const_one,
    one_mul]

end Weil

end
