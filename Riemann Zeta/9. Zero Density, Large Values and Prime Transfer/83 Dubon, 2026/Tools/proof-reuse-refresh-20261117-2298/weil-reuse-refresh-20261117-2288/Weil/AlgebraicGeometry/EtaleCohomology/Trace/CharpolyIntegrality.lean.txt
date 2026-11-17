module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTraceFormulaFinal
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.ZetaRationality
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.DeligneWeilConjecture
public import Weil.LinearAlgebra.Charpoly.WeightSeparation
public import Weil.LinearAlgebra.Charpoly.WeightSeparationIndependence
public import Weil.RingTheory.PowerSeries.Fatou

/-!
# The characteristic polynomials of Frobenius have integer coefficients independent of `ℓ`

Let `X` be a scheme smooth and proper over the finite field `k` with `q` elements, `ℓ ≠ char k`
a prime, and `P_ν(t) = det(1 - t F_ν | H^ν(X_k̄, ℚ_ℓ))`. Then (FK IV.1, Theorem 1.2)

* every `P_ν` has integer coefficients, and
* for two primes `ℓ, ℓ' ≠ char k` the integer polynomials `P_ν` formed with `ℚ_ℓ`- and with
  `ℚ_ℓ'`-cohomology coincide.

The proof is FK's: the zeta function `Z_X ∈ 1 + t ℤ⟦t⟧` does not depend on `ℓ`, and
`Z_X ∏_{ν even} P_ν = ∏_{ν odd} P_ν`; Deligne's theorem separates the `P_ν` by the absolute values
of their reciprocal roots.

## Main results

* `Weil.exists_zetaFunction_mul_prod_even_eq_prod_odd`: the cleared-denominator form of the
  cohomological formula for `Z_X`, for every large enough bound on the degrees.
* `Weil.exists_map_int_eq_rationalFrobeniusCharpolyReverse_of_satisfiesWeilEstimate`,
  `Weil.exists_map_int_eq_rationalFrobeniusCharpolyReverse`: `P_ν ∈ ℤ[t]`.
* `Weil.exists_map_int_eq_rationalFrobeniusCharpolyReverse_and_of_satisfiesWeilEstimate`,
  `Weil.exists_map_int_eq_rationalFrobeniusCharpolyReverse_and`: `P_ν^{(ℓ)} = P_ν^{(ℓ')}` in `ℤ[t]`.

## Implementation notes

FK states Theorem 1.2 for `X` smooth and projective; the results here are for `X` smooth and
proper, the generality of `Weil.satisfiesWeilEstimate`. The integral polynomial is an element
`p : ℤ[t]` whose image in `ℚ_ℓ[t]` is `P_ν`; for `ℓ`-independence, one `p` maps to both.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology PowerSeries

universe u

namespace Weil

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar k)]

/-- The cohomological formula for the zeta function of a proper scheme, for every bound `n` on
the degrees of the nonzero cohomology groups: `Z_X(t) = ∏_{ν = 0}^{2n} P_ν(t) ^ ((-1) ^ (ν + 1))`.
-/
private theorem zetaFunction_eq_prod_of_vanishing (n : ℕ)
    (hvan : ∀ ν : ℕ, 2 * n < ν → Subsingleton (rationalCohomology B X f ℓ ν)) :
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
    obtain ⟨h0, -, -, -⟩ := hTF.2.1 i hnt
    lift i to ℕ using h0
    apply hi
    simp only [Finset.mem_map, Finset.mem_range, Nat.castEmbedding_apply, Nat.cast_inj,
      exists_eq_right]
    by_contra hlt
    exact not_subsingleton_iff_nontrivial.2 hnt (hvan i (by omega))

omit [Fintype k] in
/-- The bound in `zetaFunction_eq_prod_of_vanishing` exists: the cohomology vanishes in degrees
above `2 dim X` whenever some cohomology group is nonzero. -/
private theorem exists_forall_vanishing [Finite k] :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ ν : ℕ, 2 * n < ν → Subsingleton (rationalCohomology B X f ℓ ν) := by
  have := Fintype.ofFinite k
  have := isNoetherian_of_isProper f
  have := quasiSeparatedSpace_of_isProper f
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have hℓ : ℓ ≠ ringChar k := Fact.out
  have hTF := LAdicSheaf.traceFormula B X ℓ f (CompactificationOf.ofProper f) (AlgebraicClosure k)
    (ringChar k) (FiniteField.card k (ringChar k)).choose
    (FiniteField.card k (ringChar k)).choose_spec.2 hℓ (LAdicSheaf.constantSystem B X ℓ)
  by_cases h : ∃ i : ℕ, Nontrivial (rationalCohomology B X f ℓ i)
  · obtain ⟨i, hi⟩ := h
    obtain ⟨-, d, hd, -⟩ := hTF.2.1 i hi
    refine ⟨d, fun n hn ν hν => ?_⟩
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    obtain ⟨-, d', hd', hle⟩ := hTF.2.1 ν hnt
    have : d' = d := by exact_mod_cast hd'.symm.trans hd
    subst this
    have : (ν : ℤ) ≤ 2 * n := hle.trans (by exact_mod_cast Nat.mul_le_mul_left 2 hn)
    omega
  · exact ⟨0, fun n _ ν _ => not_nontrivial_iff_subsingleton.1 fun hν => h ⟨ν, hν⟩⟩

/-- **The zeta function of a proper scheme, denominators cleared** (FK IV.1): for every large
enough `n`, `Z_X(t) ∏_{ν ≤ 2n even} P_ν(t) = ∏_{ν ≤ 2n odd} P_ν(t)` in `ℚ_ℓ⟦t⟧`. -/
theorem exists_zetaFunction_mul_prod_even_eq_prod_odd :
    ∃ N : ℕ, ∀ n, N ≤ n →
      zetaFunction B X ℓ f *
          ∏ ν ∈ (Finset.range (2 * n + 1)).filter Even,
            ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) :
              PowerSeries ℚ_[ℓ]) =
        ∏ ν ∈ (Finset.range (2 * n + 1)).filter (¬ Even ·),
          ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) :
            PowerSeries ℚ_[ℓ]) := by
  obtain ⟨N, hN⟩ := exists_forall_vanishing B X f ℓ
  refine ⟨N, fun n hn => ?_⟩
  have hc : ∀ ν, PowerSeries.constantCoeff
      ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) : PowerSeries ℚ_[ℓ]) ≠
        0 := by
    intro ν
    rw [rationalFrobeniusCharpolyReverse, ← charPowerSeries_one_eq_reverse_charpoly_of_free,
      constantCoeff_charPowerSeries _ one_ne_zero]
    exact one_ne_zero
  rw [zetaFunction_eq_prod_of_vanishing B X f ℓ n (hN n hn), Finset.prod_ite,
    mul_comm, ← mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun ν _ => PowerSeries.mul_inv_cancel _ (hc ν), Finset.prod_const_one,
    one_mul]

/-- The coercion of a finite product of polynomials to power series. -/
private theorem coe_prod_polynomial {R : Type*} [CommRing R] (s : Finset ℕ) (p : ℕ → Polynomial R) :
    ((∏ ν ∈ s, p ν : Polynomial R) : PowerSeries R) = ∏ ν ∈ s, (p ν : PowerSeries R) :=
  map_prod (Polynomial.coeToPowerSeries.ringHom (R := R)) p s

private theorem map_int_map_rat {L : Type*} [Field L] [CharZero L] (s : Polynomial ℤ) :
    (s.map (Int.castRingHom ℚ)).map (algebraMap ℚ L) = s.map (Int.castRingHom L) := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

private theorem coeff_zero_rationalFrobeniusCharpolyReverse (ν : ℕ) :
    (rationalFrobeniusCharpolyReverse B X f ℓ ν).coeff 0 = 1 := by
  rw [rationalFrobeniusCharpolyReverse, Polynomial.coeff_zero_reverse]
  exact (LinearMap.charpoly_monic _).leadingCoeff

/-- **Integrality from the Weil estimate.** If `W(X/k)` holds for the proper scheme `X`, then every
`P_ν(t) = det(1 - t F_ν | H^ν(X_k̄, ℚ_ℓ))` has integer coefficients. -/
theorem exists_map_int_eq_rationalFrobeniusCharpolyReverse_of_satisfiesWeilEstimate
    (hW : SatisfiesWeilEstimate B X f ℓ) (ν : ℕ) :
    ∃ p : Polynomial ℤ,
      p.map (Int.castRingHom ℚ_[ℓ]) = rationalFrobeniusCharpolyReverse B X f ℓ ν := by
  obtain ⟨N, hN⟩ := exists_zetaFunction_mul_prod_even_eq_prod_odd B X f ℓ
  set n := max N ν with hn
  have hrel := hN n (le_max_left _ _)
  obtain ⟨g, hg1, hgZ⟩ := exists_zetaFunction_eq_map_int B X ℓ f
  set P := rationalFrobeniusCharpolyReverse B X f ℓ with hP
  set Pev := ∏ μ ∈ (Finset.range (2 * n + 1)).filter Even, P μ
  set Pod := ∏ μ ∈ (Finset.range (2 * n + 1)).filter (¬ Even ·), P μ
  have hrel' : (Pev : ℚ_[ℓ]⟦X⟧) * PowerSeries.map (Int.castRingHom ℚ_[ℓ]) g = Pod := by
    rw [coe_prod_polynomial, coe_prod_polynomial, mul_comm, ← hgZ]
    exact hrel
  have hPev0 : Pev ≠ 0 := by
    intro h0
    have := congrArg (fun p : Polynomial ℚ_[ℓ] => p.coeff 0) h0
    simp only [Pev, Polynomial.coeff_zero_prod, Polynomial.coeff_zero] at this
    rw [Finset.prod_eq_one fun μ _ => coeff_zero_rationalFrobeniusCharpolyReverse B X f ℓ μ]
      at this
    exact one_ne_zero this
  have hmap : PowerSeries.map (Int.castRingHom ℚ_[ℓ]) g =
      PowerSeries.map (algebraMap ℚ ℚ_[ℓ]) (PowerSeries.map (Int.castRingHom ℚ) g) := by
    ext m
    simp
  obtain ⟨A₀, B₀, hB₀, hAB₀⟩ := PowerSeries.exists_mul_eq_of_map_algebraMap_mul_eq
    (PowerSeries.map (Int.castRingHom ℚ) g) (P := Pod) hPev0 (by rw [← hmap]; exact hrel')
  have hB₀0 : B₀ ≠ 0 := by
    rintro rfl
    simp at hB₀
  obtain ⟨A, B', hA1, hB1, hcop, hBA⟩ :=
    PowerSeries.exists_int_coprime_mul_eq_of_rat g hg1 hB₀0 hAB₀
  have key : ∀ p : Polynomial ℤ, ((p.map (Int.castRingHom ℚ_[ℓ]) : Polynomial ℚ_[ℓ]) :
      ℚ_[ℓ]⟦X⟧) = PowerSeries.map (Int.castRingHom ℚ_[ℓ]) (p : ℤ⟦X⟧) := by
    intro p
    ext m
    simp [Polynomial.coeff_coe]
  -- the relation `A ∏_{even} P = B ∏_{odd} P` in `ℚ_ℓ[t]`
  have hpoly : (A.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ_[ℓ]) * Pev =
      (B'.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ_[ℓ]) * Pod := by
    rw [map_int_map_rat, map_int_map_rat]
    apply Polynomial.coe_injective
    rw [Polynomial.coe_mul, Polynomial.coe_mul, ← hrel', key, key, mul_left_comm, ← map_mul, hBA,
      mul_comm]
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  obtain ⟨r, hr0, hrP, hrd⟩ := exists_rat_reverse_charpoly_of_weight (Fintype.card k) hq n
    (fun μ => (rationalFrobenius B X f ℓ μ).charpoly) (fun μ => LinearMap.charpoly_monic _)
    (fun μ _ => hW μ) (A.map (Int.castRingHom ℚ)) (B'.map (Int.castRingHom ℚ))
    (by simp [Polynomial.coeff_map, hA1]) (by simp [Polynomial.coeff_map, hB1]) hcop hpoly ν
    (by simp only [Finset.mem_range]; omega)
  have hdvd : ∃ C : Polynomial ℤ, C.coeff 0 = 1 ∧ r ∣ C.map (Int.castRingHom ℚ) := by
    split_ifs at hrd
    exacts [⟨B', hB1, hrd⟩, ⟨A, hA1, hrd⟩]
  obtain ⟨C, hC1, hCd⟩ := hdvd
  obtain ⟨s, hs⟩ := Polynomial.exists_map_eq_of_dvd_of_coeff_zero_eq_one hC1 hr0 hCd
  exact ⟨s, by rw [← map_int_map_rat, hs, hrP]; rfl⟩

/-- **The characteristic polynomials of Frobenius have integer coefficients** (Deligne; FK IV.1,
Theorem 1.2 1)). Let `X` be smooth and proper over the finite field `k` and `ℓ ≠ char k` a prime.
For every `ν`, `P_ν(t) = det(1 - t F_ν | H^ν(X_k̄, ℚ_ℓ))` lies in `ℤ[t]`. -/
@[weil "thm_fk401_deligne_char_poly_integer_coefficients"]
theorem exists_map_int_eq_rationalFrobeniusCharpolyReverse [Smooth f] (ν : ℕ) :
    ∃ p : Polynomial ℤ,
      p.map (Int.castRingHom ℚ_[ℓ]) = rationalFrobeniusCharpolyReverse B X f ℓ ν :=
  exists_map_int_eq_rationalFrobeniusCharpolyReverse_of_satisfiesWeilEstimate B X f ℓ
    (satisfiesWeilEstimate B X f) ν

/-- **Independence of `ℓ` from the Weil estimate.** If `W(X/k)` holds for the proper scheme `X`
for the primes `ℓ, ℓ' ≠ char k`, then for every `ν` the polynomials `P_ν` formed with `ℚ_ℓ`- and
with `ℚ_ℓ'`-cohomology are the images of one and the same polynomial in `ℤ[t]`. -/
theorem exists_map_int_eq_rationalFrobeniusCharpolyReverse_and_of_satisfiesWeilEstimate
    (ℓ' : ℕ) [Fact ℓ'.Prime] [Fact (ℓ' ≠ ringChar k)]
    (hW : SatisfiesWeilEstimate B X f ℓ) (hW' : SatisfiesWeilEstimate B X f ℓ') (ν : ℕ) :
    ∃ p : Polynomial ℤ,
      p.map (Int.castRingHom ℚ_[ℓ]) = rationalFrobeniusCharpolyReverse B X f ℓ ν ∧
      p.map (Int.castRingHom ℚ_[ℓ']) = rationalFrobeniusCharpolyReverse B X f ℓ' ν := by
  obtain ⟨N, hN⟩ := exists_zetaFunction_mul_prod_even_eq_prod_odd B X f ℓ
  obtain ⟨N', hN'⟩ := exists_zetaFunction_mul_prod_even_eq_prod_odd B X f ℓ'
  set n := max (max N N') ν with hn
  obtain ⟨g, -, hg, hg'⟩ := exists_zetaFunction_eq_map_int_of_two_primes B X ℓ f ℓ'
  choose p hp using exists_map_int_eq_rationalFrobeniusCharpolyReverse_of_satisfiesWeilEstimate
    B X f ℓ hW
  choose p' hp' using exists_map_int_eq_rationalFrobeniusCharpolyReverse_of_satisfiesWeilEstimate
    B X f ℓ' hW'
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have h := eq_of_weight_of_mul_eq (Fintype.card k) hq n
    (fun μ => (rationalFrobenius B X f ℓ μ).charpoly)
    (fun μ => (rationalFrobenius B X f ℓ' μ).charpoly)
    (fun μ => LinearMap.charpoly_monic _) (fun μ => LinearMap.charpoly_monic _)
    (fun μ _ => hW μ) (fun μ _ => hW' μ) p p' (fun μ _ => hp μ) (fun μ _ => hp' μ) g
    (by rw [← hg]; exact hN n (by omega)) (by rw [← hg']; exact hN' n (by omega)) ν
    (by simp only [Finset.mem_range]; omega)
  exact ⟨p ν, hp ν, h ▸ hp' ν⟩

/-- **The characteristic polynomials of Frobenius are independent of `ℓ`** (Deligne; FK IV.1,
Theorem 1.2 2)). Let `X` be smooth and proper over the finite field `k` and `ℓ, ℓ' ≠ char k`
primes. For every `ν`, the polynomials `P_ν^{(ℓ)}` and `P_ν^{(ℓ')}` formed with `ℚ_ℓ`- and with
`ℚ_ℓ'`-cohomology are equal in `ℤ[t]`: both are the images of one integer polynomial. -/
@[weil "thm_fk401_deligne_char_poly_independent_of_l"]
theorem exists_map_int_eq_rationalFrobeniusCharpolyReverse_and [Smooth f]
    (ℓ' : ℕ) [Fact ℓ'.Prime] [Fact (ℓ' ≠ ringChar k)] (ν : ℕ) :
    ∃ p : Polynomial ℤ,
      p.map (Int.castRingHom ℚ_[ℓ]) = rationalFrobeniusCharpolyReverse B X f ℓ ν ∧
      p.map (Int.castRingHom ℚ_[ℓ']) = rationalFrobeniusCharpolyReverse B X f ℓ' ν :=
  exists_map_int_eq_rationalFrobeniusCharpolyReverse_and_of_satisfiesWeilEstimate B X f ℓ ℓ'
    (satisfiesWeilEstimate B X f) (satisfiesWeilEstimate B X f) ν

end Weil
