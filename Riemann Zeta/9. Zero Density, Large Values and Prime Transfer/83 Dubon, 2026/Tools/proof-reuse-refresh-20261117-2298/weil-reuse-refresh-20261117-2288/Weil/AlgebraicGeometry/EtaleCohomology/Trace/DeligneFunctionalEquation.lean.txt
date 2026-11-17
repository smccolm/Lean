module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.EulerCharacteristic
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.FunctionalEquationSign
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import Weil.AlgebraicGeometry.EtaleCohomology.Duality.AlternatingPoincareDualityConstantSystem
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusIso
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.FieldOfConstantsFrobenius
public import Weil.LinearAlgebra.Charpoly.DualCharpolyTransfer
public import Weil.LinearAlgebra.Charpoly.FunctionalEquation
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.ConnectedComponentsCharpoly
public import Weil.Attr

/-!
# Deligne's functional equation of the zeta function

Let `S` be proper and smooth of relative dimension `n` over a finite field `k` with `q` elements,
`ℓ ∤ q`, `b_ν = dim H^ν(S_k̄, ℚ_ℓ)`, `P_ν(t) = det(1 - t F_ν)` and `χ(S) = ∑ (-1)^ν b_ν`.

## Main results

* `Weil.bettiNumber_eq_zero_of_lt`: `b_ν = 0` for `ν > 2n`.
* `Weil.eulerCharacteristic_eq_sum_range_of_smoothOfRelativeDimension`:
  `χ(S) = ∑_{ν = 0}^{2n} (-1)^ν b_ν`.
* `Weil.isCharpolyDual_rationalFrobenius`: the eigenvalues of `F_{2n-ν}` are the `q^n / μ`, `μ`
  the eigenvalues of `F_ν`, with multiplicity (Poincaré duality, characteristic polynomial form).
* `Weil.even_bettiNumber_and_even_rootMultiplicity`: for `n` odd, `b_n` is even and the square
  roots of `q^n` are eigenvalues of `F_n` of even multiplicity (alternating middle duality).
* `Weil.even_eulerCharacteristic`: `χ(S)` is even for `n` odd.
* `Weil.prod_aeval_inv_rationalFrobeniusCharpolyReverse_zpow_eq`: the functional equation.

## Implementation notes

`S` is not assumed connected or geometrically connected. For `S` connected, Poincaré duality is
applied over the field of constants `k' = Γ(S, 𝒪_S)`, over which `S` is geometrically connected
(`Weil.exists_isFrobeniusDuality_rationalFrobenius`,
`Weil.exists_alternating_isFrobeniusDuality_rationalFrobenius`), and transported along
`P_ν(S/k)(t) = P_ν(S/k')(t^{[k':k]})`
(`Weil.exists_fieldOfConstants_rationalFrobeniusCharpolyReverse_eq_comp`);
a general `S` is the disjoint union of its connected components
(`Weil.exists_connectedComponents_charpoly_eq_prod`). The duality statements are therefore stated
for characteristic polynomials, which is what the functional equation uses.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology Polynomial

universe u

namespace Weil

variable (B : BigEtaleSite.{u}) (S : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : S.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The empty space has Krull dimension `⊥`. -/
theorem topologicalKrullDim_eq_bot_of_isEmpty (X : Type*) [TopologicalSpace X] [IsEmpty X] :
    topologicalKrullDim X = ⊥ := by
  have : IsEmpty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨fun Z => isEmptyElim Z.isIrreducible.nonempty.some⟩
  exact Order.krullDim_eq_bot

omit [Fintype k] in
/-- `H^ν(S_k̄, ℚ_ℓ)` vanishes unless `ν ≤ 2 dim S`: if `2d < ν` whenever `S` has dimension `d`,
then `b_ν = 0`. -/
theorem bettiNumber_eq_zero_of_forall [Finite k] [Fact (ℓ ≠ ringChar k)] {ν : ℕ}
    (h : ∀ d : ℕ, topologicalKrullDim S.1 = d → 2 * d < ν) : bettiNumber B S f ℓ ν = 0 := by
  have := Fintype.ofFinite k
  have := isNoetherian_of_isProper f
  have := quasiSeparatedSpace_of_isProper f
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have hℓ : ℓ ≠ ringChar k := Fact.out
  have hTF := LAdicSheaf.traceFormula B S ℓ f (CompactificationOf.ofProper f) (AlgebraicClosure k)
    (ringChar k) (FiniteField.card k (ringChar k)).choose
    (FiniteField.card k (ringChar k)).choose_spec.2 hℓ (LAdicSheaf.constantSystem B S ℓ)
  have hsub : Subsingleton (rationalCohomology B S f ℓ ν) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    obtain ⟨-, d, hd, hid⟩ := hTF.2.1 ν hnt
    have := h d hd
    omega
  exact Module.finrank_zero_of_subsingleton

omit [Fintype k] in
/-- `b_ν = 0` for `ν > 2n` when `S` is smooth of relative dimension `n` over `k`. -/
theorem bettiNumber_eq_zero_of_lt [Finite k] [Fact (ℓ ≠ ringChar k)] (n : ℕ)
    [SmoothOfRelativeDimension n f] {ν : ℕ} (hν : 2 * n < ν) : bettiNumber B S f ℓ ν = 0 := by
  refine bettiNumber_eq_zero_of_forall B S f ℓ fun d hd => ?_
  rcases isEmpty_or_nonempty S.1 with hS | hS
  · rw [topologicalKrullDim_eq_bot_of_isEmpty S.1] at hd
    exact absurd hd (by simp)
  · rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field n f] at hd
    have : d = n := by exact_mod_cast hd.symm
    omega

omit [Fintype k] in
/-- **`χ(S) = ∑_{ν = 0}^{2n} (-1)^ν b_ν`** for `S` smooth of relative dimension `n` over `k`. -/
theorem eulerCharacteristic_eq_sum_range_of_smoothOfRelativeDimension [Finite k]
    [Fact (ℓ ≠ ringChar k)]
    (n : ℕ) [SmoothOfRelativeDimension n f] :
    eulerCharacteristic B S f ℓ =
      ∑ ν ∈ Finset.range (2 * n + 1), (-1) ^ ν * (bettiNumber B S f ℓ ν : ℤ) := by
  rcases isEmpty_or_nonempty S.1 with hS | hS
  · have h0 : ∀ ν, bettiNumber B S f ℓ ν = 0 := fun ν =>
      bettiNumber_eq_zero_of_forall B S f ℓ fun d hd => by
        rw [topologicalKrullDim_eq_bot_of_isEmpty S.1] at hd
        exact absurd hd (by simp)
    simp [eulerCharacteristic, h0]
  · exact eulerCharacteristic_eq_sum_range B S f ℓ
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field n f)

/-- The characteristic polynomial of the Frobenius has a nonzero constant coefficient. -/
theorem coeff_zero_charpoly_rationalFrobenius_ne_zero [Fact (ℓ ≠ ringChar k)] (ν : ℕ) :
    (rationalFrobenius B S f ℓ ν).charpoly.coeff 0 ≠ 0 := by
  intro h
  have hdet := LinearMap.det_eq_sign_charpoly_coeff (rationalFrobenius B S f ℓ ν)
  rw [h, mul_zero] at hdet
  exact (LinearMap.isUnit_iff_isUnit_det _).1 (isUnit_rationalFrobenius B S f ℓ ν) |>.ne_zero hdet

/-! ### Connected `S` -/

section Connected

variable [Fact (ℓ ≠ ringChar k)] (n : ℕ) [SmoothOfRelativeDimension n f] [ConnectedSpace S.1]

/-- **The `q^n`-duality relation between `F_ν` and `F_{2n-ν}` for `S` connected**: the
characteristic polynomial of `F_{2n-ν}` is `∏ (X - q^n / μ)`, `μ` running over the eigenvalues of
`F_ν` in `ℚ̄_ℓ` with multiplicity. `S` need not be geometrically connected: over its field of
constants `k'` it is, Poincaré duality holds there
(`Weil.exists_isFrobeniusDuality_rationalFrobenius`), and `P_ν(S/k)(t) = P_ν(S/k')(t^{[k':k]})`. -/
theorem isCharpolyDual_rationalFrobenius_of_connectedSpace {ν : ℕ} (hν : ν ≤ 2 * n) :
    Weil.Polynomial.IsCharpolyDual (AlgebraicClosure ℚ_[ℓ]) ((Fintype.card k : ℚ_[ℓ]) ^ n)
      (rationalFrobenius B S f ℓ ν).charpoly (rationalFrobenius B S f ℓ (2 * n - ν)).charpoly := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨k', _, _, _, g, _, _, hg, hsg, hgc, hrel⟩ :=
    exists_fieldOfConstants_rationalFrobeniusCharpolyReverse_eq_comp B S f ℓ n
  have : Module.Finite k k' := Module.Finite.of_finite
  obtain ⟨β, hc, hβ⟩ := exists_isFrobeniusDuality_rationalFrobenius B S g ℓ n ν hν
  have h' := hβ.isCharpolyDual (AlgebraicClosure ℚ_[ℓ])
  have hcard : (Fintype.card k' : ℚ_[ℓ]) ^ n =
      ((Fintype.card k : ℚ_[ℓ]) ^ n) ^ Module.finrank k k' := by
    rw [Module.card_eq_pow_finrank (K := k) (V := k'), Nat.cast_pow, ← pow_mul, ← pow_mul,
      mul_comm]
  simp only [Units.val_mk0, hcard] at h'
  refine Weil.Polynomial.IsCharpolyDual.of_reverse_eq_comp_X_pow
    (pow_ne_zero _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) Module.finrank_pos
    (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _)
    (coeff_zero_charpoly_rationalFrobenius_ne_zero B S f ℓ ν)
    (coeff_zero_charpoly_rationalFrobenius_ne_zero B S g ℓ ν)
    (coeff_zero_charpoly_rationalFrobenius_ne_zero B S f ℓ _)
    (coeff_zero_charpoly_rationalFrobenius_ne_zero B S g ℓ _) (hrel ν) (hrel _) h'

/-- **The middle cohomology for `n` odd, `S` connected**: `b_n` is even and every square root
`γ ∈ ℚ̄_ℓ` of `q^n` has even multiplicity as an eigenvalue of `F_n`. -/
theorem even_bettiNumber_and_even_rootMultiplicity_of_connectedSpace (hn : Odd n) :
    Even (bettiNumber B S f ℓ n) ∧
      ∀ γ : AlgebraicClosure ℚ_[ℓ],
        γ ^ 2 = algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) ((Fintype.card k : ℚ_[ℓ]) ^ n) →
          Even (((rationalFrobenius B S f ℓ n).charpoly.map
            (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))).rootMultiplicity γ) := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨k', _, _, _, g, _, _, hg, hsg, hgc, hrel⟩ :=
    exists_fieldOfConstants_rationalFrobeniusCharpolyReverse_eq_comp B S f ℓ n
  have : Module.Finite k k' := Module.Finite.of_finite
  obtain ⟨hb, hγ⟩ := even_finrank_and_even_rootMultiplicity_rationalFrobenius_of_odd B S g ℓ n hn
  have hcard : (Fintype.card k' : ℚ_[ℓ]) ^ n =
      ((Fintype.card k : ℚ_[ℓ]) ^ n) ^ Module.finrank k k' := by
    rw [Module.card_eq_pow_finrank (K := k) (V := k'), Nat.cast_pow, ← pow_mul, ← pow_mul,
      mul_comm]
  rw [hcard] at hγ
  refine ⟨?_, Weil.Polynomial.even_rootMultiplicity_of_reverse_eq_comp_X_pow Module.finrank_pos
    (coeff_zero_charpoly_rationalFrobenius_ne_zero B S f ℓ n)
    (coeff_zero_charpoly_rationalFrobenius_ne_zero B S g ℓ n) (hrel n) hγ⟩
  have h := Weil.Polynomial.even_natDegree_of_reverse_eq_comp_X_pow
    (coeff_zero_charpoly_rationalFrobenius_ne_zero B S f ℓ n)
    (coeff_zero_charpoly_rationalFrobenius_ne_zero B S g ℓ n) (hrel n)
    (by rwa [LinearMap.charpoly_natDegree])
  rwa [LinearMap.charpoly_natDegree] at h

end Connected

/-! ### The functional equation from the duality relations -/

section FromDuality

variable [Fact (ℓ ≠ ringChar k)] (n : ℕ) [SmoothOfRelativeDimension n f]

theorem bettiNumber_eq_natDegree (ν : ℕ) :
    bettiNumber B S f ℓ ν = (rationalFrobenius B S f ℓ ν).charpoly.natDegree :=
  (LinearMap.charpoly_natDegree _).symm

/-- `χ(S) = ∑_{ν ≤ 2n} (-1)^ν deg det(T - F_ν)`. -/
theorem eulerCharacteristic_eq_sum_natDegree :
    eulerCharacteristic B S f ℓ = ∑ ν ∈ Finset.range (2 * n + 1),
      (-1) ^ ν * ((rationalFrobenius B S f ℓ ν).charpoly.natDegree : ℤ) := by
  rw [eulerCharacteristic_eq_sum_range_of_smoothOfRelativeDimension B S f ℓ n]
  simp only [bettiNumber_eq_natDegree]

variable {n}

/-- **`n χ(S)` is even**, given the duality relations between `F_ν` and `F_{2n-ν}` and, for `n`
odd, the evenness of `b_n`. -/
theorem even_mul_eulerCharacteristic_of_isCharpolyDual
    (hR1 : ∀ ν ≤ 2 * n, Weil.Polynomial.IsCharpolyDual (AlgebraicClosure ℚ_[ℓ])
      ((Fintype.card k : ℚ_[ℓ]) ^ n) (rationalFrobenius B S f ℓ ν).charpoly
      (rationalFrobenius B S f ℓ (2 * n - ν)).charpoly)
    (hodd : Odd n → Even (bettiNumber B S f ℓ n)) :
    Even ((n : ℤ) * eulerCharacteristic B S f ℓ) := by
  rw [eulerCharacteristic_eq_sum_natDegree B S f ℓ n]
  exact even_mul_sum_neg_one_pow_mul_natDegree (L := AlgebraicClosure ℚ_[ℓ])
    (χ := fun ν => (rationalFrobenius B S f ℓ ν).charpoly) hR1
    (fun h => by rw [← bettiNumber_eq_natDegree]; exact hodd h)

/-- **The functional equation from the duality relations.** If the characteristic polynomials of
`F_ν` and `F_{2n-ν}` are `q^n`-dual for every `ν ≤ 2n`, and for `n` odd `b_n` is even and every
square root of `q^n` is an eigenvalue of `F_n` of even multiplicity, then in `ℚ_ℓ(t)`
`∏ P_ν(1 / (q^n t)) ^ (-1)^(ν+1) = ε q^(n χ / 2) t^χ ∏ P_ν(t) ^ (-1)^(ν+1)`. -/
theorem prod_aeval_inv_rationalFrobeniusCharpolyReverse_zpow_eq_of_isCharpolyDual
    (hR1 : ∀ ν ≤ 2 * n, Weil.Polynomial.IsCharpolyDual (AlgebraicClosure ℚ_[ℓ])
      ((Fintype.card k : ℚ_[ℓ]) ^ n) (rationalFrobenius B S f ℓ ν).charpoly
      (rationalFrobenius B S f ℓ (2 * n - ν)).charpoly)
    (hR2 : Odd n → Even (bettiNumber B S f ℓ n) ∧
      ∀ γ : AlgebraicClosure ℚ_[ℓ],
        γ ^ 2 = algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) ((Fintype.card k : ℚ_[ℓ]) ^ n) →
          Even (((rationalFrobenius B S f ℓ n).charpoly.map
            (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))).rootMultiplicity γ)) :
    ∏ ν ∈ Finset.range (2 * n + 1),
        (Polynomial.aeval ((algebraMap ℚ_[ℓ] (RatFunc ℚ_[ℓ]) ((Fintype.card k : ℚ_[ℓ]) ^ n) *
          RatFunc.X)⁻¹) (rationalFrobeniusCharpolyReverse B S f ℓ ν)) ^ ((-1 : ℤ) ^ (ν + 1)) =
      (functionalEquationSign B S f ℓ n : RatFunc ℚ_[ℓ]) *
        (Fintype.card k : RatFunc ℚ_[ℓ]) ^ ((n : ℤ) * eulerCharacteristic B S f ℓ / 2) *
        RatFunc.X ^ eulerCharacteristic B S f ℓ *
        ∏ ν ∈ Finset.range (2 * n + 1),
          (algebraMap ℚ_[ℓ][X] (RatFunc ℚ_[ℓ]) (rationalFrobeniusCharpolyReverse B S f ℓ ν)) ^
            ((-1 : ℤ) ^ (ν + 1)) := by
  rw [eulerCharacteristic_eq_sum_natDegree B S f ℓ n]
  exact prod_aeval_inv_reverse_zpow_eq (L := AlgebraicClosure ℚ_[ℓ])
    (χ := fun ν => (rationalFrobenius B S f ℓ ν).charpoly) Fintype.card_ne_zero
    (fun ν => LinearMap.charpoly_monic _)
    (fun ν => coeff_zero_charpoly_rationalFrobenius_ne_zero B S f ℓ ν) hR1
    (fun h => ⟨by rw [← bettiNumber_eq_natDegree]; exact (hR2 h).1, (hR2 h).2⟩)

end FromDuality

/-! ### The general case -/

section General

variable [Fact (ℓ ≠ ringChar k)] (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The connected components of `S`, with the multiplicativity of the Frobenius characteristic
polynomials over them (purity of the components discharged by Deligne's theorem). -/
theorem exists_connectedComponents_charpoly_eq_prod' :
    ∃ (ι : Type u) (_ : Fintype ι) (Y : ι → B.Scheme) (g : ∀ i, (Y i).1 ⟶ Spec (.of k))
      (hg : ∀ i, IsProper (g i)), (∀ i, SmoothOfRelativeDimension n (g i)) ∧
      (∀ i, ConnectedSpace (Y i).1) ∧ ∀ ν, (rationalFrobenius B S f ℓ ν).charpoly =
        ∏ i, haveI := hg i; (rationalFrobenius B (Y i) (g i) ℓ ν).charpoly :=
  exists_connectedComponents_charpoly_eq_prod (ℓ := ℓ) B S f n
    fun _ g _ _ _ ν ι => isCharpolyPureOfWeight_rationalFrobenius B g ℓ ν ι

/-- **The `q^n`-duality relation between `F_ν` and `F_{2n-ν}`** (FK IV.1.6, characteristic
polynomial form) for `S` proper and smooth of relative dimension `n` over `k`: for `ν ≤ 2n`,
`det(T - F_{2n-ν}) = ∏ (T - q^n / μ)`, `μ` running over the eigenvalues of `F_ν` in `ℚ̄_ℓ` with
multiplicity. -/
@[weil "thm_ext_fk401_poincare_duality_frobenius"]
theorem isCharpolyDual_rationalFrobenius {ν : ℕ} (hν : ν ≤ 2 * n) :
    Weil.Polynomial.IsCharpolyDual (AlgebraicClosure ℚ_[ℓ]) ((Fintype.card k : ℚ_[ℓ]) ^ n)
      (rationalFrobenius B S f ℓ ν).charpoly (rationalFrobenius B S f ℓ (2 * n - ν)).charpoly := by
  obtain ⟨ι, _, Y, g, hg, hsm, hconn, hprod⟩ :=
    exists_connectedComponents_charpoly_eq_prod' B S f ℓ n
  rw [hprod ν, hprod (2 * n - ν)]
  refine Weil.Polynomial.IsCharpolyDual.prod (fun i _ => ?_) fun i _ => ?_
  · have := hg i
    exact (LinearMap.charpoly_monic _).ne_zero
  · have := hg i; have := hsm i; have := hconn i
    exact isCharpolyDual_rationalFrobenius_of_connectedSpace B (Y i) (g i) ℓ n hν

/-- **The middle cohomology for `n` odd** (FK IV.1.6, alternating form, its consequences): for `S`
proper and smooth of relative dimension `n` odd over `k`, `b_n` is even and every square root
`γ ∈ ℚ̄_ℓ` of `q^n` has even multiplicity as an eigenvalue of `F_n`. -/
@[weil "thm_ext_fk401_poincare_duality_middle_alternating"]
theorem even_bettiNumber_and_even_rootMultiplicity (hn : Odd n) :
    Even (bettiNumber B S f ℓ n) ∧
      ∀ γ : AlgebraicClosure ℚ_[ℓ],
        γ ^ 2 = algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) ((Fintype.card k : ℚ_[ℓ]) ^ n) →
          Even (((rationalFrobenius B S f ℓ n).charpoly.map
            (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))).rootMultiplicity γ) := by
  obtain ⟨ι, _, Y, g, hg, hsm, hconn, hprod⟩ :=
    exists_connectedComponents_charpoly_eq_prod' B S f ℓ n
  have hne : ∀ i ∈ (Finset.univ : Finset ι),
      (haveI := hg i; (rationalFrobenius B (Y i) (g i) ℓ n).charpoly) ≠ 0 := fun i _ => by
    have := hg i
    exact (LinearMap.charpoly_monic _).ne_zero
  have hY : ∀ i, Even (haveI := hg i; bettiNumber B (Y i) (g i) ℓ n) ∧
      ∀ γ : AlgebraicClosure ℚ_[ℓ],
        γ ^ 2 = algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) ((Fintype.card k : ℚ_[ℓ]) ^ n) →
          Even ((haveI := hg i; (rationalFrobenius B (Y i) (g i) ℓ n).charpoly.map
            (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))).rootMultiplicity γ) := fun i => by
    have := hg i; have := hsm i; have := hconn i
    exact even_bettiNumber_and_even_rootMultiplicity_of_connectedSpace B (Y i) (g i) ℓ n hn
  rw [bettiNumber_eq_natDegree, hprod n]
  refine ⟨Weil.Polynomial.even_natDegree_prod hne fun i _ => ?_,
    Weil.Polynomial.even_rootMultiplicity_prod_of_sq_eq hne fun i _ => (hY i).2⟩
  have := hg i
  rw [← bettiNumber_eq_natDegree]
  exact (hY i).1

end General

/-! ### The parity of `χ(S)` and the functional equation -/

section FunctionalEquation

variable [Fact (ℓ ≠ ringChar k)] {n : ℕ} [SmoothOfRelativeDimension n f]

omit [Fintype k] in
/-- **`χ(S)` is even for `n` odd** (FK IV.1): for `S` proper and smooth of relative dimension `n`
odd over `k`, the Euler characteristic `χ(S) = ∑_{ν ≤ 2n} (-1)^ν b_ν` is even. -/
@[weil "lem_fk401_euler_characteristic_parity"]
theorem even_eulerCharacteristic [Finite k] (hn : Odd n) : Even (eulerCharacteristic B S f ℓ) := by
  have := Fintype.ofFinite k
  have h := even_mul_eulerCharacteristic_of_isCharpolyDual B S f ℓ
    (fun _ hν => isCharpolyDual_rationalFrobenius B S f ℓ n hν)
    (fun h => (even_bettiNumber_and_even_rootMultiplicity B S f ℓ n h).1)
  rcases Int.even_mul.1 h with h | h
  · exact absurd h (Int.not_even_iff_odd.2 (by exact_mod_cast hn))
  · exact h

/-- **Deligne's functional equation of the zeta function** (FK IV.1): let `S` be proper and
smooth of relative dimension `n` over the finite field `k` with `q` elements (FK: `S₀` smooth
projective of pure dimension `n`), `ℓ ∤ q`, `χ = χ(S)`, `ε` the sign of
`Weil.functionalEquationSign` and `P_ν(t) = det(1 - t F_ν | H^ν(S_k̄, ℚ_ℓ))`. Then `n χ` is even
and, in `ℚ_ℓ(t)`,
`∏_{ν ≤ 2n} P_ν(1 / (q^n t)) ^ (-1)^(ν+1) = ε q^(n χ / 2) t^χ ∏_{ν ≤ 2n} P_ν(t) ^ (-1)^(ν+1)`,
that is, `Z(1 / (q^n t)) = ε q^(n χ / 2) t^χ Z(t)`. -/
@[weil "thm_fk401_deligne_functional_equation"]
theorem prod_aeval_inv_rationalFrobeniusCharpolyReverse_zpow_eq :
    Even ((n : ℤ) * eulerCharacteristic B S f ℓ) ∧
    ∏ ν ∈ Finset.range (2 * n + 1),
        (Polynomial.aeval ((algebraMap ℚ_[ℓ] (RatFunc ℚ_[ℓ]) ((Fintype.card k : ℚ_[ℓ]) ^ n) *
          RatFunc.X)⁻¹) (rationalFrobeniusCharpolyReverse B S f ℓ ν)) ^ ((-1 : ℤ) ^ (ν + 1)) =
      (functionalEquationSign B S f ℓ n : RatFunc ℚ_[ℓ]) *
        (Fintype.card k : RatFunc ℚ_[ℓ]) ^ ((n : ℤ) * eulerCharacteristic B S f ℓ / 2) *
        RatFunc.X ^ eulerCharacteristic B S f ℓ *
        ∏ ν ∈ Finset.range (2 * n + 1),
          (algebraMap ℚ_[ℓ][X] (RatFunc ℚ_[ℓ]) (rationalFrobeniusCharpolyReverse B S f ℓ ν)) ^
            ((-1 : ℤ) ^ (ν + 1)) :=
  ⟨even_mul_eulerCharacteristic_of_isCharpolyDual B S f ℓ
      (fun _ hν => isCharpolyDual_rationalFrobenius B S f ℓ n hν)
      (fun h => (even_bettiNumber_and_even_rootMultiplicity B S f ℓ n h).1),
    prod_aeval_inv_rationalFrobeniusCharpolyReverse_zpow_eq_of_isCharpolyDual B S f ℓ
      (fun _ hν => isCharpolyDual_rationalFrobenius B S f ℓ n hν)
      (fun h => even_bettiNumber_and_even_rootMultiplicity B S f ℓ n h)⟩

end FunctionalEquation

end Weil

end
