import Tao2026.BurgessWeilPrimeKummerHasseDavenportIrreducibleFactorization
import Mathlib.FieldTheory.Finite.Extension

/-!
# Minimal-polynomial fibers in finite extensions

This file identifies the closed-point divisor sum from the finite
irreducible Euler product with the norm/trace Gauss sum over a finite field
extension. The key input is the exact cardinality of a minimal-polynomial
fiber: a monic irreducible polynomial of degree `d` occurs for exactly `d`
extension elements when `d` divides the extension degree, and not at all
otherwise.
-/

open Polynomial Classical
open scoped BigOperators

noncomputable section

namespace Tao2026

/-- The minimal polynomial of an extension element, packaged in the bounded
irreducible alphabet at the extension degree. -/
def hasseDavenportMinpolyIrreducibleUpTo
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L] (x : L) :
    HasseDavenportIrreduciblePolynomialUpTo K (Module.finrank K L) := by
  have hx : IsIntegral K x := IsIntegral.of_finite K x
  exact ⟨⟨(minpoly K x).natDegree,
      Nat.lt_succ_iff.mpr (minpoly.natDegree_le x)⟩,
    ⟨⟨minpoly K x, minpoly.monic hx, rfl⟩, minpoly.irreducible hx⟩⟩

@[simp] theorem hasseDavenportMinpolyIrreducibleUpTo_polynomial
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L] (x : L) :
    hasseDavenportIrreduciblePolynomial
      (hasseDavenportMinpolyIrreducibleUpTo K L x) = minpoly K x := rfl

@[simp] theorem hasseDavenportMinpolyIrreducibleUpTo_degree
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L] (x : L) :
    hasseDavenportIrreducibleDegree
      (hasseDavenportMinpolyIrreducibleUpTo K L x) =
        (minpoly K x).natDegree := rfl

/-- The relative multiplicity of a closed point is total extension degree
divided by its minimal-polynomial degree. -/
theorem finrank_adjoin_eq_extensionDegree_div_minpolyDegree
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L] (x : L) :
    Module.finrank (IntermediateField.adjoin K {x}) L =
      Module.finrank K L / (minpoly K x).natDegree := by
  have hx : IsIntegral K x := IsIntegral.of_finite K x
  have hmul := Module.finrank_mul_finrank K (IntermediateField.adjoin K {x}) L
  rw [IntermediateField.adjoin.finrank hx] at hmul
  have hdegreepos : 0 < (minpoly K x).natDegree :=
    (minpoly.monic hx).natDegree_pos_of_not_isUnit
      (minpoly.irreducible hx).not_isUnit
  apply Nat.eq_div_of_mul_eq_left hdegreepos.ne'
  simpa [mul_comm] using hmul

/-- Elements with a prescribed monic irreducible minimal polynomial are
equivalent to its roots in the extension field. -/
def hasseDavenportMinpolyFiberEquivAroots
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L]
    (q : HasseDavenportMonicIrreduciblePolynomialAny K) :
    {x : L // minpoly K x = q.1} ≃ {x : L // x ∈ q.1.aroots L} :=
  Equiv.subtypeEquiv (Equiv.refl L) (fun x => by
    constructor
    · intro hx
      rw [← hx]
      exact Polynomial.mem_aroots.mpr
        ⟨minpoly.ne_zero (IsIntegral.of_finite K x), minpoly.aeval K x⟩
    · intro hx
      have h := minpoly.eq_of_irreducible q.2.2
        (Polynomial.mem_aroots.mp hx).2
      simpa [q.2.1.leadingCoeff] using h.symm)

/-- The exact cardinality of a minimal-polynomial fiber in a finite field
extension. -/
theorem card_hasseDavenportMinpolyFiber
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L]
    (q : HasseDavenportMonicIrreduciblePolynomialAny K) :
    Fintype.card {x : L // minpoly K x = q.1} =
      if q.1.natDegree ∣ Module.finrank K L then q.1.natDegree else 0 := by
  letI : Fact (Irreducible q.1) := ⟨q.2.2⟩
  let pb := AdjoinRoot.powerBasis q.2.2.ne_zero
  letI : Fintype (AdjoinRoot q.1) :=
    Fintype.ofEquiv (Fin pb.dim → K) pb.basis.equivFun.symm.toEquiv
  have hfinrank : Module.finrank K (AdjoinRoot q.1) = q.1.natDegree := by
    rw [pb.finrank]
    rfl
  rw [Fintype.card_congr (hasseDavenportMinpolyFiberEquivAroots K L q)]
  rw [← Fintype.card_congr (AdjoinRoot.equiv L K q.1 q.2.2.ne_zero)]
  by_cases hdiv : q.1.natDegree ∣ Module.finrank K L
  · rw [if_pos hdiv, FiniteField.card_algHom_of_finrank_dvd]
    · exact hfinrank
    · rwa [hfinrank]
  · rw [if_neg hdiv]
    have hempty : IsEmpty (AdjoinRoot q.1 →ₐ[K] L) := by
      rw [isEmpty_iff]
      intro h
      apply hdiv
      rw [← hfinrank]
      exact FiniteField.nonempty_algHom_iff_finrank_dvd.mp ⟨h⟩
    exact Fintype.card_eq_zero

theorem hasseDavenportMinpolyIrreducibleUpTo_eq_iff
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L] (x : L)
    (q : HasseDavenportIrreduciblePolynomialUpTo K (Module.finrank K L)) :
    hasseDavenportMinpolyIrreducibleUpTo K L x = q ↔
      minpoly K x = hasseDavenportIrreduciblePolynomial q := by
  constructor
  · intro h
    exact congrArg hasseDavenportIrreduciblePolynomial h
  · intro h
    apply hasseDavenportIrreducibleAnyOfUpTo_injective
    apply Subtype.ext
    simpa using h

/-- Finset form of the exact minimal-polynomial fiber count. -/
theorem card_filter_minpoly_eq_irreducible
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L]
    (q : HasseDavenportIrreduciblePolynomialUpTo K (Module.finrank K L)) :
    (Finset.univ.filter
      (fun x : L => minpoly K x = hasseDavenportIrreduciblePolynomial q)).card =
      if hasseDavenportIrreducibleDegree q ∣ Module.finrank K L then
        hasseDavenportIrreducibleDegree q else 0 := by
  let s := Finset.univ.filter
    (fun x : L => minpoly K x = hasseDavenportIrreduciblePolynomial q)
  let e : ↥s ≃
      {x : L // minpoly K x = hasseDavenportIrreduciblePolynomial q} :=
    { toFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
      invFun := fun x =>
        ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    (Finset.univ.filter
      (fun x : L => minpoly K x = hasseDavenportIrreduciblePolynomial q)).card =
        Fintype.card ↥s := by
      exact (Fintype.card_coe s).symm
    _ = Fintype.card
        {x : L // minpoly K x = hasseDavenportIrreduciblePolynomial q} :=
      Fintype.card_congr e
    _ = if hasseDavenportIrreducibleDegree q ∣ Module.finrank K L then
        hasseDavenportIrreducibleDegree q else 0 := by
      rw [← hasseDavenportIrreduciblePolynomial_natDegree q]
      simpa [hasseDavenportIrreducibleAnyOfUpTo,
        hasseDavenportIrreduciblePolynomial,
        hasseDavenportIrreducibleDegree] using
        card_hasseDavenportMinpolyFiber K L
          (hasseDavenportIrreducibleAnyOfUpTo q)

/-- Regroup the minimal-polynomial sum by its bounded irreducible fibers. -/
theorem sum_minpolyWeight_pow_eq_irreducibleSum
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) :
    (∑ x : L, hasseDavenportMonicWeight χ ψ (minpoly K x) ^
        Module.finrank (IntermediateField.adjoin K {x}) L) =
      ∑ q : HasseDavenportIrreduciblePolynomialUpTo K (Module.finrank K L),
        if hasseDavenportIrreducibleDegree q ∣ Module.finrank K L then
          (hasseDavenportIrreducibleDegree q : ℂ) *
            hasseDavenportIrreducibleWeight χ ψ q ^
              (Module.finrank K L / hasseDavenportIrreducibleDegree q)
        else 0 := by
  let g : L → HasseDavenportIrreduciblePolynomialUpTo K (Module.finrank K L) :=
    hasseDavenportMinpolyIrreducibleUpTo K L
  let f : L → ℂ := fun x =>
    hasseDavenportMonicWeight χ ψ (minpoly K x) ^
      Module.finrank (IntermediateField.adjoin K {x}) L
  calc
    (∑ x : L, hasseDavenportMonicWeight χ ψ (minpoly K x) ^
        Module.finrank (IntermediateField.adjoin K {x}) L) =
        ∑ q : HasseDavenportIrreduciblePolynomialUpTo K (Module.finrank K L),
          ∑ x ∈ (Finset.univ : Finset L) with g x = q, f x := by
      symm
      exact Finset.sum_fiberwise Finset.univ g f
    _ = ∑ q : HasseDavenportIrreduciblePolynomialUpTo K (Module.finrank K L),
        if hasseDavenportIrreducibleDegree q ∣ Module.finrank K L then
          (hasseDavenportIrreducibleDegree q : ℂ) *
            hasseDavenportIrreducibleWeight χ ψ q ^
              (Module.finrank K L / hasseDavenportIrreducibleDegree q)
        else 0 := by
      apply Finset.sum_congr rfl
      intro q _hq
      let c : ℂ := hasseDavenportIrreducibleWeight χ ψ q ^
        (Module.finrank K L / hasseDavenportIrreducibleDegree q)
      have hconstant :
          (∑ x ∈ (Finset.univ : Finset L) with g x = q, f x) =
            ∑ _x ∈ (Finset.univ : Finset L) with g _x = q, c := by
        apply Finset.sum_congr rfl
        intro x hx
        have hg : g x = q := (Finset.mem_filter.mp hx).2
        have hpoly : minpoly K x = hasseDavenportIrreduciblePolynomial q :=
          (hasseDavenportMinpolyIrreducibleUpTo_eq_iff K L x q).mp hg
        dsimp [f, c]
        rw [finrank_adjoin_eq_extensionDegree_div_minpolyDegree,
          hpoly, hasseDavenportIrreduciblePolynomial_natDegree]
        rfl
      rw [hconstant]
      rw [Finset.sum_const]
      rw [nsmul_eq_mul]
      have hfilter :
          (Finset.univ : Finset L).filter (fun x => g x = q) =
            Finset.univ.filter
              (fun x : L => minpoly K x = hasseDavenportIrreduciblePolynomial q) := by
        apply Finset.ext
        intro x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hasseDavenportMinpolyIrreducibleUpTo_eq_iff K L x q
      rw [hfilter, card_filter_minpoly_eq_irreducible K L q]
      by_cases hdiv : hasseDavenportIrreducibleDegree q ∣ Module.finrank K L
      · simp [hdiv, c]
      · simp [hdiv, c]

theorem sum_minpolyWeight_pow_eq_degreeSum
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) :
    (∑ x : L, hasseDavenportMonicWeight χ ψ (minpoly K x) ^
        Module.finrank (IntermediateField.adjoin K {x}) L) =
      ∑ d : Fin (Module.finrank K L + 1),
        if d.1 ∣ Module.finrank K L then
          (d.1 : ℂ) *
            ∑ q : HasseDavenportMonicIrreduciblePolynomial K d.1,
              hasseDavenportMonicWeight χ ψ q.1.1 ^
                (Module.finrank K L / d.1)
        else 0 := by
  rw [sum_minpolyWeight_pow_eq_irreducibleSum]
  simp only [HasseDavenportIrreduciblePolynomialUpTo]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdiv : d.1 ∣ Module.finrank K L
  · simp only [hdiv, if_pos]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    simp [hasseDavenportIrreducibleDegree,
      hasseDavenportIrreducibleWeight,
      hasseDavenportIrreduciblePolynomial, hdiv]
  · simp [hasseDavenportIrreducibleDegree, hdiv]

/-- The norm/trace Gauss sum over every positive-degree finite-field
extension satisfies the exact Hasse--Davenport signed-power identity. -/
theorem gaussSum_normTraceLift_eq_signedGaussPower
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (hχ : χ ≠ 1) :
    gaussSum (finiteFieldNormLiftMulChar K L χ)
        (finiteFieldTraceLiftAddChar K L ψ) =
      (-1 : ℂ) ^ (Module.finrank K L - 1) *
        gaussSum χ ψ ^ Module.finrank K L := by
  rw [gaussSum_normTraceLift_eq_sum_minpolyWeight_pow]
  rw [sum_minpolyWeight_pow_eq_degreeSum]
  have hrankpos : 0 < Module.finrank K L := Module.finrank_pos
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hrankpos.ne'
  rw [hn]
  simpa using
    (hasseDavenportIrreducibleDegreeSum_eq_signedGaussPower
      K χ ψ hχ (n + 1) n (by omega))

/-- Universal finite-field Hasse--Davenport, discharged by the internal
monic-polynomial Euler-product proof. -/
theorem taoFiniteFieldGaussHasseDavenport :
    TaoFiniteFieldGaussHasseDavenport := by
  intro K L _ _ _ _ p _ _ _ _ χ ψ hχ _hψ
  exact gaussSum_normTraceLift_eq_signedGaussPower K L χ ψ hχ

/-- The exact prime-field Gauss-lifting proposition required by the Kummer
argument is unconditional. -/
theorem taoPrimeFieldGaussHasseDavenport :
    TaoPrimeFieldGaussHasseDavenport :=
  TaoFiniteFieldGaussHasseDavenport.toPrimeField
    taoFiniteFieldGaussHasseDavenport

theorem taoPrimeFieldJacobiHasseDavenport :
    TaoPrimeFieldJacobiHasseDavenport :=
  TaoPrimeFieldGaussHasseDavenport.toJacobi
    taoPrimeFieldGaussHasseDavenport

/-- The entire zero-, one-, and two-active-root Kummer Frobenius system is
now unconditional. -/
theorem taoPrimeKummerIsotypicFrobeniusSystemTwoRoots :
    TaoPrimeKummerIsotypicFrobeniusSystemTwoRoots :=
  TaoPrimeFieldGaussHasseDavenport.toTwoRoots
    taoPrimeFieldGaussHasseDavenport

end Tao2026
