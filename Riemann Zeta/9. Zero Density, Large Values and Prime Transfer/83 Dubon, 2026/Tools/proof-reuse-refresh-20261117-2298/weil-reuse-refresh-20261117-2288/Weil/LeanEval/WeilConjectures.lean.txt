module

public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.WeilRiemannHypothesisForm
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.DeligneFunctionalEquation
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import StacksFrontier.RingTheory.PowerSeries.ZetaRationality
public import Weil.Attr

/-!
# The Weil conjectures in the form of the LeanEval problem `weil_conjectures`

The statement of the LeanEval benchmark problem `weil_conjectures`
(`LeanEval/AlgebraicGeometry/WeilConjectures.lean` of `leanprover/lean-eval`), verbatim: for `X`
smooth of relative dimension `d`, proper and geometrically irreducible over the finite field `F`,
there are multisets `A_i ⊆ ℂ` with `A_0 = {1}`, `A_{2d-i} = q^d / A_i`, stable under every
automorphism of `ℂ`, of algebraic integers of absolute value `q ^ (i / 2)`, such that
`#X(E) = ∑_{i ≤ 2d} (-1)^i ∑_{α ∈ A_i} α^m` for every extension `E / F` of degree `m`.

## Main results

* `LeanEval.AlgebraicGeometry.WeilConjectures.weil_conjectures`: the statement.

## Implementation notes

`A_i` is the image, under a ring homomorphism `ι : ℚ̄_ℓ → ℂ`, of the multiset of eigenvalues of
the Frobenius `F_i` on `H^i(X_F̄, ℚ_ℓ)`, for a prime `ℓ ≠ char F`; equivalently the multiset of
complex roots of the integer polynomial `det(t - F_i)`. Duality is
`Weil.isCharpolyDual_rationalFrobenius`, the absolute values `Weil.satisfiesWeilEstimate`
(Deligne), integrality `Weil.exists_map_int_eq_rationalFrobeniusCharpolyReverse`, and the point
counts come from the factorization of the zeta series
(`Weil.isWeilZetaFactorization_of_map_int`) by taking logarithmic derivatives.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace LeanEval.AlgebraicGeometry.WeilConjectures

open Polynomial

section Reverse

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
/-- The reverse of the reverse of a polynomial with nonzero constant coefficient is itself. -/
theorem reverse_reverse_of_coeff_zero_ne_zero {p : R[X]} (hp : p.coeff 0 ≠ 0) :
    p.reverse.reverse = p := by
  have h0 : p.natTrailingDegree = 0 := natTrailingDegree_eq_zero.2 (Or.inr hp)
  change reflect p.reverse.natDegree p.reverse = p
  rw [reverse_natDegree, h0, Nat.sub_zero, reverse, reflect_reflect]

omit [IsDomain R] in
/-- Reversing commutes with an injective change of coefficients. -/
theorem reverse_map_of_injective {S : Type*} [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) (p : R[X]) : (p.map φ).reverse = p.reverse.map φ := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hφ, reflect_map]

/-- The reverse of `∏ (X - a)` is `∏ (1 - a X)`. -/
theorem reverse_multiset_prod_X_sub_C (s : Multiset R) :
    ((s.map fun a => Polynomial.X - C a).prod).reverse =
      (s.map fun a => 1 - C a * Polynomial.X).prod := by
  have h1 : (1 : R[X]).reverse = 1 := by simpa using reverse_C (1 : R)
  induction s using Multiset.induction_on with
  | empty => simpa using h1
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, ih, Multiset.map_cons,
      Multiset.prod_cons]
    congr 1
    have hX : (Polynomial.X : R[X]).reverse = 1 := by
      rw [← one_mul Polynomial.X, reverse_mul_X, h1]
    rw [sub_eq_add_neg, ← C_neg, reverse_add_C, hX, natDegree_X, pow_one, C_neg]
    ring

end Reverse

section LogDerivative

open PowerSeries in
/-- The coefficient of `t ^ m`, `m ≠ 0`, of the logarithmic derivative of `∏_{a ∈ s} (1 - a t)`
is `-∑_{a ∈ s} a ^ m`. -/
theorem coeff_logDerivative_multiset_prod_one_sub_C_mul_X {R : Type*} [CommRing R]
    (s : Multiset R) {m : ℕ} (hm : m ≠ 0) :
    PowerSeries.coeff m (logDerivative (s.map fun a => (1 - PowerSeries.C a * PowerSeries.X :
      R⟦X⟧)).prod) = -(s.map (· ^ m)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have h1 : PowerSeries.constantCoeff (1 - PowerSeries.C a * PowerSeries.X : R⟦X⟧) = 1 := by
      simp
    have h2 : PowerSeries.constantCoeff
        (s.map fun a => (1 - PowerSeries.C a * PowerSeries.X : R⟦X⟧)).prod = 1 := by
      rw [map_multiset_prod, Multiset.map_map]
      simp
    rw [Multiset.map_cons, Multiset.prod_cons, logDerivative_mul h1 h2, map_add, ih,
      coeff_logDerivative_one_sub_C_mul_X]
    simp only [hm, ↓reduceIte, Multiset.map_cons, Multiset.sum_cons]
    ring

end LogDerivative

section PointCount

variable {k : Type*} [Field k] [Finite k] {Y : Scheme} (g : Y ⟶ Spec (.of k))

/-- **Point counts from a factorization of the zeta series.** If
`f_Y · ∏_{j ≤ D even} P_j = ∏_{j ≤ D odd} P_j` with `P_j = ∏_{α ∈ A_j} (1 - α t)` over `ℂ`, then
`#Y(k_m) = ∑_{j ≤ D} (-1)^j ∑_{α ∈ A_j} α^m` for every `m ≥ 1`. -/
theorem pointCountOfDegree_eq_sum_of_zetaSeries_mul_eq (D : ℕ) (P : ℕ → ℤ[X])
    (A : ℕ → Multiset ℂ)
    (hPA : ∀ j ≤ D,
      (P j).map (Int.castRingHom ℂ) = ((A j).map fun a => 1 - C a * Polynomial.X).prod)
    (hZ : zetaSeries g * ∏ j ∈ (Finset.range (D + 1)).filter Even,
          (((P j).map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) =
        ∏ j ∈ (Finset.range (D + 1)).filter (¬ Even ·),
          (((P j).map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ))
    (m : ℕ) [NeZero m] :
    (pointCountOfDegree g m : ℂ) =
      ∑ j ∈ Finset.range (D + 1), (-1) ^ j * ((A j).map (· ^ m)).sum := by
  set G : ℕ → PowerSeries ℂ := fun j =>
    ((A j).map fun a => (1 - PowerSeries.C a * PowerSeries.X : PowerSeries ℂ)).prod with hG
  have hGc : ∀ j, PowerSeries.constantCoeff (G j) = 1 := by
    intro j
    rw [hG, map_multiset_prod, Multiset.map_map]
    simp
  have hmap : ∀ j ≤ D, PowerSeries.map (algebraMap ℚ ℂ)
      (((P j).map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) = G j := by
    intro j hj
    rw [← Polynomial.polynomial_map_coe, Polynomial.map_map,
      show (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ from RingHom.ext_int _ _,
      hPA j hj, hG]
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp [Polynomial.coe_C, Polynomial.coe_X]
  have hZc := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) hZ
  rw [map_mul, map_prod, map_prod,
    Finset.prod_congr rfl fun j hj => hmap j (by simp at hj; omega),
    Finset.prod_congr rfl fun j hj => hmap j (by simp at hj; omega)] at hZc
  have hZ1 : PowerSeries.constantCoeff (PowerSeries.map (algebraMap ℚ ℂ) (zetaSeries g)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_zetaSeries, map_one]
  have hprod1 : ∀ s : Finset ℕ, PowerSeries.constantCoeff (∏ j ∈ s, G j) = 1 := by
    intro s
    rw [map_prod]
    exact Finset.prod_eq_one fun j _ => hGc j
  have hL := congrArg (fun u => PowerSeries.coeff m (PowerSeries.logDerivative u)) hZc
  beta_reduce at hL
  rw [PowerSeries.logDerivative_mul hZ1 (hprod1 _),
    PowerSeries.logDerivative_finsetProd _ _ fun j _ => hGc j,
    PowerSeries.logDerivative_finsetProd _ _ fun j _ => hGc j,
    PowerSeries.logDerivative_map _ (constantCoeff_zetaSeries g), logDerivative_zetaSeries,
    map_add, map_sum, map_sum, PowerSeries.coeff_map, coeff_pointCountSeries] at hL
  have hm : m ≠ 0 := NeZero.ne m
  simp only [hG, coeff_logDerivative_multiset_prod_one_sub_C_mul_X _ hm, Finset.sum_neg_distrib,
    map_natCast] at hL
  rw [← Finset.sum_filter_add_sum_filter_not _ Even]
  have he : ∀ j ∈ (Finset.range (D + 1)).filter Even,
      (-1 : ℂ) ^ j * ((A j).map (· ^ m)).sum = ((A j).map (· ^ m)).sum := by
    intro j hj
    rw [(Finset.mem_filter.1 hj).2.neg_one_pow, one_mul]
  have ho : ∀ j ∈ (Finset.range (D + 1)).filter (¬ Even ·),
      (-1 : ℂ) ^ j * ((A j).map (· ^ m)).sum = -((A j).map (· ^ m)).sum := by
    intro j hj
    rw [(Nat.not_even_iff_odd.1 (Finset.mem_filter.1 hj).2).neg_one_pow, neg_one_mul]
  rw [Finset.sum_congr rfl he, Finset.sum_congr rfl ho, Finset.sum_neg_distrib]
  linear_combination hL

end PointCount

/-- The morphisms `Spec E ⟶ X` in `Over (Spec F)` are the `E`-valued points of `X`. -/
def overHomEquivFieldValuedPoints {F : Type u} [Field F] (X : Over (Spec (.of F))) (E : Type u)
    [Field E] [Algebra F E] :
    (Over.mk (Spec.map <| CommRingCat.ofHom <| algebraMap F E) ⟶ X) ≃
      Stacks.EtaleCohomology.fieldValuedPoints X.hom E where
  toFun u := ⟨u.left, by simp [Over.w u]⟩
  invFun x := Over.homMk x.1 x.2
  left_inv u := by ext; rfl
  right_inv x := rfl

/-- **The Weil conjectures** (LeanEval problem `weil_conjectures`, verbatim). -/
theorem weil_conjectures (F : Type*) [Finite F] [Field F]
    (X : Over (Spec (.of F))) [GeometricallyIrreducible X.hom] [IsProper X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    ∃ A : ℕ → Multiset ℂ, A 0 = {1} ∧
      (∀ i ≤ 2 * d, A (2 * d - i) = (A i).map (Nat.card F ^ d / · : ℂ → ℂ) ∧
        (∀ φ : ℂ ≃+* ℂ, (A i).map φ = A i) ∧
        ∀ α ∈ A i, IsIntegral ℤ α ∧ ‖α‖ = √(Nat.card F ^ i)) ∧
      ∀ (E : Type _) [Field E] [Algebra F E] [FiniteDimensional F E],
        Nat.card (.mk (Spec.map <| CommRingCat.ofHom <| algebraMap F E) ⟶ X) =
        ∑ i ∈ Finset.Iic (2 * d), (-1) ^ i * ((A i).map (· ^ Module.finrank F E)).sum := by
  classical
  have := Fintype.ofFinite F
  let f : X.left ⟶ Spec (.of F) := X.hom
  have : IsProper f := ‹IsProper X.hom›
  have : SmoothOfRelativeDimension d f := ‹SmoothOfRelativeDimension d X.hom›
  have : GeometricallyIrreducible f := ‹GeometricallyIrreducible X.hom›
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  let B := AlgebraicGeometry.BigEtaleSite.containing X.left
  let S : B.Scheme := ⟨X.left, AlgebraicGeometry.BigEtaleSite.contains_containing X.left⟩
  -- a prime `ℓ ≠ char F`
  obtain ⟨ℓ, hℓle, hℓ⟩ := Nat.exists_infinite_primes (ringChar F + 1)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact (ℓ ≠ ringChar F) := ⟨by omega⟩
  choose P hP using Weil.exists_map_int_eq_rationalFrobeniusCharpolyReverse B S (f := f) ℓ
  have hW := Weil.isWeilZetaFactorization_of_map_int B S f ℓ d P hP
  -- an embedding `ι : ℚ̄_ℓ → ℂ`
  let L := AlgebraicClosure ℚ_[ℓ]
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] L).injective
  have hLc : Cardinal.mk L ≤ Cardinal.continuum := by
    have : Algebra.IsAlgebraic ℚ_[ℓ] L := IsAlgClosure.isAlgebraic
    have h := Algebra.IsAlgebraic.lift_cardinalMk_le_max ℚ_[ℓ] L
    rw [← Cardinal.lift_le_continuum.{0, 0}]
    refine h.trans (max_le ?_ Cardinal.aleph0_le_continuum)
    exact Cardinal.lift_le_continuum.2 (Padic.cardinalMk_le_continuum ℓ)
  obtain ⟨ι, -⟩ := RingHom.exists_comp_algebraMap_eq_of_countable (K := ℚ) hLc (algebraMap ℚ ℂ)
  -- the characteristic polynomials `χ_j = det(t - F_j)` and their integer forms
  set χ : ℕ → ℚ_[ℓ][X] := fun j => (Weil.rationalFrobenius B S f ℓ j).charpoly with hχ
  have hχ0 : ∀ j, (χ j).coeff 0 ≠ 0 := fun j =>
    Weil.coeff_zero_charpoly_rationalFrobenius_ne_zero B S f ℓ j
  have hχm : ∀ j, (χ j).Monic := fun j => LinearMap.charpoly_monic _
  have hinjℓ : Function.Injective (Int.castRingHom ℚ_[ℓ]) := RingHom.injective_int _
  set Q : ℕ → ℤ[X] := fun j => (P j).reverse with hQdef
  have hQ : ∀ j, (Q j).map (Int.castRingHom ℚ_[ℓ]) = χ j := by
    intro j
    rw [hQdef, ← reverse_map_of_injective hinjℓ, hP j, Weil.rationalFrobeniusCharpolyReverse,
      reverse_reverse_of_coeff_zero_ne_zero (hχ0 j)]
  have hQm : ∀ j, (Q j).Monic := by
    intro j
    have h := (hχm j).leadingCoeff
    rw [← hQ j, leadingCoeff_map_of_injective hinjℓ] at h
    exact Int.cast_injective (α := ℚ_[ℓ]) (by simpa using h)
  -- the multisets `A_j`
  set A : ℕ → Multiset ℂ := fun j => ((χ j).map (algebraMap ℚ_[ℓ] L)).roots.map ι with hA
  have hsplit : ∀ j, (χ j).map (algebraMap ℚ_[ℓ] L) =
      (((χ j).map (algebraMap ℚ_[ℓ] L)).roots.map fun a => Polynomial.X - C a).prod := fun j =>
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq ((hχm j).map _)
      IsAlgClosed.card_roots_eq_natDegree).symm
  have hQC : ∀ j, (Q j).map (Int.castRingHom ℂ) = ((A j).map fun a => Polynomial.X - C a).prod := by
    intro j
    have : Int.castRingHom ℂ = (ι.comp (algebraMap ℚ_[ℓ] L)).comp (Int.castRingHom ℚ_[ℓ]) :=
      RingHom.ext_int _ _
    rw [this, ← Polynomial.map_map, ← Polynomial.map_map, hQ j, hsplit j,
      Polynomial.map_multiset_prod, Multiset.map_map, hA, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp
  have hAroots : ∀ j, A j = ((Q j).map (Int.castRingHom ℂ)).roots := fun j => by
    rw [hQC j, roots_multiset_prod_X_sub_C]
  have hPC : ∀ j ≤ 2 * d, (P j).map (Int.castRingHom ℂ) =
      ((A j).map fun a => 1 - C a * Polynomial.X).prod := by
    intro j hj
    have hP0 : (P j).coeff 0 ≠ 0 := by rw [hW.1 j hj]; exact one_ne_zero
    rw [← reverse_reverse_of_coeff_zero_ne_zero hP0,
      ← reverse_map_of_injective (RingHom.injective_int _)]
    change ((Q j).map (Int.castRingHom ℂ)).reverse = _
    rw [hQC j, reverse_multiset_prod_X_sub_C]
  refine ⟨A, ?_, fun i hi => ⟨?_, fun φ => ?_, fun α hα => ⟨?_, ?_⟩⟩, fun E _ _ _ => ?_⟩
  · -- `A_0 = {1}`
    have hQ0 : Q 0 = Polynomial.X - C 1 := by
      rw [hQdef]
      simp only
      rw [hW.2.1, sub_eq_neg_add, ← C_1, reverse_add_C, reverse_neg, natDegree_neg, natDegree_X,
        pow_one]
      have hX : (Polynomial.X : ℤ[X]).reverse = 1 := by
        rw [← one_mul Polynomial.X, reverse_mul_X]
        simpa using reverse_C (1 : ℤ)
      rw [hX]
      simp
      ring
    rw [hAroots 0, hQ0]
    simpa using roots_X_sub_C (1 : ℂ)
  · -- duality
    have hdual := Weil.isCharpolyDual_rationalFrobenius B S f ℓ d hi
    unfold Weil.Polynomial.IsCharpolyDual at hdual
    rw [hA]
    simp only
    rw [show (Weil.rationalFrobenius B S f ℓ (2 * d - i)).charpoly = χ (2 * d - i) from rfl,
      show (Weil.rationalFrobenius B S f ℓ i).charpoly = χ i from rfl] at hdual
    have h := roots_multiset_prod_X_sub_C (((χ i).map (algebraMap ℚ_[ℓ] L)).roots.map
      fun μ => algebraMap ℚ_[ℓ] L ((Fintype.card F : ℚ_[ℓ]) ^ d) / μ)
    rw [Multiset.map_map, Function.comp_def] at h
    rw [hdual, h, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun a _ => ?_
    simp
  · -- stability under automorphisms of `ℂ`
    have h := roots_map_of_injective_of_card_eq_natDegree (f := (φ : ℂ →+* ℂ)) φ.injective
      (IsAlgClosed.card_roots_eq_natDegree (p := (Q i).map (Int.castRingHom ℂ)))
    rw [RingEquiv.coe_toRingHom] at h
    rw [hAroots i, h, Polynomial.map_map]
    congr 2
    exact RingHom.ext_int _ _
  · -- integrality
    rw [hAroots i] at hα
    refine ⟨Q i, hQm i, ?_⟩
    have h := (mem_roots ((hQm i).map _).ne_zero).1 hα
    rwa [IsRoot, Polynomial.eval_map, ← algebraMap_int_eq] at h
  · -- the absolute values (Deligne)
    obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.1 hα
    have hμ' : aeval μ (χ i) = 0 := by
      have h := (mem_roots ((hχm i).map _).ne_zero).1 hμ
      rwa [IsRoot, Polynomial.eval_map, ← aeval_def] at h
    have h := (Weil.satisfiesWeilEstimate B S f (ℓ := ℓ) i μ hμ').2
      (ι.comp (IntermediateField.adjoin ℚ {μ}).val.toRingHom)
    rw [RingHom.comp_apply] at h
    have hval : (IntermediateField.adjoin ℚ {μ}).val (IntermediateField.AdjoinSimple.gen ℚ μ) =
      μ := rfl
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hval] at h
    rw [h, Nat.card_eq_fintype_card, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  · -- the point counts
    have hm : Module.finrank F E ≠ 0 := Module.finrank_pos.ne'
    have : NeZero (Module.finrank F E) := ⟨hm⟩
    rw [Nat.card_congr (overHomEquivFieldValuedPoints X E)]
    have h1 : Nat.card (Stacks.EtaleCohomology.fieldValuedPoints X.hom E) =
        pointCountOfDegree f (Module.finrank F E) :=
      (pointCountOfDegree_eq_pointCount f E rfl).symm
    rw [h1, pointCountOfDegree_eq_sum_of_zetaSeries_mul_eq f (2 * d) P A hPC hW.2.2.2.2]
    congr 1
    ext j
    simp only [Finset.mem_range, Finset.mem_Iic]
    omega

end LeanEval.AlgebraicGeometry.WeilConjectures
