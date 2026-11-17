module

public import Weil.Attr
public import Weil.Definitions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Algebra.Field.ULift

/-!
# The number of points of a scheme over a finite field

Let `k` be a finite field, `X` a scheme over `k` with structure morphism `f : X ⟶ Spec k`, and
`n ≥ 1`. Writing `k_n` for an extension of `k` of degree `n`, the set
`X(k_n) = Hom_{Spec k}(Spec k_n, X)` of `k_n`-valued points is
`Stacks.EtaleCohomology.fieldValuedPoints f k_n`, and the `n`-th point count of `X` is its
cardinality `A_n = #X(k_n) ∈ ℕ`, taken to be `0` when the set is infinite (for `X` of finite type
over `k` it is always finite).

The count does not depend on the chosen extension: two extensions of `k` of degree `n` are
isomorphic over `k`, and a `k`-isomorphism `K ≃ₐ[k] L` induces a bijection `X(K) ≃ X(L)`.

## Main definitions

The two counts are defined in `Weil.Definitions`:

* `AlgebraicGeometry.pointCount f K`: the cardinality `#X(K)` of the set of `K`-valued points of
  `X` over `k` (`0` if that set is infinite), for any field extension `K` of `k`.
* `AlgebraicGeometry.pointCountOfDegree f n`: the point count `A_n = #X(k_n)` over Mathlib's
  chosen extension `FiniteField.Extension k p n` of degree `n` of the finite field `k`.

* `AlgebraicGeometry.fieldValuedPointsOfAlgHom`: the map `X(K) → X(L)` induced by a
  `k`-embedding `K → L`.

## Main results

* `AlgebraicGeometry.fieldValuedPointsCongr`: a `k`-isomorphism `K ≃ₐ[k] L` induces a
  bijection `X(K) ≃ X(L)`.
* `AlgebraicGeometry.pointCount_congr`: hence `#X(K) = #X(L)`.
* `AlgebraicGeometry.pointCountOfDegree_eq_pointCount`: `A_n = #X(K)` for every extension `K`
  of `k` of degree `n`.

## Implementation notes

The source takes for `k_n` the subfield of degree `n` of a fixed algebraic closure of `k`. Since
the count only depends on `k_n` up to `k`-isomorphism, we use Mathlib's chosen extension
`FiniteField.Extension k (ringChar k) n`, lifted to the universe of `X`, and prove that every
extension of degree `n` gives the same number. The characteristic-dependent choice is invisible
to users: `pointCountOfDegree_eq_pointCount` is the interface.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  Introduction.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

variable {f}

/-- The `L`-valued point `Spec j ≫ t` of a `K`-valued point `t`, for a `k`-embedding
`j : K → L`. -/
def fieldValuedPointsOfAlgHom {K L : Type u} [Field K] [Algebra k K] [Field L] [Algebra k L]
    (j : K →ₐ[k] L) (t : fieldValuedPoints f K) : fieldValuedPoints f L :=
  ⟨Spec.map (CommRingCat.ofHom j.toRingHom) ≫ t.1, by
    rw [Category.assoc, t.2, ← Spec.map_comp]
    congr 2
    ext c
    exact j.commutes c⟩

/-- Pushing points forward along `j` and then `j'` is pushing them forward along `j' ∘ j`. -/
theorem fieldValuedPointsOfAlgHom_comp {K L M : Type u} [Field K] [Algebra k K] [Field L]
    [Algebra k L] [Field M] [Algebra k M] (j : K →ₐ[k] L) (j' : L →ₐ[k] M)
    (t : fieldValuedPoints f K) :
    fieldValuedPointsOfAlgHom j' (fieldValuedPointsOfAlgHom j t) =
      fieldValuedPointsOfAlgHom (j'.comp j) t := by
  apply Subtype.ext
  simp only [fieldValuedPointsOfAlgHom, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- Pushing points forward along the identity does nothing. -/
theorem fieldValuedPointsOfAlgHom_id {K : Type u} [Field K] [Algebra k K]
    (t : fieldValuedPoints f K) : fieldValuedPointsOfAlgHom (AlgHom.id k K) t = t := by
  apply Subtype.ext
  simp only [fieldValuedPointsOfAlgHom]
  convert Category.id_comp t.1
  rw [← Spec.map_id]
  rfl

/-- A `k`-isomorphism `K ≃ₐ[k] L` induces a bijection between the `K`-valued and the `L`-valued
points of `X` over `k`, by precomposition with `Spec L ≅ Spec K`. -/
def fieldValuedPointsCongr {K L : Type u} [Field K] [Algebra k K] [Field L] [Algebra k L]
    (e : K ≃ₐ[k] L) : fieldValuedPoints f K ≃ fieldValuedPoints f L where
  toFun := fieldValuedPointsOfAlgHom (e : K →ₐ[k] L)
  invFun := fieldValuedPointsOfAlgHom (e.symm : L →ₐ[k] K)
  left_inv t := by
    rw [fieldValuedPointsOfAlgHom_comp]
    convert fieldValuedPointsOfAlgHom_id t
    ext x
    simp
  right_inv t := by
    rw [fieldValuedPointsOfAlgHom_comp]
    convert fieldValuedPointsOfAlgHom_id t
    ext x
    simp

variable (f) in
/-- The point count `#X(K)` depends on the extension `K` of `k` only up to `k`-isomorphism. -/
theorem pointCount_congr {K L : Type u} [Field K] [Algebra k K] [Field L] [Algebra k L]
    (e : K ≃ₐ[k] L) : pointCount f K = pointCount f L :=
  Nat.card_congr (fieldValuedPointsCongr e)

variable [Finite k]

variable (f) in
/-- The `n`-th point count `A_n` is the number of `K`-valued points of `X` for any extension `K`
of `k` of degree `n`. -/
theorem pointCountOfDegree_eq_pointCount (K : Type u) [Field K] [Algebra k K] {n : ℕ} [NeZero n]
    (hK : Module.finrank k K = n) : pointCountOfDegree f n = pointCount f K := by
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  exact pointCount_congr f
    (ULift.algEquiv.trans (FiniteField.algEquivExtension k (ringChar k) n K hK).symm)

end AlgebraicGeometry

