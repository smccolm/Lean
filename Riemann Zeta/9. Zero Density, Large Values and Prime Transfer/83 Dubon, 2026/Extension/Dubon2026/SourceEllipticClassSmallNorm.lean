import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic

/-! The affine ideal-class route to the actual odd cyclic quotient map.
Adapted from TauCetiProject/TauCeti, Apache-2.0, commit
bfcff79b60964ba7bdb78b952828313686c327ba; the point-class argument
credits Chris Birkbeck's AINTLIB. Only the elliptic-curve consumer is
needed: omit singular-curve cotangent spaces and the general isogeny category.
Dependency: DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> continuation ->
arithmetic automorphy -> Frobenius/inertia -> modular-curve good reduction ->
reverse genus and inertia census -> cyclic modular-polynomial roots ->
explicit odd quotient homomorphism -> norm-induced map of ideal classes. -/
namespace Dubon2026.SourceEllipticClassGroup
noncomputable section
open Polynomial WeierstrassCurve.Affine FractionalIdeal
open scoped nonZeroDivisors Polynomial.Bivariate TensorProduct
variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}
/-- Every nonzero elliptic coordinate ideal has finite codimension. -/
theorem finiteDimensional_quotient_of_ne_bot
    (I : Ideal W.CoordinateRing) (hI : I ≠ ⊥) :
    FiniteDimensional F (W.CoordinateRing ⧸ I) := by
  classical
  let hFin : ∀ i, Module.Finite F
      (F[X] ⧸ Ideal.span ({Ideal.smithCoeffs (CoordinateRing.basis W) I hI i} : Set F[X])) :=
    fun i => inferInstance
  exact Module.Finite.equiv
    (Ideal.quotientEquivDirectSum F (CoordinateRing.basis W) hI).symm


/-- The actual bounded-degree coordinate-ring combinations. -/
noncomputable def basisCombMap (W : WeierstrassCurve.Affine F) (a b : ℕ) :
    (Polynomial.degreeLT F a × Polynomial.degreeLT F b) →ₗ[F] W.CoordinateRing :=
  LinearMap.coprod
    (((LinearMap.toSpanSingleton F[X] W.CoordinateRing 1).restrictScalars F).comp
      (Polynomial.degreeLT F a).subtype)
    (((LinearMap.toSpanSingleton F[X] W.CoordinateRing (CoordinateRing.basis W 1)).restrictScalars
      F).comp (Polynomial.degreeLT F b).subtype)

theorem natDegree_norm_basisComb_le {p q : F[X]} {da db : ℕ}
    (hp : p.degree < (da : ℕ)) (hq : q.degree < (db : ℕ)) :
    (Algebra.norm F[X]
      (p • (1 : W.CoordinateRing) + q • CoordinateRing.basis W 1)).natDegree ≤
        max (2 * (da - 1)) (2 * db + 1) := by
  rw [CoordinateRing.basis_one, Polynomial.natDegree_le_iff_degree_le,
    CoordinateRing.degree_norm_smul_basis]
  have hmax : ((max (2 * (da - 1)) (2 * db + 1) : ℕ) : WithBot ℕ) =
      max ((2 * (da - 1) : ℕ) : WithBot ℕ) ((2 * db + 1 : ℕ) : WithBot ℕ) := rfl
  rw [hmax]
  have hbound {r : F[X]} {n c d : ℕ} (hr : r.degree < (n : ℕ))
      (hle : ∀ k < n, 2 * k + c ≤ d) : 2 • r.degree + c ≤ (d : ℕ) := by
    by_cases h0 : r = 0
    · simp [h0]
    · have hdeg := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hr
      rw [Polynomial.degree_eq_natDegree h0, nsmul_eq_mul]
      norm_cast
      exact hle _ hdeg
  apply max_le_max
  · simpa only [Nat.cast_zero, add_zero] using hbound (c := 0) hp (by omega)
  · exact hbound (c := 3) hq (by omega)

theorem basisCombMap_ne_zero {a b : ℕ}
    (pq : Polynomial.degreeLT F a × Polynomial.degreeLT F b) (h : pq ≠ 0) :
    basisCombMap W a b pq ≠ 0 := by
  intro hz
  apply h
  rw [basisCombMap] at hz
  rw [CoordinateRing.basis_one] at hz
  obtain ⟨hp, hq⟩ := CoordinateRing.smul_basis_eq_zero hz
  exact Prod.ext (Subtype.ext hp) (Subtype.ext hq)

/-- Every nonzero ideal contains a nonzero function whose norm degree is at most one more than
the ideal's codimension. This is the concrete genus-one Riemann--Roch inequality. -/
theorem exists_mem_norm_natDegree_le
    (I : Ideal W.CoordinateRing) (hI : I ≠ ⊥) :
    ∃ a ∈ I, a ≠ 0 ∧
      (Algebra.norm F[X] a).natDegree ≤ Module.finrank F (W.CoordinateRing ⧸ I) + 1 := by
  classical
  set R := W.CoordinateRing
  set ℓ := Module.finrank F (R ⧸ I) with hℓ
  have : FiniteDimensional F (R ⧸ I) := finiteDimensional_quotient_of_ne_bot _ hI
  let da := (ℓ + 1) / 2 + 1
  let db := ℓ / 2
  set ψ : (Polynomial.degreeLT F da × Polynomial.degreeLT F db) →ₗ[F] (R ⧸ I) :=
    ((Submodule.mkQ I).restrictScalars F).comp (basisCombMap W da db) with hψ
  have hdimdom :
      Module.finrank F (Polynomial.degreeLT F da × Polynomial.degreeLT F db) = da + db := by
    rw [Module.finrank_prod, (Polynomial.degreeLTEquiv F da).finrank_eq,
      (Polynomial.degreeLTEquiv F db).finrank_eq, Module.finrank_fin_fun,
      Module.finrank_fin_fun]
  have hdomℓ :
      Module.finrank F (Polynomial.degreeLT F da × Polynomial.degreeLT F db) = ℓ + 1 := by
    rw [hdimdom]
    dsimp [da, db]
    omega
  have hrn : Module.finrank F (LinearMap.range ψ) + Module.finrank F (LinearMap.ker ψ) =
      Module.finrank F (Polynomial.degreeLT F da × Polynomial.degreeLT F db) :=
    ψ.finrank_range_add_finrank_ker
  have hrange_le : Module.finrank F (LinearMap.range ψ) ≤ ℓ :=
    le_trans (Submodule.finrank_le _) (le_of_eq hℓ.symm)
  have hker_pos : 0 < Module.finrank F (LinearMap.ker ψ) := by omega
  have : Nontrivial (LinearMap.ker ψ) := Module.nontrivial_of_finrank_pos hker_pos
  obtain ⟨z, hz⟩ := exists_ne (0 : LinearMap.ker ψ)
  set pq := (z : Polynomial.degreeLT F da × Polynomial.degreeLT F db) with hpq
  have hpq_ne : pq ≠ 0 := fun h => hz (Subtype.ext h)
  refine ⟨basisCombMap W da db pq, ?_, basisCombMap_ne_zero pq hpq_ne, ?_⟩
  · have hz0 : ψ pq = 0 := z.2
    rw [hψ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hz0
    exact hz0
  · obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := pq
    rw [Polynomial.mem_degreeLT] at hp hq
    have hbound := natDegree_norm_basisComb_le (W := W) hp hq
    rw [basisCombMap]
    refine le_trans hbound ?_
    dsimp [da, db]
    omega


end
end Dubon2026.SourceEllipticClassGroup
