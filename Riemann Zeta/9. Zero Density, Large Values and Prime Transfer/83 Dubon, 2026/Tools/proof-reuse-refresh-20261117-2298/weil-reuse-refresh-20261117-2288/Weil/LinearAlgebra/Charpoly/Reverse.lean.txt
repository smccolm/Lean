module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Polynomial.Reverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharPowerSeriesCharpoly

/-!
# The reverse of the characteristic polynomial

For an endomorphism `φ` of a finite free module, the reverse `reverse χ_φ = T ^ n χ_φ(1 / T)` of
its characteristic polynomial is the local factor `det(1 - φ T)`. Its roots are the inverses of
the nonzero roots of `χ_φ`, that is of the nonzero eigenvalues of `φ`, in the base field and in
any extension of it.

## Main results

* `LinearMap.isRoot_reverse_charpoly_inv_iff`: for `μ ≠ 0`, `μ⁻¹` is a root of `reverse χ_φ`
  if and only if `μ` is a root of `χ_φ`.
* `LinearMap.aeval_inv_reverse_charpoly_eq_zero_iff`: the same for `μ ≠ 0` in a field extension.
* `Stacks.EtaleCohomology.charPowerSeries_one_eq_reverse_charpoly_of_free`: for an endomorphism
  of a finite free module over a commutative ring, `det(1 - φ T) = reverse χ_φ` in `Λ⟦T⟧`.

## Implementation notes

The root statements hold for every polynomial, by `Polynomial.eval₂_reverse_eq_zero_iff`; no
invertibility of `φ` is needed. Over a field, the power series identity is
`Stacks.EtaleCohomology.charPowerSeries_one_eq_reverse_charpoly`; the version here holds over any
commutative ring.
-/

@[expose] public noncomputable section

open Module Polynomial

namespace LinearMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module.Finite K V]

/-- For `μ ≠ 0`, `μ⁻¹` is a root of the reverse of the characteristic polynomial of `φ` if and
only if `μ` is a root of the characteristic polynomial. -/
theorem isRoot_reverse_charpoly_inv_iff (φ : V →ₗ[K] V) {μ : K} (hμ : μ ≠ 0) :
    (φ.charpoly.reverse).IsRoot μ⁻¹ ↔ φ.charpoly.IsRoot μ := by
  let _ : Invertible μ := invertibleOfNonzero hμ
  have h := eval₂_reverse_eq_zero_iff (RingHom.id K) μ φ.charpoly
  rw [invOf_eq_inv] at h
  exact h

/-- For `μ ≠ 0` in a field extension `L` of `K`, `μ⁻¹` is a root of the reverse of the
characteristic polynomial of `φ` if and only if `μ` is a root of the characteristic
polynomial. -/
theorem aeval_inv_reverse_charpoly_eq_zero_iff {L : Type*} [Field L] [Algebra K L]
    (φ : V →ₗ[K] V) {μ : L} (hμ : μ ≠ 0) :
    aeval μ⁻¹ φ.charpoly.reverse = 0 ↔ aeval μ φ.charpoly = 0 := by
  let _ : Invertible μ := invertibleOfNonzero hμ
  have h := eval₂_reverse_eq_zero_iff (algebraMap K L) μ φ.charpoly
  rw [invOf_eq_inv] at h
  simpa [aeval_def] using h

end LinearMap

namespace Stacks.EtaleCohomology

variable {Λ : Type*} [CommRing Λ] {M : Type*} [AddCommGroup M] [Module Λ M]
  [Module.Finite Λ M] [Module.Free Λ M]

/-- **`det(1 - φ T)` is the reverse of the characteristic polynomial of `φ`**, for an
endomorphism of a finite free module over a commutative ring. -/
theorem charPowerSeries_one_eq_reverse_charpoly_of_free (φ : M →ₗ[Λ] M) :
    charPowerSeries φ 1 = ((LinearMap.charpoly φ).reverse : PowerSeries Λ) := by
  classical
  let b := Module.Free.chooseBasis Λ M
  rw [charPowerSeries_eq_localCharSeries b, ← LinearMap.charpoly_toMatrix φ b,
    Matrix.reverse_charpoly, localCharSeries, localCharMatrix, Matrix.charpolyRev,
    ← Polynomial.coeToPowerSeries.ringHom_apply, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply, apply_ite]
  ring

end Stacks.EtaleCohomology

end
