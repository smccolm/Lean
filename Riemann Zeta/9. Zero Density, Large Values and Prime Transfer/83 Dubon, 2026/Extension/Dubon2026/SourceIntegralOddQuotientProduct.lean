import Dubon2026.SourceEllipticOddQuotientJ
import Dubon2026.SourceIntegralPrimeConjugateProduct

/-! The product of the actual odd quotient j-values is monic of the exact
indexing degree and commutes with field embeddings. Equality to the existing
integral modular polynomial can therefore be checked after a field embedding.
SourceIntegralComplexOddQuotientProduct proves the complex identity; this module transports it. The identity
serves cyclic-root correspondence, inertia census and good reduction on the
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 dependency chain. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticVelu.OddDiscriminant
noncomputable section

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
variable {ι : Type*} [Fintype ι]

/-- The actual quotient factors, with ellipticity derived from each exact odd order. -/
def oddQuotientProduct (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} {Q : ι → W.toAffine.Point} (hQ : ∀ i, addOrderOf (Q i) = 2 * n + 1) :
    Polynomial F := ∏ i, (X - C (oddQuotientJ W (hQ i)))

theorem oddQuotientProduct_monic (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} {Q : ι → W.toAffine.Point} (hQ : ∀ i, addOrderOf (Q i) = 2 * n + 1) :
    (oddQuotientProduct W hQ).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem oddQuotientProduct_natDegree (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} {Q : ι → W.toAffine.Point} (hQ : ∀ i, addOrderOf (Q i) = 2 * n + 1) :
    (oddQuotientProduct W hQ).natDegree = Fintype.card ι := by
  rw [oddQuotientProduct, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

theorem oddQuotientProduct_map (f : F →+* K) (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} {Q : ι → W.toAffine.Point} (hQ : ∀ i, addOrderOf (Q i) = 2 * n + 1)
    (hQ' : ∀ i, addOrderOf (pointMapHom f W (Q i)) = 2 * n + 1) :
    (oddQuotientProduct W hQ).map f = oddQuotientProduct (W.map f) hQ' := by
  rw [oddQuotientProduct, oddQuotientProduct, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, oddQuotientJ_map f W (hQ i)]

/-- Field descent preserves and reflects the exact integral modular-polynomial identity. -/
theorem modularPolynomial_eq_oddQuotientProduct_map_iff
    (f : F →+* K) (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} {Q : ι → W.toAffine.Point} (hQ : ∀ i, addOrderOf (Q i) = 2 * n + 1)
    (hQ' : ∀ i, addOrderOf (pointMapHom f W (Q i)) = 2 * n + 1)
    (p : ℕ) [NeZero p] :
    relationAtSeed (modularPolynomial p) (W.map f).j = oddQuotientProduct (W.map f) hQ' ↔
      relationAtSeed (modularPolynomial p) W.j = oddQuotientProduct W hQ := by
  rw [WeierstrassCurve.map_j, ← relationAtSeed_map, ← oddQuotientProduct_map f W hQ hQ']
  exact (Polynomial.map_injective f f.injective).eq_iff

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
