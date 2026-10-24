import Dubon2026.SourceIntegralComplexOddQuotientProduct
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Descend the actual odd-prime quotient product through a field embedding
into the complex numbers. Native injective point maps preserve exact order
and distinct cyclic subgroups. For algebraic extensions of the rationals,
the native algebraically closed lift constructs the embedding. More general
coefficient fields and integral reduction remain on the DUB-17/18 chain. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open WeierstrassCurve SourceEllipticVelu.OddDiscriminant

theorem modularPolynomial_eq_oddQuotientProduct_of_complex_embedding
    {F : Type*} [Field F] [DecidableEq F] (f : F →+* ℂ)
    (W : WeierstrassCurve F) [W.IsElliptic] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Q : Fin (p + 1) → W.toAffine.Point)
    (hQ : ∀ i, addOrderOf (Q i) = 2 * (p / 2) + 1)
    (hinj : Function.Injective (fun i => AddSubgroup.zmultiples (Q i))) :
    relationAtSeed (modularPolynomial p) W.j = oddQuotientProduct W hQ := by
  have hf := pointMapHom_injective f W
  have hQ' : ∀ i, addOrderOf (pointMapHom f W (Q i)) = 2 * (p / 2) + 1 := by
    intro i
    rw [addOrderOf_injective _ hf, hQ]
  apply (modularPolynomial_eq_oddQuotientProduct_map_iff f W hQ hQ' p).mp
  apply modularPolynomial_eq_oddQuotientProduct_complex (W.map f) p hp2 _ hQ'
  intro i j h
  apply hinj
  apply AddSubgroup.map_injective hf
  simpa only [AddMonoidHom.map_zmultiples] using h

theorem modularPolynomial_eq_oddQuotientProduct_algebraic
    {F : Type*} [Field F] [DecidableEq F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]
    (W : WeierstrassCurve F) [W.IsElliptic] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Q : Fin (p + 1) → W.toAffine.Point)
    (hQ : ∀ i, addOrderOf (Q i) = 2 * (p / 2) + 1)
    (hinj : Function.Injective (fun i => AddSubgroup.zmultiples (Q i))) :
    relationAtSeed (modularPolynomial p) W.j = oddQuotientProduct W hQ :=
  modularPolynomial_eq_oddQuotientProduct_of_complex_embedding
    (IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom W p hp2 Q hQ hinj

end Dubon2026.SourceFunctionField.IntegralJCoordinate
