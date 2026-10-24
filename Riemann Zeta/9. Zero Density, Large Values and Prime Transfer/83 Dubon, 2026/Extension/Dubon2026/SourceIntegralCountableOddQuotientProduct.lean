import Dubon2026.SourceCountableComplexEmbedding
import Dubon2026.SourceIntegralEmbeddedOddQuotientProduct

/-! The actual odd-prime quotient product over a countable coefficient field.
The complex embedding is constructed, rather than supplied. This is the
finite-coordinate descent step towards general characteristic zero and
integral reduction on the DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 chain. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open WeierstrassCurve

/-- The exact modular-polynomial product over any countable rational coefficient field. -/
theorem modularPolynomial_eq_oddQuotientProduct_countable
    {F : Type*} [Field F] [DecidableEq F] [Algebra ℚ F] [Countable F]
    (W : WeierstrassCurve F) [W.IsElliptic] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Q : Fin (p + 1) → W.toAffine.Point)
    (hQ : ∀ i, addOrderOf (Q i) = 2 * (p / 2) + 1)
    (hinj : Function.Injective (fun i => AddSubgroup.zmultiples (Q i))) :
    relationAtSeed (modularPolynomial p) W.j = oddQuotientProduct W hQ := by
  obtain ⟨f⟩ := exists_complex_embedding_of_countable F
  exact modularPolynomial_eq_oddQuotientProduct_of_complex_embedding f W p hp2 Q hQ hinj

end Dubon2026.SourceFunctionField.IntegralJCoordinate
