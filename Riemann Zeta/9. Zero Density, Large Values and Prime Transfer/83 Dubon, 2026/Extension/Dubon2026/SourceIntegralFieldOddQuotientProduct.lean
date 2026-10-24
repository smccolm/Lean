import Dubon2026.SourceIntegralPerfectOddQuotientProduct

/-! The actual odd-prime quotient product over every field whose characteristic
does not divide the prime degree. The characteristic-zero branch is the proved
finite-coefficient descent. In positive characteristic, pass to the native
algebraic closure, apply the constructed Witt-model product, and reflect the
identity through the original field embedding. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open WeierstrassCurve SourceEllipticVelu.OddDiscriminant
noncomputable section

/-- The exact integral modular polynomial is the product of the original odd-prime quotient factors
over any field, for prime degree invertible in that field. -/
theorem modularPolynomial_eq_oddQuotientProduct
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0)
    (Q : Fin (p + 1) → W.toAffine.Point)
    (hQ : ∀ i, addOrderOf (Q i) = 2 * (p / 2) + 1)
    (hinj : Function.Injective (fun i => AddSubgroup.zmultiples (Q i))) :
    relationAtSeed (modularPolynomial p) W.j = oddQuotientProduct W hQ := by
  classical
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hchar | hchar
  · letI : Fact (ringChar K).Prime := ⟨hchar⟩
    let ι := algebraMap K (AlgebraicClosure K)
    let f := pointMapHom ι W
    have hf := pointMapHom_injective ι W
    have hQ' : ∀ i, addOrderOf (f (Q i)) = 2 * (p / 2) + 1 := by
      intro i
      exact (addOrderOf_injective f hf (Q i)).trans (hQ i)
    have hinj' : Function.Injective (fun i => AddSubgroup.zmultiples (f (Q i))) := by
      intro i j hij
      apply hinj
      apply AddSubgroup.map_injective (f := f) hf
      simpa only [AddMonoidHom.map_zmultiples] using hij
    have hp' : (p : AlgebraicClosure K) ≠ 0 := by
      simpa only [map_natCast, map_zero] using ι.injective.ne hp
    exact (modularPolynomial_eq_oddQuotientProduct_map_iff ι W hQ hQ' p).mp
      (modularPolynomial_eq_oddQuotientProduct_perfect (ringChar K) (W.map ι)
        p hp2 hp' (fun i => f (Q i)) hQ' hinj')
  · letI : CharZero K := (CharP.ringChar_zero_iff_CharZero K).mp hchar
    exact modularPolynomial_eq_oddQuotientProduct_charZero W p hp2 Q hQ hinj

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
