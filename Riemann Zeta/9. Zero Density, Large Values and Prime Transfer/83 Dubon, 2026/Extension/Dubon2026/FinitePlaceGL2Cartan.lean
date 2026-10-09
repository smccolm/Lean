import Dubon2026.FinitePlaceGL2DiagonalReduction
import Dubon2026.FinitePlaceHeckeDiagonalPowers

/-! # The genuine Cartan factorization of every original local GL2 matrix modulo its actual scalar center -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Every original local GL2 element is an actual scalar times integral matrices around a nonnegative power of the genuine original Hecke diagonal. -/
theorem finitePlaceGL2_cartan (p : ℕ) [NeZero p] (hp : p.Prime)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p hp).adicCompletion ℚ)) :
    ∃ u : ((rationalPrimePlace p hp).adicCompletion ℚ)ˣ, ∃ n : ℕ,
      ∃ l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p hp),
        g = GeneralLinearGroup.scalar (Fin 2) u * l.val *
          (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp)) (finiteAdelicHeckeDiagonal p)) ^ n * r.val := by
  obtain ⟨a, t, l, r, ht, hg⟩ := finitePlaceGL2_integral_diagonal (rationalPrimePlace p hp) g
  obtain ⟨u, n, hu⟩ := finitePlace_integral_diagonal_hecke_power p hp t ht
  let b := GeneralLinearGroup.map ((rationalPrimePlace p hp).adicCompletionIntegers ℚ).subtype
    (gl2UnitDiagonalPair 1 u)
  have hb : b ∈ finitePlaceGL2Gamma0 1 (rationalPrimePlace p hp) :=
    finitePlaceGL2_integral_mem _ _
  refine ⟨a, n, ⟨l.val * b, (finitePlaceGL2Gamma0 1 _).mul_mem l.property hb⟩, r, ?_⟩
  rw [hg, hu]
  simp only [b, mul_assoc]

end
end Dubon2026
