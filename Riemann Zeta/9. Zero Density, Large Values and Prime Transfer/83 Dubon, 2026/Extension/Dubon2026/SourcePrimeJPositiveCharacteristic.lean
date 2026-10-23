import Dubon2026.SourceHasseEndgame
import Dubon2026.SourceHassePolynomialClosure
import Dubon2026.SourceHasseResidueIdentity
import Dubon2026.SourceHassePolynomialRootCount
import Dubon2026.SourceHasseOneRoot
import Dubon2026.SourceDeltaPowerObstruction
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> automorphy/residual association -> original Frobenius/inertia
-> modular-curve good reduction -> exact degree -> prime j nonmembership.
This assembles the actual Hasse polynomial, prime orbit factorization,
discriminant norm, finite root count and eta power obstruction.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_starBank. All mathematical inputs are proved locally;
the archived conditional core is replaced by direct applications. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem prime_j_polynomial_impossible_closed
    {K : Type*} [Field K] [IsAlgClosed K] {ℓ p : ℕ}
    [Fact ℓ.Prime] [Fact p.Prime] [CharP K ℓ] (hpℓ : p ≠ ℓ)
    {R : Polynomial K} (hRmem : Polynomial.aeval (jqModC K) R = jqNModC K p) : False := by
  have hp0 : (p : K) ≠ 0 := (by
    intro h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) (Fact.out : p.Prime)).1
      ((CharP.cast_eq_zero_iff K ℓ p).1 h)).symm)
  haveI : NeZero (p : K) := ⟨hp0⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  obtain ⟨ζ, hζval⟩ := hz.isUnit (Nat.Prime.ne_zero (Fact.out : p.Prime))
  have hζ : IsPrimitiveRoot (ζ : K) p := hζval.symm ▸ hz
  obtain ⟨hRmon, hRdeg, _⟩ := prime_j_orbit_factorization p ζ hζ hRmem
  obtain ⟨M, hM1, hMK, G, hGdeg, hGstar⟩ := starK K (ℓ := ℓ)
  obtain ⟨c, hc, hdvd⟩ := hasse_polynomial_closure p ζ hGstar hRmem hζ
  have hGpos : 0 < G.natDegree := by rw [hGdeg]; omega
  obtain ⟨β₀, huniq, hRform⟩ :=
    hasse_polynomial_root_count hp0 (Nat.Prime.two_le Fact.out) hRmon hRdeg hGpos hc hdvd
  have hG0 : G ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hGstar
    exact zero_ne_one hGstar
  have hlc : G.leadingCoeff ≠ 0 := fun h => hG0 (Polynomial.leadingCoeff_eq_zero.mp h)
  have hGfact := eq_C_leadingCoeff_mul_pow_of_forall_root huniq
  rw [hGfact, hGdeg] at hGstar
  obtain ⟨γ, hγ, honep⟩ := hasse_one_root_closed hMK hlc hGstar
  have hpressEq : qExpand K p (jqModC K)
      = (jqModC K - HahnSeries.C β₀) ^ p + HahnSeries.C β₀ := by
    have h1 : Polynomial.aeval (jqModC K) R
        = (jqModC K - HahnSeries.C β₀) ^ p + HahnSeries.C β₀ := by
      rw [hRform, map_add, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        algebraMap_laurent_eq_single]
      rfl
    rw [← h1, hRmem, jqNModC]
  have hDp := endgame_read p ((Nat.Prime.one_lt (Fact.out : p.Prime)).le)
    hγ honep hpressEq
  exact delta_pow_ne K hpℓ (γ ^ (p - 1)) hDp


end
end Dubon2026.SourceFunctionField
