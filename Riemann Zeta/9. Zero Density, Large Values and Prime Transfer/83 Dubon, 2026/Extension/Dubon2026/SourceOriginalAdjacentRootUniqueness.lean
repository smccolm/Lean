import Dubon2026.SourceIntegralPrimeLaurentRoots
import Dubon2026.SourceOriginalAllLevelDegree

/-! DUB-17/18 -> actual Hecke norm -> Atkin-Lehner generator images.
The already proved all-level conjugate product identifies the common root
of the lower modular relation and the reversed prime relation. This reuses
the predecessor-generation root bounds and avoids a fresh prime-factor
induction or an assumed bivariate symmetry. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots PrimeDegreeAux IntegralJCoordinate
open scoped IntermediateField

theorem expandedJMinpoly_eq_integral_relation
    (K : Type*) [Field K] [Algebra ℚ K] (A M : ℕ) [NeZero A] [NeZero M] :
    expandedJMinpoly K A M =
      relationAtSeed (modularPolynomial M) (coeffEmb K (qExpand ℚ A jq)) := by
  rw [expandedJMinpoly, ← modularPolynomial_map_coordinate, Polynomial.map_map]
  unfold relationAtSeed
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [evaluate]

theorem original_adjacent_common_root_unique (M p : ℕ) [NeZero M] [hp : Fact p.Prime]
    (z : LaurentSeries ℚ)
    (hM : (relationAtSeed (modularPolynomial M) jq).eval z = 0)
    (hpz : (relationAtSeed (modularPolynomial p) (qExpand ℚ (M * p) jq)).eval z = 0) :
    z = qExpand ℚ M jq := by
  let K := AlgebraicClosure ℚ
  haveI : NeZero (M : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne M)⟩
  obtain ⟨u, hu⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K M
  have hunit := hu.isUnit (NeZero.ne M)
  have hη : IsPrimitiveRoot (hunit.unit : K) M := by rw [hunit.unit_spec]; exact hu
  have hlower := expandedJMinpoly_eq_slotProduct M hunit.unit hη
  obtain ⟨ζ, P, _, hPm, hPd, hP⟩ := exists_prime_product_algClosed p K
  have hPeq : P = modularPolynomial p :=
    eq_modularPolynomial_of_monic_root_degree p P hPm
      (prime_product_forward_root p K ζ P hP) (by
        rw [← modularPolynomial_natDegree, modularPolynomial_prime_natDegree, hPd])
  let φ : LaurentSeries ℚ →+* LaurentSeries K := (coeffEmb K).comp (qExpand ℚ (M * p))
  let y := φ z
  let e := M * p * M
  have hy : (expandedJMinpoly K (M * p) M).IsRoot y := by
    rw [expandedJMinpoly_eq_integral_relation]
    change (relationAtSeed (modularPolynomial M) (φ jq)).eval (φ z) = 0
    rw [← relationAtSeed_map, Polynomial.eval_map, Polynomial.eval₂_hom, hM, map_zero]
  have hyprime : (relationAtSeed P (TS K (e * p) 1)).eval y = 0 := by
    have h := congrArg φ hpz
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, relationAtSeed_map] at h
    rw [← hPeq] at h
    have he : φ (qExpand ℚ (M * p) jq) = TS K (e * p) 1 := by
      change coeffEmb K (qExpand ℚ (M * p) (qExpand ℚ (M * p) jq)) = _
      rw [qExpand_qExpand, coeffEmb_qExpand_jq_eq_TS]
      exact TS_congr (by dsimp [e]; ring) 1
    rwa [he] at h
  have hyroot : y = TS K (e * (p * p)) 1 ∨ ∃ c < p, y = TS K e (ζ ^ c) := by
    have hr := prime_twisted_product_root_iff p ζ P hP e 1 y
    simp only [one_pow, one_mul] at hr
    exact hr.mp hyprime
  have heq : y = TS K e 1 := by
    rcases hyroot with hbig | ⟨c, _, hc⟩
    · exfalso
      apply original_lower_root_ne_larger_branch M p hunit.unit hlower y hy
      exact hbig.trans (TS_congr (by dsimp [e]; ring) 1)
    · have hw := original_lower_root_top_twist_eq_one M p hunit.unit hlower y hy (ζ ^ c) hc
      simpa only [hw] using hc
  apply φ.injective
  exact heq.trans (by
    change TS K e 1 = coeffEmb K (qExpand ℚ (M * p) (qExpand ℚ M jq))
    rw [qExpand_qExpand, coeffEmb_qExpand_jq_eq_TS])

end
end Dubon2026.SourceFunctionField
