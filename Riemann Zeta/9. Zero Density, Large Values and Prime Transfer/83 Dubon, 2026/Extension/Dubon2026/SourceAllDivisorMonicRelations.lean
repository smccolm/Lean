import Dubon2026.SourcePrimeMonicRelation
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! DUB-17/18 -> original regular differential realization -> finite extension.
Prime-factor induction propagates the proved prime monic relation to every
nonzero divisor substitution. The polynomial coordinate stays the original
integral j coordinate. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero.lean.
The stronger external irreducibility and exact-degree packages are unnecessary.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial

/-- Substitute the actual seed into the coefficients of an integral bivariate polynomial. -/
def relationAtSeed {R : Type*} [CommRing R] (P : Polynomial (Polynomial ℤ)) (x : R) :
    Polynomial R := P.map (Polynomial.eval₂RingHom (Int.castRingHom R) x)

theorem relationAtSeed_map {R S : Type*} [CommRing R] [CommRing S]
    (P : Polynomial (Polynomial ℤ)) (x : R) (f : R →+* S) :
    (relationAtSeed P x).map f = relationAtSeed P (f x) := by
  rw [relationAtSeed, relationAtSeed, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp

theorem relationAtSeed_jq_eval {n : ℕ} [NeZero n] (P : Polynomial (Polynomial ℤ))
    (hP : P.eval₂ evalAtJ (qExpand ℚ n jq) = 0) :
    (relationAtSeed P jq).eval (qExpand ℚ n jq) = 0 := by
  rw [relationAtSeed, Polynomial.eval_map]
  convert hP using 2
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [evalAtJ_X]

theorem relationAtSeed_substitution_eval {n : ℕ} [NeZero n] (P : Polynomial (Polynomial ℤ))
    (hP : P.eval₂ evalAtJ (qExpand ℚ n jq) = 0) (a : ℕ) [NeZero a] :
    (relationAtSeed P (qExpand ℚ a jq)).eval (qExpand ℚ (a * n) jq) = 0 := by
  have h : (relationAtSeed P (qExpand ℚ a jq)).eval
      (qExpand ℚ a (qExpand ℚ n jq)) = 0 := by
    rw [← relationAtSeed_map, Polynomial.eval_map, Polynomial.eval₂_hom,
      relationAtSeed_jq_eval P hP, map_zero]
  simpa only [qExpand_qExpand] using h

/-- Every nonzero original substitution satisfies a monic relation over the actual integral j coordinate. -/
theorem exists_monic_relation (N : ℕ) [NeZero N] :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧
      P.eval₂ evalAtJ (qExpand ℚ N jq) = 0 := by
  letI : Algebra (Polynomial ℤ) (LaurentSeries ℚ) := evalAtJ.toAlgebra
  suffices h : ∀ (n : ℕ) [NeZero n], IsIntegral (Polynomial ℤ) (qExpand ℚ n jq) by
    obtain ⟨P, hP, hval⟩ := h N
    exact ⟨P, hP, hval⟩
  intro n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h.out
  | one =>
    intro _
    rw [qExpand_one_apply, ← evalAtJ_X]
    exact isIntegral_algebraMap
  | prime_mul p a hp ih =>
    intro hpa
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero a := ⟨fun h => NeZero.ne (p * a) (by rw [h, Nat.mul_zero])⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hia : IsIntegral (Polynomial ℤ) (qExpand ℚ a jq) := ih
    obtain ⟨P, hPm, hP0⟩ := exists_prime_monic_relation p
    let A := Algebra.adjoin (Polynomial ℤ) ({qExpand ℚ a jq} : Set (LaurentSeries ℚ))
    have hmem : qExpand ℚ a jq ∈ A := Algebra.self_mem_adjoin_singleton _ _
    haveI : Algebra.IsIntegral (Polynomial ℤ) ↥A :=
      ⟨fun x => (isIntegral_algebraMap_iff (fun _ _ huv => Subtype.ext huv)).mp
        (IsIntegral.of_mem_of_fg A hia.fg_adjoin_singleton _ x.2)⟩
    have hroot : Polynomial.eval₂ (algebraMap ↥A (LaurentSeries ℚ)) (qExpand ℚ (a * p) jq)
        (relationAtSeed P (⟨qExpand ℚ a jq, hmem⟩ : ↥A)) = 0 := by
      rw [Polynomial.eval₂_eq_eval_map, relationAtSeed_map]
      exact relationAtSeed_substitution_eval P hP0 a
    have hint : IsIntegral (Polynomial ℤ) (qExpand ℚ (a * p) jq) :=
      isIntegral_trans (qExpand ℚ (a * p) jq)
        ⟨relationAtSeed P (⟨qExpand ℚ a jq, hmem⟩ : ↥A), hPm.map _, hroot⟩
    rwa [qExpand_congr (Nat.mul_comm a p)] at hint

end
end Dubon2026.SourceFunctionField
