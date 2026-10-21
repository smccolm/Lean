import Dubon2026.SourcePrimeConjugateIntegral
import Dubon2026.SourceJPrincipalPart
import Dubon2026.SourceOriginalFieldFinite
import Mathlib.Algebra.Polynomial.Lifts


/-! DUB-17/18 -> original differential realization -> finite extension over j
-> actual monic relations. These proofs descend the literal integral q-series
coefficients through the cyclotomic conjugate product and polynomial in j.
Only integrality needed for the monic relation is selected; exact field degree,
irreducibility, symmetry and general pole bounds are deferred.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.lean; pinned polynomial lifts.
-/
namespace Dubon2026.SourceFunctionField.PhiGen
noncomputable section
open Polynomial

namespace IntCoeffs
private theorem sub {f g : LaurentSeries ℚ} (hf : IntCoeffs f) (hg : IntCoeffs g) :
    IntCoeffs (f - g) := by
  intro m
  obtain ⟨a, ha⟩ := hf m
  obtain ⟨b, hb⟩ := hg m
  exact ⟨a - b, by rw [HahnSeries.coeff_sub, ha, hb]; push_cast; ring⟩

end IntCoeffs

theorem intCoeffs_algebraMap_int_mul_jq_pow (z : ℤ) (n : ℕ) :
    IntCoeffs (algebraMap ℚ (LaurentSeries ℚ) ((z : ℚ)) * jq ^ n) := by
  intro m
  obtain ⟨a, ha⟩ := intCoeffs_jq_pow n m
  refine ⟨z * a, ?_⟩
  rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, HahnSeries.coeff_single_zero_mul, ha]
  push_cast
  ring

theorem aeval_jq_intCoeffs_descent (P : Polynomial ℚ)
    (hP : IntCoeffs (Polynomial.aeval jq P)) (k : ℕ) : ∃ z : ℤ, P.coeff k = (z : ℚ) := by
  suffices H : ∀ d : ℕ, ∀ P : Polynomial ℚ, P.natDegree = d →
      IntCoeffs (Polynomial.aeval jq P) → ∀ k : ℕ, ∃ z : ℤ, P.coeff k = (z : ℚ) by
    exact H P.natDegree P rfl hP k
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro P hd hP k

  obtain ⟨zd, hzd⟩ := hP (-(d : ℤ))
  have hlead : P.coeff d = (zd : ℚ) := by
    rw [← coeff_aeval_jq_neg P hd.le, hzd]
  rcases lt_trichotomy k d with hk | rfl | hk
  ·
    set Q : Polynomial ℚ := P - Polynomial.C (P.coeff d) * Polynomial.X ^ d with hQ
    have hQcoeff : Q.coeff k = P.coeff k := by
      rw [hQ, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (by omega), mul_zero, sub_zero]
    have hQdeg : Q.natDegree < d := by
      rcases eq_or_ne Q 0 with hQ0 | hQ0
      · rw [hQ0, Polynomial.natDegree_zero]; omega
      refine lt_of_le_of_ne ?_ ?_
      · refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        rw [hd]
        exact max_le le_rfl (Polynomial.natDegree_C_mul_X_pow_le _ _)
      · intro hcon
        apply hQ0
        rw [← Polynomial.leadingCoeff_eq_zero, Polynomial.leadingCoeff, hcon, hQ,
          Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl,
          mul_one, sub_self]
    have hQint : IntCoeffs (Polynomial.aeval jq Q) := by
      rw [hQ, map_sub, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, hlead]
      exact hP.sub (intCoeffs_algebraMap_int_mul_jq_pow zd d)
    obtain ⟨z, hz⟩ := ih Q.natDegree hQdeg Q rfl hQint k
    exact ⟨z, by rw [← hQcoeff, hz]⟩
  · exact ⟨zd, hlead⟩
  · exact ⟨0, by rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Int.cast_zero]⟩

theorem exists_integral_polynomial_of_mem_adjoin {f : LaurentSeries ℚ}
    (hint : IntCoeffs f) (hmem : f ∈ Algebra.adjoin ℚ {jq}) :
    ∃ Q : Polynomial ℤ, evalAtJ Q = f := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨P, hP⟩ := hmem
  change Polynomial.aeval jq P = f at hP
  have hPint : ∀ n : ℕ, ∃ z : ℤ, P.coeff n = (z : ℚ) :=
    aeval_jq_intCoeffs_descent P (by rw [hP]; exact hint)
  have hlift : P ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    obtain ⟨z, hz⟩ := hPint n
    exact ⟨z, by rw [eq_intCast]; exact hz.symm⟩
  obtain ⟨Q, hQ⟩ := hlift
  change Q.map (Int.castRingHom ℚ) = P at hQ
  refine ⟨Q, ?_⟩
  have hcomp : (algebraMap ℚ (LaurentSeries ℚ)).comp (Int.castRingHom ℚ)
      = algebraMap ℤ (LaurentSeries ℚ) := Subsingleton.elim _ _
  rw [← hP, ← hQ, Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
  rfl

end
end Dubon2026.SourceFunctionField.PhiGen
