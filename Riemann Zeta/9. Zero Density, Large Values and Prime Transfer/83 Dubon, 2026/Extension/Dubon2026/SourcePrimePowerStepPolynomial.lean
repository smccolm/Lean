import Dubon2026.SourcePrimeAdjacentRelations

/-! DUB-17/18 -> numerical modular genus -> all-level original j-map degree
-> prime-power step degree. The actual adjacent prime relation has a known
previous-level root. Removing that linear factor gives a monic degree-p
polynomial for the next literal j series. This proves the needed upper
bound. SourcePrimePowerExactFieldDegree proves the matching lower bound
under the explicit next-series nonmembership condition. Deriving that
condition for the original fields remains required.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.lean.
The local bidirectional product replaces its polynomial-symmetry input.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField

theorem exists_prime_power_step_polynomial
    (F : IntermediateField ℚ (LaurentSeries ℚ))
    (p : ℕ) [hp : Fact p.Prime] (k : ℕ)
    (h0 : qExpand ℚ (p ^ k) jq ∈ F)
    (h1 : qExpand ℚ (p ^ (k + 1)) jq ∈ F) :
    ∃ P : Polynomial F, P.Monic ∧ P.natDegree = p ∧
      Polynomial.aeval (qExpand ℚ (p ^ (k + 2)) jq) P = 0 := by
  obtain ⟨R, hRm, hdeg, hR⟩ := exists_prime_adjacent_relations p
  let j0 : F := ⟨qExpand ℚ (p ^ k) jq, h0⟩
  let j1 : F := ⟨qExpand ℚ (p ^ (k + 1)) jq, h1⟩
  let Q := relationAtSeed R j1
  have hQm : Q.Monic := hRm.map _
  have hQdeg : Q.natDegree = p + 1 := (hRm.natDegree_map _).trans hdeg
  have hQmap : Q.map (algebraMap F (LaurentSeries ℚ)) =
      relationAtSeed R (qExpand ℚ (p ^ (k + 1)) jq) := relationAtSeed_map R j1 _
  have hQj : Q.IsRoot j0 := by
    apply (algebraMap F (LaurentSeries ℚ)).injective
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, hQmap]
    have h := (hR (p ^ k)).2
    simpa only [← pow_succ] using h
  let P := Q /ₘ (X - C j0)
  have hfact : (X - C j0) * P = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hQj
  have hPm : P.Monic := Polynomial.Monic.of_mul_monic_left
    (Polynomial.monic_X_sub_C j0) (hfact ▸ hQm)
  have hPdeg : P.natDegree = p := by
    have h := congrArg Polynomial.natDegree hfact
    rw [Polynomial.Monic.natDegree_mul (Polynomial.monic_X_sub_C j0) hPm,
      Polynomial.natDegree_X_sub_C, hQdeg] at h
    omega
  have hQroot : Polynomial.aeval (qExpand ℚ (p ^ (k + 2)) jq) Q = 0 := by
    rw [← Polynomial.eval_map_algebraMap, hQmap]
    have h := (hR (p ^ (k + 1))).1
    simpa only [← pow_succ, Nat.add_assoc] using h
  have hne : qExpand ℚ (p ^ (k + 2)) jq ≠ qExpand ℚ (p ^ k) jq := by
    intro h
    have he := Nat.pow_right_injective hp.out.two_le (qExpand_jq_injective h)
    omega
  refine ⟨P, hPm, hPdeg, ?_⟩
  have h : Polynomial.aeval (qExpand ℚ (p ^ (k + 2)) jq) ((X - C j0) * P) = 0 :=
    hfact ▸ hQroot
  rw [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h
  exact (mul_eq_zero.mp h).resolve_left (fun he => hne (sub_eq_zero.mp he))

theorem prime_power_step_finrank_le
    (F : IntermediateField ℚ (LaurentSeries ℚ))
    (p : ℕ) [Fact p.Prime] (k : ℕ)
    (h0 : qExpand ℚ (p ^ k) jq ∈ F)
    (h1 : qExpand ℚ (p ^ (k + 1)) jq ∈ F) :
    Module.finrank F (IntermediateField.adjoin F
      ({qExpand ℚ (p ^ (k + 2)) jq} : Set (LaurentSeries ℚ))) ≤ p := by
  obtain ⟨P, hm, hd, hr⟩ := exists_prime_power_step_polynomial F p k h0 h1
  have hi : IsIntegral F (qExpand ℚ (p ^ (k + 2)) jq) := ⟨P, hm, hr⟩
  rw [IntermediateField.adjoin.finrank hi]
  calc
    _ ≤ P.natDegree := Polynomial.natDegree_le_of_dvd (minpoly.dvd F _ hr) hm.ne_zero
    _ = p := hd

theorem original_prime_power_step_finrank_le (p : ℕ) [Fact p.Prime] (k : ℕ) :
    Module.finrank (modularFunctionFieldFull (p ^ (k + 1)))
      (IntermediateField.adjoin (modularFunctionFieldFull (p ^ (k + 1)))
        ({qExpand ℚ (p ^ (k + 2)) jq} : Set (LaurentSeries ℚ))) ≤ p := by
  exact prime_power_step_finrank_le _ p k
    (jqd_mem_full _ (pow_dvd_pow p (Nat.le_succ k)))
    (jqd_mem_full _ dvd_rfl)

end
end Dubon2026.SourceFunctionField
