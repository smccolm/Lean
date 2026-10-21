import Dubon2026.SourcePrimeExpandedProduct
import Dubon2026.SourcePrimePowerCyclotomicCycle
import Dubon2026.SourcePrimePowerStepPolynomial
import Dubon2026.SourcePrimeOrbitIrreducibility

/-! DUB-17/18 -> numerical modular genus -> exact composite j-map degree.
The rational prime-power step has degree p when the next literal j series
is outside the preceding field. Both adjacent relations and the upper
degree bound are already proved. The actual cyclotomic coefficient action
cycles all remaining nondistinguished roots after the known root is removed.
Original all-level generation and nonmembership must still be established.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux

theorem prime_power_step_finrank_eq_of_not_mem
    (F : IntermediateField ℚ (LaurentSeries ℚ))
    (p : ℕ) [hp : Fact p.Prime] (k : ℕ)
    (h0 : qExpand ℚ (p ^ k) jq ∈ F)
    (h1 : qExpand ℚ (p ^ (k + 1)) jq ∈ F)
    (hF : qExpand ℚ (p ^ (k + 2)) jq ∉ F) :
    Module.finrank F (IntermediateField.adjoin F
      ({qExpand ℚ (p ^ (k + 2)) jq} : Set (LaurentSeries ℚ))) = p := by
  classical
  refine le_antisymm (prime_power_step_finrank_le F p k h0 h1) ?_
  let K := CyclotomicField p ℚ
  haveI : NeZero (p : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K
    (Set.mem_singleton p) hp.out.ne_zero
  let ζ := (hz.isUnit hp.out.ne_zero).unit
  have hζ : IsPrimitiveRoot (ζ : K) p := by
    rw [show (ζ : K) = z from (hz.isUnit hp.out.ne_zero).unit_spec]
    exact hz
  obtain ⟨R, hRm, hRdeg, hRprod⟩ := exists_prime_monic_degree_product p ζ hζ
  have hf := prime_product_forward_root p K ζ R hRprod
  have hr := prime_product_reverse_root p K ζ R hRprod
  let j0 : F := ⟨qExpand ℚ (p ^ k) jq, h0⟩
  let j1 : F := ⟨qExpand ℚ (p ^ (k + 1)) jq, h1⟩
  let Q := relationAtSeed R j1
  have hQm : Q.Monic := hRm.map _
  have hQdeg : Q.natDegree = p + 1 := (hRm.natDegree_map _).trans hRdeg
  have hQmap : Q.map (algebraMap F (LaurentSeries ℚ)) =
      relationAtSeed R (qExpand ℚ (p ^ (k + 1)) jq) := relationAtSeed_map R j1 _
  have hQj : Q.IsRoot j0 := by
    apply (algebraMap F (LaurentSeries ℚ)).injective
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, hQmap]
    have h := relationAtSeed_reverse_substitution_eval R hr (p ^ k)
    simpa only [← pow_succ] using h
  let P := Q /ₘ (X - C j0)
  have hfact : (X - C j0) * P = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hQj
  have hPm : P.Monic := Polynomial.Monic.of_mul_monic_left
    (Polynomial.monic_X_sub_C j0) (hfact ▸ hQm)
  have hQroot : Polynomial.aeval (qExpand ℚ (p ^ (k + 2)) jq) Q = 0 := by
    rw [← Polynomial.eval_map_algebraMap, hQmap]
    have h := relationAtSeed_substitution_eval R hf (p ^ (k + 1))
    simpa only [← pow_succ, Nat.add_assoc] using h
  have hProot : Polynomial.aeval (qExpand ℚ (p ^ (k + 2)) jq) P = 0 := by
    have h : Polynomial.aeval (qExpand ℚ (p ^ (k + 2)) jq) ((X - C j0) * P) = 0 :=
      hfact ▸ hQroot
    rw [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h
    refine (mul_eq_zero.mp h).resolve_left fun he => ?_
    exact hF (sub_eq_zero.mp he ▸ h0)
  have hint : IsIntegral F (qExpand ℚ (p ^ (k + 2)) jq) := ⟨P, hPm, hProot⟩
  let ι := (coeffEmb K).comp (qExpand ℚ p)
  have hdegree : P.natDegree = p ∧ Irreducible P := by
    letI : Algebra F (LaurentSeries K) := (ι.comp (algebraMap F (LaurentSeries ℚ))).toAlgebra
    have halg : ∀ a : F, algebraMap F (LaurentSeries K) a = ι a := fun _ => rfl
    have hQmapL : Q.map (algebraMap F (LaurentSeries K)) =
        relationAtSeed R (qExpand K (p ^ (k + 1) * p) (coeffEmb K jq)) := by
      rw [RingHom.algebraMap_toAlgebra, ← Polynomial.map_map, hQmap, relationAtSeed_map]
      congr 1
      change coeffEmb K (qExpand ℚ p (qExpand ℚ (p ^ (k + 1)) jq)) = _
      rw [qExpand_qExpand]
      have h := coeffMap_qExpand (algebraMap ℚ K) (p * p ^ (k + 1)) jq
      simpa only [Nat.mul_comm p (p ^ (k + 1))] using h
    have hQroots : (Q.map (algebraMap F (LaurentSeries K))).roots =
        TS K (p ^ (k + 1) * (p * p)) 1 ::ₘ
          (Multiset.range p).map (fun b => TS K (p ^ (k + 1)) (ζ ^ b)) := by
      rw [hQmapL]
      exact prime_product_expanded_roots p ζ R hRprod _
    have hQnodup : (Q.map (algebraMap F (LaurentSeries K))).roots.Nodup := by
      rw [hQroots]
      exact prime_expanded_root_list_nodup p ζ hζ _
    have hjL : algebraMap F (LaurentSeries K) j0 = TS K (p ^ (k + 1)) 1 := by
      rw [halg]
      change coeffEmb K (qExpand ℚ p (qExpand ℚ (p ^ k) jq)) = _
      rw [qExpand_qExpand, coeffEmb_qExpand_jq_eq_TS]
      exact TS_congr (pow_succ' p k).symm 1
    have hQPmapL : Q.map (algebraMap F (LaurentSeries K)) =
        (X - C (TS K (p ^ (k + 1)) 1)) * P.map (algebraMap F (LaurentSeries K)) := by
      rw [← hfact, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hjL]
    have hQm0 : Q.map (algebraMap F (LaurentSeries K)) ≠ 0 := (hQm.map _).ne_zero
    have hsum : (Q.map (algebraMap F (LaurentSeries K))).roots =
        TS K (p ^ (k + 1)) 1 ::ₘ (P.map (algebraMap F (LaurentSeries K))).roots := by
      rw [hQPmapL, Polynomial.roots_mul (hQPmapL ▸ hQm0), Polynomial.roots_X_sub_C,
        Multiset.singleton_add]
    obtain ⟨g, τ, hg, hcycle⟩ := exists_cyclotomic_root_cycle p K ζ hζ (p ^ (k + 1))
    have hProots : (P.map (algebraMap F (LaurentSeries K))).roots =
        TS K (p ^ (k + 1) * (p * p)) 1 ::ₘ
          (Multiset.range (p - 1)).map (rUnit (p ^ (k + 1)) ζ g) := by
      have h := hsum.symm.trans hQroots
      rw [range_map_eq_rUnit p _ ζ hζ g hg, Multiset.cons_swap] at h
      exact (Multiset.cons_inj_right _).mp h
    have hPnodup : (P.map (algebraMap F (LaurentSeries K))).roots.Nodup := by
      rw [hsum] at hQnodup
      exact (Multiset.nodup_cons.mp hQnodup).2
    have hQsplit : (Q.map (algebraMap F (LaurentSeries K))).Splits := by
      rw [Polynomial.splits_iff_card_roots, hQroots, Multiset.card_cons,
        Multiset.card_map, Multiset.card_range, hQm.natDegree_map, hQdeg]
    have hPsplits : (P.map (algebraMap F (LaurentSeries K))).Splits :=
      hQsplit.of_dvd hQm0 ⟨X - C (TS K (p ^ (k + 1)) 1), hQPmapL.trans (mul_comm _ _)⟩
    have hPdeg : P.natDegree = p := by
      rw [← hPm.natDegree_map (algebraMap F (LaurentSeries K)),
        hPsplits.natDegree_eq_card_roots, hProots,
        Multiset.card_cons, Multiset.card_map, Multiset.card_range]
      have hp2 := hp.out.two_le
      omega
    refine ⟨hPdeg, irreducible_of_transitive_ringAut P hPm hPsplits
      (coeffMapEquiv τ) ?_ _ _ (p - 1) hProots hPnodup (fun i _ => hcycle i) ?_⟩
    · intro a
      rw [halg, coeffMapEquiv_apply]
      exact coeffMap_coeffEmb_algHom (τ : K →ₐ[ℚ] K) (qExpand ℚ p (a : LaurentSeries ℚ))
    · rintro ⟨a, ha⟩
      rw [halg] at ha
      have he : ι (qExpand ℚ (p ^ (k + 2)) jq) = TS K (p ^ (k + 1) * (p * p)) 1 := by
        change coeffEmb K (qExpand ℚ p (qExpand ℚ (p ^ (k + 2)) jq)) = _
        rw [qExpand_qExpand, coeffEmb_qExpand_jq_eq_TS]
        apply TS_congr
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        ring
      exact hF (ι.injective (ha.trans he.symm) ▸ a.2)
  have hmin : P = minpoly F (qExpand ℚ (p ^ (k + 2)) jq) :=
    minpoly.eq_of_irreducible_of_monic hdegree.2 hProot hPm
  rw [IntermediateField.adjoin.finrank hint, ← hmin, hdegree.1]

theorem original_prime_power_step_finrank_eq_of_not_mem
    (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hF : qExpand ℚ (p ^ (k + 2)) jq ∉ modularFunctionFieldFull (p ^ (k + 1))) :
    Module.finrank (modularFunctionFieldFull (p ^ (k + 1)))
      (IntermediateField.adjoin (modularFunctionFieldFull (p ^ (k + 1)))
        ({qExpand ℚ (p ^ (k + 2)) jq} : Set (LaurentSeries ℚ))) = p :=
  prime_power_step_finrank_eq_of_not_mem _ p k
    (jqd_mem_full _ (pow_dvd_pow p (Nat.le_succ k))) (jqd_mem_full _ dvd_rfl) hF

end
end Dubon2026.SourceFunctionField
