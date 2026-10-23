import Dubon2026.SourceHasseCoefficientExpansion

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime j nonmembership -> Hasse polynomial.
The existing level-one polynomial theorem supplies the complex identity.
The integral, unitriangular q-expansions descend its coefficients to integers.
This proves the exact polynomial identity needed downstream, not prime
nonmembership or good reduction by itself.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_hassePolyDescent. Existing local j powers and the
level-one polynomial theorem are reused. No resource or pin changes. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial HahnSeries UpperHalfPlane
open scoped MatrixGroups

theorem hassePolyDescent {N : ℕ}
    (F : ModularForm 𝒮ℒ (12 * (N : ℤ))) {T : PowerSeries ℤ}
    (hT : T.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑F)
    (h0 : PowerSeries.constantCoeff T ≠ 0) :
    ∃ G : Polynomial ℤ, G.natDegree = N ∧ G.coeff N = PowerSeries.constantCoeff T ∧
      HahnSeries.ofPowerSeries ℤ ℤ T
        = Polynomial.aeval (jqModC ℤ) G
          * (HahnSeries.single (1 : ℤ) 1
              * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24) ^ N := by
  obtain ⟨P, hPdeg, hPid⟩ := exists_levelOne_j_polynomial N F
  rw [← jqModC_eq_modular_quotient, ← hT,
    qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit] at hPid
  have hXded : HahnSeries.ofPowerSeries ℤ ℂ
      ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom ℂ))
      = HahnSeries.single (1 : ℤ) 1
        * HahnSeries.ofPowerSeries ℤ ℂ (dedekindEtaUnit.map (Int.castRingHom ℂ)) := by
    rw [map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X]
  rw [hXded] at hPid

  have hCa : ∀ a : ℕ, (jNum ^ a * dedekindEtaUnit ^ N).map (Int.castRingHom ℂ)
      = jNum.map (Int.castRingHom ℂ) ^ a * dedekindEtaUnit.map (Int.castRingHom ℂ) ^ N := by
    intro a
    rw [map_mul, map_pow, map_pow]
  have hsum : Polynomial.aeval (jqModC ℂ) P
      * (HahnSeries.single (1 : ℤ) 1
          * HahnSeries.ofPowerSeries ℤ ℂ (dedekindEtaUnit.map (Int.castRingHom ℂ))) ^ N
      = ∑ a ∈ Finset.range (N + 1),
          HahnSeries.single (0 : ℤ) (P.coeff a)
            * (HahnSeries.single ((N : ℤ) - a) 1
                * HahnSeries.ofPowerSeries ℤ ℂ
                    ((jNum ^ a * dedekindEtaUnit ^ N).map (Int.castRingHom ℂ))) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum,
      Polynomial.sum_over_range' P (fun n => by rw [map_zero, zero_mul]) (N + 1)
        (Nat.lt_succ_of_le hPdeg), Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc, algebraMap_laurent_eq_single,
      jqModC_pow_mul_etaBlock ℂ a N, ← hCa a]
  rw [hsum] at hPid

  have hkey : ∀ i : ℕ, i ≤ N →
      ((PowerSeries.coeff (N - i) T : ℤ) : ℂ)
        = ∑ a ∈ Finset.range (N + 1), P.coeff a *
            (if i ≤ a
              then ((PowerSeries.coeff (a - i) (jNum ^ a * dedekindEtaUnit ^ N) : ℤ) : ℂ)
              else 0) := by
    intro i hi
    have h1 := congrArg (fun x : LaurentSeries ℂ => x.coeff ((N : ℤ) - i)) hPid
    have hL : (HahnSeries.ofPowerSeries ℤ ℂ (T.map (Int.castRingHom ℂ))).coeff ((N : ℤ) - i)
        = ((PowerSeries.coeff (N - i) T : ℤ) : ℂ) := by
      rw [show ((N : ℤ) - i) = ((N - i : ℕ) : ℤ) from by omega,
        HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, Int.coe_castRingHom]
    have hR : (∑ a ∈ Finset.range (N + 1),
          HahnSeries.single (0 : ℤ) (P.coeff a)
            * (HahnSeries.single ((N : ℤ) - a) 1
                * HahnSeries.ofPowerSeries ℤ ℂ
                    ((jNum ^ a * dedekindEtaUnit ^ N).map (Int.castRingHom ℂ)))).coeff
            ((N : ℤ) - i)
        = ∑ a ∈ Finset.range (N + 1), P.coeff a *
            (if i ≤ a
              then ((PowerSeries.coeff (a - i) (jNum ^ a * dedekindEtaUnit ^ N) : ℤ) : ℂ)
              else 0) := by
      rw [HahnSeries.coeff_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [HahnSeries.coeff_single_zero_mul]
      congr 1
      by_cases hia : i ≤ a
      · rw [if_pos hia, show ((N : ℤ) - i) = ((N : ℤ) - a) + ((a - i : ℕ) : ℤ) from by omega,
          coeff_single_mul_ofPowerSeries_nonneg, PowerSeries.coeff_map,
          Int.coe_castRingHom]
      · rw [if_neg hia]
        exact coeff_single_mul_ofPowerSeries_neg _ _ (by omega)
    dsimp only at h1
    rw [hL, hR] at h1
    exact h1

  have hdiag : ∀ i : ℕ, PowerSeries.coeff 0 (jNum ^ i * dedekindEtaUnit ^ N) = 1 := by
    intro i
    have h1 : PowerSeries.constantCoeff (jNum ^ i * dedekindEtaUnit ^ N) = 1 := by
      rw [map_mul, map_pow, map_pow, constantCoeff_jNum,
        constantCoeff_dedekindEtaUnit, one_pow, one_pow, one_mul]
    rw [← h1]
    exact congrFun PowerSeries.coeff_zero_eq_constantCoeff _

  have hPN : P.coeff N = ((PowerSeries.constantCoeff T : ℤ) : ℂ) := by
    have hk := hkey N le_rfl
    have hdiagN : (if N ≤ N
        then ((PowerSeries.coeff (N - N) (jNum ^ N * dedekindEtaUnit ^ N) : ℤ) : ℂ)
        else 0) = 1 := by
      rw [if_pos le_rfl, Nat.sub_self, hdiag N, Int.cast_one]
    rw [Finset.sum_eq_single_of_mem N (Finset.mem_range.mpr (Nat.lt_succ_self N))
      (fun a ha hne => by
        rw [if_neg (show ¬N ≤ a from by
          have := Finset.mem_range.mp ha
          omega), mul_zero]), hdiagN, mul_one, Nat.sub_self] at hk
    rw [← hk]
    congr 1
    exact congrFun PowerSeries.coeff_zero_eq_constantCoeff T

  have hstep : ∀ i : ℕ, i ≤ N →
      (∀ a : ℕ, a ≤ N → i < a → P.coeff a ∈ Set.range ⇑(Int.castRingHom ℂ)) →
      P.coeff i ∈ Set.range ⇑(Int.castRingHom ℂ) := by
    intro i hi hIH
    have hk := hkey i hi
    have hmem : i ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hdiagterm : (if i ≤ i
        then ((PowerSeries.coeff (i - i) (jNum ^ i * dedekindEtaUnit ^ N) : ℤ) : ℂ)
        else 0) = 1 := by
      rw [if_pos le_rfl, Nat.sub_self, hdiag i, Int.cast_one]
    rw [← Finset.add_sum_erase _ _ hmem, hdiagterm, mul_one] at hk
    have hPi : P.coeff i
        = ((PowerSeries.coeff (N - i) T : ℤ) : ℂ)
          - ∑ a ∈ (Finset.range (N + 1)).erase i, P.coeff a *
              (if i ≤ a
                then ((PowerSeries.coeff (a - i) (jNum ^ a * dedekindEtaUnit ^ N) : ℤ) : ℂ)
                else 0) := by
      rw [hk]
      ring
    rw [hPi]
    have hSmem : (∑ a ∈ (Finset.range (N + 1)).erase i, P.coeff a *
        (if i ≤ a
          then ((PowerSeries.coeff (a - i) (jNum ^ a * dedekindEtaUnit ^ N) : ℤ) : ℂ)
          else 0)) ∈ (Int.castRingHom ℂ).range := by
      refine Subring.sum_mem _ fun a ha => ?_
      by_cases hia : i ≤ a
      · have haN : a ≤ N := by
          have := Finset.mem_range.mp (Finset.mem_of_mem_erase ha)
          omega
        have hlt : i < a := lt_of_le_of_ne hia (Ne.symm (Finset.ne_of_mem_erase ha))
        obtain ⟨z, hz⟩ := hIH a haN hlt
        rw [if_pos hia, ← hz]
        refine Subring.mul_mem _ (RingHom.mem_range.mpr ⟨z, rfl⟩)
          (RingHom.mem_range.mpr
            ⟨PowerSeries.coeff (a - i) (jNum ^ a * dedekindEtaUnit ^ N),
              by rw [Int.coe_castRingHom]⟩)
      · rw [if_neg hia, mul_zero]
        exact Subring.zero_mem _
    obtain ⟨zS, hzS⟩ := RingHom.mem_range.mp hSmem
    exact ⟨PowerSeries.coeff (N - i) T - zS, by rw [map_sub, hzS, Int.coe_castRingHom]⟩

  have hmemP : ∀ i : ℕ, i ≤ N → P.coeff i ∈ Set.range ⇑(Int.castRingHom ℂ) := by
    have H : ∀ j : ℕ, ∀ i : ℕ, i ≤ N → N - i ≤ j →
        P.coeff i ∈ Set.range ⇑(Int.castRingHom ℂ) := by
      intro j
      induction j with
      | zero =>
        intro i hi hj
        exact hstep i hi fun a ha hia => absurd hia (by omega)
      | succ j IH =>
        intro i hi hj
        exact hstep i hi fun a ha hia => IH a ha (by omega)
    exact fun i hi => H N i hi (by omega)

  have hlifts : P ∈ Polynomial.lifts (Int.castRingHom ℂ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rcases (show n ≤ N ∨ N < n from by omega) with hn | hn
    · exact hmemP n hn
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hPdeg hn)]
      exact ⟨0, map_zero _⟩
  obtain ⟨G, hG⟩ := (Polynomial.mem_lifts P).mp hlifts

  have hGcoeff : ∀ n : ℕ, ((G.coeff n : ℤ) : ℂ) = P.coeff n := by
    intro n
    rw [← hG, Polynomial.coeff_map, Int.coe_castRingHom]
  have hGN : G.coeff N = PowerSeries.constantCoeff T := by
    apply Int.cast_injective (α := ℂ)
    rw [hGcoeff N, hPN]
  have hGdeg : G.natDegree = N := by
    refine le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_)
      (Polynomial.le_natDegree_of_ne_zero ?_)
    · apply Int.cast_injective (α := ℂ)
      rw [hGcoeff m, Int.cast_zero]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hPdeg hm)
    · rw [hGN]
      exact h0
  refine ⟨G, hGdeg, hGN, ?_⟩

  have hblock : HahnSeries.single (1 : ℤ) (1 : ℤ)
      * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24
      = HahnSeries.single (1 : ℤ) 1
        * HahnSeries.ofPowerSeries ℤ ℤ (dedekindEtaUnit.map (Int.castRingHom ℤ)) := by
    rw [← map_pow, ← dedekindEtaUnit, powerSeries_map_intCast_self]
  have hZsum : Polynomial.aeval (jqModC ℤ) G
      * (HahnSeries.single (1 : ℤ) 1
          * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24) ^ N
      = ∑ a ∈ Finset.range (N + 1),
          HahnSeries.single (0 : ℤ) (G.coeff a)
            * (HahnSeries.single ((N : ℤ) - a) 1
                * HahnSeries.ofPowerSeries ℤ ℤ (jNum ^ a * dedekindEtaUnit ^ N)) := by
    rw [hblock, Polynomial.aeval_def, Polynomial.eval₂_eq_sum,
      Polynomial.sum_over_range' G (fun n => by rw [map_zero, zero_mul]) (N + 1)
        (show G.natDegree < N + 1 by omega), Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc, algebraMap_laurent_eq_single,
      jqModC_pow_mul_etaBlock ℤ a N,
      powerSeries_map_intCast_self jNum,
      powerSeries_map_intCast_self dedekindEtaUnit]
  rw [hZsum]
  ext g
  have hfinal : (((HahnSeries.ofPowerSeries ℤ ℤ T).coeff g : ℤ) : ℂ)
      = (((∑ a ∈ Finset.range (N + 1),
          HahnSeries.single (0 : ℤ) (G.coeff a)
            * (HahnSeries.single ((N : ℤ) - a) 1
                * HahnSeries.ofPowerSeries ℤ ℤ (jNum ^ a * dedekindEtaUnit ^ N))).coeff g
          : ℤ) : ℂ) :=
    calc (((HahnSeries.ofPowerSeries ℤ ℤ T).coeff g : ℤ) : ℂ)
      = (HahnSeries.ofPowerSeries ℤ ℂ (T.map (Int.castRingHom ℂ))).coeff g :=
        (coeff_ofPowerSeries_map T g).symm
    _ = (∑ a ∈ Finset.range (N + 1),
          HahnSeries.single (0 : ℤ) (P.coeff a)
            * (HahnSeries.single ((N : ℤ) - a) 1
                * HahnSeries.ofPowerSeries ℤ ℂ
                    ((jNum ^ a * dedekindEtaUnit ^ N).map (Int.castRingHom ℂ)))).coeff g := by
        rw [hPid]
    _ = ∑ a ∈ Finset.range (N + 1),
          (((HahnSeries.single (0 : ℤ) (G.coeff a)
              * (HahnSeries.single ((N : ℤ) - a) 1
                  * HahnSeries.ofPowerSeries ℤ ℤ (jNum ^ a * dedekindEtaUnit ^ N))).coeff g
            : ℤ) : ℂ) := by
        rw [HahnSeries.coeff_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [HahnSeries.coeff_single_zero_mul, HahnSeries.coeff_single_zero_mul,
          Int.cast_mul, ← hGcoeff a]
        congr 1
        rw [HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul, one_mul, one_mul]
        exact coeff_ofPowerSeries_map _ _
    _ = (((∑ a ∈ Finset.range (N + 1),
          HahnSeries.single (0 : ℤ) (G.coeff a)
            * (HahnSeries.single ((N : ℤ) - a) 1
                * HahnSeries.ofPowerSeries ℤ ℤ (jNum ^ a * dedekindEtaUnit ^ N))).coeff g
          : ℤ) : ℂ) := by
        rw [HahnSeries.coeff_sum]
        exact (map_sum (Int.castRingHom ℂ) _ _).symm
  exact_mod_cast hfinal


end
end Dubon2026.SourceFunctionField
