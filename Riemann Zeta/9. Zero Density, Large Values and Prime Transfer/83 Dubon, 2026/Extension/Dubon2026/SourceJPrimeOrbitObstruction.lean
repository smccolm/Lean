import Dubon2026.SourceJPrimePolynomialDegree

/-! DUB-17/18 -> numerical modular genus -> exact j-map degree ->
prime lower bound. The literal q-substituted j series cannot be a polynomial
in j: its root-of-unity orbit would force a positive j coefficient to vanish.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean.
Only the coefficient obstruction is selected; field integrality is supplied
by the already proved actual monic relation, without an irreducibility input.
-/
namespace Dubon2026.SourceFunctionField.PrimeDegreeAux
noncomputable section
variable {K : Type*} [Field K]

section Transfer

theorem qTwist_algebraMap (v : Kˣ) (c : K) :
    qTwist v (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) c := by
  ext k
  rw [qTwist_coeff, SourceDifferential.algebraMap_laurentSeries_apply_alt]
  by_cases hk : k = 0
  · subst k
    simp only [zpow_zero, Units.val_one, one_mul]
  · rw [HahnSeries.coeff_single_of_ne hk, mul_zero]

theorem qTwist_comp_algebraMap (v : Kˣ) :
    (qTwist v).comp (algebraMap K (LaurentSeries K)) = algebraMap K (LaurentSeries K) :=
  RingHom.ext fun c => qTwist_algebraMap v c

variable {p : ℕ} [hp : Fact (Nat.Prime p)] {ζ : Kˣ} {P : Polynomial K}

theorem aeval_qTwist_jqModC_eq_of_aeval_eq (hζ : IsPrimitiveRoot (ζ : K) p)
    (h : Polynomial.aeval (jqModC K) P = jqNModC K p) (b : ℕ) :
    Polynomial.aeval (qTwist (ζ ^ b) (jqModC K)) P = jqNModC K p := by
  have hζp : ζ ^ p = 1 := units_pow_eq_one_of_isPrimitiveRoot hζ
  have hvb : (ζ ^ b) ^ p = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hζp, one_pow]
  have h2 := congrArg (qTwist (ζ ^ b)) h
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, qTwist_comp_algebraMap, jqNModC,
    qTwist_qExpand_of_pow_eq_one p (ζ ^ b) hvb] at h2
  rw [Polynomial.aeval_def]
  exact h2

end Transfer

section Vieta

variable {p : ℕ} [hp : Fact (Nat.Prime p)] {ζ : Kˣ} {P : Polynomial K}

private theorem qTwist_jqModC_eq_TS' (u : Kˣ) : qTwist u (jqModC K) = TS K 1 u := by
  rw [TS, qExpand_one_apply]

omit hp in
theorem qTwist_pow_jqModC_injective (hζ : IsPrimitiveRoot (ζ : K) p) :
    Function.Injective (fun b : Fin p => qTwist (ζ ^ (b : ℕ)) (jqModC K)) := by
  intro b b' h
  have h1 : qTwist (ζ ^ (b : ℕ)) (jqModC K) = qTwist (ζ ^ (b' : ℕ)) (jqModC K) := h
  rw [qTwist_jqModC_eq_TS', qTwist_jqModC_eq_TS'] at h1
  have h2 : ζ ^ (b : ℕ) = ζ ^ (b' : ℕ) := (TS_injective h1).2
  have h3 : ((ζ : Kˣ) : K) ^ (b : ℕ) = ((ζ : Kˣ) : K) ^ (b' : ℕ) := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h2]
  exact Fin.ext (hζ.pow_inj b.isLt b'.isLt h3)

theorem sum_qTwist_jqModC_eq_of_aeval_eq (hζ : IsPrimitiveRoot (ζ : K) p)
    (h : Polynomial.aeval (jqModC K) P = jqNModC K p) :
    ∑ b : Fin p, qTwist (ζ ^ (b : ℕ)) (jqModC K) = algebraMap K (LaurentSeries K) (-P.coeff (p - 1)) := by
  have hPdeg : P.natDegree = p := natDegree_eq_of_aeval_eq h
  have hPmonic : P.Monic := monic_of_aeval_eq h
  set A : Polynomial (LaurentSeries K) := P.map (algebraMap K (LaurentSeries K)) with hA
  set B : Polynomial (LaurentSeries K) :=
    ∏ b : Fin p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ (b : ℕ)) (jqModC K))) with hB
  have hAmonic : A.Monic := hPmonic.map _
  have hAdeg : A.natDegree = p := by rw [hA, hPmonic.natDegree_map, hPdeg]
  have hBmonic : B.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hBdeg : B.natDegree = p := by
    rw [hB, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  have key : A - B = Polynomial.C (jqNModC K p) := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (qTwist_pow_jqModC_injective hζ) (fun b => ?_) ?_
    · have hAev : A.eval (qTwist (ζ ^ (b : ℕ)) (jqModC K)) = jqNModC K p := by
        rw [hA, Polynomial.eval_map_algebraMap]
        exact aeval_qTwist_jqModC_eq_of_aeval_eq hζ h b
      have hBev : B.eval (qTwist (ζ ^ (b : ℕ)) (jqModC K)) = 0 := by
        rw [hB, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp)
      simp only [Polynomial.eval_sub, Polynomial.eval_C, hAev, hBev, sub_zero]
    · rw [Fintype.card_fin]
      refine max_lt ?_ (by rw [Polynomial.natDegree_C]; exact hp.out.pos)
      by_cases hAB : A = B
      · rw [hAB, sub_self, Polynomial.natDegree_zero]
        exact hp.out.pos
      · refine lt_of_lt_of_eq (Polynomial.natDegree_lt_natDegree (sub_ne_zero.mpr hAB) ?_) hAdeg
        exact Polynomial.degree_sub_lt
          (by rw [Polynomial.degree_eq_natDegree hAmonic.ne_zero, Polynomial.degree_eq_natDegree hBmonic.ne_zero,
            hAdeg, hBdeg])
          hAmonic.ne_zero (by rw [hAmonic.leadingCoeff, hBmonic.leadingCoeff])
  have hcoeff := congrArg (fun Q : Polynomial (LaurentSeries K) => Q.coeff (p - 1)) key
  have hp2 : 2 ≤ p := hp.out.two_le
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by omega : ¬(p - 1 = 0))] at hcoeff
  have hBcoeff : B.coeff (p - 1) = -∑ b : Fin p, qTwist (ζ ^ (b : ℕ)) (jqModC K) := by
    have hv := Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin p))
      (fun b => qTwist (ζ ^ (b : ℕ)) (jqModC K)) (by simp [hp.out.pos])
    simpa using hv
  have hAcoeff : A.coeff (p - 1) = algebraMap K (LaurentSeries K) (P.coeff (p - 1)) := Polynomial.coeff_map _ _
  rw [hAcoeff, hBcoeff, sub_neg_eq_add, add_comm] at hcoeff
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_left hcoeff

end Vieta

section Collapse

variable {p : ℕ} [hp : Fact (Nat.Prime p)] {ζ : Kˣ}

omit hp in

theorem coeff_sum_qTwist_jqModC (hζ : IsPrimitiveRoot (ζ : K) p) (m : ℕ) :
    (∑ b : Fin p, qTwist (ζ ^ (b : ℕ)) (jqModC K)).coeff ((p * m : ℕ) : ℤ)
      = (p : K) * (jqModC K).coeff ((p * m : ℕ) : ℤ) := by
  have hζp : ζ ^ p = 1 := units_pow_eq_one_of_isPrimitiveRoot hζ
  rw [HahnSeries.coeff_sum]
  have hterm : ∀ b : Fin p,
      (qTwist (ζ ^ (b : ℕ)) (jqModC K)).coeff ((p * m : ℕ) : ℤ) = (jqModC K).coeff ((p * m : ℕ) : ℤ) := by
    intro b
    rw [qTwist_coeff, zpow_natCast, ← pow_mul, Nat.mul_comm (b : ℕ), Nat.mul_assoc, pow_mul, hζp, one_pow,
      Units.val_one, one_mul]
  rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem aeval_jqModC_ne_jqNModC_of_isPrimitiveRoot (hpK : (p : K) ≠ 0) (hζ : IsPrimitiveRoot (ζ : K) p) {m : ℕ}
    (hm : 0 < m) (hw : (jqModC K).coeff ((p * m : ℕ) : ℤ) ≠ 0) (P : Polynomial K) :
    Polynomial.aeval (jqModC K) P ≠ jqNModC K p := by
  intro h
  have h1 := sum_qTwist_jqModC_eq_of_aeval_eq hζ h
  have h2 := coeff_sum_qTwist_jqModC hζ m
  have hne : ((p * m : ℕ) : ℤ) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero hp.out.ne_zero hm.ne'
  rw [h1, SourceDifferential.algebraMap_laurentSeries_apply_alt, HahnSeries.coeff_single_of_ne hne] at h2
  exact mul_ne_zero hpK hw h2.symm

end Collapse
end
end Dubon2026.SourceFunctionField.PrimeDegreeAux
