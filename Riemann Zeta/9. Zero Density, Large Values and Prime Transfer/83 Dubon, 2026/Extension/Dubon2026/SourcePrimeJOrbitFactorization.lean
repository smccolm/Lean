import Dubon2026.SourceJPrimeOrbitObstruction

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime j nonmembership. These are the precise orbit
factorization and polynomial-root counting consequences used with the proved
Hasse identity. They do not assume or conclude prime nonmembership.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. The existing local prime degree,
monicity and root-of-unity orbit lemmas replace the archived prerequisites. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux

theorem prime_j_orbit_factorization {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) {R : Polynomial K}
    (hR : Polynomial.aeval (jqModC K) R = jqNModC K p) :
    R.Monic ∧ R.natDegree = p ∧
      R.map (algebraMap K (LaurentSeries K)) - Polynomial.C (jqNModC K p) =
        ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))) := by
  have hp : Fact p.Prime := inferInstance
  refine ⟨monic_of_aeval_eq hR, natDegree_eq_of_aeval_eq hR, ?_⟩

  set A : Polynomial (LaurentSeries K) := R.map (algebraMap K (LaurentSeries K)) with hA
  set B : Polynomial (LaurentSeries K) :=
    ∏ b : Fin p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ (b : ℕ)) (jqModC K))) with hB
  have hAmonic : A.Monic := (monic_of_aeval_eq hR).map _
  have hAdeg : A.natDegree = p := by
    rw [hA, (monic_of_aeval_eq hR).natDegree_map, natDegree_eq_of_aeval_eq hR]
  have hBmonic : B.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hBdeg : B.natDegree = p := by
    rw [hB, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  have key : A - B = Polynomial.C (jqNModC K p) := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _
      (qTwist_pow_jqModC_injective hζ) (fun b => ?_) ?_
    · have hAev : A.eval (qTwist (ζ ^ (b : ℕ)) (jqModC K)) = jqNModC K p := by
        rw [hA, Polynomial.eval_map_algebraMap]
        exact aeval_qTwist_jqModC_eq_of_aeval_eq hζ hR b
      have hBev : B.eval (qTwist (ζ ^ (b : ℕ)) (jqModC K)) = 0 := by
        rw [hB, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp)
      simp only [Polynomial.eval_sub, Polynomial.eval_C, hAev, hBev, sub_zero]
    · rw [Fintype.card_fin]
      refine max_lt ?_ (by rw [Polynomial.natDegree_C]; exact hp.out.pos)
      by_cases hAB : A = B
      · rw [hAB, sub_self, Polynomial.natDegree_zero]; exact hp.out.pos
      · refine lt_of_lt_of_eq (Polynomial.natDegree_lt_natDegree (sub_ne_zero.mpr hAB) ?_) hAdeg
        exact Polynomial.degree_sub_lt
          (by rw [Polynomial.degree_eq_natDegree hAmonic.ne_zero,
            Polynomial.degree_eq_natDegree hBmonic.ne_zero, hAdeg, hBdeg])
          hAmonic.ne_zero (by rw [hAmonic.leadingCoeff, hBmonic.leadingCoeff])

  have hconcl : A - Polynomial.C (jqNModC K p) = B := by
    rw [← key]; ring
  rw [hconcl, hB, Finset.prod_range]


end
end Dubon2026.SourceFunctionField
