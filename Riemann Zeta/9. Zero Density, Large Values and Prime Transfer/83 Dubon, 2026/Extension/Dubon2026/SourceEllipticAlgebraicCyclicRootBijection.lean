import Dubon2026.SourceEllipticPrimeFiberMultiplicity
import Dubon2026.SourceEllipticQuotientRangeConjugacy
import Dubon2026.SourceIntegralPrimeRootTranscendence
import Dubon2026.SourceCyclicFiberCounting

/-! The all-level actual cyclic-root bijection in an algebraically closed
field algebraic over its transcendental j-coordinate field. Strong induction
uses the actual prime quotient family, composition multiplicities and exact
cyclic counts. Existing coordinate exchange keeps the same field at each
step. The field-algebraicity condition is explicit; transport to arbitrary
algebraically closed overfields remains a separate required obligation. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial SourceEllipticCyclicCount SourceLevelProjective
open SourceFunctionField SourceFunctionField.IntegralJCoordinate
open scoped IntermediateField
noncomputable section
variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [DecidableEq F]
variable [IsAlgClosed F] [Algebra K F]

/-- Actual cyclic quotients biject with the original modular roots at every invertible level over an algebraic j-field closure. -/
theorem cyclicQuotientJ_bijOn_transcendental_algebraic
    (N : ℕ) [hNZ : NeZero N] (hNK : (N : K) ≠ 0) (hNF : (N : F) ≠ 0)
    (W : WeierstrassCurve F) [W.IsElliptic] (hj : Transcendental K W.j)
    [Algebra.IsAlgebraic K⟮W.j⟯ F] :
    Set.BijOn (cyclicQuotientJ W N hNF) Set.univ
      {y | (relationAtSeed (modularPolynomial N) W.j).IsRoot y} := by
  induction N using Nat.strong_induction_on generalizing W hNZ with
  | h N ih =>
    let A := {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}
    have hA : Nat.card A = dedekindPsi N := by
      simpa only [A, baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] using
        (actual_cyclic_subgroup_cardinality (F := F) (K := F) W hNF)
    letI : Finite A := Nat.finite_of_card_ne_zero (hA.trans_ne (dedekindPsi_pos (NeZero.ne N)).ne')
    letI : Fintype A := Fintype.ofFinite A
    by_cases hN1 : N = 1
    · subst N
      rw [dedekindPsi_one] at hA
      obtain ⟨H0, hall⟩ := Nat.card_eq_one_iff_exists.mp hA
      refine ⟨?_, ?_, ?_⟩
      · intro H _
        simp only [Set.mem_setOf_eq, modularPolynomial_one_fiber, IsRoot.def,
          eval_sub, eval_X, eval_C, cyclicQuotientJ_one, sub_self]
      · intro H _ H' _ _
        exact (hall H).trans (hall H').symm
      · intro y hy
        have he : y = W.j := by
          simpa only [Set.mem_setOf_eq, modularPolynomial_one_fiber, IsRoot.def,
            eval_sub, eval_X, eval_C, sub_eq_zero] using hy
        exact ⟨H0, Set.mem_univ _, (cyclicQuotientJ_one W H0).trans he.symm⟩
    · have ha := cyclicQuotient_prime_arithmetic N hNF hN1
      have haK := cyclicQuotient_prime_arithmetic N hNK hN1
      letI : Fact N.minFac.Prime := ⟨ha.1⟩
      letI : NeZero (N / N.minFac) := ⟨ha.2.1⟩
      obtain ⟨e, hdiv⟩ := exists_prime_quotient_fiber_composition W N.minFac (N / N.minFac) ha.2.2.2.1
      simp only [Nat.mul_div_cancel' (Nat.minFac_dvd N)] at hdiv
      let V := fun i => primeAbscissaQuotient W N.minFac (e i)
      letI : ∀ i, (V i).IsElliptic := fun i => primeAbscissaQuotient_isElliptic W N.minFac ha.2.2.2.1 (e i)
      have hzT (i) : Transcendental K (V i).j :=
        modularPolynomial_prime_root_transcendental N.minFac haK.2.2.2.1 hj
          (primeAbscissaQuotient_isRoot W N.minFac ha.2.2.2.1 (e i))
      have IHi (i) : Set.BijOn (cyclicQuotientJ (V i) (N / N.minFac) ha.2.2.2.2) Set.univ
          {y | (relationAtSeed (modularPolynomial (N / N.minFac)) (V i).j).IsRoot y} := by
        letI := SourceCurve.isAlgebraic_adjoin_of_transcendental W.j (hzT i)
        exact ih (N / N.minFac) ha.2.2.1 haK.2.2.2.2 ha.2.2.2.2 (V i) (hzT i)
      let P := relationAtSeed (modularPolynomial N) W.j
      let Pi := fun i => relationAtSeed (modularPolynomial (N / N.minFac)) (V i).j
      let Q := ∏ i, Pi i
      let R := P.roots.toFinset
      let M := Finset.univ.val.map (cyclicQuotientJ W N hNF)
      have hPm : P.Monic := (modularPolynomial_monic N).map _
      have hPi (i) : (Pi i).Monic := (modularPolynomial_monic (N / N.minFac)).map _
      have hQm : Q.Monic := monic_prod_of_monic _ _ fun i _ => hPi i
      have hsep : P.Separable := modularPolynomial_separable_transcendental N hNK W.j hj
      have hRv : R.val = P.roots := by
        rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (nodup_roots hsep)]
      have hRc : R.card = dedekindPsi N := by
        change R.val.card = _
        rw [hRv, ← (IsAlgClosed.splits P).natDegree_eq_card_roots]
        exact (modularPolynomial_monic N).natDegree_map _ |>.trans (modularPolynomial_natDegree N)
      have hRmem (y) : y ∈ R ↔ P.IsRoot y := by
        simp only [R, Multiset.mem_toFinset, mem_roots hPm.ne_zero]
      have hMmem (y) : y ∈ M ↔ y ∈ Set.range (cyclicQuotientJ W N hNF) := by
        simp only [M, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, Set.mem_range]
      have hMc : M.card = R.card := by
        dsimp only [M]
        rw [Multiset.card_map]
        change Fintype.card A = R.card
        rw [← Nat.card_eq_fintype_card, hA, hRc]
      have hMcount (y) : M.count y = Nat.card {H : A // cyclicQuotientJ W N hNF H = y} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        simp only [M, Multiset.count_map, ← Finset.filter_val, eq_comm]
        rfl
      have hMQ : M ≤ Q.roots := by
        apply Multiset.le_iff_count.mpr
        intro y
        rw [hMcount]
        exact cyclicQuotientJ_fiber_card_le_composition W N hNF hN1 e IHi y
      have hRQ : R.val ≤ Q.roots := by
        rw [hRv]
        exact Polynomial.roots.le_of_dvd hQm.ne_zero hdiv
      have hQdeg : Q.natDegree = (N.minFac + 1) * dedekindPsi (N / N.minFac) := by
        change (∏ i, Pi i).natDegree = _
        rw [natDegree_prod_of_monic _ _ fun i _ => hPi i]
        have hi (i) : (Pi i).natDegree = dedekindPsi (N / N.minFac) :=
          (modularPolynomial_monic (N / N.minFac)).natDegree_map _ |>.trans
            (modularPolynomial_natDegree (N / N.minFac))
        simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      have hbound : Q.roots.card < 2 * R.card := by
        apply lt_of_le_of_lt (card_roots' Q)
        rw [hQdeg, hRc]
        simpa only [Nat.mul_div_cancel' (Nat.minFac_dvd N)] using prime_composition_degree_lt ha.1 ha.2.1
      have horbit : ∀ x ∈ R, ∀ y ∈ R, x ∈ M ↔ y ∈ M := by
        intro x hx y hy
        rw [hMmem, hMmem]
        exact modular_roots_quotient_range_iff W N hNK hNF hj ((hRmem x).mp hx) ((hRmem y).mp hy)
      have hMR := quotient_multiset_eq_of_transitive_support R M Q.roots hMQ hRQ hMc hbound horbit
      have hn : M.Nodup := by rw [hMR]; exact R.nodup
      refine ⟨?_, ?_, ?_⟩
      · intro H _
        apply (hRmem _).mp
        change cyclicQuotientJ W N hNF H ∈ R.val
        rw [← hMR]
        exact (hMmem _).mpr ⟨H, rfl⟩
      · intro H _ H' _ he
        exact Multiset.inj_on_of_nodup_map hn H (Finset.mem_univ _) H' (Finset.mem_univ _) he
      · intro y hy
        have hym : y ∈ M := by
          rw [hMR]
          exact (hRmem y).mpr hy
        obtain ⟨H, he⟩ := (hMmem y).mp hym
        exact ⟨H, Set.mem_univ _, he⟩

end
end Dubon2026.SourceEllipticVelu
