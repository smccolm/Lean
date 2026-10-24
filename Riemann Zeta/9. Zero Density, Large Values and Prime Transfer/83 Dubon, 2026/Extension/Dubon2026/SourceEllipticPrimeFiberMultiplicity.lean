import Dubon2026.SourceEllipticCompositeQuotientStep
import Dubon2026.SourceEllipticPrimeFiberComposition
import Dubon2026.SourceIntegralCyclicInductionArithmetic

/-! The actual composite quotient multiset fits inside the prime composition
root multiset. The explicit lower-level bijections are induction hypotheses
at the strictly smaller level N/minFac N. Exact kernel uniqueness, actual
image orders and the proved recursive value identity derive the bound;
neither a level-N root relation nor injectivity is assumed. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial SourceEllipticCyclicCount SourceLevelProjective
open SourceFunctionField SourceFunctionField.IntegralJCoordinate
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

/-- Lower-level quotient bijections bound each actual level-N fiber by the full composition multiplicity. -/
theorem cyclicQuotientJ_fiber_card_le_composition
    (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ) (hN : (N : F) ≠ 0) (hN1 : N ≠ 1) :
    let ha := cyclicQuotient_prime_arithmetic N hN hN1
    letI : Fact N.minFac.Prime := ⟨ha.1⟩
    letI : NeZero (N / N.minFac) := ⟨ha.2.1⟩
    ∀ e : Fin (N.minFac + 1) ≃
        {D : AddSubgroup W.toAffine.Point // IsAddCyclic D ∧ Nat.card D = N.minFac},
    let V := fun i => primeAbscissaQuotient W N.minFac (e i)
    letI : ∀ i, (V i).IsElliptic := fun i => primeAbscissaQuotient_isElliptic W N.minFac ha.2.2.2.1 (e i)
    (∀ i, Set.BijOn (cyclicQuotientJ (V i) (N / N.minFac) ha.2.2.2.2) Set.univ
      {y | (relationAtSeed (modularPolynomial (N / N.minFac)) (V i).j).IsRoot y}) →
    ∀ y, Nat.card {H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} //
        cyclicQuotientJ W N hN H = y} ≤
      (∏ i, relationAtSeed (modularPolynomial (N / N.minFac)) (V i).j).roots.count y := by
  intro ha e V IH y
  letI : Fact N.minFac.Prime := ⟨ha.1⟩
  letI : NeZero (N / N.minFac) := ⟨ha.2.1⟩
  letI : ∀ i, (V i).IsElliptic := fun i => primeAbscissaQuotient_isElliptic W N.minFac ha.2.2.2.1 (e i)
  let A := {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  have hA : Nat.card A = dedekindPsi N := by
    simpa only [A, baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] using
      (actual_cyclic_subgroup_cardinality (F := F) (K := F) W hN)
  letI : Finite A := Nat.finite_of_card_ne_zero (hA.trans_ne (dedekindPsi_pos hN0).ne')
  letI : Fintype A := Fintype.ofFinite A
  let φ := fun i => primeAbscissaHom W N.minFac ha.2.2.2.1 (e i)
  have hker (i) : (φ i).ker = (e i).1 := primeAbscissaHom_ker W N.minFac ha.2.2.2.1 (e i)
  have hs (H : A) (i) (hi : (e i).1 ≤ H.1) :
      IsAddCyclic (H.1.map (φ i)) ∧ Nat.card (H.1.map (φ i)) = N / N.minFac :=
    cyclic_image_card_of_kernel (φ i) ha.1.ne_zero H.1 H.2.1
      (H.2.2.trans (Nat.mul_div_cancel' (Nat.minFac_dvd N)).symm)
      ((hker i) ▸ hi) ((hker i) ▸ (e i).2.2)
  have hval (H : A) (i) (hi : (e i).1 ≤ H.1) :
      cyclicQuotientJ W N hN H =
        cyclicQuotientJ (V i) (N / N.minFac) ha.2.2.2.2
          ⟨H.1.map (φ i), (hs H i hi).1, (hs H i hi).2⟩ :=
    cyclicQuotientJ_step W N hN hN1 H (e i) hi (hs H i hi).1 (hs H i hi).2
  let iOf := fun H : A => e.symm (cyclicQuotientLeastKernel W N hN hN1 H.1 H.2.1 H.2.2)
  have hiOf (H : A) : (e (iOf H)).1 ≤ H.1 := by
    simp only [iOf, Equiv.apply_symm_apply, cyclicQuotientLeastKernel]
    exact inf_le_left
  let P := fun i => relationAtSeed (modularPolynomial (N / N.minFac)) (V i).j
  have hroot (H : A) (i) (hi : (e i).1 ≤ H.1) : (P i).IsRoot (cyclicQuotientJ W N hN H) := by
    rw [hval H i hi]
    exact (IH i).mapsTo (Set.mem_univ _)
  have hc : Nat.card {H : A // cyclicQuotientJ W N hN H = y} =
      (Finset.univ.filter fun H : A => cyclicQuotientJ W N hN H = y).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc]
  refine le_trans (Finset.card_le_card_of_injOn iOf
    (t := Finset.univ.filter fun i => (P i).IsRoot y) ?_ ?_) ?_
  · intro H hH
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hH ⊢
    exact hH ▸ hroot H (iOf H) (hiOf H)
  · intro H hH H' hH' hii
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hH hH'
    have hi' : (e (iOf H)).1 ≤ H'.1 := hii ▸ hiOf H'
    have hv : cyclicQuotientJ (V (iOf H)) (N / N.minFac) ha.2.2.2.2
        ⟨H.1.map (φ (iOf H)), (hs H _ (hiOf H)).1, (hs H _ (hiOf H)).2⟩ =
      cyclicQuotientJ (V (iOf H)) (N / N.minFac) ha.2.2.2.2
        ⟨H'.1.map (φ (iOf H)), (hs H' _ hi').1, (hs H' _ hi').2⟩ := by
      rw [← hval H _ (hiOf H), ← hval H' _ hi', hH, hH']
    have hm := (IH (iOf H)).injOn (Set.mem_univ _) (Set.mem_univ _) hv
    apply Subtype.ext
    have hmaps := congrArg Subtype.val hm
    have hk : (φ (iOf H)).ker ≤ H.1 := (hker _) ▸ hiOf H
    have hk' : (φ (iOf H)).ker ≤ H'.1 := (hker _) ▸ hi'
    rw [← AddSubgroup.comap_map_eq_self hk, ← AddSubgroup.comap_map_eq_self hk']
    exact congrArg (AddSubgroup.comap (φ (iOf H))) hmaps
  · have hmonic (i) : (P i).Monic := (modularPolynomial_monic (N / N.minFac)).map _
    have hprod0 : (∏ i, P i) ≠ 0 := (monic_prod_of_monic _ _ fun i _ => hmonic i).ne_zero
    change _ ≤ (∏ i, P i).roots.count y
    rw [Polynomial.roots_prod _ _ hprod0, Multiset.count_bind, Finset.card_filter,
      ← Finset.sum_eq_multiset_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h
    · rw [count_roots]
      exact (Polynomial.rootMultiplicity_pos (hmonic i).ne_zero).mpr h
    · exact Nat.zero_le _

end
end Dubon2026.SourceEllipticVelu
