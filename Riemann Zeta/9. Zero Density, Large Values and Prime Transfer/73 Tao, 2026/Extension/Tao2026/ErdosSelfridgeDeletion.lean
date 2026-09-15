import Tao2026.ErdosSelfridgeProductSeparation

/-!
# The deletion lemma in the Erdős--Selfridge setup

This file formalizes Lemma 2 on journal pages 294--295 of Erdős--Selfridge
(1975).  One interval position of maximal `p`-adic valuation is marked for
each prime `p < H`; after deleting those positions, the product of the
canonical power-free coefficients divides `(H - 1)!`.
-/

namespace Tao2026

/-- The product of the nonzero distances from one position in `range H`.
This is the factorial identity used in the proof of source Lemma 2. -/
theorem prod_range_erase_dist_eq_factorials {H m : ℕ} (hm : m < H) :
    ∏ i ∈ (Finset.range H).erase m, Nat.dist i m =
      m.factorial * (H - 1 - m).factorial := by
  induction H with
  | zero => omega
  | succ H ih =>
      by_cases hmH : m = H
      · subst m
        have herase : (Finset.range (H + 1)).erase H = Finset.range H := by
          ext i
          simp only [Finset.mem_erase, Finset.mem_range]
          omega
        rw [herase]
        have hreflect := Finset.prod_range_reflect (fun j : ℕ => j + 1) H
        have hprod : (Finset.range H).prod (fun i => Nat.dist i H) =
            H.factorial := by
          calc
            (Finset.range H).prod (fun i => Nat.dist i H) =
                (Finset.range H).prod (fun i => (H - 1 - i) + 1) := by
                  refine Finset.prod_congr rfl ?_
                  intro i hi
                  have hiH : i < H := Finset.mem_range.mp hi
                  rw [Nat.dist_eq_sub_of_le hiH.le]
                  omega
            _ = (Finset.range H).prod (fun j => j + 1) := hreflect
            _ = H.factorial := by
              exact Finset.prod_range_add_one_eq_factorial H
        simpa using hprod
      · have hmOld : m < H := by omega
        have hHnot : H ∉ (Finset.range H).erase m := by simp
        have herase : (Finset.range (H + 1)).erase m =
            insert H ((Finset.range H).erase m) := by
          ext i
          simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert]
          omega
        rw [herase, Finset.prod_insert hHnot, ih hmOld]
        have hdist : Nat.dist H m = H - m := by
          rw [Nat.dist_eq_sub_of_le_right hmOld.le]
        rw [hdist]
        have hsub : H - m = (H - 1 - m) + 1 := by omega
        have hfinal : H + 1 - 1 - m = (H - 1 - m) + 1 := by omega
        rw [hsub, hfinal, Nat.factorial_succ]
        ring

/-- For a prime `p`, choose a position whose corresponding interval element
has maximal `p`-adic valuation.  The zero-length branch is a harmless default. -/
noncomputable def erdosSelfridgeMaxValuationIndex (N H p : ℕ) : ℕ :=
  if h : (Finset.range H).Nonempty then
    Classical.choose
      ((Finset.range H).exists_max_image
        (fun i => (N + (i + 1)).factorization p) h)
  else 0

theorem erdosSelfridgeMaxValuationIndex_mem {N H p : ℕ} (hH : 0 < H) :
    erdosSelfridgeMaxValuationIndex N H p ∈ Finset.range H := by
  have hne : (Finset.range H).Nonempty := ⟨0, Finset.mem_range.mpr hH⟩
  rw [erdosSelfridgeMaxValuationIndex, dif_pos hne]
  exact (Classical.choose_spec
    ((Finset.range H).exists_max_image
      (fun i => (N + (i + 1)).factorization p) hne)).1

theorem factorization_le_at_erdosSelfridgeMaxValuationIndex
    {N H p i : ℕ} (hH : 0 < H) (hi : i ∈ Finset.range H) :
    (N + (i + 1)).factorization p ≤
      (N + (erdosSelfridgeMaxValuationIndex N H p + 1)).factorization p := by
  have hne : (Finset.range H).Nonempty := ⟨0, Finset.mem_range.mpr hH⟩
  rw [erdosSelfridgeMaxValuationIndex, dif_pos hne]
  exact (Classical.choose_spec
    ((Finset.range H).exists_max_image
      (fun j => (N + (j + 1)).factorization p) hne)).2 i hi

/-- The source deletion set: one maximal-valuation position is marked for
each prime strictly below the interval length. -/
noncomputable def erdosSelfridgeDeletionSet (N H : ℕ) : Finset ℕ :=
  (Nat.primesBelow H).image (erdosSelfridgeMaxValuationIndex N H)

theorem erdosSelfridgeDeletionSet_subset_range {N H : ℕ} (hH : 0 < H) :
    erdosSelfridgeDeletionSet N H ⊆ Finset.range H := by
  intro i hi
  rw [erdosSelfridgeDeletionSet, Finset.mem_image] at hi
  obtain ⟨p, _hp, rfl⟩ := hi
  exact erdosSelfridgeMaxValuationIndex_mem hH

theorem card_erdosSelfridgeDeletionSet_le (N H : ℕ) :
    (erdosSelfridgeDeletionSet N H).card ≤ (Nat.primesBelow H).card := by
  exact Finset.card_image_le

theorem erdosSelfridgeMaxValuationIndex_mem_deletionSet
    {N H p : ℕ} (hp : p.Prime) (hpH : p < H) :
    erdosSelfridgeMaxValuationIndex N H p ∈ erdosSelfridgeDeletionSet N H := by
  rw [erdosSelfridgeDeletionSet, Finset.mem_image]
  exact ⟨p, by simp [Nat.mem_primesBelow, hp, hpH], rfl⟩

/-- Away from the position selected for `p`, the valuation of a canonical
coefficient is bounded by the valuation of its distance from the position
chosen for `p`. -/
theorem factorization_powerFreePart_le_factorization_dist_maxIndex_of_ne
    {N H l p i : ℕ} (hH : 0 < H) (hp : p.Prime)
    (hi : i ∈ Finset.range H)
    (him : i ≠ erdosSelfridgeMaxValuationIndex N H p) :
    (powerFreePart l (N + (i + 1))).factorization p ≤
      (Nat.dist i (erdosSelfridgeMaxValuationIndex N H p)).factorization p := by
  let m := erdosSelfridgeMaxValuationIndex N H p
  have hm : m ∈ Finset.range H := erdosSelfridgeMaxValuationIndex_mem hH
  have hiVal : 0 < N + (i + 1) := by omega
  have hmVal : 0 < N + (m + 1) := by omega
  let e := (powerFreePart l (N + (i + 1))).factorization p
  have heSource : e ≤ (N + (i + 1)).factorization p := by
    dsimp [e]
    rw [factorization_powerFreePart, powerFreeFactorization,
      Finsupp.mapRange_apply]
    exact Nat.mod_le _ _
  have heMax : e ≤ (N + (m + 1)).factorization p :=
    heSource.trans
      (factorization_le_at_erdosSelfridgeMaxValuationIndex hH hi)
  have hpowI : p ^ e ∣ N + (i + 1) :=
    (hp.pow_dvd_iff_le_factorization hiVal.ne').mpr heSource
  have hpowM : p ^ e ∣ N + (m + 1) :=
    (hp.pow_dvd_iff_le_factorization hmVal.ne').mpr heMax
  have hpowDistValues : p ^ e ∣ Nat.dist (N + (i + 1)) (N + (m + 1)) := by
    rcases le_total (N + (i + 1)) (N + (m + 1)) with hle | hle
    · rw [Nat.dist_eq_sub_of_le hle]
      exact Nat.dvd_sub hpowM hpowI
    · rw [Nat.dist_eq_sub_of_le_right hle]
      exact Nat.dvd_sub hpowI hpowM
  have hdist : Nat.dist (N + (i + 1)) (N + (m + 1)) = Nat.dist i m := by
    rw [Nat.dist_add_add_left, Nat.dist_add_add_right]
  have hdistPos : 0 < Nat.dist i m := Nat.dist_pos_of_ne him
  apply (hp.pow_dvd_iff_le_factorization hdistPos.ne').mp
  rwa [hdist] at hpowDistValues

/-- A retained position is in particular different from the maximal position
chosen for `p`. -/
theorem factorization_powerFreePart_le_factorization_dist_maxIndex
    {N H l p i : ℕ} (hH : 0 < H) (hp : p.Prime) (hpH : p < H)
    (hi : i ∈ Finset.range H)
    (hiKeep : i ∉ erdosSelfridgeDeletionSet N H) :
    (powerFreePart l (N + (i + 1))).factorization p ≤
      (Nat.dist i (erdosSelfridgeMaxValuationIndex N H p)).factorization p := by
  apply factorization_powerFreePart_le_factorization_dist_maxIndex_of_ne
    hH hp hi
  intro him
  subst i
  exact hiKeep (erdosSelfridgeMaxValuationIndex_mem_deletionSet hp hpH)

theorem factorization_powerFreePart_eq_zero_of_failure_of_length_le
    {N H l p i : ℕ} (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H l)
    (hp : p.Prime) (hHp : H ≤ p) (hi : i ∈ Finset.range H) :
    (powerFreePart l (N + (i + 1))).factorization p = 0 := by
  have hiInterval : N + (i + 1) ∈ consecutiveInterval N H := by
    rw [consecutiveInterval, Finset.mem_Ioc]
    have hiH := Finset.mem_range.mp hi
    omega
  have hsupport : ∀ q : ℕ, q.Prime → q ∣ powerFreePart l (N + (i + 1)) → q < H := by
    intro q hq hqdvd
    apply prime_dvd_powerFreePart_lt_of_large_factorization_dvd ?_ hq hqdvd
    intro r hHr hr
    by_cases hri : r ∣ N + (i + 1)
    · rw [← factorization_consecutiveProduct_eq_intervalElement_of_length_le
        hiInterval hr hHr hri]
      exact hfail r hHr hr
    · rw [Nat.factorization_eq_zero_of_not_dvd hri]
      exact dvd_zero l
  by_contra hne
  have hpos : 1 ≤ (powerFreePart l (N + (i + 1))).factorization p :=
    Nat.one_le_iff_ne_zero.mpr hne
  have hpdvd : p ∣ powerFreePart l (N + (i + 1)) :=
    (hp.dvd_iff_one_le_factorization (powerFreePart_ne_zero _ _)).mpr hpos
  exact (not_lt_of_ge hHp) (hsupport p hp hpdvd)

/-- Source equation (9), before optional padding of the deletion set: deleting
the maximal-valuation position chosen for each prime below `H` leaves a
coefficient product dividing `(H - 1)!`. -/
theorem product_powerFreePart_sdiff_deletionSet_dvd_factorial
    {N H l : ℕ} (hH : 1 ≤ H)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H l) :
    (∏ i ∈ Finset.range H \ erdosSelfridgeDeletionSet N H,
      powerFreePart l (N + (i + 1))) ∣ (H - 1).factorial := by
  let kept := Finset.range H \ erdosSelfridgeDeletionSet N H
  have hprod0 : (∏ i ∈ kept, powerFreePart l (N + (i + 1))) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _hi => powerFreePart_ne_zero _ _
  rw [← Nat.factorization_le_iff_dvd hprod0 (Nat.factorial_ne_zero _)]
  intro p
  by_cases hp : p.Prime
  · by_cases hpH : p < H
    · let m := erdosSelfridgeMaxValuationIndex N H p
      have hm : m ∈ Finset.range H :=
        erdosSelfridgeMaxValuationIndex_mem (by omega)
      have hmDeleted : m ∈ erdosSelfridgeDeletionSet N H :=
        erdosSelfridgeMaxValuationIndex_mem_deletionSet hp hpH
      have hkeptSubset : kept ⊆ (Finset.range H).erase m := by
        intro i hi
        rw [Finset.mem_sdiff] at hi
        rw [Finset.mem_erase]
        exact ⟨fun him => hi.2 (him ▸ hmDeleted), hi.1⟩
      have hterm : ∀ i ∈ kept,
          (powerFreePart l (N + (i + 1))).factorization p ≤
            (Nat.dist i m).factorization p := by
        intro i hi
        rw [Finset.mem_sdiff] at hi
        exact factorization_powerFreePart_le_factorization_dist_maxIndex
          (by omega) hp hpH hi.1 hi.2
      have hdist0 : ∀ i ∈ (Finset.range H).erase m, Nat.dist i m ≠ 0 := by
        intro i hi
        rw [Finset.mem_erase] at hi
        exact (Nat.dist_pos_of_ne hi.1).ne'
      have hmLt : m < H := Finset.mem_range.mp hm
      have hmLe : m ≤ H - 1 := by omega
      have hfactorialDvd :
          m.factorial * (H - 1 - m).factorial ∣ (H - 1).factorial := by
        exact Nat.factorial_mul_factorial_dvd_factorial hmLe
      have hfactorialFac :
          (m.factorial * (H - 1 - m).factorial).factorization p ≤
            ((H - 1).factorial).factorization p :=
        (Nat.factorization_le_iff_dvd
          (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
          (Nat.factorial_ne_zero _)).mpr hfactorialDvd p
      calc
        (∏ i ∈ kept, powerFreePart l (N + (i + 1))).factorization p =
            ∑ i ∈ kept, (powerFreePart l (N + (i + 1))).factorization p := by
              rw [Nat.factorization_prod_apply]
              exact fun i _hi => powerFreePart_ne_zero _ _
        _ ≤ ∑ i ∈ kept, (Nat.dist i m).factorization p := by
              exact Finset.sum_le_sum hterm
        _ ≤ ∑ i ∈ (Finset.range H).erase m,
            (Nat.dist i m).factorization p := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hkeptSubset
                (fun _i _hi _hnot => Nat.zero_le _)
        _ = (∏ i ∈ (Finset.range H).erase m, Nat.dist i m).factorization p := by
              rw [Nat.factorization_prod_apply hdist0]
        _ = (m.factorial * (H - 1 - m).factorial).factorization p := by
              rw [prod_range_erase_dist_eq_factorials (Finset.mem_range.mp hm)]
        _ ≤ ((H - 1).factorial).factorization p := hfactorialFac
    · have hHp : H ≤ p := by omega
      rw [Nat.factorization_prod_apply]
      · have hzero :
            ∑ i ∈ kept, (powerFreePart l (N + (i + 1))).factorization p = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          exact factorization_powerFreePart_eq_zero_of_failure_of_length_le
            hfail hp hHp (Finset.mem_sdiff.mp hi).1
        rw [hzero]
        exact Nat.zero_le _
      · exact fun i _hi => powerFreePart_ne_zero _ _
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Full source Lemma 2 in canonical coefficient form.  The deletion set is
padded, when several primes choose the same maximal position, to have exactly
`π(H-1)` elements.  The surviving set therefore has the source cardinality
`H-π(H-1)`, and its coefficient product satisfies equation (9). -/
theorem exists_erdosSelfridgeDeletionSet_card_eq_primeCounting_and_dvd
    {N H l : ℕ} (hH : 1 ≤ H)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H l) :
    ∃ D : Finset ℕ,
      D ⊆ Finset.range H ∧
      D.card = (H - 1).primeCounting ∧
      (Finset.range H \ D).card = H - (H - 1).primeCounting ∧
      (∏ i ∈ Finset.range H \ D, powerFreePart l (N + (i + 1))) ∣
        (H - 1).factorial := by
  let D₀ := erdosSelfridgeDeletionSet N H
  have hD₀subset : D₀ ⊆ Finset.range H :=
    erdosSelfridgeDeletionSet_subset_range (by omega)
  have hHsplit : H - 1 + 1 = H := by omega
  have hprimeCard : (Nat.primesBelow H).card = (H - 1).primeCounting := by
    calc
      (Nat.primesBelow H).card =
          (Nat.primesBelow (H - 1 + 1)).card := by rw [hHsplit]
      _ = (H - 1).primeCounting :=
        card_primesBelow_succ_eq_primeCounting (H - 1)
  have hD₀card : D₀.card ≤ (H - 1).primeCounting := by
    rw [← hprimeCard]
    exact card_erdosSelfridgeDeletionSet_le N H
  have htargetCard : (H - 1).primeCounting ≤ (Finset.range H).card := by
    rw [← hprimeCard]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  obtain ⟨D, hD₀D, hDrange, hDcard⟩ :=
    Finset.exists_subsuperset_card_eq hD₀subset hD₀card htargetCard
  refine ⟨D, hDrange, hDcard, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hDrange, Finset.card_range, hDcard]
  · have hkeptSubset : Finset.range H \ D ⊆ Finset.range H \ D₀ := by
      intro i hi
      rw [Finset.mem_sdiff] at hi ⊢
      exact ⟨hi.1, fun hiD₀ => hi.2 (hD₀D hiD₀)⟩
    exact (Finset.prod_dvd_prod_of_subset
      (Finset.range H \ D) (Finset.range H \ D₀)
      (fun i => powerFreePart l (N + (i + 1))) hkeptSubset).trans
        (product_powerFreePart_sdiff_deletionSet_dvd_factorial hH hfail)

/-- The product of the primes strictly below the interval length. -/
def erdosSelfridgePrimeProduct (H : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesBelow H, p

theorem erdosSelfridgePrimeProduct_pos (H : ℕ) :
    0 < erdosSelfridgePrimeProduct H := by
  apply Finset.prod_pos
  intro p hp
  exact (Nat.mem_primesBelow.mp hp).2.pos

/-- Equation (21), the square-case consequence of Lemma 2.  The valuation
discarded for each prime is at most one because the canonical coefficients
are squarefree. -/
theorem product_powerFreePart_two_dvd_factorial_mul_primeProduct
    {N H : ℕ} (hH : 1 ≤ H)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    (∏ i ∈ Finset.range H, powerFreePart 2 (N + (i + 1))) ∣
      (H - 1).factorial * erdosSelfridgePrimeProduct H := by
  have hleft0 : (∏ i ∈ Finset.range H,
      powerFreePart 2 (N + (i + 1))) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _hi => powerFreePart_ne_zero _ _
  have hright0 : (H - 1).factorial * erdosSelfridgePrimeProduct H ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero _)
      (erdosSelfridgePrimeProduct_pos H).ne'
  rw [← Nat.factorization_le_iff_dvd hleft0 hright0]
  intro p
  by_cases hp : p.Prime
  · by_cases hpH : p < H
    · let m := erdosSelfridgeMaxValuationIndex N H p
      have hm : m ∈ Finset.range H :=
        erdosSelfridgeMaxValuationIndex_mem (by omega)
      have hmLt : m < H := Finset.mem_range.mp hm
      have hdist0 : ∀ i ∈ (Finset.range H).erase m, Nat.dist i m ≠ 0 := by
        intro i hi
        rw [Finset.mem_erase] at hi
        exact (Nat.dist_pos_of_ne hi.1).ne'
      have hterm : ∀ i ∈ (Finset.range H).erase m,
          (powerFreePart 2 (N + (i + 1))).factorization p ≤
            (Nat.dist i m).factorization p := by
        intro i hi
        rw [Finset.mem_erase] at hi
        exact factorization_powerFreePart_le_factorization_dist_maxIndex_of_ne
          (by omega) hp hi.2 hi.1
      have hmLe : m ≤ H - 1 := by omega
      have hfactorialDvd :
          m.factorial * (H - 1 - m).factorial ∣ (H - 1).factorial :=
        Nat.factorial_mul_factorial_dvd_factorial hmLe
      have hfactorialFac :
          (m.factorial * (H - 1 - m).factorial).factorization p ≤
            ((H - 1).factorial).factorization p :=
        (Nat.factorization_le_iff_dvd
          (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
          (Nat.factorial_ne_zero _)).mpr hfactorialDvd p
      have heraseBound :
          ∑ i ∈ (Finset.range H).erase m,
              (powerFreePart 2 (N + (i + 1))).factorization p ≤
            ((H - 1).factorial).factorization p := by
        calc
          (∑ i ∈ (Finset.range H).erase m,
              (powerFreePart 2 (N + (i + 1))).factorization p) ≤
              ∑ i ∈ (Finset.range H).erase m,
                (Nat.dist i m).factorization p := Finset.sum_le_sum hterm
          _ = (∏ i ∈ (Finset.range H).erase m,
              Nat.dist i m).factorization p := by
                rw [Nat.factorization_prod_apply hdist0]
          _ = (m.factorial * (H - 1 - m).factorial).factorization p := by
                rw [prod_range_erase_dist_eq_factorials hmLt]
          _ ≤ ((H - 1).factorial).factorization p := hfactorialFac
      have hmCoeff :
          (powerFreePart 2 (N + (m + 1))).factorization p ≤ 1 := by
        have := factorization_powerFreePart_lt
          (l := 2) (n := N + (m + 1)) (p := p) (by omega)
        omega
      have hpMem : p ∈ Nat.primesBelow H := Nat.mem_primesBelow.mpr ⟨hpH, hp⟩
      have hpDvdPrimeProduct : p ∣ erdosSelfridgePrimeProduct H := by
        rw [erdosSelfridgePrimeProduct]
        exact Finset.dvd_prod_of_mem id hpMem
      have hprimeFac : 1 ≤ (erdosSelfridgePrimeProduct H).factorization p :=
        (hp.dvd_iff_one_le_factorization
          (erdosSelfridgePrimeProduct_pos H).ne').mp hpDvdPrimeProduct
      rw [Nat.factorization_prod_apply]
      · rw [Nat.factorization_mul (Nat.factorial_ne_zero _)
          (erdosSelfridgePrimeProduct_pos H).ne']
        calc
          (∑ i ∈ Finset.range H,
              (powerFreePart 2 (N + (i + 1))).factorization p) =
              (∑ i ∈ (Finset.range H).erase m,
                (powerFreePart 2 (N + (i + 1))).factorization p) +
                (powerFreePart 2 (N + (m + 1))).factorization p := by
                  symm
                  exact Finset.sum_erase_add (Finset.range H)
                    (fun i =>
                      (powerFreePart 2 (N + (i + 1))).factorization p) hm
          _ ≤ ((H - 1).factorial).factorization p + 1 :=
            Nat.add_le_add heraseBound hmCoeff
          _ ≤ ((H - 1).factorial).factorization p +
              (erdosSelfridgePrimeProduct H).factorization p :=
            Nat.add_le_add_left hprimeFac _
      · exact fun i _hi => powerFreePart_ne_zero _ _
    · have hHp : H ≤ p := by omega
      rw [Nat.factorization_prod_apply]
      · have hzero :
            ∑ i ∈ Finset.range H,
                (powerFreePart 2 (N + (i + 1))).factorization p = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          exact factorization_powerFreePart_eq_zero_of_failure_of_length_le
            hfail hp hHp hi
        rw [hzero]
        exact Nat.zero_le _
      · exact fun i _hi => powerFreePart_ne_zero _ _
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

end Tao2026
