import Tao2026.BadIntervalPrimeTupleFiber

/-!
# Freezing several coordinates of the prime tuple

The crude proofs of Propositions 6.7 and 6.8 freeze respectively two and
three ordinary sampled primes.  This module provides the common exact finite
probability mechanism for an arbitrary finite set of coordinates.  The
cardinality of the frozen support times the product of the omitted band
cardinalities is exactly the full support cardinality, so a uniform bound on
every frozen fiber divides by precisely that product.
-/

namespace Tao2026

open MeasureTheory
open scoped Classical

noncomputable section

set_option maxRecDepth 10000

/-- Replace every coordinate in `J` by the sentinel value zero. -/
def taoPrimeTupleFreezeCoordinates
    (J : Finset (Fin 1001)) (ω : TaoPrimeTuple) : TaoPrimeTuple :=
  fun k => if k ∈ J then 0 else ω k

/-- Cartesian support retaining precisely the coordinates outside `J`. -/
def taoPrimeTupleMultiFrozenSupport
    (P : Fin 1001 → ℕ) (J : Finset (Fin 1001)) : Finset TaoPrimeTuple :=
  Fintype.piFinset fun k =>
    if k ∈ J then {0} else taoDyadicPrimeBand (P k)

theorem taoPrimeTupleFreezeCoordinates_mem_multiFrozenSupport
    {P : Fin 1001 → ℕ} {J : Finset (Fin 1001)} {ω : TaoPrimeTuple}
    (hω : ω ∈ taoPrimeTupleSupport P) :
    taoPrimeTupleFreezeCoordinates J ω ∈
      taoPrimeTupleMultiFrozenSupport P J := by
  unfold taoPrimeTupleMultiFrozenSupport
  rw [Fintype.mem_piFinset]
  intro k
  by_cases hk : k ∈ J
  · simp [taoPrimeTupleFreezeCoordinates, hk]
  · simp [taoPrimeTupleFreezeCoordinates, hk,
      (mem_taoPrimeTupleSupport.mp hω) k]

theorem taoPrimeTupleMultiFrozenSupport_nonempty
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (J : Finset (Fin 1001)) :
    (taoPrimeTupleMultiFrozenSupport P J).Nonempty := by
  let ω : TaoPrimeTuple := fun k => (hP k).choose
  have hω : ω ∈ taoPrimeTupleSupport P :=
    mem_taoPrimeTupleSupport.mpr fun k => (hP k).choose_spec
  exact ⟨taoPrimeTupleFreezeCoordinates J ω,
    taoPrimeTupleFreezeCoordinates_mem_multiFrozenSupport hω⟩

theorem taoPrimeTuple_apply_eq_of_freezeCoordinates_eq
    {J : Finset (Fin 1001)} {k : Fin 1001} {ω₁ ω₂ : TaoPrimeTuple}
    (hfreeze : taoPrimeTupleFreezeCoordinates J ω₁ =
      taoPrimeTupleFreezeCoordinates J ω₂)
    (hk : k ∉ J) :
    ω₁ k = ω₂ k := by
  have h := congrFun hfreeze k
  simpa [taoPrimeTupleFreezeCoordinates, hk] using h

theorem taoPrimeTuple_eq_of_freezeCoordinates_eq_of_apply_eq
    {J : Finset (Fin 1001)} {ω₁ ω₂ : TaoPrimeTuple}
    (hfreeze : taoPrimeTupleFreezeCoordinates J ω₁ =
      taoPrimeTupleFreezeCoordinates J ω₂)
    (happly : ∀ j ∈ J, ω₁ j = ω₂ j) :
    ω₁ = ω₂ := by
  funext k
  by_cases hk : k ∈ J
  · exact happly k hk
  · exact taoPrimeTuple_apply_eq_of_freezeCoordinates_eq hfreeze hk

theorem taoPrimeTupleMultiFrozenSupport_insert
    (P : Fin 1001 → ℕ) (J : Finset (Fin 1001)) (j : Fin 1001) :
    taoPrimeTupleMultiFrozenSupport P (insert j J) =
      Fintype.piFinset fun k =>
        if k = j then {0} else
          if k ∈ J then {0} else taoDyadicPrimeBand (P k) := by
  ext ω
  simp only [taoPrimeTupleMultiFrozenSupport, Fintype.mem_piFinset,
    Finset.mem_insert]
  constructor
  · intro h k
    by_cases hkj : k = j
    · subst k
      simpa using h j
    · simpa [hkj] using h k
  · intro h k
    by_cases hkj : k = j
    · simpa [hkj] using h k
    · simpa [hkj] using h k

/-- Exact cardinality cancellation for any finite set of frozen coordinates. -/
theorem card_taoPrimeTupleMultiFrozenSupport_mul_bands
    (P : Fin 1001 → ℕ) (J : Finset (Fin 1001)) :
    (taoPrimeTupleMultiFrozenSupport P J).card *
        (∏ j ∈ J, (taoDyadicPrimeBand (P j)).card) =
      (taoPrimeTupleSupport P).card := by
  induction J using Finset.induction_on with
  | empty =>
      simp [taoPrimeTupleMultiFrozenSupport, taoPrimeTupleSupport]
  | @insert j J hj ih =>
      have hsingle := card_piFinset_singleton_coordinate
        (fun k => if k ∈ J then {0} else taoDyadicPrimeBand (P k)) j 0
      have hstep :
          (taoPrimeTupleMultiFrozenSupport P (insert j J)).card *
              (taoDyadicPrimeBand (P j)).card =
            (taoPrimeTupleMultiFrozenSupport P J).card := by
        rw [taoPrimeTupleMultiFrozenSupport_insert]
        simpa [taoPrimeTupleMultiFrozenSupport, hj] using hsingle
      rw [Finset.prod_insert hj]
      calc
        (taoPrimeTupleMultiFrozenSupport P (insert j J)).card *
            ((taoDyadicPrimeBand (P j)).card *
              ∏ k ∈ J, (taoDyadicPrimeBand (P k)).card) =
          ((taoPrimeTupleMultiFrozenSupport P (insert j J)).card *
              (taoDyadicPrimeBand (P j)).card) *
                ∏ k ∈ J, (taoDyadicPrimeBand (P k)).card := by
            rw [Nat.mul_assoc]
        _ = (taoPrimeTupleMultiFrozenSupport P J).card *
              ∏ k ∈ J, (taoDyadicPrimeBand (P k)).card := by
            rw [hstep]
        _ = (taoPrimeTupleSupport P).card := ih

/-- Uniform finite event-fiber bound after freezing any coordinate set. -/
theorem card_taoPrimeTupleEvent_le_multiFrozenSupport_mul
    (P : Fin 1001 → ℕ) (E : Set TaoPrimeTuple)
    (J : Finset (Fin 1001)) (M : ℕ)
    (hM : ∀ ρ ∈ taoPrimeTupleMultiFrozenSupport P J,
      (((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).filter
        fun ω => taoPrimeTupleFreezeCoordinates J ω = ρ).card ≤ M) :
    ((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).card ≤
      (taoPrimeTupleMultiFrozenSupport P J).card * M := by
  let A := (taoPrimeTupleSupport P).filter fun ω => ω ∈ E
  calc
    A.card ≤ (A.image (taoPrimeTupleFreezeCoordinates J)).card * M := by
      apply card_le_card_image_mul_of_fiber_le
      intro ρ hρ
      apply hM
      rcases Finset.mem_image.mp hρ with ⟨ω, hω, rfl⟩
      exact taoPrimeTupleFreezeCoordinates_mem_multiFrozenSupport
        (Finset.mem_filter.mp hω).1
    _ ≤ (taoPrimeTupleMultiFrozenSupport P J).card * M := by
      apply Nat.mul_le_mul_right
      apply Finset.card_le_card
      intro ρ hρ
      rcases Finset.mem_image.mp hρ with ⟨ω, hω, rfl⟩
      exact taoPrimeTupleFreezeCoordinates_mem_multiFrozenSupport
        (Finset.mem_filter.mp hω).1

/-- Exact finite analogue of conditioning on all coordinates outside `J`. -/
theorem taoPrimeTupleMeasure_le_card_multiCoordinateFiber_div_bands
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (E : Set TaoPrimeTuple) (J : Finset (Fin 1001)) (M : ℕ)
    (hM : ∀ ρ ∈ taoPrimeTupleMultiFrozenSupport P J,
      (((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).filter
        fun ω => taoPrimeTupleFreezeCoordinates J ω = ρ).card ≤ M) :
    taoPrimeTupleMeasure P hP E ≤
      (M : ENNReal) /
        (∏ j ∈ J, ((taoDyadicPrimeBand (P j)).card : ENNReal)) := by
  rw [taoPrimeTupleMeasure_apply_eq_card_div_support,
    ← card_taoPrimeTupleMultiFrozenSupport_mul_bands P J]
  push_cast
  calc
    (((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).card : ENNReal) /
        ((taoPrimeTupleMultiFrozenSupport P J).card *
          ∏ j ∈ J, ((taoDyadicPrimeBand (P j)).card : ENNReal)) ≤
      (((taoPrimeTupleMultiFrozenSupport P J).card * M : ℕ) : ENNReal) /
        ((taoPrimeTupleMultiFrozenSupport P J).card *
          ∏ j ∈ J, ((taoDyadicPrimeBand (P j)).card : ENNReal)) := by
      apply ENNReal.div_le_div_right
      exact_mod_cast card_taoPrimeTupleEvent_le_multiFrozenSupport_mul
        P E J M hM
    _ = (M : ENNReal) /
        (∏ j ∈ J, ((taoDyadicPrimeBand (P j)).card : ENNReal)) := by
      rw [Nat.cast_mul]
      apply ENNReal.mul_div_mul_left
      · exact_mod_cast Finset.card_ne_zero.mpr
          (taoPrimeTupleMultiFrozenSupport_nonempty P hP J)
      · simp

/-- Product of the coordinates selected by `J`. -/
def taoPrimeTupleSelectedProduct
    (J : Finset (Fin 1001)) (ω : TaoPrimeTuple) : ℕ :=
  ∏ j ∈ J, ω j

/-- Complementary factor after extracting all ordinary coordinates in `J`. -/
def taoPrimeTupleMultiCofactor
    (m' : ℕ) (J : Finset (Fin 1001)) (ω : TaoPrimeTuple) : ℕ :=
  (ω 0) ^ 2 *
    (∏ k ∈ (Finset.univ.erase (0 : Fin 1001)) \ J, ω k) * m'

theorem taoPrimeTupleStart_eq_multiCofactor_mul_selectedProduct
    (m' : ℕ) (J : Finset (Fin 1001)) (hzero : 0 ∉ J) (ω : TaoPrimeTuple) :
    taoPrimeTupleStart m' ω =
      taoPrimeTupleMultiCofactor m' J ω * taoPrimeTupleSelectedProduct J ω := by
  have hJ : J ⊆ Finset.univ.erase (0 : Fin 1001) := by
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact fun h => hzero (h ▸ hj)
  rw [taoPrimeTupleStart, taoPrimeTupleTailProduct,
    ← Finset.prod_sdiff hJ]
  unfold taoPrimeTupleMultiCofactor taoPrimeTupleSelectedProduct
  ac_rfl

theorem taoPrimeTupleMultiCofactor_eq_of_freezeCoordinates_eq
    (m' : ℕ) {J : Finset (Fin 1001)} (hzero : 0 ∉ J)
    {ω₁ ω₂ : TaoPrimeTuple}
    (hfreeze : taoPrimeTupleFreezeCoordinates J ω₁ =
      taoPrimeTupleFreezeCoordinates J ω₂) :
    taoPrimeTupleMultiCofactor m' J ω₁ =
      taoPrimeTupleMultiCofactor m' J ω₂ := by
  unfold taoPrimeTupleMultiCofactor
  congr 2
  · exact congrArg (fun n : ℕ => n ^ 2)
      (taoPrimeTuple_apply_eq_of_freezeCoordinates_eq hfreeze hzero)
  · apply Finset.prod_congr rfl
    intro k hk
    exact taoPrimeTuple_apply_eq_of_freezeCoordinates_eq hfreeze
      (Finset.mem_sdiff.mp hk).2

theorem taoPrimeTupleSelectedProduct_modEq_of_start_modEq
    (m' : ℕ) {J : Finset (Fin 1001)} (hzero : 0 ∉ J)
    {q : ℕ} {ω₁ ω₂ : TaoPrimeTuple}
    (hfreeze : taoPrimeTupleFreezeCoordinates J ω₁ =
      taoPrimeTupleFreezeCoordinates J ω₂)
    (hcop : Nat.Coprime (taoPrimeTupleMultiCofactor m' J ω₁) q)
    (hstart : taoPrimeTupleStart m' ω₁ ≡ taoPrimeTupleStart m' ω₂ [MOD q]) :
    taoPrimeTupleSelectedProduct J ω₁ ≡
      taoPrimeTupleSelectedProduct J ω₂ [MOD q] := by
  have hcofactor := taoPrimeTupleMultiCofactor_eq_of_freezeCoordinates_eq
    m' hzero hfreeze
  rw [taoPrimeTupleStart_eq_multiCofactor_mul_selectedProduct m' J hzero,
    taoPrimeTupleStart_eq_multiCofactor_mul_selectedProduct m' J hzero,
    ← hcofactor] at hstart
  exact Nat.ModEq.cancel_left_of_coprime hcop.symm hstart

/-- Naturals below `U` in one residue class modulo `q`. -/
def taoNatResidueFiber (q a U : ℕ) : Finset ℕ :=
  (Finset.range U).filter fun n => n ≡ a [MOD q]

theorem card_taoNatResidueFiber_le
    {q a U : ℕ} (hq : 0 < q) :
    (taoNatResidueFiber q a U).card ≤ U / q + 1 := by
  rw [taoNatResidueFiber, ← Nat.count_eq_card_filter_range]
  rw [Nat.count_modEq_card U hq a]
  split_ifs <;> omega

/-- General multi-coordinate progression estimate.  Within each frozen fiber,
the selected product may represent a given natural number at most `R` times;
if all selected products lie below `U` in one residue class modulo `q`, the
event fiber has size at most `(U/q+1)R`. -/
theorem taoPrimeTupleMeasure_le_multiFrozen_productResidue
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (E : Set TaoPrimeTuple) (J : Finset (Fin 1001))
    (q U R : ℕ) (hq : 0 < q)
    (hupper : ∀ ω ∈ (taoPrimeTupleSupport P).filter (fun ω => ω ∈ E),
      taoPrimeTupleSelectedProduct J ω < U)
    (hMultiplicity : ∀ ρ ∈ taoPrimeTupleMultiFrozenSupport P J, ∀ n,
      ((((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).filter
        fun ω => taoPrimeTupleFreezeCoordinates J ω = ρ).filter
          fun ω => taoPrimeTupleSelectedProduct J ω = n).card ≤ R)
    (hModEq : ∀ ω₁ ∈ (taoPrimeTupleSupport P).filter (fun ω => ω ∈ E),
      ∀ ω₂ ∈ (taoPrimeTupleSupport P).filter (fun ω => ω ∈ E),
        taoPrimeTupleFreezeCoordinates J ω₁ =
          taoPrimeTupleFreezeCoordinates J ω₂ →
        taoPrimeTupleSelectedProduct J ω₁ ≡
          taoPrimeTupleSelectedProduct J ω₂ [MOD q]) :
    taoPrimeTupleMeasure P hP E ≤
      ((((U / q + 1) * R : ℕ) : ENNReal) /
        (∏ j ∈ J, ((taoDyadicPrimeBand (P j)).card : ENNReal))) := by
  apply taoPrimeTupleMeasure_le_card_multiCoordinateFiber_div_bands
  intro ρ hρ
  let A := ((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).filter
    fun ω => taoPrimeTupleFreezeCoordinates J ω = ρ
  by_cases hA : A.Nonempty
  · let ω₀ := hA.choose
    have hω₀ : ω₀ ∈ A := hA.choose_spec
    calc
      A.card ≤ (A.image (taoPrimeTupleSelectedProduct J)).card * R := by
        apply card_le_card_image_mul_of_fiber_le
        intro n hn
        apply hMultiplicity ρ hρ n
      _ ≤ (U / q + 1) * R := by
        apply Nat.mul_le_mul_right
        calc
          (A.image (taoPrimeTupleSelectedProduct J)).card ≤
              (taoNatResidueFiber q
                (taoPrimeTupleSelectedProduct J ω₀) U).card := by
            apply Finset.card_le_card
            intro n hn
            rcases Finset.mem_image.mp hn with ⟨ω, hω, rfl⟩
            have hωData := Finset.mem_filter.mp hω
            have hω₀Data := Finset.mem_filter.mp hω₀
            rw [taoNatResidueFiber, Finset.mem_filter]
            exact ⟨Finset.mem_range.mpr (hupper ω hωData.1),
              hModEq ω hωData.1 ω₀ hω₀Data.1
                (hωData.2.trans hω₀Data.2.symm)⟩
          _ ≤ U / q + 1 := card_taoNatResidueFiber_le hq
  · change A.card ≤ (U / q + 1) * R
    rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

theorem prime_pair_mul_eq_pair_or_swap
    {a b c d : ℕ} (ha : Nat.Prime a)
    (hc : Nat.Prime c) (hd : Nat.Prime d) (h : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hadiv : a ∣ c * d := by
    rw [← h]
    exact ⟨b, rfl⟩
  rcases ha.dvd_mul.mp hadiv with hac | had
  · left
    have hacEq : a = c := (Nat.prime_dvd_prime_iff_eq ha hc).mp hac
    subst c
    exact ⟨rfl, Nat.mul_left_cancel ha.pos h⟩
  · right
    have hadEq : a = d := (Nat.prime_dvd_prime_iff_eq ha hd).mp had
    subst d
    refine ⟨rfl, ?_⟩
    rw [Nat.mul_comm c a] at h
    exact Nat.mul_left_cancel ha.pos h

/-- Two prime coordinates represent a fixed product at most twice, even after
an arbitrary extra event filter is imposed. -/
theorem card_taoPrimeTuple_pairProduct_fiber_le_two
    (P : Fin 1001 → ℕ) (E : Set TaoPrimeTuple)
    (j₁ j₂ : Fin 1001) (hj : j₁ ≠ j₂) (ρ : TaoPrimeTuple) (n : ℕ) :
    (((((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).filter
      fun ω => taoPrimeTupleFreezeCoordinates {j₁, j₂} ω = ρ).filter
        fun ω => taoPrimeTupleSelectedProduct {j₁, j₂} ω = n).card) ≤ 2 := by
  let A := ((((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).filter
    fun ω => taoPrimeTupleFreezeCoordinates {j₁, j₂} ω = ρ).filter
      fun ω => taoPrimeTupleSelectedProduct {j₁, j₂} ω = n)
  by_cases hA : A.Nonempty
  · let ω₀ := hA.choose
    have hω₀ : ω₀ ∈ A := hA.choose_spec
    let values : TaoPrimeTuple → ℕ × ℕ := fun ω => (ω j₁, ω j₂)
    calc
      A.card = (A.image values).card := by
        rw [Finset.card_image_iff.mpr]
        intro ω₁ hω₁ ω₂ hω₂ hvalues
        apply taoPrimeTuple_eq_of_freezeCoordinates_eq_of_apply_eq
        · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hω₁).1).2.trans
            (Finset.mem_filter.mp (Finset.mem_filter.mp hω₂).1).2.symm
        · intro k hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact congrArg Prod.fst hvalues
          · exact congrArg Prod.snd hvalues
      _ ≤ ({values ω₀, (ω₀ j₂, ω₀ j₁)} : Finset (ℕ × ℕ)).card := by
        apply Finset.card_le_card
        intro v hv
        rcases Finset.mem_image.mp hv with ⟨ω, hω, rfl⟩
        have hωSupport := (Finset.mem_filter.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hω).1).1).1
        have hω₀Support := (Finset.mem_filter.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hω₀).1).1).1
        have hprodω := (Finset.mem_filter.mp hω).2
        have hprodω₀ := (Finset.mem_filter.mp hω₀).2
        have hprod : ω j₁ * ω j₂ = ω₀ j₁ * ω₀ j₂ := by
          simpa [taoPrimeTupleSelectedProduct, hj] using hprodω.trans hprodω₀.symm
        have hprimeω := mem_taoPrimeTupleSupport.mp hωSupport
        have hprimeω₀ := mem_taoPrimeTupleSupport.mp hω₀Support
        rcases prime_pair_mul_eq_pair_or_swap
            (mem_taoDyadicPrimeBand.mp (hprimeω j₁)).1
            (mem_taoDyadicPrimeBand.mp (hprimeω₀ j₁)).1
            (mem_taoDyadicPrimeBand.mp (hprimeω₀ j₂)).1 hprod with h | h
        · simp [values, h.1, h.2]
        · simp [values, h.1, h.2]
      _ ≤ 2 := Finset.card_le_two
  · change A.card ≤ 2
    rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

/-- Source two-coordinate crude bound for a single prime divisibility event,
before the noncoprime part is charged to coordinate collisions. -/
theorem taoPrimeTupleMeasure_largePrimeDivisibilityEvent_le_crude_pair
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) (j₁ j₂ : Fin 1001)
    (hj₁ : j₁ ≠ 0) (hj₂ : j₂ ≠ 0) (hj : j₁ ≠ j₂)
    (hq : 0 < a.2)
    (hcop : ∀ ω ∈ (taoPrimeTupleSupport P).filter
      (fun ω => TaoLargePrimeDivisibilityEvent m' a ω),
      Nat.Coprime
        (taoPrimeTupleMultiCofactor m' {j₁, j₂} ω) a.2) :
    taoPrimeTupleMeasure P hP
        { ω | TaoLargePrimeDivisibilityEvent m' a ω } ≤
      (((((2 * P j₁) * (2 * P j₂)) / a.2 + 1) * 2 : ℕ) : ENNReal) /
        (((taoDyadicPrimeBand (P j₁)).card : ENNReal) *
          (taoDyadicPrimeBand (P j₂)).card) := by
  have hzero : (0 : Fin 1001) ∉ ({j₁, j₂} : Finset (Fin 1001)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hj₁, Ne.symm hj₂⟩
  have hbound := taoPrimeTupleMeasure_le_multiFrozen_productResidue
    P hP { ω | TaoLargePrimeDivisibilityEvent m' a ω } {j₁, j₂}
      a.2 ((2 * P j₁) * (2 * P j₂)) 2 hq
      (by
        intro ω hω
        have hωSupport := (Finset.mem_filter.mp hω).1
        have hmem := mem_taoPrimeTupleSupport.mp hωSupport
        have hj₁Upper := (mem_taoDyadicPrimeBand.mp (hmem j₁)).2.2
        have hj₂Upper := (mem_taoDyadicPrimeBand.mp (hmem j₂)).2.2
        have hj₂Pos := (mem_taoDyadicPrimeBand.mp (hmem j₂)).1.pos
        rw [show taoPrimeTupleSelectedProduct {j₁, j₂} ω =
            ω j₁ * ω j₂ by
          simp [taoPrimeTupleSelectedProduct, hj]]
        exact mul_lt_mul hj₁Upper (Nat.le_of_lt hj₂Upper)
          hj₂Pos (Nat.zero_le _))
      (by
        intro ρ hρ n
        exact card_taoPrimeTuple_pairProduct_fiber_le_two
          P { ω | TaoLargePrimeDivisibilityEvent m' a ω } j₁ j₂ hj ρ n)
      (by
        intro ω₁ hω₁ ω₂ hω₂ hfreeze
        apply taoPrimeTupleSelectedProduct_modEq_of_start_modEq m' hzero hfreeze
        · exact hcop ω₁ hω₁
        · exact taoLargePrimeDivisibilityEvent_modEq
            (Finset.mem_filter.mp hω₁).2
            (Finset.mem_filter.mp hω₂).2)
  simpa [hj, Ne.symm hj] using hbound

/-- Finite source form of Proposition 6.7(i).  Since the prime modulus does
not divide the shift, the divisibility event itself makes the full source
product coprime to the modulus, so the pair-cofactor hypothesis is automatic. -/
theorem taoLargePrimeProbability_le_crude_pair_of_not_dvd_shift
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) (j₁ j₂ : Fin 1001)
    (hj₁ : j₁ ≠ 0) (hj₂ : j₂ ≠ 0) (hj : j₁ ≠ j₂)
    (hp : Nat.Prime a.2) (hpl : ¬a.2 ∣ a.1) :
    taoLargePrimeProbability P hP m' a ≤
      (((((2 * P j₁) * (2 * P j₂)) / a.2 + 1) * 2 : ℕ) : ℝ) /
        (((taoDyadicPrimeBand (P j₁)).card : ℝ) *
          (taoDyadicPrimeBand (P j₂)).card) := by
  have hzero : (0 : Fin 1001) ∉ ({j₁, j₂} : Finset (Fin 1001)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hj₁, Ne.symm hj₂⟩
  have hENN := taoPrimeTupleMeasure_largePrimeDivisibilityEvent_le_crude_pair
    P hP m' a j₁ j₂ hj₁ hj₂ hj hp.pos (by
      intro ω hω
      have hEvent := (Finset.mem_filter.mp hω).2
      have hcopStart := taoLargePrimeDivisibilityEvent_coprime hp hpl hEvent
      rw [taoPrimeTupleStart_eq_multiCofactor_mul_selectedProduct
        m' {j₁, j₂} hzero] at hcopStart
      exact (Nat.coprime_mul_iff_left.mp hcopStart).1)
  rw [taoLargePrimeProbability, measureReal_def]
  have hdenom :
      (((taoDyadicPrimeBand (P j₁)).card : ENNReal) *
        (taoDyadicPrimeBand (P j₂)).card) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast Finset.card_ne_zero.mpr (hP j₁)
    · exact_mod_cast Finset.card_ne_zero.mpr (hP j₂)
  have hreal := ENNReal.toReal_mono
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hdenom) hENN
  simpa using hreal

theorem prime_triple_mul_eq_one_of_six_permutations
    {a b c d e f : ℕ}
    (ha : Nat.Prime a) (hb : Nat.Prime b)
    (hd : Nat.Prime d) (he : Nat.Prime e) (hf : Nat.Prime f)
    (h : a * b * c = d * e * f) :
    (a = d ∧ b = e ∧ c = f) ∨
    (a = d ∧ b = f ∧ c = e) ∨
    (a = e ∧ b = d ∧ c = f) ∨
    (a = e ∧ b = f ∧ c = d) ∨
    (a = f ∧ b = d ∧ c = e) ∨
    (a = f ∧ b = e ∧ c = d) := by
  have hnorm : a * (b * c) = d * (e * f) := by
    simpa [Nat.mul_assoc] using h
  have hadiv : a ∣ d * (e * f) := by
    rw [← hnorm]
    exact ⟨b * c, rfl⟩
  rcases ha.dvd_mul.mp hadiv with had | haef
  · have hadEq : a = d := (Nat.prime_dvd_prime_iff_eq ha hd).mp had
    subst d
    have hpairs : b * c = e * f := Nat.mul_left_cancel ha.pos hnorm
    rcases prime_pair_mul_eq_pair_or_swap hb he hf hpairs with hp | hp
    · exact Or.inl ⟨rfl, hp.1, hp.2⟩
    · exact Or.inr (Or.inl ⟨rfl, hp.1, hp.2⟩)
  · rcases ha.dvd_mul.mp haef with hae | haf
    · have haeEq : a = e := (Nat.prime_dvd_prime_iff_eq ha he).mp hae
      subst e
      have hcancel : a * (b * c) = a * (d * f) := by
        calc
          a * (b * c) = d * (a * f) := hnorm
          _ = a * (d * f) := by ac_rfl
      have hpairs : b * c = d * f := Nat.mul_left_cancel ha.pos hcancel
      rcases prime_pair_mul_eq_pair_or_swap hb hd hf hpairs with hp | hp
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hp.1, hp.2⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hp.1, hp.2⟩)))
    · have hafEq : a = f := (Nat.prime_dvd_prime_iff_eq ha hf).mp haf
      subst f
      have hcancel : a * (b * c) = a * (d * e) := by
        calc
          a * (b * c) = d * (e * a) := hnorm
          _ = a * (d * e) := by ac_rfl
      have hpairs : b * c = d * e := Nat.mul_left_cancel ha.pos hcancel
      rcases prime_pair_mul_eq_pair_or_swap hb hd he hpairs with hp | hp
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, hp.1, hp.2⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨rfl, hp.1, hp.2⟩))))

/-- Three prime coordinates represent a fixed product at most six times. -/
theorem card_taoPrimeTuple_tripleProduct_fiber_le_six
    (P : Fin 1001 → ℕ) (E : Set TaoPrimeTuple)
    (j₁ j₂ j₃ : Fin 1001)
    (h₁₂ : j₁ ≠ j₂) (h₁₃ : j₁ ≠ j₃) (h₂₃ : j₂ ≠ j₃)
    (ρ : TaoPrimeTuple) (n : ℕ) :
    (((((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).filter
      fun ω => taoPrimeTupleFreezeCoordinates {j₁, j₂, j₃} ω = ρ).filter
        fun ω => taoPrimeTupleSelectedProduct {j₁, j₂, j₃} ω = n).card) ≤ 6 := by
  let A := ((((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).filter
    fun ω => taoPrimeTupleFreezeCoordinates {j₁, j₂, j₃} ω = ρ).filter
      fun ω => taoPrimeTupleSelectedProduct {j₁, j₂, j₃} ω = n)
  by_cases hA : A.Nonempty
  · let ω₀ := hA.choose
    have hω₀ : ω₀ ∈ A := hA.choose_spec
    let values : TaoPrimeTuple → ℕ × ℕ × ℕ :=
      fun ω => (ω j₁, ω j₂, ω j₃)
    let permutations : Finset (ℕ × ℕ × ℕ) :=
      {(ω₀ j₁, ω₀ j₂, ω₀ j₃),
       (ω₀ j₁, ω₀ j₃, ω₀ j₂),
       (ω₀ j₂, ω₀ j₁, ω₀ j₃),
       (ω₀ j₂, ω₀ j₃, ω₀ j₁),
       (ω₀ j₃, ω₀ j₁, ω₀ j₂),
       (ω₀ j₃, ω₀ j₂, ω₀ j₁)}
    calc
      A.card = (A.image values).card := by
        rw [Finset.card_image_iff.mpr]
        intro ω₁ hω₁ ω₂ hω₂ hvalues
        apply taoPrimeTuple_eq_of_freezeCoordinates_eq_of_apply_eq
        · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hω₁).1).2.trans
            (Finset.mem_filter.mp (Finset.mem_filter.mp hω₂).1).2.symm
        · intro k hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl | rfl
          · exact congrArg (fun v => v.1) hvalues
          · exact congrArg (fun v => v.2.1) hvalues
          · exact congrArg (fun v => v.2.2) hvalues
      _ ≤ permutations.card := by
        apply Finset.card_le_card
        intro v hv
        rcases Finset.mem_image.mp hv with ⟨ω, hω, rfl⟩
        have hωSupport := (Finset.mem_filter.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hω).1).1).1
        have hω₀Support := (Finset.mem_filter.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hω₀).1).1).1
        have hprodω := (Finset.mem_filter.mp hω).2
        have hprodω₀ := (Finset.mem_filter.mp hω₀).2
        have hprod : ω j₁ * ω j₂ * ω j₃ =
            ω₀ j₁ * ω₀ j₂ * ω₀ j₃ := by
          simpa [taoPrimeTupleSelectedProduct, h₁₂, h₁₃, h₂₃,
            Nat.mul_assoc] using
            hprodω.trans hprodω₀.symm
        have hprimeω := mem_taoPrimeTupleSupport.mp hωSupport
        have hprimeω₀ := mem_taoPrimeTupleSupport.mp hω₀Support
        have hperm := prime_triple_mul_eq_one_of_six_permutations
          (mem_taoDyadicPrimeBand.mp (hprimeω j₁)).1
          (mem_taoDyadicPrimeBand.mp (hprimeω j₂)).1
          (mem_taoDyadicPrimeBand.mp (hprimeω₀ j₁)).1
          (mem_taoDyadicPrimeBand.mp (hprimeω₀ j₂)).1
          (mem_taoDyadicPrimeBand.mp (hprimeω₀ j₃)).1 hprod
        rcases hperm with h | h | h | h | h | h <;>
          simp [values, permutations, h.1, h.2.1, h.2.2]
      _ ≤ 6 := Finset.card_le_six
  · change A.card ≤ 6
    rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

/-- Source three-coordinate crude bound for a joint divisibility event, before
the noncoprime part is charged to coordinate collisions. -/
theorem taoPrimeTupleMeasure_largePrimeJointEvent_le_crude_triple
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) (j₁ j₂ j₃ : Fin 1001)
    (hj₁ : j₁ ≠ 0) (hj₂ : j₂ ≠ 0) (hj₃ : j₃ ≠ 0)
    (h₁₂ : j₁ ≠ j₂) (h₁₃ : j₁ ≠ j₃) (h₂₃ : j₂ ≠ j₃)
    (hpq : Nat.Coprime a.2 b.2) (hq : 0 < a.2 * b.2)
    (hcop : ∀ ω ∈ (taoPrimeTupleSupport P).filter
      (fun ω => TaoLargePrimeJointDivisibilityEvent m' a b ω),
      Nat.Coprime
        (taoPrimeTupleMultiCofactor m' {j₁, j₂, j₃} ω) (a.2 * b.2)) :
    taoPrimeTupleMeasure P hP
        {ω | TaoLargePrimeJointDivisibilityEvent m' a b ω} ≤
      (((((((2 * P j₁) * (2 * P j₂)) * (2 * P j₃)) /
          (a.2 * b.2) + 1) * 6 : ℕ) : ENNReal) /
        (((taoDyadicPrimeBand (P j₁)).card : ENNReal) *
          (taoDyadicPrimeBand (P j₂)).card *
          (taoDyadicPrimeBand (P j₃)).card)) := by
  have hzero : (0 : Fin 1001) ∉ ({j₁, j₂, j₃} : Finset (Fin 1001)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hj₁, Ne.symm hj₂, Ne.symm hj₃⟩
  have hbound := taoPrimeTupleMeasure_le_multiFrozen_productResidue
    P hP {ω | TaoLargePrimeJointDivisibilityEvent m' a b ω}
      {j₁, j₂, j₃} (a.2 * b.2)
      (((2 * P j₁) * (2 * P j₂)) * (2 * P j₃)) 6 hq
      (by
        intro ω hω
        have hωSupport := (Finset.mem_filter.mp hω).1
        have hmem := mem_taoPrimeTupleSupport.mp hωSupport
        have hj₁Upper := (mem_taoDyadicPrimeBand.mp (hmem j₁)).2.2
        have hj₂Upper := (mem_taoDyadicPrimeBand.mp (hmem j₂)).2.2
        have hj₃Upper := (mem_taoDyadicPrimeBand.mp (hmem j₃)).2.2
        have hj₂Pos := (mem_taoDyadicPrimeBand.mp (hmem j₂)).1.pos
        have hj₃Pos := (mem_taoDyadicPrimeBand.mp (hmem j₃)).1.pos
        have hpair : ω j₁ * ω j₂ < (2 * P j₁) * (2 * P j₂) :=
          mul_lt_mul hj₁Upper (Nat.le_of_lt hj₂Upper)
            hj₂Pos (Nat.zero_le _)
        have htriple : (ω j₁ * ω j₂) * ω j₃ <
            ((2 * P j₁) * (2 * P j₂)) * (2 * P j₃) :=
          mul_lt_mul hpair (Nat.le_of_lt hj₃Upper)
            hj₃Pos (Nat.zero_le _)
        simpa [taoPrimeTupleSelectedProduct, h₁₂, h₁₃, h₂₃,
          Nat.mul_assoc] using htriple)
      (by
        intro ρ hρ n
        exact card_taoPrimeTuple_tripleProduct_fiber_le_six
          P {ω | TaoLargePrimeJointDivisibilityEvent m' a b ω}
            j₁ j₂ j₃ h₁₂ h₁₃ h₂₃ ρ n)
      (by
        intro ω₁ hω₁ ω₂ hω₂ hfreeze
        apply taoPrimeTupleSelectedProduct_modEq_of_start_modEq
          m' hzero hfreeze
        · exact hcop ω₁ hω₁
        · exact taoLargePrimeJointDivisibilityEvent_modEq_mul hpq
            (Finset.mem_filter.mp hω₁).2
            (Finset.mem_filter.mp hω₂).2)
  simpa [h₁₂, h₁₃, h₂₃, Ne.symm h₁₂, Ne.symm h₁₃,
    Ne.symm h₂₃, Nat.mul_assoc, mul_assoc] using hbound

/-- Finite source form of Proposition 6.8(i).  For distinct prime moduli whose
shifts are nonzero modulo those primes, a joint divisibility event makes the
full source product coprime to their product, so the triple-cofactor hypothesis
is automatic. -/
theorem taoLargePrimeJointProbability_le_crude_triple_of_not_dvd_shifts
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) (j₁ j₂ j₃ : Fin 1001)
    (hj₁ : j₁ ≠ 0) (hj₂ : j₂ ≠ 0) (hj₃ : j₃ ≠ 0)
    (h₁₂ : j₁ ≠ j₂) (h₁₃ : j₁ ≠ j₃) (h₂₃ : j₂ ≠ j₃)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpa : ¬a.2 ∣ a.1) (hqb : ¬b.2 ∣ b.1) :
    taoLargePrimeJointProbability P hP m' a b ≤
      (((((((2 * P j₁) * (2 * P j₂)) * (2 * P j₃)) /
          (a.2 * b.2) + 1) * 6 : ℕ) : ℝ) /
        (((taoDyadicPrimeBand (P j₁)).card : ℝ) *
          (taoDyadicPrimeBand (P j₂)).card *
          (taoDyadicPrimeBand (P j₃)).card)) := by
  have hzero : (0 : Fin 1001) ∉ ({j₁, j₂, j₃} : Finset (Fin 1001)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hj₁, Ne.symm hj₂, Ne.symm hj₃⟩
  have hpqCop : Nat.Coprime a.2 b.2 :=
    (Nat.coprime_primes hp hq).mpr hpq
  have hENN := taoPrimeTupleMeasure_largePrimeJointEvent_le_crude_triple
    P hP m' a b j₁ j₂ j₃ hj₁ hj₂ hj₃ h₁₂ h₁₃ h₂₃
      hpqCop (Nat.mul_pos hp.pos hq.pos) (by
        intro ω hω
        have hEvent := (Finset.mem_filter.mp hω).2
        have hcopStart :=
          taoLargePrimeJointDivisibilityEvent_coprime_mul
            hp hq hpa hqb hEvent
        rw [taoPrimeTupleStart_eq_multiCofactor_mul_selectedProduct
          m' {j₁, j₂, j₃} hzero] at hcopStart
        exact (Nat.coprime_mul_iff_left.mp hcopStart).1)
  rw [taoLargePrimeJointProbability, measureReal_def]
  have hdenom :
      (((taoDyadicPrimeBand (P j₁)).card : ENNReal) *
        (taoDyadicPrimeBand (P j₂)).card *
        (taoDyadicPrimeBand (P j₃)).card) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact_mod_cast Finset.card_ne_zero.mpr (hP j₁)
      · exact_mod_cast Finset.card_ne_zero.mpr (hP j₂)
    · exact_mod_cast Finset.card_ne_zero.mpr (hP j₃)
  have hreal := ENNReal.toReal_mono
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hdenom) hENN
  simpa using hreal

end

end Tao2026
