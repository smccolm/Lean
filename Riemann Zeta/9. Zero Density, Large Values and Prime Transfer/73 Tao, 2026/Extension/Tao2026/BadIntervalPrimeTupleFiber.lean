import Tao2026.BadIntervalPrimeTupleUniform

/-!
# Coordinate fibers of the prime tuple law

This module formalizes the finite ``freeze all coordinates except one'' step.
Replacing coordinate `j` by zero maps the tuple support onto a frozen support
whose cardinality is exactly the full support cardinality divided by the size
of the `j`-th prime band.  Consequently, a uniform cardinality bound `M` for
the event inside every frozen-coordinate fiber gives probability at most
`M / |primeBand(P j)|`.
-/

namespace Tao2026

open MeasureTheory
open scoped Classical

noncomputable section

set_option maxRecDepth 10000

/-- Replace coordinate `j` by the sentinel value zero.  Prime bands contain
only primes, so this records precisely the remaining 1000 coordinates. -/
def taoPrimeTupleFreezeCoordinate (j : Fin 1001) (ω : TaoPrimeTuple) : TaoPrimeTuple :=
  Function.update ω j 0

/-- Cartesian support in which coordinate `j` is replaced by `{0}`. -/
def taoPrimeTupleFrozenSupport (P : Fin 1001 → ℕ) (j : Fin 1001) :
    Finset TaoPrimeTuple :=
  Fintype.piFinset fun k => if k = j then {0} else taoDyadicPrimeBand (P k)

theorem taoPrimeTupleFreezeCoordinate_mem_frozenSupport
    {P : Fin 1001 → ℕ} {j : Fin 1001} {ω : TaoPrimeTuple}
    (hω : ω ∈ taoPrimeTupleSupport P) :
    taoPrimeTupleFreezeCoordinate j ω ∈ taoPrimeTupleFrozenSupport P j := by
  unfold taoPrimeTupleFrozenSupport
  rw [Fintype.mem_piFinset]
  intro k
  by_cases hkj : k = j
  · subst k
    simp [taoPrimeTupleFreezeCoordinate]
  · simp [taoPrimeTupleFreezeCoordinate, hkj,
      (mem_taoPrimeTupleSupport.mp hω) k]

theorem taoPrimeTuple_eq_of_freezeCoordinate_eq_of_apply_eq
    {j : Fin 1001} {ω₁ ω₂ : TaoPrimeTuple}
    (hfreeze : taoPrimeTupleFreezeCoordinate j ω₁ =
      taoPrimeTupleFreezeCoordinate j ω₂)
    (happly : ω₁ j = ω₂ j) :
    ω₁ = ω₂ := by
  funext k
  by_cases hkj : k = j
  · subst k
    exact happly
  · have hk := congrFun hfreeze k
    simpa [taoPrimeTupleFreezeCoordinate, hkj] using hk

theorem taoPrimeTuple_apply_eq_of_freezeCoordinate_eq
    {j k : Fin 1001} {ω₁ ω₂ : TaoPrimeTuple}
    (hfreeze : taoPrimeTupleFreezeCoordinate j ω₁ =
      taoPrimeTupleFreezeCoordinate j ω₂)
    (hkj : k ≠ j) :
    ω₁ k = ω₂ k := by
  have hk := congrFun hfreeze k
  simpa [taoPrimeTupleFreezeCoordinate, hkj] using hk

/-- The factor multiplying an ordinary coordinate in
`p₀²p₁⋯p₁₀₀₀m'`. -/
def taoPrimeTupleCoordinateCofactor
    (m' : ℕ) (j : Fin 1001) (ω : TaoPrimeTuple) : ℕ :=
  (ω 0) ^ 2 *
    (∏ k ∈ (Finset.univ.erase (0 : Fin 1001)).erase j, ω k) * m'

theorem taoPrimeTupleStart_eq_coordinateCofactor_mul
    (m' : ℕ) (j : Fin 1001) (hj : j ≠ 0) (ω : TaoPrimeTuple) :
    taoPrimeTupleStart m' ω = taoPrimeTupleCoordinateCofactor m' j ω * ω j := by
  have hjMem : j ∈ Finset.univ.erase (0 : Fin 1001) := by
    simp [hj]
  rw [taoPrimeTupleStart, taoPrimeTupleTailProduct,
    ← Finset.prod_erase_mul _ _ hjMem]
  unfold taoPrimeTupleCoordinateCofactor
  ac_rfl

theorem taoPrimeTupleCoordinateCofactor_eq_of_freezeCoordinate_eq
    (m' : ℕ) {j : Fin 1001} {ω₁ ω₂ : TaoPrimeTuple} (hj : j ≠ 0)
    (hfreeze : taoPrimeTupleFreezeCoordinate j ω₁ =
      taoPrimeTupleFreezeCoordinate j ω₂) :
    taoPrimeTupleCoordinateCofactor m' j ω₁ =
      taoPrimeTupleCoordinateCofactor m' j ω₂ := by
  unfold taoPrimeTupleCoordinateCofactor
  congr 2
  · exact congrArg (fun n : ℕ => n ^ 2)
      (taoPrimeTuple_apply_eq_of_freezeCoordinate_eq hfreeze (Ne.symm hj))
  · apply Finset.prod_congr rfl
    intro k hk
    exact taoPrimeTuple_apply_eq_of_freezeCoordinate_eq hfreeze
      (Finset.ne_of_mem_erase hk)

theorem taoPrimeTuple_apply_modEq_of_start_modEq
    (m' : ℕ) {j : Fin 1001} (hj : j ≠ 0) {q : ℕ} {ω₁ ω₂ : TaoPrimeTuple}
    (hfreeze : taoPrimeTupleFreezeCoordinate j ω₁ =
      taoPrimeTupleFreezeCoordinate j ω₂)
    (hcop : Nat.Coprime (taoPrimeTupleCoordinateCofactor m' j ω₁) q)
    (hstart : taoPrimeTupleStart m' ω₁ ≡ taoPrimeTupleStart m' ω₂ [MOD q]) :
    ω₁ j ≡ ω₂ j [MOD q] := by
  have hcofactor :=
    taoPrimeTupleCoordinateCofactor_eq_of_freezeCoordinate_eq m' hj hfreeze
  rw [taoPrimeTupleStart_eq_coordinateCofactor_mul m' j hj,
    taoPrimeTupleStart_eq_coordinateCofactor_mul m' j hj, ← hcofactor] at hstart
  exact Nat.ModEq.cancel_left_of_coprime hcop.symm hstart

theorem taoPrimeTupleFrozenSupport_nonempty
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (j : Fin 1001) :
    (taoPrimeTupleFrozenSupport P j).Nonempty := by
  let ω : TaoPrimeTuple := fun k => (hP k).choose
  have hω : ω ∈ taoPrimeTupleSupport P :=
    mem_taoPrimeTupleSupport.mpr fun k => (hP k).choose_spec
  exact ⟨taoPrimeTupleFreezeCoordinate j ω,
    taoPrimeTupleFreezeCoordinate_mem_frozenSupport hω⟩

/-- Generic cardinality identity underlying coordinate freezing. -/
theorem card_piFinset_singleton_coordinate
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (s : ι → Finset α) (j : ι) (a : α) :
    (Fintype.piFinset fun k => if k = j then {a} else s k).card * (s j).card =
      (Fintype.piFinset s).card := by
  rw [Fintype.card_piFinset, Fintype.card_piFinset]
  calc
    (∏ k : ι, (if k = j then {a} else s k).card) * (s j).card =
        (∏ k ∈ Finset.univ.erase j, (s k).card) * (s j).card := by
      congr 1
      rw [← Finset.prod_erase_mul Finset.univ
        (fun k => (if k = j then {a} else s k).card) (Finset.mem_univ j)]
      simp only [if_pos, Finset.card_singleton, mul_one]
      apply Finset.prod_congr rfl
      intro k hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      simp [hkj]
    _ = ∏ k : ι, (s k).card :=
      Finset.prod_erase_mul _ _ (Finset.mem_univ j)

/-- The frozen support times the missing band is the full tuple support. -/
theorem card_taoPrimeTupleFrozenSupport_mul_band
    (P : Fin 1001 → ℕ) (j : Fin 1001) :
    (taoPrimeTupleFrozenSupport P j).card * (taoDyadicPrimeBand (P j)).card =
      (taoPrimeTupleSupport P).card := by
  simpa only [taoPrimeTupleFrozenSupport, taoPrimeTupleSupport] using
    card_piFinset_singleton_coordinate
      (fun k => taoDyadicPrimeBand (P k)) j 0

/-- A finite set is bounded by the number of attained images times a uniform
bound for every fiber. -/
theorem card_le_card_image_mul_of_fiber_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (M : ℕ)
    (hM : ∀ y ∈ s.image f, (s.filter fun x => f x = y).card ≤ M) :
    s.card ≤ (s.image f).card * M := by
  have hMaps : ∀ x ∈ s, f x ∈ s.image f := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hFiber := Finset.sum_fiberwise_of_maps_to hMaps (fun _ => 1)
  calc
    s.card = ∑ x ∈ s, 1 := by simp
    _ = ∑ y ∈ s.image f, ∑ x ∈ s with f x = y, 1 := hFiber.symm
    _ = ∑ y ∈ s.image f, (s.filter fun x => f x = y).card := by simp
    _ ≤ ∑ _y ∈ s.image f, M := by
      exact Finset.sum_le_sum fun y hy => hM y hy
    _ = (s.image f).card * M := by simp

/-- A uniform bound on the event in every frozen-coordinate fiber bounds the
total number of supported event tuples. -/
theorem card_taoPrimeTupleEvent_le_frozenSupport_mul
    (P : Fin 1001 → ℕ) (E : Set TaoPrimeTuple) (j : Fin 1001) (M : ℕ)
    (hM : ∀ ρ ∈ taoPrimeTupleFrozenSupport P j,
      (((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).filter
        fun ω => taoPrimeTupleFreezeCoordinate j ω = ρ).card ≤ M) :
    ((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).card ≤
      (taoPrimeTupleFrozenSupport P j).card * M := by
  let A := (taoPrimeTupleSupport P).filter fun ω => ω ∈ E
  calc
    A.card ≤ (A.image (taoPrimeTupleFreezeCoordinate j)).card * M := by
      apply card_le_card_image_mul_of_fiber_le
      intro ρ hρ
      apply hM
      rcases Finset.mem_image.mp hρ with ⟨ω, hω, rfl⟩
      exact taoPrimeTupleFreezeCoordinate_mem_frozenSupport
        (Finset.mem_filter.mp hω).1
    _ ≤ (taoPrimeTupleFrozenSupport P j).card * M := by
      apply Nat.mul_le_mul_right
      apply Finset.card_le_card
      intro ρ hρ
      rcases Finset.mem_image.mp hρ with ⟨ω, hω, rfl⟩
      exact taoPrimeTupleFreezeCoordinate_mem_frozenSupport
        (Finset.mem_filter.mp hω).1

/-- Exact counting-ratio form of the finite uniform tuple law. -/
theorem taoPrimeTupleMeasure_apply_eq_card_div_support
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (E : Set TaoPrimeTuple) :
    taoPrimeTupleMeasure P hP E =
      ((taoPrimeTupleSupport P).filter (fun ω => ω ∈ E)).card /
        (taoPrimeTupleSupport P).card := by
  rw [taoPrimeTupleMeasure_apply_eq_card_mul_atom, div_eq_mul_inv]
  congr 2
  rw [taoPrimeTupleSupport, Fintype.card_piFinset]
  exact (Nat.cast_prod _ _).symm

/-- Coordinate-freezing probability bound.  This is the exact finite version
of conditioning on all coordinates other than `j`. -/
theorem taoPrimeTupleMeasure_le_card_coordinateFiber_div_band
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (E : Set TaoPrimeTuple) (j : Fin 1001) (M : ℕ)
    (hM : ∀ ρ ∈ taoPrimeTupleFrozenSupport P j,
      (((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).filter
        fun ω => taoPrimeTupleFreezeCoordinate j ω = ρ).card ≤ M) :
    taoPrimeTupleMeasure P hP E ≤
      (M : ENNReal) / (taoDyadicPrimeBand (P j)).card := by
  rw [taoPrimeTupleMeasure_apply_eq_card_div_support,
    ← card_taoPrimeTupleFrozenSupport_mul_band P j]
  push_cast
  calc
    (((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).card : ENNReal) /
        ((taoPrimeTupleFrozenSupport P j).card *
          (taoDyadicPrimeBand (P j)).card) ≤
        (((taoPrimeTupleFrozenSupport P j).card * M : ℕ) : ENNReal) /
          ((taoPrimeTupleFrozenSupport P j).card *
            (taoDyadicPrimeBand (P j)).card) := by
      apply ENNReal.div_le_div_right
      exact_mod_cast card_taoPrimeTupleEvent_le_frozenSupport_mul P E j M hM
    _ = (M : ENNReal) / (taoDyadicPrimeBand (P j)).card := by
      rw [Nat.cast_mul]
      apply ENNReal.mul_div_mul_left
      · exact_mod_cast Finset.card_ne_zero.mpr
          (taoPrimeTupleFrozenSupport_nonempty P hP j)
      · simp

/-- If, after the other coordinates are frozen, every event tuple places its
`j`-th coordinate in one residue class modulo `q`, the elementary progression
count gives the corresponding crude probability estimate. -/
theorem taoPrimeTupleMeasure_le_residueFiber_div_band
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (E : Set TaoPrimeTuple) (j : Fin 1001) (q : ℕ) (hq : 0 < q)
    (a : TaoPrimeTuple → ℕ)
    (hResidue : ∀ ω ∈ (taoPrimeTupleSupport P).filter (fun ω => ω ∈ E),
      ω j ≡ a (taoPrimeTupleFreezeCoordinate j ω) [MOD q]) :
    taoPrimeTupleMeasure P hP E ≤
      (((2 * P j) / q + 1 : ℕ) : ENNReal) /
        (taoDyadicPrimeBand (P j)).card := by
  apply taoPrimeTupleMeasure_le_card_coordinateFiber_div_band
  intro ρ hρ
  let A := ((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).filter
    fun ω => taoPrimeTupleFreezeCoordinate j ω = ρ
  calc
    A.card = (A.image fun ω => ω j).card := by
      rw [Finset.card_image_iff.mpr]
      intro ω₁ hω₁ ω₂ hω₂ heval
      apply taoPrimeTuple_eq_of_freezeCoordinate_eq_of_apply_eq
      · exact (Finset.mem_filter.mp hω₁).2.trans
          (Finset.mem_filter.mp hω₂).2.symm
      · exact heval
    _ ≤ (taoDyadicPrimeResidueFiber q (a ρ) (P j)).card := by
      apply Finset.card_le_card
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨ω, hω, rfl⟩
      have hωData := Finset.mem_filter.mp hω
      rw [taoDyadicPrimeResidueFiber, Finset.mem_filter]
      refine ⟨(mem_taoPrimeTupleSupport.mp
        (Finset.mem_filter.mp hωData.1).1) j, ?_⟩
      simpa [hωData.2] using hResidue ω hωData.1
    _ ≤ (2 * P j) / q + 1 :=
      card_taoDyadicPrimeResidueFiber_le hq

/-- Pairwise residue rigidity is enough for the crude coordinate estimate;
no explicit choice of the residue class is needed by a consumer. -/
theorem taoPrimeTupleMeasure_le_of_freezeCoordinate_modEq
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (E : Set TaoPrimeTuple) (j : Fin 1001) (q : ℕ) (hq : 0 < q)
    (hModEq : ∀ ω₁ ∈ (taoPrimeTupleSupport P).filter (fun ω => ω ∈ E),
      ∀ ω₂ ∈ (taoPrimeTupleSupport P).filter (fun ω => ω ∈ E),
        taoPrimeTupleFreezeCoordinate j ω₁ =
          taoPrimeTupleFreezeCoordinate j ω₂ →
        ω₁ j ≡ ω₂ j [MOD q]) :
    taoPrimeTupleMeasure P hP E ≤
      (((2 * P j) / q + 1 : ℕ) : ENNReal) /
        (taoDyadicPrimeBand (P j)).card := by
  apply taoPrimeTupleMeasure_le_card_coordinateFiber_div_band
  intro ρ hρ
  let A := ((taoPrimeTupleSupport P).filter fun ω => ω ∈ E).filter
    fun ω => taoPrimeTupleFreezeCoordinate j ω = ρ
  by_cases hA : A.Nonempty
  · let ω₀ := hA.choose
    have hω₀ : ω₀ ∈ A := hA.choose_spec
    calc
      A.card = (A.image fun ω => ω j).card := by
        rw [Finset.card_image_iff.mpr]
        intro ω₁ hω₁ ω₂ hω₂ heval
        apply taoPrimeTuple_eq_of_freezeCoordinate_eq_of_apply_eq
        · exact (Finset.mem_filter.mp hω₁).2.trans
            (Finset.mem_filter.mp hω₂).2.symm
        · exact heval
      _ ≤ (taoDyadicPrimeResidueFiber q (ω₀ j) (P j)).card := by
        apply Finset.card_le_card
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨ω, hω, rfl⟩
        have hωData := Finset.mem_filter.mp hω
        have hω₀Data := Finset.mem_filter.mp hω₀
        rw [taoDyadicPrimeResidueFiber, Finset.mem_filter]
        refine ⟨(mem_taoPrimeTupleSupport.mp
          (Finset.mem_filter.mp hωData.1).1) j, ?_⟩
        exact hModEq ω hωData.1 ω₀ hω₀Data.1
          (hωData.2.trans hω₀Data.2.symm)
      _ ≤ (2 * P j) / q + 1 :=
        card_taoDyadicPrimeResidueFiber_le hq
  · change A.card ≤ (2 * P j) / q + 1
    rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

/-- Crude estimate for an event whose source products are pairwise congruent
modulo `q`, provided an ordinary coordinate has coprime complementary factor. -/
theorem taoPrimeTupleMeasure_startEvent_le_crude_coordinate
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (m' : ℕ) (E : Set TaoPrimeTuple) (j : Fin 1001) (hj : j ≠ 0)
    (q : ℕ) (hq : 0 < q)
    (hcop : ∀ ω ∈ (taoPrimeTupleSupport P).filter (fun ω => ω ∈ E),
      Nat.Coprime (taoPrimeTupleCoordinateCofactor m' j ω) q)
    (hstart : ∀ ω₁ ∈ (taoPrimeTupleSupport P).filter (fun ω => ω ∈ E),
      ∀ ω₂ ∈ (taoPrimeTupleSupport P).filter (fun ω => ω ∈ E),
        taoPrimeTupleStart m' ω₁ ≡ taoPrimeTupleStart m' ω₂ [MOD q]) :
    taoPrimeTupleMeasure P hP E ≤
      (((2 * P j) / q + 1 : ℕ) : ENNReal) /
        (taoDyadicPrimeBand (P j)).card := by
  apply taoPrimeTupleMeasure_le_of_freezeCoordinate_modEq P hP E j q hq
  intro ω₁ hω₁ ω₂ hω₂ hfreeze
  exact taoPrimeTuple_apply_modEq_of_start_modEq m' hj hfreeze
    (hcop ω₁ hω₁) (hstart ω₁ hω₁ ω₂ hω₂)

/-- Single large-prime divisibility events satisfy the crude coordinate bound
as soon as the complementary source factor is coprime to the modulus. -/
theorem taoPrimeTupleMeasure_largePrimeDivisibilityEvent_le_crude_coordinate
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) (j : Fin 1001) (hj : j ≠ 0) (hq : 0 < a.2)
    (hcop : ∀ ω ∈ (taoPrimeTupleSupport P).filter
      (fun ω => TaoLargePrimeDivisibilityEvent m' a ω),
      Nat.Coprime (taoPrimeTupleCoordinateCofactor m' j ω) a.2) :
    taoPrimeTupleMeasure P hP
        { ω | TaoLargePrimeDivisibilityEvent m' a ω } ≤
      (((2 * P j) / a.2 + 1 : ℕ) : ENNReal) /
        (taoDyadicPrimeBand (P j)).card := by
  apply taoPrimeTupleMeasure_startEvent_le_crude_coordinate
    P hP m' { ω | TaoLargePrimeDivisibilityEvent m' a ω } j hj a.2 hq hcop
  intro ω₁ hω₁ ω₂ hω₂
  exact taoLargePrimeDivisibilityEvent_modEq
    (Finset.mem_filter.mp hω₁).2 (Finset.mem_filter.mp hω₂).2

/-- Joint distinct-modulus events have the analogous product-modulus crude
bound when their complementary source factor is coprime to the product. -/
theorem taoPrimeTupleMeasure_largePrimeJointEvent_le_crude_coordinate
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) (j : Fin 1001) (hj : j ≠ 0)
    (hpq : Nat.Coprime a.2 b.2) (hq : 0 < a.2 * b.2)
    (hcop : ∀ ω ∈ (taoPrimeTupleSupport P).filter
      (fun ω => TaoLargePrimeJointDivisibilityEvent m' a b ω),
      Nat.Coprime (taoPrimeTupleCoordinateCofactor m' j ω) (a.2 * b.2)) :
    taoPrimeTupleMeasure P hP
        { ω | TaoLargePrimeJointDivisibilityEvent m' a b ω } ≤
      (((2 * P j) / (a.2 * b.2) + 1 : ℕ) : ENNReal) /
        (taoDyadicPrimeBand (P j)).card := by
  apply taoPrimeTupleMeasure_startEvent_le_crude_coordinate
    P hP m' { ω | TaoLargePrimeJointDivisibilityEvent m' a b ω }
      j hj (a.2 * b.2) hq hcop
  intro ω₁ hω₁ ω₂ hω₂
  exact taoLargePrimeJointDivisibilityEvent_modEq_mul hpq
    (Finset.mem_filter.mp hω₁).2 (Finset.mem_filter.mp hω₂).2

/-- Split a source-product residue event into the coprime part, controlled by
coordinate freezing, and the noncoprime part, ready for collision bounds. -/
theorem taoPrimeTupleMeasureReal_startEvent_le_crude_add_notCoprime
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (m' : ℕ) (E : Set TaoPrimeTuple) (j : Fin 1001) (hj : j ≠ 0)
    (q : ℕ) (hq : 0 < q)
    (hstart : ∀ ω₁ ∈ (taoPrimeTupleSupport P).filter (fun ω => ω ∈ E),
      ∀ ω₂ ∈ (taoPrimeTupleSupport P).filter (fun ω => ω ∈ E),
        taoPrimeTupleStart m' ω₁ ≡ taoPrimeTupleStart m' ω₂ [MOD q]) :
    (taoPrimeTupleMeasure P hP).real E ≤
      (((2 * P j) / q + 1 : ℕ) : ℝ) /
          (taoDyadicPrimeBand (P j)).card +
        (taoPrimeTupleMeasure P hP).real
          { ω | ¬ Nat.Coprime (taoPrimeTupleStart m' ω) q } := by
  classical
  let good : Set TaoPrimeTuple :=
    { ω | ω ∈ E ∧ Nat.Coprime (taoPrimeTupleStart m' ω) q }
  have hgoodENN : taoPrimeTupleMeasure P hP good ≤
      (((2 * P j) / q + 1 : ℕ) : ENNReal) /
        (taoDyadicPrimeBand (P j)).card := by
    dsimp only [good]
    apply taoPrimeTupleMeasure_startEvent_le_crude_coordinate
      P hP m' { ω | ω ∈ E ∧
        Nat.Coprime (taoPrimeTupleStart m' ω) q } j hj q hq
    · intro ω hω
      have hωData := (@Finset.mem_filter TaoPrimeTuple
        (fun ν => ν ∈ { ξ | ξ ∈ E ∧
          Nat.Coprime (taoPrimeTupleStart m' ξ) q })
        (fun _ => Classical.propDecidable _) _ ω).mp hω
      have hcopStart : Nat.Coprime (taoPrimeTupleStart m' ω) q :=
        hωData.2.2
      rw [taoPrimeTupleStart_eq_coordinateCofactor_mul m' j hj] at hcopStart
      exact (Nat.coprime_mul_iff_left.mp hcopStart).1
    · intro ω₁ hω₁ ω₂ hω₂
      have hω₁Data := (@Finset.mem_filter TaoPrimeTuple
        (fun ν => ν ∈ { ξ | ξ ∈ E ∧
          Nat.Coprime (taoPrimeTupleStart m' ξ) q })
        (fun _ => Classical.propDecidable _) _ ω₁).mp hω₁
      have hω₂Data := (@Finset.mem_filter TaoPrimeTuple
        (fun ν => ν ∈ { ξ | ξ ∈ E ∧
          Nat.Coprime (taoPrimeTupleStart m' ξ) q })
        (fun _ => Classical.propDecidable _) _ ω₂).mp hω₂
      apply hstart
      · exact (@Finset.mem_filter TaoPrimeTuple (fun ν => ν ∈ E)
          (fun _ => Classical.propDecidable _) _ ω₁).mpr
            ⟨hω₁Data.1, hω₁Data.2.1⟩
      · exact (@Finset.mem_filter TaoPrimeTuple (fun ν => ν ∈ E)
          (fun _ => Classical.propDecidable _) _ ω₂).mpr
            ⟨hω₂Data.1, hω₂Data.2.1⟩
  have hgoodReal : (taoPrimeTupleMeasure P hP).real good ≤
      (((2 * P j) / q + 1 : ℕ) : ℝ) /
        (taoDyadicPrimeBand (P j)).card := by
    rw [measureReal_def]
    have h := ENNReal.toReal_mono (ENNReal.div_ne_top (by simp) (by
      exact_mod_cast Finset.card_ne_zero.mpr (hP j))) hgoodENN
    simpa using h
  have hsplit : E = good ∪
      { ω | ω ∈ E ∧ ¬ Nat.Coprime (taoPrimeTupleStart m' ω) q } := by
    ext ω
    change ω ∈ E ↔
      (ω ∈ E ∧ Nat.Coprime (taoPrimeTupleStart m' ω) q) ∨
      (ω ∈ E ∧ ¬ Nat.Coprime (taoPrimeTupleStart m' ω) q)
    constructor
    · intro hωE
      by_cases hcop : Nat.Coprime (taoPrimeTupleStart m' ω) q
      · exact Or.inl ⟨hωE, hcop⟩
      · exact Or.inr ⟨hωE, hcop⟩
    · rintro (⟨hωE, _⟩ | ⟨hωE, _⟩) <;> exact hωE
  rw [hsplit]
  calc
    (taoPrimeTupleMeasure P hP).real
        (good ∪ { ω | ω ∈ E ∧
          ¬ Nat.Coprime (taoPrimeTupleStart m' ω) q }) ≤
      (taoPrimeTupleMeasure P hP).real good +
        (taoPrimeTupleMeasure P hP).real
          { ω | ω ∈ E ∧
            ¬ Nat.Coprime (taoPrimeTupleStart m' ω) q } :=
      measureReal_union_le _ _
    _ ≤ (((2 * P j) / q + 1 : ℕ) : ℝ) /
          (taoDyadicPrimeBand (P j)).card +
        (taoPrimeTupleMeasure P hP).real
          { ω | ¬ Nat.Coprime (taoPrimeTupleStart m' ω) q } := by
      apply add_le_add hgoodReal
      apply measureReal_mono (by
        intro ω hω
        exact hω.2) (by simp)

/-- Unconditional crude one-prime probability bound: the noncoprime part is
charged to the existing coordinate-collision union. -/
theorem taoLargePrimeProbability_le_crude_coordinate_add_collisions
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) (j : Fin 1001) (hj : j ≠ 0)
    (hp : Nat.Prime a.2) (hm : Nat.Coprime m' a.2) :
    taoLargePrimeProbability P hP m' a ≤
      (((2 * P j) / a.2 + 1 : ℕ) : ℝ) /
          (taoDyadicPrimeBand (P j)).card +
        ∑ k : Fin 1001, ((taoDyadicPrimeBand (P k)).card : ℝ)⁻¹ := by
  have hcrude := taoPrimeTupleMeasureReal_startEvent_le_crude_add_notCoprime
    P hP m' { ω | TaoLargePrimeDivisibilityEvent m' a ω }
      j hj a.2 hp.pos (by
        intro ω₁ hω₁ ω₂ hω₂
        exact taoLargePrimeDivisibilityEvent_modEq
          (Finset.mem_filter.mp hω₁).2
          (Finset.mem_filter.mp hω₂).2)
  calc
    taoLargePrimeProbability P hP m' a ≤
        (((2 * P j) / a.2 + 1 : ℕ) : ℝ) /
            (taoDyadicPrimeBand (P j)).card +
          (taoPrimeTupleMeasure P hP).real
            { ω | ¬ Nat.Coprime (taoPrimeTupleStart m' ω) a.2 } := by
      simpa [taoLargePrimeProbability] using hcrude
    _ ≤ (((2 * P j) / a.2 + 1 : ℕ) : ℝ) /
            (taoDyadicPrimeBand (P j)).card +
          ∑ k : Fin 1001, ((taoDyadicPrimeBand (P k)).card : ℝ)⁻¹ := by
      apply add_le_add le_rfl
      calc
        (taoPrimeTupleMeasure P hP).real
            { ω | ¬ Nat.Coprime (taoPrimeTupleStart m' ω) a.2 } ≤
          (taoPrimeTupleMeasure P hP).real
            { ω | TaoPrimeTuplePrimeCollision a.2 ω } :=
          measureReal_mono
            (not_coprime_taoPrimeTupleStart_subset_primeCollision hp hm)
        _ ≤ ∑ k : Fin 1001,
            ((taoDyadicPrimeBand (P k)).card : ℝ)⁻¹ :=
          taoPrimeTuplePrimeCollision_probability_le P hP hp

/-- Unconditional crude two-prime joint-probability bound, with both possible
modulus-prime collisions charged explicitly. -/
theorem taoLargePrimeJointProbability_le_crude_coordinate_add_collisions
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) (j : Fin 1001) (hj : j ≠ 0)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hm : Nat.Coprime m' (a.2 * b.2)) :
    taoLargePrimeJointProbability P hP m' a b ≤
      (((2 * P j) / (a.2 * b.2) + 1 : ℕ) : ℝ) /
          (taoDyadicPrimeBand (P j)).card +
        2 * ∑ k : Fin 1001,
          ((taoDyadicPrimeBand (P k)).card : ℝ)⁻¹ := by
  have hpqCop : Nat.Coprime a.2 b.2 := (Nat.coprime_primes hp hq).mpr hpq
  have hcrude := taoPrimeTupleMeasureReal_startEvent_le_crude_add_notCoprime
    P hP m' { ω | TaoLargePrimeJointDivisibilityEvent m' a b ω }
      j hj (a.2 * b.2) (Nat.mul_pos hp.pos hq.pos) (by
        intro ω₁ hω₁ ω₂ hω₂
        exact taoLargePrimeJointDivisibilityEvent_modEq_mul hpqCop
          (Finset.mem_filter.mp hω₁).2
          (Finset.mem_filter.mp hω₂).2)
  calc
    taoLargePrimeJointProbability P hP m' a b ≤
        (((2 * P j) / (a.2 * b.2) + 1 : ℕ) : ℝ) /
            (taoDyadicPrimeBand (P j)).card +
          (taoPrimeTupleMeasure P hP).real
            { ω | ¬ Nat.Coprime
              (taoPrimeTupleStart m' ω) (a.2 * b.2) } := by
      simpa [taoLargePrimeJointProbability] using hcrude
    _ ≤ (((2 * P j) / (a.2 * b.2) + 1 : ℕ) : ℝ) /
            (taoDyadicPrimeBand (P j)).card +
          2 * ∑ k : Fin 1001,
            ((taoDyadicPrimeBand (P k)).card : ℝ)⁻¹ := by
      apply add_le_add le_rfl
      calc
        (taoPrimeTupleMeasure P hP).real
            { ω | ¬ Nat.Coprime
              (taoPrimeTupleStart m' ω) (a.2 * b.2) } ≤
          (taoPrimeTupleMeasure P hP).real
            ({ ω | TaoPrimeTuplePrimeCollision a.2 ω } ∪
              { ω | TaoPrimeTuplePrimeCollision b.2 ω }) :=
          measureReal_mono
            (not_coprime_taoPrimeTupleStart_mul_subset_primeCollision_union
              hp hq hm)
        _ ≤ 2 * ∑ k : Fin 1001,
            ((taoDyadicPrimeBand (P k)).card : ℝ)⁻¹ :=
          taoPrimeTuplePrimeCollision_union_probability_le P hP hp hq

end

end Tao2026
