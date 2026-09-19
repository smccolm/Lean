import Tao2026.BurgessWeilPrimeKummerNewtonQuarticIntegrality

/-!
# Unconditional quintic higher-root Newton integrality

An order-five orbit theorem decomposes the quintic extension correlation into
base-field fixed points and full five-element Frobenius orbits.  The fifth
Newton numerator is then assembled from the degree-five complete homogeneous
base expression, the already-integral degree-two through degree-four
aggregate residuals, and the quintic orbit sum.
-/

namespace Tao2026

open Finset
open scoped BigOperators

noncomputable section

def orbitFive {α : Type*} [DecidableEq α]
    (σ : α ≃ α) (x : α) : Finset α :=
  {x, σ x, σ (σ x), σ (σ (σ x)), σ (σ (σ (σ x)))}

def orbitFiveRep {α : Type*} [LinearOrder α]
    (σ : α ≃ α) (x : α) : α :=
  (orbitFive σ x).min' (by simp [orbitFive])

private theorem orbitFive_apply
    {α : Type*} [LinearOrder α] (σ : α ≃ α)
    (hσ : ∀ x, σ (σ (σ (σ (σ x)))) = x) (x : α) :
    orbitFive σ (σ x) = orbitFive σ x := by
  ext y
  simp only [orbitFive, Finset.mem_insert, Finset.mem_singleton]
  rw [hσ]
  aesop

private theorem orbitFiveRep_apply
    {α : Type*} [LinearOrder α] (σ : α ≃ α)
    (hσ : ∀ x, σ (σ (σ (σ (σ x)))) = x) (x : α) :
    orbitFiveRep σ (σ x) = orbitFiveRep σ x := by
  unfold orbitFiveRep
  apply (Finset.min'_eq_iff (orbitFive σ (σ x)) _ _).2
  constructor
  · rw [orbitFive_apply σ hσ]
    exact Finset.min'_mem _ _
  · intro b hb
    apply Finset.min'_le
    rw [← orbitFive_apply σ hσ]
    exact hb

private theorem orbitFiveRep_iterate_two
    {α : Type*} [LinearOrder α] (σ : α ≃ α)
    (hσ : ∀ x, σ (σ (σ (σ (σ x)))) = x) (x : α) :
    orbitFiveRep σ (σ (σ x)) = orbitFiveRep σ x := by
  rw [orbitFiveRep_apply σ hσ, orbitFiveRep_apply σ hσ]

private theorem orbitFiveRep_iterate_three
    {α : Type*} [LinearOrder α] (σ : α ≃ α)
    (hσ : ∀ x, σ (σ (σ (σ (σ x)))) = x) (x : α) :
    orbitFiveRep σ (σ (σ (σ x))) = orbitFiveRep σ x := by
  rw [orbitFiveRep_apply σ hσ, orbitFiveRep_apply σ hσ,
    orbitFiveRep_apply σ hσ]

private theorem orbitFiveRep_iterate_four
    {α : Type*} [LinearOrder α] (σ : α ≃ α)
    (hσ : ∀ x, σ (σ (σ (σ (σ x)))) = x) (x : α) :
    orbitFiveRep σ (σ (σ (σ (σ x)))) = orbitFiveRep σ x := by
  rw [orbitFiveRep_apply σ hσ, orbitFiveRep_apply σ hσ,
    orbitFiveRep_apply σ hσ, orbitFiveRep_apply σ hσ]

private theorem orbitFiveRep_mem
    {α : Type*} [LinearOrder α] (σ : α ≃ α) (x : α) :
    orbitFiveRep σ x ∈ orbitFive σ x := by
  exact Finset.min'_mem _ _

theorem sum_order_five
    {α R : Type*} [Fintype α] [LinearOrder α]
    [CommRing R] (σ : α ≃ α) (hσ : ∀ x, σ (σ (σ (σ (σ x)))) = x)
    (w : α → R) (hw : ∀ x, w (σ x) = w x) :
    ∑ x, w x =
      ∑ x ∈ Finset.univ.filter (fun x => σ x = x), w x +
        5 * ∑ x ∈ Finset.univ.filter
          (fun x => σ x ≠ x ∧ orbitFiveRep σ x = x), w x := by
  let fixed := Finset.univ.filter (fun x => σ x = x)
  let moved := Finset.univ.filter (fun x => σ x ≠ x)
  let reps := Finset.univ.filter
    (fun x => σ x ≠ x ∧ orbitFiveRep σ x = x)
  let act : α × Fin 5 → α := fun z =>
    match z.2.1 with
    | 0 => z.1
    | 1 => σ z.1
    | 2 => σ (σ z.1)
    | 3 => σ (σ (σ z.1))
    | _ => σ (σ (σ (σ z.1)))
  have hsplit :
      (∑ x, w x) = (∑ x ∈ fixed, w x) + ∑ x ∈ moved, w x := by
    symm
    simpa [fixed, moved] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => σ x = x) w)
  have hact_zero (x : α) : act (x, (0 : Fin 5)) = x := by rfl
  have hact_one (x : α) : act (x, (1 : Fin 5)) = σ x := by rfl
  have hact_two (x : α) : act (x, (2 : Fin 5)) = σ (σ x) := by rfl
  have hact_three (x : α) : act (x, (3 : Fin 5)) = σ (σ (σ x)) := by rfl
  have hact_four (x : α) : act (x, (4 : Fin 5)) =
      σ (σ (σ (σ x))) := by rfl
  have hrep_act (x : α) (i : Fin 5) :
      orbitFiveRep σ (act (x, i)) = orbitFiveRep σ x := by
    fin_cases i
    · simp [act]
    · simp [act, orbitFiveRep_apply σ hσ]
    · simp [act, orbitFiveRep_iterate_two σ hσ]
    · simp [act, orbitFiveRep_iterate_three σ hσ]
    · simp [act, orbitFiveRep_iterate_four σ hσ]
  have hact_moved {x : α} (hx : σ x ≠ x) (i : Fin 5) :
      σ (act (x, i)) ≠ act (x, i) := by
    fin_cases i
    · simpa [act] using hx
    · simp only [act]
      intro h
      exact hx (σ.injective h)
    · simp only [act]
      intro h
      exact hx (σ.injective (σ.injective h))
    · simp only [act]
      intro h
      exact hx (σ.injective (σ.injective (σ.injective h)))
    · simp only [act, hσ]
      intro h
      exact hx (by simpa [hσ] using congrArg σ h)
  have horbit :
      (∑ x ∈ moved, w x) =
        ∑ z ∈ reps ×ˢ (Finset.univ : Finset (Fin 5)), w (act z) := by
    symm
    refine Finset.sum_bij (fun z _hz => act z) ?_ ?_ ?_ ?_
    · intro z hz
      have hzrep : z.1 ∈ reps := (Finset.mem_product.mp hz).1
      have hzmove : σ z.1 ≠ z.1 := (Finset.mem_filter.mp hzrep).2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact_moved hzmove z.2⟩
    · rintro ⟨a, i⟩ hz₁ ⟨b, j⟩ hz₂ heq
      change act (a, i) = act (b, j) at heq
      have hz₁rep : orbitFiveRep σ a = a :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hz₁).1).2.2
      have hz₂rep : orbitFiveRep σ b = b :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hz₂).1).2.2
      have hfst : a = b := by
        rw [← hz₁rep, ← hz₂rep, ← hrep_act a i,
          ← hrep_act b j, heq]
      subst b
      have h01 : σ a ≠ a :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hz₁).1).2.1
      have h02 : σ (σ a) ≠ a := by
        intro h
        apply h01
        have h4 : σ (σ (σ (σ a))) = a := by
          calc
            σ (σ (σ (σ a))) = σ (σ a) := congrArg (fun z => σ (σ z)) h
            _ = a := h
        simpa [hσ] using (congrArg σ h4).symm
      have h03 : σ (σ (σ a)) ≠ a := by
        intro h
        apply h02
        have hh := congrArg (fun z => σ (σ z)) h
        simpa [hσ] using hh.symm
      have h04 : σ (σ (σ (σ a))) ≠ a := by
        intro h
        apply h01
        simpa [hσ] using (congrArg σ h).symm
      have h12 : σ (σ a) ≠ σ a := fun h => h01 (σ.injective h)
      have h13 : σ (σ (σ a)) ≠ σ a := fun h => h02 (σ.injective h)
      have h14 : σ (σ (σ (σ a))) ≠ σ a := fun h => h03 (σ.injective h)
      have h23 : σ (σ (σ a)) ≠ σ (σ a) := fun h => h12 (σ.injective h)
      have h24 : σ (σ (σ (σ a))) ≠ σ (σ a) := fun h =>
        h02 (σ.injective (σ.injective h))
      have h34 : σ (σ (σ (σ a))) ≠ σ (σ (σ a)) := fun h =>
        h23 (σ.injective h)
      apply Prod.ext
      · rfl
      fin_cases i <;> fin_cases j
      all_goals simp only [act] at heq
      all_goals try rfl
      · exact (h01 heq.symm).elim
      · exact (h02 heq.symm).elim
      · exact (h03 heq.symm).elim
      · exact (h04 heq.symm).elim
      · exact (h01 heq).elim
      · exact (h12 heq.symm).elim
      · exact (h13 heq.symm).elim
      · exact (h14 heq.symm).elim
      · exact (h02 heq).elim
      · exact (h12 heq).elim
      · exact (h23 heq.symm).elim
      · exact (h24 heq.symm).elim
      · exact (h03 heq).elim
      · exact (h13 heq).elim
      · exact (h23 heq).elim
      · exact (h34 heq.symm).elim
      · exact (h04 heq).elim
      · exact (h14 heq).elim
      · exact (h24 heq).elim
      · exact (h34 heq).elim
    · intro z hz
      have hzmove : σ z ≠ z := (Finset.mem_filter.mp hz).2
      let r := orbitFiveRep σ z
      have hrmem := orbitFiveRep_mem σ z
      change r ∈ orbitFive σ z at hrmem
      simp only [orbitFive, Finset.mem_insert, Finset.mem_singleton] at hrmem
      have hrmove : σ r ≠ r := by
        rcases hrmem with hr | hr | hr | hr | hr
        · simpa [r, hr] using hzmove
        · rw [hr]
          simpa [act] using hact_moved hzmove (1 : Fin 5)
        · rw [hr]
          simpa [act] using hact_moved hzmove (2 : Fin 5)
        · rw [hr]
          simpa [act] using hact_moved hzmove (3 : Fin 5)
        · rw [hr]
          simpa [act] using hact_moved hzmove (4 : Fin 5)
      have hrrep : orbitFiveRep σ r = r := by
        rcases hrmem with hr | hr | hr | hr | hr
        · simpa [hr]
        · calc
            orbitFiveRep σ r = orbitFiveRep σ z := by
              rw [hr, orbitFiveRep_apply σ hσ]
            _ = r := rfl
        · calc
            orbitFiveRep σ r = orbitFiveRep σ z := by
              rw [hr, orbitFiveRep_iterate_two σ hσ]
            _ = r := rfl
        · calc
            orbitFiveRep σ r = orbitFiveRep σ z := by
              rw [hr, orbitFiveRep_iterate_three σ hσ]
            _ = r := rfl
        · calc
            orbitFiveRep σ r = orbitFiveRep σ z := by
              rw [hr, orbitFiveRep_iterate_four σ hσ]
            _ = r := rfl
      have hrin : r ∈ reps := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrmove, hrrep⟩
      rcases hrmem with hr | hr | hr | hr | hr
      · refine ⟨(r, (0 : Fin 5)), Finset.mem_product.mpr
          ⟨hrin, Finset.mem_univ _⟩, ?_⟩
        change act (r, (0 : Fin 5)) = z
        rw [hact_zero, hr]
      · refine ⟨(r, (4 : Fin 5)), Finset.mem_product.mpr
          ⟨hrin, Finset.mem_univ _⟩, ?_⟩
        change act (r, (4 : Fin 5)) = z
        rw [hact_four, hr, hσ]
      · refine ⟨(r, (3 : Fin 5)), Finset.mem_product.mpr
          ⟨hrin, Finset.mem_univ _⟩, ?_⟩
        change act (r, (3 : Fin 5)) = z
        rw [hact_three, hr, hσ]
      · refine ⟨(r, (2 : Fin 5)), Finset.mem_product.mpr
          ⟨hrin, Finset.mem_univ _⟩, ?_⟩
        change act (r, (2 : Fin 5)) = z
        rw [hact_two, hr, hσ]
      · refine ⟨(r, (1 : Fin 5)), Finset.mem_product.mpr
          ⟨hrin, Finset.mem_univ _⟩, ?_⟩
        change act (r, (1 : Fin 5)) = z
        rw [hact_one, hr, hσ]
    · rintro ⟨x, i⟩ hz
      fin_cases i
      · simp [act]
      · simp [act, hw]
      · simp [act, hw]
      · simp [act, hw]
      · simp [act, hw]
  have hproduct :
      (∑ z ∈ reps ×ˢ (Finset.univ : Finset (Fin 5)), w (act z)) =
        5 * ∑ x ∈ reps, w x := by
    rw [Finset.sum_product]
    calc
      (∑ x ∈ reps, ∑ i : Fin 5, w (act (x, i))) =
          ∑ x ∈ reps, 5 * w x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
          Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp [act, hw]
        ring
      _ = 5 * ∑ x ∈ reps, w x := by rw [Finset.mul_sum]
  rw [hsplit, horbit, hproduct]

private abbrev E5 (p : ℕ) [NeZero p] [Fact p.Prime] :=
  FiniteField.Extension (ZMod p) p 5

theorem quintic_frob_order_five
    (p : ℕ) [NeZero p] [Fact p.Prime] (x : E5 p) :
    let σ : E5 p ≃ₐ[ZMod p] E5 p :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    σ (σ (σ (σ (σ x)))) = x := by
  letI : Fintype (E5 p) := Fintype.ofFinite _
  dsimp only
  change ((((x ^ Fintype.card (ZMod p)) ^ Fintype.card (ZMod p)) ^
      Fintype.card (ZMod p)) ^ Fintype.card (ZMod p)) ^
      Fintype.card (ZMod p) = x
  rw [ZMod.card p, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
  have hcard : Fintype.card (E5 p) = p ^ 5 := by
    rw [Fintype.card_eq_nat_card,
      FiniteField.natCard_extension, Nat.card_zmod]
  rw [show p * (p * (p * (p * p))) = p ^ 5 by ring, ← hcard]
  exact FiniteField.pow_card x

theorem quintic_frob_fixed_iff
    (p : ℕ) [NeZero p] [Fact p.Prime] (x : E5 p) :
    let σ : E5 p ≃ₐ[ZMod p] E5 p :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    σ x = x ↔ ∃ a : ZMod p, algebraMap (ZMod p) (E5 p) a = x := by
  letI : Fintype (E5 p) := Fintype.ofFinite _
  dsimp only
  constructor
  · intro hx
    apply (IsGalois.mem_range_algebraMap_iff_fixed x).2
    intro g
    obtain ⟨i, rfl⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
        (ZMod p) (E5 p)).2 g
    let σ : E5 p ≃ₐ[ZMod p] E5 p :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    have hall : ∀ n : ℕ, (σ ^ n) x = x := by
      intro n
      induction n with
      | zero => simp
      | succ n hn =>
          rw [pow_succ']
          change σ ((σ ^ n) x) = x
          rw [hn, hx]
    exact hall i.1
  · rintro ⟨a, rfl⟩
    simp

theorem quintic_norm_frob
    (p : ℕ) [NeZero p] [Fact p.Prime] (x : E5 p) :
    let σ : E5 p ≃ₐ[ZMod p] E5 p :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    Algebra.norm (ZMod p) (σ x) = Algebra.norm (ZMod p) x := by
  dsimp only
  exact Algebra.norm_eq_of_algEquiv
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (E5 p)) x

theorem quintic_rootMultisetWeight_frob
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (x : E5 p) :
    let χE := finiteFieldNormLiftMulChar (ZMod p) (E5 p) χ
    let σ : E5 p ≃ₐ[ZMod p] E5 p :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    (∏ r ∈ R.toFinset,
        (χE ^ R.count r) (σ x - algebraMap (ZMod p) (E5 p) r)) =
      ∏ r ∈ R.toFinset,
        (χE ^ R.count r) (x - algebraMap (ZMod p) (E5 p) r) := by
  dsimp only
  let σ : E5 p ≃ₐ[ZMod p] E5 p :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  apply Finset.prod_congr rfl
  intro r hr
  rw [show σ x - algebraMap (ZMod p) (E5 p) r =
      σ (x - algebraMap (ZMod p) (E5 p) r) by simp]
  rw [← map_pow (finiteFieldNormLiftMulChar (ZMod p) (E5 p)) χ
    (R.count r)]
  rw [finiteFieldNormLiftMulChar_apply]
  rw [show Algebra.norm (ZMod p)
      (σ (x - algebraMap (ZMod p) (E5 p) r)) =
      Algebra.norm (ZMod p)
        (x - algebraMap (ZMod p) (E5 p) r) by
    exact quintic_norm_frob p _]
  exact (finiteFieldNormLiftMulChar_apply (ZMod p) (E5 p)
    (χ ^ R.count r) (x - algebraMap (ZMod p) (E5 p) r)).symm

theorem quintic_rootMultisetWeight_algebraMap
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (a : ZMod p) :
    let χE := finiteFieldNormLiftMulChar (ZMod p) (E5 p) χ
    (∏ r ∈ R.toFinset,
        (χE ^ R.count r)
          (algebraMap (ZMod p) (E5 p) a -
            algebraMap (ZMod p) (E5 p) r)) =
      (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 5 := by
  dsimp only
  have hfinrank : Module.finrank (ZMod p) (E5 p) = 5 := by
    refine Nat.pow_right_injective (Finite.one_lt_card :
      2 ≤ Nat.card (ZMod p)) ?_
    simp only [← Module.natCard_eq_pow_finrank,
      FiniteField.natCard_extension]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro r hr
  rw [← map_sub]
  rw [← map_pow (finiteFieldNormLiftMulChar (ZMod p) (E5 p)) χ
    (R.count r)]
  rw [finiteFieldNormLiftMulChar_apply, Algebra.norm_algebraMap, hfinrank]
  exact map_pow (χ ^ R.count r) (a - r) 5

theorem quintic_rootMultisetCorrelation_orbit_decomposition
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    let E := E5 p
    letI : Fintype E := Fintype.ofFinite E
    letI : DecidableEq E := Classical.decEq E
    letI : LinearOrder E := Equiv.linearOrder (Fintype.equivFin E)
    let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
    let σ : E ≃ₐ[ZMod p] E :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    finiteFieldRootMultisetCorrelation (ZMod p) E χE R =
      ∑ a : ZMod p,
          (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 5 +
        5 * ∑ x ∈ Finset.univ.filter
          (fun x : E => σ x ≠ x ∧ orbitFiveRep σ.toEquiv x = x),
          ∏ r ∈ R.toFinset,
            (χE ^ R.count r) (x - algebraMap (ZMod p) E r) := by
  dsimp only
  let E := E5 p
  letI : Fintype E := Fintype.ofFinite E
  letI : DecidableEq E := Classical.decEq E
  letI : LinearOrder E := Equiv.linearOrder (Fintype.equivFin E)
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let σ : E ≃ₐ[ZMod p] E :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  let w : E → ℂ := fun x =>
    ∏ r ∈ R.toFinset,
      (χE ^ R.count r) (x - algebraMap (ZMod p) E r)
  have horbit :
      (∑ x : E, w x) =
        ∑ x ∈ Finset.univ.filter (fun x : E => σ x = x), w x +
          5 * ∑ x ∈ Finset.univ.filter
            (fun x : E => σ x ≠ x ∧ orbitFiveRep σ.toEquiv x = x), w x := by
    apply sum_order_five σ.toEquiv
    · intro x
      exact quintic_frob_order_five p x
    · intro x
      exact quintic_rootMultisetWeight_frob p χ R x
  have hfixed :
      (∑ x ∈ Finset.univ.filter (fun x : E => σ x = x), w x) =
        ∑ a : ZMod p,
          (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 5 := by
    symm
    refine Finset.sum_bij
      (fun a (_ha : a ∈ (Finset.univ : Finset (ZMod p))) =>
        algebraMap (ZMod p) E a) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [σ]
    · intro a₁ ha₁ a₂ ha₂ h
      exact (algebraMap (ZMod p) E).injective h
    · intro x hx
      have hxfix : σ x = x := (Finset.mem_filter.mp hx).2
      obtain ⟨a, ha⟩ := (quintic_frob_fixed_iff p x).mp (by
        simpa [σ] using hxfix)
      exact ⟨a, Finset.mem_univ a, ha⟩
    · intro a ha
      change (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 5 =
        w (algebraMap (ZMod p) E a)
      exact (quintic_rootMultisetWeight_algebraMap p χ R a).symm
  unfold finiteFieldRootMultisetCorrelation
  change (∑ x : E, w x) = _
  rw [horbit, hfixed]

theorem completeHomogeneousFive_integral
    {α : Type*} [DecidableEq α] (s : Finset α) (u : α → ℂ)
    (hu : ∀ x ∈ s, IsIntegral ℤ (u x)) :
    IsIntegral ℤ
      (((∑ x ∈ s, u x) ^ 5 +
          10 * (∑ x ∈ s, u x) ^ 3 * (∑ x ∈ s, u x ^ 2) +
          15 * (∑ x ∈ s, u x) * (∑ x ∈ s, u x ^ 2) ^ 2 +
          20 * (∑ x ∈ s, u x) ^ 2 * (∑ x ∈ s, u x ^ 3) +
          20 * (∑ x ∈ s, u x ^ 2) * (∑ x ∈ s, u x ^ 3) +
          30 * (∑ x ∈ s, u x) * (∑ x ∈ s, u x ^ 4) +
          24 * (∑ x ∈ s, u x ^ 5)) / 120) := by
  induction s using Finset.induction_on with
  | empty =>
      norm_num
      exact isIntegral_zero
  | @insert a s ha ih =>
      have hi := ih (fun x hx => hu x (Finset.mem_insert_of_mem hx))
      have hfour := completeHomogeneousFour_integral s u
        (fun x hx => hu x (Finset.mem_insert_of_mem hx))
      have hthree := completeHomogeneousThree_integral s u
        (fun x hx => hu x (Finset.mem_insert_of_mem hx))
      have htwo := completeHomogeneousTwo_integral s u
        (fun x hx => hu x (Finset.mem_insert_of_mem hx))
      have hua := hu a (Finset.mem_insert_self a s)
      have hsum : IsIntegral ℤ (∑ x ∈ s, u x) :=
        IsIntegral.sum (fun x => u x)
          (fun x hx => hu x (Finset.mem_insert_of_mem hx))
      have hformula :
          (((∑ x ∈ insert a s, u x) ^ 5 +
              10 * (∑ x ∈ insert a s, u x) ^ 3 *
                (∑ x ∈ insert a s, u x ^ 2) +
              15 * (∑ x ∈ insert a s, u x) *
                (∑ x ∈ insert a s, u x ^ 2) ^ 2 +
              20 * (∑ x ∈ insert a s, u x) ^ 2 *
                (∑ x ∈ insert a s, u x ^ 3) +
              20 * (∑ x ∈ insert a s, u x ^ 2) *
                (∑ x ∈ insert a s, u x ^ 3) +
              30 * (∑ x ∈ insert a s, u x) *
                (∑ x ∈ insert a s, u x ^ 4) +
              24 * (∑ x ∈ insert a s, u x ^ 5)) / 120) =
            (((∑ x ∈ s, u x) ^ 5 +
                10 * (∑ x ∈ s, u x) ^ 3 * (∑ x ∈ s, u x ^ 2) +
                15 * (∑ x ∈ s, u x) * (∑ x ∈ s, u x ^ 2) ^ 2 +
                20 * (∑ x ∈ s, u x) ^ 2 * (∑ x ∈ s, u x ^ 3) +
                20 * (∑ x ∈ s, u x ^ 2) * (∑ x ∈ s, u x ^ 3) +
                30 * (∑ x ∈ s, u x) * (∑ x ∈ s, u x ^ 4) +
                24 * (∑ x ∈ s, u x ^ 5)) / 120) +
              u a * (((∑ x ∈ s, u x) ^ 4 +
                6 * (∑ x ∈ s, u x) ^ 2 * (∑ x ∈ s, u x ^ 2) +
                3 * (∑ x ∈ s, u x ^ 2) ^ 2 +
                8 * (∑ x ∈ s, u x) * (∑ x ∈ s, u x ^ 3) +
                6 * (∑ x ∈ s, u x ^ 4)) / 24) +
              u a ^ 2 * (((∑ x ∈ s, u x) ^ 3 +
                3 * (∑ x ∈ s, u x) * (∑ x ∈ s, u x ^ 2) +
                2 * (∑ x ∈ s, u x ^ 3)) / 6) +
              u a ^ 3 * (((∑ x ∈ s, u x) ^ 2 +
                ∑ x ∈ s, u x ^ 2) / 2) +
              u a ^ 4 * (∑ x ∈ s, u x) + u a ^ 5 := by
        simp only [Finset.sum_insert ha]
        ring
      rw [hformula]
      exact ((((hi.add (hua.mul hfour)).add ((hua.pow 2).mul hthree)).add
        ((hua.pow 3).mul htwo)).add ((hua.pow 4).mul hsum)).add (hua.pow 5)

theorem primeRootMultisetFifthNewtonNumerator_integral
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    IsIntegral ℤ
      ((primeRootMultisetExtensionCorrelation p χ R 0 ^ 5 +
        10 * primeRootMultisetExtensionCorrelation p χ R 0 ^ 3 *
          primeRootMultisetExtensionCorrelation p χ R 1 +
        15 * primeRootMultisetExtensionCorrelation p χ R 0 *
          primeRootMultisetExtensionCorrelation p χ R 1 ^ 2 +
        20 * primeRootMultisetExtensionCorrelation p χ R 0 ^ 2 *
          primeRootMultisetExtensionCorrelation p χ R 2 +
        20 * primeRootMultisetExtensionCorrelation p χ R 1 *
          primeRootMultisetExtensionCorrelation p χ R 2 +
        30 * primeRootMultisetExtensionCorrelation p χ R 0 *
          primeRootMultisetExtensionCorrelation p χ R 3 +
        24 * primeRootMultisetExtensionCorrelation p χ R 4) / 120) := by
  let C : ℕ → ℂ := primeRootMultisetExtensionCorrelation p χ R
  let u : ZMod p → ℂ := fun a =>
    ∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)
  let A : ℂ := ∑ a : ZMod p, u a
  let D₂ : ℂ := ∑ a : ZMod p, u a ^ 2
  let D₃ : ℂ := ∑ a : ZMod p, u a ^ 3
  let D₄ : ℂ := ∑ a : ZMod p, u a ^ 4
  let D₅ : ℂ := ∑ a : ZMod p, u a ^ 5
  let H₂ : ℂ := (A ^ 2 + D₂) / 2
  let H₃ : ℂ := (A ^ 3 + 3 * A * D₂ + 2 * D₃) / 6
  let H₄ : ℂ :=
    (A ^ 4 + 6 * A ^ 2 * D₂ + 3 * D₂ ^ 2 + 8 * A * D₃ + 6 * D₄) / 24
  let H₅ : ℂ :=
    (A ^ 5 + 10 * A ^ 3 * D₂ + 15 * A * D₂ ^ 2 +
      20 * A ^ 2 * D₃ + 20 * D₂ * D₃ + 30 * A * D₄ + 24 * D₅) / 120
  let N₄ : ℂ :=
    (C 0 ^ 4 + 6 * C 0 ^ 2 * C 1 + 3 * C 1 ^ 2 +
      8 * C 0 * C 2 + 6 * C 3) / 24
  let Y : ℂ := (C 1 - D₂) / 2
  let X : ℂ := (C 2 - D₃) / 3
  let V : ℂ := N₄ - H₄ - H₂ * Y - A * X
  let E := E5 p
  letI : Fintype E := Fintype.ofFinite E
  letI : DecidableEq E := Classical.decEq E
  letI : LinearOrder E := Equiv.linearOrder (Fintype.equivFin E)
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let σ : E ≃ₐ[ZMod p] E :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  let w : E → ℂ := fun x =>
    ∏ r ∈ R.toFinset,
      (χE ^ R.count r) (x - algebraMap (ZMod p) E r)
  let W : ℂ :=
    ∑ x ∈ Finset.univ.filter
      (fun x : E => σ x ≠ x ∧ orbitFiveRep σ.toEquiv x = x), w x
  have hzero : C 0 = A := by rfl
  have hone : C 1 = D₂ + 2 * Y := by
    unfold Y
    ring
  have htwo : C 2 = D₃ + 3 * X := by
    unfold X
    ring
  have hfour : C 4 = D₅ + 5 * W := by
    change finiteFieldRootMultisetCorrelation (ZMod p) E χE R =
      D₅ + 5 * W
    exact quintic_rootMultisetCorrelation_orbit_decomposition p χ R
  have hformula :
      ((C 0 ^ 5 + 10 * C 0 ^ 3 * C 1 + 15 * C 0 * C 1 ^ 2 +
          20 * C 0 ^ 2 * C 2 + 20 * C 1 * C 2 + 30 * C 0 * C 3 +
          24 * C 4) / 120) =
        H₅ + H₃ * Y + (H₂ + Y) * X + A * V + W := by
    unfold V N₄ H₂ H₃ H₄ H₅
    rw [hzero, hone, htwo, hfour]
    ring
  have hu (a : ZMod p) : IsIntegral ℤ (u a) := by
    unfold u
    exact IsIntegral.prod (fun r : ZMod p =>
      (χ ^ R.count r) (a - r))
      (fun r _hr => isIntegral_finiteFieldMulChar_apply
        (χ ^ R.count r) (a - r))
  have hA : IsIntegral ℤ A := by
    unfold A
    exact IsIntegral.sum (fun a : ZMod p => u a) (fun a _ha => hu a)
  have hH₂ : IsIntegral ℤ H₂ := by
    unfold H₂ A D₂
    exact completeHomogeneousTwo_integral Finset.univ u
      (fun a _ha => hu a)
  have hH₃ : IsIntegral ℤ H₃ := by
    unfold H₃ A D₂ D₃
    exact completeHomogeneousThree_integral Finset.univ u
      (fun a _ha => hu a)
  have hH₄ : IsIntegral ℤ H₄ := by
    unfold H₄ A D₂ D₃ D₄
    exact completeHomogeneousFour_integral Finset.univ u
      (fun a _ha => hu a)
  have hH₅ : IsIntegral ℤ H₅ := by
    unfold H₅ A D₂ D₃ D₄ D₅
    exact completeHomogeneousFive_integral Finset.univ u
      (fun a _ha => hu a)
  have hY : IsIntegral ℤ Y := by
    have hn := primeRootMultisetSecondNewtonNumerator_integral p χ R
    have hnformula : ((C 0 ^ 2 + C 1) / 2) = H₂ + Y := by
      rw [hzero, hone]
      unfold H₂
      ring
    change IsIntegral ℤ ((C 0 ^ 2 + C 1) / 2) at hn
    rw [hnformula] at hn
    convert hn.sub hH₂ using 1
    ring
  have hX : IsIntegral ℤ X := by
    have hn := primeRootMultisetThirdNewtonNumerator_integral p χ R
    have hnformula :
        ((C 0 ^ 3 + 3 * C 0 * C 1 + 2 * C 2) / 6) =
          H₃ + A * Y + X := by
      rw [hzero, hone, htwo]
      unfold H₃
      ring
    change IsIntegral ℤ
      ((C 0 ^ 3 + 3 * C 0 * C 1 + 2 * C 2) / 6) at hn
    rw [hnformula] at hn
    convert (hn.sub hH₃).sub (hA.mul hY) using 1
    ring
  have hV : IsIntegral ℤ V := by
    have hn := primeRootMultisetFourthNewtonNumerator_integral p χ R
    change IsIntegral ℤ N₄ at hn
    unfold V
    exact (((hn.sub hH₄).sub (hH₂.mul hY)).sub (hA.mul hX))
  have hW : IsIntegral ℤ W := by
    unfold W w
    exact IsIntegral.sum
      (fun x : E => ∏ r ∈ R.toFinset,
        (χE ^ R.count r) (x - algebraMap (ZMod p) E r))
      (fun x _hx => IsIntegral.prod
        (fun r : ZMod p =>
          (χE ^ R.count r) (x - algebraMap (ZMod p) E r))
        (fun r _hr => isIntegral_finiteFieldMulChar_apply
          (χE ^ R.count r) (x - algebraMap (ZMod p) E r)))
  change IsIntegral ℤ
    ((C 0 ^ 5 + 10 * C 0 ^ 3 * C 1 + 15 * C 0 * C 1 ^ 2 +
      20 * C 0 ^ 2 * C 2 + 20 * C 1 * C 2 + 30 * C 0 * C 3 +
      24 * C 4) / 120)
  rw [hformula]
  exact (((hH₅.add (hH₃.mul hY)).add ((hH₂.add hY).mul hX)).add
    (hA.mul hV)).add hW

theorem complexNewtonElementary_five (v : ℕ → ℂ) :
    complexNewtonElementary v 5 =
      (v 1 ^ 5 - 10 * v 1 ^ 3 * v 2 + 15 * v 1 * v 2 ^ 2 +
        20 * v 1 ^ 2 * v 3 - 20 * v 2 * v 3 - 30 * v 1 * v 4 +
        24 * v 5) / 120 := by
  change complexNewtonElementary v (4 + 1) = _
  rw [complexNewtonElementary_succ]
  have had : {a ∈ Finset.antidiagonal 5 | a.1 < 5} =
      {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1)} := by decide
  norm_num only at had ⊢
  rw [had]
  norm_num [Finset.sum_insert]
  rw [complexNewtonElementary_one, complexNewtonElementary_two,
    complexNewtonElementary_three, complexNewtonElementary_four]
  norm_num [Finset.sum_insert, complexNewtonElementary]
  ring

theorem primeRootMultisetNewtonElementary_five_integral
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    IsIntegral ℤ (primeRootMultisetNewtonElementary p χ R 5) := by
  have h := primeRootMultisetFifthNewtonNumerator_integral p χ R
  have hneg := h.neg
  convert hneg using 1
  rw [primeRootMultisetNewtonElementary, complexNewtonElementary_five]
  simp only [primeRootMultisetNewtonPowerSum]
  ring

/-- The first six Newton elementary coefficients are unconditional. -/
theorem primeRootMultisetNewtonElementary_integral_of_le_five
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (j : ℕ) (hj : j ≤ 5) :
    IsIntegral ℤ (primeRootMultisetNewtonElementary p χ R j) := by
  interval_cases j
  · exact primeRootMultisetNewtonElementary_zero_integral p χ R
  · exact primeRootMultisetNewtonElementary_one_integral p χ R
  · exact primeRootMultisetNewtonElementary_two_integral p χ R
  · exact primeRootMultisetNewtonElementary_three_integral p χ R
  · exact primeRootMultisetNewtonElementary_four_integral p χ R
  · exact primeRootMultisetNewtonElementary_five_integral p χ R

end

end Tao2026
