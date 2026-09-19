import Tao2026.BurgessWeilPrimeKummerNewtonLowDegreeIntegrality

/-!
# Unconditional cubic higher-root Newton integrality

The cubic extension correlation is decomposed into Frobenius orbits of sizes
one and three. Its fixed contribution is the cube of each base-field Kummer
weight, while every non-fixed orbit contributes three times one algebraic
integer. Together with the quadratic-orbit decomposition, this is the
degree-three truncation of the Euler product for the literal correlation
sequence.

An induction proves directly that the degree-three complete homogeneous
expression in any finite family of algebraic integers is integral. Combining
the degree-one, degree-two, and degree-three orbit terms gives unconditional
integrality of the third Newton elementary coefficient.
-/

namespace Tao2026

open Finset
open scoped BigOperators

noncomputable section

private def orbitThree {α : Type*} [DecidableEq α]
    (σ : α ≃ α) (x : α) : Finset α :=
  {x, σ x, σ (σ x)}

private def orbitThreeRep {α : Type*} [LinearOrder α]
    (σ : α ≃ α) (x : α) : α :=
  (orbitThree σ x).min' (by simp [orbitThree])

private theorem orbitThree_apply
    {α : Type*} [LinearOrder α] (σ : α ≃ α)
    (hσ : ∀ x, σ (σ (σ x)) = x) (x : α) :
    orbitThree σ (σ x) = orbitThree σ x := by
  ext y
  simp only [orbitThree, Finset.mem_insert, Finset.mem_singleton]
  rw [hσ]
  aesop

private theorem orbitThree_apply_apply
    {α : Type*} [LinearOrder α] (σ : α ≃ α)
    (hσ : ∀ x, σ (σ (σ x)) = x) (x : α) :
    orbitThree σ (σ (σ x)) = orbitThree σ x := by
  rw [orbitThree_apply σ hσ, orbitThree_apply σ hσ]

private theorem orbitThreeRep_apply
    {α : Type*} [LinearOrder α] (σ : α ≃ α)
    (hσ : ∀ x, σ (σ (σ x)) = x) (x : α) :
    orbitThreeRep σ (σ x) = orbitThreeRep σ x := by
  unfold orbitThreeRep
  apply (Finset.min'_eq_iff (orbitThree σ (σ x)) _ _).2
  constructor
  · rw [orbitThree_apply σ hσ]
    exact Finset.min'_mem _ _
  · intro b hb
    apply Finset.min'_le
    rw [← orbitThree_apply σ hσ]
    exact hb

private theorem orbitThreeRep_apply_apply
    {α : Type*} [LinearOrder α] (σ : α ≃ α)
    (hσ : ∀ x, σ (σ (σ x)) = x) (x : α) :
    orbitThreeRep σ (σ (σ x)) = orbitThreeRep σ x := by
  rw [orbitThreeRep_apply σ hσ, orbitThreeRep_apply σ hσ]

private theorem orbitThreeRep_mem
    {α : Type*} [LinearOrder α] (σ : α ≃ α) (x : α) :
    orbitThreeRep σ x ∈ orbitThree σ x := by
  exact Finset.min'_mem _ _

theorem sum_order_three
    {α R : Type*} [Fintype α] [LinearOrder α]
    [CommRing R] (σ : α ≃ α) (hσ : ∀ x, σ (σ (σ x)) = x)
    (w : α → R) (hw : ∀ x, w (σ x) = w x) :
    ∑ x, w x =
      ∑ x ∈ Finset.univ.filter (fun x => σ x = x), w x +
        3 * ∑ x ∈ Finset.univ.filter
          (fun x => σ x ≠ x ∧ orbitThreeRep σ x = x), w x := by
  let fixed := Finset.univ.filter (fun x => σ x = x)
  let moved := Finset.univ.filter (fun x => σ x ≠ x)
  let reps := Finset.univ.filter
    (fun x => σ x ≠ x ∧ orbitThreeRep σ x = x)
  let act : α × Fin 3 → α := fun z =>
    match z.2.1 with
    | 0 => z.1
    | 1 => σ z.1
    | _ => σ (σ z.1)
  have hsplit :
      (∑ x, w x) = (∑ x ∈ fixed, w x) + ∑ x ∈ moved, w x := by
    symm
    simpa [fixed, moved] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => σ x = x) w)
  have hact_zero (x : α) : act (x, (0 : Fin 3)) = x := by rfl
  have hact_one (x : α) : act (x, (1 : Fin 3)) = σ x := by rfl
  have hact_two (x : α) : act (x, (2 : Fin 3)) = σ (σ x) := by rfl
  have hrep_act (x : α) (i : Fin 3) :
      orbitThreeRep σ (act (x, i)) = orbitThreeRep σ x := by
    fin_cases i
    · simp [act]
    · simp [act, orbitThreeRep_apply σ hσ]
    · simp [act, orbitThreeRep_apply_apply σ hσ]
  have hact_moved {x : α} (hx : σ x ≠ x) (i : Fin 3) :
      σ (act (x, i)) ≠ act (x, i) := by
    fin_cases i
    · simpa [act] using hx
    · simp only [act]
      intro h
      exact hx (σ.injective h)
    · simp only [act, hσ]
      intro h
      exact hx (by simpa [hσ] using congrArg σ h)
  have horbit :
      (∑ x ∈ moved, w x) =
        ∑ z ∈ reps ×ˢ (Finset.univ : Finset (Fin 3)), w (act z) := by
    symm
    refine Finset.sum_bij (fun z _hz => act z) ?_ ?_ ?_ ?_
    · intro z hz
      have hzrep : z.1 ∈ reps := (Finset.mem_product.mp hz).1
      have hzmove : σ z.1 ≠ z.1 := (Finset.mem_filter.mp hzrep).2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact_moved hzmove z.2⟩
    · rintro ⟨a, i⟩ hz₁ ⟨b, j⟩ hz₂ heq
      change act (a, i) = act (b, j) at heq
      have hz₁rep : orbitThreeRep σ a = a :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hz₁).1).2.2
      have hz₂rep : orbitThreeRep σ b = b :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hz₂).1).2.2
      have hfst : a = b := by
        rw [← hz₁rep, ← hz₂rep, ← hrep_act a i,
          ← hrep_act b j, heq]
      have hmove : σ a ≠ a :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hz₁).1).2.1
      subst b
      apply Prod.ext
      · rfl
      fin_cases i <;> fin_cases j
      all_goals simp only [act] at heq
      all_goals try rfl
      · exact (hmove heq.symm).elim
      · exact (hmove (by simpa [hσ] using congrArg σ heq)).elim
      · exact (hmove heq).elim
      · exact (hmove (σ.injective heq).symm).elim
      · exact (hmove (by simpa [hσ] using (congrArg σ heq).symm)).elim
      · exact (hmove (σ.injective heq)).elim
    · intro z hz
      have hzmove : σ z ≠ z := (Finset.mem_filter.mp hz).2
      let r := orbitThreeRep σ z
      have hrmem := orbitThreeRep_mem σ z
      change r ∈ orbitThree σ z at hrmem
      simp only [orbitThree, Finset.mem_insert, Finset.mem_singleton] at hrmem
      have hrmove : σ r ≠ r := by
        rcases hrmem with hr | hr | hr
        · simpa [r, hr] using hzmove
        · intro h
          apply hzmove
          rw [hr] at h
          exact σ.injective h
        · intro h
          apply hzmove
          rw [hr, hσ] at h
          simpa [hσ] using congrArg σ h
      have hrrep : orbitThreeRep σ r = r := by
        rcases hrmem with hr | hr | hr
        · simpa [hr]
        · calc
            orbitThreeRep σ r = orbitThreeRep σ z := by
              rw [hr, orbitThreeRep_apply σ hσ]
            _ = r := rfl
        · calc
            orbitThreeRep σ r = orbitThreeRep σ z := by
              rw [hr, orbitThreeRep_apply_apply σ hσ]
            _ = r := rfl
      have hrin : r ∈ reps := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrmove, hrrep⟩
      rcases hrmem with hr | hr | hr
      · refine ⟨(r, (0 : Fin 3)), Finset.mem_product.mpr
          ⟨hrin, Finset.mem_univ _⟩, ?_⟩
        change act (r, (0 : Fin 3)) = z
        rw [hact_zero, hr]
      · refine ⟨(r, (2 : Fin 3)), Finset.mem_product.mpr
          ⟨hrin, Finset.mem_univ _⟩, ?_⟩
        change act (r, (2 : Fin 3)) = z
        rw [hact_two, hr, hσ]
      · refine ⟨(r, (1 : Fin 3)), Finset.mem_product.mpr
          ⟨hrin, Finset.mem_univ _⟩, ?_⟩
        change act (r, (1 : Fin 3)) = z
        rw [hact_one, hr, hσ]
    · rintro ⟨x, i⟩ hz
      fin_cases i
      · simp [act]
      · simp [act, hw]
      · simp [act, hw]
  have hproduct :
      (∑ z ∈ reps ×ˢ (Finset.univ : Finset (Fin 3)), w (act z)) =
        3 * ∑ x ∈ reps, w x := by
    rw [Finset.sum_product]
    calc
      (∑ x ∈ reps, ∑ i : Fin 3, w (act (x, i))) =
          ∑ x ∈ reps, 3 * w x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp [act, hw]
        ring
      _ = 3 * ∑ x ∈ reps, w x := by rw [Finset.mul_sum]
  rw [hsplit, horbit, hproduct]

theorem cubic_frob_order_three
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (x : FiniteField.Extension (ZMod p) p 3) :
    let σ : (FiniteField.Extension (ZMod p) p 3) ≃ₐ[ZMod p]
        (FiniteField.Extension (ZMod p) p 3) :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    σ (σ (σ x)) = x := by
  letI : Fintype (FiniteField.Extension (ZMod p) p 3) := Fintype.ofFinite _
  dsimp only
  change ((x ^ Fintype.card (ZMod p)) ^ Fintype.card (ZMod p)) ^
      Fintype.card (ZMod p) = x
  rw [ZMod.card p, ← pow_mul, ← pow_mul]
  have hcard : Fintype.card (FiniteField.Extension (ZMod p) p 3) = p ^ 3 := by
    rw [Fintype.card_eq_nat_card,
      FiniteField.natCard_extension, Nat.card_zmod]
  rw [show p * (p * p) = p ^ 3 by ring, ← hcard]
  exact FiniteField.pow_card x

theorem cubic_frob_fixed_iff
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (x : FiniteField.Extension (ZMod p) p 3) :
    let σ : (FiniteField.Extension (ZMod p) p 3) ≃ₐ[ZMod p]
        (FiniteField.Extension (ZMod p) p 3) :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    σ x = x ↔ ∃ a : ZMod p,
      algebraMap (ZMod p) (FiniteField.Extension (ZMod p) p 3) a = x := by
  letI : Fintype (FiniteField.Extension (ZMod p) p 3) := Fintype.ofFinite _
  dsimp only
  constructor
  · intro hx
    apply (IsGalois.mem_range_algebraMap_iff_fixed x).2
    intro g
    obtain ⟨i, rfl⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
        (ZMod p) (FiniteField.Extension (ZMod p) p 3)).2 g
    have hfinrank : Module.finrank (ZMod p)
        (FiniteField.Extension (ZMod p) p 3) = 3 := by
      refine Nat.pow_right_injective (Finite.one_lt_card :
        2 ≤ Nat.card (ZMod p)) ?_
      simp only [← Module.natCard_eq_pow_finrank,
        FiniteField.natCard_extension]
    have hi : i.1 < 3 := by simpa [hfinrank] using i.2
    interval_cases hval : i.1
    · simp [hval]
    · simpa [hval] using hx
    · simp only [hval, pow_two]
      change (FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod p) (FiniteField.Extension (ZMod p) p 3))
          ((FiniteField.frobeniusAlgEquivOfAlgebraic
            (ZMod p) (FiniteField.Extension (ZMod p) p 3)) x) = x
      rw [hx]
      exact hx
  · rintro ⟨a, rfl⟩
    simp

theorem cubic_norm_frob
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (x : FiniteField.Extension (ZMod p) p 3) :
    let σ : (FiniteField.Extension (ZMod p) p 3) ≃ₐ[ZMod p]
        (FiniteField.Extension (ZMod p) p 3) :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    Algebra.norm (ZMod p) (σ x) = Algebra.norm (ZMod p) x := by
  letI : Fintype (FiniteField.Extension (ZMod p) p 3) := Fintype.ofFinite _
  dsimp only
  apply (algebraMap (ZMod p)
    (FiniteField.Extension (ZMod p) p 3)).injective
  rw [FiniteField.algebraMap_norm_eq_prod_pow,
    FiniteField.algebraMap_norm_eq_prod_pow]
  have hfinrank : Module.finrank (ZMod p)
      (FiniteField.Extension (ZMod p) p 3) = 3 := by
    refine Nat.pow_right_injective (Finite.one_lt_card :
      2 ≤ Nat.card (ZMod p)) ?_
    simp only [← Module.natCard_eq_pow_finrank,
      FiniteField.natCard_extension]
  rw [hfinrank]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    Nat.card_zmod, pow_zero, pow_one]
  have hpow : ((x ^ p) ^ p) ^ p = x := by
    rw [← pow_mul, ← pow_mul]
    have hcard : Fintype.card (FiniteField.Extension (ZMod p) p 3) = p ^ 3 := by
      rw [Fintype.card_eq_nat_card,
        FiniteField.natCard_extension, Nat.card_zmod]
    rw [show p * (p * p) = p ^ 3 by ring, ← hcard]
    exact FiniteField.pow_card x
  change (x ^ Fintype.card (ZMod p)) *
      (x ^ Fintype.card (ZMod p)) ^ p *
      (x ^ Fintype.card (ZMod p)) ^ p ^ 2 =
    x * x ^ p * x ^ p ^ 2
  rw [ZMod.card p]
  rw [show (x ^ p) ^ p ^ 2 = ((x ^ p) ^ p) ^ p by
    simp only [← pow_mul]; congr 1; ring]
  rw [hpow]
  ring

theorem cubic_rootMultisetWeight_frob
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (x : FiniteField.Extension (ZMod p) p 3) :
    let E := FiniteField.Extension (ZMod p) p 3
    let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
    let σ : E ≃ₐ[ZMod p] E :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    (∏ r ∈ R.toFinset,
        (χE ^ R.count r) (σ x - algebraMap (ZMod p) E r)) =
      ∏ r ∈ R.toFinset,
        (χE ^ R.count r) (x - algebraMap (ZMod p) E r) := by
  dsimp only
  let E := FiniteField.Extension (ZMod p) p 3
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let σ : E ≃ₐ[ZMod p] E :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  apply Finset.prod_congr rfl
  intro r hr
  rw [show σ x - algebraMap (ZMod p) E r =
      σ (x - algebraMap (ZMod p) E r) by simp]
  change ((finiteFieldNormLiftMulChar (ZMod p) E χ) ^ R.count r)
      (σ (x - algebraMap (ZMod p) E r)) = _
  rw [← map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ (R.count r)]
  rw [finiteFieldNormLiftMulChar_apply]
  rw [show Algebra.norm (ZMod p) (σ (x - algebraMap (ZMod p) E r)) =
      Algebra.norm (ZMod p) (x - algebraMap (ZMod p) E r) by
    exact cubic_norm_frob p _]
  exact (finiteFieldNormLiftMulChar_apply (ZMod p) E
    (χ ^ R.count r) (x - algebraMap (ZMod p) E r)).symm

theorem cubic_rootMultisetWeight_algebraMap
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (a : ZMod p) :
    let E := FiniteField.Extension (ZMod p) p 3
    let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
    (∏ r ∈ R.toFinset,
        (χE ^ R.count r)
          (algebraMap (ZMod p) E a - algebraMap (ZMod p) E r)) =
      (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 3 := by
  dsimp only
  let E := FiniteField.Extension (ZMod p) p 3
  have hfinrank : Module.finrank (ZMod p)
      (FiniteField.Extension (ZMod p) p 3) = 3 := by
    refine Nat.pow_right_injective (Finite.one_lt_card :
      2 ≤ Nat.card (ZMod p)) ?_
    simp only [← Module.natCard_eq_pow_finrank,
      FiniteField.natCard_extension]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro r hr
  rw [← map_sub]
  rw [← map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ (R.count r)]
  rw [finiteFieldNormLiftMulChar_apply, Algebra.norm_algebraMap, hfinrank]
  exact map_pow (χ ^ R.count r) (a - r) 3

theorem cubic_rootMultisetCorrelation_orbit_decomposition
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    let E := FiniteField.Extension (ZMod p) p 3
    letI : Fintype E := Fintype.ofFinite E
    letI : DecidableEq E := Classical.decEq E
    letI : LinearOrder E := Equiv.linearOrder (Fintype.equivFin E)
    let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
    let σ : E ≃ₐ[ZMod p] E :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    finiteFieldRootMultisetCorrelation (ZMod p) E χE R =
      ∑ a : ZMod p,
          (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 3 +
        3 * ∑ x ∈ Finset.univ.filter
          (fun x : E => σ x ≠ x ∧ orbitThreeRep σ.toEquiv x = x),
          ∏ r ∈ R.toFinset,
            (χE ^ R.count r) (x - algebraMap (ZMod p) E r) := by
  dsimp only
  let E := FiniteField.Extension (ZMod p) p 3
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
          3 * ∑ x ∈ Finset.univ.filter
            (fun x : E => σ x ≠ x ∧ orbitThreeRep σ.toEquiv x = x), w x := by
    apply sum_order_three σ.toEquiv
    · intro x
      exact cubic_frob_order_three p x
    · intro x
      exact cubic_rootMultisetWeight_frob p χ R x
  have hfixed :
      (∑ x ∈ Finset.univ.filter (fun x : E => σ x = x), w x) =
        ∑ a : ZMod p,
          (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 3 := by
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
      obtain ⟨a, ha⟩ := (cubic_frob_fixed_iff p x).mp (by
        simpa [σ] using hxfix)
      exact ⟨a, Finset.mem_univ a, ha⟩
    · intro a ha
      change (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 3 =
        w (algebraMap (ZMod p) E a)
      exact (cubic_rootMultisetWeight_algebraMap p χ R a).symm
  unfold finiteFieldRootMultisetCorrelation
  change (∑ x : E, w x) = _
  rw [horbit, hfixed]

theorem completeHomogeneousTwo_integral
    {α : Type*} [DecidableEq α] (s : Finset α) (u : α → ℂ)
    (hu : ∀ x ∈ s, IsIntegral ℤ (u x)) :
    IsIntegral ℤ
      (((∑ x ∈ s, u x) ^ 2 + ∑ x ∈ s, u x ^ 2) / 2) := by
  induction s using Finset.induction_on with
  | empty =>
      norm_num
      exact isIntegral_zero
  | @insert a s ha ih =>
      have hi := ih (fun x hx => hu x (Finset.mem_insert_of_mem hx))
      have hua := hu a (Finset.mem_insert_self a s)
      have hformula :
          (((∑ x ∈ insert a s, u x) ^ 2 +
              ∑ x ∈ insert a s, u x ^ 2) / 2) =
            (((∑ x ∈ s, u x) ^ 2 + ∑ x ∈ s, u x ^ 2) / 2) +
              u a * (∑ x ∈ s, u x) + u a ^ 2 := by
        simp only [Finset.sum_insert ha]
        ring
      rw [hformula]
      exact (hi.add (hua.mul (IsIntegral.sum (fun x => u x)
        (fun x hx => hu x (Finset.mem_insert_of_mem hx))))).add (hua.pow 2)

theorem completeHomogeneousThree_integral
    {α : Type*} [DecidableEq α] (s : Finset α) (u : α → ℂ)
    (hu : ∀ x ∈ s, IsIntegral ℤ (u x)) :
    IsIntegral ℤ
      (((∑ x ∈ s, u x) ^ 3 +
          3 * (∑ x ∈ s, u x) * (∑ x ∈ s, u x ^ 2) +
          2 * (∑ x ∈ s, u x ^ 3)) / 6) := by
  induction s using Finset.induction_on with
  | empty =>
      norm_num
      exact isIntegral_zero
  | @insert a s ha ih =>
      have hi := ih (fun x hx => hu x (Finset.mem_insert_of_mem hx))
      have htwo := completeHomogeneousTwo_integral s u
        (fun x hx => hu x (Finset.mem_insert_of_mem hx))
      have hua := hu a (Finset.mem_insert_self a s)
      have hsum : IsIntegral ℤ (∑ x ∈ s, u x) :=
        IsIntegral.sum (fun x => u x)
          (fun x hx => hu x (Finset.mem_insert_of_mem hx))
      have hformula :
          (((∑ x ∈ insert a s, u x) ^ 3 +
              3 * (∑ x ∈ insert a s, u x) *
                (∑ x ∈ insert a s, u x ^ 2) +
              2 * (∑ x ∈ insert a s, u x ^ 3)) / 6) =
            (((∑ x ∈ s, u x) ^ 3 +
                3 * (∑ x ∈ s, u x) * (∑ x ∈ s, u x ^ 2) +
                2 * (∑ x ∈ s, u x ^ 3)) / 6) +
              u a * (((∑ x ∈ s, u x) ^ 2 +
                ∑ x ∈ s, u x ^ 2) / 2) +
              u a ^ 2 * (∑ x ∈ s, u x) + u a ^ 3 := by
        simp only [Finset.sum_insert ha]
        ring
      rw [hformula]
      exact ((hi.add (hua.mul htwo)).add ((hua.pow 2).mul hsum)).add
        (hua.pow 3)

theorem primeRootMultisetThirdNewtonNumerator_integral
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    IsIntegral ℤ
      ((primeRootMultisetExtensionCorrelation p χ R 0 ^ 3 +
        3 * primeRootMultisetExtensionCorrelation p χ R 0 *
          primeRootMultisetExtensionCorrelation p χ R 1 +
        2 * primeRootMultisetExtensionCorrelation p χ R 2) / 6) := by
  let u : ZMod p → ℂ := fun a =>
    ∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)
  let A : ℂ := ∑ a : ZMod p, u a
  let D₂ : ℂ := ∑ a : ZMod p, u a ^ 2
  let D₃ : ℂ := ∑ a : ZMod p, u a ^ 3
  let E₂ := FiniteField.Extension (ZMod p) p 2
  letI : Fintype E₂ := Fintype.ofFinite E₂
  letI : DecidableEq E₂ := Classical.decEq E₂
  letI : LinearOrder E₂ := Equiv.linearOrder (Fintype.equivFin E₂)
  let χE₂ := finiteFieldNormLiftMulChar (ZMod p) E₂ χ
  let σ₂ : E₂ ≃ₐ[ZMod p] E₂ :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  let w₂ : E₂ → ℂ := fun x =>
    ∏ r ∈ R.toFinset,
      (χE₂ ^ R.count r) (x - algebraMap (ZMod p) E₂ r)
  let Y : ℂ :=
    ∑ x ∈ Finset.univ.filter (fun x : E₂ => x < σ₂ x), w₂ x
  let E₃ := FiniteField.Extension (ZMod p) p 3
  letI : Fintype E₃ := Fintype.ofFinite E₃
  letI : DecidableEq E₃ := Classical.decEq E₃
  letI : LinearOrder E₃ := Equiv.linearOrder (Fintype.equivFin E₃)
  let χE₃ := finiteFieldNormLiftMulChar (ZMod p) E₃ χ
  let σ₃ : E₃ ≃ₐ[ZMod p] E₃ :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  let w₃ : E₃ → ℂ := fun x =>
    ∏ r ∈ R.toFinset,
      (χE₃ ^ R.count r) (x - algebraMap (ZMod p) E₃ r)
  let X : ℂ :=
    ∑ x ∈ Finset.univ.filter
      (fun x : E₃ => σ₃ x ≠ x ∧ orbitThreeRep σ₃.toEquiv x = x), w₃ x
  have hzero : primeRootMultisetExtensionCorrelation p χ R 0 = A := by
    rfl
  have hone : primeRootMultisetExtensionCorrelation p χ R 1 = D₂ + 2 * Y := by
    change finiteFieldRootMultisetCorrelation (ZMod p) E₂ χE₂ R = D₂ + 2 * Y
    exact quadratic_rootMultisetCorrelation_orbit_decomposition p χ R
  have htwo : primeRootMultisetExtensionCorrelation p χ R 2 = D₃ + 3 * X := by
    change finiteFieldRootMultisetCorrelation (ZMod p) E₃ χE₃ R = D₃ + 3 * X
    exact cubic_rootMultisetCorrelation_orbit_decomposition p χ R
  have hformula :
      ((primeRootMultisetExtensionCorrelation p χ R 0 ^ 3 +
          3 * primeRootMultisetExtensionCorrelation p χ R 0 *
            primeRootMultisetExtensionCorrelation p χ R 1 +
          2 * primeRootMultisetExtensionCorrelation p χ R 2) / 6) =
        ((A ^ 3 + 3 * A * D₂ + 2 * D₃) / 6) + A * Y + X := by
    rw [hzero, hone, htwo]
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
  have hH₃ : IsIntegral ℤ ((A ^ 3 + 3 * A * D₂ + 2 * D₃) / 6) := by
    change IsIntegral ℤ
      (((∑ a ∈ (Finset.univ : Finset (ZMod p)), u a) ^ 3 +
        3 * (∑ a ∈ (Finset.univ : Finset (ZMod p)), u a) *
          (∑ a ∈ (Finset.univ : Finset (ZMod p)), u a ^ 2) +
        2 * (∑ a ∈ (Finset.univ : Finset (ZMod p)), u a ^ 3)) / 6)
    exact completeHomogeneousThree_integral Finset.univ u
      (fun a _ha => hu a)
  have hY : IsIntegral ℤ Y := by
    unfold Y w₂
    exact IsIntegral.sum
      (fun x : E₂ => ∏ r ∈ R.toFinset,
        (χE₂ ^ R.count r) (x - algebraMap (ZMod p) E₂ r))
      (fun x _hx => IsIntegral.prod
        (fun r : ZMod p =>
          (χE₂ ^ R.count r) (x - algebraMap (ZMod p) E₂ r))
        (fun r _hr => isIntegral_finiteFieldMulChar_apply
          (χE₂ ^ R.count r) (x - algebraMap (ZMod p) E₂ r)))
  have hX : IsIntegral ℤ X := by
    unfold X w₃
    exact IsIntegral.sum
      (fun x : E₃ => ∏ r ∈ R.toFinset,
        (χE₃ ^ R.count r) (x - algebraMap (ZMod p) E₃ r))
      (fun x _hx => IsIntegral.prod
        (fun r : ZMod p =>
          (χE₃ ^ R.count r) (x - algebraMap (ZMod p) E₃ r))
        (fun r _hr => isIntegral_finiteFieldMulChar_apply
          (χE₃ ^ R.count r) (x - algebraMap (ZMod p) E₃ r)))
  rw [hformula]
  exact (hH₃.add (hA.mul hY)).add hX

theorem complexNewtonElementary_two (v : ℕ → ℂ) :
    complexNewtonElementary v 2 = (v 1 ^ 2 - v 2) / 2 := by
  rw [show 2 = 1 + 1 by omega, complexNewtonElementary_succ]
  have had : {a ∈ Finset.antidiagonal 2 | a.1 < 2} =
      {(0, 2), (1, 1)} := by decide
  norm_num only at had ⊢
  rw [had]
  norm_num [Finset.sum_insert]
  rw [complexNewtonElementary_one]
  norm_num [Finset.sum_insert, complexNewtonElementary]
  ring

theorem complexNewtonElementary_three (v : ℕ → ℂ) :
    complexNewtonElementary v 3 =
      (v 1 ^ 3 - 3 * v 1 * v 2 + 2 * v 3) / 6 := by
  rw [show 3 = 2 + 1 by omega, complexNewtonElementary_succ]
  have had : {a ∈ Finset.antidiagonal 3 | a.1 < 3} =
      {(0, 3), (1, 2), (2, 1)} := by decide
  norm_num only at had ⊢
  rw [had]
  norm_num [Finset.sum_insert]
  rw [complexNewtonElementary_one, complexNewtonElementary_two]
  norm_num [Finset.sum_insert, complexNewtonElementary]
  ring

theorem primeRootMultisetNewtonElementary_three_integral
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    IsIntegral ℤ (primeRootMultisetNewtonElementary p χ R 3) := by
  have h := primeRootMultisetThirdNewtonNumerator_integral p χ R
  have hneg := h.neg
  convert hneg using 1
  rw [primeRootMultisetNewtonElementary, complexNewtonElementary_three]
  simp only [primeRootMultisetNewtonPowerSum]
  ring

/-- The first four Newton elementary coefficients are unconditional. -/
theorem primeRootMultisetNewtonElementary_integral_of_le_three
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (j : ℕ) (hj : j ≤ 3) :
    IsIntegral ℤ (primeRootMultisetNewtonElementary p χ R j) := by
  interval_cases j
  · exact primeRootMultisetNewtonElementary_zero_integral p χ R
  · exact primeRootMultisetNewtonElementary_one_integral p χ R
  · exact primeRootMultisetNewtonElementary_two_integral p χ R
  · exact primeRootMultisetNewtonElementary_three_integral p χ R

end

end Tao2026
