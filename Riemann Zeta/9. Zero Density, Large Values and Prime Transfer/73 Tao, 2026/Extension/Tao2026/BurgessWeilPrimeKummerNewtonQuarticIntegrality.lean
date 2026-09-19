import Tao2026.BurgessWeilPrimeKummerNewtonCubicIntegrality

/-!
# Unconditional quartic higher-root Newton integrality

The quartic extension correlation is split into Frobenius orbits of sizes
one, two, and four.  A finite-field embedding identifies the size-two locus
with the quadratic subfield; norm transitivity shows that its Kummer weight
is the square of the corresponding quadratic weight.  The remaining full
orbits contribute in multiples of four.

Together with direct finite-family proofs for the complete homogeneous
expressions through degree four, this yields unconditional integrality of
the fourth Newton elementary coefficient.
-/

namespace Tao2026

open Finset
open scoped BigOperators

noncomputable section

def orbitFour {α : Type*} [DecidableEq α]
    (σ : α ≃ α) (x : α) : Finset α :=
  {x, σ x, σ (σ x), σ (σ (σ x))}

def orbitFourRep {α : Type*} [LinearOrder α]
    (σ : α ≃ α) (x : α) : α :=
  (orbitFour σ x).min' (by simp [orbitFour])

private theorem orbitFour_apply
    {α : Type*} [LinearOrder α] (σ : α ≃ α)
    (hσ : ∀ x, σ (σ (σ (σ x))) = x) (x : α) :
    orbitFour σ (σ x) = orbitFour σ x := by
  ext y
  simp only [orbitFour, Finset.mem_insert, Finset.mem_singleton]
  rw [hσ]
  aesop

private theorem orbitFourRep_apply
    {α : Type*} [LinearOrder α] (σ : α ≃ α)
    (hσ : ∀ x, σ (σ (σ (σ x))) = x) (x : α) :
    orbitFourRep σ (σ x) = orbitFourRep σ x := by
  unfold orbitFourRep
  apply (Finset.min'_eq_iff (orbitFour σ (σ x)) _ _).2
  constructor
  · rw [orbitFour_apply σ hσ]
    exact Finset.min'_mem _ _
  · intro b hb
    apply Finset.min'_le
    rw [← orbitFour_apply σ hσ]
    exact hb

private theorem orbitFourRep_iterate_two
    {α : Type*} [LinearOrder α] (σ : α ≃ α)
    (hσ : ∀ x, σ (σ (σ (σ x))) = x) (x : α) :
    orbitFourRep σ (σ (σ x)) = orbitFourRep σ x := by
  rw [orbitFourRep_apply σ hσ, orbitFourRep_apply σ hσ]

private theorem orbitFourRep_iterate_three
    {α : Type*} [LinearOrder α] (σ : α ≃ α)
    (hσ : ∀ x, σ (σ (σ (σ x))) = x) (x : α) :
    orbitFourRep σ (σ (σ (σ x))) = orbitFourRep σ x := by
  rw [orbitFourRep_apply σ hσ, orbitFourRep_apply σ hσ,
    orbitFourRep_apply σ hσ]

private theorem orbitFourRep_mem
    {α : Type*} [LinearOrder α] (σ : α ≃ α) (x : α) :
    orbitFourRep σ x ∈ orbitFour σ x := by
  exact Finset.min'_mem _ _

theorem sum_order_four_full
    {α R : Type*} [Fintype α] [LinearOrder α]
    [CommRing R] (σ : α ≃ α) (hσ : ∀ x, σ (σ (σ (σ x))) = x)
    (w : α → R) (hw : ∀ x, w (σ x) = w x) :
    (∑ x ∈ Finset.univ.filter (fun x => σ (σ x) ≠ x), w x) =
      4 * ∑ x ∈ Finset.univ.filter
        (fun x => σ (σ x) ≠ x ∧ orbitFourRep σ x = x), w x := by
  let full := Finset.univ.filter (fun x => σ (σ x) ≠ x)
  let reps := Finset.univ.filter
    (fun x => σ (σ x) ≠ x ∧ orbitFourRep σ x = x)
  let act : α × Fin 4 → α := fun z =>
    match z.2.1 with
    | 0 => z.1
    | 1 => σ z.1
    | 2 => σ (σ z.1)
    | _ => σ (σ (σ z.1))
  have hact_zero (x : α) : act (x, (0 : Fin 4)) = x := by rfl
  have hact_one (x : α) : act (x, (1 : Fin 4)) = σ x := by rfl
  have hact_two (x : α) : act (x, (2 : Fin 4)) = σ (σ x) := by rfl
  have hact_three (x : α) : act (x, (3 : Fin 4)) = σ (σ (σ x)) := by rfl
  have hrep_act (x : α) (i : Fin 4) :
      orbitFourRep σ (act (x, i)) = orbitFourRep σ x := by
    fin_cases i
    · simp [act]
    · simp [act, orbitFourRep_apply σ hσ]
    · simp [act, orbitFourRep_iterate_two σ hσ]
    · simp [act, orbitFourRep_iterate_three σ hσ]
  have hact_full {x : α} (hx : σ (σ x) ≠ x) (i : Fin 4) :
      σ (σ (act (x, i))) ≠ act (x, i) := by
    fin_cases i
    · simpa [act] using hx
    · simp only [act]
      intro h
      exact hx (σ.injective h)
    · simp only [act, hσ]
      exact hx.symm
    · simp only [act, hσ]
      intro h
      exact hx (by simpa [hσ] using (σ.injective h).symm)
  have horbit :
      (∑ x ∈ full, w x) =
        ∑ z ∈ reps ×ˢ (Finset.univ : Finset (Fin 4)), w (act z) := by
    symm
    refine Finset.sum_bij (fun z _hz => act z) ?_ ?_ ?_ ?_
    · intro z hz
      have hzrep : z.1 ∈ reps := (Finset.mem_product.mp hz).1
      have hzfull : σ (σ z.1) ≠ z.1 :=
        (Finset.mem_filter.mp hzrep).2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact_full hzfull z.2⟩
    · rintro ⟨a, i⟩ hz₁ ⟨b, j⟩ hz₂ heq
      change act (a, i) = act (b, j) at heq
      have hz₁rep : orbitFourRep σ a = a :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hz₁).1).2.2
      have hz₂rep : orbitFourRep σ b = b :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hz₂).1).2.2
      have hfst : a = b := by
        rw [← hz₁rep, ← hz₂rep, ← hrep_act a i,
          ← hrep_act b j, heq]
      subst b
      have hfull : σ (σ a) ≠ a :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hz₁).1).2.1
      have h01 : σ a ≠ a := by
        intro h
        exact hfull ((congrArg σ h).trans h)
      have h03 : σ (σ (σ a)) ≠ a := by
        intro h
        apply h01
        simpa [hσ] using (congrArg σ h).symm
      have h12 : σ (σ a) ≠ σ a := by
        intro h
        exact h01 (σ.injective h)
      have h13 : σ (σ (σ a)) ≠ σ a := by
        intro h
        exact hfull (σ.injective h)
      have h23 : σ (σ (σ a)) ≠ σ (σ a) := by
        intro h
        exact h12 (σ.injective h)
      apply Prod.ext
      · rfl
      fin_cases i <;> fin_cases j
      all_goals simp only [act] at heq
      all_goals try rfl
      · exact (h01 heq.symm).elim
      · exact (hfull heq.symm).elim
      · exact (h03 heq.symm).elim
      · exact (h01 heq).elim
      · exact (h12 heq.symm).elim
      · exact (h13 heq.symm).elim
      · exact (hfull heq).elim
      · exact (h12 heq).elim
      · exact (h23 heq.symm).elim
      · exact (h03 heq).elim
      · exact (h13 heq).elim
      · exact (h23 heq).elim
    · intro z hz
      have hzfull : σ (σ z) ≠ z := (Finset.mem_filter.mp hz).2
      let r := orbitFourRep σ z
      have hrmem := orbitFourRep_mem σ z
      change r ∈ orbitFour σ z at hrmem
      simp only [orbitFour, Finset.mem_insert, Finset.mem_singleton] at hrmem
      have hrfull : σ (σ r) ≠ r := by
        rcases hrmem with hr | hr | hr | hr
        · simpa [r, hr] using hzfull
        · rw [hr]
          simpa [act] using hact_full hzfull (1 : Fin 4)
        · rw [hr]
          simpa [act] using hact_full hzfull (2 : Fin 4)
        · rw [hr]
          simpa [act] using hact_full hzfull (3 : Fin 4)
      have hrrep : orbitFourRep σ r = r := by
        rcases hrmem with hr | hr | hr | hr
        · simpa [hr]
        · calc
            orbitFourRep σ r = orbitFourRep σ z := by
              rw [hr, orbitFourRep_apply σ hσ]
            _ = r := rfl
        · calc
            orbitFourRep σ r = orbitFourRep σ z := by
              rw [hr, orbitFourRep_iterate_two σ hσ]
            _ = r := rfl
        · calc
            orbitFourRep σ r = orbitFourRep σ z := by
              rw [hr, orbitFourRep_iterate_three σ hσ]
            _ = r := rfl
      have hrin : r ∈ reps := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrfull, hrrep⟩
      rcases hrmem with hr | hr | hr | hr
      · refine ⟨(r, (0 : Fin 4)), Finset.mem_product.mpr
          ⟨hrin, Finset.mem_univ _⟩, ?_⟩
        change act (r, (0 : Fin 4)) = z
        rw [hact_zero, hr]
      · refine ⟨(r, (3 : Fin 4)), Finset.mem_product.mpr
          ⟨hrin, Finset.mem_univ _⟩, ?_⟩
        change act (r, (3 : Fin 4)) = z
        rw [hact_three, hr, hσ]
      · refine ⟨(r, (2 : Fin 4)), Finset.mem_product.mpr
          ⟨hrin, Finset.mem_univ _⟩, ?_⟩
        change act (r, (2 : Fin 4)) = z
        rw [hact_two, hr, hσ]
      · refine ⟨(r, (1 : Fin 4)), Finset.mem_product.mpr
          ⟨hrin, Finset.mem_univ _⟩, ?_⟩
        change act (r, (1 : Fin 4)) = z
        rw [hact_one, hr, hσ]
    · rintro ⟨x, i⟩ hz
      fin_cases i
      · simp [act]
      · simp [act, hw]
      · simp [act, hw]
      · simp [act, hw]
  have hproduct :
      (∑ z ∈ reps ×ˢ (Finset.univ : Finset (Fin 4)), w (act z)) =
        4 * ∑ x ∈ reps, w x := by
    rw [Finset.sum_product]
    calc
      (∑ x ∈ reps, ∑ i : Fin 4, w (act (x, i))) =
          ∑ x ∈ reps, 4 * w x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ,
          Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp [act, hw]
        ring
      _ = 4 * ∑ x ∈ reps, w x := by rw [Finset.mul_sum]
  rw [horbit, hproduct]

private abbrev E2 (p : ℕ) [NeZero p] [Fact p.Prime] :=
  FiniteField.Extension (ZMod p) p 2
private abbrev E4 (p : ℕ) [NeZero p] [Fact p.Prime] :=
  FiniteField.Extension (ZMod p) p 4

private noncomputable def quadToQuartic
    (p : ℕ) [NeZero p] [Fact p.Prime] : E2 p →ₐ[ZMod p] E4 p := by
  apply Nonempty.some
  apply FiniteField.nonempty_algHom_of_finrank_dvd
  have h2 : Module.finrank (ZMod p) (E2 p) = 2 := by
    refine Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card (ZMod p)) ?_
    simp only [← Module.natCard_eq_pow_finrank,
      FiniteField.natCard_extension]
  have h4 : Module.finrank (ZMod p) (E4 p) = 4 := by
    refine Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card (ZMod p)) ?_
    simp only [← Module.natCard_eq_pow_finrank,
      FiniteField.natCard_extension]
  rw [h2, h4]
  omega

private theorem quadToQuartic_injective (p : ℕ) [NeZero p] [Fact p.Prime] :
    Function.Injective (quadToQuartic p) := by
  exact (quadToQuartic p).injective

private theorem quadToQuartic_frob (p : ℕ) [NeZero p] [Fact p.Prime] :
    ∀ y : E2 p,
      quadToQuartic p
          ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (E2 p)) y) =
        (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (E4 p))
          (quadToQuartic p y) := by
  intro y
  change quadToQuartic p (y ^ Fintype.card (ZMod p)) =
    (quadToQuartic p y) ^ Fintype.card (ZMod p)
  exact map_pow _ _ _

private theorem quadToQuartic_norm (p : ℕ) [NeZero p] [Fact p.Prime]
    (y : E2 p) :
    Algebra.norm (ZMod p) (quadToQuartic p y) =
      (Algebra.norm (ZMod p) y) ^ 2 := by
  letI : Algebra (E2 p) (E4 p) :=
    (quadToQuartic p).toRingHom.toAlgebra
  letI : IsScalarTower (ZMod p) (E2 p) (E4 p) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (quadToQuartic p).commutes a |>.symm)
  have h2 : Module.finrank (ZMod p) (E2 p) = 2 := by
    refine Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card (ZMod p)) ?_
    simp only [← Module.natCard_eq_pow_finrank,
      FiniteField.natCard_extension]
  have h4 : Module.finrank (ZMod p) (E4 p) = 4 := by
    refine Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card (ZMod p)) ?_
    simp only [← Module.natCard_eq_pow_finrank,
      FiniteField.natCard_extension]
  have hrel : Module.finrank (E2 p) (E4 p) = 2 := by
    have hmul := Module.finrank_mul_finrank (ZMod p) (E2 p) (E4 p)
    rw [h2, h4] at hmul
    omega
  rw [← Algebra.norm_norm (R := ZMod p) (S := E2 p) (A := E4 p)
    (a := quadToQuartic p y)]
  rw [show quadToQuartic p y = algebraMap (E2 p) (E4 p) y by rfl]
  rw [Algebra.norm_algebraMap, hrel, map_pow]

private theorem quadToQuartic_weight
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (y : E2 p) :
    let χ₂ := finiteFieldNormLiftMulChar (ZMod p) (E2 p) χ
    let χ₄ := finiteFieldNormLiftMulChar (ZMod p) (E4 p) χ
    (∏ r ∈ R.toFinset,
        (χ₄ ^ R.count r)
          (quadToQuartic p y - algebraMap (ZMod p) (E4 p) r)) =
      (∏ r ∈ R.toFinset,
        (χ₂ ^ R.count r)
          (y - algebraMap (ZMod p) (E2 p) r)) ^ 2 := by
  dsimp only
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro r hr
  rw [show quadToQuartic p y - algebraMap (ZMod p) (E4 p) r =
      quadToQuartic p (y - algebraMap (ZMod p) (E2 p) r) by
    rw [map_sub, (quadToQuartic p).commutes]]
  rw [← map_pow (finiteFieldNormLiftMulChar (ZMod p) (E4 p)) χ
    (R.count r)]
  rw [finiteFieldNormLiftMulChar_apply, quadToQuartic_norm]
  rw [map_pow]
  rw [← finiteFieldNormLiftMulChar_apply (ZMod p) (E2 p)
    (χ ^ R.count r)]
  rw [map_pow (finiteFieldNormLiftMulChar (ZMod p) (E2 p)) χ
    (R.count r)]

theorem quartic_frob_order_four
    (p : ℕ) [NeZero p] [Fact p.Prime] (x : E4 p) :
    let σ : E4 p ≃ₐ[ZMod p] E4 p :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    σ (σ (σ (σ x))) = x := by
  letI : Fintype (E4 p) := Fintype.ofFinite _
  dsimp only
  change (((x ^ Fintype.card (ZMod p)) ^ Fintype.card (ZMod p)) ^
      Fintype.card (ZMod p)) ^ Fintype.card (ZMod p) = x
  rw [ZMod.card p, ← pow_mul, ← pow_mul, ← pow_mul]
  have hcard : Fintype.card (E4 p) = p ^ 4 := by
    rw [Fintype.card_eq_nat_card,
      FiniteField.natCard_extension, Nat.card_zmod]
  rw [show p * (p * (p * p)) = p ^ 4 by ring, ← hcard]
  exact FiniteField.pow_card x

theorem quartic_frob_fixed_iff
    (p : ℕ) [NeZero p] [Fact p.Prime] (x : E4 p) :
    let σ : E4 p ≃ₐ[ZMod p] E4 p :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    σ x = x ↔ ∃ a : ZMod p, algebraMap (ZMod p) (E4 p) a = x := by
  letI : Fintype (E4 p) := Fintype.ofFinite _
  dsimp only
  constructor
  · intro hx
    apply (IsGalois.mem_range_algebraMap_iff_fixed x).2
    intro g
    obtain ⟨i, rfl⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
        (ZMod p) (E4 p)).2 g
    let σ : E4 p ≃ₐ[ZMod p] E4 p :=
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

theorem quartic_norm_frob
    (p : ℕ) [NeZero p] [Fact p.Prime] (x : E4 p) :
    let σ : E4 p ≃ₐ[ZMod p] E4 p :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    Algebra.norm (ZMod p) (σ x) = Algebra.norm (ZMod p) x := by
  dsimp only
  exact Algebra.norm_eq_of_algEquiv
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (E4 p)) x

theorem quartic_rootMultisetWeight_frob
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (x : E4 p) :
    let χE := finiteFieldNormLiftMulChar (ZMod p) (E4 p) χ
    let σ : E4 p ≃ₐ[ZMod p] E4 p :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    (∏ r ∈ R.toFinset,
        (χE ^ R.count r) (σ x - algebraMap (ZMod p) (E4 p) r)) =
      ∏ r ∈ R.toFinset,
        (χE ^ R.count r) (x - algebraMap (ZMod p) (E4 p) r) := by
  dsimp only
  let σ : E4 p ≃ₐ[ZMod p] E4 p :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  apply Finset.prod_congr rfl
  intro r hr
  rw [show σ x - algebraMap (ZMod p) (E4 p) r =
      σ (x - algebraMap (ZMod p) (E4 p) r) by simp]
  rw [← map_pow (finiteFieldNormLiftMulChar (ZMod p) (E4 p)) χ
    (R.count r)]
  rw [finiteFieldNormLiftMulChar_apply]
  rw [show Algebra.norm (ZMod p)
      (σ (x - algebraMap (ZMod p) (E4 p) r)) =
      Algebra.norm (ZMod p)
        (x - algebraMap (ZMod p) (E4 p) r) by
    exact quartic_norm_frob p _]
  exact (finiteFieldNormLiftMulChar_apply (ZMod p) (E4 p)
    (χ ^ R.count r) (x - algebraMap (ZMod p) (E4 p) r)).symm

theorem quartic_rootMultisetWeight_algebraMap
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (a : ZMod p) :
    let χE := finiteFieldNormLiftMulChar (ZMod p) (E4 p) χ
    (∏ r ∈ R.toFinset,
        (χE ^ R.count r)
          (algebraMap (ZMod p) (E4 p) a -
            algebraMap (ZMod p) (E4 p) r)) =
      (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 4 := by
  dsimp only
  have hfinrank : Module.finrank (ZMod p) (E4 p) = 4 := by
    refine Nat.pow_right_injective (Finite.one_lt_card :
      2 ≤ Nat.card (ZMod p)) ?_
    simp only [← Module.natCard_eq_pow_finrank,
      FiniteField.natCard_extension]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro r hr
  rw [← map_sub]
  rw [← map_pow (finiteFieldNormLiftMulChar (ZMod p) (E4 p)) χ
    (R.count r)]
  rw [finiteFieldNormLiftMulChar_apply, Algebra.norm_algebraMap, hfinrank]
  exact map_pow (χ ^ R.count r) (a - r) 4

private theorem quadToQuartic_fixed_iff
    (p : ℕ) [NeZero p] [Fact p.Prime] (x : E4 p) :
    let σ₄ : E4 p ≃ₐ[ZMod p] E4 p :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    σ₄ (σ₄ x) = x ↔ ∃ y : E2 p, quadToQuartic p y = x := by
  letI : Fintype (E2 p) := Fintype.ofFinite _
  letI : Fintype (E4 p) := Fintype.ofFinite _
  letI : Algebra (E2 p) (E4 p) :=
    (quadToQuartic p).toRingHom.toAlgebra
  letI : IsScalarTower (ZMod p) (E2 p) (E4 p) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (quadToQuartic p).commutes a |>.symm)
  have h2 : Module.finrank (ZMod p) (E2 p) = 2 := by
    refine Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card (ZMod p)) ?_
    simp only [← Module.natCard_eq_pow_finrank,
      FiniteField.natCard_extension]
  have h4 : Module.finrank (ZMod p) (E4 p) = 4 := by
    refine Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card (ZMod p)) ?_
    simp only [← Module.natCard_eq_pow_finrank,
      FiniteField.natCard_extension]
  have hrel : Module.finrank (E2 p) (E4 p) = 2 := by
    have hmul := Module.finrank_mul_finrank (ZMod p) (E2 p) (E4 p)
    rw [h2, h4] at hmul
    omega
  dsimp only
  constructor
  · intro hx
    have hxpow : x ^ Fintype.card (E2 p) = x := by
      change (x ^ Fintype.card (ZMod p)) ^ Fintype.card (ZMod p) = x at hx
      rw [Fintype.card_eq_nat_card, FiniteField.natCard_extension]
      rw [Nat.card_zmod]
      rw [ZMod.card p, ← pow_mul] at hx
      simpa [pow_two] using hx
    have hrange : ∃ y : E2 p, algebraMap (E2 p) (E4 p) y = x := by
      apply (IsGalois.mem_range_algebraMap_iff_fixed x).2
      intro g
      obtain ⟨i, rfl⟩ :=
        (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
          (E2 p) (E4 p)).2 g
      have hi : i.1 < 2 := by simpa [hrel] using i.2
      interval_cases hval : i.1
      · simp [hval]
      · simpa [hval] using hxpow
    simpa only [RingHom.algebraMap_toAlgebra] using hrange
  · rintro ⟨y, rfl⟩
    let σ₂ : E2 p ≃ₐ[ZMod p] E2 p :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    let σ₄ : E4 p ≃ₐ[ZMod p] E4 p :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    change σ₄ (σ₄ (quadToQuartic p y)) = quadToQuartic p y
    rw [← quadToQuartic_frob p y, ← quadToQuartic_frob p (σ₂ y)]
    exact congrArg (quadToQuartic p) (quadratic_frob_involutive p y)

theorem quartic_rootMultisetCorrelation_orbit_decomposition
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    let E₂ := E2 p
    let E₄ := E4 p
    letI : Fintype E₂ := Fintype.ofFinite E₂
    letI : DecidableEq E₂ := Classical.decEq E₂
    letI : LinearOrder E₂ := Equiv.linearOrder (Fintype.equivFin E₂)
    letI : Fintype E₄ := Fintype.ofFinite E₄
    letI : DecidableEq E₄ := Classical.decEq E₄
    letI : LinearOrder E₄ := Equiv.linearOrder (Fintype.equivFin E₄)
    let χ₂ := finiteFieldNormLiftMulChar (ZMod p) E₂ χ
    let χ₄ := finiteFieldNormLiftMulChar (ZMod p) E₄ χ
    let σ₂ : E₂ ≃ₐ[ZMod p] E₂ :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    let σ₄ : E₄ ≃ₐ[ZMod p] E₄ :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    finiteFieldRootMultisetCorrelation (ZMod p) E₄ χ₄ R =
      ∑ a : ZMod p,
          (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 4 +
        2 * ∑ y ∈ Finset.univ.filter (fun y : E₂ => y < σ₂ y),
          (∏ r ∈ R.toFinset,
            (χ₂ ^ R.count r) (y - algebraMap (ZMod p) E₂ r)) ^ 2 +
        4 * ∑ x ∈ Finset.univ.filter
          (fun x : E₄ => σ₄ (σ₄ x) ≠ x ∧
            orbitFourRep σ₄.toEquiv x = x),
          ∏ r ∈ R.toFinset,
            (χ₄ ^ R.count r) (x - algebraMap (ZMod p) E₄ r) := by
  dsimp only
  let E₂ := E2 p
  let E₄ := E4 p
  letI : Fintype E₂ := Fintype.ofFinite E₂
  letI : DecidableEq E₂ := Classical.decEq E₂
  letI : LinearOrder E₂ := Equiv.linearOrder (Fintype.equivFin E₂)
  letI : Fintype E₄ := Fintype.ofFinite E₄
  letI : DecidableEq E₄ := Classical.decEq E₄
  letI : LinearOrder E₄ := Equiv.linearOrder (Fintype.equivFin E₄)
  let χ₂ := finiteFieldNormLiftMulChar (ZMod p) E₂ χ
  let χ₄ := finiteFieldNormLiftMulChar (ZMod p) E₄ χ
  let σ₂ : E₂ ≃ₐ[ZMod p] E₂ :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  let σ₄ : E₄ ≃ₐ[ZMod p] E₄ :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  let w₂ : E₂ → ℂ := fun y =>
    ∏ r ∈ R.toFinset,
      (χ₂ ^ R.count r) (y - algebraMap (ZMod p) E₂ r)
  let w₄ : E₄ → ℂ := fun x =>
    ∏ r ∈ R.toFinset,
      (χ₄ ^ R.count r) (x - algebraMap (ZMod p) E₄ r)
  have hfull :
      (∑ x ∈ Finset.univ.filter (fun x : E₄ => σ₄ (σ₄ x) ≠ x),
          w₄ x) =
        4 * ∑ x ∈ Finset.univ.filter
          (fun x : E₄ => σ₄ (σ₄ x) ≠ x ∧
            orbitFourRep σ₄.toEquiv x = x), w₄ x := by
    apply sum_order_four_full σ₄.toEquiv
    · intro x
      exact quartic_frob_order_four p x
    · intro x
      exact quartic_rootMultisetWeight_frob p χ R x
  have hsubfield :
      (∑ x ∈ Finset.univ.filter (fun x : E₄ => σ₄ (σ₄ x) = x),
          w₄ x) = ∑ y : E₂, (w₂ y) ^ 2 := by
    symm
    refine Finset.sum_bij
      (fun y (_hy : y ∈ (Finset.univ : Finset E₂)) => quadToQuartic p y)
      ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (quadToQuartic_fixed_iff p (quadToQuartic p y)).2 ⟨y, rfl⟩
    · intro y₁ hy₁ y₂ hy₂ h
      exact quadToQuartic_injective p h
    · intro x hx
      have hxfix : σ₄ (σ₄ x) = x := (Finset.mem_filter.mp hx).2
      obtain ⟨y, hy⟩ := (quadToQuartic_fixed_iff p x).mp (by
        simpa [σ₄] using hxfix)
      exact ⟨y, Finset.mem_univ y, hy⟩
    · intro y hy
      change (w₂ y) ^ 2 = w₄ (quadToQuartic p y)
      exact (quadToQuartic_weight p χ R y).symm
  have hquadOrbit :
      (∑ y : E₂, (w₂ y) ^ 2) =
        ∑ y ∈ Finset.univ.filter (fun y : E₂ => σ₂ y = y),
            (w₂ y) ^ 2 +
          2 * ∑ y ∈ Finset.univ.filter (fun y : E₂ => y < σ₂ y),
            (w₂ y) ^ 2 := by
    apply sum_involution σ₂.toEquiv
    · intro y
      exact quadratic_frob_involutive p y
    · intro y
      simpa [w₂, χ₂, σ₂] using congrArg (fun z : ℂ => z ^ 2)
        (quadratic_rootMultisetWeight_frob p χ R y)
  have hquadFixed :
      (∑ y ∈ Finset.univ.filter (fun y : E₂ => σ₂ y = y),
          (w₂ y) ^ 2) =
        ∑ a : ZMod p,
          (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 4 := by
    symm
    refine Finset.sum_bij
      (fun a (_ha : a ∈ (Finset.univ : Finset (ZMod p))) =>
        algebraMap (ZMod p) E₂ a) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [σ₂]
    · intro a₁ ha₁ a₂ ha₂ h
      exact (algebraMap (ZMod p) E₂).injective h
    · intro y hy
      have hyfix : σ₂ y = y := (Finset.mem_filter.mp hy).2
      obtain ⟨a, ha⟩ := (quadratic_frob_fixed_iff p y).mp (by
        simpa [σ₂] using hyfix)
      exact ⟨a, Finset.mem_univ a, ha⟩
    · intro a ha
      change (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 4 =
        (w₂ (algebraMap (ZMod p) E₂ a)) ^ 2
      have haweight := quadratic_rootMultisetWeight_algebraMap p χ R a
      simp only [w₂, χ₂] at ⊢
      rw [haweight]
      ring
  have hsplit :
      (∑ x : E₄, w₄ x) =
        (∑ x ∈ Finset.univ.filter (fun x : E₄ => σ₄ (σ₄ x) = x),
            w₄ x) +
          ∑ x ∈ Finset.univ.filter (fun x : E₄ => σ₄ (σ₄ x) ≠ x),
            w₄ x := by
    symm
    simpa only using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x : E₄ => σ₄ (σ₄ x) = x) w₄)
  unfold finiteFieldRootMultisetCorrelation
  change (∑ x : E₄, w₄ x) = _
  rw [hsplit, hsubfield, hquadOrbit, hquadFixed, hfull]

theorem completeHomogeneousFour_integral
    {α : Type*} [DecidableEq α] (s : Finset α) (u : α → ℂ)
    (hu : ∀ x ∈ s, IsIntegral ℤ (u x)) :
    IsIntegral ℤ
      (((∑ x ∈ s, u x) ^ 4 +
          6 * (∑ x ∈ s, u x) ^ 2 * (∑ x ∈ s, u x ^ 2) +
          3 * (∑ x ∈ s, u x ^ 2) ^ 2 +
          8 * (∑ x ∈ s, u x) * (∑ x ∈ s, u x ^ 3) +
          6 * (∑ x ∈ s, u x ^ 4)) / 24) := by
  induction s using Finset.induction_on with
  | empty =>
      norm_num
      exact isIntegral_zero
  | @insert a s ha ih =>
      have hi := ih (fun x hx => hu x (Finset.mem_insert_of_mem hx))
      have hthree := completeHomogeneousThree_integral s u
        (fun x hx => hu x (Finset.mem_insert_of_mem hx))
      have htwo := completeHomogeneousTwo_integral s u
        (fun x hx => hu x (Finset.mem_insert_of_mem hx))
      have hua := hu a (Finset.mem_insert_self a s)
      have hsum : IsIntegral ℤ (∑ x ∈ s, u x) :=
        IsIntegral.sum (fun x => u x)
          (fun x hx => hu x (Finset.mem_insert_of_mem hx))
      have hformula :
          (((∑ x ∈ insert a s, u x) ^ 4 +
              6 * (∑ x ∈ insert a s, u x) ^ 2 *
                (∑ x ∈ insert a s, u x ^ 2) +
              3 * (∑ x ∈ insert a s, u x ^ 2) ^ 2 +
              8 * (∑ x ∈ insert a s, u x) *
                (∑ x ∈ insert a s, u x ^ 3) +
              6 * (∑ x ∈ insert a s, u x ^ 4)) / 24) =
            (((∑ x ∈ s, u x) ^ 4 +
                6 * (∑ x ∈ s, u x) ^ 2 * (∑ x ∈ s, u x ^ 2) +
                3 * (∑ x ∈ s, u x ^ 2) ^ 2 +
                8 * (∑ x ∈ s, u x) * (∑ x ∈ s, u x ^ 3) +
                6 * (∑ x ∈ s, u x ^ 4)) / 24) +
              u a * (((∑ x ∈ s, u x) ^ 3 +
                3 * (∑ x ∈ s, u x) * (∑ x ∈ s, u x ^ 2) +
                2 * (∑ x ∈ s, u x ^ 3)) / 6) +
              u a ^ 2 * (((∑ x ∈ s, u x) ^ 2 +
                ∑ x ∈ s, u x ^ 2) / 2) +
              u a ^ 3 * (∑ x ∈ s, u x) + u a ^ 4 := by
        simp only [Finset.sum_insert ha]
        ring
      rw [hformula]
      exact (((hi.add (hua.mul hthree)).add ((hua.pow 2).mul htwo)).add
        ((hua.pow 3).mul hsum)).add (hua.pow 4)

theorem primeRootMultisetFourthNewtonNumerator_integral
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    IsIntegral ℤ
      ((primeRootMultisetExtensionCorrelation p χ R 0 ^ 4 +
        6 * primeRootMultisetExtensionCorrelation p χ R 0 ^ 2 *
          primeRootMultisetExtensionCorrelation p χ R 1 +
        3 * primeRootMultisetExtensionCorrelation p χ R 1 ^ 2 +
        8 * primeRootMultisetExtensionCorrelation p χ R 0 *
          primeRootMultisetExtensionCorrelation p χ R 2 +
        6 * primeRootMultisetExtensionCorrelation p χ R 3) / 24) := by
  let u : ZMod p → ℂ := fun a =>
    ∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)
  let A : ℂ := ∑ a : ZMod p, u a
  let D₂ : ℂ := ∑ a : ZMod p, u a ^ 2
  let D₃ : ℂ := ∑ a : ZMod p, u a ^ 3
  let D₄ : ℂ := ∑ a : ZMod p, u a ^ 4
  let E₂ := E2 p
  letI : Fintype E₂ := Fintype.ofFinite E₂
  letI : DecidableEq E₂ := Classical.decEq E₂
  letI : LinearOrder E₂ := Equiv.linearOrder (Fintype.equivFin E₂)
  let χE₂ := finiteFieldNormLiftMulChar (ZMod p) E₂ χ
  let σ₂ : E₂ ≃ₐ[ZMod p] E₂ :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  let w₂ : E₂ → ℂ := fun y =>
    ∏ r ∈ R.toFinset,
      (χE₂ ^ R.count r) (y - algebraMap (ZMod p) E₂ r)
  let S₂ : Finset E₂ := Finset.univ.filter (fun y : E₂ => y < σ₂ y)
  let Y : ℂ := ∑ y ∈ S₂, w₂ y
  let Y₂ : ℂ := ∑ y ∈ S₂, w₂ y ^ 2
  let X : ℂ :=
    (primeRootMultisetExtensionCorrelation p χ R 2 - D₃) / 3
  let E₄ := E4 p
  letI : Fintype E₄ := Fintype.ofFinite E₄
  letI : DecidableEq E₄ := Classical.decEq E₄
  letI : LinearOrder E₄ := Equiv.linearOrder (Fintype.equivFin E₄)
  let χE₄ := finiteFieldNormLiftMulChar (ZMod p) E₄ χ
  let σ₄ : E₄ ≃ₐ[ZMod p] E₄ :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  let w₄ : E₄ → ℂ := fun x =>
    ∏ r ∈ R.toFinset,
      (χE₄ ^ R.count r) (x - algebraMap (ZMod p) E₄ r)
  let Z : ℂ :=
    ∑ x ∈ Finset.univ.filter
      (fun x : E₄ => σ₄ (σ₄ x) ≠ x ∧
        orbitFourRep σ₄.toEquiv x = x), w₄ x
  have hzero : primeRootMultisetExtensionCorrelation p χ R 0 = A := by
    rfl
  have hone : primeRootMultisetExtensionCorrelation p χ R 1 = D₂ + 2 * Y := by
    change finiteFieldRootMultisetCorrelation (ZMod p) E₂ χE₂ R =
      D₂ + 2 * Y
    exact quadratic_rootMultisetCorrelation_orbit_decomposition p χ R
  have htwo : primeRootMultisetExtensionCorrelation p χ R 2 = D₃ + 3 * X := by
    unfold X
    ring
  have hthree : primeRootMultisetExtensionCorrelation p χ R 3 =
      D₄ + 2 * Y₂ + 4 * Z := by
    change finiteFieldRootMultisetCorrelation (ZMod p) E₄ χE₄ R =
      D₄ + 2 * Y₂ + 4 * Z
    exact quartic_rootMultisetCorrelation_orbit_decomposition p χ R
  have hformula :
      ((primeRootMultisetExtensionCorrelation p χ R 0 ^ 4 +
          6 * primeRootMultisetExtensionCorrelation p χ R 0 ^ 2 *
            primeRootMultisetExtensionCorrelation p χ R 1 +
          3 * primeRootMultisetExtensionCorrelation p χ R 1 ^ 2 +
          8 * primeRootMultisetExtensionCorrelation p χ R 0 *
            primeRootMultisetExtensionCorrelation p χ R 2 +
          6 * primeRootMultisetExtensionCorrelation p χ R 3) / 24) =
        ((A ^ 4 + 6 * A ^ 2 * D₂ + 3 * D₂ ^ 2 +
            8 * A * D₃ + 6 * D₄) / 24) +
          ((A ^ 2 + D₂) / 2) * Y +
          ((Y ^ 2 + Y₂) / 2) + A * X + Z := by
    rw [hzero, hone, htwo, hthree]
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
  have hH₄ : IsIntegral ℤ
      ((A ^ 4 + 6 * A ^ 2 * D₂ + 3 * D₂ ^ 2 +
        8 * A * D₃ + 6 * D₄) / 24) := by
    change IsIntegral ℤ
      (((∑ a ∈ (Finset.univ : Finset (ZMod p)), u a) ^ 4 +
        6 * (∑ a ∈ (Finset.univ : Finset (ZMod p)), u a) ^ 2 *
          (∑ a ∈ (Finset.univ : Finset (ZMod p)), u a ^ 2) +
        3 * (∑ a ∈ (Finset.univ : Finset (ZMod p)), u a ^ 2) ^ 2 +
        8 * (∑ a ∈ (Finset.univ : Finset (ZMod p)), u a) *
          (∑ a ∈ (Finset.univ : Finset (ZMod p)), u a ^ 3) +
        6 * (∑ a ∈ (Finset.univ : Finset (ZMod p)), u a ^ 4)) / 24)
    exact completeHomogeneousFour_integral Finset.univ u
      (fun a _ha => hu a)
  have hH₂ : IsIntegral ℤ ((A ^ 2 + D₂) / 2) := by
    change IsIntegral ℤ
      (((∑ a ∈ (Finset.univ : Finset (ZMod p)), u a) ^ 2 +
        ∑ a ∈ (Finset.univ : Finset (ZMod p)), u a ^ 2) / 2)
    exact completeHomogeneousTwo_integral Finset.univ u
      (fun a _ha => hu a)
  have hw₂ (y : E₂) : IsIntegral ℤ (w₂ y) := by
    unfold w₂
    exact IsIntegral.prod
      (fun r : ZMod p =>
        (χE₂ ^ R.count r) (y - algebraMap (ZMod p) E₂ r))
      (fun r _hr => isIntegral_finiteFieldMulChar_apply
        (χE₂ ^ R.count r) (y - algebraMap (ZMod p) E₂ r))
  have hY : IsIntegral ℤ Y := by
    unfold Y
    exact IsIntegral.sum (fun y : E₂ => w₂ y) (fun y _hy => hw₂ y)
  have hYtwo : IsIntegral ℤ ((Y ^ 2 + Y₂) / 2) := by
    change IsIntegral ℤ
      (((∑ y ∈ S₂, w₂ y) ^ 2 + ∑ y ∈ S₂, w₂ y ^ 2) / 2)
    exact completeHomogeneousTwo_integral S₂ w₂
      (fun y _hy => hw₂ y)
  have hH₃ : IsIntegral ℤ
      ((A ^ 3 + 3 * A * D₂ + 2 * D₃) / 6) := by
    change IsIntegral ℤ
      (((∑ a ∈ (Finset.univ : Finset (ZMod p)), u a) ^ 3 +
        3 * (∑ a ∈ (Finset.univ : Finset (ZMod p)), u a) *
          (∑ a ∈ (Finset.univ : Finset (ZMod p)), u a ^ 2) +
        2 * (∑ a ∈ (Finset.univ : Finset (ZMod p)), u a ^ 3)) / 6)
    exact completeHomogeneousThree_integral Finset.univ u
      (fun a _ha => hu a)
  have hX : IsIntegral ℤ X := by
    have hn := primeRootMultisetThirdNewtonNumerator_integral p χ R
    have hnformula :
        ((primeRootMultisetExtensionCorrelation p χ R 0 ^ 3 +
          3 * primeRootMultisetExtensionCorrelation p χ R 0 *
            primeRootMultisetExtensionCorrelation p χ R 1 +
          2 * primeRootMultisetExtensionCorrelation p χ R 2) / 6) =
          ((A ^ 3 + 3 * A * D₂ + 2 * D₃) / 6) + A * Y + X := by
      rw [hzero, hone]
      unfold X
      ring
    rw [hnformula] at hn
    convert (hn.sub hH₃).sub (hA.mul hY) using 1
    ring
  have hZ : IsIntegral ℤ Z := by
    unfold Z w₄
    exact IsIntegral.sum
      (fun x : E₄ => ∏ r ∈ R.toFinset,
        (χE₄ ^ R.count r) (x - algebraMap (ZMod p) E₄ r))
      (fun x _hx => IsIntegral.prod
        (fun r : ZMod p =>
          (χE₄ ^ R.count r) (x - algebraMap (ZMod p) E₄ r))
        (fun r _hr => isIntegral_finiteFieldMulChar_apply
          (χE₄ ^ R.count r) (x - algebraMap (ZMod p) E₄ r)))
  rw [hformula]
  exact (((hH₄.add (hH₂.mul hY)).add hYtwo).add (hA.mul hX)).add hZ

theorem complexNewtonElementary_four (v : ℕ → ℂ) :
    complexNewtonElementary v 4 =
      (v 1 ^ 4 - 6 * v 1 ^ 2 * v 2 + 3 * v 2 ^ 2 +
        8 * v 1 * v 3 - 6 * v 4) / 24 := by
  change complexNewtonElementary v (3 + 1) = _
  rw [complexNewtonElementary_succ]
  have had : {a ∈ Finset.antidiagonal 4 | a.1 < 4} =
      {(0, 4), (1, 3), (2, 2), (3, 1)} := by decide
  norm_num only at had ⊢
  rw [had]
  norm_num [Finset.sum_insert]
  rw [complexNewtonElementary_one, complexNewtonElementary_two,
    complexNewtonElementary_three]
  norm_num [Finset.sum_insert, complexNewtonElementary]
  ring

theorem primeRootMultisetNewtonElementary_four_integral
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    IsIntegral ℤ (primeRootMultisetNewtonElementary p χ R 4) := by
  have h := primeRootMultisetFourthNewtonNumerator_integral p χ R
  convert h using 1
  rw [primeRootMultisetNewtonElementary, complexNewtonElementary_four]
  simp only [primeRootMultisetNewtonPowerSum]
  ring

/-- The first five Newton elementary coefficients are unconditional. -/
theorem primeRootMultisetNewtonElementary_integral_of_le_four
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (j : ℕ) (hj : j ≤ 4) :
    IsIntegral ℤ (primeRootMultisetNewtonElementary p χ R j) := by
  interval_cases j
  · exact primeRootMultisetNewtonElementary_zero_integral p χ R
  · exact primeRootMultisetNewtonElementary_one_integral p χ R
  · exact primeRootMultisetNewtonElementary_two_integral p χ R
  · exact primeRootMultisetNewtonElementary_three_integral p χ R
  · exact primeRootMultisetNewtonElementary_four_integral p χ R

end

end Tao2026
