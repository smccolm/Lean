import Tao2026.BurgessWeilPrimeKummerLegendreIntegrality

/-!
# Unconditional integrality of the canonical Legendre determinant

The quadratic-extension correlation admits a Frobenius-orbit decomposition.
Its fixed points are precisely the embedded base field, and the norm-lifted
Legendre weight on those points is the square of the base-field weight.  The
square of the base correlation has the same diagonal term after pairing
ordered pairs under coordinate swap.  Consequently the numerator in the
quadratic Newton determinant is twice an explicit sum of algebraic integers.

This removes determinant integrality from the remaining canonical Legendre
source.  Only the square-root bounds on the two explicit roots and the
all-extension recurrence remain.
-/

namespace Tao2026

open Finset
open scoped BigOperators

noncomputable section

theorem sum_involution
    {α R : Type*} [Fintype α] [LinearOrder α]
    [CommRing R] (σ : α ≃ α) (hσ : ∀ x, σ (σ x) = x)
    (w : α → R) (hw : ∀ x, w (σ x) = w x) :
    ∑ x, w x =
      ∑ x ∈ Finset.univ.filter (fun x => σ x = x), w x +
        2 * ∑ x ∈ Finset.univ.filter (fun x => x < σ x), w x := by
  let fixed := Finset.univ.filter (fun x => σ x = x)
  let moved := Finset.univ.filter (fun x => σ x ≠ x)
  let lower := Finset.univ.filter (fun x => x < σ x)
  let upper := Finset.univ.filter (fun x => σ x < x)
  have hsplit :
      (∑ x, w x) = (∑ x ∈ fixed, w x) + ∑ x ∈ moved, w x := by
    symm
    simpa [fixed, moved] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => σ x = x) w)
  have hmoved : moved = lower ∪ upper := by
    ext x
    simp only [moved, lower, upper, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · intro hx
      exact lt_or_gt_of_ne hx.symm
    · intro hx
      exact hx.elim ne_of_gt ne_of_lt
  have hdisjoint : Disjoint lower upper := by
    rw [Finset.disjoint_left]
    intro x hxlower hxupper
    simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and] at hxlower
    simp only [upper, Finset.mem_filter, Finset.mem_univ, true_and] at hxupper
    exact lt_asymm hxlower hxupper
  have hupper : (∑ x ∈ upper, w x) = ∑ x ∈ lower, w x := by
    apply Finset.sum_equiv σ
    · intro x
      simp only [upper, lower, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hσ]
    · intro x _hx
      exact (hw x).symm
  rw [hsplit, hmoved, Finset.sum_union hdisjoint, hupper]
  change _ = _ + 2 * _
  ring

theorem quadratic_frob_involutive
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (x : FiniteField.Extension (ZMod p) p 2) :
    let σ : (FiniteField.Extension (ZMod p) p 2) ≃ₐ[ZMod p]
        (FiniteField.Extension (ZMod p) p 2) :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    σ (σ x) = x := by
  letI : Fintype (FiniteField.Extension (ZMod p) p 2) := Fintype.ofFinite _
  dsimp only
  change (x ^ Fintype.card (ZMod p)) ^ Fintype.card (ZMod p) = x
  rw [ZMod.card p, ← pow_mul, ← pow_two]
  have hcard : Fintype.card (FiniteField.Extension (ZMod p) p 2) = p ^ 2 := by
    rw [Fintype.card_eq_nat_card,
      FiniteField.natCard_extension, Nat.card_zmod]
  rw [← hcard]
  exact FiniteField.pow_card x

theorem quadratic_norm_frob
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (x : FiniteField.Extension (ZMod p) p 2) :
    let σ : (FiniteField.Extension (ZMod p) p 2) ≃ₐ[ZMod p]
        (FiniteField.Extension (ZMod p) p 2) :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    Algebra.norm (ZMod p) (σ x) =
      Algebra.norm (ZMod p) x := by
  letI : Fintype (FiniteField.Extension (ZMod p) p 2) := Fintype.ofFinite _
  dsimp only
  apply (algebraMap (ZMod p)
    (FiniteField.Extension (ZMod p) p 2)).injective
  rw [FiniteField.algebraMap_norm_eq_prod_pow,
    FiniteField.algebraMap_norm_eq_prod_pow]
  have hfinrank : Module.finrank (ZMod p)
      (FiniteField.Extension (ZMod p) p 2) = 2 := by
    refine Nat.pow_right_injective (Finite.one_lt_card :
      2 ≤ Nat.card (ZMod p)) ?_
    simp only [← Module.natCard_eq_pow_finrank,
      FiniteField.natCard_extension]
  rw [hfinrank]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    Nat.card_zmod, pow_zero, pow_one]
  have hpow : (x ^ p) ^ p = x := by
    rw [← pow_mul, ← pow_two]
    have hcard : Fintype.card (FiniteField.Extension (ZMod p) p 2) = p ^ 2 := by
      rw [Fintype.card_eq_nat_card,
        FiniteField.natCard_extension, Nat.card_zmod]
    rw [← hcard]
    exact FiniteField.pow_card x
  change (x ^ Fintype.card (ZMod p)) *
      (x ^ Fintype.card (ZMod p)) ^ p = x * x ^ p
  rw [ZMod.card p]
  rw [hpow]
  ring

theorem quadratic_frob_fixed_iff
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (x : FiniteField.Extension (ZMod p) p 2) :
    let σ : (FiniteField.Extension (ZMod p) p 2) ≃ₐ[ZMod p]
        (FiniteField.Extension (ZMod p) p 2) :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    σ x = x ↔ ∃ a : ZMod p,
      algebraMap (ZMod p) (FiniteField.Extension (ZMod p) p 2) a = x := by
  letI : Fintype (FiniteField.Extension (ZMod p) p 2) := Fintype.ofFinite _
  dsimp only
  constructor
  · intro hx
    apply (IsGalois.mem_range_algebraMap_iff_fixed x).2
    intro g
    obtain ⟨i, rfl⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
        (ZMod p) (FiniteField.Extension (ZMod p) p 2)).2 g
    have hfinrank : Module.finrank (ZMod p)
        (FiniteField.Extension (ZMod p) p 2) = 2 := by
      refine Nat.pow_right_injective (Finite.one_lt_card :
        2 ≤ Nat.card (ZMod p)) ?_
      simp only [← Module.natCard_eq_pow_finrank,
        FiniteField.natCard_extension]
    have hi : i.1 < 2 := by simpa [hfinrank] using i.2
    interval_cases hval : i.1
    · simp [hval]
    · simpa [hval] using hx
  · rintro ⟨a, rfl⟩
    simp

private theorem quadratic_legendreWeight_frob
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p)
    (x : FiniteField.Extension (ZMod p) p 2) :
    let E := FiniteField.Extension (ZMod p) p 2
    let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
    let σ : E ≃ₐ[ZMod p] E :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    (χE ^ m) (σ x) * (χE ^ n) (σ x - 1) *
        (χE ^ k) (σ x - algebraMap (ZMod p) E t) =
      (χE ^ m) x * (χE ^ n) (x - 1) *
        (χE ^ k) (x - algebraMap (ZMod p) E t) := by
  dsimp only
  let E := FiniteField.Extension (ZMod p) p 2
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let σ : E ≃ₐ[ZMod p] E :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  change (χE ^ m) (σ x) * (χE ^ n) (σ x - 1) *
      (χE ^ k) (σ x - algebraMap (ZMod p) E t) =
    (χE ^ m) x * (χE ^ n) (x - 1) *
      (χE ^ k) (x - algebraMap (ZMod p) E t)
  rw [show σ x - 1 = σ (x - 1) by simp,
    show σ x - algebraMap (ZMod p) E t =
        σ (x - algebraMap (ZMod p) E t) by simp]
  have heval (r : ℕ) (y : E) : (χE ^ r) (σ y) = (χE ^ r) y := by
    change ((finiteFieldNormLiftMulChar (ZMod p) E χ) ^ r) (σ y) = _
    rw [← map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ r]
    rw [finiteFieldNormLiftMulChar_apply]
    rw [show Algebra.norm (ZMod p) (σ y) = Algebra.norm (ZMod p) y by
      exact quadratic_norm_frob p y]
    exact (finiteFieldNormLiftMulChar_apply (ZMod p) E (χ ^ r) y).symm
  rw [heval m x, heval n (x - 1),
    heval k (x - algebraMap (ZMod p) E t)]

private theorem quadratic_legendreWeight_algebraMap
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t a : ZMod p) :
    let E := FiniteField.Extension (ZMod p) p 2
    let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
    (χE ^ m) (algebraMap (ZMod p) E a) *
        (χE ^ n) (algebraMap (ZMod p) E a - 1) *
        (χE ^ k) (algebraMap (ZMod p) E a - algebraMap (ZMod p) E t) =
      ((χ ^ m) a * (χ ^ n) (a - 1) * (χ ^ k) (a - t)) ^ 2 := by
  dsimp only
  have hfinrank : Module.finrank (ZMod p)
      (FiniteField.Extension (ZMod p) p 2) = 2 := by
    refine Nat.pow_right_injective (Finite.one_lt_card :
      2 ≤ Nat.card (ZMod p)) ?_
    simp only [← Module.natCard_eq_pow_finrank,
      FiniteField.natCard_extension]
  rw [← map_sub, ← map_one (algebraMap (ZMod p)
    (FiniteField.Extension (ZMod p) p 2)), ← map_sub]
  have heval (r : ℕ) (y : ZMod p) :
      (finiteFieldNormLiftMulChar (ZMod p)
          (FiniteField.Extension (ZMod p) p 2) χ ^ r)
          (algebraMap (ZMod p) (FiniteField.Extension (ZMod p) p 2) y) =
        (χ ^ r) y ^ 2 := by
    rw [← map_pow (finiteFieldNormLiftMulChar (ZMod p)
      (FiniteField.Extension (ZMod p) p 2)) χ r]
    rw [finiteFieldNormLiftMulChar_apply,
      Algebra.norm_algebraMap, hfinrank]
    exact map_pow (χ ^ r) y 2
  rw [heval m a, heval n (a - 1), heval k (a - t)]
  ring

private theorem quadratic_correlation_orbit_decomposition
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    let E := FiniteField.Extension (ZMod p) p 2
    letI : Fintype E := Fintype.ofFinite E
    letI : DecidableEq E := Classical.decEq E
    letI : LinearOrder E := Equiv.linearOrder (Fintype.equivFin E)
    let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
    let σ : E ≃ₐ[ZMod p] E :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    finiteFieldPowerLegendreCorrelation E (χE ^ m) (χE ^ n) (χE ^ k)
        (algebraMap (ZMod p) E t) =
      ∑ a : ZMod p,
          ((χ ^ m) a * (χ ^ n) (a - 1) * (χ ^ k) (a - t)) ^ 2 +
        2 * ∑ x ∈ Finset.univ.filter (fun x : E => x < σ x),
          (χE ^ m) x * (χE ^ n) (x - 1) *
            (χE ^ k) (x - algebraMap (ZMod p) E t) := by
  dsimp only
  let E := FiniteField.Extension (ZMod p) p 2
  letI : Fintype E := Fintype.ofFinite E
  letI : DecidableEq E := Classical.decEq E
  letI : LinearOrder E := Equiv.linearOrder (Fintype.equivFin E)
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let σ : E ≃ₐ[ZMod p] E :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  let w : E → ℂ := fun x =>
    (χE ^ m) x * (χE ^ n) (x - 1) *
      (χE ^ k) (x - algebraMap (ZMod p) E t)
  have horbit :
      (∑ x : E, w x) =
        ∑ x ∈ Finset.univ.filter (fun x : E => σ x = x), w x +
          2 * ∑ x ∈ Finset.univ.filter (fun x : E => x < σ x), w x := by
    apply sum_involution σ.toEquiv
    · intro x
      exact quadratic_frob_involutive p x
    · intro x
      exact quadratic_legendreWeight_frob p χ m n k t x
  have hfixed :
      (∑ x ∈ Finset.univ.filter (fun x : E => σ x = x), w x) =
        ∑ a : ZMod p,
          ((χ ^ m) a * (χ ^ n) (a - 1) * (χ ^ k) (a - t)) ^ 2 := by
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
      obtain ⟨a, ha⟩ := (quadratic_frob_fixed_iff p x).mp (by
        simpa [σ] using hxfix)
      exact ⟨a, Finset.mem_univ a, ha⟩
    · intro a ha
      change ((χ ^ m) a * (χ ^ n) (a - 1) * (χ ^ k) (a - t)) ^ 2 =
        w (algebraMap (ZMod p) E a)
      exact (quadratic_legendreWeight_algebraMap p χ m n k t a).symm
  unfold finiteFieldPowerLegendreCorrelation
  change (∑ x : E, w x) = _
  rw [horbit, hfixed]

theorem sum_sq_orbit_decomposition
    {α R : Type*} [Fintype α] [CommRing R] (u : α → R) :
    let P := α × α
    letI : Fintype P := inferInstance
    letI : DecidableEq P := Classical.decEq P
    letI : LinearOrder P := Equiv.linearOrder (Fintype.equivFin P)
    let σ : P ≃ P :=
      { toFun := fun z => (z.2, z.1)
        invFun := fun z => (z.2, z.1)
        left_inv := fun z => by cases z; rfl
        right_inv := fun z => by cases z; rfl }
    (∑ a : α, u a) ^ 2 =
      ∑ a : α, u a ^ 2 +
        2 * ∑ z ∈ Finset.univ.filter (fun z : P => z < σ z),
          u z.1 * u z.2 := by
  dsimp only
  let P := α × α
  letI : Fintype P := inferInstance
  letI : DecidableEq P := Classical.decEq P
  letI : LinearOrder P := Equiv.linearOrder (Fintype.equivFin P)
  let σ : P ≃ P :=
    { toFun := fun z => (z.2, z.1)
      invFun := fun z => (z.2, z.1)
      left_inv := fun z => by cases z; rfl
      right_inv := fun z => by cases z; rfl }
  let w : P → R := fun z => u z.1 * u z.2
  have horbit :
      (∑ z : P, w z) =
        ∑ z ∈ Finset.univ.filter (fun z : P => σ z = z), w z +
          2 * ∑ z ∈ Finset.univ.filter (fun z : P => z < σ z), w z := by
    apply sum_involution σ
    · intro z
      cases z
      rfl
    · intro z
      cases z
      dsimp [σ, w]
      ring
  have htotal : (∑ z : P, w z) = (∑ a : α, u a) ^ 2 := by
    rw [pow_two, Fintype.sum_mul_sum]
    rw [Fintype.sum_prod_type]
  have hfixed :
      (∑ z ∈ Finset.univ.filter (fun z : P => σ z = z), w z) =
        ∑ a : α, u a ^ 2 := by
    symm
    refine Finset.sum_bij
      (fun a (_ha : a ∈ (Finset.univ : Finset α)) => (a, a)) ?_ ?_ ?_ ?_
    · intro a ha
      simp [σ]
    · intro a₁ ha₁ a₂ ha₂ h
      exact congrArg Prod.fst h
    · intro z hz
      have hzfix : σ z = z := (Finset.mem_filter.mp hz).2
      refine ⟨z.1, Finset.mem_univ z.1, ?_⟩
      cases z with
      | mk a b =>
          change (b, a) = (a, b) at hzfix
          exact Prod.ext rfl (congrArg Prod.fst hzfix).symm
    · intro a ha
      change u a ^ 2 = w (a, a)
      simp [w, pow_two]
  rw [← htotal, horbit, hfixed]

/-- The correlation-determined canonical determinant is always an algebraic
integer; no Frobenius spectrum is required. -/
theorem primePowerLegendreCharacteristicDeterminant_integral_unconditional
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    IsIntegral ℤ
      (primePowerLegendreCharacteristicDeterminant p χ m n k t) := by
  let u : ZMod p → ℂ := fun a =>
    (χ ^ m) a * (χ ^ n) (a - 1) * (χ ^ k) (a - t)
  let P := ZMod p × ZMod p
  letI : Fintype P := inferInstance
  letI : DecidableEq P := Classical.decEq P
  letI : LinearOrder P := Equiv.linearOrder (Fintype.equivFin P)
  let swap : P ≃ P :=
    { toFun := fun z => (z.2, z.1)
      invFun := fun z => (z.2, z.1)
      left_inv := fun z => by cases z; rfl
      right_inv := fun z => by cases z; rfl }
  let B : ℂ :=
    ∑ z ∈ Finset.univ.filter (fun z : P => z < swap z), u z.1 * u z.2
  let D : ℂ := ∑ a : ZMod p, u a ^ 2
  let E := FiniteField.Extension (ZMod p) p 2
  letI : Fintype E := Fintype.ofFinite E
  letI : DecidableEq E := Classical.decEq E
  letI : LinearOrder E := Equiv.linearOrder (Fintype.equivFin E)
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let σ : E ≃ₐ[ZMod p] E :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  let w : E → ℂ := fun x =>
    (χE ^ m) x * (χE ^ n) (x - 1) *
      (χE ^ k) (x - algebraMap (ZMod p) E t)
  let X : ℂ :=
    ∑ x ∈ Finset.univ.filter (fun x : E => x < σ x), w x
  have hbase :
      primePowerLegendreExtensionCorrelation p χ m n k t 0 ^ 2 =
        D + 2 * B := by
    change (∑ a : ZMod p, u a) ^ 2 = D + 2 * B
    exact sum_sq_orbit_decomposition u
  have hext :
      primePowerLegendreExtensionCorrelation p χ m n k t 1 =
        D + 2 * X := by
    change finiteFieldPowerLegendreCorrelation E
        (χE ^ m) (χE ^ n) (χE ^ k)
          (algebraMap (ZMod p) E t) = D + 2 * X
    exact quadratic_correlation_orbit_decomposition p χ m n k t
  have hdet :
      primePowerLegendreCharacteristicDeterminant p χ m n k t =
        D + B + X := by
    rw [primePowerLegendreCharacteristicDeterminant, hbase, hext]
    ring
  have hu (a : ZMod p) : IsIntegral ℤ (u a) := by
    exact ((isIntegral_finiteFieldMulChar_apply (χ ^ m) a).mul
      (isIntegral_finiteFieldMulChar_apply (χ ^ n) (a - 1))).mul
        (isIntegral_finiteFieldMulChar_apply (χ ^ k) (a - t))
  have hD : IsIntegral ℤ D := by
    unfold D
    exact IsIntegral.sum (fun a : ZMod p => u a ^ 2)
      (fun a _ha => (hu a).pow 2)
  have hB : IsIntegral ℤ B := by
    unfold B
    exact IsIntegral.sum (fun z : P => u z.1 * u z.2)
      (fun z _hz => (hu z.1).mul (hu z.2))
  have hX : IsIntegral ℤ X := by
    unfold X w
    exact IsIntegral.sum
      (fun x : E =>
        (χE ^ m) x * (χE ^ n) (x - 1) *
          (χE ^ k) (x - algebraMap (ZMod p) E t))
      (fun x _hx =>
        ((isIntegral_finiteFieldMulChar_apply (χE ^ m) x).mul
          (isIntegral_finiteFieldMulChar_apply (χE ^ n) (x - 1))).mul
            (isIntegral_finiteFieldMulChar_apply (χE ^ k)
              (x - algebraMap (ZMod p) E t)))
  rw [hdet]
  exact (hD.add hB).add hX

/-- After the determinant integrality theorem, the exact remaining canonical
Legendre data consist only of the root weight bound and the literal
all-extension recurrence. -/
def PrimePowerLegendreCanonicalWeightRecurrenceConditions
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) : Prop :=
  (∀ a ∈ primePowerLegendreCanonicalEigenvalues p χ m n k t,
      ‖a‖ ≤ Real.sqrt p) ∧
  ∀ q : ℕ,
    primePowerLegendreExtensionCorrelation p χ m n k t (q + 2) =
      primePowerLegendreCharacteristicTrace p χ m n k t *
          primePowerLegendreExtensionCorrelation p χ m n k t (q + 1) -
        primePowerLegendreCharacteristicDeterminant p χ m n k t *
          primePowerLegendreExtensionCorrelation p χ m n k t q

theorem primePowerLegendreCanonicalDeterminantConditions_iff_weightRecurrence
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    PrimePowerLegendreCanonicalDeterminantConditions p χ m n k t ↔
      PrimePowerLegendreCanonicalWeightRecurrenceConditions p χ m n k t := by
  constructor
  · rintro ⟨_hdet, hweight, hrecurrence⟩
    exact ⟨hweight, hrecurrence⟩
  · rintro ⟨hweight, hrecurrence⟩
    exact ⟨primePowerLegendreCharacteristicDeterminant_integral_unconditional
      p χ m n k t, hweight, hrecurrence⟩

theorem nonempty_primePowerLegendreSpectrum_iff_canonicalWeightRecurrence
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p} :
    Nonempty (PrimePowerLegendreSpectrum p χ m n k t) ↔
      PrimePowerLegendreCanonicalWeightRecurrenceConditions p χ m n k t := by
  rw [nonempty_primePowerLegendreSpectrum_iff_canonicalDeterminantConditions,
    primePowerLegendreCanonicalDeterminantConditions_iff_weightRecurrence]

/-- The global three-root Legendre source after deleting the now-unconditional
determinant-integrality conjunct. -/
def TaoPrimePowerLegendreCanonicalWeightRecurrenceConditions : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p),
    χ ≠ 1 → 0 < m → 0 < n → 0 < k →
      m < orderOf χ → n < orderOf χ → k < orderOf χ →
      t ≠ 0 → t ≠ 1 → ¬orderOf χ ∣ m + n + k →
        PrimePowerLegendreCanonicalWeightRecurrenceConditions p χ m n k t

theorem taoPrimePowerLegendreCanonicalDeterminantConditions_iff_weightRecurrence :
    TaoPrimePowerLegendreCanonicalDeterminantConditions ↔
      TaoPrimePowerLegendreCanonicalWeightRecurrenceConditions := by
  constructor
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum
    exact (primePowerLegendreCanonicalDeterminantConditions_iff_weightRecurrence
      p χ m n k t).mp
        (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum)
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum
    exact (primePowerLegendreCanonicalDeterminantConditions_iff_weightRecurrence
      p χ m n k t).mpr
        (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum)

theorem taoPrimePowerLegendreSpectrum_iff_canonicalWeightRecurrence :
    TaoPrimePowerLegendreSpectrum ↔
      TaoPrimePowerLegendreCanonicalWeightRecurrenceConditions := by
  rw [taoPrimePowerLegendreSpectrum_iff_canonicalDeterminantConditions,
    taoPrimePowerLegendreCanonicalDeterminantConditions_iff_weightRecurrence]

/-- The complete residual after determinant integrality is discharged:
canonical-root weight/recurrence data in the three-root case and explicit
root-multiset spectra in the higher-root case. -/
def TaoPrimeCanonicalWeightRecurrenceLegendreAndRootMultisetSpectra : Prop :=
  TaoPrimePowerLegendreCanonicalWeightRecurrenceConditions ∧
    TaoPrimeKummerExplicitRootMultisetSpectrumFourRootsOrMore

theorem taoPrimeCanonicalDeterminantLegendreAndRootMultisetSpectra_iff_weightRecurrence :
    TaoPrimeCanonicalDeterminantLegendreAndRootMultisetSpectra ↔
      TaoPrimeCanonicalWeightRecurrenceLegendreAndRootMultisetSpectra := by
  rw [TaoPrimeCanonicalDeterminantLegendreAndRootMultisetSpectra,
    TaoPrimeCanonicalWeightRecurrenceLegendreAndRootMultisetSpectra,
    taoPrimePowerLegendreCanonicalDeterminantConditions_iff_weightRecurrence]

theorem TaoPrimeCanonicalWeightRecurrenceLegendreAndRootMultisetSpectra.toFull
    (h : TaoPrimeCanonicalWeightRecurrenceLegendreAndRootMultisetSpectra) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeCanonicalDeterminantLegendreAndRootMultisetSpectra.toFull
    (taoPrimeCanonicalDeterminantLegendreAndRootMultisetSpectra_iff_weightRecurrence.mpr h)

end
end Tao2026
