import Tao2026.BurgessWeilPrimeLargeCharacteristic

/-!
# The four-active-root prime Burgess sum

For four active roots whose character exponents multiply to the trivial
character, the same fractional-linear substitution used in the three-root
case sends one root to infinity.  The denominator character cancels exactly,
leaving a canonical three-point (hypergeometric) character sum and one
deleted point.

This file proves that algebraic reduction.  It isolates the genuinely
analytic four-root input from the polynomial bookkeeping used by Burgess.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

set_option maxHeartbeats 800000 in
/-- The pointwise four-root Möbius reduction away from the deleted point. -/
theorem fourRootMobius_term
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ : MulChar (ZMod p) ℂ) (hprod : α * β * γ * δ = 1)
    (a b c d : ZMod p) (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (y : ZMod p) (hy : y ≠ 1) :
    let e := threeRootMobiusEquiv p a c hac
    let lam := (a - b) / (c - b)
    let mu := (a - d) / (c - d)
    α (e.symm y - a) * β (e.symm y - b) * γ (e.symm y - c) *
        δ (e.symm y - d) =
      (α (c - a) * β (c - b) * γ (c - a) * δ (c - d)) *
        (α y * β (y - lam) * δ (y - mu)) := by
  dsimp only
  rw [threeRootMobiusEquiv_symm_apply, if_neg hy]
  have hden : y - 1 ≠ 0 := sub_ne_zero.mpr hy
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr hbc.symm
  have hcd : c - d ≠ 0 := sub_ne_zero.mpr hdc.symm
  have hxa : (y * c - a) / (y - 1) - a =
      y * (c - a) / (y - 1) := by field_simp; ring
  have hxb : (y * c - a) / (y - 1) - b =
      (c - b) * (y - (a - b) / (c - b)) / (y - 1) := by
    field_simp
    ring
  have hxc : (y * c - a) / (y - 1) - c =
      (c - a) / (y - 1) := by field_simp; ring
  have hxd : (y * c - a) / (y - 1) - d =
      (c - d) * (y - (a - d) / (c - d)) / (y - 1) := by
    field_simp
    ring
  rw [hxa, hxb, hxc, hxd]
  have hmapdivα (u v : ZMod p) : α (u / v) = α u / α v := by
    exact map_div₀ α.toMonoidWithZeroHom u v
  have hmapdivβ (u v : ZMod p) : β (u / v) = β u / β v := by
    exact map_div₀ β.toMonoidWithZeroHom u v
  have hmapdivγ (u v : ZMod p) : γ (u / v) = γ u / γ v := by
    exact map_div₀ γ.toMonoidWithZeroHom u v
  have hmapdivδ (u v : ZMod p) : δ (u / v) = δ u / δ v := by
    exact map_div₀ δ.toMonoidWithZeroHom u v
  rw [hmapdivα, map_mul, hmapdivβ, map_mul, hmapdivγ,
    hmapdivδ, map_mul]
  have hcancel :
      α (y - 1) * β (y - 1) * γ (y - 1) * δ (y - 1) = 1 := by
    rw [← MulChar.mul_apply, ← MulChar.mul_apply, ← MulChar.mul_apply, hprod]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hden)
  have hα : α (y - 1) ≠ 0 := by
    intro h
    rw [h, zero_mul, zero_mul, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hβ : β (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hγ : γ (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hδ : δ (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcancel
    exact zero_ne_one hcancel
  field_simp [hα, hβ, hγ, hδ]
  linear_combination
    -(α y * α (c - a) * β (c - b) *
      β ((y * (c - b) - (a - b)) / (c - b)) * γ (c - a) *
      δ (c - d) * δ ((y * (c - d) - (a - d)) / (c - d))) * hcancel

/-- A four-root character sum is a canonical three-point sum with one
deleted point, up to a character-valued constant. -/
theorem fourRootMulCharSum_eq_threePointSum_sub
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ : MulChar (ZMod p) ℂ) (hprod : α * β * γ * δ = 1)
    (a b c d : ZMod p) (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c) :
    let lam := (a - b) / (c - b)
    let mu := (a - d) / (c - d)
    (∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d)) =
      (α (c - a) * β (c - b) * γ (c - a) * δ (c - d)) *
        ((∑ y : ZMod p, α y * β (y - lam) * δ (y - mu)) -
          β (1 - lam) * δ (1 - mu)) := by
  dsimp only
  let e := threeRootMobiusEquiv p a c hac
  let f : ZMod p → ℂ := fun x =>
    α (x - a) * β (x - b) * γ (x - c) * δ (x - d)
  let g : ZMod p → ℂ := fun y =>
    α y * β (y - (a - b) / (c - b)) *
      δ (y - (a - d) / (c - d))
  let C : ℂ :=
    α (c - a) * β (c - b) * γ (c - a) * δ (c - d)
  have hone : f (e.symm 1) = 0 := by
    simp [f, e, γ.map_zero]
  have hterm (y : ZMod p) (hy : y ∈ Finset.univ.erase 1) :
      f (e.symm y) = C * g y := by
    have hyOne : y ≠ 1 := by simpa using hy
    simpa [f, g, C, e] using
      fourRootMobius_term p α β γ δ hprod a b c d hac hbc hdc y hyOne
  calc
    (∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d)) =
        ∑ x : ZMod p, f x := by rfl
    _ = ∑ y : ZMod p, f (e.symm y) :=
      (Equiv.sum_comp e.symm f).symm
    _ = ∑ y ∈ Finset.univ.erase 1, f (e.symm y) := by
      exact (Finset.sum_erase (s := Finset.univ)
        (f := fun y => f (e.symm y)) hone).symm
    _ = C * ∑ y ∈ Finset.univ.erase 1, g y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      exact hterm
    _ = C * ((∑ y : ZMod p, g y) - g 1) := by
      congr 1
      have h := Finset.sum_erase_add Finset.univ g
        (Finset.mem_univ (1 : ZMod p))
      linear_combination h
    _ = _ := by simp [C, g, MulChar.map_one]

/-- The canonical analytic input at one prime left by the four-root Möbius
reduction.  The fourth local monodromy is the inverse of `α * β * δ`, so all
four characters are required to be nontrivial. -/
def TaoPrimeThreePointHypergeometricWeilBoundAt
    (p : ℕ) [NeZero p] [Fact p.Prime] : Prop :=
  ∀ (α β δ : MulChar (ZMod p) ℂ) (lam mu : ZMod p),
    α ≠ 1 → β ≠ 1 → δ ≠ 1 → α * β * δ ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → lam ≠ mu →
    ‖∑ y : ZMod p, α y * β (y - lam) * δ (y - mu)‖ ≤
      2 * Real.sqrt p

def TaoPrimeThreePointHypergeometricWeilBound : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime],
    TaoPrimeThreePointHypergeometricWeilBoundAt p

/-- The only range needed after the small-characteristic disposal. -/
def TaoPrimeThreePointHypergeometricWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime],
    64 < p → TaoPrimeThreePointHypergeometricWeilBoundAt p

/-- The source-shaped version: all three finite local characters are powers
of the one Burgess character. -/
def TaoPrimePowerThreePointHypergeometricWeilBoundAt
    (p : ℕ) [NeZero p] [Fact p.Prime] : Prop :=
  ∀ (χ : MulChar (ZMod p) ℂ) (m n l : ℕ) (lam mu : ZMod p),
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ l ≠ 1 → χ ^ (m + n + l) ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → lam ≠ mu →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ l) (y - mu)‖ ≤
      2 * Real.sqrt p

def TaoPrimePowerThreePointHypergeometricWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime],
    64 < p → TaoPrimePowerThreePointHypergeometricWeilBoundAt p

/-- A finite exponent-range formulation of the source-shaped analytic input. -/
def TaoPrimeReducedPowerThreePointHypergeometricWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime], 64 < p →
    ∀ (χ : MulChar (ZMod p) ℂ) (m n l : ℕ) (lam mu : ZMod p),
    m < orderOf χ → n < orderOf χ → l < orderOf χ →
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ l ≠ 1 → χ ^ (m + n + l) ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → lam ≠ mu →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ l) (y - mu)‖ ≤
      2 * Real.sqrt p

/-- Scaling by the first nonzero marked point puts a three-point character
sum into the Legendre normal form with finite points `0`, `1`, and one
cross-ratio parameter. -/
theorem threePointMulCharSum_eq_legendreForm
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β δ : MulChar (ZMod p) ℂ) (lam mu : ZMod p) (hlam : lam ≠ 0) :
    (∑ y : ZMod p, α y * β (y - lam) * δ (y - mu)) =
      (α lam * β lam * δ lam) *
        ∑ t : ZMod p, α t * β (t - 1) * δ (t - mu / lam) := by
  let e : ZMod p ≃ ZMod p := Equiv.mulLeft₀ lam hlam
  calc
    (∑ y : ZMod p, α y * β (y - lam) * δ (y - mu)) =
        ∑ t : ZMod p, α (e t) * β (e t - lam) * δ (e t - mu) :=
      (Equiv.sum_comp e
        (fun y : ZMod p => α y * β (y - lam) * δ (y - mu))).symm
    _ = (α lam * β lam * δ lam) *
        ∑ t : ZMod p, α t * β (t - 1) * δ (t - mu / lam) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have hsubOne : lam * t - lam = lam * (t - 1) := by ring
      have hsubMu : lam * t - mu = lam * (t - mu / lam) := by
        field_simp
      dsimp [e]
      rw [hsubOne, hsubMu, map_mul, map_mul, map_mul]
      ring

/-- The final one-parameter analytic boundary for four active roots. -/
def TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime], 64 < p →
    ∀ (χ : MulChar (ZMod p) ℂ) (m n l : ℕ) (t : ZMod p),
    m < orderOf χ → n < orderOf χ → l < orderOf χ →
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ l ≠ 1 → χ ^ (m + n + l) ≠ 1 →
    t ≠ 0 → t ≠ 1 →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ l) (y - t)‖ ≤
      2 * Real.sqrt p

theorem TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour.toThreePoint
    (hweil :
      TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour) :
    TaoPrimeReducedPowerThreePointHypergeometricWeilBoundAboveSixtyFour := by
  intro p _ _ hp χ m n l lam mu hm hn hl hpowM hpowN hpowL hpowMNL
    hlam hmu hlammu
  let t : ZMod p := mu / lam
  have ht0 : t ≠ 0 := div_ne_zero hmu hlam
  have ht1 : t ≠ 1 := by
    intro heq
    apply hlammu
    dsimp [t] at heq
    rw [div_eq_one_iff_eq hlam] at heq
    exact heq.symm
  have hbound := hweil p hp χ m n l t hm hn hl
    hpowM hpowN hpowL hpowMNL ht0 ht1
  rw [threePointMulCharSum_eq_legendreForm
    p (χ ^ m) (χ ^ n) (χ ^ l) lam mu hlam]
  simp only [norm_mul]
  have hC :
      ‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ l) lam‖ ≤ 1 := by
    calc
      ‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ l) lam‖ ≤
          1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one (χ ^ m) lam
        · exact DirichletCharacter.norm_le_one (χ ^ n) lam
        · exact DirichletCharacter.norm_le_one (χ ^ l) lam
      _ = 1 := by norm_num
  calc
    (‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ l) lam‖) *
          ‖∑ y : ZMod p,
            (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ l) (y - mu / lam)‖ ≤
        1 * ‖∑ y : ZMod p,
          (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ l) (y - mu / lam)‖ := by
      gcongr
    _ ≤ 2 * Real.sqrt p := by simpa [t] using hbound

theorem TaoPrimeReducedPowerThreePointHypergeometricWeilBoundAboveSixtyFour.toPower
    (hweil :
      TaoPrimeReducedPowerThreePointHypergeometricWeilBoundAboveSixtyFour) :
    TaoPrimePowerThreePointHypergeometricWeilBoundAboveSixtyFour := by
  intro p _ _ hp χ m n l lam mu hpowM hpowN hpowL hpowMNL
    hlam hmu hlammu
  let m' := m % orderOf χ
  let n' := n % orderOf χ
  let l' := l % orderOf χ
  have hord : 0 < orderOf χ := orderOf_pos χ
  have hmLt : m' < orderOf χ := Nat.mod_lt m hord
  have hnLt : n' < orderOf χ := Nat.mod_lt n hord
  have hlLt : l' < orderOf χ := Nat.mod_lt l hord
  have hmEq : χ ^ m' = χ ^ m := by
    exact pow_mod_orderOf χ m
  have hnEq : χ ^ n' = χ ^ n := by
    exact pow_mod_orderOf χ n
  have hlEq : χ ^ l' = χ ^ l := by
    exact pow_mod_orderOf χ l
  have hpowM' : χ ^ m' ≠ 1 := by simpa only [hmEq] using hpowM
  have hpowN' : χ ^ n' ≠ 1 := by simpa only [hnEq] using hpowN
  have hpowL' : χ ^ l' ≠ 1 := by simpa only [hlEq] using hpowL
  have hsumEq : χ ^ (m' + n' + l') = χ ^ (m + n + l) := by
    rw [pow_add, pow_add, pow_add, pow_add, hmEq, hnEq, hlEq]
  have hpowMNL' : χ ^ (m' + n' + l') ≠ 1 := by
    simpa only [hsumEq] using hpowMNL
  have hbound := hweil p hp χ m' n' l' lam mu hmLt hnLt hlLt
    hpowM' hpowN' hpowL' hpowMNL' hlam hmu hlammu
  simpa only [hmEq, hnEq, hlEq] using hbound

/-- Once the canonical three-point sum itself is bounded, the Möbius
identity and the deleted-point estimate need no further character theory. -/
theorem norm_fourRootMulCharSum_le_two_mul_sqrt_add_one_of_threePoint
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ : MulChar (ZMod p) ℂ) (hprod : α * β * γ * δ = 1)
    (a b c d : ZMod p) (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (hthree :
      ‖∑ y : ZMod p,
        α y * β (y - (a - b) / (c - b)) *
          δ (y - (a - d) / (c - d))‖ ≤ 2 * Real.sqrt p) :
    ‖∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d)‖ ≤
      2 * Real.sqrt p + 1 := by
  rw [fourRootMulCharSum_eq_threePointSum_sub
    p α β γ δ hprod a b c d hac hbc hdc]
  simp only [norm_mul]
  have hC :
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ ≤ 1 := by
    calc
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ ≤
          1 * 1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one α (c - a)
        · exact DirichletCharacter.norm_le_one β (c - b)
        · exact DirichletCharacter.norm_le_one γ (c - a)
        · exact DirichletCharacter.norm_le_one δ (c - d)
      _ = 1 := by norm_num
  have hdeleted :
      ‖β (1 - (a - b) / (c - b)) *
        δ (1 - (a - d) / (c - d))‖ ≤ 1 := by
    rw [norm_mul]
    calc
      ‖β (1 - (a - b) / (c - b))‖ *
          ‖δ (1 - (a - d) / (c - d))‖ ≤ 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one β _
        · exact DirichletCharacter.norm_le_one δ _
      _ = 1 := by norm_num
  calc
    (‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖) *
          ‖(∑ y : ZMod p,
              α y * β (y - (a - b) / (c - b)) *
                δ (y - (a - d) / (c - d))) -
            β (1 - (a - b) / (c - b)) *
              δ (1 - (a - d) / (c - d))‖ ≤
        1 * ‖(∑ y : ZMod p,
              α y * β (y - (a - b) / (c - b)) *
                δ (y - (a - d) / (c - d))) -
            β (1 - (a - b) / (c - b)) *
              δ (1 - (a - d) / (c - d))‖ := by
      gcongr
    _ ≤ ‖∑ y : ZMod p,
          α y * β (y - (a - b) / (c - b)) *
            δ (y - (a - d) / (c - d))‖ +
          ‖β (1 - (a - b) / (c - b)) *
            δ (1 - (a - d) / (c - d))‖ := by
      simpa using norm_sub_le
        (∑ y : ZMod p,
          α y * β (y - (a - b) / (c - b)) *
            δ (y - (a - d) / (c - d)))
        (β (1 - (a - b) / (c - b)) *
          δ (1 - (a - d) / (c - d)))
    _ ≤ 2 * Real.sqrt p + 1 := add_le_add hthree hdeleted

/-- The canonical three-point Weil estimate implies the expected four-root
bound, with one unit of loss for the point deleted by the Möbius map. -/
theorem norm_fourRootMulCharSum_le_two_mul_sqrt_add_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimeThreePointHypergeometricWeilBoundAt p)
    (α β γ δ : MulChar (ZMod p) ℂ)
    (hα : α ≠ 1) (hβ : β ≠ 1) (hγ : γ ≠ 1) (hδ : δ ≠ 1)
    (hprod : α * β * γ * δ = 1)
    (a b c d : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hdc : d ≠ c) :
    ‖∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d)‖ ≤
      2 * Real.sqrt p + 1 := by
  let lam : ZMod p := (a - b) / (c - b)
  let mu : ZMod p := (a - d) / (c - d)
  have hlam : lam ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hbc.symm)
  have hmu : mu ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr had) (sub_ne_zero.mpr hdc.symm)
  have hlammu : lam ≠ mu := by
    intro heq
    have hcb : c - b ≠ 0 := sub_ne_zero.mpr hbc.symm
    have hcd : c - d ≠ 0 := sub_ne_zero.mpr hdc.symm
    dsimp [lam, mu] at heq
    rw [div_eq_div_iff hcb hcd] at heq
    have hzero : (a - c) * (b - d) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp hzero with hac' | hbd'
    · exact hac (sub_eq_zero.mp hac')
    · exact hbd (sub_eq_zero.mp hbd')
  have hαβδ : α * β * δ ≠ 1 := by
    intro heq
    apply hγ
    calc
      γ = 1 * γ := by simp
      _ = (α * β * δ) * γ := by rw [heq]
      _ = α * β * γ * δ := by ac_rfl
      _ = 1 := hprod
  rw [fourRootMulCharSum_eq_threePointSum_sub
    p α β γ δ hprod a b c d hac hbc hdc]
  simp only [norm_mul]
  have hC :
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ ≤ 1 := by
    calc
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ ≤
          1 * 1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one α (c - a)
        · exact DirichletCharacter.norm_le_one β (c - b)
        · exact DirichletCharacter.norm_le_one γ (c - a)
        · exact DirichletCharacter.norm_le_one δ (c - d)
      _ = 1 := by norm_num
  have hthree :
      ‖∑ y : ZMod p, α y * β (y - lam) * δ (y - mu)‖ ≤
        2 * Real.sqrt p :=
    hweil α β δ lam mu hα hβ hδ hαβδ hlam hmu hlammu
  have hdeleted : ‖β (1 - lam) * δ (1 - mu)‖ ≤ 1 := by
    rw [norm_mul]
    calc
      ‖β (1 - lam)‖ * ‖δ (1 - mu)‖ ≤ 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one β (1 - lam)
        · exact DirichletCharacter.norm_le_one δ (1 - mu)
      _ = 1 := by norm_num
  calc
    (‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖) *
          ‖(∑ y : ZMod p, α y * β (y - lam) * δ (y - mu)) -
            β (1 - lam) * δ (1 - mu)‖ ≤
        1 * ‖(∑ y : ZMod p, α y * β (y - lam) * δ (y - mu)) -
          β (1 - lam) * δ (1 - mu)‖ := by
      gcongr
    _ ≤ ‖∑ y : ZMod p, α y * β (y - lam) * δ (y - mu)‖ +
          ‖β (1 - lam) * δ (1 - mu)‖ := by
      simpa using norm_sub_le
        (∑ y : ZMod p, α y * β (y - lam) * δ (y - mu))
        (β (1 - lam) * δ (1 - mu))
    _ ≤ 2 * Real.sqrt p + 1 := add_le_add hthree hdeleted

/-- Exactly four active roots reduce to the canonical three-point analytic
input.  Divisibility of the total degree supplies the cancellation of the
four character exponents. -/
theorem norm_primeActiveRootCharacterSum_le_two_mul_sqrt_add_one_of_card_eq_four
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimeThreePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 4) :
    ‖primeActiveRootCharacterSum p χ P‖ ≤ 2 * Real.sqrt p + 1 := by
  obtain ⟨u, v, w, z, huv, huw, huz, hvw, hvz, hwz, hroots⟩ :=
    Finset.card_eq_four.mp hcard
  have huActive : u ∈ primeActiveRoots p χ P := by simp [hroots]
  have hvActive : v ∈ primeActiveRoots p χ P := by simp [hroots]
  have hwActive : w ∈ primeActiveRoots p χ P := by simp [hroots]
  have hzActive : z ∈ primeActiveRoots p χ P := by simp [hroots]
  have huRoot : u ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P huActive
  have hvRoot : v ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hvActive
  have hwRoot : w ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hwActive
  have hzRoot : z ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hzActive
  let m := P.roots.count u
  let n := P.roots.count v
  let k := P.roots.count w
  let l := P.roots.count z
  have hm : m ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp huRoot)).ne'
  have hn : n ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hvRoot)).ne'
  have hk : k ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hwRoot)).ne'
  have hl : l ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hzRoot)).ne'
  have hmActive : ¬orderOf χ ∣ m := (Finset.mem_filter.mp huActive).2
  have hnActive : ¬orderOf χ ∣ n := (Finset.mem_filter.mp hvActive).2
  have hkActive : ¬orderOf χ ∣ k := (Finset.mem_filter.mp hwActive).2
  have hlActive : ¬orderOf χ ∣ l := (Finset.mem_filter.mp hzActive).2
  have hpowM : χ ^ m ≠ 1 := by
    intro heq
    exact hmActive (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowN : χ ^ n ≠ 1 := by
    intro heq
    exact hnActive (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowK : χ ^ k ≠ 1 := by
    intro heq
    exact hkActive (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowL : χ ^ l ≠ 1 := by
    intro heq
    exact hlActive (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hsum := orderOf_dvd_sum_primeActiveRoots_count
    p χ P hP hdegree
  have hmnkl : orderOf χ ∣ m + n + k + l := by
    simpa [hroots, huv, huw, huz, hvw, hvz, hwz, m, n, k, l,
      add_assoc, add_comm, add_left_comm] using hsum
  have hprod : (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add]
    exact orderOf_dvd_iff_pow_eq_one.mp hmnkl
  have hfour := norm_fourRootMulCharSum_le_two_mul_sqrt_add_one
    p hweil (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l)
      hpowM hpowN hpowK hpowL hprod u v w z
      huv huw huz hvw hvz hwz.symm
  unfold primeActiveRootCharacterSum
  rw [hroots]
  convert hfour using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro x hx
  simp [huv, huw, huz, hvw, hvz, hwz]
  rw [MulChar.pow_apply' χ hm, MulChar.pow_apply' χ hn,
    MulChar.pow_apply' χ hk, MulChar.pow_apply' χ hl]
  simp [m, n, k, l, Polynomial.count_roots]
  ac_rfl

/-- Source-shaped four-root reduction: the canonical estimate is required
only for three powers of the single ambient Burgess character. -/
theorem norm_primeActiveRootCharacterSum_le_two_mul_sqrt_add_one_of_card_eq_four_power
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerThreePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 4) :
    ‖primeActiveRootCharacterSum p χ P‖ ≤ 2 * Real.sqrt p + 1 := by
  obtain ⟨u, v, w, z, huv, huw, huz, hvw, hvz, hwz, hroots⟩ :=
    Finset.card_eq_four.mp hcard
  have huActive : u ∈ primeActiveRoots p χ P := by simp [hroots]
  have hvActive : v ∈ primeActiveRoots p χ P := by simp [hroots]
  have hwActive : w ∈ primeActiveRoots p χ P := by simp [hroots]
  have hzActive : z ∈ primeActiveRoots p χ P := by simp [hroots]
  have huRoot : u ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P huActive
  have hvRoot : v ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hvActive
  have hwRoot : w ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hwActive
  have hzRoot : z ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hzActive
  let m := P.roots.count u
  let n := P.roots.count v
  let k := P.roots.count w
  let l := P.roots.count z
  have hm : m ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp huRoot)).ne'
  have hn : n ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hvRoot)).ne'
  have hk : k ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hwRoot)).ne'
  have hl : l ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hzRoot)).ne'
  have hmActive : ¬orderOf χ ∣ m := (Finset.mem_filter.mp huActive).2
  have hnActive : ¬orderOf χ ∣ n := (Finset.mem_filter.mp hvActive).2
  have hkActive : ¬orderOf χ ∣ k := (Finset.mem_filter.mp hwActive).2
  have hlActive : ¬orderOf χ ∣ l := (Finset.mem_filter.mp hzActive).2
  have hpowM : χ ^ m ≠ 1 := by
    intro heq
    exact hmActive (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowN : χ ^ n ≠ 1 := by
    intro heq
    exact hnActive (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowK : χ ^ k ≠ 1 := by
    intro heq
    exact hkActive (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowL : χ ^ l ≠ 1 := by
    intro heq
    exact hlActive (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hsum := orderOf_dvd_sum_primeActiveRoots_count
    p χ P hP hdegree
  have hmnkl : orderOf χ ∣ m + n + k + l := by
    simpa [hroots, huv, huw, huz, hvw, hvz, hwz, m, n, k, l,
      add_assoc, add_comm, add_left_comm] using hsum
  have hprod : (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add]
    exact orderOf_dvd_iff_pow_eq_one.mp hmnkl
  have hpowMNL : χ ^ (m + n + l) ≠ 1 := by
    intro heq
    apply hpowK
    calc
      χ ^ k = 1 * χ ^ k := by simp
      _ = χ ^ (m + n + l) * χ ^ k := by rw [heq]
      _ = (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) := by
        rw [pow_add, pow_add]
        ac_rfl
      _ = 1 := hprod
  let lam : ZMod p := (u - v) / (w - v)
  let mu : ZMod p := (u - z) / (w - z)
  have hlam : lam ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr huv) (sub_ne_zero.mpr hvw.symm)
  have hmu : mu ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr huz) (sub_ne_zero.mpr hwz)
  have hlammu : lam ≠ mu := by
    intro heq
    have hwv : w - v ≠ 0 := sub_ne_zero.mpr hvw.symm
    have hwz' : w - z ≠ 0 := sub_ne_zero.mpr hwz
    dsimp [lam, mu] at heq
    rw [div_eq_div_iff hwv hwz'] at heq
    have hzero : (u - w) * (v - z) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp hzero with huw' | hvz'
    · exact huw (sub_eq_zero.mp huw')
    · exact hvz (sub_eq_zero.mp hvz')
  have hthree :
      ‖∑ y : ZMod p,
        (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ l) (y - mu)‖ ≤
          2 * Real.sqrt p :=
    hweil χ m n l lam mu hpowM hpowN hpowL hpowMNL hlam hmu hlammu
  have hfour := norm_fourRootMulCharSum_le_two_mul_sqrt_add_one_of_threePoint
    p (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l) hprod u v w z
      huw hvw hwz.symm (by simpa [lam, mu] using hthree)
  unfold primeActiveRootCharacterSum
  rw [hroots]
  convert hfour using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro x hx
  simp [huv, huw, huz, hvw, hvz, hwz]
  rw [MulChar.pow_apply' χ hm, MulChar.pow_apply' χ hn,
    MulChar.pow_apply' χ hk, MulChar.pow_apply' χ hl]
  simp [m, n, k, l, Polynomial.count_roots]
  ac_rfl

theorem norm_filter_primeActiveRootProduct_le_of_card_eq_four_degree
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimeThreePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 4) :
    ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
        x ∉ primeInactiveRoots p χ P),
      ∏ b ∈ primeActiveRoots p χ P,
        χ (x - b) ^ P.roots.count b‖ ≤
      2 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card := by
  let f : ZMod p → ℂ := fun x =>
    ∏ b ∈ primeActiveRoots p χ P,
      χ (x - b) ^ P.roots.count b
  let I := primeInactiveRoots p χ P
  have hsplit :
      (∑ x ∈ I, f x) +
          (∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ∉ I), f x) =
        ∑ x : ZMod p, f x := by
    simpa [I] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x : ZMod p => x ∈ I) f)
  have hrewrite :
      (∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ∉ I), f x) =
        (∑ x : ZMod p, f x) - ∑ x ∈ I, f x := by
    linear_combination hsplit
  have htotal : ‖∑ x : ZMod p, f x‖ ≤ 2 * Real.sqrt p + 1 := by
    simpa [f, primeActiveRootCharacterSum] using
      norm_primeActiveRootCharacterSum_le_two_mul_sqrt_add_one_of_card_eq_four
        p hweil χ P hP hdegree hcard
  have hbad : ‖∑ x ∈ I, f x‖ ≤ I.card := by
    calc
      ‖∑ x ∈ I, f x‖ ≤ ∑ x ∈ I, ‖f x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ I, (1 : ℝ) := by
        exact Finset.sum_le_sum fun x hx => by
          simpa [f] using norm_primeActiveRootProduct_le_one p χ P x
      _ = I.card := by simp
  change ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ∉ I), f x‖ ≤ _
  rw [hrewrite]
  exact (norm_sub_le _ _).trans (add_le_add htotal hbad)

theorem norm_filter_primeActiveRootProduct_le_of_card_eq_four_degree_power
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerThreePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 4) :
    ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
        x ∉ primeInactiveRoots p χ P),
      ∏ b ∈ primeActiveRoots p χ P,
        χ (x - b) ^ P.roots.count b‖ ≤
      2 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card := by
  let f : ZMod p → ℂ := fun x =>
    ∏ b ∈ primeActiveRoots p χ P,
      χ (x - b) ^ P.roots.count b
  let I := primeInactiveRoots p χ P
  have hsplit :
      (∑ x ∈ I, f x) +
          (∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ∉ I), f x) =
        ∑ x : ZMod p, f x := by
    simpa [I] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x : ZMod p => x ∈ I) f)
  have hrewrite :
      (∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ∉ I), f x) =
        (∑ x : ZMod p, f x) - ∑ x ∈ I, f x := by
    linear_combination hsplit
  have htotal : ‖∑ x : ZMod p, f x‖ ≤ 2 * Real.sqrt p + 1 := by
    simpa [f, primeActiveRootCharacterSum] using
      norm_primeActiveRootCharacterSum_le_two_mul_sqrt_add_one_of_card_eq_four_power
        p hweil χ P hP hdegree hcard
  have hbad : ‖∑ x ∈ I, f x‖ ≤ I.card := by
    calc
      ‖∑ x ∈ I, f x‖ ≤ ∑ x ∈ I, ‖f x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ I, (1 : ℝ) := by
        exact Finset.sum_le_sum fun x hx => by
          simpa [f] using norm_primeActiveRootProduct_le_one p χ P x
      _ = I.card := by simp
  change ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ∉ I), f x‖ ≤ _
  rw [hrewrite]
  exact (norm_sub_le _ _).trans (add_le_add htotal hbad)

/-- The canonical hypergeometric estimate discharges the split-polynomial
Weil target whenever there are exactly four active roots. -/
theorem primeSplitPolynomialWeilBound_of_card_activeRoots_eq_four_degree
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimeThreePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (_a : ZMod p) (_hχ : χ ≠ 1) (hP : P.Splits)
    (_hnot : ¬orderOf χ ∣ P.rootMultiplicity _a)
    (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 4) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
  have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
  have hrestricted :=
    norm_filter_primeActiveRootProduct_le_of_card_eq_four_degree
      p hweil χ P hP hdegree hcard
  have hrootCard : 4 ≤ P.roots.toFinset.card := by
    rw [← hcard]
    exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
  have hInactiveCard :
      (primeInactiveRoots p χ P).card ≤ P.roots.toFinset.card :=
    Finset.card_le_card (primeInactiveRoots_subset_roots p χ P)
  have hp : p.Prime := Fact.out
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hp.one_le
  have hroom :
      2 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
    have hInactiveCard' :
        ((primeInactiveRoots p χ P).card : ℝ) ≤
          (P.roots.toFinset.card : ℝ) := by exact_mod_cast hInactiveCard
    have hrootCard' : (4 : ℝ) ≤ P.roots.toFinset.card := by
      exact_mod_cast hrootCard
    push_cast
    nlinarith [Real.sqrt_nonneg (p : ℝ)]
  rw [primePolynomialCharacterCorrelation_eq_rootProduct p χ P hP,
    hsum, norm_mul]
  calc
    ‖χ P.leadingCoeff‖ *
          ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ ≤
        1 * ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ := by
      gcongr
      exact DirichletCharacter.norm_le_one χ P.leadingCoeff
    _ ≤ 2 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card := by
      simpa using hrestricted
    _ ≤ ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := hroom

theorem primeSplitPolynomialWeilBound_of_card_activeRoots_eq_four_degree_power
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerThreePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (_a : ZMod p) (_hχ : χ ≠ 1) (hP : P.Splits)
    (_hnot : ¬orderOf χ ∣ P.rootMultiplicity _a)
    (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 4) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
  have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
  have hrestricted :=
    norm_filter_primeActiveRootProduct_le_of_card_eq_four_degree_power
      p hweil χ P hP hdegree hcard
  have hrootCard : 4 ≤ P.roots.toFinset.card := by
    rw [← hcard]
    exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
  have hInactiveCard :
      (primeInactiveRoots p χ P).card ≤ P.roots.toFinset.card :=
    Finset.card_le_card (primeInactiveRoots_subset_roots p χ P)
  have hp : p.Prime := Fact.out
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hp.one_le
  have hroom :
      2 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
    have hInactiveCard' :
        ((primeInactiveRoots p χ P).card : ℝ) ≤
          (P.roots.toFinset.card : ℝ) := by exact_mod_cast hInactiveCard
    have hrootCard' : (4 : ℝ) ≤ P.roots.toFinset.card := by
      exact_mod_cast hrootCard
    push_cast
    nlinarith [Real.sqrt_nonneg (p : ℝ)]
  rw [primePolynomialCharacterCorrelation_eq_rootProduct p χ P hP,
    hsum, norm_mul]
  calc
    ‖χ P.leadingCoeff‖ *
          ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ ≤
        1 * ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ := by
      gcongr
      exact DirichletCharacter.norm_le_one χ P.leadingCoeff
    _ ≤ 2 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card := by
      simpa using hrestricted
    _ ≤ ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := hroom

/-- After the exact four-root normalization and the elementary
small-characteristic estimate, the unrestricted split-polynomial input is
needed only for at least five active roots in large characteristic. -/
def TaoPrimeSplitPolynomialWeilBoundFiveActiveRootsLargeCharacteristic : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) (a : ZMod p),
    χ ≠ 1 → P.Splits →
    ¬orderOf χ ∣ P.rootMultiplicity a →
    orderOf χ ∣ P.natDegree →
    5 ≤ (primeActiveRoots p χ P).card →
    4 * P.roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p

theorem TaoPrimeSplitPolynomialWeilBoundFiveActiveRootsLargeCharacteristic.toFourActiveRoots
    (hhyper : TaoPrimeThreePointHypergeometricWeilBound)
    (hweil : TaoPrimeSplitPolynomialWeilBoundFiveActiveRootsLargeCharacteristic) :
    TaoPrimeSplitPolynomialWeilBoundFourActiveRootsLargeCharacteristic := by
  intro p _ _ χ P a hχ hP hnot hdegree hactive hlarge
  by_cases hcard : (primeActiveRoots p χ P).card = 4
  · exact primeSplitPolynomialWeilBound_of_card_activeRoots_eq_four_degree
      p (hhyper p) χ P a hχ hP hnot hdegree hcard
  · exact hweil p χ P a hχ hP hnot hdegree (by omega) hlarge

theorem TaoPrimeSplitPolynomialWeilBoundFiveActiveRootsLargeCharacteristic.toComposite
    (hhyper : TaoPrimeThreePointHypergeometricWeilBound)
    (hweil : TaoPrimeSplitPolynomialWeilBoundFiveActiveRootsLargeCharacteristic) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (hweil.toFourActiveRoots hhyper).toComposite

end

end Tao2026
