import Tao2026.BurgessWeilPrimeThreeRoots

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

/-- The canonical analytic input left by the four-root Möbius reduction.
The fourth local monodromy is the inverse of `α * β * δ`, so all four
characters are required to be nontrivial. -/
def TaoPrimeThreePointHypergeometricWeilBound : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β δ : MulChar (ZMod p) ℂ) (lam mu : ZMod p),
    α ≠ 1 → β ≠ 1 → δ ≠ 1 → α * β * δ ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → lam ≠ mu →
    ‖∑ y : ZMod p, α y * β (y - lam) * δ (y - mu)‖ ≤
      2 * Real.sqrt p

/-- The canonical three-point Weil estimate implies the expected four-root
bound, with one unit of loss for the point deleted by the Möbius map. -/
theorem norm_fourRootMulCharSum_le_two_mul_sqrt_add_one
    (hweil : TaoPrimeThreePointHypergeometricWeilBound)
    (p : ℕ) [NeZero p] [Fact p.Prime]
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
    hweil p α β δ lam mu hα hβ hδ hαβδ hlam hmu hlammu
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
    (hweil : TaoPrimeThreePointHypergeometricWeilBound)
    (p : ℕ) [NeZero p] [Fact p.Prime]
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
    hweil p (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l)
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

end

end Tao2026
