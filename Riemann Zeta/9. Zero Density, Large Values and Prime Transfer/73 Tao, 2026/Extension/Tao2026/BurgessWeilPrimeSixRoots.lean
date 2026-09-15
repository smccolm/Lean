import Tao2026.BurgessWeilPrimeKummer

/-!
# Six active roots in the prime Burgess sum

This file isolates the source-shaped analytic endpoint left after sending one
of six degree-balanced active roots to infinity.  The five remaining local
characters are powers of the single Burgess character.  Their exponents may
be reduced modulo the character order, and scaling gives the finite marked
points `0`, `1`, `t`, `u`, and `v`.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The source-shaped five-point endpoint at one prime. -/
def TaoPrimePowerFivePointHypergeometricWeilBoundAt
    (p : ℕ) [NeZero p] [Fact p.Prime] : Prop :=
  ∀ (χ : MulChar (ZMod p) ℂ) (m n k l s : ℕ)
    (lam mu nu xi : ZMod p),
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 → χ ^ s ≠ 1 →
    χ ^ (m + n + k + l + s) ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → nu ≠ 0 → xi ≠ 0 →
    lam ≠ mu → lam ≠ nu → lam ≠ xi →
    mu ≠ nu → mu ≠ xi → nu ≠ xi →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ k) (y - mu) *
        (χ ^ l) (y - nu) * (χ ^ s) (y - xi)‖ ≤
      4 * Real.sqrt p

/-- The only characteristic range needed after the trivial-bound branch. -/
def TaoPrimePowerFivePointHypergeometricWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime],
    64 < p → TaoPrimePowerFivePointHypergeometricWeilBoundAt p

/-- Finite exponent-range form of the source-shaped five-point endpoint. -/
def TaoPrimeReducedPowerFivePointHypergeometricWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime], 64 < p →
    ∀ (χ : MulChar (ZMod p) ℂ) (m n k l s : ℕ)
      (lam mu nu xi : ZMod p),
    m < orderOf χ → n < orderOf χ → k < orderOf χ →
    l < orderOf χ → s < orderOf χ →
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 → χ ^ s ≠ 1 →
    χ ^ (m + n + k + l + s) ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → nu ≠ 0 → xi ≠ 0 →
    lam ≠ mu → lam ≠ nu → lam ≠ xi →
    mu ≠ nu → mu ≠ xi → nu ≠ xi →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ k) (y - mu) *
        (χ ^ l) (y - nu) * (χ ^ s) (y - xi)‖ ≤
      4 * Real.sqrt p

/-- Scaling by the first nonzero point puts a five-point sum into the
three-parameter Legendre form `0`, `1`, `t`, `u`, `v`. -/
theorem fivePointMulCharSum_eq_legendreForm
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε : MulChar (ZMod p) ℂ) (lam mu nu xi : ZMod p)
    (hlam : lam ≠ 0) :
    (∑ y : ZMod p,
      α y * β (y - lam) * γ (y - mu) * δ (y - nu) * ε (y - xi)) =
      (α lam * β lam * γ lam * δ lam * ε lam) *
        ∑ t : ZMod p,
          α t * β (t - 1) * γ (t - mu / lam) * δ (t - nu / lam) *
            ε (t - xi / lam) := by
  let e : ZMod p ≃ ZMod p := Equiv.mulLeft₀ lam hlam
  calc
    (∑ y : ZMod p,
        α y * β (y - lam) * γ (y - mu) * δ (y - nu) * ε (y - xi)) =
        ∑ t : ZMod p,
          α (e t) * β (e t - lam) * γ (e t - mu) * δ (e t - nu) *
            ε (e t - xi) :=
      (Equiv.sum_comp e
        (fun y : ZMod p =>
          α y * β (y - lam) * γ (y - mu) * δ (y - nu) * ε (y - xi))).symm
    _ = (α lam * β lam * γ lam * δ lam * ε lam) *
        ∑ t : ZMod p,
          α t * β (t - 1) * γ (t - mu / lam) * δ (t - nu / lam) *
            ε (t - xi / lam) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      have hsubOne : lam * t - lam = lam * (t - 1) := by ring
      have hsubMu : lam * t - mu = lam * (t - mu / lam) := by field_simp
      have hsubNu : lam * t - nu = lam * (t - nu / lam) := by field_simp
      have hsubXi : lam * t - xi = lam * (t - xi / lam) := by field_simp
      dsimp [e]
      rw [hsubOne, hsubMu, hsubNu, hsubXi,
        map_mul, map_mul, map_mul, map_mul, map_mul]
      ring

/-- The final three-parameter analytic boundary for six active roots. -/
def TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime], 64 < p →
    ∀ (χ : MulChar (ZMod p) ℂ) (m n k l s : ℕ) (t u v : ZMod p),
    m < orderOf χ → n < orderOf χ → k < orderOf χ →
    l < orderOf χ → s < orderOf χ →
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 → χ ^ s ≠ 1 →
    χ ^ (m + n + k + l + s) ≠ 1 →
    t ≠ 0 → u ≠ 0 → v ≠ 0 →
    t ≠ 1 → u ≠ 1 → v ≠ 1 → t ≠ u → t ≠ v → u ≠ v →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - t) *
        (χ ^ l) (y - u) * (χ ^ s) (y - v)‖ ≤
      4 * Real.sqrt p

theorem TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour.toFivePoint
    (hweil : TaoPrimeReducedPowerFivePointLegendreWeilBoundAboveSixtyFour) :
    TaoPrimeReducedPowerFivePointHypergeometricWeilBoundAboveSixtyFour := by
  intro p _ _ hp χ m n k l s lam mu nu xi hm hn hk hl hs
    hpowM hpowN hpowK hpowL hpowS hpowSum
    hlam hmu hnu hxi hlammu hlamnu hlamxi hmunu hmuxi hnuxi
  let t : ZMod p := mu / lam
  let u : ZMod p := nu / lam
  let v : ZMod p := xi / lam
  have ht0 : t ≠ 0 := div_ne_zero hmu hlam
  have hu0 : u ≠ 0 := div_ne_zero hnu hlam
  have hv0 : v ≠ 0 := div_ne_zero hxi hlam
  have ht1 : t ≠ 1 := by
    intro heq
    apply hlammu
    dsimp [t] at heq
    rw [div_eq_one_iff_eq hlam] at heq
    exact heq.symm
  have hu1 : u ≠ 1 := by
    intro heq
    apply hlamnu
    dsimp [u] at heq
    rw [div_eq_one_iff_eq hlam] at heq
    exact heq.symm
  have hv1 : v ≠ 1 := by
    intro heq
    apply hlamxi
    dsimp [v] at heq
    rw [div_eq_one_iff_eq hlam] at heq
    exact heq.symm
  have htu : t ≠ u := by
    intro heq
    exact hmunu ((div_left_inj' hlam).mp heq)
  have htv : t ≠ v := by
    intro heq
    exact hmuxi ((div_left_inj' hlam).mp heq)
  have huv : u ≠ v := by
    intro heq
    exact hnuxi ((div_left_inj' hlam).mp heq)
  have hbound := hweil p hp χ m n k l s t u v hm hn hk hl hs
    hpowM hpowN hpowK hpowL hpowS hpowSum
      ht0 hu0 hv0 ht1 hu1 hv1 htu htv huv
  rw [fivePointMulCharSum_eq_legendreForm
    p (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l) (χ ^ s) lam mu nu xi hlam]
  simp only [norm_mul]
  have hC :
      ‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖ *
          ‖(χ ^ s) lam‖ ≤ 1 := by
    calc
      ‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖ *
            ‖(χ ^ s) lam‖ ≤ 1 * 1 * 1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one (χ ^ m) lam
        · exact DirichletCharacter.norm_le_one (χ ^ n) lam
        · exact DirichletCharacter.norm_le_one (χ ^ k) lam
        · exact DirichletCharacter.norm_le_one (χ ^ l) lam
        · exact DirichletCharacter.norm_le_one (χ ^ s) lam
      _ = 1 := by norm_num
  calc
    (‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖ *
          ‖(χ ^ s) lam‖) *
        ‖∑ y : ZMod p,
          (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - mu / lam) *
            (χ ^ l) (y - nu / lam) * (χ ^ s) (y - xi / lam)‖ ≤
      1 * ‖∑ y : ZMod p,
        (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - mu / lam) *
          (χ ^ l) (y - nu / lam) * (χ ^ s) (y - xi / lam)‖ := by
      gcongr
    _ ≤ 4 * Real.sqrt p := by simpa [t, u, v] using hbound

theorem TaoPrimeReducedPowerFivePointHypergeometricWeilBoundAboveSixtyFour.toPower
    (hweil : TaoPrimeReducedPowerFivePointHypergeometricWeilBoundAboveSixtyFour) :
    TaoPrimePowerFivePointHypergeometricWeilBoundAboveSixtyFour := by
  intro p _ _ hp χ m n k l s lam mu nu xi
    hpowM hpowN hpowK hpowL hpowS hpowSum
    hlam hmu hnu hxi hlammu hlamnu hlamxi hmunu hmuxi hnuxi
  let m' := m % orderOf χ
  let n' := n % orderOf χ
  let k' := k % orderOf χ
  let l' := l % orderOf χ
  let s' := s % orderOf χ
  have hord : 0 < orderOf χ := orderOf_pos χ
  have hmLt : m' < orderOf χ := Nat.mod_lt m hord
  have hnLt : n' < orderOf χ := Nat.mod_lt n hord
  have hkLt : k' < orderOf χ := Nat.mod_lt k hord
  have hlLt : l' < orderOf χ := Nat.mod_lt l hord
  have hsLt : s' < orderOf χ := Nat.mod_lt s hord
  have hmEq : χ ^ m' = χ ^ m := pow_mod_orderOf χ m
  have hnEq : χ ^ n' = χ ^ n := pow_mod_orderOf χ n
  have hkEq : χ ^ k' = χ ^ k := pow_mod_orderOf χ k
  have hlEq : χ ^ l' = χ ^ l := pow_mod_orderOf χ l
  have hsEq : χ ^ s' = χ ^ s := pow_mod_orderOf χ s
  have hpowM' : χ ^ m' ≠ 1 := by simpa only [hmEq] using hpowM
  have hpowN' : χ ^ n' ≠ 1 := by simpa only [hnEq] using hpowN
  have hpowK' : χ ^ k' ≠ 1 := by simpa only [hkEq] using hpowK
  have hpowL' : χ ^ l' ≠ 1 := by simpa only [hlEq] using hpowL
  have hpowS' : χ ^ s' ≠ 1 := by simpa only [hsEq] using hpowS
  have hsumEq :
      χ ^ (m' + n' + k' + l' + s') = χ ^ (m + n + k + l + s) := by
    rw [pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
      hmEq, hnEq, hkEq, hlEq, hsEq]
  have hpowSum' : χ ^ (m' + n' + k' + l' + s') ≠ 1 := by
    simpa only [hsumEq] using hpowSum
  have hbound := hweil p hp χ m' n' k' l' s' lam mu nu xi
    hmLt hnLt hkLt hlLt hsLt
    hpowM' hpowN' hpowK' hpowL' hpowS' hpowSum'
      hlam hmu hnu hxi hlammu hlamnu hlamxi hmunu hmuxi hnuxi
  simpa only [hmEq, hnEq, hkEq, hlEq, hsEq] using hbound

set_option maxHeartbeats 4000000 in
/-- Pointwise six-root Möbius reduction away from the deleted projective
point.  Triviality of the six-character product cancels the denominator and
leaves five finite character factors. -/
theorem sixRootMobius_term
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ : MulChar (ZMod p) ℂ)
    (hprod : α * β * γ * δ * ε * ζ = 1)
    (a b c d e f : ZMod p)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (hec : e ≠ c) (hfc : f ≠ c)
    (y : ZMod p) (hy : y ≠ 1) :
    let mob := threeRootMobiusEquiv p a c hac
    let lam := (a - b) / (c - b)
    let mu := (a - d) / (c - d)
    let nu := (a - e) / (c - e)
    let xi := (a - f) / (c - f)
    α (mob.symm y - a) * β (mob.symm y - b) * γ (mob.symm y - c) *
        δ (mob.symm y - d) * ε (mob.symm y - e) * ζ (mob.symm y - f) =
      (α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
          ε (c - e) * ζ (c - f)) *
        (α y * β (y - lam) * δ (y - mu) * ε (y - nu) * ζ (y - xi)) := by
  dsimp only
  rw [threeRootMobiusEquiv_symm_apply, if_neg hy]
  have hden : y - 1 ≠ 0 := sub_ne_zero.mpr hy
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr hbc.symm
  have hcd : c - d ≠ 0 := sub_ne_zero.mpr hdc.symm
  have hce : c - e ≠ 0 := sub_ne_zero.mpr hec.symm
  have hcf : c - f ≠ 0 := sub_ne_zero.mpr hfc.symm
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
  have hxe : (y * c - a) / (y - 1) - e =
      (c - e) * (y - (a - e) / (c - e)) / (y - 1) := by
    field_simp
    ring
  have hxf : (y * c - a) / (y - 1) - f =
      (c - f) * (y - (a - f) / (c - f)) / (y - 1) := by
    field_simp
    ring
  rw [hxa, hxb, hxc, hxd, hxe, hxf]
  have hmapdivα (u v : ZMod p) : α (u / v) = α u / α v := by
    exact map_div₀ α.toMonoidWithZeroHom u v
  have hmapdivβ (u v : ZMod p) : β (u / v) = β u / β v := by
    exact map_div₀ β.toMonoidWithZeroHom u v
  have hmapdivγ (u v : ZMod p) : γ (u / v) = γ u / γ v := by
    exact map_div₀ γ.toMonoidWithZeroHom u v
  have hmapdivδ (u v : ZMod p) : δ (u / v) = δ u / δ v := by
    exact map_div₀ δ.toMonoidWithZeroHom u v
  have hmapdivε (u v : ZMod p) : ε (u / v) = ε u / ε v := by
    exact map_div₀ ε.toMonoidWithZeroHom u v
  have hmapdivζ (u v : ZMod p) : ζ (u / v) = ζ u / ζ v := by
    exact map_div₀ ζ.toMonoidWithZeroHom u v
  rw [hmapdivα, map_mul, hmapdivβ, map_mul, hmapdivγ,
    hmapdivδ, map_mul, hmapdivε, map_mul, hmapdivζ, map_mul]
  have hcancel :
      α (y - 1) * β (y - 1) * γ (y - 1) * δ (y - 1) *
          ε (y - 1) * ζ (y - 1) = 1 := by
    rw [← MulChar.mul_apply, ← MulChar.mul_apply, ← MulChar.mul_apply,
      ← MulChar.mul_apply, ← MulChar.mul_apply, hprod]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hden)
  have hα : α (y - 1) ≠ 0 := by
    intro h
    rw [h, zero_mul, zero_mul, zero_mul, zero_mul, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hβ : β (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul, zero_mul, zero_mul, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hγ : γ (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul, zero_mul, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hδ : δ (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hε : ε (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hζ : ζ (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcancel
    exact zero_ne_one hcancel
  field_simp [hα, hβ, hγ, hδ, hε, hζ]
  linear_combination
    -(α y * α (c - a) * β (c - b) *
      β ((y * (c - b) - (a - b)) / (c - b)) * γ (c - a) *
      δ (c - d) * δ ((y * (c - d) - (a - d)) / (c - d)) *
      ε (c - e) * ε ((y * (c - e) - (a - e)) / (c - e)) *
      ζ (c - f) * ζ ((y * (c - f) - (a - f)) / (c - f))) * hcancel

/-- A degree-balanced six-root sum is a five-point sum with one deleted
projective value, up to a character-valued constant. -/
theorem sixRootMulCharSum_eq_fivePointSum_sub
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ : MulChar (ZMod p) ℂ)
    (hprod : α * β * γ * δ * ε * ζ = 1)
    (a b c d e f : ZMod p)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (hec : e ≠ c) (hfc : f ≠ c) :
    let lam := (a - b) / (c - b)
    let mu := (a - d) / (c - d)
    let nu := (a - e) / (c - e)
    let xi := (a - f) / (c - f)
    (∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
          ε (x - e) * ζ (x - f)) =
      (α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
          ε (c - e) * ζ (c - f)) *
        ((∑ y : ZMod p,
            α y * β (y - lam) * δ (y - mu) * ε (y - nu) * ζ (y - xi)) -
          β (1 - lam) * δ (1 - mu) * ε (1 - nu) * ζ (1 - xi)) := by
  dsimp only
  let mob := threeRootMobiusEquiv p a c hac
  let F : ZMod p → ℂ := fun x =>
    α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
      ε (x - e) * ζ (x - f)
  let G : ZMod p → ℂ := fun y =>
    α y * β (y - (a - b) / (c - b)) * δ (y - (a - d) / (c - d)) *
      ε (y - (a - e) / (c - e)) * ζ (y - (a - f) / (c - f))
  let C : ℂ :=
    α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
      ε (c - e) * ζ (c - f)
  have hone : F (mob.symm 1) = 0 := by
    simp [F, mob, γ.map_zero]
  have hterm (y : ZMod p) (hy : y ∈ Finset.univ.erase 1) :
      F (mob.symm y) = C * G y := by
    have hyOne : y ≠ 1 := by simpa using hy
    simpa [F, G, C, mob] using
      sixRootMobius_term p α β γ δ ε ζ hprod a b c d e f
        hac hbc hdc hec hfc y hyOne
  calc
    (∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
          ε (x - e) * ζ (x - f)) = ∑ x : ZMod p, F x := by rfl
    _ = ∑ y : ZMod p, F (mob.symm y) :=
      (Equiv.sum_comp mob.symm F).symm
    _ = ∑ y ∈ Finset.univ.erase 1, F (mob.symm y) := by
      exact (Finset.sum_erase (s := Finset.univ)
        (f := fun y => F (mob.symm y)) hone).symm
    _ = C * ∑ y ∈ Finset.univ.erase 1, G y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      exact hterm
    _ = C * ((∑ y : ZMod p, G y) - G 1) := by
      congr 1
      have h := Finset.sum_erase_add Finset.univ G
        (Finset.mem_univ (1 : ZMod p))
      linear_combination h
    _ = _ := by simp [C, G, MulChar.map_one]

/-- Once the canonical five-point trace is bounded, the six-root Möbius
identity costs only the single deleted value. -/
theorem norm_sixRootMulCharSum_le_four_mul_sqrt_add_one_of_fivePoint
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ : MulChar (ZMod p) ℂ)
    (hprod : α * β * γ * δ * ε * ζ = 1)
    (a b c d e f : ZMod p)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (hec : e ≠ c) (hfc : f ≠ c)
    (hfive :
      ‖∑ y : ZMod p,
        α y * β (y - (a - b) / (c - b)) *
          δ (y - (a - d) / (c - d)) *
          ε (y - (a - e) / (c - e)) *
          ζ (y - (a - f) / (c - f))‖ ≤ 4 * Real.sqrt p) :
    ‖∑ x : ZMod p,
      α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
        ε (x - e) * ζ (x - f)‖ ≤
      4 * Real.sqrt p + 1 := by
  rw [sixRootMulCharSum_eq_fivePointSum_sub
    p α β γ δ ε ζ hprod a b c d e f hac hbc hdc hec hfc]
  simp only [norm_mul]
  have hC :
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ *
          ‖ε (c - e)‖ * ‖ζ (c - f)‖ ≤ 1 := by
    calc
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ *
            ‖ε (c - e)‖ * ‖ζ (c - f)‖ ≤ 1 * 1 * 1 * 1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one α _
        · exact DirichletCharacter.norm_le_one β _
        · exact DirichletCharacter.norm_le_one γ _
        · exact DirichletCharacter.norm_le_one δ _
        · exact DirichletCharacter.norm_le_one ε _
        · exact DirichletCharacter.norm_le_one ζ _
      _ = 1 := by norm_num
  have hdeleted :
      ‖β (1 - (a - b) / (c - b)) * δ (1 - (a - d) / (c - d)) *
          ε (1 - (a - e) / (c - e)) * ζ (1 - (a - f) / (c - f))‖ ≤ 1 := by
    simp only [norm_mul]
    calc
      ‖β (1 - (a - b) / (c - b))‖ * ‖δ (1 - (a - d) / (c - d))‖ *
            ‖ε (1 - (a - e) / (c - e))‖ * ‖ζ (1 - (a - f) / (c - f))‖ ≤
          1 * 1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one β _
        · exact DirichletCharacter.norm_le_one δ _
        · exact DirichletCharacter.norm_le_one ε _
        · exact DirichletCharacter.norm_le_one ζ _
      _ = 1 := by norm_num
  calc
    (‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ *
          ‖ε (c - e)‖ * ‖ζ (c - f)‖) *
        ‖(∑ y : ZMod p,
            α y * β (y - (a - b) / (c - b)) *
              δ (y - (a - d) / (c - d)) *
              ε (y - (a - e) / (c - e)) *
              ζ (y - (a - f) / (c - f))) -
          β (1 - (a - b) / (c - b)) * δ (1 - (a - d) / (c - d)) *
            ε (1 - (a - e) / (c - e)) * ζ (1 - (a - f) / (c - f))‖ ≤
      1 * ‖(∑ y : ZMod p,
            α y * β (y - (a - b) / (c - b)) *
              δ (y - (a - d) / (c - d)) *
              ε (y - (a - e) / (c - e)) *
              ζ (y - (a - f) / (c - f))) -
          β (1 - (a - b) / (c - b)) * δ (1 - (a - d) / (c - d)) *
            ε (1 - (a - e) / (c - e)) * ζ (1 - (a - f) / (c - f))‖ := by
      gcongr
    _ ≤ ‖∑ y : ZMod p,
          α y * β (y - (a - b) / (c - b)) *
            δ (y - (a - d) / (c - d)) *
            ε (y - (a - e) / (c - e)) *
            ζ (y - (a - f) / (c - f))‖ +
        ‖β (1 - (a - b) / (c - b)) * δ (1 - (a - d) / (c - d)) *
          ε (1 - (a - e) / (c - e)) * ζ (1 - (a - f) / (c - f))‖ := by
      simpa using norm_sub_le
        (∑ y : ZMod p,
          α y * β (y - (a - b) / (c - b)) *
            δ (y - (a - d) / (c - d)) *
            ε (y - (a - e) / (c - e)) *
            ζ (y - (a - f) / (c - f)))
        (β (1 - (a - b) / (c - b)) * δ (1 - (a - d) / (c - d)) *
          ε (1 - (a - e) / (c - e)) * ζ (1 - (a - f) / (c - f)))
    _ ≤ 4 * Real.sqrt p + 1 := add_le_add hfive hdeleted

/-- The source-shaped five-point endpoint gives the projective estimate for
six distinct roots whose six local powers multiply to one. -/
theorem norm_sixRootMulCharPowerSum_le_four_mul_sqrt_add_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerFivePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (m n k l s q : ℕ)
    (hpowM : χ ^ m ≠ 1) (hpowN : χ ^ n ≠ 1) (hpowK : χ ^ k ≠ 1)
    (hpowL : χ ^ l ≠ 1) (hpowS : χ ^ s ≠ 1) (hpowQ : χ ^ q ≠ 1)
    (hprod :
      (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) * (χ ^ q) = 1)
    (a b c d e f : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hdc : d ≠ c) (hde : d ≠ e) (hdf : d ≠ f)
    (hec : e ≠ c) (hef : e ≠ f) (hfc : f ≠ c) :
    ‖∑ x : ZMod p,
      (χ ^ m) (x - a) * (χ ^ n) (x - b) * (χ ^ k) (x - c) *
        (χ ^ l) (x - d) * (χ ^ s) (x - e) * (χ ^ q) (x - f)‖ ≤
      4 * Real.sqrt p + 1 := by
  let lam : ZMod p := (a - b) / (c - b)
  let mu : ZMod p := (a - d) / (c - d)
  let nu : ZMod p := (a - e) / (c - e)
  let xi : ZMod p := (a - f) / (c - f)
  have hlam : lam ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hbc.symm)
  have hmu : mu ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr had) (sub_ne_zero.mpr hdc.symm)
  have hnu : nu ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hae) (sub_ne_zero.mpr hec.symm)
  have hxi : xi ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr haf) (sub_ne_zero.mpr hfc.symm)
  have crossRatio_ne {r t : ZMod p}
      (hrc : r ≠ c) (htc : t ≠ c) (hrt : r ≠ t) :
      (a - r) / (c - r) ≠ (a - t) / (c - t) := by
    intro heq
    rw [div_eq_div_iff (sub_ne_zero.mpr hrc.symm)
      (sub_ne_zero.mpr htc.symm)] at heq
    have hzero : (a - c) * (r - t) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp hzero with hac' | hrt'
    · exact hac (sub_eq_zero.mp hac')
    · exact hrt (sub_eq_zero.mp hrt')
  have hlammu : lam ≠ mu := crossRatio_ne hbc hdc hbd
  have hlamnu : lam ≠ nu := crossRatio_ne hbc hec hbe
  have hlamxi : lam ≠ xi := crossRatio_ne hbc hfc hbf
  have hmunu : mu ≠ nu := crossRatio_ne hdc hec hde
  have hmuxi : mu ≠ xi := crossRatio_ne hdc hfc hdf
  have hnuxi : nu ≠ xi := crossRatio_ne hec hfc hef
  have hfiniteProd : χ ^ (m + n + l + s + q) ≠ 1 := by
    intro heq
    apply hpowK
    calc
      χ ^ k = 1 * χ ^ k := by simp
      _ = χ ^ (m + n + l + s + q) * χ ^ k := by rw [heq]
      _ = (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) * (χ ^ q) := by
        simp only [pow_add]
        ac_rfl
      _ = 1 := hprod
  have hfive :
      ‖∑ y : ZMod p,
        (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ l) (y - mu) *
          (χ ^ s) (y - nu) * (χ ^ q) (y - xi)‖ ≤
        4 * Real.sqrt p :=
    hweil χ m n l s q lam mu nu xi
      hpowM hpowN hpowL hpowS hpowQ hfiniteProd
      hlam hmu hnu hxi hlammu hlamnu hlamxi hmunu hmuxi hnuxi
  exact norm_sixRootMulCharSum_le_four_mul_sqrt_add_one_of_fivePoint
    p (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l) (χ ^ s) (χ ^ q) hprod
      a b c d e f hac hbc hdc hec hfc hfive

/-- Exactly six active roots of character-order-divisible degree reduce to
the source-shaped five-point endpoint. -/
theorem norm_primeActiveRootCharacterSum_le_four_mul_sqrt_add_one_of_card_eq_six_degree_power
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerFivePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 6) :
    ‖primeActiveRootCharacterSum p χ P‖ ≤ 4 * Real.sqrt p + 1 := by
  let S := primeActiveRoots p χ P
  obtain ⟨u, huS⟩ : S.Nonempty := Finset.card_pos.mp (by simp [S, hcard])
  have hcardS : S.card = 6 := by simpa only [S] using hcard
  have hcardOne : (S.erase u).card = 5 := by
    rw [Finset.card_erase_of_mem huS]
    omega
  obtain ⟨v, hvOne⟩ : (S.erase u).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardTwo : ((S.erase u).erase v).card = 4 := by
    rw [Finset.card_erase_of_mem hvOne, hcardOne]
  obtain ⟨w, z, t, q, hwz, hwt, hwq, hzt, hzq, htq, hrest⟩ :=
    Finset.card_eq_four.mp hcardTwo
  have hwTwo : w ∈ (S.erase u).erase v := by simp [hrest]
  have hzTwo : z ∈ (S.erase u).erase v := by simp [hrest]
  have htTwo : t ∈ (S.erase u).erase v := by simp [hrest]
  have hqTwo : q ∈ (S.erase u).erase v := by simp [hrest]
  have huv : u ≠ v := (Finset.mem_erase.mp hvOne).1.symm
  have huw : u ≠ w := (Finset.mem_erase.mp (Finset.mem_erase.mp hwTwo).2).1.symm
  have huz : u ≠ z := (Finset.mem_erase.mp (Finset.mem_erase.mp hzTwo).2).1.symm
  have hut : u ≠ t := (Finset.mem_erase.mp (Finset.mem_erase.mp htTwo).2).1.symm
  have huq : u ≠ q := (Finset.mem_erase.mp (Finset.mem_erase.mp hqTwo).2).1.symm
  have hvw : v ≠ w := (Finset.mem_erase.mp hwTwo).1.symm
  have hvz : v ≠ z := (Finset.mem_erase.mp hzTwo).1.symm
  have hvt : v ≠ t := (Finset.mem_erase.mp htTwo).1.symm
  have hvq : v ≠ q := (Finset.mem_erase.mp hqTwo).1.symm
  have hvS : v ∈ S := (Finset.mem_erase.mp hvOne).2
  have hwS : w ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hwTwo).2).2
  have hzS : z ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hzTwo).2).2
  have htS : t ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp htTwo).2).2
  have hqS : q ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hqTwo).2).2
  have hroots : S = {u, v, w, z, t, q} := by
    calc
      S = insert u (S.erase u) := (Finset.insert_erase huS).symm
      _ = insert u (insert v ((S.erase u).erase v)) := by
        rw [Finset.insert_erase hvOne]
      _ = {u, v, w, z, t, q} := by rw [hrest]
  have huActive : u ∈ primeActiveRoots p χ P := by
    simpa only [S] using huS
  have hvActive : v ∈ primeActiveRoots p χ P := by
    simpa only [S] using hvS
  have hwActive : w ∈ primeActiveRoots p χ P := by
    simpa only [S] using hwS
  have hzActive : z ∈ primeActiveRoots p χ P := by
    simpa only [S] using hzS
  have htActive : t ∈ primeActiveRoots p χ P := by
    simpa only [S] using htS
  have hqActive : q ∈ primeActiveRoots p χ P := by
    simpa only [S] using hqS
  have huRoot : u ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P huActive
  have hvRoot : v ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hvActive
  have hwRoot : w ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hwActive
  have hzRoot : z ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hzActive
  have htRoot : t ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P htActive
  have hqRoot : q ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hqActive
  let m := P.roots.count u
  let n := P.roots.count v
  let k := P.roots.count w
  let l := P.roots.count z
  let s := P.roots.count t
  let o := P.roots.count q
  have hm : m ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp huRoot)).ne'
  have hn : n ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hvRoot)).ne'
  have hk : k ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hwRoot)).ne'
  have hl : l ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hzRoot)).ne'
  have hs : s ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp htRoot)).ne'
  have ho : o ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hqRoot)).ne'
  have hpowM : χ ^ m ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp huActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowN : χ ^ n ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hvActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowK : χ ^ k ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hwActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowL : χ ^ l ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hzActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowS : χ ^ s ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp htActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowO : χ ^ o ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hqActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hsum := orderOf_dvd_sum_primeActiveRoots_count p χ P hP hdegree
  have hmnklso : orderOf χ ∣ m + n + k + l + s + o := by
    simpa [S, hroots, huv, huw, huz, hut, huq, hvw, hvz, hvt, hvq,
      hwz, hwt, hwq, hzt, hzq, htq, m, n, k, l, s, o,
      add_assoc, add_comm, add_left_comm] using hsum
  have hprod :
      (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) * (χ ^ o) = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    exact orderOf_dvd_iff_pow_eq_one.mp hmnklso
  have hsix := norm_sixRootMulCharPowerSum_le_four_mul_sqrt_add_one
    p hweil χ m n k l s o hpowM hpowN hpowK hpowL hpowS hpowO hprod
      u v w z t q huv huw huz hut huq hvw hvz hvt hvq
      hwz.symm hzt hzq hwt.symm htq hwq.symm
  unfold primeActiveRootCharacterSum
  rw [show primeActiveRoots p χ P = {u, v, w, z, t, q} by simpa [S] using hroots]
  convert hsix using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro x _hx
  simp [huv, huw, huz, hut, huq, hvw, hvz, hvt, hvq,
    hwz, hwt, hwq, hzt, hzq, htq]
  rw [MulChar.pow_apply' χ hm, MulChar.pow_apply' χ hn,
    MulChar.pow_apply' χ hk, MulChar.pow_apply' χ hl,
    MulChar.pow_apply' χ hs, MulChar.pow_apply' χ ho]
  simp [m, n, k, l, s, o, Polynomial.count_roots]
  ac_rfl

/-- The five-point power endpoint discharges the existing split-polynomial
target when exactly six roots are active and the degree is divisible by the
character order. -/
theorem primeSplitPolynomialWeilBound_of_card_activeRoots_eq_six_degree_power
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerFivePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (_a : ZMod p) (_hχ : χ ≠ 1) (hP : P.Splits)
    (_hnot : ¬orderOf χ ∣ P.rootMultiplicity _a)
    (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 6) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
  have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
  have hactive :=
    norm_primeActiveRootCharacterSum_le_four_mul_sqrt_add_one_of_card_eq_six_degree_power
      p hweil χ P hP hdegree hcard
  have hrestricted :=
    norm_filter_primeActiveRootProduct_le_of_activeRootCharacterSum
      p χ P (4 * Real.sqrt p + 1) hactive
  have hrootCard : 6 ≤ P.roots.toFinset.card := by
    rw [← hcard]
    exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
  have hInactiveCard :
      (primeInactiveRoots p χ P).card ≤ P.roots.toFinset.card :=
    Finset.card_le_card (primeInactiveRoots_subset_roots p χ P)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hroom :
      4 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
    have hInactiveCard' :
        ((primeInactiveRoots p χ P).card : ℝ) ≤
          (P.roots.toFinset.card : ℝ) := by exact_mod_cast hInactiveCard
    have hrootCard' : (6 : ℝ) ≤ P.roots.toFinset.card := by
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
    _ ≤ 4 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card := by
      simpa using hrestricted
    _ ≤ ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := hroom

end

end Tao2026
