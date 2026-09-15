import Tao2026.BurgessWeilPrimeEightRoots

/-!
# Nine active roots in the prime Burgess sum

This file isolates the next source-shaped endpoint obtained by sending one
of nine degree-balanced active roots to infinity. The eight finite local
characters remain powers of one Burgess character, and scaling normalizes
their marked points to `0`, `1`, `t`, `u`, `v`, `w`, `z`, and `r₀`.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The source-shaped eight-point endpoint at one prime. -/
def TaoPrimePowerEightPointHypergeometricWeilBoundAt
    (p : ℕ) [NeZero p] [Fact p.Prime] : Prop :=
  ∀ (χ : MulChar (ZMod p) ℂ) (m n k l s o q r : ℕ)
    (lam mu nu xi rho sigma tau : ZMod p),
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 →
    χ ^ s ≠ 1 → χ ^ o ≠ 1 → χ ^ q ≠ 1 → χ ^ r ≠ 1 →
    χ ^ (m + n + k + l + s + o + q + r) ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → nu ≠ 0 → xi ≠ 0 → rho ≠ 0 → sigma ≠ 0 → tau ≠ 0 →
    lam ≠ mu → lam ≠ nu → lam ≠ xi → lam ≠ rho → lam ≠ sigma → lam ≠ tau →
    mu ≠ nu → mu ≠ xi → mu ≠ rho → mu ≠ sigma → mu ≠ tau →
    nu ≠ xi → nu ≠ rho → nu ≠ sigma → nu ≠ tau →
    xi ≠ rho → xi ≠ sigma → xi ≠ tau →
    rho ≠ sigma → rho ≠ tau → sigma ≠ tau →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ k) (y - mu) *
        (χ ^ l) (y - nu) * (χ ^ s) (y - xi) * (χ ^ o) (y - rho) *
          (χ ^ q) (y - sigma) * (χ ^ r) (y - tau)‖ ≤ 7 * Real.sqrt p

/-- The large-characteristic range needed by the exact Burgess branch. -/
def TaoPrimePowerEightPointHypergeometricWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime],
    64 < p → TaoPrimePowerEightPointHypergeometricWeilBoundAt p

/-- Finite exponent-range form of the source-shaped eight-point endpoint. -/
def TaoPrimeReducedPowerEightPointHypergeometricWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime], 64 < p →
    ∀ (χ : MulChar (ZMod p) ℂ) (m n k l s o q r : ℕ)
      (lam mu nu xi rho sigma tau : ZMod p),
    m < orderOf χ → n < orderOf χ → k < orderOf χ →
    l < orderOf χ → s < orderOf χ → o < orderOf χ → q < orderOf χ →
    r < orderOf χ →
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 →
    χ ^ s ≠ 1 → χ ^ o ≠ 1 → χ ^ q ≠ 1 → χ ^ r ≠ 1 →
    χ ^ (m + n + k + l + s + o + q + r) ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → nu ≠ 0 → xi ≠ 0 → rho ≠ 0 → sigma ≠ 0 → tau ≠ 0 →
    lam ≠ mu → lam ≠ nu → lam ≠ xi → lam ≠ rho → lam ≠ sigma → lam ≠ tau →
    mu ≠ nu → mu ≠ xi → mu ≠ rho → mu ≠ sigma → mu ≠ tau →
    nu ≠ xi → nu ≠ rho → nu ≠ sigma → nu ≠ tau →
    xi ≠ rho → xi ≠ sigma → xi ≠ tau →
    rho ≠ sigma → rho ≠ tau → sigma ≠ tau →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ k) (y - mu) *
        (χ ^ l) (y - nu) * (χ ^ s) (y - xi) * (χ ^ o) (y - rho) *
          (χ ^ q) (y - sigma) * (χ ^ r) (y - tau)‖ ≤ 7 * Real.sqrt p

/-- Scaling by the first nonzero point puts an eight-point sum into the
six-parameter Legendre form `0`, `1`, `t`, `u`, `v`, `w`, `z`, `r₀`. -/
theorem eightPointMulCharSum_eq_legendreForm
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ η θ : MulChar (ZMod p) ℂ)
    (lam mu nu xi rho sigma tau : ZMod p) (hlam : lam ≠ 0) :
    (∑ y : ZMod p,
      α y * β (y - lam) * γ (y - mu) * δ (y - nu) * ε (y - xi) *
        ζ (y - rho) * η (y - sigma) * θ (y - tau)) =
      (α lam * β lam * γ lam * δ lam * ε lam * ζ lam * η lam * θ lam) *
        ∑ t : ZMod p,
          α t * β (t - 1) * γ (t - mu / lam) * δ (t - nu / lam) *
            ε (t - xi / lam) * ζ (t - rho / lam) * η (t - sigma / lam) *
              θ (t - tau / lam) := by
  let e : ZMod p ≃ ZMod p := Equiv.mulLeft₀ lam hlam
  calc
    (∑ y : ZMod p,
        α y * β (y - lam) * γ (y - mu) * δ (y - nu) * ε (y - xi) *
          ζ (y - rho) * η (y - sigma) * θ (y - tau)) =
        ∑ t : ZMod p,
          α (e t) * β (e t - lam) * γ (e t - mu) * δ (e t - nu) *
            ε (e t - xi) * ζ (e t - rho) * η (e t - sigma) * θ (e t - tau) :=
      (Equiv.sum_comp e
        (fun y : ZMod p =>
          α y * β (y - lam) * γ (y - mu) * δ (y - nu) * ε (y - xi) *
            ζ (y - rho) * η (y - sigma) * θ (y - tau))).symm
    _ = (α lam * β lam * γ lam * δ lam * ε lam * ζ lam * η lam * θ lam) *
        ∑ t : ZMod p,
          α t * β (t - 1) * γ (t - mu / lam) * δ (t - nu / lam) *
            ε (t - xi / lam) * ζ (t - rho / lam) * η (t - sigma / lam) *
              θ (t - tau / lam) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      have hsubOne : lam * t - lam = lam * (t - 1) := by ring
      have hsubMu : lam * t - mu = lam * (t - mu / lam) := by field_simp
      have hsubNu : lam * t - nu = lam * (t - nu / lam) := by field_simp
      have hsubXi : lam * t - xi = lam * (t - xi / lam) := by field_simp
      have hsubRho : lam * t - rho = lam * (t - rho / lam) := by field_simp
      have hsubSigma : lam * t - sigma = lam * (t - sigma / lam) := by field_simp
      have hsubTau : lam * t - tau = lam * (t - tau / lam) := by field_simp
      dsimp [e]
      rw [hsubOne, hsubMu, hsubNu, hsubXi, hsubRho, hsubSigma, hsubTau,
        map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
      ring

/-- The final six-parameter analytic boundary for nine active roots. -/
def TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime], 64 < p →
    ∀ (χ : MulChar (ZMod p) ℂ) (m n k l s o q r : ℕ)
      (t u v w z r₀ : ZMod p),
    m < orderOf χ → n < orderOf χ → k < orderOf χ →
    l < orderOf χ → s < orderOf χ → o < orderOf χ → q < orderOf χ →
    r < orderOf χ →
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 →
    χ ^ s ≠ 1 → χ ^ o ≠ 1 → χ ^ q ≠ 1 → χ ^ r ≠ 1 →
    χ ^ (m + n + k + l + s + o + q + r) ≠ 1 →
    t ≠ 0 → u ≠ 0 → v ≠ 0 → w ≠ 0 → z ≠ 0 → r₀ ≠ 0 →
    t ≠ 1 → u ≠ 1 → v ≠ 1 → w ≠ 1 → z ≠ 1 → r₀ ≠ 1 →
    t ≠ u → t ≠ v → t ≠ w → t ≠ z → t ≠ r₀ →
    u ≠ v → u ≠ w → u ≠ z → u ≠ r₀ →
    v ≠ w → v ≠ z → v ≠ r₀ → w ≠ z → w ≠ r₀ → z ≠ r₀ →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - t) *
        (χ ^ l) (y - u) * (χ ^ s) (y - v) * (χ ^ o) (y - w) *
          (χ ^ q) (y - z) * (χ ^ r) (y - r₀)‖ ≤ 7 * Real.sqrt p

theorem TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour.toEightPoint
    (hweil : TaoPrimeReducedPowerEightPointLegendreWeilBoundAboveSixtyFour) :
    TaoPrimeReducedPowerEightPointHypergeometricWeilBoundAboveSixtyFour := by
  intro p _ _ hp χ m n k l s o q r lam mu nu xi rho sigma tau
    hm hn hk hl hs ho hq hr
    hpowM hpowN hpowK hpowL hpowS hpowO hpowQ hpowR hpowSum
    hlam hmu hnu hxi hrho hsigma htau
    hlammu hlamnu hlamxi hlamrho hlamsigma hlamtau
    hmunu hmuxi hmurho hmusigma hmutau
    hnuxi hnurho hnusigma hnutau
    hxirho hxisigma hxitau hrhosigma hrhotau hsigmatau
  let t : ZMod p := mu / lam
  let u : ZMod p := nu / lam
  let v : ZMod p := xi / lam
  let w : ZMod p := rho / lam
  let z : ZMod p := sigma / lam
  let r₀ : ZMod p := tau / lam
  have ht0 : t ≠ 0 := div_ne_zero hmu hlam
  have hu0 : u ≠ 0 := div_ne_zero hnu hlam
  have hv0 : v ≠ 0 := div_ne_zero hxi hlam
  have hw0 : w ≠ 0 := div_ne_zero hrho hlam
  have hz0 : z ≠ 0 := div_ne_zero hsigma hlam
  have hr₀0 : r₀ ≠ 0 := div_ne_zero htau hlam
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
  have hw1 : w ≠ 1 := by
    intro heq
    apply hlamrho
    dsimp [w] at heq
    rw [div_eq_one_iff_eq hlam] at heq
    exact heq.symm
  have hz1 : z ≠ 1 := by
    intro heq
    apply hlamsigma
    dsimp [z] at heq
    rw [div_eq_one_iff_eq hlam] at heq
    exact heq.symm
  have hr₀1 : r₀ ≠ 1 := by
    intro heq
    apply hlamtau
    dsimp [r₀] at heq
    rw [div_eq_one_iff_eq hlam] at heq
    exact heq.symm
  have htu : t ≠ u := fun heq => hmunu ((div_left_inj' hlam).mp heq)
  have htv : t ≠ v := fun heq => hmuxi ((div_left_inj' hlam).mp heq)
  have htw : t ≠ w := fun heq => hmurho ((div_left_inj' hlam).mp heq)
  have htz : t ≠ z := fun heq => hmusigma ((div_left_inj' hlam).mp heq)
  have htr₀ : t ≠ r₀ := fun heq => hmutau ((div_left_inj' hlam).mp heq)
  have huv : u ≠ v := fun heq => hnuxi ((div_left_inj' hlam).mp heq)
  have huw : u ≠ w := fun heq => hnurho ((div_left_inj' hlam).mp heq)
  have huz : u ≠ z := fun heq => hnusigma ((div_left_inj' hlam).mp heq)
  have hur₀ : u ≠ r₀ := fun heq => hnutau ((div_left_inj' hlam).mp heq)
  have hvw : v ≠ w := fun heq => hxirho ((div_left_inj' hlam).mp heq)
  have hvz : v ≠ z := fun heq => hxisigma ((div_left_inj' hlam).mp heq)
  have hvr₀ : v ≠ r₀ := fun heq => hxitau ((div_left_inj' hlam).mp heq)
  have hwz : w ≠ z := fun heq => hrhosigma ((div_left_inj' hlam).mp heq)
  have hwr₀ : w ≠ r₀ := fun heq => hrhotau ((div_left_inj' hlam).mp heq)
  have hzr₀ : z ≠ r₀ := fun heq => hsigmatau ((div_left_inj' hlam).mp heq)
  have hbound := hweil p hp χ m n k l s o q r t u v w z r₀
    hm hn hk hl hs ho hq hr
    hpowM hpowN hpowK hpowL hpowS hpowO hpowQ hpowR hpowSum
    ht0 hu0 hv0 hw0 hz0 hr₀0 ht1 hu1 hv1 hw1 hz1 hr₀1
    htu htv htw htz htr₀ huv huw huz hur₀ hvw hvz hvr₀ hwz hwr₀ hzr₀
  rw [eightPointMulCharSum_eq_legendreForm
    p (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l) (χ ^ s) (χ ^ o) (χ ^ q) (χ ^ r)
      lam mu nu xi rho sigma tau hlam]
  simp only [norm_mul]
  have hC :
      ‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖ *
          ‖(χ ^ s) lam‖ * ‖(χ ^ o) lam‖ * ‖(χ ^ q) lam‖ * ‖(χ ^ r) lam‖ ≤ 1 := by
    calc
      ‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖ *
            ‖(χ ^ s) lam‖ * ‖(χ ^ o) lam‖ * ‖(χ ^ q) lam‖ * ‖(χ ^ r) lam‖ ≤
          1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one (χ ^ m) lam
        · exact DirichletCharacter.norm_le_one (χ ^ n) lam
        · exact DirichletCharacter.norm_le_one (χ ^ k) lam
        · exact DirichletCharacter.norm_le_one (χ ^ l) lam
        · exact DirichletCharacter.norm_le_one (χ ^ s) lam
        · exact DirichletCharacter.norm_le_one (χ ^ o) lam
        · exact DirichletCharacter.norm_le_one (χ ^ q) lam
        · exact DirichletCharacter.norm_le_one (χ ^ r) lam
      _ = 1 := by norm_num
  calc
    (‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖ *
          ‖(χ ^ s) lam‖ * ‖(χ ^ o) lam‖ * ‖(χ ^ q) lam‖ * ‖(χ ^ r) lam‖) *
        ‖∑ y : ZMod p,
          (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - mu / lam) *
            (χ ^ l) (y - nu / lam) * (χ ^ s) (y - xi / lam) *
              (χ ^ o) (y - rho / lam) * (χ ^ q) (y - sigma / lam) *
                (χ ^ r) (y - tau / lam)‖ ≤
      1 * ‖∑ y : ZMod p,
        (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - mu / lam) *
          (χ ^ l) (y - nu / lam) * (χ ^ s) (y - xi / lam) *
            (χ ^ o) (y - rho / lam) * (χ ^ q) (y - sigma / lam) *
              (χ ^ r) (y - tau / lam)‖ := by gcongr
    _ ≤ 7 * Real.sqrt p := by simpa [t, u, v, w, z, r₀] using hbound

theorem TaoPrimeReducedPowerEightPointHypergeometricWeilBoundAboveSixtyFour.toPower
    (hweil : TaoPrimeReducedPowerEightPointHypergeometricWeilBoundAboveSixtyFour) :
    TaoPrimePowerEightPointHypergeometricWeilBoundAboveSixtyFour := by
  intro p _ _ hp χ m n k l s o q r lam mu nu xi rho sigma tau
    hpowM hpowN hpowK hpowL hpowS hpowO hpowQ hpowR hpowSum
    hlam hmu hnu hxi hrho hsigma htau
    hlammu hlamnu hlamxi hlamrho hlamsigma hlamtau
    hmunu hmuxi hmurho hmusigma hmutau
    hnuxi hnurho hnusigma hnutau
    hxirho hxisigma hxitau hrhosigma hrhotau hsigmatau
  let m' := m % orderOf χ
  let n' := n % orderOf χ
  let k' := k % orderOf χ
  let l' := l % orderOf χ
  let s' := s % orderOf χ
  let o' := o % orderOf χ
  let q' := q % orderOf χ
  let r' := r % orderOf χ
  have hord : 0 < orderOf χ := orderOf_pos χ
  have hmLt : m' < orderOf χ := Nat.mod_lt m hord
  have hnLt : n' < orderOf χ := Nat.mod_lt n hord
  have hkLt : k' < orderOf χ := Nat.mod_lt k hord
  have hlLt : l' < orderOf χ := Nat.mod_lt l hord
  have hsLt : s' < orderOf χ := Nat.mod_lt s hord
  have hoLt : o' < orderOf χ := Nat.mod_lt o hord
  have hqLt : q' < orderOf χ := Nat.mod_lt q hord
  have hrLt : r' < orderOf χ := Nat.mod_lt r hord
  have hmEq : χ ^ m' = χ ^ m := pow_mod_orderOf χ m
  have hnEq : χ ^ n' = χ ^ n := pow_mod_orderOf χ n
  have hkEq : χ ^ k' = χ ^ k := pow_mod_orderOf χ k
  have hlEq : χ ^ l' = χ ^ l := pow_mod_orderOf χ l
  have hsEq : χ ^ s' = χ ^ s := pow_mod_orderOf χ s
  have hoEq : χ ^ o' = χ ^ o := pow_mod_orderOf χ o
  have hqEq : χ ^ q' = χ ^ q := pow_mod_orderOf χ q
  have hrEq : χ ^ r' = χ ^ r := pow_mod_orderOf χ r
  have hpowM' : χ ^ m' ≠ 1 := by simpa only [hmEq] using hpowM
  have hpowN' : χ ^ n' ≠ 1 := by simpa only [hnEq] using hpowN
  have hpowK' : χ ^ k' ≠ 1 := by simpa only [hkEq] using hpowK
  have hpowL' : χ ^ l' ≠ 1 := by simpa only [hlEq] using hpowL
  have hpowS' : χ ^ s' ≠ 1 := by simpa only [hsEq] using hpowS
  have hpowO' : χ ^ o' ≠ 1 := by simpa only [hoEq] using hpowO
  have hpowQ' : χ ^ q' ≠ 1 := by simpa only [hqEq] using hpowQ
  have hpowR' : χ ^ r' ≠ 1 := by simpa only [hrEq] using hpowR
  have hsumEq :
      χ ^ (m' + n' + k' + l' + s' + o' + q' + r') =
        χ ^ (m + n + k + l + s + o + q + r) := by
    simp only [pow_add, hmEq, hnEq, hkEq, hlEq, hsEq, hoEq, hqEq, hrEq]
  have hpowSum' : χ ^ (m' + n' + k' + l' + s' + o' + q' + r') ≠ 1 := by
    simpa only [hsumEq] using hpowSum
  have hbound := hweil p hp χ m' n' k' l' s' o' q' r'
    lam mu nu xi rho sigma tau
    hmLt hnLt hkLt hlLt hsLt hoLt hqLt hrLt
    hpowM' hpowN' hpowK' hpowL' hpowS' hpowO' hpowQ' hpowR' hpowSum'
    hlam hmu hnu hxi hrho hsigma htau
    hlammu hlamnu hlamxi hlamrho hlamsigma hlamtau
    hmunu hmuxi hmurho hmusigma hmutau
    hnuxi hnurho hnusigma hnutau
    hxirho hxisigma hxitau hrhosigma hrhotau hsigmatau
  simpa only [hmEq, hnEq, hkEq, hlEq, hsEq, hoEq, hqEq, hrEq] using hbound

/-- Nine scalar denominators whose product is one cancel without expanding
the surrounding character expressions. -/
private theorem nine_div_product_eq_of_denominator_product_eq_one
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ)
    (hb : b₁ * b₂ * b₃ * b₄ * b₅ * b₆ * b₇ * b₈ * b₉ = 1) :
    a₁ / b₁ * (a₂ / b₂) * (a₃ / b₃) * (a₄ / b₄) *
        (a₅ / b₅) * (a₆ / b₆) * (a₇ / b₇) * (a₈ / b₈) * (a₉ / b₉) =
      a₁ * a₂ * a₃ * a₄ * a₅ * a₆ * a₇ * a₈ * a₉ := by
  have hb0 : b₁ * b₂ * b₃ * b₄ * b₅ * b₆ * b₇ * b₈ * b₉ ≠ 0 := by
    rw [hb]
    exact one_ne_zero
  have hb₁ : b₁ ≠ 0 := fun h => hb0 (by simp [h])
  have hb₂ : b₂ ≠ 0 := fun h => hb0 (by simp [h])
  have hb₃ : b₃ ≠ 0 := fun h => hb0 (by simp [h])
  have hb₄ : b₄ ≠ 0 := fun h => hb0 (by simp [h])
  have hb₅ : b₅ ≠ 0 := fun h => hb0 (by simp [h])
  have hb₆ : b₆ ≠ 0 := fun h => hb0 (by simp [h])
  have hb₇ : b₇ ≠ 0 := fun h => hb0 (by simp [h])
  have hb₈ : b₈ ≠ 0 := fun h => hb0 (by simp [h])
  have hb₉ : b₉ ≠ 0 := fun h => hb0 (by simp [h])
  field_simp [hb₁, hb₂, hb₃, hb₄, hb₅, hb₆, hb₇, hb₈, hb₉]
  linear_combination
    -(a₁ * a₂ * a₃ * a₄ * a₅ * a₆ * a₇ * a₈ * a₉) * hb

set_option maxHeartbeats 4000000 in
/-- Pointwise nine-root Möbius reduction away from the deleted projective
point. Triviality of the nine-character product cancels the denominator and
leaves eight finite character factors. -/
theorem nineRootMobius_term
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ η θ ι : MulChar (ZMod p) ℂ)
    (hprod : α * β * γ * δ * ε * ζ * η * θ * ι = 1)
    (a b c d e f g h i : ZMod p)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (hec : e ≠ c) (hfc : f ≠ c) (hgc : g ≠ c) (hhc : h ≠ c) (hic : i ≠ c)
    (y : ZMod p) (hy : y ≠ 1) :
    let mob := threeRootMobiusEquiv p a c hac
    let lam := (a - b) / (c - b)
    let mu := (a - d) / (c - d)
    let nu := (a - e) / (c - e)
    let xi := (a - f) / (c - f)
    let rho := (a - g) / (c - g)
    let sigma := (a - h) / (c - h)
    let tau := (a - i) / (c - i)
    α (mob.symm y - a) * β (mob.symm y - b) * γ (mob.symm y - c) *
        δ (mob.symm y - d) * ε (mob.symm y - e) * ζ (mob.symm y - f) *
          η (mob.symm y - g) * θ (mob.symm y - h) * ι (mob.symm y - i) =
      (α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
          ε (c - e) * ζ (c - f) * η (c - g) * θ (c - h) * ι (c - i)) *
        (α y * β (y - lam) * δ (y - mu) * ε (y - nu) * ζ (y - xi) *
          η (y - rho) * θ (y - sigma) * ι (y - tau)) := by
  dsimp only
  rw [threeRootMobiusEquiv_symm_apply, if_neg hy]
  have hden : y - 1 ≠ 0 := sub_ne_zero.mpr hy
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr hbc.symm
  have hcd : c - d ≠ 0 := sub_ne_zero.mpr hdc.symm
  have hce : c - e ≠ 0 := sub_ne_zero.mpr hec.symm
  have hcf : c - f ≠ 0 := sub_ne_zero.mpr hfc.symm
  have hcg : c - g ≠ 0 := sub_ne_zero.mpr hgc.symm
  have hch : c - h ≠ 0 := sub_ne_zero.mpr hhc.symm
  have hci : c - i ≠ 0 := sub_ne_zero.mpr hic.symm
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
  have hxg : (y * c - a) / (y - 1) - g =
      (c - g) * (y - (a - g) / (c - g)) / (y - 1) := by
    field_simp
    ring
  have hxh : (y * c - a) / (y - 1) - h =
      (c - h) * (y - (a - h) / (c - h)) / (y - 1) := by
    field_simp
    ring
  have hxi : (y * c - a) / (y - 1) - i =
      (c - i) * (y - (a - i) / (c - i)) / (y - 1) := by
    field_simp
    ring
  rw [hxa, hxb, hxc, hxd, hxe, hxf, hxg, hxh, hxi]
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
  have hmapdivη (u v : ZMod p) : η (u / v) = η u / η v := by
    exact map_div₀ η.toMonoidWithZeroHom u v
  have hmapdivθ (u v : ZMod p) : θ (u / v) = θ u / θ v := by
    exact map_div₀ θ.toMonoidWithZeroHom u v
  have hmapdivι (u v : ZMod p) : ι (u / v) = ι u / ι v := by
    exact map_div₀ ι.toMonoidWithZeroHom u v
  have hcancel :
      α (y - 1) * β (y - 1) * γ (y - 1) * δ (y - 1) *
          ε (y - 1) * ζ (y - 1) * η (y - 1) * θ (y - 1) * ι (y - 1) = 1 := by
    rw [← MulChar.mul_apply, ← MulChar.mul_apply, ← MulChar.mul_apply,
      ← MulChar.mul_apply, ← MulChar.mul_apply, ← MulChar.mul_apply,
      ← MulChar.mul_apply, ← MulChar.mul_apply, hprod]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hden)
  calc
    α (y * (c - a) / (y - 1)) *
          β ((c - b) * (y - (a - b) / (c - b)) / (y - 1)) *
          γ ((c - a) / (y - 1)) *
          δ ((c - d) * (y - (a - d) / (c - d)) / (y - 1)) *
          ε ((c - e) * (y - (a - e) / (c - e)) / (y - 1)) *
          ζ ((c - f) * (y - (a - f) / (c - f)) / (y - 1)) *
          η ((c - g) * (y - (a - g) / (c - g)) / (y - 1)) *
          θ ((c - h) * (y - (a - h) / (c - h)) / (y - 1)) *
          ι ((c - i) * (y - (a - i) / (c - i)) / (y - 1)) =
        ((α y * α (c - a)) / α (y - 1)) *
          ((β (c - b) * β (y - (a - b) / (c - b))) / β (y - 1)) *
          (γ (c - a) / γ (y - 1)) *
          ((δ (c - d) * δ (y - (a - d) / (c - d))) / δ (y - 1)) *
          ((ε (c - e) * ε (y - (a - e) / (c - e))) / ε (y - 1)) *
          ((ζ (c - f) * ζ (y - (a - f) / (c - f))) / ζ (y - 1)) *
          ((η (c - g) * η (y - (a - g) / (c - g))) / η (y - 1)) *
          ((θ (c - h) * θ (y - (a - h) / (c - h))) / θ (y - 1)) *
          ((ι (c - i) * ι (y - (a - i) / (c - i))) / ι (y - 1)) := by
      rw [hmapdivα, map_mul, hmapdivβ, map_mul, hmapdivγ,
        hmapdivδ, map_mul, hmapdivε, map_mul, hmapdivζ, map_mul,
        hmapdivη, map_mul, hmapdivθ, map_mul, hmapdivι, map_mul]
    _ = (α y * α (c - a)) *
          (β (c - b) * β (y - (a - b) / (c - b))) * γ (c - a) *
          (δ (c - d) * δ (y - (a - d) / (c - d))) *
          (ε (c - e) * ε (y - (a - e) / (c - e))) *
          (ζ (c - f) * ζ (y - (a - f) / (c - f))) *
          (η (c - g) * η (y - (a - g) / (c - g))) *
          (θ (c - h) * θ (y - (a - h) / (c - h))) *
          (ι (c - i) * ι (y - (a - i) / (c - i))) := by
      exact nine_div_product_eq_of_denominator_product_eq_one
        (α y * α (c - a))
        (β (c - b) * β (y - (a - b) / (c - b)))
        (γ (c - a))
        (δ (c - d) * δ (y - (a - d) / (c - d)))
        (ε (c - e) * ε (y - (a - e) / (c - e)))
        (ζ (c - f) * ζ (y - (a - f) / (c - f)))
        (η (c - g) * η (y - (a - g) / (c - g)))
        (θ (c - h) * θ (y - (a - h) / (c - h)))
        (ι (c - i) * ι (y - (a - i) / (c - i)))
        (α (y - 1)) (β (y - 1)) (γ (y - 1)) (δ (y - 1))
        (ε (y - 1)) (ζ (y - 1)) (η (y - 1)) (θ (y - 1)) (ι (y - 1)) hcancel
    _ = (α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
          ε (c - e) * ζ (c - f) * η (c - g) * θ (c - h) * ι (c - i)) *
        (α y * β (y - (a - b) / (c - b)) *
          δ (y - (a - d) / (c - d)) * ε (y - (a - e) / (c - e)) *
          ζ (y - (a - f) / (c - f)) * η (y - (a - g) / (c - g)) *
            θ (y - (a - h) / (c - h)) * ι (y - (a - i) / (c - i))) := by
      ac_rfl

/-- A degree-balanced nine-root sum is a eight-point sum with one deleted
projective value, up to a character-valued constant. -/
theorem nineRootMulCharSum_eq_eightPointSum_sub
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ η θ ι : MulChar (ZMod p) ℂ)
    (hprod : α * β * γ * δ * ε * ζ * η * θ * ι = 1)
    (a b c d e f g h i : ZMod p)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (hec : e ≠ c) (hfc : f ≠ c) (hgc : g ≠ c) (hhc : h ≠ c) (hic : i ≠ c) :
    let lam := (a - b) / (c - b)
    let mu := (a - d) / (c - d)
    let nu := (a - e) / (c - e)
    let xi := (a - f) / (c - f)
    let rho := (a - g) / (c - g)
    let sigma := (a - h) / (c - h)
    let tau := (a - i) / (c - i)
    (∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
          ε (x - e) * ζ (x - f) * η (x - g) * θ (x - h) * ι (x - i)) =
      (α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
          ε (c - e) * ζ (c - f) * η (c - g) * θ (c - h) * ι (c - i)) *
        ((∑ y : ZMod p,
            α y * β (y - lam) * δ (y - mu) * ε (y - nu) * ζ (y - xi) *
              η (y - rho) * θ (y - sigma) * ι (y - tau)) -
          β (1 - lam) * δ (1 - mu) * ε (1 - nu) * ζ (1 - xi) *
            η (1 - rho) * θ (1 - sigma) * ι (1 - tau)) := by
  dsimp only
  let mob := threeRootMobiusEquiv p a c hac
  let F : ZMod p → ℂ := fun x =>
    α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
      ε (x - e) * ζ (x - f) * η (x - g) * θ (x - h) * ι (x - i)
  let G : ZMod p → ℂ := fun y =>
    α y * β (y - (a - b) / (c - b)) * δ (y - (a - d) / (c - d)) *
      ε (y - (a - e) / (c - e)) * ζ (y - (a - f) / (c - f)) *
        η (y - (a - g) / (c - g)) * θ (y - (a - h) / (c - h)) *
          ι (y - (a - i) / (c - i))
  let C : ℂ :=
    α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
      ε (c - e) * ζ (c - f) * η (c - g) * θ (c - h) * ι (c - i)
  have hone : F (mob.symm 1) = 0 := by
    simp [F, mob, γ.map_zero]
  have hterm (y : ZMod p) (hy : y ∈ Finset.univ.erase 1) :
      F (mob.symm y) = C * G y := by
    have hyOne : y ≠ 1 := by simpa using hy
    simpa [F, G, C, mob] using
      nineRootMobius_term p α β γ δ ε ζ η θ ι hprod a b c d e f g h i
        hac hbc hdc hec hfc hgc hhc hic y hyOne
  calc
    (∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
          ε (x - e) * ζ (x - f) * η (x - g) * θ (x - h) * ι (x - i)) =
        ∑ x : ZMod p, F x := by rfl
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

/-- Once the canonical eight-point trace is bounded, the nine-root identity
costs only the single deleted projective value. -/
theorem norm_nineRootMulCharSum_le_seven_mul_sqrt_add_one_of_eightPoint
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ η θ ι : MulChar (ZMod p) ℂ)
    (hprod : α * β * γ * δ * ε * ζ * η * θ * ι = 1)
    (a b c d e f g h i : ZMod p)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (hec : e ≠ c) (hfc : f ≠ c) (hgc : g ≠ c) (hhc : h ≠ c) (hic : i ≠ c)
    (height :
      ‖∑ y : ZMod p,
        α y * β (y - (a - b) / (c - b)) *
          δ (y - (a - d) / (c - d)) *
          ε (y - (a - e) / (c - e)) *
          ζ (y - (a - f) / (c - f)) *
          η (y - (a - g) / (c - g)) *
          θ (y - (a - h) / (c - h)) *
          ι (y - (a - i) / (c - i))‖ ≤ 7 * Real.sqrt p) :
    ‖∑ x : ZMod p,
      α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
        ε (x - e) * ζ (x - f) * η (x - g) * θ (x - h) * ι (x - i)‖ ≤
      7 * Real.sqrt p + 1 := by
  rw [nineRootMulCharSum_eq_eightPointSum_sub
    p α β γ δ ε ζ η θ ι hprod a b c d e f g h i
      hac hbc hdc hec hfc hgc hhc hic]
  simp only [norm_mul]
  have hC :
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ *
          ‖ε (c - e)‖ * ‖ζ (c - f)‖ * ‖η (c - g)‖ * ‖θ (c - h)‖ *
            ‖ι (c - i)‖ ≤ 1 := by
    calc
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ *
            ‖ε (c - e)‖ * ‖ζ (c - f)‖ * ‖η (c - g)‖ * ‖θ (c - h)‖ *
              ‖ι (c - i)‖ ≤ 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one α _
        · exact DirichletCharacter.norm_le_one β _
        · exact DirichletCharacter.norm_le_one γ _
        · exact DirichletCharacter.norm_le_one δ _
        · exact DirichletCharacter.norm_le_one ε _
        · exact DirichletCharacter.norm_le_one ζ _
        · exact DirichletCharacter.norm_le_one η _
        · exact DirichletCharacter.norm_le_one θ _
        · exact DirichletCharacter.norm_le_one ι _
      _ = 1 := by norm_num
  have hdeleted :
      ‖β (1 - (a - b) / (c - b)) * δ (1 - (a - d) / (c - d)) *
          ε (1 - (a - e) / (c - e)) * ζ (1 - (a - f) / (c - f)) *
            η (1 - (a - g) / (c - g)) * θ (1 - (a - h) / (c - h)) *
              ι (1 - (a - i) / (c - i))‖ ≤ 1 := by
    simp only [norm_mul]
    calc
      ‖β (1 - (a - b) / (c - b))‖ * ‖δ (1 - (a - d) / (c - d))‖ *
            ‖ε (1 - (a - e) / (c - e))‖ * ‖ζ (1 - (a - f) / (c - f))‖ *
              ‖η (1 - (a - g) / (c - g))‖ *
                ‖θ (1 - (a - h) / (c - h))‖ *
                  ‖ι (1 - (a - i) / (c - i))‖ ≤ 1 * 1 * 1 * 1 * 1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one β _
        · exact DirichletCharacter.norm_le_one δ _
        · exact DirichletCharacter.norm_le_one ε _
        · exact DirichletCharacter.norm_le_one ζ _
        · exact DirichletCharacter.norm_le_one η _
        · exact DirichletCharacter.norm_le_one θ _
        · exact DirichletCharacter.norm_le_one ι _
      _ = 1 := by norm_num
  let T : ℂ := ∑ y : ZMod p,
    α y * β (y - (a - b) / (c - b)) *
      δ (y - (a - d) / (c - d)) * ε (y - (a - e) / (c - e)) *
      ζ (y - (a - f) / (c - f)) * η (y - (a - g) / (c - g)) *
        θ (y - (a - h) / (c - h)) * ι (y - (a - i) / (c - i))
  let D : ℂ :=
    β (1 - (a - b) / (c - b)) * δ (1 - (a - d) / (c - d)) *
      ε (1 - (a - e) / (c - e)) * ζ (1 - (a - f) / (c - f)) *
        η (1 - (a - g) / (c - g)) * θ (1 - (a - h) / (c - h)) *
          ι (1 - (a - i) / (c - i))
  calc
    (‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ *
          ‖ε (c - e)‖ * ‖ζ (c - f)‖ * ‖η (c - g)‖ * ‖θ (c - h)‖ *
            ‖ι (c - i)‖) * ‖T - D‖ ≤
        1 * ‖T - D‖ := by gcongr
    _ ≤ ‖T‖ + ‖D‖ := by simpa using norm_sub_le T D
    _ ≤ 7 * Real.sqrt p + 1 := by
      exact add_le_add (by simpa [T] using height) (by simpa [D] using hdeleted)

/-- The eight-point power endpoint gives the projective estimate for nine
distinct roots whose nine local powers multiply to one. -/
theorem norm_nineRootMulCharPowerSum_le_seven_mul_sqrt_add_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerEightPointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (m n k l s o q z rExp : ℕ)
    (hpowM : χ ^ m ≠ 1) (hpowN : χ ^ n ≠ 1) (hpowK : χ ^ k ≠ 1)
    (hpowL : χ ^ l ≠ 1) (hpowS : χ ^ s ≠ 1) (hpowO : χ ^ o ≠ 1)
    (hpowQ : χ ^ q ≠ 1)
    (hpowZ : χ ^ z ≠ 1)
    (hpowR : χ ^ rExp ≠ 1)
    (hprod :
      (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) * (χ ^ o) *
        (χ ^ q) * (χ ^ z) * (χ ^ rExp) = 1)
    (a b c d e f g h i : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (haf : a ≠ f) (hag : a ≠ g) (hah : a ≠ h) (hai : a ≠ i)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hbg : b ≠ g) (hbh : b ≠ h) (hbi : b ≠ i)
    (hdc : d ≠ c) (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hdh : d ≠ h) (hdi : d ≠ i)
    (hec : e ≠ c) (hef : e ≠ f) (heg : e ≠ g) (heh : e ≠ h) (hei : e ≠ i)
    (hfc : f ≠ c) (hfg : f ≠ g) (hfh : f ≠ h) (hfi : f ≠ i)
    (hgc : g ≠ c) (hgh : g ≠ h) (hgi : g ≠ i)
    (hhc : h ≠ c) (hhi : h ≠ i) (hic : i ≠ c) :
    ‖∑ x : ZMod p,
      (χ ^ m) (x - a) * (χ ^ n) (x - b) * (χ ^ k) (x - c) *
        (χ ^ l) (x - d) * (χ ^ s) (x - e) * (χ ^ o) (x - f) *
          (χ ^ q) (x - g) * (χ ^ z) (x - h) * (χ ^ rExp) (x - i)‖ ≤
      7 * Real.sqrt p + 1 := by
  let lam : ZMod p := (a - b) / (c - b)
  let mu : ZMod p := (a - d) / (c - d)
  let nu : ZMod p := (a - e) / (c - e)
  let xi : ZMod p := (a - f) / (c - f)
  let rho : ZMod p := (a - g) / (c - g)
  let sigma : ZMod p := (a - h) / (c - h)
  let tau : ZMod p := (a - i) / (c - i)
  have hlam : lam ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hbc.symm)
  have hmu : mu ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr had) (sub_ne_zero.mpr hdc.symm)
  have hnu : nu ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hae) (sub_ne_zero.mpr hec.symm)
  have hxi : xi ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr haf) (sub_ne_zero.mpr hfc.symm)
  have hrho : rho ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hag) (sub_ne_zero.mpr hgc.symm)
  have hsigma : sigma ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hah) (sub_ne_zero.mpr hhc.symm)
  have htau : tau ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hai) (sub_ne_zero.mpr hic.symm)
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
  have hlamrho : lam ≠ rho := crossRatio_ne hbc hgc hbg
  have hlamsigma : lam ≠ sigma := crossRatio_ne hbc hhc hbh
  have hlamtau : lam ≠ tau := crossRatio_ne hbc hic hbi
  have hmunu : mu ≠ nu := crossRatio_ne hdc hec hde
  have hmuxi : mu ≠ xi := crossRatio_ne hdc hfc hdf
  have hmurho : mu ≠ rho := crossRatio_ne hdc hgc hdg
  have hmusigma : mu ≠ sigma := crossRatio_ne hdc hhc hdh
  have hmutau : mu ≠ tau := crossRatio_ne hdc hic hdi
  have hnuxi : nu ≠ xi := crossRatio_ne hec hfc hef
  have hnurho : nu ≠ rho := crossRatio_ne hec hgc heg
  have hnusigma : nu ≠ sigma := crossRatio_ne hec hhc heh
  have hnutau : nu ≠ tau := crossRatio_ne hec hic hei
  have hxirho : xi ≠ rho := crossRatio_ne hfc hgc hfg
  have hxisigma : xi ≠ sigma := crossRatio_ne hfc hhc hfh
  have hxitau : xi ≠ tau := crossRatio_ne hfc hic hfi
  have hrhosigma : rho ≠ sigma := crossRatio_ne hgc hhc hgh
  have hrhotau : rho ≠ tau := crossRatio_ne hgc hic hgi
  have hsigmatau : sigma ≠ tau := crossRatio_ne hhc hic hhi
  have hfiniteProd : χ ^ (m + n + l + s + o + q + z + rExp) ≠ 1 := by
    intro heq
    apply hpowK
    calc
      χ ^ k = 1 * χ ^ k := by simp
      _ = χ ^ (m + n + l + s + o + q + z + rExp) * χ ^ k := by rw [heq]
      _ = (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) * (χ ^ o) *
          (χ ^ q) * (χ ^ z) * (χ ^ rExp) := by
        simp only [pow_add]
        ac_rfl
      _ = 1 := hprod
  have height :
      ‖∑ y : ZMod p,
        (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ l) (y - mu) *
          (χ ^ s) (y - nu) * (χ ^ o) (y - xi) * (χ ^ q) (y - rho) *
            (χ ^ z) (y - sigma) * (χ ^ rExp) (y - tau)‖ ≤ 7 * Real.sqrt p :=
    hweil χ m n l s o q z rExp lam mu nu xi rho sigma tau
      hpowM hpowN hpowL hpowS hpowO hpowQ hpowZ hpowR hfiniteProd
      hlam hmu hnu hxi hrho hsigma htau
      hlammu hlamnu hlamxi hlamrho hlamsigma hlamtau
      hmunu hmuxi hmurho hmusigma hmutau
      hnuxi hnurho hnusigma hnutau
      hxirho hxisigma hxitau hrhosigma hrhotau hsigmatau
  exact norm_nineRootMulCharSum_le_seven_mul_sqrt_add_one_of_eightPoint
    p (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l) (χ ^ s) (χ ^ o) (χ ^ q) (χ ^ z)
      (χ ^ rExp) hprod a b c d e f g h i hac hbc hdc hec hfc hgc hhc hic height

set_option maxHeartbeats 4000000 in
/-- Exactly nine active roots of character-order-divisible degree reduce to
the source-shaped eight-point endpoint. -/
theorem norm_primeActiveRootCharacterSum_le_seven_mul_sqrt_add_one_of_card_eq_nine_degree_power
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerEightPointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 9) :
    ‖primeActiveRootCharacterSum p χ P‖ ≤ 7 * Real.sqrt p + 1 := by
  let S := primeActiveRoots p χ P
  obtain ⟨u, huS⟩ : S.Nonempty := Finset.card_pos.mp (by simp [S, hcard])
  have hcardS : S.card = 9 := by simpa only [S] using hcard
  have hcardOne : (S.erase u).card = 8 := by
    rw [Finset.card_erase_of_mem huS]
    omega
  obtain ⟨v, hvOne⟩ : (S.erase u).Nonempty := Finset.card_pos.mp (by omega)
  have hcardTwo : ((S.erase u).erase v).card = 7 := by
    rw [Finset.card_erase_of_mem hvOne, hcardOne]
  obtain ⟨w, hwTwo⟩ : ((S.erase u).erase v).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardThree : (((S.erase u).erase v).erase w).card = 6 := by
    rw [Finset.card_erase_of_mem hwTwo, hcardTwo]
  obtain ⟨z, hzThree⟩ : (((S.erase u).erase v).erase w).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardFour : ((((S.erase u).erase v).erase w).erase z).card = 5 := by
    rw [Finset.card_erase_of_mem hzThree, hcardThree]
  obtain ⟨t, htFour⟩ : ((((S.erase u).erase v).erase w).erase z).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardFive : (((((S.erase u).erase v).erase w).erase z).erase t).card = 4 := by
    rw [Finset.card_erase_of_mem htFour, hcardFour]
  obtain ⟨q, r, x, y, hqr, hqx, hqy, hrx, hry, hxy, hrest⟩ :=
    Finset.card_eq_four.mp hcardFive
  have hqFive : q ∈ ((((S.erase u).erase v).erase w).erase z).erase t := by
    simp [hrest]
  have hrFive : r ∈ ((((S.erase u).erase v).erase w).erase z).erase t := by
    simp [hrest]
  have hxFive : x ∈ ((((S.erase u).erase v).erase w).erase z).erase t := by
    simp [hrest]
  have hyFive : y ∈ ((((S.erase u).erase v).erase w).erase z).erase t := by
    simp [hrest]
  have hvData : v ≠ u ∧ v ∈ S := by
    simpa only [Finset.mem_erase] using hvOne
  have hwData : w ≠ v ∧ w ≠ u ∧ w ∈ S := by
    simpa only [Finset.mem_erase] using hwTwo
  have hzData : z ≠ w ∧ z ≠ v ∧ z ≠ u ∧ z ∈ S := by
    simpa only [Finset.mem_erase] using hzThree
  have htData : t ≠ z ∧ t ≠ w ∧ t ≠ v ∧ t ≠ u ∧ t ∈ S := by
    simpa only [Finset.mem_erase] using htFour
  have hqData : q ≠ t ∧ q ≠ z ∧ q ≠ w ∧ q ≠ v ∧ q ≠ u ∧ q ∈ S := by
    simpa only [Finset.mem_erase] using hqFive
  have hrData : r ≠ t ∧ r ≠ z ∧ r ≠ w ∧ r ≠ v ∧ r ≠ u ∧ r ∈ S := by
    simpa only [Finset.mem_erase] using hrFive
  have hxData : x ≠ t ∧ x ≠ z ∧ x ≠ w ∧ x ≠ v ∧ x ≠ u ∧ x ∈ S := by
    simpa only [Finset.mem_erase] using hxFive
  have hyData : y ≠ t ∧ y ≠ z ∧ y ≠ w ∧ y ≠ v ∧ y ≠ u ∧ y ∈ S := by
    simpa only [Finset.mem_erase] using hyFive
  have huv : u ≠ v := hvData.1.symm
  have huw : u ≠ w := hwData.2.1.symm
  have huz : u ≠ z := hzData.2.2.1.symm
  have hut : u ≠ t := htData.2.2.2.1.symm
  have huq : u ≠ q := hqData.2.2.2.2.1.symm
  have hur : u ≠ r := hrData.2.2.2.2.1.symm
  have hux : u ≠ x := hxData.2.2.2.2.1.symm
  have huy : u ≠ y := hyData.2.2.2.2.1.symm
  have hvw : v ≠ w := hwData.1.symm
  have hvz : v ≠ z := hzData.2.1.symm
  have hvt : v ≠ t := htData.2.2.1.symm
  have hvq : v ≠ q := hqData.2.2.2.1.symm
  have hvr : v ≠ r := hrData.2.2.2.1.symm
  have hvx : v ≠ x := hxData.2.2.2.1.symm
  have hvy : v ≠ y := hyData.2.2.2.1.symm
  have hwz : w ≠ z := hzData.1.symm
  have hwt : w ≠ t := htData.2.1.symm
  have hwq : w ≠ q := hqData.2.2.1.symm
  have hwr : w ≠ r := hrData.2.2.1.symm
  have hwx : w ≠ x := hxData.2.2.1.symm
  have hwy : w ≠ y := hyData.2.2.1.symm
  have hzt : z ≠ t := htData.1.symm
  have hzq : z ≠ q := hqData.2.1.symm
  have hzr : z ≠ r := hrData.2.1.symm
  have hzx : z ≠ x := hxData.2.1.symm
  have hzy : z ≠ y := hyData.2.1.symm
  have htq : t ≠ q := hqData.1.symm
  have htr : t ≠ r := hrData.1.symm
  have htx : t ≠ x := hxData.1.symm
  have hty : t ≠ y := hyData.1.symm
  have hvS : v ∈ S := hvData.2
  have hwS : w ∈ S := hwData.2.2
  have hzS : z ∈ S := hzData.2.2.2
  have htS : t ∈ S := htData.2.2.2.2
  have hqS : q ∈ S := hqData.2.2.2.2.2
  have hrS : r ∈ S := hrData.2.2.2.2.2
  have hxS : x ∈ S := hxData.2.2.2.2.2
  have hyS : y ∈ S := hyData.2.2.2.2.2
  have hroots : S = {u, v, w, z, t, q, r, x, y} := by
    calc
      S = insert u (S.erase u) := (Finset.insert_erase huS).symm
      _ = insert u (insert v ((S.erase u).erase v)) := by
        rw [Finset.insert_erase hvOne]
      _ = insert u (insert v (insert w (((S.erase u).erase v).erase w))) := by
        rw [Finset.insert_erase hwTwo]
      _ = insert u (insert v (insert w
          (insert z ((((S.erase u).erase v).erase w).erase z)))) := by
        rw [Finset.insert_erase hzThree]
      _ = insert u (insert v (insert w (insert z
          (insert t (((((S.erase u).erase v).erase w).erase z).erase t))))) := by
        rw [Finset.insert_erase htFour]
      _ = {u, v, w, z, t, q, r, x, y} := by rw [hrest]
  have huActive : u ∈ primeActiveRoots p χ P := by simpa only [S] using huS
  have hvActive : v ∈ primeActiveRoots p χ P := by simpa only [S] using hvS
  have hwActive : w ∈ primeActiveRoots p χ P := by simpa only [S] using hwS
  have hzActive : z ∈ primeActiveRoots p χ P := by simpa only [S] using hzS
  have htActive : t ∈ primeActiveRoots p χ P := by simpa only [S] using htS
  have hqActive : q ∈ primeActiveRoots p χ P := by simpa only [S] using hqS
  have hrActive : r ∈ primeActiveRoots p χ P := by simpa only [S] using hrS
  have hxActive : x ∈ primeActiveRoots p χ P := by simpa only [S] using hxS
  have hyActive : y ∈ primeActiveRoots p χ P := by simpa only [S] using hyS
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
  have hrRoot : r ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hrActive
  have hxRoot : x ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hxActive
  have hyRoot : y ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hyActive
  let m := P.roots.count u
  let n := P.roots.count v
  let k := P.roots.count w
  let l := P.roots.count z
  let s := P.roots.count t
  let o := P.roots.count q
  let qn := P.roots.count r
  let zn := P.roots.count x
  let rn := P.roots.count y
  have hm : m ≠ 0 := (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp huRoot)).ne'
  have hn : n ≠ 0 := (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hvRoot)).ne'
  have hk : k ≠ 0 := (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hwRoot)).ne'
  have hl : l ≠ 0 := (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hzRoot)).ne'
  have hs : s ≠ 0 := (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp htRoot)).ne'
  have ho : o ≠ 0 := (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hqRoot)).ne'
  have hqn : qn ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hrRoot)).ne'
  have hzn : zn ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hxRoot)).ne'
  have hrn : rn ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hyRoot)).ne'
  have hpowM : χ ^ m ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp huActive).2 (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowN : χ ^ n ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hvActive).2 (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowK : χ ^ k ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hwActive).2 (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowL : χ ^ l ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hzActive).2 (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowS : χ ^ s ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp htActive).2 (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowO : χ ^ o ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hqActive).2 (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowQn : χ ^ qn ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hrActive).2 (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowZn : χ ^ zn ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hxActive).2 (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowRn : χ ^ rn ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hyActive).2 (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hsum := orderOf_dvd_sum_primeActiveRoots_count p χ P hP hdegree
  have hmnklsoqzr : orderOf χ ∣ m + n + k + l + s + o + qn + zn + rn := by
    simpa [S, hroots, huv, huw, huz, hut, huq, hur, hux, huy,
      hvw, hvz, hvt, hvq, hvr, hvx, hvy,
      hwz, hwt, hwq, hwr, hwx, hwy,
      hzt, hzq, hzr, hzx, hzy, htq, htr, htx, hty,
      hqr, hqx, hqy, hrx, hry, hxy,
      m, n, k, l, s, o, qn, zn, rn,
      add_assoc, add_comm, add_left_comm] using hsum
  have hprod :
      (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) * (χ ^ o) *
        (χ ^ qn) * (χ ^ zn) * (χ ^ rn) = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add, ← pow_add]
    exact orderOf_dvd_iff_pow_eq_one.mp hmnklsoqzr
  have hnine := norm_nineRootMulCharPowerSum_le_seven_mul_sqrt_add_one
    p hweil χ m n k l s o qn zn rn
      hpowM hpowN hpowK hpowL hpowS hpowO hpowQn hpowZn hpowRn hprod
      u v w z t q r x y huv huw huz hut huq hur hux huy
      hvw hvz hvt hvq hvr hvx hvy
      hwz.symm hzt hzq hzr hzx hzy
      hwt.symm htq htr htx hty
      hwq.symm hqr hqx hqy hwr.symm hrx hry hwx.symm hxy hwy.symm
  unfold primeActiveRootCharacterSum
  rw [show primeActiveRoots p χ P = {u, v, w, z, t, q, r, x, y} by
    simpa [S] using hroots]
  convert hnine using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro x _hx
  simp [huv, huw, huz, hut, huq, hur, hux, huy,
    hvw, hvz, hvt, hvq, hvr, hvx, hvy,
    hwz, hwt, hwq, hwr, hwx, hwy,
    hzt, hzq, hzr, hzx, hzy, htq, htr, htx, hty,
    hqr, hqx, hqy, hrx, hry, hxy]
  rw [MulChar.pow_apply' χ hm, MulChar.pow_apply' χ hn,
    MulChar.pow_apply' χ hk, MulChar.pow_apply' χ hl,
    MulChar.pow_apply' χ hs, MulChar.pow_apply' χ ho, MulChar.pow_apply' χ hqn,
    MulChar.pow_apply' χ hzn, MulChar.pow_apply' χ hrn]
  simp [m, n, k, l, s, o, qn, zn, rn, Polynomial.count_roots]
  ac_rfl

/-- The eight-point power endpoint discharges the split-polynomial target when
exactly nine roots are active and degree is character-order divisible. -/
theorem primeSplitPolynomialWeilBound_of_card_activeRoots_eq_nine_degree_power
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerEightPointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (_a : ZMod p) (_hχ : χ ≠ 1) (hP : P.Splits)
    (_hnot : ¬orderOf χ ∣ P.rootMultiplicity _a)
    (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 9) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
  have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
  have hactive :=
    norm_primeActiveRootCharacterSum_le_seven_mul_sqrt_add_one_of_card_eq_nine_degree_power
      p hweil χ P hP hdegree hcard
  have hrestricted :=
    norm_filter_primeActiveRootProduct_le_of_activeRootCharacterSum
      p χ P (7 * Real.sqrt p + 1) hactive
  have hrootCard : 9 ≤ P.roots.toFinset.card := by
    rw [← hcard]
    exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
  have hInactiveCard :
      (primeInactiveRoots p χ P).card ≤ P.roots.toFinset.card :=
    Finset.card_le_card (primeInactiveRoots_subset_roots p χ P)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hroom :
      7 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
    have hInactiveCard' :
        ((primeInactiveRoots p χ P).card : ℝ) ≤
          (P.roots.toFinset.card : ℝ) := by exact_mod_cast hInactiveCard
    have hrootCard' : (9 : ℝ) ≤ P.roots.toFinset.card := by
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
    _ ≤ 7 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card := by
      simpa using hrestricted
    _ ≤ ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := hroom

end

end Tao2026
