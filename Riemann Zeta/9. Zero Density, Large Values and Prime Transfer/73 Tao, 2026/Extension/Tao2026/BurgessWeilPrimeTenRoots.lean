import Tao2026.BurgessWeilPrimeNineRoots

/-!
# Ten active roots in the prime Burgess sum

This file isolates the next source-shaped endpoint obtained by sending one
of ten degree-balanced active roots to infinity. The nine finite local
characters remain powers of one Burgess character, and scaling normalizes
their marked points to `0`, `1`, `t`, `u`, `v`, `w`, `z`, `r₀`, and `s₀`.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The source-shaped nine-point endpoint at one prime. -/
def TaoPrimePowerNinePointHypergeometricWeilBoundAt
    (p : ℕ) [NeZero p] [Fact p.Prime] : Prop :=
  ∀ (χ : MulChar (ZMod p) ℂ) (m n k l s o q r j : ℕ)
    (lam mu nu xi rho sigma tau upsilon : ZMod p),
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 →
    χ ^ s ≠ 1 → χ ^ o ≠ 1 → χ ^ q ≠ 1 → χ ^ r ≠ 1 → χ ^ j ≠ 1 →
    χ ^ (m + n + k + l + s + o + q + r + j) ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → nu ≠ 0 → xi ≠ 0 → rho ≠ 0 → sigma ≠ 0 → tau ≠ 0 →
    upsilon ≠ 0 →
    lam ≠ mu → lam ≠ nu → lam ≠ xi → lam ≠ rho → lam ≠ sigma → lam ≠ tau →
    lam ≠ upsilon →
    mu ≠ nu → mu ≠ xi → mu ≠ rho → mu ≠ sigma → mu ≠ tau → mu ≠ upsilon →
    nu ≠ xi → nu ≠ rho → nu ≠ sigma → nu ≠ tau → nu ≠ upsilon →
    xi ≠ rho → xi ≠ sigma → xi ≠ tau → xi ≠ upsilon →
    rho ≠ sigma → rho ≠ tau → rho ≠ upsilon →
    sigma ≠ tau → sigma ≠ upsilon → tau ≠ upsilon →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ k) (y - mu) *
        (χ ^ l) (y - nu) * (χ ^ s) (y - xi) * (χ ^ o) (y - rho) *
          (χ ^ q) (y - sigma) * (χ ^ r) (y - tau) *
            (χ ^ j) (y - upsilon)‖ ≤ 8 * Real.sqrt p

/-- The large-characteristic range needed by the exact Burgess branch. -/
def TaoPrimePowerNinePointHypergeometricWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime],
    64 < p → TaoPrimePowerNinePointHypergeometricWeilBoundAt p

/-- Finite exponent-range form of the source-shaped nine-point endpoint. -/
def TaoPrimeReducedPowerNinePointHypergeometricWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime], 64 < p →
    ∀ (χ : MulChar (ZMod p) ℂ) (m n k l s o q r j : ℕ)
      (lam mu nu xi rho sigma tau upsilon : ZMod p),
    m < orderOf χ → n < orderOf χ → k < orderOf χ →
    l < orderOf χ → s < orderOf χ → o < orderOf χ → q < orderOf χ →
    r < orderOf χ → j < orderOf χ →
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 →
    χ ^ s ≠ 1 → χ ^ o ≠ 1 → χ ^ q ≠ 1 → χ ^ r ≠ 1 → χ ^ j ≠ 1 →
    χ ^ (m + n + k + l + s + o + q + r + j) ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → nu ≠ 0 → xi ≠ 0 → rho ≠ 0 → sigma ≠ 0 → tau ≠ 0 →
    upsilon ≠ 0 →
    lam ≠ mu → lam ≠ nu → lam ≠ xi → lam ≠ rho → lam ≠ sigma → lam ≠ tau →
    lam ≠ upsilon →
    mu ≠ nu → mu ≠ xi → mu ≠ rho → mu ≠ sigma → mu ≠ tau → mu ≠ upsilon →
    nu ≠ xi → nu ≠ rho → nu ≠ sigma → nu ≠ tau → nu ≠ upsilon →
    xi ≠ rho → xi ≠ sigma → xi ≠ tau → xi ≠ upsilon →
    rho ≠ sigma → rho ≠ tau → rho ≠ upsilon →
    sigma ≠ tau → sigma ≠ upsilon → tau ≠ upsilon →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ k) (y - mu) *
        (χ ^ l) (y - nu) * (χ ^ s) (y - xi) * (χ ^ o) (y - rho) *
          (χ ^ q) (y - sigma) * (χ ^ r) (y - tau) *
            (χ ^ j) (y - upsilon)‖ ≤ 8 * Real.sqrt p

/-- Scaling by the first nonzero point puts a nine-point sum into the
seven-parameter Legendre form `0`, `1`, `t`, `u`, `v`, `w`, `z`, `r₀`, `s₀`. -/
theorem ninePointMulCharSum_eq_legendreForm
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ η θ ι : MulChar (ZMod p) ℂ)
    (lam mu nu xi rho sigma tau upsilon : ZMod p) (hlam : lam ≠ 0) :
    (∑ y : ZMod p,
      α y * β (y - lam) * γ (y - mu) * δ (y - nu) * ε (y - xi) *
        ζ (y - rho) * η (y - sigma) * θ (y - tau) * ι (y - upsilon)) =
      (α lam * β lam * γ lam * δ lam * ε lam * ζ lam * η lam * θ lam * ι lam) *
        ∑ t : ZMod p,
          α t * β (t - 1) * γ (t - mu / lam) * δ (t - nu / lam) *
            ε (t - xi / lam) * ζ (t - rho / lam) * η (t - sigma / lam) *
              θ (t - tau / lam) * ι (t - upsilon / lam) := by
  let e : ZMod p ≃ ZMod p := Equiv.mulLeft₀ lam hlam
  calc
    (∑ y : ZMod p,
        α y * β (y - lam) * γ (y - mu) * δ (y - nu) * ε (y - xi) *
          ζ (y - rho) * η (y - sigma) * θ (y - tau) * ι (y - upsilon)) =
        ∑ t : ZMod p,
          α (e t) * β (e t - lam) * γ (e t - mu) * δ (e t - nu) *
            ε (e t - xi) * ζ (e t - rho) * η (e t - sigma) * θ (e t - tau) *
              ι (e t - upsilon) :=
      (Equiv.sum_comp e
        (fun y : ZMod p =>
          α y * β (y - lam) * γ (y - mu) * δ (y - nu) * ε (y - xi) *
            ζ (y - rho) * η (y - sigma) * θ (y - tau) * ι (y - upsilon))).symm
    _ = (α lam * β lam * γ lam * δ lam * ε lam * ζ lam * η lam * θ lam * ι lam) *
        ∑ t : ZMod p,
          α t * β (t - 1) * γ (t - mu / lam) * δ (t - nu / lam) *
            ε (t - xi / lam) * ζ (t - rho / lam) * η (t - sigma / lam) *
              θ (t - tau / lam) * ι (t - upsilon / lam) := by
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
      have hsubUpsilon : lam * t - upsilon = lam * (t - upsilon / lam) := by field_simp
      dsimp [e]
      rw [hsubOne, hsubMu, hsubNu, hsubXi, hsubRho, hsubSigma, hsubTau, hsubUpsilon,
        map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
      ring

/-- The final seven-parameter analytic boundary for ten active roots. -/
def TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime], 64 < p →
    ∀ (χ : MulChar (ZMod p) ℂ) (m n k l s o q r j : ℕ)
      (t u v w z r₀ s₀ : ZMod p),
    m < orderOf χ → n < orderOf χ → k < orderOf χ →
    l < orderOf χ → s < orderOf χ → o < orderOf χ → q < orderOf χ →
    r < orderOf χ → j < orderOf χ →
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 →
    χ ^ s ≠ 1 → χ ^ o ≠ 1 → χ ^ q ≠ 1 → χ ^ r ≠ 1 → χ ^ j ≠ 1 →
    χ ^ (m + n + k + l + s + o + q + r + j) ≠ 1 →
    t ≠ 0 → u ≠ 0 → v ≠ 0 → w ≠ 0 → z ≠ 0 → r₀ ≠ 0 → s₀ ≠ 0 →
    t ≠ 1 → u ≠ 1 → v ≠ 1 → w ≠ 1 → z ≠ 1 → r₀ ≠ 1 → s₀ ≠ 1 →
    t ≠ u → t ≠ v → t ≠ w → t ≠ z → t ≠ r₀ → t ≠ s₀ →
    u ≠ v → u ≠ w → u ≠ z → u ≠ r₀ → u ≠ s₀ →
    v ≠ w → v ≠ z → v ≠ r₀ → v ≠ s₀ →
    w ≠ z → w ≠ r₀ → w ≠ s₀ → z ≠ r₀ → z ≠ s₀ → r₀ ≠ s₀ →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - t) *
        (χ ^ l) (y - u) * (χ ^ s) (y - v) * (χ ^ o) (y - w) *
          (χ ^ q) (y - z) * (χ ^ r) (y - r₀) * (χ ^ j) (y - s₀)‖ ≤
      8 * Real.sqrt p

theorem TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour.toNinePoint
    (hweil : TaoPrimeReducedPowerNinePointLegendreWeilBoundAboveSixtyFour) :
    TaoPrimeReducedPowerNinePointHypergeometricWeilBoundAboveSixtyFour := by
  intro p _ _ hp χ m n k l s o q r j lam mu nu xi rho sigma tau upsilon
    hm hn hk hl hs ho hq hr hj
    hpowM hpowN hpowK hpowL hpowS hpowO hpowQ hpowR hpowJ hpowSum
    hlam hmu hnu hxi hrho hsigma htau hupsilon
    hlammu hlamnu hlamxi hlamrho hlamsigma hlamtau hlamupsilon
    hmunu hmuxi hmurho hmusigma hmutau hmuupsilon
    hnuxi hnurho hnusigma hnutau hnuupsilon
    hxirho hxisigma hxitau hxiupsilon
    hrhosigma hrhotau hrhoupsilon hsigmatau hsigmaupsilon htauupsilon
  let t : ZMod p := mu / lam
  let u : ZMod p := nu / lam
  let v : ZMod p := xi / lam
  let w : ZMod p := rho / lam
  let z : ZMod p := sigma / lam
  let r₀ : ZMod p := tau / lam
  let s₀ : ZMod p := upsilon / lam
  have ht0 : t ≠ 0 := div_ne_zero hmu hlam
  have hu0 : u ≠ 0 := div_ne_zero hnu hlam
  have hv0 : v ≠ 0 := div_ne_zero hxi hlam
  have hw0 : w ≠ 0 := div_ne_zero hrho hlam
  have hz0 : z ≠ 0 := div_ne_zero hsigma hlam
  have hr₀0 : r₀ ≠ 0 := div_ne_zero htau hlam
  have hs₀0 : s₀ ≠ 0 := div_ne_zero hupsilon hlam
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
  have hs₀1 : s₀ ≠ 1 := by
    intro heq
    apply hlamupsilon
    dsimp [s₀] at heq
    rw [div_eq_one_iff_eq hlam] at heq
    exact heq.symm
  have htu : t ≠ u := fun heq => hmunu ((div_left_inj' hlam).mp heq)
  have htv : t ≠ v := fun heq => hmuxi ((div_left_inj' hlam).mp heq)
  have htw : t ≠ w := fun heq => hmurho ((div_left_inj' hlam).mp heq)
  have htz : t ≠ z := fun heq => hmusigma ((div_left_inj' hlam).mp heq)
  have htr₀ : t ≠ r₀ := fun heq => hmutau ((div_left_inj' hlam).mp heq)
  have hts₀ : t ≠ s₀ := fun heq => hmuupsilon ((div_left_inj' hlam).mp heq)
  have huv : u ≠ v := fun heq => hnuxi ((div_left_inj' hlam).mp heq)
  have huw : u ≠ w := fun heq => hnurho ((div_left_inj' hlam).mp heq)
  have huz : u ≠ z := fun heq => hnusigma ((div_left_inj' hlam).mp heq)
  have hur₀ : u ≠ r₀ := fun heq => hnutau ((div_left_inj' hlam).mp heq)
  have hus₀ : u ≠ s₀ := fun heq => hnuupsilon ((div_left_inj' hlam).mp heq)
  have hvw : v ≠ w := fun heq => hxirho ((div_left_inj' hlam).mp heq)
  have hvz : v ≠ z := fun heq => hxisigma ((div_left_inj' hlam).mp heq)
  have hvr₀ : v ≠ r₀ := fun heq => hxitau ((div_left_inj' hlam).mp heq)
  have hvs₀ : v ≠ s₀ := fun heq => hxiupsilon ((div_left_inj' hlam).mp heq)
  have hwz : w ≠ z := fun heq => hrhosigma ((div_left_inj' hlam).mp heq)
  have hwr₀ : w ≠ r₀ := fun heq => hrhotau ((div_left_inj' hlam).mp heq)
  have hws₀ : w ≠ s₀ := fun heq => hrhoupsilon ((div_left_inj' hlam).mp heq)
  have hzr₀ : z ≠ r₀ := fun heq => hsigmatau ((div_left_inj' hlam).mp heq)
  have hzs₀ : z ≠ s₀ := fun heq => hsigmaupsilon ((div_left_inj' hlam).mp heq)
  have hr₀s₀ : r₀ ≠ s₀ := fun heq => htauupsilon ((div_left_inj' hlam).mp heq)
  have hbound := hweil p hp χ m n k l s o q r j t u v w z r₀ s₀
    hm hn hk hl hs ho hq hr hj
    hpowM hpowN hpowK hpowL hpowS hpowO hpowQ hpowR hpowJ hpowSum
    ht0 hu0 hv0 hw0 hz0 hr₀0 hs₀0 ht1 hu1 hv1 hw1 hz1 hr₀1 hs₀1
    htu htv htw htz htr₀ hts₀ huv huw huz hur₀ hus₀ hvw hvz hvr₀ hvs₀
    hwz hwr₀ hws₀ hzr₀ hzs₀ hr₀s₀
  rw [ninePointMulCharSum_eq_legendreForm
    p (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l) (χ ^ s) (χ ^ o) (χ ^ q) (χ ^ r) (χ ^ j)
      lam mu nu xi rho sigma tau upsilon hlam]
  simp only [norm_mul]
  have hC :
      ‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖ *
          ‖(χ ^ s) lam‖ * ‖(χ ^ o) lam‖ * ‖(χ ^ q) lam‖ * ‖(χ ^ r) lam‖ *
            ‖(χ ^ j) lam‖ ≤ 1 := by
    calc
      ‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖ *
            ‖(χ ^ s) lam‖ * ‖(χ ^ o) lam‖ * ‖(χ ^ q) lam‖ * ‖(χ ^ r) lam‖ *
              ‖(χ ^ j) lam‖ ≤
          1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one (χ ^ m) lam
        · exact DirichletCharacter.norm_le_one (χ ^ n) lam
        · exact DirichletCharacter.norm_le_one (χ ^ k) lam
        · exact DirichletCharacter.norm_le_one (χ ^ l) lam
        · exact DirichletCharacter.norm_le_one (χ ^ s) lam
        · exact DirichletCharacter.norm_le_one (χ ^ o) lam
        · exact DirichletCharacter.norm_le_one (χ ^ q) lam
        · exact DirichletCharacter.norm_le_one (χ ^ r) lam
        · exact DirichletCharacter.norm_le_one (χ ^ j) lam
      _ = 1 := by norm_num
  calc
    (‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖ *
          ‖(χ ^ s) lam‖ * ‖(χ ^ o) lam‖ * ‖(χ ^ q) lam‖ * ‖(χ ^ r) lam‖ *
            ‖(χ ^ j) lam‖) *
        ‖∑ y : ZMod p,
          (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - mu / lam) *
            (χ ^ l) (y - nu / lam) * (χ ^ s) (y - xi / lam) *
              (χ ^ o) (y - rho / lam) * (χ ^ q) (y - sigma / lam) *
                (χ ^ r) (y - tau / lam) * (χ ^ j) (y - upsilon / lam)‖ ≤
      1 * ‖∑ y : ZMod p,
        (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - mu / lam) *
          (χ ^ l) (y - nu / lam) * (χ ^ s) (y - xi / lam) *
            (χ ^ o) (y - rho / lam) * (χ ^ q) (y - sigma / lam) *
              (χ ^ r) (y - tau / lam) * (χ ^ j) (y - upsilon / lam)‖ := by gcongr
    _ ≤ 8 * Real.sqrt p := by simpa [t, u, v, w, z, r₀, s₀] using hbound

theorem TaoPrimeReducedPowerNinePointHypergeometricWeilBoundAboveSixtyFour.toPower
    (hweil : TaoPrimeReducedPowerNinePointHypergeometricWeilBoundAboveSixtyFour) :
    TaoPrimePowerNinePointHypergeometricWeilBoundAboveSixtyFour := by
  intro p _ _ hp χ m n k l s o q r j lam mu nu xi rho sigma tau upsilon
    hpowM hpowN hpowK hpowL hpowS hpowO hpowQ hpowR hpowJ hpowSum
    hlam hmu hnu hxi hrho hsigma htau hupsilon
    hlammu hlamnu hlamxi hlamrho hlamsigma hlamtau hlamupsilon
    hmunu hmuxi hmurho hmusigma hmutau hmuupsilon
    hnuxi hnurho hnusigma hnutau hnuupsilon
    hxirho hxisigma hxitau hxiupsilon
    hrhosigma hrhotau hrhoupsilon hsigmatau hsigmaupsilon htauupsilon
  let m' := m % orderOf χ
  let n' := n % orderOf χ
  let k' := k % orderOf χ
  let l' := l % orderOf χ
  let s' := s % orderOf χ
  let o' := o % orderOf χ
  let q' := q % orderOf χ
  let r' := r % orderOf χ
  let j' := j % orderOf χ
  have hord : 0 < orderOf χ := orderOf_pos χ
  have hmLt : m' < orderOf χ := Nat.mod_lt m hord
  have hnLt : n' < orderOf χ := Nat.mod_lt n hord
  have hkLt : k' < orderOf χ := Nat.mod_lt k hord
  have hlLt : l' < orderOf χ := Nat.mod_lt l hord
  have hsLt : s' < orderOf χ := Nat.mod_lt s hord
  have hoLt : o' < orderOf χ := Nat.mod_lt o hord
  have hqLt : q' < orderOf χ := Nat.mod_lt q hord
  have hrLt : r' < orderOf χ := Nat.mod_lt r hord
  have hjLt : j' < orderOf χ := Nat.mod_lt j hord
  have hmEq : χ ^ m' = χ ^ m := pow_mod_orderOf χ m
  have hnEq : χ ^ n' = χ ^ n := pow_mod_orderOf χ n
  have hkEq : χ ^ k' = χ ^ k := pow_mod_orderOf χ k
  have hlEq : χ ^ l' = χ ^ l := pow_mod_orderOf χ l
  have hsEq : χ ^ s' = χ ^ s := pow_mod_orderOf χ s
  have hoEq : χ ^ o' = χ ^ o := pow_mod_orderOf χ o
  have hqEq : χ ^ q' = χ ^ q := pow_mod_orderOf χ q
  have hrEq : χ ^ r' = χ ^ r := pow_mod_orderOf χ r
  have hjEq : χ ^ j' = χ ^ j := pow_mod_orderOf χ j
  have hpowM' : χ ^ m' ≠ 1 := by simpa only [hmEq] using hpowM
  have hpowN' : χ ^ n' ≠ 1 := by simpa only [hnEq] using hpowN
  have hpowK' : χ ^ k' ≠ 1 := by simpa only [hkEq] using hpowK
  have hpowL' : χ ^ l' ≠ 1 := by simpa only [hlEq] using hpowL
  have hpowS' : χ ^ s' ≠ 1 := by simpa only [hsEq] using hpowS
  have hpowO' : χ ^ o' ≠ 1 := by simpa only [hoEq] using hpowO
  have hpowQ' : χ ^ q' ≠ 1 := by simpa only [hqEq] using hpowQ
  have hpowR' : χ ^ r' ≠ 1 := by simpa only [hrEq] using hpowR
  have hpowJ' : χ ^ j' ≠ 1 := by simpa only [hjEq] using hpowJ
  have hsumEq :
      χ ^ (m' + n' + k' + l' + s' + o' + q' + r' + j') =
        χ ^ (m + n + k + l + s + o + q + r + j) := by
    simp only [pow_add, hmEq, hnEq, hkEq, hlEq, hsEq, hoEq, hqEq, hrEq, hjEq]
  have hpowSum' : χ ^ (m' + n' + k' + l' + s' + o' + q' + r' + j') ≠ 1 := by
    simpa only [hsumEq] using hpowSum
  have hbound := hweil p hp χ m' n' k' l' s' o' q' r' j'
    lam mu nu xi rho sigma tau upsilon
    hmLt hnLt hkLt hlLt hsLt hoLt hqLt hrLt hjLt
    hpowM' hpowN' hpowK' hpowL' hpowS' hpowO' hpowQ' hpowR' hpowJ' hpowSum'
    hlam hmu hnu hxi hrho hsigma htau hupsilon
    hlammu hlamnu hlamxi hlamrho hlamsigma hlamtau hlamupsilon
    hmunu hmuxi hmurho hmusigma hmutau hmuupsilon
    hnuxi hnurho hnusigma hnutau hnuupsilon
    hxirho hxisigma hxitau hxiupsilon
    hrhosigma hrhotau hrhoupsilon hsigmatau hsigmaupsilon htauupsilon
  simpa only [hmEq, hnEq, hkEq, hlEq, hsEq, hoEq, hqEq, hrEq, hjEq] using hbound

/-- Ten scalar denominators whose product is one cancel without expanding
the surrounding character expressions. -/
private theorem ten_div_product_eq_of_denominator_product_eq_one
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ : ℂ)
    (hb : b₁ * b₂ * b₃ * b₄ * b₅ * b₆ * b₇ * b₈ * b₉ * b₁₀ = 1) :
    a₁ / b₁ * (a₂ / b₂) * (a₃ / b₃) * (a₄ / b₄) *
        (a₅ / b₅) * (a₆ / b₆) * (a₇ / b₇) * (a₈ / b₈) * (a₉ / b₉) * (a₁₀ / b₁₀) =
      a₁ * a₂ * a₃ * a₄ * a₅ * a₆ * a₇ * a₈ * a₉ * a₁₀ := by
  have hb0 : b₁ * b₂ * b₃ * b₄ * b₅ * b₆ * b₇ * b₈ * b₉ * b₁₀ ≠ 0 := by
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
  have hb₁₀ : b₁₀ ≠ 0 := fun h => hb0 (by simp [h])
  field_simp [hb₁, hb₂, hb₃, hb₄, hb₅, hb₆, hb₇, hb₈, hb₉, hb₁₀]
  linear_combination
    -(a₁ * a₂ * a₃ * a₄ * a₅ * a₆ * a₇ * a₈ * a₉ * a₁₀) * hb

set_option maxHeartbeats 4000000 in
/-- Pointwise ten-root Möbius reduction away from the deleted projective
point. Triviality of the ten-character product cancels the denominator and
leaves nine finite character factors. -/
theorem tenRootMobius_term
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ η θ ι κ : MulChar (ZMod p) ℂ)
    (hprod : α * β * γ * δ * ε * ζ * η * θ * ι * κ = 1)
    (a b c d e f g h i j : ZMod p)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (hec : e ≠ c) (hfc : f ≠ c) (hgc : g ≠ c) (hhc : h ≠ c) (hic : i ≠ c)
    (hjc : j ≠ c)
    (y : ZMod p) (hy : y ≠ 1) :
    let mob := threeRootMobiusEquiv p a c hac
    let lam := (a - b) / (c - b)
    let mu := (a - d) / (c - d)
    let nu := (a - e) / (c - e)
    let xi := (a - f) / (c - f)
    let rho := (a - g) / (c - g)
    let sigma := (a - h) / (c - h)
    let tau := (a - i) / (c - i)
    let upsilon := (a - j) / (c - j)
    α (mob.symm y - a) * β (mob.symm y - b) * γ (mob.symm y - c) *
        δ (mob.symm y - d) * ε (mob.symm y - e) * ζ (mob.symm y - f) *
          η (mob.symm y - g) * θ (mob.symm y - h) * ι (mob.symm y - i) *
            κ (mob.symm y - j) =
      (α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
          ε (c - e) * ζ (c - f) * η (c - g) * θ (c - h) * ι (c - i) * κ (c - j)) *
        (α y * β (y - lam) * δ (y - mu) * ε (y - nu) * ζ (y - xi) *
          η (y - rho) * θ (y - sigma) * ι (y - tau) * κ (y - upsilon)) := by
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
  have hcj : c - j ≠ 0 := sub_ne_zero.mpr hjc.symm
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
  have hxj : (y * c - a) / (y - 1) - j =
      (c - j) * (y - (a - j) / (c - j)) / (y - 1) := by
    field_simp
    ring
  rw [hxa, hxb, hxc, hxd, hxe, hxf, hxg, hxh, hxi, hxj]
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
  have hmapdivκ (u v : ZMod p) : κ (u / v) = κ u / κ v := by
    exact map_div₀ κ.toMonoidWithZeroHom u v
  have hcancel :
      α (y - 1) * β (y - 1) * γ (y - 1) * δ (y - 1) *
          ε (y - 1) * ζ (y - 1) * η (y - 1) * θ (y - 1) * ι (y - 1) *
            κ (y - 1) = 1 := by
    rw [← MulChar.mul_apply, ← MulChar.mul_apply, ← MulChar.mul_apply,
      ← MulChar.mul_apply, ← MulChar.mul_apply, ← MulChar.mul_apply,
      ← MulChar.mul_apply, ← MulChar.mul_apply, ← MulChar.mul_apply, hprod]
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
          ι ((c - i) * (y - (a - i) / (c - i)) / (y - 1)) *
          κ ((c - j) * (y - (a - j) / (c - j)) / (y - 1)) =
        ((α y * α (c - a)) / α (y - 1)) *
          ((β (c - b) * β (y - (a - b) / (c - b))) / β (y - 1)) *
          (γ (c - a) / γ (y - 1)) *
          ((δ (c - d) * δ (y - (a - d) / (c - d))) / δ (y - 1)) *
          ((ε (c - e) * ε (y - (a - e) / (c - e))) / ε (y - 1)) *
          ((ζ (c - f) * ζ (y - (a - f) / (c - f))) / ζ (y - 1)) *
          ((η (c - g) * η (y - (a - g) / (c - g))) / η (y - 1)) *
          ((θ (c - h) * θ (y - (a - h) / (c - h))) / θ (y - 1)) *
          ((ι (c - i) * ι (y - (a - i) / (c - i))) / ι (y - 1)) *
          ((κ (c - j) * κ (y - (a - j) / (c - j))) / κ (y - 1)) := by
      rw [hmapdivα, map_mul, hmapdivβ, map_mul, hmapdivγ,
        hmapdivδ, map_mul, hmapdivε, map_mul, hmapdivζ, map_mul,
        hmapdivη, map_mul, hmapdivθ, map_mul, hmapdivι, map_mul,
        hmapdivκ, map_mul]
    _ = (α y * α (c - a)) *
          (β (c - b) * β (y - (a - b) / (c - b))) * γ (c - a) *
          (δ (c - d) * δ (y - (a - d) / (c - d))) *
          (ε (c - e) * ε (y - (a - e) / (c - e))) *
          (ζ (c - f) * ζ (y - (a - f) / (c - f))) *
          (η (c - g) * η (y - (a - g) / (c - g))) *
          (θ (c - h) * θ (y - (a - h) / (c - h))) *
          (ι (c - i) * ι (y - (a - i) / (c - i))) *
          (κ (c - j) * κ (y - (a - j) / (c - j))) := by
      exact ten_div_product_eq_of_denominator_product_eq_one
        (α y * α (c - a))
        (β (c - b) * β (y - (a - b) / (c - b)))
        (γ (c - a))
        (δ (c - d) * δ (y - (a - d) / (c - d)))
        (ε (c - e) * ε (y - (a - e) / (c - e)))
        (ζ (c - f) * ζ (y - (a - f) / (c - f)))
        (η (c - g) * η (y - (a - g) / (c - g)))
        (θ (c - h) * θ (y - (a - h) / (c - h)))
        (ι (c - i) * ι (y - (a - i) / (c - i)))
        (κ (c - j) * κ (y - (a - j) / (c - j)))
        (α (y - 1)) (β (y - 1)) (γ (y - 1)) (δ (y - 1))
        (ε (y - 1)) (ζ (y - 1)) (η (y - 1)) (θ (y - 1)) (ι (y - 1))
        (κ (y - 1)) hcancel
    _ = (α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
          ε (c - e) * ζ (c - f) * η (c - g) * θ (c - h) * ι (c - i) * κ (c - j)) *
        (α y * β (y - (a - b) / (c - b)) *
          δ (y - (a - d) / (c - d)) * ε (y - (a - e) / (c - e)) *
          ζ (y - (a - f) / (c - f)) * η (y - (a - g) / (c - g)) *
            θ (y - (a - h) / (c - h)) * ι (y - (a - i) / (c - i)) *
              κ (y - (a - j) / (c - j))) := by
      ac_rfl

/-- A degree-balanced ten-root sum is a nine-point sum with one deleted
projective value, up to a character-valued constant. -/
theorem tenRootMulCharSum_eq_ninePointSum_sub
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ η θ ι κ : MulChar (ZMod p) ℂ)
    (hprod : α * β * γ * δ * ε * ζ * η * θ * ι * κ = 1)
    (a b c d e f g h i j : ZMod p)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (hec : e ≠ c) (hfc : f ≠ c) (hgc : g ≠ c) (hhc : h ≠ c) (hic : i ≠ c)
    (hjc : j ≠ c) :
    let lam := (a - b) / (c - b)
    let mu := (a - d) / (c - d)
    let nu := (a - e) / (c - e)
    let xi := (a - f) / (c - f)
    let rho := (a - g) / (c - g)
    let sigma := (a - h) / (c - h)
    let tau := (a - i) / (c - i)
    let upsilon := (a - j) / (c - j)
    (∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
          ε (x - e) * ζ (x - f) * η (x - g) * θ (x - h) * ι (x - i) * κ (x - j)) =
      (α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
          ε (c - e) * ζ (c - f) * η (c - g) * θ (c - h) * ι (c - i) * κ (c - j)) *
        ((∑ y : ZMod p,
            α y * β (y - lam) * δ (y - mu) * ε (y - nu) * ζ (y - xi) *
              η (y - rho) * θ (y - sigma) * ι (y - tau) * κ (y - upsilon)) -
          β (1 - lam) * δ (1 - mu) * ε (1 - nu) * ζ (1 - xi) *
            η (1 - rho) * θ (1 - sigma) * ι (1 - tau) * κ (1 - upsilon)) := by
  dsimp only
  let mob := threeRootMobiusEquiv p a c hac
  let F : ZMod p → ℂ := fun x =>
    α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
      ε (x - e) * ζ (x - f) * η (x - g) * θ (x - h) * ι (x - i) * κ (x - j)
  let G : ZMod p → ℂ := fun y =>
    α y * β (y - (a - b) / (c - b)) * δ (y - (a - d) / (c - d)) *
      ε (y - (a - e) / (c - e)) * ζ (y - (a - f) / (c - f)) *
        η (y - (a - g) / (c - g)) * θ (y - (a - h) / (c - h)) *
          ι (y - (a - i) / (c - i)) * κ (y - (a - j) / (c - j))
  let C : ℂ :=
    α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
      ε (c - e) * ζ (c - f) * η (c - g) * θ (c - h) * ι (c - i) * κ (c - j)
  have hone : F (mob.symm 1) = 0 := by
    simp [F, mob, γ.map_zero]
  have hterm (y : ZMod p) (hy : y ∈ Finset.univ.erase 1) :
      F (mob.symm y) = C * G y := by
    have hyOne : y ≠ 1 := by simpa using hy
    simpa [F, G, C, mob] using
      tenRootMobius_term p α β γ δ ε ζ η θ ι κ hprod a b c d e f g h i j
        hac hbc hdc hec hfc hgc hhc hic hjc y hyOne
  calc
    (∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
          ε (x - e) * ζ (x - f) * η (x - g) * θ (x - h) * ι (x - i) * κ (x - j)) =
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

/-- Once the canonical nine-point trace is bounded, the ten-root identity
costs only the single deleted projective value. -/
theorem norm_tenRootMulCharSum_le_eight_mul_sqrt_add_one_of_ninePoint
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ η θ ι κ : MulChar (ZMod p) ℂ)
    (hprod : α * β * γ * δ * ε * ζ * η * θ * ι * κ = 1)
    (a b c d e f g h i j : ZMod p)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (hec : e ≠ c) (hfc : f ≠ c) (hgc : g ≠ c) (hhc : h ≠ c) (hic : i ≠ c)
    (hjc : j ≠ c)
    (height :
      ‖∑ y : ZMod p,
        α y * β (y - (a - b) / (c - b)) *
          δ (y - (a - d) / (c - d)) *
          ε (y - (a - e) / (c - e)) *
          ζ (y - (a - f) / (c - f)) *
          η (y - (a - g) / (c - g)) *
          θ (y - (a - h) / (c - h)) *
          ι (y - (a - i) / (c - i)) * κ (y - (a - j) / (c - j))‖ ≤
        8 * Real.sqrt p) :
    ‖∑ x : ZMod p,
      α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
        ε (x - e) * ζ (x - f) * η (x - g) * θ (x - h) * ι (x - i) * κ (x - j)‖ ≤
      8 * Real.sqrt p + 1 := by
  rw [tenRootMulCharSum_eq_ninePointSum_sub
    p α β γ δ ε ζ η θ ι κ hprod a b c d e f g h i j
      hac hbc hdc hec hfc hgc hhc hic hjc]
  simp only [norm_mul]
  have hC :
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ *
          ‖ε (c - e)‖ * ‖ζ (c - f)‖ * ‖η (c - g)‖ * ‖θ (c - h)‖ *
            ‖ι (c - i)‖ * ‖κ (c - j)‖ ≤ 1 := by
    calc
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ *
            ‖ε (c - e)‖ * ‖ζ (c - f)‖ * ‖η (c - g)‖ * ‖θ (c - h)‖ *
              ‖ι (c - i)‖ * ‖κ (c - j)‖ ≤ 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 := by
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
        · exact DirichletCharacter.norm_le_one κ _
      _ = 1 := by norm_num
  have hdeleted :
      ‖β (1 - (a - b) / (c - b)) * δ (1 - (a - d) / (c - d)) *
          ε (1 - (a - e) / (c - e)) * ζ (1 - (a - f) / (c - f)) *
            η (1 - (a - g) / (c - g)) * θ (1 - (a - h) / (c - h)) *
              ι (1 - (a - i) / (c - i)) * κ (1 - (a - j) / (c - j))‖ ≤ 1 := by
    simp only [norm_mul]
    calc
      ‖β (1 - (a - b) / (c - b))‖ * ‖δ (1 - (a - d) / (c - d))‖ *
            ‖ε (1 - (a - e) / (c - e))‖ * ‖ζ (1 - (a - f) / (c - f))‖ *
              ‖η (1 - (a - g) / (c - g))‖ *
                ‖θ (1 - (a - h) / (c - h))‖ *
                  ‖ι (1 - (a - i) / (c - i))‖ *
                    ‖κ (1 - (a - j) / (c - j))‖ ≤ 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one β _
        · exact DirichletCharacter.norm_le_one δ _
        · exact DirichletCharacter.norm_le_one ε _
        · exact DirichletCharacter.norm_le_one ζ _
        · exact DirichletCharacter.norm_le_one η _
        · exact DirichletCharacter.norm_le_one θ _
        · exact DirichletCharacter.norm_le_one ι _
        · exact DirichletCharacter.norm_le_one κ _
      _ = 1 := by norm_num
  let T : ℂ := ∑ y : ZMod p,
    α y * β (y - (a - b) / (c - b)) *
      δ (y - (a - d) / (c - d)) * ε (y - (a - e) / (c - e)) *
      ζ (y - (a - f) / (c - f)) * η (y - (a - g) / (c - g)) *
        θ (y - (a - h) / (c - h)) * ι (y - (a - i) / (c - i)) *
          κ (y - (a - j) / (c - j))
  let D : ℂ :=
    β (1 - (a - b) / (c - b)) * δ (1 - (a - d) / (c - d)) *
      ε (1 - (a - e) / (c - e)) * ζ (1 - (a - f) / (c - f)) *
        η (1 - (a - g) / (c - g)) * θ (1 - (a - h) / (c - h)) *
          ι (1 - (a - i) / (c - i)) * κ (1 - (a - j) / (c - j))
  calc
    (‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ *
          ‖ε (c - e)‖ * ‖ζ (c - f)‖ * ‖η (c - g)‖ * ‖θ (c - h)‖ *
            ‖ι (c - i)‖ * ‖κ (c - j)‖) * ‖T - D‖ ≤
        1 * ‖T - D‖ := by gcongr
    _ ≤ ‖T‖ + ‖D‖ := by simpa using norm_sub_le T D
    _ ≤ 8 * Real.sqrt p + 1 := by
      exact add_le_add (by simpa [T] using height) (by simpa [D] using hdeleted)

/-- The nine-point power endpoint gives the projective estimate for ten
distinct roots whose ten local powers multiply to one. -/
theorem norm_tenRootMulCharPowerSum_le_eight_mul_sqrt_add_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerNinePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (m n k l s o q z rExp tExp : ℕ)
    (hpowM : χ ^ m ≠ 1) (hpowN : χ ^ n ≠ 1) (hpowK : χ ^ k ≠ 1)
    (hpowL : χ ^ l ≠ 1) (hpowS : χ ^ s ≠ 1) (hpowO : χ ^ o ≠ 1)
    (hpowQ : χ ^ q ≠ 1)
    (hpowZ : χ ^ z ≠ 1)
    (hpowR : χ ^ rExp ≠ 1)
    (hpowT : χ ^ tExp ≠ 1)
    (hprod :
      (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) * (χ ^ o) *
        (χ ^ q) * (χ ^ z) * (χ ^ rExp) * (χ ^ tExp) = 1)
    (a b c d e f g h i j : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (haf : a ≠ f) (hag : a ≠ g) (hah : a ≠ h) (hai : a ≠ i) (haj : a ≠ j)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hbg : b ≠ g) (hbh : b ≠ h) (hbi : b ≠ i) (hbj : b ≠ j)
    (hdc : d ≠ c) (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hdh : d ≠ h) (hdi : d ≠ i) (hdj : d ≠ j)
    (hec : e ≠ c) (hef : e ≠ f) (heg : e ≠ g) (heh : e ≠ h) (hei : e ≠ i)
    (hej : e ≠ j)
    (hfc : f ≠ c) (hfg : f ≠ g) (hfh : f ≠ h) (hfi : f ≠ i) (hfj : f ≠ j)
    (hgc : g ≠ c) (hgh : g ≠ h) (hgi : g ≠ i) (hgj : g ≠ j)
    (hhc : h ≠ c) (hhi : h ≠ i) (hhj : h ≠ j)
    (hic : i ≠ c) (hij : i ≠ j) (hjc : j ≠ c) :
    ‖∑ x : ZMod p,
      (χ ^ m) (x - a) * (χ ^ n) (x - b) * (χ ^ k) (x - c) *
        (χ ^ l) (x - d) * (χ ^ s) (x - e) * (χ ^ o) (x - f) *
          (χ ^ q) (x - g) * (χ ^ z) (x - h) * (χ ^ rExp) (x - i) *
            (χ ^ tExp) (x - j)‖ ≤
      8 * Real.sqrt p + 1 := by
  let lam : ZMod p := (a - b) / (c - b)
  let mu : ZMod p := (a - d) / (c - d)
  let nu : ZMod p := (a - e) / (c - e)
  let xi : ZMod p := (a - f) / (c - f)
  let rho : ZMod p := (a - g) / (c - g)
  let sigma : ZMod p := (a - h) / (c - h)
  let tau : ZMod p := (a - i) / (c - i)
  let upsilon : ZMod p := (a - j) / (c - j)
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
  have hupsilon : upsilon ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr haj) (sub_ne_zero.mpr hjc.symm)
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
  have hlamupsilon : lam ≠ upsilon := crossRatio_ne hbc hjc hbj
  have hmunu : mu ≠ nu := crossRatio_ne hdc hec hde
  have hmuxi : mu ≠ xi := crossRatio_ne hdc hfc hdf
  have hmurho : mu ≠ rho := crossRatio_ne hdc hgc hdg
  have hmusigma : mu ≠ sigma := crossRatio_ne hdc hhc hdh
  have hmutau : mu ≠ tau := crossRatio_ne hdc hic hdi
  have hmuupsilon : mu ≠ upsilon := crossRatio_ne hdc hjc hdj
  have hnuxi : nu ≠ xi := crossRatio_ne hec hfc hef
  have hnurho : nu ≠ rho := crossRatio_ne hec hgc heg
  have hnusigma : nu ≠ sigma := crossRatio_ne hec hhc heh
  have hnutau : nu ≠ tau := crossRatio_ne hec hic hei
  have hnuupsilon : nu ≠ upsilon := crossRatio_ne hec hjc hej
  have hxirho : xi ≠ rho := crossRatio_ne hfc hgc hfg
  have hxisigma : xi ≠ sigma := crossRatio_ne hfc hhc hfh
  have hxitau : xi ≠ tau := crossRatio_ne hfc hic hfi
  have hxiupsilon : xi ≠ upsilon := crossRatio_ne hfc hjc hfj
  have hrhosigma : rho ≠ sigma := crossRatio_ne hgc hhc hgh
  have hrhotau : rho ≠ tau := crossRatio_ne hgc hic hgi
  have hrhoupsilon : rho ≠ upsilon := crossRatio_ne hgc hjc hgj
  have hsigmatau : sigma ≠ tau := crossRatio_ne hhc hic hhi
  have hsigmaupsilon : sigma ≠ upsilon := crossRatio_ne hhc hjc hhj
  have htauupsilon : tau ≠ upsilon := crossRatio_ne hic hjc hij
  have hfiniteProd : χ ^ (m + n + l + s + o + q + z + rExp + tExp) ≠ 1 := by
    intro heq
    apply hpowK
    calc
      χ ^ k = 1 * χ ^ k := by simp
      _ = χ ^ (m + n + l + s + o + q + z + rExp + tExp) * χ ^ k := by rw [heq]
      _ = (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) * (χ ^ o) *
          (χ ^ q) * (χ ^ z) * (χ ^ rExp) * (χ ^ tExp) := by
        simp only [pow_add]
        ac_rfl
      _ = 1 := hprod
  have height :
      ‖∑ y : ZMod p,
        (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ l) (y - mu) *
          (χ ^ s) (y - nu) * (χ ^ o) (y - xi) * (χ ^ q) (y - rho) *
            (χ ^ z) (y - sigma) * (χ ^ rExp) (y - tau) *
              (χ ^ tExp) (y - upsilon)‖ ≤ 8 * Real.sqrt p :=
    hweil χ m n l s o q z rExp tExp lam mu nu xi rho sigma tau upsilon
      hpowM hpowN hpowL hpowS hpowO hpowQ hpowZ hpowR hpowT hfiniteProd
      hlam hmu hnu hxi hrho hsigma htau hupsilon
      hlammu hlamnu hlamxi hlamrho hlamsigma hlamtau hlamupsilon
      hmunu hmuxi hmurho hmusigma hmutau hmuupsilon
      hnuxi hnurho hnusigma hnutau hnuupsilon
      hxirho hxisigma hxitau hxiupsilon
      hrhosigma hrhotau hrhoupsilon hsigmatau hsigmaupsilon htauupsilon
  exact norm_tenRootMulCharSum_le_eight_mul_sqrt_add_one_of_ninePoint
    p (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l) (χ ^ s) (χ ^ o) (χ ^ q) (χ ^ z)
      (χ ^ rExp) (χ ^ tExp) hprod a b c d e f g h i j
      hac hbc hdc hec hfc hgc hhc hic hjc height

set_option maxHeartbeats 4000000 in
/-- Exactly ten active roots of character-order-divisible degree reduce to
the source-shaped nine-point endpoint. -/
theorem norm_primeActiveRootCharacterSum_le_eight_mul_sqrt_add_one_of_card_eq_ten_degree_power
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerNinePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 10) :
    ‖primeActiveRootCharacterSum p χ P‖ ≤ 8 * Real.sqrt p + 1 := by
  let S := primeActiveRoots p χ P
  obtain ⟨u, huS⟩ : S.Nonempty := Finset.card_pos.mp (by simp [S, hcard])
  have hcardS : S.card = 10 := by simpa only [S] using hcard
  have hcardOne : (S.erase u).card = 9 := by
    rw [Finset.card_erase_of_mem huS]
    omega
  obtain ⟨v, hvOne⟩ : (S.erase u).Nonempty := Finset.card_pos.mp (by omega)
  have hcardTwo : ((S.erase u).erase v).card = 8 := by
    rw [Finset.card_erase_of_mem hvOne, hcardOne]
  obtain ⟨w, hwTwo⟩ : ((S.erase u).erase v).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardThree : (((S.erase u).erase v).erase w).card = 7 := by
    rw [Finset.card_erase_of_mem hwTwo, hcardTwo]
  obtain ⟨z, hzThree⟩ : (((S.erase u).erase v).erase w).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardFour : ((((S.erase u).erase v).erase w).erase z).card = 6 := by
    rw [Finset.card_erase_of_mem hzThree, hcardThree]
  obtain ⟨t, htFour⟩ : ((((S.erase u).erase v).erase w).erase z).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardFive : (((((S.erase u).erase v).erase w).erase z).erase t).card = 5 := by
    rw [Finset.card_erase_of_mem htFour, hcardFour]
  obtain ⟨q, hqFive⟩ : (((((S.erase u).erase v).erase w).erase z).erase t).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardSix : ((((((S.erase u).erase v).erase w).erase z).erase t).erase q).card = 4 := by
    rw [Finset.card_erase_of_mem hqFive, hcardFive]
  obtain ⟨r, x, y, j, hrx, hry, hrj, hxy, hxj, hyj, hrest⟩ :=
    Finset.card_eq_four.mp hcardSix
  have hrSix : r ∈ (((((S.erase u).erase v).erase w).erase z).erase t).erase q := by
    simp [hrest]
  have hxSix : x ∈ (((((S.erase u).erase v).erase w).erase z).erase t).erase q := by
    simp [hrest]
  have hySix : y ∈ (((((S.erase u).erase v).erase w).erase z).erase t).erase q := by
    simp [hrest]
  have hjSix : j ∈ (((((S.erase u).erase v).erase w).erase z).erase t).erase q := by
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
  have hrData : r ≠ q ∧ r ≠ t ∧ r ≠ z ∧ r ≠ w ∧ r ≠ v ∧ r ≠ u ∧ r ∈ S := by
    simpa only [Finset.mem_erase] using hrSix
  have hxData : x ≠ q ∧ x ≠ t ∧ x ≠ z ∧ x ≠ w ∧ x ≠ v ∧ x ≠ u ∧ x ∈ S := by
    simpa only [Finset.mem_erase] using hxSix
  have hyData : y ≠ q ∧ y ≠ t ∧ y ≠ z ∧ y ≠ w ∧ y ≠ v ∧ y ≠ u ∧ y ∈ S := by
    simpa only [Finset.mem_erase] using hySix
  have hjData : j ≠ q ∧ j ≠ t ∧ j ≠ z ∧ j ≠ w ∧ j ≠ v ∧ j ≠ u ∧ j ∈ S := by
    simpa only [Finset.mem_erase] using hjSix
  have huv : u ≠ v := hvData.1.symm
  have huw : u ≠ w := hwData.2.1.symm
  have huz : u ≠ z := hzData.2.2.1.symm
  have hut : u ≠ t := htData.2.2.2.1.symm
  have huq : u ≠ q := hqData.2.2.2.2.1.symm
  have hur : u ≠ r := hrData.2.2.2.2.2.1.symm
  have hux : u ≠ x := hxData.2.2.2.2.2.1.symm
  have huy : u ≠ y := hyData.2.2.2.2.2.1.symm
  have huj : u ≠ j := hjData.2.2.2.2.2.1.symm
  have hvw : v ≠ w := hwData.1.symm
  have hvz : v ≠ z := hzData.2.1.symm
  have hvt : v ≠ t := htData.2.2.1.symm
  have hvq : v ≠ q := hqData.2.2.2.1.symm
  have hvr : v ≠ r := hrData.2.2.2.2.1.symm
  have hvx : v ≠ x := hxData.2.2.2.2.1.symm
  have hvy : v ≠ y := hyData.2.2.2.2.1.symm
  have hvj : v ≠ j := hjData.2.2.2.2.1.symm
  have hwz : w ≠ z := hzData.1.symm
  have hwt : w ≠ t := htData.2.1.symm
  have hwq : w ≠ q := hqData.2.2.1.symm
  have hwr : w ≠ r := hrData.2.2.2.1.symm
  have hwx : w ≠ x := hxData.2.2.2.1.symm
  have hwy : w ≠ y := hyData.2.2.2.1.symm
  have hwj : w ≠ j := hjData.2.2.2.1.symm
  have hzt : z ≠ t := htData.1.symm
  have hzq : z ≠ q := hqData.2.1.symm
  have hzr : z ≠ r := hrData.2.2.1.symm
  have hzx : z ≠ x := hxData.2.2.1.symm
  have hzy : z ≠ y := hyData.2.2.1.symm
  have hzj : z ≠ j := hjData.2.2.1.symm
  have htq : t ≠ q := hqData.1.symm
  have htr : t ≠ r := hrData.2.1.symm
  have htx : t ≠ x := hxData.2.1.symm
  have hty : t ≠ y := hyData.2.1.symm
  have htj : t ≠ j := hjData.2.1.symm
  have hqr : q ≠ r := hrData.1.symm
  have hqx : q ≠ x := hxData.1.symm
  have hqy : q ≠ y := hyData.1.symm
  have hqj : q ≠ j := hjData.1.symm
  have hvS : v ∈ S := hvData.2
  have hwS : w ∈ S := hwData.2.2
  have hzS : z ∈ S := hzData.2.2.2
  have htS : t ∈ S := htData.2.2.2.2
  have hqS : q ∈ S := hqData.2.2.2.2.2
  have hrS : r ∈ S := hrData.2.2.2.2.2.2
  have hxS : x ∈ S := hxData.2.2.2.2.2.2
  have hyS : y ∈ S := hyData.2.2.2.2.2.2
  have hjS : j ∈ S := hjData.2.2.2.2.2.2
  have hroots : S = {u, v, w, z, t, q, r, x, y, j} := by
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
      _ = insert u (insert v (insert w (insert z (insert t
          (insert q ((((((S.erase u).erase v).erase w).erase z).erase t).erase q)))))) := by
        rw [Finset.insert_erase hqFive]
      _ = {u, v, w, z, t, q, r, x, y, j} := by rw [hrest]
  have huActive : u ∈ primeActiveRoots p χ P := by simpa only [S] using huS
  have hvActive : v ∈ primeActiveRoots p χ P := by simpa only [S] using hvS
  have hwActive : w ∈ primeActiveRoots p χ P := by simpa only [S] using hwS
  have hzActive : z ∈ primeActiveRoots p χ P := by simpa only [S] using hzS
  have htActive : t ∈ primeActiveRoots p χ P := by simpa only [S] using htS
  have hqActive : q ∈ primeActiveRoots p χ P := by simpa only [S] using hqS
  have hrActive : r ∈ primeActiveRoots p χ P := by simpa only [S] using hrS
  have hxActive : x ∈ primeActiveRoots p χ P := by simpa only [S] using hxS
  have hyActive : y ∈ primeActiveRoots p χ P := by simpa only [S] using hyS
  have hjActive : j ∈ primeActiveRoots p χ P := by simpa only [S] using hjS
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
  have hjRoot : j ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hjActive
  let m := P.roots.count u
  let n := P.roots.count v
  let k := P.roots.count w
  let l := P.roots.count z
  let s := P.roots.count t
  let o := P.roots.count q
  let qn := P.roots.count r
  let zn := P.roots.count x
  let rn := P.roots.count y
  let tn := P.roots.count j
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
  have htn : tn ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hjRoot)).ne'
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
  have hpowTn : χ ^ tn ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hjActive).2 (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hsum := orderOf_dvd_sum_primeActiveRoots_count p χ P hP hdegree
  have hmnklsoqzrt : orderOf χ ∣ m + n + k + l + s + o + qn + zn + rn + tn := by
    simpa [S, hroots, huv, huw, huz, hut, huq, hur, hux, huy, huj,
      hvw, hvz, hvt, hvq, hvr, hvx, hvy, hvj,
      hwz, hwt, hwq, hwr, hwx, hwy, hwj,
      hzt, hzq, hzr, hzx, hzy, hzj, htq, htr, htx, hty, htj,
      hqr, hqx, hqy, hqj, hrx, hry, hrj, hxy, hxj, hyj,
      m, n, k, l, s, o, qn, zn, rn, tn,
      add_assoc, add_comm, add_left_comm] using hsum
  have hprod :
      (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) * (χ ^ o) *
        (χ ^ qn) * (χ ^ zn) * (χ ^ rn) * (χ ^ tn) = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add, ← pow_add, ← pow_add]
    exact orderOf_dvd_iff_pow_eq_one.mp hmnklsoqzrt
  have hten := norm_tenRootMulCharPowerSum_le_eight_mul_sqrt_add_one
    p hweil χ m n k l s o qn zn rn tn
      hpowM hpowN hpowK hpowL hpowS hpowO hpowQn hpowZn hpowRn hpowTn hprod
      u v w z t q r x y j huv huw huz hut huq hur hux huy huj
      hvw hvz hvt hvq hvr hvx hvy hvj
      hwz.symm hzt hzq hzr hzx hzy hzj
      hwt.symm htq htr htx hty htj
      hwq.symm hqr hqx hqy hqj
      hwr.symm hrx hry hrj hwx.symm hxy hxj hwy.symm hyj hwj.symm
  unfold primeActiveRootCharacterSum
  rw [show primeActiveRoots p χ P = {u, v, w, z, t, q, r, x, y, j} by
    simpa [S] using hroots]
  convert hten using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro x _hx
  simp [huv, huw, huz, hut, huq, hur, hux, huy, huj,
    hvw, hvz, hvt, hvq, hvr, hvx, hvy, hvj,
    hwz, hwt, hwq, hwr, hwx, hwy, hwj,
    hzt, hzq, hzr, hzx, hzy, hzj, htq, htr, htx, hty, htj,
    hqr, hqx, hqy, hqj, hrx, hry, hrj, hxy, hxj, hyj]
  rw [MulChar.pow_apply' χ hm, MulChar.pow_apply' χ hn,
    MulChar.pow_apply' χ hk, MulChar.pow_apply' χ hl,
    MulChar.pow_apply' χ hs, MulChar.pow_apply' χ ho, MulChar.pow_apply' χ hqn,
    MulChar.pow_apply' χ hzn, MulChar.pow_apply' χ hrn, MulChar.pow_apply' χ htn]
  simp [m, n, k, l, s, o, qn, zn, rn, tn, Polynomial.count_roots]
  ac_rfl

/-- The nine-point power endpoint discharges the split-polynomial target when
exactly ten roots are active and degree is character-order divisible. -/
theorem primeSplitPolynomialWeilBound_of_card_activeRoots_eq_ten_degree_power
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerNinePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (_a : ZMod p) (_hχ : χ ≠ 1) (hP : P.Splits)
    (_hnot : ¬orderOf χ ∣ P.rootMultiplicity _a)
    (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 10) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
  have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
  have hactive :=
    norm_primeActiveRootCharacterSum_le_eight_mul_sqrt_add_one_of_card_eq_ten_degree_power
      p hweil χ P hP hdegree hcard
  have hrestricted :=
    norm_filter_primeActiveRootProduct_le_of_activeRootCharacterSum
      p χ P (8 * Real.sqrt p + 1) hactive
  have hrootCard : 10 ≤ P.roots.toFinset.card := by
    rw [← hcard]
    exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
  have hInactiveCard :
      (primeInactiveRoots p χ P).card ≤ P.roots.toFinset.card :=
    Finset.card_le_card (primeInactiveRoots_subset_roots p χ P)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hroom :
      8 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
    have hInactiveCard' :
        ((primeInactiveRoots p χ P).card : ℝ) ≤
          (P.roots.toFinset.card : ℝ) := by exact_mod_cast hInactiveCard
    have hrootCard' : (10 : ℝ) ≤ P.roots.toFinset.card := by
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
    _ ≤ 8 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card := by
      simpa using hrestricted
    _ ≤ ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := hroom

end

end Tao2026
