import Tao2026.BurgessWeilPrimeTwelveRoots

/-!
# Thirteen active roots in the prime Burgess sum

This file isolates the next source-shaped endpoint obtained by sending one
of thirteen degree-balanced active roots to infinity. The twelve finite local
characters remain powers of one Burgess character, and scaling normalizes
their marked points to `0`, `1`, `t`, `u`, `v`, `w`, `z`, `r₀`, `s₀`, `a₀`,
`b₀`, and `c₀`.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The source-shaped twelve-point endpoint at one prime. -/
def TaoPrimePowerTwelvePointHypergeometricWeilBoundAt
    (p : ℕ) [NeZero p] [Fact p.Prime] : Prop :=
  ∀ (χ : MulChar (ZMod p) ℂ) (m n k l s o q r j uExp vExp wExp : ℕ)
    (lam mu nu xi rho sigma tau upsilon phi psi omega : ZMod p),
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 →
    χ ^ s ≠ 1 → χ ^ o ≠ 1 → χ ^ q ≠ 1 → χ ^ r ≠ 1 → χ ^ j ≠ 1 →
    χ ^ uExp ≠ 1 → χ ^ vExp ≠ 1 → χ ^ wExp ≠ 1 →
    χ ^ (m + n + k + l + s + o + q + r + j + uExp + vExp + wExp) ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → nu ≠ 0 → xi ≠ 0 → rho ≠ 0 → sigma ≠ 0 → tau ≠ 0 →
    upsilon ≠ 0 → phi ≠ 0 → psi ≠ 0 → omega ≠ 0 →
    lam ≠ mu → lam ≠ nu → lam ≠ xi → lam ≠ rho → lam ≠ sigma → lam ≠ tau →
    lam ≠ upsilon → lam ≠ phi → lam ≠ psi → lam ≠ omega →
    mu ≠ nu → mu ≠ xi → mu ≠ rho → mu ≠ sigma → mu ≠ tau → mu ≠ upsilon →
    mu ≠ phi → mu ≠ psi → mu ≠ omega →
    nu ≠ xi → nu ≠ rho → nu ≠ sigma → nu ≠ tau → nu ≠ upsilon → nu ≠ phi →
    nu ≠ psi → nu ≠ omega →
    xi ≠ rho → xi ≠ sigma → xi ≠ tau → xi ≠ upsilon → xi ≠ phi → xi ≠ psi →
    xi ≠ omega →
    rho ≠ sigma → rho ≠ tau → rho ≠ upsilon → rho ≠ phi → rho ≠ psi → rho ≠ omega →
    sigma ≠ tau → sigma ≠ upsilon → sigma ≠ phi → sigma ≠ psi → sigma ≠ omega →
    tau ≠ upsilon → tau ≠ phi → tau ≠ psi → tau ≠ omega →
    upsilon ≠ phi → upsilon ≠ psi → upsilon ≠ omega →
    phi ≠ psi → phi ≠ omega → psi ≠ omega →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ k) (y - mu) *
        (χ ^ l) (y - nu) * (χ ^ s) (y - xi) * (χ ^ o) (y - rho) *
          (χ ^ q) (y - sigma) * (χ ^ r) (y - tau) *
            (χ ^ j) (y - upsilon) * (χ ^ uExp) (y - phi) *
              (χ ^ vExp) (y - psi) * (χ ^ wExp) (y - omega)‖ ≤ 11 * Real.sqrt p

/-- The large-characteristic range needed by the exact Burgess branch. -/
def TaoPrimePowerTwelvePointHypergeometricWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime],
    64 < p → TaoPrimePowerTwelvePointHypergeometricWeilBoundAt p

/-- Finite exponent-range form of the source-shaped twelve-point endpoint. -/
def TaoPrimeReducedPowerTwelvePointHypergeometricWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime], 64 < p →
    ∀ (χ : MulChar (ZMod p) ℂ) (m n k l s o q r j uExp vExp wExp : ℕ)
      (lam mu nu xi rho sigma tau upsilon phi psi omega : ZMod p),
    m < orderOf χ → n < orderOf χ → k < orderOf χ →
    l < orderOf χ → s < orderOf χ → o < orderOf χ → q < orderOf χ →
    r < orderOf χ → j < orderOf χ → uExp < orderOf χ → vExp < orderOf χ →
    wExp < orderOf χ →
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 →
    χ ^ s ≠ 1 → χ ^ o ≠ 1 → χ ^ q ≠ 1 → χ ^ r ≠ 1 → χ ^ j ≠ 1 →
    χ ^ uExp ≠ 1 → χ ^ vExp ≠ 1 → χ ^ wExp ≠ 1 →
    χ ^ (m + n + k + l + s + o + q + r + j + uExp + vExp + wExp) ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → nu ≠ 0 → xi ≠ 0 → rho ≠ 0 → sigma ≠ 0 → tau ≠ 0 →
    upsilon ≠ 0 → phi ≠ 0 → psi ≠ 0 → omega ≠ 0 →
    lam ≠ mu → lam ≠ nu → lam ≠ xi → lam ≠ rho → lam ≠ sigma → lam ≠ tau →
    lam ≠ upsilon → lam ≠ phi → lam ≠ psi → lam ≠ omega →
    mu ≠ nu → mu ≠ xi → mu ≠ rho → mu ≠ sigma → mu ≠ tau → mu ≠ upsilon →
    mu ≠ phi → mu ≠ psi → mu ≠ omega →
    nu ≠ xi → nu ≠ rho → nu ≠ sigma → nu ≠ tau → nu ≠ upsilon → nu ≠ phi →
    nu ≠ psi → nu ≠ omega →
    xi ≠ rho → xi ≠ sigma → xi ≠ tau → xi ≠ upsilon → xi ≠ phi → xi ≠ psi →
    xi ≠ omega →
    rho ≠ sigma → rho ≠ tau → rho ≠ upsilon → rho ≠ phi → rho ≠ psi → rho ≠ omega →
    sigma ≠ tau → sigma ≠ upsilon → sigma ≠ phi → sigma ≠ psi → sigma ≠ omega →
    tau ≠ upsilon → tau ≠ phi → tau ≠ psi → tau ≠ omega →
    upsilon ≠ phi → upsilon ≠ psi → upsilon ≠ omega →
    phi ≠ psi → phi ≠ omega → psi ≠ omega →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ k) (y - mu) *
        (χ ^ l) (y - nu) * (χ ^ s) (y - xi) * (χ ^ o) (y - rho) *
          (χ ^ q) (y - sigma) * (χ ^ r) (y - tau) *
            (χ ^ j) (y - upsilon) * (χ ^ uExp) (y - phi) *
              (χ ^ vExp) (y - psi) * (χ ^ wExp) (y - omega)‖ ≤ 11 * Real.sqrt p

/-- Scaling by the first nonzero point puts a twelve-point sum into the
ten-parameter Legendre form `0`, `1`, `t`, `u`, `v`, `w`, `z`, `r₀`, `s₀`,
`a₀`, `b₀`, `c₀`. -/
theorem twelvePointMulCharSum_eq_legendreForm
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ η θ ι κ lambdaChar muChar : MulChar (ZMod p) ℂ)
    (lam mu nu xi rho sigma tau upsilon phi psi omega : ZMod p) (hlam : lam ≠ 0) :
    (∑ y : ZMod p,
      α y * β (y - lam) * γ (y - mu) * δ (y - nu) * ε (y - xi) *
        ζ (y - rho) * η (y - sigma) * θ (y - tau) * ι (y - upsilon) * κ (y - phi) *
          lambdaChar (y - psi) * muChar (y - omega)) =
      (α lam * β lam * γ lam * δ lam * ε lam * ζ lam * η lam * θ lam * ι lam * κ lam *
        lambdaChar lam * muChar lam) *
        ∑ t : ZMod p,
          α t * β (t - 1) * γ (t - mu / lam) * δ (t - nu / lam) *
            ε (t - xi / lam) * ζ (t - rho / lam) * η (t - sigma / lam) *
              θ (t - tau / lam) * ι (t - upsilon / lam) * κ (t - phi / lam) *
                lambdaChar (t - psi / lam) * muChar (t - omega / lam) := by
  let e : ZMod p ≃ ZMod p := Equiv.mulLeft₀ lam hlam
  calc
    (∑ y : ZMod p,
        α y * β (y - lam) * γ (y - mu) * δ (y - nu) * ε (y - xi) *
          ζ (y - rho) * η (y - sigma) * θ (y - tau) * ι (y - upsilon) * κ (y - phi) *
            lambdaChar (y - psi) * muChar (y - omega)) =
        ∑ t : ZMod p,
          α (e t) * β (e t - lam) * γ (e t - mu) * δ (e t - nu) *
            ε (e t - xi) * ζ (e t - rho) * η (e t - sigma) * θ (e t - tau) *
              ι (e t - upsilon) * κ (e t - phi) * lambdaChar (e t - psi) :=
      (Equiv.sum_comp e
        (fun y : ZMod p =>
          α y * β (y - lam) * γ (y - mu) * δ (y - nu) * ε (y - xi) *
            ζ (y - rho) * η (y - sigma) * θ (y - tau) * ι (y - upsilon) * κ (y - phi) *
              lambdaChar (y - psi) * muChar (y - omega))).symm
    _ = (α lam * β lam * γ lam * δ lam * ε lam * ζ lam * η lam * θ lam * ι lam * κ lam *
          lambdaChar lam * muChar lam) *
        ∑ t : ZMod p,
          α t * β (t - 1) * γ (t - mu / lam) * δ (t - nu / lam) *
            ε (t - xi / lam) * ζ (t - rho / lam) * η (t - sigma / lam) *
              θ (t - tau / lam) * ι (t - upsilon / lam) * κ (t - phi / lam) *
                lambdaChar (t - psi / lam) * muChar (t - omega / lam) := by
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
      have hsubPhi : lam * t - phi = lam * (t - phi / lam) := by field_simp
      have hsubPsi : lam * t - psi = lam * (t - psi / lam) := by field_simp
      have hsubOmega : lam * t - omega = lam * (t - omega / lam) := by field_simp
      dsimp [e]
      rw [hsubOne, hsubMu, hsubNu, hsubXi, hsubRho, hsubSigma, hsubTau, hsubUpsilon,
        hsubPhi, hsubPsi, hsubOmega, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul,
        map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
      ring

/-- The final ten-parameter analytic boundary for thirteen active roots. -/
def TaoPrimeReducedPowerTwelvePointLegendreWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime], 64 < p →
    ∀ (χ : MulChar (ZMod p) ℂ) (m n k l s o q r j uExp vExp wExp : ℕ)
      (t u v w z r₀ s₀ a₀ b₀ c₀ : ZMod p),
    m < orderOf χ → n < orderOf χ → k < orderOf χ →
    l < orderOf χ → s < orderOf χ → o < orderOf χ → q < orderOf χ →
    r < orderOf χ → j < orderOf χ → uExp < orderOf χ → vExp < orderOf χ →
    wExp < orderOf χ →
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 →
    χ ^ s ≠ 1 → χ ^ o ≠ 1 → χ ^ q ≠ 1 → χ ^ r ≠ 1 → χ ^ j ≠ 1 →
    χ ^ uExp ≠ 1 → χ ^ vExp ≠ 1 → χ ^ wExp ≠ 1 →
    χ ^ (m + n + k + l + s + o + q + r + j + uExp + vExp + wExp) ≠ 1 →
    t ≠ 0 → u ≠ 0 → v ≠ 0 → w ≠ 0 → z ≠ 0 → r₀ ≠ 0 → s₀ ≠ 0 → a₀ ≠ 0 →
    b₀ ≠ 0 → c₀ ≠ 0 →
    t ≠ 1 → u ≠ 1 → v ≠ 1 → w ≠ 1 → z ≠ 1 → r₀ ≠ 1 → s₀ ≠ 1 → a₀ ≠ 1 →
    b₀ ≠ 1 → c₀ ≠ 1 →
    t ≠ u → t ≠ v → t ≠ w → t ≠ z → t ≠ r₀ → t ≠ s₀ → t ≠ a₀ → t ≠ b₀ →
    t ≠ c₀ →
    u ≠ v → u ≠ w → u ≠ z → u ≠ r₀ → u ≠ s₀ → u ≠ a₀ → u ≠ b₀ → u ≠ c₀ →
    v ≠ w → v ≠ z → v ≠ r₀ → v ≠ s₀ → v ≠ a₀ → v ≠ b₀ → v ≠ c₀ →
    w ≠ z → w ≠ r₀ → w ≠ s₀ → w ≠ a₀ → w ≠ b₀ → w ≠ c₀ →
    z ≠ r₀ → z ≠ s₀ → z ≠ a₀ → z ≠ b₀ → z ≠ c₀ →
    r₀ ≠ s₀ → r₀ ≠ a₀ → r₀ ≠ b₀ → r₀ ≠ c₀ →
    s₀ ≠ a₀ → s₀ ≠ b₀ → s₀ ≠ c₀ → a₀ ≠ b₀ → a₀ ≠ c₀ → b₀ ≠ c₀ →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - t) *
        (χ ^ l) (y - u) * (χ ^ s) (y - v) * (χ ^ o) (y - w) *
          (χ ^ q) (y - z) * (χ ^ r) (y - r₀) * (χ ^ j) (y - s₀) *
            (χ ^ uExp) (y - a₀) * (χ ^ vExp) (y - b₀) *
              (χ ^ wExp) (y - c₀)‖ ≤
      11 * Real.sqrt p

theorem TaoPrimeReducedPowerTwelvePointLegendreWeilBoundAboveSixtyFour.toTwelvePoint
    (hweil : TaoPrimeReducedPowerTwelvePointLegendreWeilBoundAboveSixtyFour) :
    TaoPrimeReducedPowerTwelvePointHypergeometricWeilBoundAboveSixtyFour := by
  intro p _ _ hp χ m n k l s o q r j uExp vExp wExp
    lam mu nu xi rho sigma tau upsilon phi psi omega
    hm hn hk hl hs ho hq hr hj huExp hvExp hwExp
    hpowM hpowN hpowK hpowL hpowS hpowO hpowQ hpowR hpowJ hpowU hpowV hpowW hpowSum
    hlam hmu hnu hxi hrho hsigma htau hupsilon hphi hpsi homega
    hlammu hlamnu hlamxi hlamrho hlamsigma hlamtau hlamupsilon hlamphi hlampsi hlamomega
    hmunu hmuxi hmurho hmusigma hmutau hmuupsilon hmuphi hmupsi hmuomega
    hnuxi hnurho hnusigma hnutau hnuupsilon hnuphi hnupsi hnuomega
    hxirho hxisigma hxitau hxiupsilon hxiphi hxipsi hxiomega
    hrhosigma hrhotau hrhoupsilon hrhophi hrhopsi hrhoomega
    hsigmatau hsigmaupsilon hsigmaphi hsigmapsi hsigmaomega
    htauupsilon htauphi htaupsi htauomega
    hupsilonphi hupsilonpsi hupsilonomega hphipsi hphiomega hpsiomega
  let t : ZMod p := mu / lam
  let u : ZMod p := nu / lam
  let v : ZMod p := xi / lam
  let w : ZMod p := rho / lam
  let z : ZMod p := sigma / lam
  let r₀ : ZMod p := tau / lam
  let s₀ : ZMod p := upsilon / lam
  let a₀ : ZMod p := phi / lam
  let b₀ : ZMod p := psi / lam
  let c₀ : ZMod p := omega / lam
  have ht0 : t ≠ 0 := div_ne_zero hmu hlam
  have hu0 : u ≠ 0 := div_ne_zero hnu hlam
  have hv0 : v ≠ 0 := div_ne_zero hxi hlam
  have hw0 : w ≠ 0 := div_ne_zero hrho hlam
  have hz0 : z ≠ 0 := div_ne_zero hsigma hlam
  have hr₀0 : r₀ ≠ 0 := div_ne_zero htau hlam
  have hs₀0 : s₀ ≠ 0 := div_ne_zero hupsilon hlam
  have ha₀0 : a₀ ≠ 0 := div_ne_zero hphi hlam
  have hb₀0 : b₀ ≠ 0 := div_ne_zero hpsi hlam
  have hc₀0 : c₀ ≠ 0 := div_ne_zero homega hlam
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
  have ha₀1 : a₀ ≠ 1 := by
    intro heq
    apply hlamphi
    dsimp [a₀] at heq
    rw [div_eq_one_iff_eq hlam] at heq
    exact heq.symm
  have hb₀1 : b₀ ≠ 1 := by
    intro heq
    apply hlampsi
    dsimp [b₀] at heq
    rw [div_eq_one_iff_eq hlam] at heq
    exact heq.symm
  have hc₀1 : c₀ ≠ 1 := by
    intro heq
    apply hlamomega
    dsimp [c₀] at heq
    rw [div_eq_one_iff_eq hlam] at heq
    exact heq.symm
  have htu : t ≠ u := fun heq => hmunu ((div_left_inj' hlam).mp heq)
  have htv : t ≠ v := fun heq => hmuxi ((div_left_inj' hlam).mp heq)
  have htw : t ≠ w := fun heq => hmurho ((div_left_inj' hlam).mp heq)
  have htz : t ≠ z := fun heq => hmusigma ((div_left_inj' hlam).mp heq)
  have htr₀ : t ≠ r₀ := fun heq => hmutau ((div_left_inj' hlam).mp heq)
  have hts₀ : t ≠ s₀ := fun heq => hmuupsilon ((div_left_inj' hlam).mp heq)
  have hta₀ : t ≠ a₀ := fun heq => hmuphi ((div_left_inj' hlam).mp heq)
  have htb₀ : t ≠ b₀ := fun heq => hmupsi ((div_left_inj' hlam).mp heq)
  have htc₀ : t ≠ c₀ := fun heq => hmuomega ((div_left_inj' hlam).mp heq)
  have huv : u ≠ v := fun heq => hnuxi ((div_left_inj' hlam).mp heq)
  have huw : u ≠ w := fun heq => hnurho ((div_left_inj' hlam).mp heq)
  have huz : u ≠ z := fun heq => hnusigma ((div_left_inj' hlam).mp heq)
  have hur₀ : u ≠ r₀ := fun heq => hnutau ((div_left_inj' hlam).mp heq)
  have hus₀ : u ≠ s₀ := fun heq => hnuupsilon ((div_left_inj' hlam).mp heq)
  have hua₀ : u ≠ a₀ := fun heq => hnuphi ((div_left_inj' hlam).mp heq)
  have hub₀ : u ≠ b₀ := fun heq => hnupsi ((div_left_inj' hlam).mp heq)
  have huc₀ : u ≠ c₀ := fun heq => hnuomega ((div_left_inj' hlam).mp heq)
  have hvw : v ≠ w := fun heq => hxirho ((div_left_inj' hlam).mp heq)
  have hvz : v ≠ z := fun heq => hxisigma ((div_left_inj' hlam).mp heq)
  have hvr₀ : v ≠ r₀ := fun heq => hxitau ((div_left_inj' hlam).mp heq)
  have hvs₀ : v ≠ s₀ := fun heq => hxiupsilon ((div_left_inj' hlam).mp heq)
  have hva₀ : v ≠ a₀ := fun heq => hxiphi ((div_left_inj' hlam).mp heq)
  have hvb₀ : v ≠ b₀ := fun heq => hxipsi ((div_left_inj' hlam).mp heq)
  have hvc₀ : v ≠ c₀ := fun heq => hxiomega ((div_left_inj' hlam).mp heq)
  have hwz : w ≠ z := fun heq => hrhosigma ((div_left_inj' hlam).mp heq)
  have hwr₀ : w ≠ r₀ := fun heq => hrhotau ((div_left_inj' hlam).mp heq)
  have hws₀ : w ≠ s₀ := fun heq => hrhoupsilon ((div_left_inj' hlam).mp heq)
  have hwa₀ : w ≠ a₀ := fun heq => hrhophi ((div_left_inj' hlam).mp heq)
  have hwb₀ : w ≠ b₀ := fun heq => hrhopsi ((div_left_inj' hlam).mp heq)
  have hwc₀ : w ≠ c₀ := fun heq => hrhoomega ((div_left_inj' hlam).mp heq)
  have hzr₀ : z ≠ r₀ := fun heq => hsigmatau ((div_left_inj' hlam).mp heq)
  have hzs₀ : z ≠ s₀ := fun heq => hsigmaupsilon ((div_left_inj' hlam).mp heq)
  have hza₀ : z ≠ a₀ := fun heq => hsigmaphi ((div_left_inj' hlam).mp heq)
  have hzb₀ : z ≠ b₀ := fun heq => hsigmapsi ((div_left_inj' hlam).mp heq)
  have hzc₀ : z ≠ c₀ := fun heq => hsigmaomega ((div_left_inj' hlam).mp heq)
  have hr₀s₀ : r₀ ≠ s₀ := fun heq => htauupsilon ((div_left_inj' hlam).mp heq)
  have hr₀a₀ : r₀ ≠ a₀ := fun heq => htauphi ((div_left_inj' hlam).mp heq)
  have hr₀b₀ : r₀ ≠ b₀ := fun heq => htaupsi ((div_left_inj' hlam).mp heq)
  have hr₀c₀ : r₀ ≠ c₀ := fun heq => htauomega ((div_left_inj' hlam).mp heq)
  have hs₀a₀ : s₀ ≠ a₀ := fun heq => hupsilonphi ((div_left_inj' hlam).mp heq)
  have hs₀b₀ : s₀ ≠ b₀ := fun heq => hupsilonpsi ((div_left_inj' hlam).mp heq)
  have hs₀c₀ : s₀ ≠ c₀ := fun heq => hupsilonomega ((div_left_inj' hlam).mp heq)
  have ha₀b₀ : a₀ ≠ b₀ := fun heq => hphipsi ((div_left_inj' hlam).mp heq)
  have ha₀c₀ : a₀ ≠ c₀ := fun heq => hphiomega ((div_left_inj' hlam).mp heq)
  have hb₀c₀ : b₀ ≠ c₀ := fun heq => hpsiomega ((div_left_inj' hlam).mp heq)
  have hbound := hweil p hp χ m n k l s o q r j uExp vExp wExp
    t u v w z r₀ s₀ a₀ b₀ c₀
    hm hn hk hl hs ho hq hr hj huExp hvExp hwExp
    hpowM hpowN hpowK hpowL hpowS hpowO hpowQ hpowR hpowJ hpowU hpowV hpowW hpowSum
    ht0 hu0 hv0 hw0 hz0 hr₀0 hs₀0 ha₀0 hb₀0 hc₀0
    ht1 hu1 hv1 hw1 hz1 hr₀1 hs₀1 ha₀1 hb₀1 hc₀1
    htu htv htw htz htr₀ hts₀ hta₀ htb₀ htc₀
    huv huw huz hur₀ hus₀ hua₀ hub₀ huc₀
    hvw hvz hvr₀ hvs₀ hva₀ hvb₀ hvc₀
    hwz hwr₀ hws₀ hwa₀ hwb₀ hwc₀
    hzr₀ hzs₀ hza₀ hzb₀ hzc₀
    hr₀s₀ hr₀a₀ hr₀b₀ hr₀c₀ hs₀a₀ hs₀b₀ hs₀c₀ ha₀b₀ ha₀c₀ hb₀c₀
  rw [twelvePointMulCharSum_eq_legendreForm
    p (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l) (χ ^ s) (χ ^ o) (χ ^ q) (χ ^ r) (χ ^ j)
      (χ ^ uExp) (χ ^ vExp) (χ ^ wExp)
      lam mu nu xi rho sigma tau upsilon phi psi omega hlam]
  simp only [norm_mul]
  have hC :
      ‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖ *
          ‖(χ ^ s) lam‖ * ‖(χ ^ o) lam‖ * ‖(χ ^ q) lam‖ * ‖(χ ^ r) lam‖ *
            ‖(χ ^ j) lam‖ * ‖(χ ^ uExp) lam‖ * ‖(χ ^ vExp) lam‖ *
              ‖(χ ^ wExp) lam‖ ≤ 1 := by
    calc
      ‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖ *
            ‖(χ ^ s) lam‖ * ‖(χ ^ o) lam‖ * ‖(χ ^ q) lam‖ * ‖(χ ^ r) lam‖ *
              ‖(χ ^ j) lam‖ * ‖(χ ^ uExp) lam‖ * ‖(χ ^ vExp) lam‖ *
                ‖(χ ^ wExp) lam‖ ≤
          1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 := by
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
        · exact DirichletCharacter.norm_le_one (χ ^ uExp) lam
        · exact DirichletCharacter.norm_le_one (χ ^ vExp) lam
        · exact DirichletCharacter.norm_le_one (χ ^ wExp) lam
      _ = 1 := by norm_num
  calc
    (‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖ *
          ‖(χ ^ s) lam‖ * ‖(χ ^ o) lam‖ * ‖(χ ^ q) lam‖ * ‖(χ ^ r) lam‖ *
            ‖(χ ^ j) lam‖ * ‖(χ ^ uExp) lam‖ * ‖(χ ^ vExp) lam‖ *
              ‖(χ ^ wExp) lam‖) *
        ‖∑ y : ZMod p,
          (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - mu / lam) *
            (χ ^ l) (y - nu / lam) * (χ ^ s) (y - xi / lam) *
              (χ ^ o) (y - rho / lam) * (χ ^ q) (y - sigma / lam) *
                (χ ^ r) (y - tau / lam) * (χ ^ j) (y - upsilon / lam) *
                  (χ ^ uExp) (y - phi / lam) * (χ ^ vExp) (y - psi / lam) *
                    (χ ^ wExp) (y - omega / lam)‖ ≤
      1 * ‖∑ y : ZMod p,
        (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - mu / lam) *
          (χ ^ l) (y - nu / lam) * (χ ^ s) (y - xi / lam) *
            (χ ^ o) (y - rho / lam) * (χ ^ q) (y - sigma / lam) *
              (χ ^ r) (y - tau / lam) * (χ ^ j) (y - upsilon / lam) *
                (χ ^ uExp) (y - phi / lam) * (χ ^ vExp) (y - psi / lam) *
                  (χ ^ wExp) (y - omega / lam)‖ := by gcongr
    _ ≤ 11 * Real.sqrt p := by
      simpa [t, u, v, w, z, r₀, s₀, a₀, b₀, c₀] using hbound

theorem TaoPrimeReducedPowerTwelvePointHypergeometricWeilBoundAboveSixtyFour.toPower
    (hweil : TaoPrimeReducedPowerTwelvePointHypergeometricWeilBoundAboveSixtyFour) :
    TaoPrimePowerTwelvePointHypergeometricWeilBoundAboveSixtyFour := by
  intro p _ _ hp χ m n k l s o q r j uExp vExp wExp
    lam mu nu xi rho sigma tau upsilon phi psi omega
    hpowM hpowN hpowK hpowL hpowS hpowO hpowQ hpowR hpowJ hpowU hpowV hpowW hpowSum
    hlam hmu hnu hxi hrho hsigma htau hupsilon hphi hpsi homega
    hlammu hlamnu hlamxi hlamrho hlamsigma hlamtau hlamupsilon hlamphi hlampsi hlamomega
    hmunu hmuxi hmurho hmusigma hmutau hmuupsilon hmuphi hmupsi hmuomega
    hnuxi hnurho hnusigma hnutau hnuupsilon hnuphi hnupsi hnuomega
    hxirho hxisigma hxitau hxiupsilon hxiphi hxipsi hxiomega
    hrhosigma hrhotau hrhoupsilon hrhophi hrhopsi hrhoomega
    hsigmatau hsigmaupsilon hsigmaphi hsigmapsi hsigmaomega
    htauupsilon htauphi htaupsi htauomega
    hupsilonphi hupsilonpsi hupsilonomega hphipsi hphiomega hpsiomega
  let m' := m % orderOf χ
  let n' := n % orderOf χ
  let k' := k % orderOf χ
  let l' := l % orderOf χ
  let s' := s % orderOf χ
  let o' := o % orderOf χ
  let q' := q % orderOf χ
  let r' := r % orderOf χ
  let j' := j % orderOf χ
  let uExp' := uExp % orderOf χ
  let vExp' := vExp % orderOf χ
  let wExp' := wExp % orderOf χ
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
  have huExpLt : uExp' < orderOf χ := Nat.mod_lt uExp hord
  have hvExpLt : vExp' < orderOf χ := Nat.mod_lt vExp hord
  have hwExpLt : wExp' < orderOf χ := Nat.mod_lt wExp hord
  have hmEq : χ ^ m' = χ ^ m := pow_mod_orderOf χ m
  have hnEq : χ ^ n' = χ ^ n := pow_mod_orderOf χ n
  have hkEq : χ ^ k' = χ ^ k := pow_mod_orderOf χ k
  have hlEq : χ ^ l' = χ ^ l := pow_mod_orderOf χ l
  have hsEq : χ ^ s' = χ ^ s := pow_mod_orderOf χ s
  have hoEq : χ ^ o' = χ ^ o := pow_mod_orderOf χ o
  have hqEq : χ ^ q' = χ ^ q := pow_mod_orderOf χ q
  have hrEq : χ ^ r' = χ ^ r := pow_mod_orderOf χ r
  have hjEq : χ ^ j' = χ ^ j := pow_mod_orderOf χ j
  have huExpEq : χ ^ uExp' = χ ^ uExp := pow_mod_orderOf χ uExp
  have hvExpEq : χ ^ vExp' = χ ^ vExp := pow_mod_orderOf χ vExp
  have hwExpEq : χ ^ wExp' = χ ^ wExp := pow_mod_orderOf χ wExp
  have hpowM' : χ ^ m' ≠ 1 := by simpa only [hmEq] using hpowM
  have hpowN' : χ ^ n' ≠ 1 := by simpa only [hnEq] using hpowN
  have hpowK' : χ ^ k' ≠ 1 := by simpa only [hkEq] using hpowK
  have hpowL' : χ ^ l' ≠ 1 := by simpa only [hlEq] using hpowL
  have hpowS' : χ ^ s' ≠ 1 := by simpa only [hsEq] using hpowS
  have hpowO' : χ ^ o' ≠ 1 := by simpa only [hoEq] using hpowO
  have hpowQ' : χ ^ q' ≠ 1 := by simpa only [hqEq] using hpowQ
  have hpowR' : χ ^ r' ≠ 1 := by simpa only [hrEq] using hpowR
  have hpowJ' : χ ^ j' ≠ 1 := by simpa only [hjEq] using hpowJ
  have hpowU' : χ ^ uExp' ≠ 1 := by simpa only [huExpEq] using hpowU
  have hpowV' : χ ^ vExp' ≠ 1 := by simpa only [hvExpEq] using hpowV
  have hpowW' : χ ^ wExp' ≠ 1 := by simpa only [hwExpEq] using hpowW
  have hsumEq :
      χ ^ (m' + n' + k' + l' + s' + o' + q' + r' + j' + uExp' + vExp' + wExp') =
        χ ^ (m + n + k + l + s + o + q + r + j + uExp + vExp + wExp) := by
    simp only [pow_add, hmEq, hnEq, hkEq, hlEq, hsEq, hoEq, hqEq, hrEq, hjEq,
      huExpEq, hvExpEq, hwExpEq]
  have hpowSum' :
      χ ^ (m' + n' + k' + l' + s' + o' + q' + r' + j' + uExp' + vExp' + wExp') ≠ 1 := by
    simpa only [hsumEq] using hpowSum
  have hbound := hweil p hp χ m' n' k' l' s' o' q' r' j' uExp' vExp' wExp'
    lam mu nu xi rho sigma tau upsilon phi psi omega
    hmLt hnLt hkLt hlLt hsLt hoLt hqLt hrLt hjLt huExpLt hvExpLt hwExpLt
    hpowM' hpowN' hpowK' hpowL' hpowS' hpowO' hpowQ' hpowR' hpowJ' hpowU' hpowV' hpowW'
      hpowSum'
    hlam hmu hnu hxi hrho hsigma htau hupsilon hphi hpsi homega
    hlammu hlamnu hlamxi hlamrho hlamsigma hlamtau hlamupsilon hlamphi hlampsi hlamomega
    hmunu hmuxi hmurho hmusigma hmutau hmuupsilon hmuphi hmupsi hmuomega
    hnuxi hnurho hnusigma hnutau hnuupsilon hnuphi hnupsi hnuomega
    hxirho hxisigma hxitau hxiupsilon hxiphi hxipsi hxiomega
    hrhosigma hrhotau hrhoupsilon hrhophi hrhopsi hrhoomega
    hsigmatau hsigmaupsilon hsigmaphi hsigmapsi hsigmaomega
    htauupsilon htauphi htaupsi htauomega
    hupsilonphi hupsilonpsi hupsilonomega hphipsi hphiomega hpsiomega
  simpa only [hmEq, hnEq, hkEq, hlEq, hsEq, hoEq, hqEq, hrEq, hjEq, huExpEq,
    hvExpEq, hwExpEq]
    using hbound

/-- Thirteen scalar denominators whose product is one cancel without expanding
the surrounding character expressions. -/
private theorem twelve_div_product_eq_of_denominator_product_eq_one
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂
      b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ : ℂ)
    (hb : b₁ * b₂ * b₃ * b₄ * b₅ * b₆ * b₇ * b₈ * b₉ * b₁₀ * b₁₁ * b₁₂ = 1) :
    a₁ / b₁ * (a₂ / b₂) * (a₃ / b₃) * (a₄ / b₄) *
        (a₅ / b₅) * (a₆ / b₆) * (a₇ / b₇) * (a₈ / b₈) * (a₉ / b₉) * (a₁₀ / b₁₀) *
          (a₁₁ / b₁₁) * (a₁₂ / b₁₂) =
      a₁ * a₂ * a₃ * a₄ * a₅ * a₆ * a₇ * a₈ * a₉ * a₁₀ * a₁₁ * a₁₂ := by
  calc
    a₁ / b₁ * (a₂ / b₂) * (a₃ / b₃) * (a₄ / b₄) *
          (a₅ / b₅) * (a₆ / b₆) * (a₇ / b₇) * (a₈ / b₈) * (a₉ / b₉) *
            (a₁₀ / b₁₀) * (a₁₁ / b₁₁) * (a₁₂ / b₁₂) =
        (a₁ * a₂ * a₃ * a₄ * a₅ * a₆ * a₇ * a₈ * a₉ * a₁₀ * a₁₁ * a₁₂) *
          (b₁ * b₂ * b₃ * b₄ * b₅ * b₆ * b₇ * b₈ * b₉ * b₁₀ * b₁₁ * b₁₂)⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ac_rfl
    _ = a₁ * a₂ * a₃ * a₄ * a₅ * a₆ * a₇ * a₈ * a₉ * a₁₀ * a₁₁ * a₁₂ := by
      rw [hb]
      simp

set_option maxHeartbeats 4000000 in
/-- Pointwise Thirteen-root Möbius reduction away from the deleted projective
point. Triviality of the Thirteen-character product cancels the denominator and
leaves eleven finite character factors. -/
theorem thirteenRootMobius_term
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ η θ ι κ lambdaChar muChar : MulChar (ZMod p) ℂ)
    (hprod : α * β * γ * δ * ε * ζ * η * θ * ι * κ * lambdaChar * muChar = 1)
    (a b c d e f g h i j k₀ l₀ : ZMod p)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (hec : e ≠ c) (hfc : f ≠ c) (hgc : g ≠ c) (hhc : h ≠ c) (hic : i ≠ c)
    (hjc : j ≠ c) (hk₀c : k₀ ≠ c) (hl₀c : l₀ ≠ c)
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
    let phi := (a - k₀) / (c - k₀)
    let psi := (a - l₀) / (c - l₀)
    α (mob.symm y - a) * β (mob.symm y - b) * γ (mob.symm y - c) *
        δ (mob.symm y - d) * ε (mob.symm y - e) * ζ (mob.symm y - f) *
          η (mob.symm y - g) * θ (mob.symm y - h) * ι (mob.symm y - i) *
            κ (mob.symm y - j) * lambdaChar (mob.symm y - k₀) *
              muChar (mob.symm y - l₀) =
      (α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
          ε (c - e) * ζ (c - f) * η (c - g) * θ (c - h) * ι (c - i) * κ (c - j) *
            lambdaChar (c - k₀) * muChar (c - l₀)) *
        (α y * β (y - lam) * δ (y - mu) * ε (y - nu) * ζ (y - xi) *
          η (y - rho) * θ (y - sigma) * ι (y - tau) * κ (y - upsilon) *
            lambdaChar (y - phi) * muChar (y - psi)) := by
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
  have hck₀ : c - k₀ ≠ 0 := sub_ne_zero.mpr hk₀c.symm
  have hcl₀ : c - l₀ ≠ 0 := sub_ne_zero.mpr hl₀c.symm
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
  have hxk₀ : (y * c - a) / (y - 1) - k₀ =
      (c - k₀) * (y - (a - k₀) / (c - k₀)) / (y - 1) := by
    field_simp
    ring
  have hxl₀ : (y * c - a) / (y - 1) - l₀ =
      (c - l₀) * (y - (a - l₀) / (c - l₀)) / (y - 1) := by
    field_simp
    ring
  rw [hxa, hxb, hxc, hxd, hxe, hxf, hxg, hxh, hxi, hxj, hxk₀, hxl₀]
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
  have hmapdivLambdaChar (u v : ZMod p) :
      lambdaChar (u / v) = lambdaChar u / lambdaChar v := by
    exact map_div₀ lambdaChar.toMonoidWithZeroHom u v
  have hmapdivMuChar (u v : ZMod p) : muChar (u / v) = muChar u / muChar v := by
    exact map_div₀ muChar.toMonoidWithZeroHom u v
  have hcancel :
      α (y - 1) * β (y - 1) * γ (y - 1) * δ (y - 1) *
          ε (y - 1) * ζ (y - 1) * η (y - 1) * θ (y - 1) * ι (y - 1) *
            κ (y - 1) * lambdaChar (y - 1) * muChar (y - 1) = 1 := by
    rw [← MulChar.mul_apply, ← MulChar.mul_apply, ← MulChar.mul_apply,
      ← MulChar.mul_apply, ← MulChar.mul_apply, ← MulChar.mul_apply,
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
          ι ((c - i) * (y - (a - i) / (c - i)) / (y - 1)) *
          κ ((c - j) * (y - (a - j) / (c - j)) / (y - 1)) *
          lambdaChar ((c - k₀) * (y - (a - k₀) / (c - k₀)) / (y - 1)) *
          muChar ((c - l₀) * (y - (a - l₀) / (c - l₀)) / (y - 1)) =
        ((α y * α (c - a)) / α (y - 1)) *
          ((β (c - b) * β (y - (a - b) / (c - b))) / β (y - 1)) *
          (γ (c - a) / γ (y - 1)) *
          ((δ (c - d) * δ (y - (a - d) / (c - d))) / δ (y - 1)) *
          ((ε (c - e) * ε (y - (a - e) / (c - e))) / ε (y - 1)) *
          ((ζ (c - f) * ζ (y - (a - f) / (c - f))) / ζ (y - 1)) *
          ((η (c - g) * η (y - (a - g) / (c - g))) / η (y - 1)) *
          ((θ (c - h) * θ (y - (a - h) / (c - h))) / θ (y - 1)) *
          ((ι (c - i) * ι (y - (a - i) / (c - i))) / ι (y - 1)) *
          ((κ (c - j) * κ (y - (a - j) / (c - j))) / κ (y - 1)) *
          ((lambdaChar (c - k₀) * lambdaChar (y - (a - k₀) / (c - k₀))) /
            lambdaChar (y - 1)) *
          ((muChar (c - l₀) * muChar (y - (a - l₀) / (c - l₀))) /
            muChar (y - 1)) := by
      rw [hmapdivα, map_mul, hmapdivβ, map_mul, hmapdivγ,
        hmapdivδ, map_mul, hmapdivε, map_mul, hmapdivζ, map_mul,
        hmapdivη, map_mul, hmapdivθ, map_mul, hmapdivι, map_mul,
        hmapdivκ, map_mul, hmapdivLambdaChar, map_mul, hmapdivMuChar, map_mul]
    _ = (α y * α (c - a)) *
          (β (c - b) * β (y - (a - b) / (c - b))) * γ (c - a) *
          (δ (c - d) * δ (y - (a - d) / (c - d))) *
          (ε (c - e) * ε (y - (a - e) / (c - e))) *
          (ζ (c - f) * ζ (y - (a - f) / (c - f))) *
          (η (c - g) * η (y - (a - g) / (c - g))) *
          (θ (c - h) * θ (y - (a - h) / (c - h))) *
          (ι (c - i) * ι (y - (a - i) / (c - i))) *
          (κ (c - j) * κ (y - (a - j) / (c - j))) *
          (lambdaChar (c - k₀) * lambdaChar (y - (a - k₀) / (c - k₀))) *
          (muChar (c - l₀) * muChar (y - (a - l₀) / (c - l₀))) := by
      exact twelve_div_product_eq_of_denominator_product_eq_one
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
        (lambdaChar (c - k₀) * lambdaChar (y - (a - k₀) / (c - k₀)))
        (muChar (c - l₀) * muChar (y - (a - l₀) / (c - l₀)))
        (α (y - 1)) (β (y - 1)) (γ (y - 1)) (δ (y - 1))
        (ε (y - 1)) (ζ (y - 1)) (η (y - 1)) (θ (y - 1)) (ι (y - 1))
        (κ (y - 1)) (lambdaChar (y - 1)) (muChar (y - 1)) hcancel
    _ = (α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
          ε (c - e) * ζ (c - f) * η (c - g) * θ (c - h) * ι (c - i) * κ (c - j) *
            lambdaChar (c - k₀) * muChar (c - l₀)) *
        (α y * β (y - (a - b) / (c - b)) *
          δ (y - (a - d) / (c - d)) * ε (y - (a - e) / (c - e)) *
          ζ (y - (a - f) / (c - f)) * η (y - (a - g) / (c - g)) *
            θ (y - (a - h) / (c - h)) * ι (y - (a - i) / (c - i)) *
              κ (y - (a - j) / (c - j)) *
                lambdaChar (y - (a - k₀) / (c - k₀)) *
                  muChar (y - (a - l₀) / (c - l₀))) := by
      ac_rfl

/-- A degree-balanced Thirteen-root sum is an twelve-point sum with one deleted
projective value, up to a character-valued constant. -/
theorem thirteenRootMulCharSum_eq_elevenPointSum_sub
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ η θ ι κ lambdaChar muChar : MulChar (ZMod p) ℂ)
    (hprod : α * β * γ * δ * ε * ζ * η * θ * ι * κ * lambdaChar * muChar = 1)
    (a b c d e f g h i j k₀ l₀ : ZMod p)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (hec : e ≠ c) (hfc : f ≠ c) (hgc : g ≠ c) (hhc : h ≠ c) (hic : i ≠ c)
    (hjc : j ≠ c) (hk₀c : k₀ ≠ c) (hl₀c : l₀ ≠ c) :
    let lam := (a - b) / (c - b)
    let mu := (a - d) / (c - d)
    let nu := (a - e) / (c - e)
    let xi := (a - f) / (c - f)
    let rho := (a - g) / (c - g)
    let sigma := (a - h) / (c - h)
    let tau := (a - i) / (c - i)
    let upsilon := (a - j) / (c - j)
    let phi := (a - k₀) / (c - k₀)
    let psi := (a - l₀) / (c - l₀)
    (∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
          ε (x - e) * ζ (x - f) * η (x - g) * θ (x - h) * ι (x - i) * κ (x - j) *
            lambdaChar (x - k₀) * muChar (x - l₀)) =
      (α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
          ε (c - e) * ζ (c - f) * η (c - g) * θ (c - h) * ι (c - i) * κ (c - j) *
            lambdaChar (c - k₀) * muChar (c - l₀)) *
        ((∑ y : ZMod p,
            α y * β (y - lam) * δ (y - mu) * ε (y - nu) * ζ (y - xi) *
              η (y - rho) * θ (y - sigma) * ι (y - tau) * κ (y - upsilon) *
                lambdaChar (y - phi) * muChar (y - psi)) -
          β (1 - lam) * δ (1 - mu) * ε (1 - nu) * ζ (1 - xi) *
            η (1 - rho) * θ (1 - sigma) * ι (1 - tau) * κ (1 - upsilon) *
              lambdaChar (1 - phi) * muChar (1 - psi)) := by
  dsimp only
  let mob := threeRootMobiusEquiv p a c hac
  let F : ZMod p → ℂ := fun x =>
    α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
      ε (x - e) * ζ (x - f) * η (x - g) * θ (x - h) * ι (x - i) * κ (x - j) *
        lambdaChar (x - k₀) * muChar (x - l₀)
  let G : ZMod p → ℂ := fun y =>
    α y * β (y - (a - b) / (c - b)) * δ (y - (a - d) / (c - d)) *
      ε (y - (a - e) / (c - e)) * ζ (y - (a - f) / (c - f)) *
        η (y - (a - g) / (c - g)) * θ (y - (a - h) / (c - h)) *
          ι (y - (a - i) / (c - i)) * κ (y - (a - j) / (c - j)) *
            lambdaChar (y - (a - k₀) / (c - k₀)) * muChar (y - (a - l₀) / (c - l₀))
  let C : ℂ :=
    α (c - a) * β (c - b) * γ (c - a) * δ (c - d) *
      ε (c - e) * ζ (c - f) * η (c - g) * θ (c - h) * ι (c - i) * κ (c - j) *
        lambdaChar (c - k₀) * muChar (c - l₀)
  have hone : F (mob.symm 1) = 0 := by
    simp [F, mob, γ.map_zero]
  have hterm (y : ZMod p) (hy : y ∈ Finset.univ.erase 1) :
      F (mob.symm y) = C * G y := by
    have hyOne : y ≠ 1 := by simpa using hy
    simpa [F, G, C, mob] using
      thirteenRootMobius_term p α β γ δ ε ζ η θ ι κ lambdaChar muChar hprod
        a b c d e f g h i j k₀ l₀
        hac hbc hdc hec hfc hgc hhc hic hjc hk₀c hl₀c y hyOne
  calc
    (∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
          ε (x - e) * ζ (x - f) * η (x - g) * θ (x - h) * ι (x - i) * κ (x - j) *
            lambdaChar (x - k₀) * muChar (x - l₀)) =
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

/-- Once the canonical twelve-point trace is bounded, the Thirteen-root identity
costs only the single deleted projective value. -/
theorem norm_thirteenRootMulCharSum_le_eleven_mul_sqrt_add_one_of_elevenPoint
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε ζ η θ ι κ lambdaChar muChar : MulChar (ZMod p) ℂ)
    (hprod : α * β * γ * δ * ε * ζ * η * θ * ι * κ * lambdaChar * muChar = 1)
    (a b c d e f g h i j k₀ l₀ : ZMod p)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (hec : e ≠ c) (hfc : f ≠ c) (hgc : g ≠ c) (hhc : h ≠ c) (hic : i ≠ c)
    (hjc : j ≠ c) (hk₀c : k₀ ≠ c) (hl₀c : l₀ ≠ c)
    (height :
      ‖∑ y : ZMod p,
        α y * β (y - (a - b) / (c - b)) *
          δ (y - (a - d) / (c - d)) *
          ε (y - (a - e) / (c - e)) *
          ζ (y - (a - f) / (c - f)) *
          η (y - (a - g) / (c - g)) *
          θ (y - (a - h) / (c - h)) *
          ι (y - (a - i) / (c - i)) * κ (y - (a - j) / (c - j)) *
            lambdaChar (y - (a - k₀) / (c - k₀)) *
              muChar (y - (a - l₀) / (c - l₀))‖ ≤
        11 * Real.sqrt p) :
    ‖∑ x : ZMod p,
      α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
        ε (x - e) * ζ (x - f) * η (x - g) * θ (x - h) * ι (x - i) * κ (x - j) *
          lambdaChar (x - k₀) * muChar (x - l₀)‖ ≤
      11 * Real.sqrt p + 1 := by
  rw [thirteenRootMulCharSum_eq_elevenPointSum_sub
    p α β γ δ ε ζ η θ ι κ lambdaChar muChar hprod a b c d e f g h i j k₀ l₀
      hac hbc hdc hec hfc hgc hhc hic hjc hk₀c hl₀c]
  simp only [norm_mul]
  have hC :
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ *
          ‖ε (c - e)‖ * ‖ζ (c - f)‖ * ‖η (c - g)‖ * ‖θ (c - h)‖ *
            ‖ι (c - i)‖ * ‖κ (c - j)‖ * ‖lambdaChar (c - k₀)‖ *
              ‖muChar (c - l₀)‖ ≤ 1 := by
    calc
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ *
            ‖ε (c - e)‖ * ‖ζ (c - f)‖ * ‖η (c - g)‖ * ‖θ (c - h)‖ *
              ‖ι (c - i)‖ * ‖κ (c - j)‖ * ‖lambdaChar (c - k₀)‖ *
                ‖muChar (c - l₀)‖ ≤
            1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 := by
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
        · exact DirichletCharacter.norm_le_one lambdaChar _
        · exact DirichletCharacter.norm_le_one muChar _
      _ = 1 := by norm_num
  have hdeleted :
      ‖β (1 - (a - b) / (c - b)) * δ (1 - (a - d) / (c - d)) *
          ε (1 - (a - e) / (c - e)) * ζ (1 - (a - f) / (c - f)) *
            η (1 - (a - g) / (c - g)) * θ (1 - (a - h) / (c - h)) *
              ι (1 - (a - i) / (c - i)) * κ (1 - (a - j) / (c - j)) *
                lambdaChar (1 - (a - k₀) / (c - k₀)) *
                  muChar (1 - (a - l₀) / (c - l₀))‖ ≤ 1 := by
    simp only [norm_mul]
    calc
      ‖β (1 - (a - b) / (c - b))‖ * ‖δ (1 - (a - d) / (c - d))‖ *
            ‖ε (1 - (a - e) / (c - e))‖ * ‖ζ (1 - (a - f) / (c - f))‖ *
              ‖η (1 - (a - g) / (c - g))‖ *
                ‖θ (1 - (a - h) / (c - h))‖ *
                  ‖ι (1 - (a - i) / (c - i))‖ *
                    ‖κ (1 - (a - j) / (c - j))‖ *
                      ‖lambdaChar (1 - (a - k₀) / (c - k₀))‖ *
                        ‖muChar (1 - (a - l₀) / (c - l₀))‖ ≤
                    1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one β _
        · exact DirichletCharacter.norm_le_one δ _
        · exact DirichletCharacter.norm_le_one ε _
        · exact DirichletCharacter.norm_le_one ζ _
        · exact DirichletCharacter.norm_le_one η _
        · exact DirichletCharacter.norm_le_one θ _
        · exact DirichletCharacter.norm_le_one ι _
        · exact DirichletCharacter.norm_le_one κ _
        · exact DirichletCharacter.norm_le_one lambdaChar _
        · exact DirichletCharacter.norm_le_one muChar _
      _ = 1 := by norm_num
  let T : ℂ := ∑ y : ZMod p,
    α y * β (y - (a - b) / (c - b)) *
      δ (y - (a - d) / (c - d)) * ε (y - (a - e) / (c - e)) *
      ζ (y - (a - f) / (c - f)) * η (y - (a - g) / (c - g)) *
        θ (y - (a - h) / (c - h)) * ι (y - (a - i) / (c - i)) *
          κ (y - (a - j) / (c - j)) * lambdaChar (y - (a - k₀) / (c - k₀)) *
            muChar (y - (a - l₀) / (c - l₀))
  let D : ℂ :=
    β (1 - (a - b) / (c - b)) * δ (1 - (a - d) / (c - d)) *
      ε (1 - (a - e) / (c - e)) * ζ (1 - (a - f) / (c - f)) *
        η (1 - (a - g) / (c - g)) * θ (1 - (a - h) / (c - h)) *
          ι (1 - (a - i) / (c - i)) * κ (1 - (a - j) / (c - j)) *
            lambdaChar (1 - (a - k₀) / (c - k₀)) *
              muChar (1 - (a - l₀) / (c - l₀))
  calc
    (‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ * ‖δ (c - d)‖ *
          ‖ε (c - e)‖ * ‖ζ (c - f)‖ * ‖η (c - g)‖ * ‖θ (c - h)‖ *
            ‖ι (c - i)‖ * ‖κ (c - j)‖ * ‖lambdaChar (c - k₀)‖ *
              ‖muChar (c - l₀)‖) * ‖T - D‖ ≤
        1 * ‖T - D‖ := by gcongr
    _ ≤ ‖T‖ + ‖D‖ := by simpa using norm_sub_le T D
    _ ≤ 11 * Real.sqrt p + 1 := by
      exact add_le_add (by simpa [T] using height) (by simpa [D] using hdeleted)

/-- The twelve-point power endpoint gives the projective estimate for Thirteen
distinct roots whose Thirteen local powers multiply to one. -/
theorem norm_thirteenRootMulCharPowerSum_le_eleven_mul_sqrt_add_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerTwelvePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (m n k l s o q z rExp tExp uExp vExp : ℕ)
    (hpowM : χ ^ m ≠ 1) (hpowN : χ ^ n ≠ 1) (hpowK : χ ^ k ≠ 1)
    (hpowL : χ ^ l ≠ 1) (hpowS : χ ^ s ≠ 1) (hpowO : χ ^ o ≠ 1)
    (hpowQ : χ ^ q ≠ 1)
    (hpowZ : χ ^ z ≠ 1)
    (hpowR : χ ^ rExp ≠ 1)
    (hpowT : χ ^ tExp ≠ 1)
    (hpowU : χ ^ uExp ≠ 1)
    (hpowV : χ ^ vExp ≠ 1)
    (hprod :
      (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) * (χ ^ o) *
        (χ ^ q) * (χ ^ z) * (χ ^ rExp) * (χ ^ tExp) * (χ ^ uExp) *
          (χ ^ vExp) = 1)
    (a b c d e f g h i j k₀ l₀ : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (haf : a ≠ f) (hag : a ≠ g) (hah : a ≠ h) (hai : a ≠ i) (haj : a ≠ j)
    (hak₀ : a ≠ k₀) (hal₀ : a ≠ l₀)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hbg : b ≠ g) (hbh : b ≠ h) (hbi : b ≠ i) (hbj : b ≠ j) (hbk₀ : b ≠ k₀)
    (hbl₀ : b ≠ l₀)
    (hdc : d ≠ c) (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hdh : d ≠ h) (hdi : d ≠ i) (hdj : d ≠ j) (hdk₀ : d ≠ k₀) (hdl₀ : d ≠ l₀)
    (hec : e ≠ c) (hef : e ≠ f) (heg : e ≠ g) (heh : e ≠ h) (hei : e ≠ i)
    (hej : e ≠ j) (hek₀ : e ≠ k₀) (hel₀ : e ≠ l₀)
    (hfc : f ≠ c) (hfg : f ≠ g) (hfh : f ≠ h) (hfi : f ≠ i) (hfj : f ≠ j)
    (hfk₀ : f ≠ k₀) (hfl₀ : f ≠ l₀)
    (hgc : g ≠ c) (hgh : g ≠ h) (hgi : g ≠ i) (hgj : g ≠ j) (hgk₀ : g ≠ k₀)
    (hgl₀ : g ≠ l₀)
    (hhc : h ≠ c) (hhi : h ≠ i) (hhj : h ≠ j) (hhk₀ : h ≠ k₀) (hhl₀ : h ≠ l₀)
    (hic : i ≠ c) (hij : i ≠ j) (hik₀ : i ≠ k₀) (hil₀ : i ≠ l₀)
    (hjc : j ≠ c) (hjk₀ : j ≠ k₀) (hjl₀ : j ≠ l₀)
    (hk₀c : k₀ ≠ c) (hk₀l₀ : k₀ ≠ l₀) (hl₀c : l₀ ≠ c) :
    ‖∑ x : ZMod p,
      (χ ^ m) (x - a) * (χ ^ n) (x - b) * (χ ^ k) (x - c) *
        (χ ^ l) (x - d) * (χ ^ s) (x - e) * (χ ^ o) (x - f) *
          (χ ^ q) (x - g) * (χ ^ z) (x - h) * (χ ^ rExp) (x - i) *
            (χ ^ tExp) (x - j) * (χ ^ uExp) (x - k₀) *
              (χ ^ vExp) (x - l₀)‖ ≤
      11 * Real.sqrt p + 1 := by
  let lam : ZMod p := (a - b) / (c - b)
  let mu : ZMod p := (a - d) / (c - d)
  let nu : ZMod p := (a - e) / (c - e)
  let xi : ZMod p := (a - f) / (c - f)
  let rho : ZMod p := (a - g) / (c - g)
  let sigma : ZMod p := (a - h) / (c - h)
  let tau : ZMod p := (a - i) / (c - i)
  let upsilon : ZMod p := (a - j) / (c - j)
  let phi : ZMod p := (a - k₀) / (c - k₀)
  let psi : ZMod p := (a - l₀) / (c - l₀)
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
  have hphi : phi ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hak₀) (sub_ne_zero.mpr hk₀c.symm)
  have hpsi : psi ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hal₀) (sub_ne_zero.mpr hl₀c.symm)
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
  have hlamphi : lam ≠ phi := crossRatio_ne hbc hk₀c hbk₀
  have hlampsi : lam ≠ psi := crossRatio_ne hbc hl₀c hbl₀
  have hmunu : mu ≠ nu := crossRatio_ne hdc hec hde
  have hmuxi : mu ≠ xi := crossRatio_ne hdc hfc hdf
  have hmurho : mu ≠ rho := crossRatio_ne hdc hgc hdg
  have hmusigma : mu ≠ sigma := crossRatio_ne hdc hhc hdh
  have hmutau : mu ≠ tau := crossRatio_ne hdc hic hdi
  have hmuupsilon : mu ≠ upsilon := crossRatio_ne hdc hjc hdj
  have hmuphi : mu ≠ phi := crossRatio_ne hdc hk₀c hdk₀
  have hmupsi : mu ≠ psi := crossRatio_ne hdc hl₀c hdl₀
  have hnuxi : nu ≠ xi := crossRatio_ne hec hfc hef
  have hnurho : nu ≠ rho := crossRatio_ne hec hgc heg
  have hnusigma : nu ≠ sigma := crossRatio_ne hec hhc heh
  have hnutau : nu ≠ tau := crossRatio_ne hec hic hei
  have hnuupsilon : nu ≠ upsilon := crossRatio_ne hec hjc hej
  have hnuphi : nu ≠ phi := crossRatio_ne hec hk₀c hek₀
  have hnupsi : nu ≠ psi := crossRatio_ne hec hl₀c hel₀
  have hxirho : xi ≠ rho := crossRatio_ne hfc hgc hfg
  have hxisigma : xi ≠ sigma := crossRatio_ne hfc hhc hfh
  have hxitau : xi ≠ tau := crossRatio_ne hfc hic hfi
  have hxiupsilon : xi ≠ upsilon := crossRatio_ne hfc hjc hfj
  have hxiphi : xi ≠ phi := crossRatio_ne hfc hk₀c hfk₀
  have hxipsi : xi ≠ psi := crossRatio_ne hfc hl₀c hfl₀
  have hrhosigma : rho ≠ sigma := crossRatio_ne hgc hhc hgh
  have hrhotau : rho ≠ tau := crossRatio_ne hgc hic hgi
  have hrhoupsilon : rho ≠ upsilon := crossRatio_ne hgc hjc hgj
  have hrhophi : rho ≠ phi := crossRatio_ne hgc hk₀c hgk₀
  have hrhopsi : rho ≠ psi := crossRatio_ne hgc hl₀c hgl₀
  have hsigmatau : sigma ≠ tau := crossRatio_ne hhc hic hhi
  have hsigmaupsilon : sigma ≠ upsilon := crossRatio_ne hhc hjc hhj
  have hsigmaphi : sigma ≠ phi := crossRatio_ne hhc hk₀c hhk₀
  have hsigmapsi : sigma ≠ psi := crossRatio_ne hhc hl₀c hhl₀
  have htauupsilon : tau ≠ upsilon := crossRatio_ne hic hjc hij
  have htauphi : tau ≠ phi := crossRatio_ne hic hk₀c hik₀
  have htaupsi : tau ≠ psi := crossRatio_ne hic hl₀c hil₀
  have hupsilonphi : upsilon ≠ phi := crossRatio_ne hjc hk₀c hjk₀
  have hupsilonpsi : upsilon ≠ psi := crossRatio_ne hjc hl₀c hjl₀
  have hphipsi : phi ≠ psi := crossRatio_ne hk₀c hl₀c hk₀l₀
  have hfiniteProd :
      χ ^ (m + n + l + s + o + q + z + rExp + tExp + uExp + vExp) ≠ 1 := by
    intro heq
    apply hpowK
    calc
      χ ^ k = 1 * χ ^ k := by simp
      _ = χ ^ (m + n + l + s + o + q + z + rExp + tExp + uExp + vExp) *
          χ ^ k := by rw [heq]
      _ = (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) * (χ ^ o) *
          (χ ^ q) * (χ ^ z) * (χ ^ rExp) * (χ ^ tExp) * (χ ^ uExp) *
            (χ ^ vExp) := by
        simp only [pow_add]
        ac_rfl
      _ = 1 := hprod
  have height :
      ‖∑ y : ZMod p,
        (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ l) (y - mu) *
          (χ ^ s) (y - nu) * (χ ^ o) (y - xi) * (χ ^ q) (y - rho) *
            (χ ^ z) (y - sigma) * (χ ^ rExp) (y - tau) *
              (χ ^ tExp) (y - upsilon) * (χ ^ uExp) (y - phi) *
                (χ ^ vExp) (y - psi)‖ ≤ 11 * Real.sqrt p :=
    hweil χ m n l s o q z rExp tExp uExp vExp
      lam mu nu xi rho sigma tau upsilon phi psi
      hpowM hpowN hpowL hpowS hpowO hpowQ hpowZ hpowR hpowT hpowU hpowV hfiniteProd
      hlam hmu hnu hxi hrho hsigma htau hupsilon hphi hpsi
      hlammu hlamnu hlamxi hlamrho hlamsigma hlamtau hlamupsilon hlamphi hlampsi
      hmunu hmuxi hmurho hmusigma hmutau hmuupsilon hmuphi hmupsi
      hnuxi hnurho hnusigma hnutau hnuupsilon hnuphi hnupsi
      hxirho hxisigma hxitau hxiupsilon hxiphi hxipsi
      hrhosigma hrhotau hrhoupsilon hrhophi hrhopsi
      hsigmatau hsigmaupsilon hsigmaphi hsigmapsi
      htauupsilon htauphi htaupsi hupsilonphi hupsilonpsi hphipsi
  exact norm_thirteenRootMulCharSum_le_eleven_mul_sqrt_add_one_of_elevenPoint
    p (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l) (χ ^ s) (χ ^ o) (χ ^ q) (χ ^ z)
      (χ ^ rExp) (χ ^ tExp) (χ ^ uExp) (χ ^ vExp) hprod a b c d e f g h i j k₀ l₀
      hac hbc hdc hec hfc hgc hhc hic hjc hk₀c hl₀c height

set_option maxHeartbeats 40000000 in
/-- Exactly Thirteen active roots of character-order-divisible degree reduce to
the source-shaped twelve-point endpoint. -/
theorem norm_primeActiveRootCharacterSum_le_eleven_mul_sqrt_add_one_of_card_eq_thirteen_degree_power
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerTwelvePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 12) :
    ‖primeActiveRootCharacterSum p χ P‖ ≤ 11 * Real.sqrt p + 1 := by
  let S := primeActiveRoots p χ P
  obtain ⟨u, huS⟩ : S.Nonempty := Finset.card_pos.mp (by simp [S, hcard])
  have hcardS : S.card = 12 := by simpa only [S] using hcard
  have hcardOne : (S.erase u).card = 11 := by
    rw [Finset.card_erase_of_mem huS]
    omega
  obtain ⟨v, hvOne⟩ : (S.erase u).Nonempty := Finset.card_pos.mp (by omega)
  have hcardTwo : ((S.erase u).erase v).card = 10 := by
    rw [Finset.card_erase_of_mem hvOne, hcardOne]
  obtain ⟨w, hwTwo⟩ : ((S.erase u).erase v).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardThree : (((S.erase u).erase v).erase w).card = 9 := by
    rw [Finset.card_erase_of_mem hwTwo, hcardTwo]
  obtain ⟨z, hzThree⟩ : (((S.erase u).erase v).erase w).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardFour : ((((S.erase u).erase v).erase w).erase z).card = 8 := by
    rw [Finset.card_erase_of_mem hzThree, hcardThree]
  obtain ⟨t, htFour⟩ : ((((S.erase u).erase v).erase w).erase z).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardFive : (((((S.erase u).erase v).erase w).erase z).erase t).card = 7 := by
    rw [Finset.card_erase_of_mem htFour, hcardFour]
  obtain ⟨q, hqFive⟩ : (((((S.erase u).erase v).erase w).erase z).erase t).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardSix : ((((((S.erase u).erase v).erase w).erase z).erase t).erase q).card = 6 := by
    rw [Finset.card_erase_of_mem hqFive, hcardFive]
  obtain ⟨r, hrSix⟩ : ((((((S.erase u).erase v).erase w).erase z).erase t).erase q).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardSeven : (((((((S.erase u).erase v).erase w).erase z).erase t).erase q).erase r).card = 5 := by
    rw [Finset.card_erase_of_mem hrSix, hcardSix]
  obtain ⟨x, hxSeven⟩ :
      (((((((S.erase u).erase v).erase w).erase z).erase t).erase q).erase r).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardEight :
      ((((((((S.erase u).erase v).erase w).erase z).erase t).erase q).erase r).erase x).card = 4 := by
    rw [Finset.card_erase_of_mem hxSeven, hcardSeven]
  obtain ⟨y, j, k₀, l₀, hyj, hyk₀, hyl₀, hjk₀, hjl₀, hk₀l₀, hrest⟩ :=
    Finset.card_eq_four.mp hcardEight
  have hyEight : y ∈
      (((((((S.erase u).erase v).erase w).erase z).erase t).erase q).erase r).erase x := by
    simp [hrest]
  have hjEight : j ∈
      (((((((S.erase u).erase v).erase w).erase z).erase t).erase q).erase r).erase x := by
    simp [hrest]
  have hk₀Eight : k₀ ∈
      (((((((S.erase u).erase v).erase w).erase z).erase t).erase q).erase r).erase x := by
    simp [hrest]
  have hl₀Eight : l₀ ∈
      (((((((S.erase u).erase v).erase w).erase z).erase t).erase q).erase r).erase x := by
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
  have hxData : x ≠ r ∧ x ≠ q ∧ x ≠ t ∧ x ≠ z ∧ x ≠ w ∧ x ≠ v ∧ x ≠ u ∧ x ∈ S := by
    simpa only [Finset.mem_erase] using hxSeven
  have hyData : y ≠ x ∧ y ≠ r ∧ y ≠ q ∧ y ≠ t ∧ y ≠ z ∧ y ≠ w ∧ y ≠ v ∧
      y ≠ u ∧ y ∈ S := by
    simpa only [Finset.mem_erase] using hyEight
  have hjData : j ≠ x ∧ j ≠ r ∧ j ≠ q ∧ j ≠ t ∧ j ≠ z ∧ j ≠ w ∧ j ≠ v ∧
      j ≠ u ∧ j ∈ S := by
    simpa only [Finset.mem_erase] using hjEight
  have hk₀Data : k₀ ≠ x ∧ k₀ ≠ r ∧ k₀ ≠ q ∧ k₀ ≠ t ∧ k₀ ≠ z ∧ k₀ ≠ w ∧
      k₀ ≠ v ∧ k₀ ≠ u ∧ k₀ ∈ S := by
    simpa only [Finset.mem_erase] using hk₀Eight
  have hl₀Data : l₀ ≠ x ∧ l₀ ≠ r ∧ l₀ ≠ q ∧ l₀ ≠ t ∧ l₀ ≠ z ∧ l₀ ≠ w ∧
      l₀ ≠ v ∧ l₀ ≠ u ∧ l₀ ∈ S := by
    simpa only [Finset.mem_erase] using hl₀Eight
  rcases hvData with ⟨hvu, hvS⟩
  rcases hwData with ⟨hwv, hwu, hwS⟩
  rcases hzData with ⟨hzw, hzv, hzu, hzS⟩
  rcases htData with ⟨htz, htw, htv, htu, htS⟩
  rcases hqData with ⟨hqt, hqz, hqw, hqv, hqu, hqS⟩
  rcases hrData with ⟨hrq, hrt, hrz, hrw, hrv, hru, hrS⟩
  rcases hxData with ⟨hxr, hxq, hxt, hxz, hxw, hxv, hxu, hxS⟩
  rcases hyData with ⟨hyx, hyr, hyq, hyt, hyz, hyw, hyv, hyu, hyS⟩
  rcases hjData with ⟨hjx, hjr, hjq, hjt, hjz, hjw, hjv, hju, hjS⟩
  rcases hk₀Data with ⟨hk₀x, hk₀r, hk₀q, hk₀t, hk₀z, hk₀w, hk₀v, hk₀u, hk₀S⟩
  rcases hl₀Data with ⟨hl₀x, hl₀r, hl₀q, hl₀t, hl₀z, hl₀w, hl₀v, hl₀u, hl₀S⟩
  have huv : u ≠ v := hvu.symm
  have huw : u ≠ w := hwu.symm
  have huz : u ≠ z := hzu.symm
  have hut : u ≠ t := htu.symm
  have huq : u ≠ q := hqu.symm
  have hur : u ≠ r := hru.symm
  have hux : u ≠ x := hxu.symm
  have huy : u ≠ y := hyu.symm
  have huj : u ≠ j := hju.symm
  have huk₀ : u ≠ k₀ := hk₀u.symm
  have hul₀ : u ≠ l₀ := hl₀u.symm
  have hvw : v ≠ w := hwv.symm
  have hvz : v ≠ z := hzv.symm
  have hvt : v ≠ t := htv.symm
  have hvq : v ≠ q := hqv.symm
  have hvr : v ≠ r := hrv.symm
  have hvx : v ≠ x := hxv.symm
  have hvy : v ≠ y := hyv.symm
  have hvj : v ≠ j := hjv.symm
  have hvk₀ : v ≠ k₀ := hk₀v.symm
  have hvl₀ : v ≠ l₀ := hl₀v.symm
  have hwz : w ≠ z := hzw.symm
  have hwt : w ≠ t := htw.symm
  have hwq : w ≠ q := hqw.symm
  have hwr : w ≠ r := hrw.symm
  have hwx : w ≠ x := hxw.symm
  have hwy : w ≠ y := hyw.symm
  have hwj : w ≠ j := hjw.symm
  have hwk₀ : w ≠ k₀ := hk₀w.symm
  have hwl₀ : w ≠ l₀ := hl₀w.symm
  have hzt : z ≠ t := htz.symm
  have hzq : z ≠ q := hqz.symm
  have hzr : z ≠ r := hrz.symm
  have hzx : z ≠ x := hxz.symm
  have hzy : z ≠ y := hyz.symm
  have hzj : z ≠ j := hjz.symm
  have hzk₀ : z ≠ k₀ := hk₀z.symm
  have hzl₀ : z ≠ l₀ := hl₀z.symm
  have htq : t ≠ q := hqt.symm
  have htr : t ≠ r := hrt.symm
  have htx : t ≠ x := hxt.symm
  have hty : t ≠ y := hyt.symm
  have htj : t ≠ j := hjt.symm
  have htk₀ : t ≠ k₀ := hk₀t.symm
  have htl₀ : t ≠ l₀ := hl₀t.symm
  have hqr : q ≠ r := hrq.symm
  have hqx : q ≠ x := hxq.symm
  have hqy : q ≠ y := hyq.symm
  have hqj : q ≠ j := hjq.symm
  have hqk₀ : q ≠ k₀ := hk₀q.symm
  have hql₀ : q ≠ l₀ := hl₀q.symm
  have hrx : r ≠ x := hxr.symm
  have hry : r ≠ y := hyr.symm
  have hrj : r ≠ j := hjr.symm
  have hrk₀ : r ≠ k₀ := hk₀r.symm
  have hrl₀ : r ≠ l₀ := hl₀r.symm
  have hxy : x ≠ y := hyx.symm
  have hxj : x ≠ j := hjx.symm
  have hxk₀ : x ≠ k₀ := hk₀x.symm
  have hxl₀ : x ≠ l₀ := hl₀x.symm
  have huTail : u ∉ ({v, w, z, t, q, r, x, y, j, k₀, l₀} : Finset (ZMod p)) := by
    simp [huv, huw, huz, hut, huq, hur, hux, huy, huj, huk₀, hul₀]
  have hvTail : v ∉ ({w, z, t, q, r, x, y, j, k₀, l₀} : Finset (ZMod p)) := by
    simp [hvw, hvz, hvt, hvq, hvr, hvx, hvy, hvj, hvk₀, hvl₀]
  have hwTail : w ∉ ({z, t, q, r, x, y, j, k₀, l₀} : Finset (ZMod p)) := by
    simp [hwz, hwt, hwq, hwr, hwx, hwy, hwj, hwk₀, hwl₀]
  have hzTail : z ∉ ({t, q, r, x, y, j, k₀, l₀} : Finset (ZMod p)) := by
    simp [hzt, hzq, hzr, hzx, hzy, hzj, hzk₀, hzl₀]
  have htTail : t ∉ ({q, r, x, y, j, k₀, l₀} : Finset (ZMod p)) := by
    simp [htq, htr, htx, hty, htj, htk₀, htl₀]
  have hqTail : q ∉ ({r, x, y, j, k₀, l₀} : Finset (ZMod p)) := by
    simp [hqr, hqx, hqy, hqj, hqk₀, hql₀]
  have hrTail : r ∉ ({x, y, j, k₀, l₀} : Finset (ZMod p)) := by
    simp [hrx, hry, hrj, hrk₀, hrl₀]
  have hxTail : x ∉ ({y, j, k₀, l₀} : Finset (ZMod p)) := by
    simp [hxy, hxj, hxk₀, hxl₀]
  have hyTail : y ∉ ({j, k₀, l₀} : Finset (ZMod p)) := by
    simp [hyj, hyk₀, hyl₀]
  have hjTail : j ∉ ({k₀, l₀} : Finset (ZMod p)) := by
    simp [hjk₀, hjl₀]
  have hk₀Tail : k₀ ∉ ({l₀} : Finset (ZMod p)) := by simp [hk₀l₀]
  have hroots : S = {u, v, w, z, t, q, r, x, y, j, k₀, l₀} := by
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
      _ = insert u (insert v (insert w (insert z (insert t (insert q
          (insert r (((((((S.erase u).erase v).erase w).erase z).erase t).erase q).erase r))))))) := by
        rw [Finset.insert_erase hrSix]
      _ = insert u (insert v (insert w (insert z (insert t (insert q (insert r
          (insert x ((((((((S.erase u).erase v).erase w).erase z).erase t).erase q).erase r).erase x)))))))) := by
        rw [Finset.insert_erase hxSeven]
      _ = {u, v, w, z, t, q, r, x, y, j, k₀, l₀} := by rw [hrest]
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
  have hk₀Active : k₀ ∈ primeActiveRoots p χ P := by simpa only [S] using hk₀S
  have hl₀Active : l₀ ∈ primeActiveRoots p χ P := by simpa only [S] using hl₀S
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
  have hk₀Root : k₀ ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hk₀Active
  have hl₀Root : l₀ ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hl₀Active
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
  let un := P.roots.count k₀
  let vn := P.roots.count l₀
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
  have hun : un ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hk₀Root)).ne'
  have hvn : vn ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hl₀Root)).ne'
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
  have hpowUn : χ ^ un ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hk₀Active).2 (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowVn : χ ^ vn ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hl₀Active).2 (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hsum := orderOf_dvd_sum_primeActiveRoots_count p χ P hP hdegree
  have hmnklsoqzrtuv :
      orderOf χ ∣ m + n + k + l + s + o + qn + zn + rn + tn + un + vn := by
    rw [show primeActiveRoots p χ P = {u, v, w, z, t, q, r, x, y, j, k₀, l₀} by
      simpa [S] using hroots] at hsum
    rw [Finset.sum_insert huTail, Finset.sum_insert hvTail,
      Finset.sum_insert hwTail, Finset.sum_insert hzTail,
      Finset.sum_insert htTail, Finset.sum_insert hqTail,
      Finset.sum_insert hrTail, Finset.sum_insert hxTail,
      Finset.sum_insert hyTail, Finset.sum_insert hjTail,
      Finset.sum_insert hk₀Tail, Finset.sum_singleton] at hsum
    simpa [m, n, k, l, s, o, qn, zn, rn, tn, un, vn, add_assoc] using hsum
  have hprod :
      (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) * (χ ^ o) *
        (χ ^ qn) * (χ ^ zn) * (χ ^ rn) * (χ ^ tn) * (χ ^ un) * (χ ^ vn) = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    exact orderOf_dvd_iff_pow_eq_one.mp hmnklsoqzrtuv
  have htwelve := norm_thirteenRootMulCharPowerSum_le_eleven_mul_sqrt_add_one
    p hweil χ m n k l s o qn zn rn tn un vn
      hpowM hpowN hpowK hpowL hpowS hpowO hpowQn hpowZn hpowRn hpowTn hpowUn hpowVn
      hprod u v w z t q r x y j k₀ l₀
      huv huw huz hut huq hur hux huy huj huk₀ hul₀
      hvw hvz hvt hvq hvr hvx hvy hvj hvk₀ hvl₀
      hwz.symm hzt hzq hzr hzx hzy hzj hzk₀ hzl₀
      hwt.symm htq htr htx hty htj htk₀ htl₀
      hwq.symm hqr hqx hqy hqj hqk₀ hql₀
      hwr.symm hrx hry hrj hrk₀ hrl₀
      hwx.symm hxy hxj hxk₀ hxl₀
      hwy.symm hyj hyk₀ hyl₀
      hwj.symm hjk₀ hjl₀ hwk₀.symm hk₀l₀ hwl₀.symm
  unfold primeActiveRootCharacterSum
  rw [show primeActiveRoots p χ P = {u, v, w, z, t, q, r, x, y, j, k₀, l₀} by
    simpa [S] using hroots]
  convert htwelve using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.prod_insert huTail, Finset.prod_insert hvTail,
    Finset.prod_insert hwTail, Finset.prod_insert hzTail,
    Finset.prod_insert htTail, Finset.prod_insert hqTail,
    Finset.prod_insert hrTail, Finset.prod_insert hxTail,
    Finset.prod_insert hyTail, Finset.prod_insert hjTail,
    Finset.prod_insert hk₀Tail, Finset.prod_singleton]
  rw [MulChar.pow_apply' χ hm, MulChar.pow_apply' χ hn,
    MulChar.pow_apply' χ hk, MulChar.pow_apply' χ hl,
    MulChar.pow_apply' χ hs, MulChar.pow_apply' χ ho, MulChar.pow_apply' χ hqn,
    MulChar.pow_apply' χ hzn, MulChar.pow_apply' χ hrn, MulChar.pow_apply' χ htn,
    MulChar.pow_apply' χ hun, MulChar.pow_apply' χ hvn]
  simp [m, n, k, l, s, o, qn, zn, rn, tn, un, vn, Polynomial.count_roots]
  ac_rfl

/-- The twelve-point power endpoint discharges the split-polynomial target when
exactly Thirteen roots are active and degree is character-order divisible. -/
theorem primeSplitPolynomialWeilBound_of_card_activeRoots_eq_thirteen_degree_power
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerTwelvePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (_a : ZMod p) (_hχ : χ ≠ 1) (hP : P.Splits)
    (_hnot : ¬orderOf χ ∣ P.rootMultiplicity _a)
    (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 12) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
  have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
  have hactive :=
    norm_primeActiveRootCharacterSum_le_eleven_mul_sqrt_add_one_of_card_eq_thirteen_degree_power
      p hweil χ P hP hdegree hcard
  have hrestricted :=
    norm_filter_primeActiveRootProduct_le_of_activeRootCharacterSum
      p χ P (11 * Real.sqrt p + 1) hactive
  have hrootCard : 12 ≤ P.roots.toFinset.card := by
    rw [← hcard]
    exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
  have hInactiveCard :
      (primeInactiveRoots p χ P).card ≤ P.roots.toFinset.card :=
    Finset.card_le_card (primeInactiveRoots_subset_roots p χ P)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hroom :
      11 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
    have hInactiveCard' :
        ((primeInactiveRoots p χ P).card : ℝ) ≤
          (P.roots.toFinset.card : ℝ) := by exact_mod_cast hInactiveCard
    have hrootCard' : (12 : ℝ) ≤ P.roots.toFinset.card := by
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
    _ ≤ 11 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card := by
      simpa using hrestricted
    _ ≤ ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := hroom

end

end Tao2026
