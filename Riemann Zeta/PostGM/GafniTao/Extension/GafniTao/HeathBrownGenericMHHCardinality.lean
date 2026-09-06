import GafniTao.HeathBrownSymmetricMHH
import GafniTao.HeathBrownFullyUniformOutputs

/-!
# MHH bound for an arbitrary powered cardinality packet

The fully uniform output stores cardinality packets at consecutive powers.
The earlier MHH consumer was specialized to the first packet.  The source's
high-cell companion argument needs the same theorem at `p+1`; this module
states the packet-level result once, without manufacturing an energy packet
at the companion power.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem HeathBrownPoweredCardinalityPacket.card_le_mhh_common_generic
    {epsilonMHH U R eta L : Real} {N p P : Nat}
    {W : Finset Real} {a : Nat → Complex} {Cmhh : Real}
    (packet : HeathBrownPoweredCardinalityPacket
      ((2 ^ P : Real) * U) R N p eta L W a)
    (hCmhh : 0 ≤ Cmhh)
    (hMHH : ∀ (M : Nat) (B R' V : Real) (W' : Finset Real)
        (b : Nat → Complex),
      0 < M → 1 ≤ B → (M : Real) ≤ B → 0 < V → 2 * R' ≤ B →
      IsSeparated 1 W' →
      (∀ t ∈ W', -R' ≤ t ∧ t ≤ R') →
      (∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) →
      (∀ t ∈ W', V ≤ ‖sourceDirichletPoly M b t‖) →
      (W'.card : Real) ≤
        Cmhh * B ^ epsilonMHH *
          ((M : Real) ^ 2 / V ^ 2 +
            B * min ((M : Real) / V ^ 2)
              ((M : Real) ^ 4 / V ^ 6)))
    (hU : 1 ≤ U) (hN : 0 < N) (hp : 0 < p) (hpP : p ≤ P)
    (hNpU : (N : Real) ^ p ≤ U) (hL : 0 < L)
    (hRB : 2 * R ≤ (2 ^ P : Real) * U)
    (hSep : IsSeparated 1 W)
    (hSymm : ∀ t ∈ W, -R ≤ t ∧ t ≤ R) :
    let B := (2 ^ P : Real) * U
    let Q := ((2 ^ P : Nat) : Real) * (N ^ p : Nat)
    let V := heathBrownPoweredThreshold N p L packet.Cp eta
    (W.card : Real) ≤
      p * Cmhh * B ^ epsilonMHH *
        (Q ^ 2 / V ^ 2 + B * Q ^ 4 / V ^ 6) := by
  let B : Real := (2 ^ P : Real) * U
  let M : Nat := 2 ^ packet.r * N ^ p
  let Q : Real := ((2 ^ P : Nat) : Real) * (N ^ p : Nat)
  let V : Real := heathBrownPoweredThreshold N p L packet.Cp eta
  have hB : 1 ≤ B := by
    have hTwo : (1 : Real) ≤ (2 : Real) ^ P := one_le_pow₀ (by norm_num)
    dsimp only [B]
    nlinarith [mul_le_mul hTwo hU (by norm_num : (0 : Real) ≤ 1)
      (by positivity : (0 : Real) ≤ (2 : Real) ^ P)]
  have hM : 0 < M := by
    dsimp only [M]
    exact Nat.mul_pos (pow_pos (by omega) _) (pow_pos hN _)
  have hrP : packet.r ≤ P :=
    (Finset.mem_range.mp packet.hr).le.trans hpP
  have hTwo : (2 : Real) ^ packet.r ≤ (2 : Real) ^ P :=
    pow_le_pow_right₀ (by norm_num) hrP
  have hMleQ : (M : Real) ≤ Q := by
    dsimp only [M, Q]
    push_cast
    exact mul_le_mul hTwo (le_refl ((N : Real) ^ p))
      (by positivity) (by positivity)
  have hQleB : Q ≤ B := by
    dsimp only [Q, B]
    push_cast
    exact mul_le_mul_of_nonneg_left hNpU (by positivity)
  have hV : 0 < V := by
    dsimp only [V, heathBrownPoweredThreshold]
    have hpR : (0 : Real) < p := by exact_mod_cast hp
    have hBaseNat : 0 < 2 ^ p * N ^ p :=
      Nat.mul_pos (pow_pos (by omega) p) (pow_pos hN p)
    have hBaseReal : (0 : Real) < (2 ^ p * N ^ p : Nat) := by
      exact_mod_cast hBaseNat
    have hRpow : 0 < ((2 ^ p * N ^ p : Nat) : Real) ^ eta :=
      Real.rpow_pos_of_pos hBaseReal eta
    exact div_pos (div_pos (pow_pos hL p) (mul_pos packet.hCp hRpow)) hpR
  have hSep' : IsSeparated 1 packet.W' := by
    intro x hx y hy hxy
    exact hSep x (packet.hW' hx) y (packet.hW' hy) hxy
  have hSymm' : ∀ t ∈ packet.W', -R ≤ t ∧ t ≤ R := by
    intro t ht
    exact hSymm t (packet.hW' ht)
  have hRaw := hMHH M B R V packet.W'
    (sourceNormalizedFinitePoweredCoeffs N p a packet.Cp eta)
    hM hB (hMleQ.trans hQleB) hV hRB hSep' hSymm'
    (by simpa only [M] using packet.hUnit)
    (by simpa only [M, V] using packet.hLarge)
  have hMin : min ((M : Real) / V ^ 2) ((M : Real) ^ 4 / V ^ 6) ≤
      (M : Real) ^ 4 / V ^ 6 := min_le_right _ _
  have hExpr :
      (M : Real) ^ 2 / V ^ 2 +
          B * min ((M : Real) / V ^ 2) ((M : Real) ^ 4 / V ^ 6) ≤
        Q ^ 2 / V ^ 2 + B * Q ^ 4 / V ^ 6 := by
    have hM0 : (0 : Real) ≤ M := by positivity
    have hQ0 : 0 ≤ Q := by positivity
    have hPow2 : (M : Real) ^ 2 ≤ Q ^ 2 := by gcongr
    have hPow4 : (M : Real) ^ 4 ≤ Q ^ 4 := by gcongr
    have hB0 : 0 ≤ B := zero_le_one.trans hB
    have hDiv4 : (M : Real) ^ 4 / V ^ 6 ≤ Q ^ 4 / V ^ 6 :=
      div_le_div_of_nonneg_right hPow4 (by positivity)
    have hTerm4 : B * ((M : Real) ^ 4 / V ^ 6) ≤
        B * Q ^ 4 / V ^ 6 := by
      calc
        B * ((M : Real) ^ 4 / V ^ 6) ≤ B * (Q ^ 4 / V ^ 6) :=
          mul_le_mul_of_nonneg_left hDiv4 hB0
        _ = B * Q ^ 4 / V ^ 6 := by ring
    calc
      (M : Real) ^ 2 / V ^ 2 +
          B * min ((M : Real) / V ^ 2) ((M : Real) ^ 4 / V ^ 6) ≤
          (M : Real) ^ 2 / V ^ 2 + B * ((M : Real) ^ 4 / V ^ 6) := by
            gcongr
      _ ≤ Q ^ 2 / V ^ 2 + B * Q ^ 4 / V ^ 6 := by
        have hDiv2 : (M : Real) ^ 2 / V ^ 2 ≤ Q ^ 2 / V ^ 2 :=
          div_le_div_of_nonneg_right hPow2 (by positivity)
        exact add_le_add hDiv2 hTerm4
  have hFactor : 0 ≤ Cmhh * B ^ epsilonMHH := by positivity
  have hW' : (packet.W'.card : Real) ≤
      Cmhh * B ^ epsilonMHH *
        (Q ^ 2 / V ^ 2 + B * Q ^ 4 / V ^ 6) :=
    hRaw.trans (mul_le_mul_of_nonneg_left hExpr hFactor)
  have hp0 : (0 : Real) ≤ p := by positivity
  simpa only [B, Q, V] using
    (calc
      (W.card : Real) ≤ p * (packet.W'.card : Real) := packet.hCard
      _ ≤ p * (Cmhh * B ^ epsilonMHH *
          (Q ^ 2 / V ^ 2 + B * Q ^ 4 / V ^ 6)) :=
        mul_le_mul_of_nonneg_left hW' hp0
      _ = p * Cmhh * B ^ epsilonMHH *
          (Q ^ 2 / V ^ 2 + B * Q ^ 4 / V ^ 6) := by ring)

#print axioms HeathBrownPoweredCardinalityPacket.card_le_mhh_common_generic

end
end GafniTao
