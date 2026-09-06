import GafniTao.HeathBrownSymmetricMHH
import GafniTao.HeathBrownFullyUniformOutputs

/-!
# MHH cardinality bound for the actual Heath--Brown powered block

This is the high-line companion to the two mean-value cardinality bounds.
It consumes the `p`-power block stored in the real fully uniform output and
applies the symmetric source MHH theorem to that very block.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Exact common-length MHH bound for the actual selected `p`-power packet.
The `min` in MHH is bounded by its sixth-power member, which is precisely the
high-line alternative used by Heath--Brown. -/
theorem HeathBrownFullyUniformOutputs.card_le_mhh_common
    {epsilon epsilonMHH U R eta L : Real} {N p P : Nat}
    {W : Finset Real} {a : Nat → Complex}
    {Cp Cmv C0 C2 C4 Cmhh : Real}
    (full : HeathBrownFullyUniformOutputs epsilon
      ((2 ^ P : Real) * U) R N p eta L W a
      Cp Cmv C0 C2 C4)
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
    (hNpU : (N : Real) ^ p ≤ U)
    (hL : 0 < L)
    (hRB : 2 * R ≤ (2 ^ P : Real) * U)
    (hSep : IsSeparated 1 W)
    (hSymm : ∀ t ∈ W, -R ≤ t ∧ t ≤ R) :
    let B := (2 ^ P : Real) * U
    let Q := ((2 ^ P : Nat) : Real) * (N ^ p : Nat)
    let V := heathBrownPoweredThreshold N p L Cp eta
    (W.card : Real) ≤
      p * Cmhh * B ^ epsilonMHH *
        (Q ^ 2 / V ^ 2 + B * Q ^ 4 / V ^ 6) := by
  let B : Real := (2 ^ P : Real) * U
  let M : Nat := 2 ^ full.card.r * N ^ p
  let Q : Real := ((2 ^ P : Nat) : Real) * (N ^ p : Nat)
  let V : Real := heathBrownPoweredThreshold N p L Cp eta
  have hB : 1 ≤ B := by
    have hTwo : (1 : Real) ≤ (2 : Real) ^ P := one_le_pow₀ (by norm_num)
    dsimp only [B]
    nlinarith [mul_le_mul hTwo hU (by norm_num : (0 : Real) ≤ 1)
      (by positivity : (0 : Real) ≤ (2 : Real) ^ P)]
  have hM : 0 < M := by
    dsimp only [M]
    exact Nat.mul_pos (pow_pos (by omega) _) (pow_pos hN _)
  have hrP : full.card.r ≤ P :=
    (Finset.mem_range.mp full.card.hr).le.trans hpP
  have hTwo : (2 : Real) ^ full.card.r ≤ (2 : Real) ^ P :=
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
    have hCpPos : 0 < Cp := by
      rw [← full.card_Cp]
      exact full.card.hCp
    positivity
  have hSep' : IsSeparated 1 full.card.W' := by
    intro x hx y hy hxy
    exact hSep x (full.card.hW' hx) y (full.card.hW' hy) hxy
  have hSymm' : ∀ t ∈ full.card.W', -R ≤ t ∧ t ≤ R := by
    intro t ht
    exact hSymm t (full.card.hW' ht)
  have hRaw := hMHH M B R V full.card.W'
    (sourceNormalizedFinitePoweredCoeffs N p a full.card.Cp eta)
    hM hB (hMleQ.trans hQleB) hV hRB hSep' hSymm'
    (by simpa only [M] using full.card.hUnit)
    (by simpa only [M, V, full.card_Cp] using full.card.hLarge)
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
  have hW' : (full.card.W'.card : Real) ≤
      Cmhh * B ^ epsilonMHH *
        (Q ^ 2 / V ^ 2 + B * Q ^ 4 / V ^ 6) :=
    hRaw.trans (mul_le_mul_of_nonneg_left hExpr hFactor)
  have hp0 : (0 : Real) ≤ p := by positivity
  simpa only [B, Q, V] using
    (calc
      (W.card : Real) ≤ p * (full.card.W'.card : Real) := full.card.hCard
      _ ≤ p * (Cmhh * B ^ epsilonMHH *
          (Q ^ 2 / V ^ 2 + B * Q ^ 4 / V ^ 6)) :=
        mul_le_mul_of_nonneg_left hW' hp0
      _ = p * Cmhh * B ^ epsilonMHH *
          (Q ^ 2 / V ^ 2 + B * Q ^ 4 / V ^ 6) := by ring)

#print axioms HeathBrownFullyUniformOutputs.card_le_mhh_common

end

end GafniTao
