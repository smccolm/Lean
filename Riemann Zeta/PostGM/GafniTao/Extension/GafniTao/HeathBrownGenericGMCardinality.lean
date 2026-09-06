import GafniTao.HeathBrownGenericMHHCardinality
import RiemannZeta.GuthMaynard.LargeValuesFinal

/-!
# Guth--Maynard cardinality bound for a powered Heath--Brown packet

This is the symmetric-interval packet consumer needed in the high-energy
argument.  It applies the frozen native Guth--Maynard theorem to the actual
dyadic block selected by `HeathBrownPoweredCardinalityPacket`; translation
and phase twisting preserve both cardinality and coefficient norms.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

private noncomputable def restrictSourceCoeffs
    (M : Nat) (b : Nat -> Complex) (n : Nat) : Complex :=
  if n ∈ dyadicInterval M then b n else 0

private theorem norm_restrictSourceCoeffs_le_one
    {M : Nat} {b : Nat -> Complex}
    (hb : forall n, n ∈ dyadicInterval M -> ‖b n‖ <= 1) :
    forall n, ‖restrictSourceCoeffs M b n‖ <= 1 := by
  intro n
  by_cases hn : n ∈ dyadicInterval M
  · simpa [restrictSourceCoeffs, hn] using hb n hn
  · simp [restrictSourceCoeffs, hn]

private theorem sourceDirichletPoly_restrictSourceCoeffs
    (M : Nat) (b : Nat -> Complex) (t : Real) :
    sourceDirichletPoly M (restrictSourceCoeffs M b) t =
      sourceDirichletPoly M b t := by
  unfold sourceDirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  simp [restrictSourceCoeffs, hn]

/-- The frozen Guth--Maynard large-values theorem, transferred to a genuine
powered cardinality packet on a symmetric ordinate interval.  The output
uses the common upper scale `Q = 2^P N^p`; no coefficient or large-value
condition is supplied independently of the packet. -/
theorem exists_heathBrown_powered_cardinality_gm_common
    {epsilon U R eta L : Real} {N p P : Nat}
    {W : Finset Real} {a : Nat -> Complex}
    (hepsilon : 0 < epsilon) :
    exists C B0 : Real, 0 < C /\ 1 <= B0 /\
      forall
        (packet : HeathBrownPoweredCardinalityPacket
          ((2 ^ P : Real) * U) R N p eta L W a),
        1 <= U -> 0 < N -> 0 < p -> p <= P ->
        (N : Real) ^ p <= U -> 0 < L ->
        2 * R <= (2 ^ P : Real) * U ->
        IsSeparated 1 W ->
        (forall t, t ∈ W -> -R <= t /\ t <= R) ->
        B0 <= (2 ^ P : Real) * U ->
        let B := (2 ^ P : Real) * U
        let Q := ((2 ^ P : Nat) : Real) * (N ^ p : Nat)
        let V := heathBrownPoweredThreshold N p L packet.Cp eta
        (W.card : Real) <= p * C * B ^ epsilon *
          (Q ^ 2 * V ^ (-2 : Real) +
            Q ^ (18 / 5 : Real) * V ^ (-4 : Real) +
            B * Q ^ (12 / 5 : Real) * V ^ (-4 : Real)) := by
  obtain ⟨C, B0, hC, hB0, hGM⟩ :=
    guthMaynardLargeValues_native epsilon hepsilon
  refine ⟨C, B0, hC, hB0, ?_⟩
  intro packet hU hN hp hpP hNpU hL hRB hSep hSymm hB0B
  dsimp only
  let B : Real := (2 ^ P : Real) * U
  let M : Nat := 2 ^ packet.r * N ^ p
  let Q : Real := ((2 ^ P : Nat) : Real) * (N ^ p : Nat)
  let V : Real := heathBrownPoweredThreshold N p L packet.Cp eta
  let b : Nat -> Complex :=
    sourceNormalizedFinitePoweredCoeffs N p a packet.Cp eta
  let bT : Nat -> Complex := phaseShiftCoeffs R b
  let c : Nat -> Complex := restrictSourceCoeffs M bT
  let WT : Finset Real := gmTranslate R packet.W'
  have hB : 1 <= B := by
    have hTwo : (1 : Real) <= (2 : Real) ^ P := one_le_pow₀ (by norm_num)
    dsimp only [B]
    nlinarith [mul_le_mul hTwo hU (by norm_num : (0 : Real) <= 1)
      (by positivity : (0 : Real) <= (2 : Real) ^ P)]
  have hM : 0 < M := by
    dsimp only [M]
    exact Nat.mul_pos (pow_pos (by omega) _) (pow_pos hN _)
  have hrP : packet.r <= P :=
    (Finset.mem_range.mp packet.hr).le.trans hpP
  have hTwo : (2 : Real) ^ packet.r <= (2 : Real) ^ P :=
    pow_le_pow_right₀ (by norm_num) hrP
  have hMleQ : (M : Real) <= Q := by
    dsimp only [M, Q]
    push_cast
    exact mul_le_mul hTwo (le_refl ((N : Real) ^ p))
      (by positivity) (by positivity)
  have hQleB : Q <= B := by
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
    exact div_pos
      (div_pos (pow_pos hL p)
        (mul_pos packet.hCp (Real.rpow_pos_of_pos hBaseReal eta))) hpR
  have hSepW' : IsSeparated 1 packet.W' := by
    intro x hx y hy hxy
    exact hSep x (packet.hW' hx) y (packet.hW' hy) hxy
  have hSymmW' : forall t, t ∈ packet.W' -> -R <= t /\ t <= R := by
    intro t ht
    exact hSymm t (packet.hW' ht)
  have hSepT : IsSeparated 1 WT :=
    isSeparated_gmTranslate 1 R packet.W' hSepW'
  have hBaseT : InBaseInterval B WT := by
    have hSmall := inBaseInterval_gmTranslate_of_symmetric R packet.W' hSymmW'
    intro t ht
    obtain ⟨ht0, htUpper⟩ := hSmall t ht
    exact ⟨ht0, htUpper.trans hRB⟩
  have hUnitT : forall n, n ∈ dyadicInterval M -> ‖bT n‖ <= 1 := by
    intro n hn
    rw [show ‖bT n‖ = ‖b n‖ by
      dsimp only [bT]
      exact norm_phaseShiftCoeffs R b n]
    simpa only [b, M] using packet.hUnit n hn
  have hUnit : forall n, ‖c n‖ <= 1 := by
    exact norm_restrictSourceCoeffs_le_one hUnitT
  have hLargeT : forall t, t ∈ WT ->
      V <= ‖sourceDirichletPoly M bT t‖ := by
    exact sourceDirichletPoly_large_on_gmTranslate M b R V packet.W'
      (by simpa only [b, M, V] using packet.hLarge)
  have hLargeC : forall t, t ∈ WT ->
      V <= ‖sourceDirichletPoly M c t‖ := by
    intro t ht
    rw [sourceDirichletPoly_restrictSourceCoeffs]
    exact hLargeT t ht
  have hRaw := hGM M V B c WT hM hB0B hV hUnit hSepT hBaseT hLargeC
  have h2 : (M : Real) ^ 2 * V ^ (-2 : Real) <=
      Q ^ 2 * V ^ (-2 : Real) := by
    gcongr
  have h18 : (M : Real) ^ (18 / 5 : Real) * V ^ (-4 : Real) <=
      Q ^ (18 / 5 : Real) * V ^ (-4 : Real) := by
    gcongr
  have h12 : B * (M : Real) ^ (12 / 5 : Real) * V ^ (-4 : Real) <=
      B * Q ^ (12 / 5 : Real) * V ^ (-4 : Real) := by
    gcongr
  have hShape :
      (M : Real) ^ 2 * V ^ (-2 : Real) +
          (M : Real) ^ (18 / 5 : Real) * V ^ (-4 : Real) +
          B * (M : Real) ^ (12 / 5 : Real) * V ^ (-4 : Real) <=
        Q ^ 2 * V ^ (-2 : Real) +
          Q ^ (18 / 5 : Real) * V ^ (-4 : Real) +
          B * Q ^ (12 / 5 : Real) * V ^ (-4 : Real) := by
    linarith
  have hCardW' : (packet.W'.card : Real) <= C * B ^ epsilon *
      (Q ^ 2 * V ^ (-2 : Real) +
        Q ^ (18 / 5 : Real) * V ^ (-4 : Real) +
        B * Q ^ (12 / 5 : Real) * V ^ (-4 : Real)) := by
    rw [show (packet.W'.card : Real) = (WT.card : Real) by
      simp only [WT, card_gmTranslate]]
    exact hRaw.trans (mul_le_mul_of_nonneg_left hShape (by positivity))
  calc
    (W.card : Real) <= p * (packet.W'.card : Real) := packet.hCard
    _ <= p * (C * B ^ epsilon *
        (Q ^ 2 * V ^ (-2 : Real) +
          Q ^ (18 / 5 : Real) * V ^ (-4 : Real) +
          B * Q ^ (12 / 5 : Real) * V ^ (-4 : Real))) := by
      gcongr
    _ = p * C * B ^ epsilon *
        (Q ^ 2 * V ^ (-2 : Real) +
          Q ^ (18 / 5 : Real) * V ^ (-4 : Real) +
          B * Q ^ (12 / 5 : Real) * V ^ (-4 : Real)) := by ring

#print axioms exists_heathBrown_powered_cardinality_gm_common

end

end GafniTao
