import GafniTao.HeathBrownUniformPowerConstants
import GafniTao.ClassicalBinaryHeathBrownPowered

/-!
# Powered cardinality packets with globally selected constants

This file constructs the existing packet interface from factorization and
mean-value constants selected before the physical parameters.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- A powered cardinality packet built from factorization and mean-value
constants already fixed outside all physical parameters. -/
theorem finite_symmetric_source_powered_cardinality_of_constants
    (Cp Cmv : Real)
    (hCp : 0 < Cp) (hCmv : 0 < Cmv)
    (hMean : ∀ (M : Nat) (B R V : Real) (W : Finset Real)
        (b : Nat → Complex),
      0 < M → 1 ≤ B → 0 < V → 2 * R ≤ B →
      IsSeparated 1 W →
      (∀ t, t ∈ W → -R ≤ t ∧ t ≤ R) →
      (∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, V ≤ ‖sourceDirichletPoly M b t‖) →
      (W.card : Real) ≤
        Cmv * ((M : Real) ^ 2 / V ^ 2 +
          B * (M : Real) / V ^ 2))
    (N p : Nat) (B R eta L : Real) (W : Finset Real)
    (a : Nat → Complex)
    (hN : 0 < N) (hp : 0 < p) (hB : 1 ≤ B)
    (hRB : 2 * R ≤ B) (heta : 0 < eta) (hL : 0 < L)
    (hSep : IsSeparated 1 W)
    (hSymm : ∀ t, t ∈ W → -R ≤ t ∧ t ≤ R)
    (hCoeff : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hPowAll : ∀ (N' : Nat) (a' : Nat → Complex),
      (∀ n ∈ dyadicInterval N', ‖a' n‖ ≤ 1) →
      ∀ m : Nat, 0 < m →
        ‖finitePowCoeff N' p a' m‖ ≤ Cp * (m : Real) ^ eta)
    (hLarge : ∀ t ∈ W, L ≤ ‖sourceDirichletPoly N a t‖) :
    ∃ packet : HeathBrownPoweredCardinalityPacket B R N p eta L W a,
      packet.Cp = Cp ∧ packet.Cmv = Cmv := by
  have hConjCoeff : ∀ n ∈ dyadicInterval N,
      ‖conjugateCoeffs a n‖ ≤ 1 := by
    intro n hn
    rw [norm_conjugateCoeffs]
    exact hCoeff n hn
  have hPow : ∀ m : Nat, 0 < m →
      ‖finitePowCoeff N p (conjugateCoeffs a) m‖ ≤
        Cp * (m : Real) ^ eta :=
    hPowAll N (conjugateCoeffs a) hConjCoeff
  obtain ⟨r, hr, W', hW', hCard, hUnit, hPowered⟩ :=
    exists_source_normalized_powered_block_of_bound
      N p a Cp eta L W hN hp hCp heta hL.le hCoeff hPow hLarge
  have hM : 0 < 2 ^ r * N ^ p :=
    Nat.mul_pos (pow_pos (by omega) r) (pow_pos hN p)
  have hV : 0 < heathBrownPoweredThreshold N p L Cp eta := by
    unfold heathBrownPoweredThreshold
    have hpR : (0 : Real) < p := by exact_mod_cast hp
    positivity
  have hSep' : IsSeparated 1 W' := by
    intro x hx y hy hxy
    exact hSep x (hW' hx) y (hW' hy) hxy
  have hSymm' : ∀ t, t ∈ W' → -R ≤ t ∧ t ≤ R := by
    intro t ht
    exact hSymm t (hW' ht)
  have hMean' := hMean (2 ^ r * N ^ p) B R
    (heathBrownPoweredThreshold N p L Cp eta) W'
    (sourceNormalizedFinitePoweredCoeffs N p a Cp eta)
    hM hB hV hRB hSep' hSymm' hUnit hPowered
  let packet : HeathBrownPoweredCardinalityPacket B R N p eta L W a :=
    ⟨Cp, Cmv, hCp, hCmv, r, hr, W', hW', hCard,
      hUnit, hPowered, hMean'⟩
  exact ⟨packet, rfl, rfl⟩

#print axioms finite_symmetric_source_powered_cardinality_of_constants

end

end GafniTao
