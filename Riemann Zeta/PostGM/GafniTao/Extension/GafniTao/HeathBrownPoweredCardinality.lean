import GafniTao.HeathBrownPoweredEnergy
import GafniTao.EnergyDetectorTranslation
import RiemannZeta.GuthMaynard.ClassicalLargeValues

/-!
# Powered cardinality input for the Heath--Brown argument

The low and middle zero-energy cells use two powers of the same detector.
The `p`-th power supplies the fourth-energy estimate, while the `(p+1)`-st
power supplies an ordinary large-values cardinality bound.  This file proves
the latter finite statement with the source positive-sign convention and the
symmetric ordinate interval used by the zero shells.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Symmetric-interval, positive-sign form of the unrestricted classical
mean-value large-values bound.  Translation, phase twisting, sign conversion,
and cardinality preservation are all performed in this theorem. -/
theorem finite_symmetric_source_cardinality_meanValue_native :
    exists Cmv : Real, 0 < Cmv ∧
      forall (M : Nat) (B R V : Real) (W : Finset Real) (b : Nat → Complex),
        0 < M → 1 ≤ B → 0 < V → 2 * R ≤ B →
        IsSeparated 1 W →
        (forall t, t ∈ W → -R ≤ t ∧ t ≤ R) →
        (∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) →
        (∀ t ∈ W, V ≤ ‖sourceDirichletPoly M b t‖) →
        (W.card : Real) ≤
          Cmv * ((M : Real) ^ 2 / V ^ 2 +
            B * (M : Real) / V ^ 2) := by
  obtain ⟨Cmv, hCmv, hMean⟩ :=
    classical_large_values_second_branch_unrestricted
  refine ⟨Cmv, hCmv, ?_⟩
  intro M B R V W b hM hB hV hRB hSep hSymm hCoeff hLarge
  let WT := gmTranslate R W
  let bT := phaseShiftCoeffs R b
  let c := conjugateCoeffs bT
  have hSepT : IsSeparated 1 WT :=
    isSeparated_gmTranslate 1 R W hSep
  have hBaseT : InBaseInterval B WT := by
    have hSmall := inBaseInterval_gmTranslate_of_symmetric R W hSymm
    intro t ht
    obtain ⟨ht0, htUpper⟩ := hSmall t ht
    exact ⟨ht0, htUpper.trans hRB⟩
  have hCoeffT : ∀ n ∈ dyadicInterval M, ‖c n‖ ≤ 1 := by
    intro n hn
    change ‖conjugateCoeffs bT n‖ ≤ 1
    rw [norm_conjugateCoeffs]
    exact norm_phaseShiftCoeffs_le_one_on M b R hCoeff n hn
  have hSourceLarge : ∀ t ∈ WT,
      V ≤ ‖sourceDirichletPoly M bT t‖ := by
    exact sourceDirichletPoly_large_on_gmTranslate M b R V W hLarge
  have hNegativeLarge : ∀ t ∈ WT,
      V ≤ ‖dirichletPoly M c t‖ := by
    intro t ht
    have hcc : conjugateCoeffs c = bT := by
      funext n
      simp only [c, conjugateCoeffs, star_star]
    have hSign := norm_sourceDirichletPoly_conjugateCoeffs M c t
    rw [hcc] at hSign
    rw [← hSign]
    exact hSourceLarge t ht
  have hBound := hMean M B V WT c hM hB hV hCoeffT hSepT hBaseT
    hNegativeLarge
  simpa only [WT, card_gmTranslate] using hBound

/-- Exact `(p+1)`-power companion to the powered Heath--Brown energy bound.
It selects one common powered dyadic block, retains the finite colouring loss,
and applies the genuine classical mean-value theorem to that block. -/
theorem finite_symmetric_source_powered_cardinality_meanValue_native
    (N p : Nat) (B R eta L : Real) (W : Finset Real) (a : Nat → Complex)
    (hN : 0 < N) (hp : 0 < p) (hB : 1 ≤ B) (hRB : 2 * R ≤ B)
    (heta : 0 < eta) (hL : 0 < L)
    (hSep : IsSeparated 1 W)
    (hSymm : forall t, t ∈ W → -R ≤ t ∧ t ≤ R)
    (hCoeff : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hLarge : ∀ t ∈ W, L ≤ ‖sourceDirichletPoly N a t‖) :
    exists Cp Cmv : Real, 0 < Cp ∧ 0 < Cmv ∧
      ∃ r ∈ Finset.range p, ∃ W' ⊆ W,
        (W.card : Real) ≤ p * (W'.card : Real) ∧
        (∀ n ∈ dyadicInterval (2 ^ r * N ^ p),
          ‖sourceNormalizedFinitePoweredCoeffs N p a Cp eta n‖ ≤ 1) ∧
        (∀ t ∈ W',
          heathBrownPoweredThreshold N p L Cp eta ≤
            ‖sourceDirichletPoly (2 ^ r * N ^ p)
              (sourceNormalizedFinitePoweredCoeffs N p a Cp eta) t‖) ∧
        (W'.card : Real) ≤
          Cmv * (((2 ^ r * N ^ p : Nat) : Real) ^ 2 /
              (heathBrownPoweredThreshold N p L Cp eta) ^ 2 +
            B * ((2 ^ r * N ^ p : Nat) : Real) /
              (heathBrownPoweredThreshold N p L Cp eta) ^ 2) := by
  obtain ⟨Cmv, hCmv, hMean⟩ :=
    finite_symmetric_source_cardinality_meanValue_native
  obtain ⟨Cp, hCp, r, hr, W', hW', hCard, hUnit, hPowered⟩ :=
    exists_source_normalized_powered_block N p a eta L W
      hN hp heta hL.le hCoeff hLarge
  refine ⟨Cp, Cmv, hCp, hCmv, r, hr, W', hW', hCard, hUnit, hPowered, ?_⟩
  have hM : 0 < 2 ^ r * N ^ p :=
    Nat.mul_pos (pow_pos (by omega) r) (pow_pos hN p)
  have hV : 0 < heathBrownPoweredThreshold N p L Cp eta := by
    unfold heathBrownPoweredThreshold
    have hpReal : (0 : Real) < p := by exact_mod_cast hp
    positivity
  have hSep' : IsSeparated 1 W' := by
    intro x hx y hy hxy
    exact hSep x (hW' hx) y (hW' hy) hxy
  have hSymm' : forall t, t ∈ W' → -R ≤ t ∧ t ≤ R := by
    intro t ht
    exact hSymm t (hW' ht)
  exact hMean (2 ^ r * N ^ p) B R
    (heathBrownPoweredThreshold N p L Cp eta) W'
    (sourceNormalizedFinitePoweredCoeffs N p a Cp eta)
    hM hB hV hRB hSep' hSymm' hUnit hPowered

#print axioms finite_symmetric_source_cardinality_meanValue_native
#print axioms finite_symmetric_source_powered_cardinality_meanValue_native

end

end GafniTao
