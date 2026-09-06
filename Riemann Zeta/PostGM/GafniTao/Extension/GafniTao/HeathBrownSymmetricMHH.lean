import GafniTao.HeathBrownPoweredCardinality

/-!
# Symmetric source form of Montgomery--Halász--Huxley

The frozen theorem is stated for negative-sign Dirichlet polynomials on a
positive ordinate interval.  Heath--Brown's powered zero detector is a
positive-sign polynomial on a symmetric interval.  This file proves the
literal translation, phase-twist, conjugation, and cardinality bridge once,
without changing either source object.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Symmetric-interval, positive-sign form of the frozen finite
Montgomery--Halász--Huxley theorem.  The constant is chosen before every
physical parameter. -/
theorem finite_symmetric_source_cardinality_mhh_native
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ Cmhh : Real, 0 < Cmhh ∧
      ∀ (M : Nat) (B R V : Real) (W : Finset Real)
          (b : Nat → Complex),
        0 < M → 1 ≤ B → (M : Real) ≤ B → 0 < V → 2 * R ≤ B →
        IsSeparated 1 W →
        (∀ t ∈ W, -R ≤ t ∧ t ≤ R) →
        (∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) →
        (∀ t ∈ W, V ≤ ‖sourceDirichletPoly M b t‖) →
        (W.card : Real) ≤
          Cmhh * B ^ epsilon *
            ((M : Real) ^ 2 / V ^ 2 +
              B * min ((M : Real) / V ^ 2)
                ((M : Real) ^ 4 / V ^ 6)) := by
  obtain ⟨Cmhh, hCmhh, hMHH⟩ :=
    classical_montgomery_halasz_huxley_native epsilon hepsilon
  refine ⟨Cmhh, hCmhh, ?_⟩
  intro M B R V W b hM hB hMB hV hRB hSep hSymm hCoeff hLarge
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
      V ≤ ‖sourceDirichletPoly M bT t‖ :=
    sourceDirichletPoly_large_on_gmTranslate M b R V W hLarge
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
  have hBound := hMHH M B V WT c hM hB hMB hV hCoeffT hSepT
    hBaseT hNegativeLarge
  simpa only [WT, card_gmTranslate] using hBound

#print axioms finite_symmetric_source_cardinality_mhh_native

end

end GafniTao
