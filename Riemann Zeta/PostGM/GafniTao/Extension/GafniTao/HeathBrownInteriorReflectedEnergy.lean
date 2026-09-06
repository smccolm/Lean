import GafniTao.ReflectedWideEnergyOutput
import RiemannZeta.GuthMaynard.MediumTypeIEndpoint

/-!
# Energy-preserving entry into the frozen Type-I Poisson reflection

This is the missing source-entry bridge for an interior Type-I family.  It
consumes the actual frozen reflection theorem, retains its literal dual
cutoff and threshold, colours all four energy coordinates by reflection
sign, and performs the simultaneous dyadic extraction.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The actual interior Type-I source family feeds the exact reflected-wide
energy output.  No independently supplied reflected family or large-value
hypothesis occurs in the conclusion. -/
theorem eventually_interior_source_family_reflected_energy
    {sigma d u : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma < 1) (hd : 0 < d) (hdOne : d ≤ 1)
    (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (hu : 0 ≤ u) (huD : u ≤ d) :
    ∃ T₀ : Real, 8 ≤ T₀ ∧
      ∀ {T tau : Real} {Y A r : Nat} (W : Finset Real), T₀ ≤ T →
        A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
        (((Y + 1 : Nat) : Real) ≤ (((2 ^ r * Y : Nat) : Real) / 2)) →
        2 * (2 ^ r * Y) ≤ A →
        tau = typeILogarithmicScale T (2 ^ r * Y) →
        1 < tau → tau < 2 → W.Nonempty → IsSeparated 1 W →
        (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
        (∀ t ∈ W,
          ((3 / 4) * (T ^ (-u) / 2)) /
              (Nat.clog 2 A + 1 : Nat) ≤
            ‖typeISourceSmoothBlock Y A r sigma t‖) →
        let Q := 2 ^ r * Y
        let M := mediumTypeIDualCutoff T d Q
        let V := ((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 A + 1 : Nat)
        let Rdet := (Real.pi * V) /
          (8 * (Q : Real) * mediumTypeIStationaryKernel sigma T Q *
            (typeIDyadicCutoffMellinL1 + 1))
        let S := Rdet / (2 * (M : Real) ^ sigma)
        1 < M ∧ Nonempty (ReflectedWideEnergyOutput W (T ^ d) S (3 * T)
          (Nat.clog 2 M) (normalizedTypeIReflectedCoeff sigma M)) := by
  have hdStrict : d < 1 := by
    have hSigmaGap : 0 < sigma - 1 / 2 := by linarith
    nlinarith [hdGap]
  obtain ⟨Treflect, hTreflect, hReflect⟩ :=
    eventually_interior_source_family_reflects hsigma hsigmaUpper hd hdOne
      hdGap hu huD
  obtain ⟨Tdisp, hTdisp, hDisp⟩ := eventually_rpow_le_half_self d hdStrict
  let T₀ := max Treflect Tdisp
  refine ⟨T₀, hTreflect.trans (le_max_left _ _), ?_⟩
  intro T tau Y A r W hT hA hY hr hLower hUpper hTau hTauOne hTauTwo
    hW hSep hRange hLarge
  dsimp only
  have hTReflect : Treflect ≤ T := (le_max_left _ _).trans hT
  have hTDisp : Tdisp ≤ T := (le_max_right _ _).trans hT
  have hTOne : 1 ≤ T := hTreflect.trans hTReflect |>.trans' (by norm_num)
  have hHalf : T ^ d ≤ T / 2 := hDisp T hTDisp
  have hRaw := hReflect W hTReflect hA hY hr hLower hUpper hTau
    hTauOne hTauTwo hRange hLarge hW
  let Q : Nat := 2 ^ r * Y
  let M : Nat := mediumTypeIDualCutoff T d Q
  let V : Real := ((3 / 4) * (T ^ (-u) / 2)) /
    (Nat.clog 2 A + 1 : Nat)
  let Rdet : Real := (Real.pi * V) /
    (8 * (Q : Real) * mediumTypeIStationaryKernel sigma T Q *
      (typeIDyadicCutoffMellinL1 + 1))
  let S : Real := Rdet / (2 * (M : Real) ^ sigma)
  have hM : 1 < M := by simpa only [Q, M] using hRaw.1
  have hk : 0 < Nat.clog 2 M := Nat.clog_pos Nat.one_lt_two hM
  let negative : Real → Prop := fun t ↦
    ∃ v ∈ Set.Icc (-(T ^ d)) (T ^ d),
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-(t + v))‖
  let positive : Real → Prop := fun t ↦
    ∃ v ∈ Set.Icc (-(T ^ d)) (T ^ d),
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (t - v)‖
  have hAlternative : ∀ t, t ∈ W → negative t ∨ positive t := by
    intro t ht
    simpa only [negative, positive, Q, M, V, Rdet, S] using hRaw.2 t ht
  have hNegative : ∀ t, t ∈ W → negative t →
      ∃ s : Real, |(-t) - s| ≤ T ^ d ∧
        (-(3 * T) ≤ s ∧ s ≤ 3 * T) ∧
        S ≤ ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) s‖ := by
    intro t ht hneg
    obtain ⟨v, hv, hlarge⟩ := hneg
    have hvBounds : -(T ^ d) ≤ v ∧ v ≤ T ^ d := hv
    refine ⟨-(t + v), ?_, ?_, hlarge.le⟩
    · rw [show (-t) - (-(t + v)) = v by ring]
      exact abs_le.mpr hv
    · have htRange := hRange t ht
      constructor <;> nlinarith
  have hPositive : ∀ t, t ∈ W → positive t →
      ∃ s : Real, |t - s| ≤ T ^ d ∧
        (-(3 * T) ≤ s ∧ s ≤ 3 * T) ∧
        S ≤ ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) s‖ := by
    intro t ht hpos
    obtain ⟨v, hv, hlarge⟩ := hpos
    have hvBounds : -(T ^ d) ≤ v ∧ v ≤ T ^ d := hv
    refine ⟨t - v, ?_, ?_, hlarge.le⟩
    · rw [show t - (t - v) = v by ring]
      exact abs_le.mpr hv
    · have htRange := hRange t ht
      constructor <;> nlinarith
  refine ⟨hM, ?_⟩
  simpa only [Q, M, V, Rdet, S] using
    (reflected_wide_energy_to_dyadic_self W hSep (T ^ d) S (3 * T)
      (Nat.clog 2 M) hk (normalizedTypeIReflectedCoeff sigma M)
      negative positive hAlternative hNegative hPositive)

#print axioms eventually_interior_source_family_reflected_energy

end

end GafniTao
