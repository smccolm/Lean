import GafniTao.ClassicalBinaryHeathBrownFamily

/-!
# Frozen large-values consumers for long selected Type-I families

The Type-II and short Type-I alternatives enter the two-to-four power
window.  This module handles the complementary labelled Type-I family by
orienting it to positive ordinates and applying the actual frozen normalized
MHH theorem.  The result retains the literal detector threshold and harmonic
factor; later exponent bookkeeping must absorb them explicitly.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Exact normalized MHH estimate for a fixed detector colour in the Type-I
branch.  This theorem consumes the real binary detector family and the frozen
Type-I polynomial, not an independently supplied large-value set. -/
theorem classicalBinaryColorFamily_typeI_mhh_native :
    ∃ K : Real, 0 < K ∧
      ∀ {sigma U delta q0 : Real} {Y X A : Nat}
        (d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0)
        (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
        (r : Fin (d.kI * 2)),
        binaryScaleLabel label.1 = Sum.inl r →
        0 ≤ sigma → 2 ≤ U → 0 < q0 → U ^ delta ≤ U / 2 →
        let N := classicalTypeIShellScaleN Y r
        let V := ((3 / 4 : Real) * (q0 / 2)) / (d.kI : Real)
        0 < N →
        ((classicalBinaryColorFamily d label).card : Real) ≤
          K * (1 + (((harmonic N : Rat) : Real))) *
            ((N : Real) ^ 2 / ((N : Real) ^ sigma * V) ^ 2 +
              (3 * U) * min
                ((N : Real) / ((N : Real) ^ sigma * V) ^ 2)
                ((N : Real) ^ 4 / ((N : Real) ^ sigma * V) ^ 6)) := by
  obtain ⟨K, hK, hMHH⟩ :=
    actual_typeI_normalized_dichotomy_witness_mhh_native
  refine ⟨K, hK, ?_⟩
  intro sigma U delta q0 Y X A d label r hq hsigma hU hq0 hShift
  dsimp only
  intro hN
  let W := classicalBinaryColorFamily d label
  let Wpos := classicalBinaryOrientedFamily label.1 W
  have hkIProduct : 0 < d.kI * 2 := d.hkI
  have hkI : 0 < d.kI := by omega
  have hV : 0 < ((3 / 4 : Real) * (q0 / 2)) / (d.kI : Real) := by
    have hkIReal : (0 : Real) < d.kI := by exact_mod_cast hkI
    positivity
  have hSep : IsSeparated 1 Wpos :=
    isSeparated_classicalBinaryOrientedFamily label.1
      (classicalBinaryColorFamily_separated d label)
  have hBaseShell : ∀ t ∈ Wpos,
      U - U ^ delta ≤ t ∧ t ≤ 2 * U + U ^ delta := by
    simpa only [Wpos, W, classicalBinaryColorFamily] using
      classicalBinaryOrientedFamily_in_physical_interval d label
  have hLarge : ∀ t ∈ Wpos,
      ((3 / 4 : Real) * (q0 / 2)) / (d.kI : Real) ≤
        ‖dirichletPoly (classicalTypeIShellScaleN Y r)
          (classicalZetaLongLineCoeff A sigma) t‖ := by
    simpa only [Wpos, W] using
      classicalTypeIShellScaleLarge_on_orientedFamily
        label.1 r hq (classicalBinaryColorFamily d label)
          (classicalBinaryColorFamily_large d label)
  have hBound := hMHH A (classicalTypeIShellScaleN Y r)
    sigma delta U (((3 / 4 : Real) * (q0 / 2)) / (d.kI : Real))
    Wpos hsigma hN hU hV hShift hSep hBaseShell hLarge
  simpa only [Wpos, W, card_classicalBinaryOrientedFamily] using hBound

#print axioms classicalBinaryColorFamily_typeI_mhh_native

end

end GafniTao
