import Dubon2026.SourceEllipticPrimeImageVariableChange
import Dubon2026.SourceEllipticCanonicalKernelVariableChange

/-! All successive actual cyclic quotient curves respect the original
Weierstrass coordinate change. The induction consumes the exact transported
least-prime kernel and actual image-subgroup equality, not an assumed
quotient compatibility. This removes the model-transport obstacle for the
all-level cyclic-root bijection in the DUB-17/18 inertia census. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticCyclicCount SourceEllipticVariableChange
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

/-- The actual composite cyclic quotient transforms under the original coordinate change at every invertible level. -/
theorem cyclicQuotientCurve_variableChange (C : VariableChange F) (N : ℕ)
    (hN : (N : F) ≠ 0) (W : WeierstrassCurve F) [W.IsElliptic]
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    let H' := cyclicKernelVariableChange C W N H
    (cyclicQuotientCurve N hN (C • W) H'.1 H'.2.1 H'.2.2).1 =
      C • (cyclicQuotientCurve N hN W H.1 H.2.1 H.2.2).1 := by
  induction N using Nat.strong_induction_on generalizing W with
  | h N ih =>
    dsimp only
    by_cases hN1 : N = 1
    · subst N
      rw [cyclicQuotientCurve_one, cyclicQuotientCurve_one]
    · have ha := cyclicQuotient_prime_arithmetic N hN hN1
      letI : Fact N.minFac.Prime := ⟨ha.1⟩
      let H' := cyclicKernelVariableChange C W N H
      let D := cyclicQuotientLeastKernel W N hN hN1 H.1 H.2.1 H.2.2
      let D' := cyclicQuotientLeastKernel (C • W) N hN hN1 H'.1 H'.2.1 H'.2.2
      have hD : D' = cyclicKernelVariableChange C W N.minFac D :=
        (cyclicQuotientLeastKernel_variableChange C W N hN hN1 H.1 H.2.1 H.2.2).symm
      let V := primeAbscissaQuotient W N.minFac D
      let V' := primeAbscissaQuotient (C • W) N.minFac D'
      letI : V.IsElliptic := primeAbscissaQuotient_isElliptic W N.minFac ha.2.2.2.1 D
      letI : V'.IsElliptic := primeAbscissaQuotient_isElliptic (C • W) N.minFac ha.2.2.2.1 D'
      have hV : V' = C • V := by
        dsimp only [V', V]
        rw [hD]
        exact primeAbscissaQuotient_variableChange C W N.minFac ha.2.2.2.1 D
      let e := AddEquiv.cast (M := fun E : WeierstrassCurve F => E.toAffine.Point) hV
      let v := (variableChangeAddEquiv C V.toAffine).symm
      let J := H.1.map (primeAbscissaHom W N.minFac ha.2.2.2.1 D)
      let J' := H'.1.map (primeAbscissaHom (C • W) N.minFac ha.2.2.2.1 D')
      have hs := canonical_cyclic_prime_step W N.minFac (N / N.minFac) ha.2.2.2.1 ha.2.1
        H.1 H.2.1 (H.2.2.trans (Nat.mul_div_cancel' (Nat.minFac_dvd N)).symm)
      have hs' := canonical_cyclic_prime_step (C • W) N.minFac (N / N.minFac) ha.2.2.2.1 ha.2.1
        H'.1 H'.2.1 (H'.2.2.trans (Nat.mul_div_cancel' (Nat.minFac_dvd N)).symm)
      letI : Finite H.1 := Nat.finite_of_card_ne_zero (by
        intro hz
        have he : N = 0 := H.2.2.symm.trans hz
        exact hN (by rw [he, Nat.cast_zero]))
      have hJ : J.map v.toAddMonoidHom = J'.map e.toAddMonoidHom := by
        have ht : ∀ (A : {A : AddSubgroup (C • W).toAffine.Point //
            IsAddCyclic A ∧ Nat.card A = N.minFac})
            (hA : A = cyclicKernelVariableChange C W N.minFac D)
            (hE : primeAbscissaQuotient (C • W) N.minFac A = C • V),
            J.map v.toAddMonoidHom =
              (H'.1.map (primeAbscissaHom (C • W) N.minFac ha.2.2.2.1 A)).map
                (AddEquiv.cast (M := fun E : WeierstrassCurve F => E.toAffine.Point) hE).toAddMonoidHom := by
          rintro A rfl hE
          exact primeAbscissaHom_image_variableChange C W N.minFac ha.2.2.2.1 D H.1
        exact ht D' hD hV
      have hc := cyclicQuotientCurve_cast (N / N.minFac) ha.2.2.2.2 V' (C • V) hV
        J' hs'.2.2.1 hs'.2.2.2.1
      dsimp only at hc
      have hsJ := isAddCyclic_map_and_card_of_injective (N / N.minFac)
        e.toAddMonoidHom e.injective ⟨hs'.2.2.1, hs'.2.2.2.1⟩
      have hInput : cyclicKernelVariableChange C V (N / N.minFac) ⟨J, hs.2.2.1, hs.2.2.2.1⟩ =
          ⟨J'.map e.toAddMonoidHom, hsJ.1, hsJ.2.1⟩ := Subtype.ext hJ
      have heq := congrArg (fun A : {A : AddSubgroup (C • V).toAffine.Point //
          IsAddCyclic A ∧ Nat.card A = N / N.minFac} =>
          (cyclicQuotientCurve (N / N.minFac) ha.2.2.2.2 (C • V) A.1 A.2.1 A.2.2).1) hInput
      have hi := ih (N / N.minFac) ha.2.2.1 ha.2.2.2.2 V
        ⟨J, hs.2.2.1, hs.2.2.2.1⟩
      conv_lhs => rw [cyclicQuotientCurve]; simp only [dif_neg hN1]
      conv_rhs => rw [cyclicQuotientCurve]; simp only [dif_neg hN1]
      exact hc.symm.trans (heq.symm.trans hi)

end
end Dubon2026.SourceEllipticVelu
