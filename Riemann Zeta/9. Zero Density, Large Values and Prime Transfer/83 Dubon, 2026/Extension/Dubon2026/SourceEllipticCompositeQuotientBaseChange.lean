import Dubon2026.SourceEllipticCompositeQuotientTransport

/-! The successive actual cyclic quotient commutes with field embeddings.
Strong induction uses the transported literal least-prime kernel, intrinsic
quotient curve, and actual image-subgroup equality. No higher-level
compatibility certificate is assumed. The all-level modular-polynomial
relation and inertia census on DUB-17/18 remain separate obligations. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticCyclicCount OddDiscriminant
open SourceFunctionField.IntegralJCoordinate
noncomputable section
variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
variable [IsAlgClosed F] [IsAlgClosed K]

/-- The literal composite cyclic quotient commutes with the original field embedding at every invertible level. -/
theorem cyclicQuotientCurve_map (f : F →+* K) (N : ℕ)
    (hNF : (N : F) ≠ 0)
    (W : WeierstrassCurve F) [W.IsElliptic]
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    let hNK : (N : K) ≠ 0 := by simpa only [map_natCast] using (_root_.map_ne_zero f).mpr hNF
    let H' := primeCyclicKernelMap f W N H
    (cyclicQuotientCurve N hNK (W.map f) H'.1 H'.2.1 H'.2.2).1 =
      (cyclicQuotientCurve N hNF W H.1 H.2.1 H.2.2).1.map f := by
  induction N using Nat.strong_induction_on generalizing W with
  | h N ih =>
    dsimp only
    have hNK : (N : K) ≠ 0 := by simpa only [map_natCast] using (_root_.map_ne_zero f).mpr hNF
    by_cases hN1 : N = 1
    · subst N
      rw [cyclicQuotientCurve_one, cyclicQuotientCurve_one]
    · have haF := cyclicQuotient_prime_arithmetic N hNF hN1
      have haK := cyclicQuotient_prime_arithmetic N hNK hN1
      letI : Fact N.minFac.Prime := ⟨haF.1⟩
      let H' := primeCyclicKernelMap f W N H
      let C := cyclicQuotientLeastKernel W N hNF hN1 H.1 H.2.1 H.2.2
      let C' := cyclicQuotientLeastKernel (W.map f) N hNK hN1 H'.1 H'.2.1 H'.2.2
      have hC : C' = primeCyclicKernelMap f W N.minFac C :=
        (cyclicQuotientLeastKernel_map f W N hNF hNK hN1 H.1 H.2.1 H.2.2).symm
      let V := primeAbscissaQuotient W N.minFac C
      let V' := primeAbscissaQuotient (W.map f) N.minFac C'
      letI : V.IsElliptic := primeAbscissaQuotient_isElliptic W N.minFac haF.2.2.2.1 C
      letI : V'.IsElliptic := primeAbscissaQuotient_isElliptic (W.map f) N.minFac haK.2.2.2.1 C'
      have hV : V' = V.map f := by
        dsimp only [V', V]
        rw [hC]
        exact primeAbscissaQuotient_map f W N.minFac C
      let e := AddEquiv.cast (M := fun E : WeierstrassCurve K => E.toAffine.Point) hV
      let J := H.1.map (primeAbscissaHom W N.minFac haF.2.2.2.1 C)
      let J' := H'.1.map (primeAbscissaHom (W.map f) N.minFac haK.2.2.2.1 C')
      have hsF := canonical_cyclic_prime_step W N.minFac (N / N.minFac) haF.2.2.2.1 haF.2.1
        H.1 H.2.1 (H.2.2.trans (Nat.mul_div_cancel' (Nat.minFac_dvd N)).symm)
      have hsK := canonical_cyclic_prime_step (W.map f) N.minFac (N / N.minFac) haK.2.2.2.1 haK.2.1
        H'.1 H'.2.1 (H'.2.2.trans (Nat.mul_div_cancel' (Nat.minFac_dvd N)).symm)
      letI : Finite H.1 := Nat.finite_of_card_ne_zero (by
        intro hz
        have he : N = 0 := H.2.2.symm.trans hz
        exact hNF (by rw [he, Nat.cast_zero]))
      have hJ : J.map (pointMapHom f V) = J'.map e.toAddMonoidHom := by
        have ht : ∀ (D : {D : AddSubgroup (W.map f).toAffine.Point //
            IsAddCyclic D ∧ Nat.card D = N.minFac})
            (hD : D = primeCyclicKernelMap f W N.minFac C)
            (hE : primeAbscissaQuotient (W.map f) N.minFac D = V.map f),
            J.map (pointMapHom f V) =
              (H'.1.map (primeAbscissaHom (W.map f) N.minFac haK.2.2.2.1 D)).map
                (AddEquiv.cast (M := fun E : WeierstrassCurve K => E.toAffine.Point) hE).toAddMonoidHom := by
          rintro D rfl hE
          exact primeAbscissaHom_image_map f W N.minFac haF.2.2.2.1 C H.1
        exact ht C' hC hV
      have hc := cyclicQuotientCurve_cast (N / N.minFac) haK.2.2.2.2 V' (V.map f) hV
        J' hsK.2.2.1 hsK.2.2.2.1
      dsimp only at hc
      have hsJ := isAddCyclic_map_and_card_of_injective (N / N.minFac)
        e.toAddMonoidHom e.injective ⟨hsK.2.2.1, hsK.2.2.2.1⟩
      have hInput : primeCyclicKernelMap f V (N / N.minFac) ⟨J, hsF.2.2.1, hsF.2.2.2.1⟩ =
          ⟨J'.map e.toAddMonoidHom, hsJ.1, hsJ.2.1⟩ := Subtype.ext hJ
      have heq := congrArg (fun A : {A : AddSubgroup (V.map f).toAffine.Point //
          IsAddCyclic A ∧ Nat.card A = N / N.minFac} =>
          (cyclicQuotientCurve (N / N.minFac) haK.2.2.2.2 (V.map f) A.1 A.2.1 A.2.2).1) hInput
      have hi := ih (N / N.minFac) haF.2.2.1 haF.2.2.2.2 V
        ⟨J, hsF.2.2.1, hsF.2.2.2.1⟩
      conv_lhs => rw [cyclicQuotientCurve]; simp only [dif_neg hN1]
      conv_rhs => rw [cyclicQuotientCurve]; simp only [dif_neg hN1]
      exact hc.symm.trans (heq.symm.trans hi)

end
end Dubon2026.SourceEllipticVelu
