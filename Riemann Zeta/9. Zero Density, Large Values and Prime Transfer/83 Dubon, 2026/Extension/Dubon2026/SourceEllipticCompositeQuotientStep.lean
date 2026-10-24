import Dubon2026.SourceEllipticCompositeQuotientJ

/-! The actual composite quotient can take any contained subgroup of its
least-prime order as its first step. Uniqueness of that prime torsion kernel
identifies it with the literal recursive construction. The image cyclicity
and order proofs only type the already constructed quotient and are supplied
by the existing exact-kernel image theorem in the counting application. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticCyclicCount
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

/-- Every contained least-prime kernel gives the same actual recursive quotient value. -/
theorem cyclicQuotientJ_step
    (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ) (hN : (N : F) ≠ 0) (hN1 : N ≠ 1)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    let ha := cyclicQuotient_prime_arithmetic N hN hN1
    letI : Fact N.minFac.Prime := ⟨ha.1⟩
    ∀ (D : {D : AddSubgroup W.toAffine.Point // IsAddCyclic D ∧ Nat.card D = N.minFac})
      (_hDH : D.1 ≤ H.1),
    let V := primeAbscissaQuotient W N.minFac D
    letI : V.IsElliptic := primeAbscissaQuotient_isElliptic W N.minFac ha.2.2.2.1 D
    let J := H.1.map (primeAbscissaHom W N.minFac ha.2.2.2.1 D)
    ∀ (hcyc : IsAddCyclic J) (hcard : Nat.card J = N / N.minFac),
      cyclicQuotientJ W N hN H = cyclicQuotientJ V (N / N.minFac) ha.2.2.2.2 ⟨J, hcyc, hcard⟩ := by
  intro ha D hDH V J hcyc hcard
  letI : Fact N.minFac.Prime := ⟨ha.1⟩
  letI : IsAddCyclic H.1 := H.2.1
  letI : Finite H.1 := Nat.finite_of_card_ne_zero (by
    intro hz
    have he : N = 0 := H.2.2.symm.trans hz
    exact hN (by rw [he, Nat.cast_zero]))
  have hD : D = cyclicQuotientLeastKernel W N hN hN1 H.1 H.2.1 H.2.2 := by
    apply Subtype.ext
    exact (cyclicPrimeKernel_eq_of_card H.1 ha.1.pos hDH D.2.2).symm
  subst D
  letI : V.IsElliptic := primeAbscissaQuotient_isElliptic W N.minFac ha.2.2.2.1 _
  have he : cyclicQuotientCurve N hN W H.1 H.2.1 H.2.2 =
      cyclicQuotientCurve (N / N.minFac) ha.2.2.2.2 V J hcyc hcard := by
    conv_lhs => rw [cyclicQuotientCurve]; simp only [dif_neg hN1]
  exact congrArg (fun E : {E : WeierstrassCurve F // E.IsElliptic} =>
    letI := E.2
    E.1.j) he

end
end Dubon2026.SourceEllipticVelu
