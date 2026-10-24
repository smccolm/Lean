import Dubon2026.SourceEllipticAbscissaQuotientX
import Dubon2026.SourceEllipticCanonicalPrimeHom
import Dubon2026.SourceEllipticCyclicAbscissaBaseChange

/-! The specific prime quotient homomorphism has the intrinsic abscissa
formula away from its exact kernel. The formula commutes with field maps.
This is the input for comparing actual image subgroups in the composite
cyclic quotient construction needed by the DUB-17/18 inertia census. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticFunctionField OddDiscriminant
open SourceFunctionField.IntegralJCoordinate
noncomputable section
variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]

/-- The intrinsic x-coordinate formula for the actual prime quotient. -/
def primeAbscissaQuotientX (W : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime]
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) (x : F) : F :=
  letI : Finite H.1 := Nat.finite_of_card_ne_zero (H.2.2.symm ▸ hp.out.ne_zero)
  if p = 2 then twoAbscissaQuotientX W (cyclicAbscissae W H.1) x
  else abscissaQuotientX W (cyclicAbscissae W H.1) x

/-- The intrinsic prime x-coordinate formula specializes under the original field map. -/
theorem primeAbscissaQuotientX_map (f : F →+* K) (W : WeierstrassCurve F)
    (p : ℕ) [hp : Fact p.Prime]
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) (x : F) :
    primeAbscissaQuotientX (W.map f) p (primeCyclicKernelMap f W p H) (f x) =
      f (primeAbscissaQuotientX W p H x) := by
  letI : Finite H.1 := Nat.finite_of_card_ne_zero (H.2.2.symm ▸ hp.out.ne_zero)
  have he := cyclicAbscissae_map f W H.1
  simp only [primeAbscissaQuotientX, primeCyclicKernelMap]
  split_ifs with hp2
  · rw [he]
    exact twoAbscissaQuotientX_map f W _ x
  · rw [he]
    exact abscissaQuotientX_map f W _ x

/-- The specific prime quotient map has the intrinsic abscissa formula off its original kernel. -/
theorem primeAbscissaHom_x [IsAlgClosed F]
    (W : WeierstrassCurve F) [W.IsElliptic] (p : ℕ) [hprime : Fact p.Prime]
    (hp : (p : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p})
    (R : W.toAffine.Point) (hRH : R ∉ H.1) :
    (coordsOrZero (primeAbscissaHom W p hp H R)).1 =
      primeAbscissaQuotientX W p H (coordsOrZero R).1 := by
  letI : Finite H.1 := Nat.finite_of_card_ne_zero (H.2.2.symm ▸ hprime.out.ne_zero)
  cases R with
  | zero => exact (hRH H.1.zero_mem).elim
  | some x y h =>
    by_cases hp2 : p = 2
    · subst p
      let P := primeKernelGenerator W 2 H
      have hP : addOrderOf P = 2 := primeKernelGenerator_order W 2 H
      have hPH : AddSubgroup.zmultiples P = H.1 := primeKernelGenerator_zmultiples W 2 H
      have hP0 : P ≠ 0 := by intro hz; rw [hz, addOrderOf_zero] at hP; omega
      have hx : x ≠ (coordsOrZero P).1 := by
        intro he
        have hmem : P ∈ H.1 := hPH ▸ AddSubgroup.mem_zmultiples P
        rcases eq_or_eq_neg_of_xco_eq (Affine.Point.some_ne_zero h) hP0 he with hr | hr
        · exact hRH (hr ▸ hmem)
        · apply hRH
          rw [hr]
          exact H.1.neg_mem hmem
      simp only [primeAbscissaHom, dite_true, AddMonoidHom.comp_apply,
        AddEquiv.coe_toAddMonoidHom, coordsOrZero_cast,
        primeAbscissaQuotientX, ite_true]
      rw [veluTwoHom_coe, veluPointMap2_some_of_ne _ _ _ h hx]
      exact (twoAbscissaQuotientX_eq W hp H.1 hP hPH x).symm
    · let hP := primeKernelGenerator_oddOrder W p hp2 H
      have hd : (OddDiscriminant.Algebra.hP
          (oddOrderSummingSet W (primeKernelGenerator W p H) (p / 2)) Prod.fst).eval x ≠ 0 := by
        intro hz
        apply hRH
        rw [← primeKernelGenerator_zmultiples W p H]
        exact (eval_oddKernel_eq_zero_iff_mem_zmultiples W h hP).mp hz
      simp only [primeAbscissaHom, dif_neg hp2, AddMonoidHom.comp_apply,
        AddEquiv.coe_toAddMonoidHom, coordsOrZero_cast,
        primeAbscissaQuotientX, if_neg hp2]
      rw [oddPointNorm_some W h hP hd]
      exact (abscissaQuotientX_oddOrderSummingSet W H.1 hP
        (primeKernelGenerator_zmultiples W p H) x).symm

end
end Dubon2026.SourceEllipticVelu
