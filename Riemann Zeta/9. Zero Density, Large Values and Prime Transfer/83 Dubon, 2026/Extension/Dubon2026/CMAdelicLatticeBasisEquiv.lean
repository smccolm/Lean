import Dubon2026.CMAdelicTraceActionFiniteInvariants

/-! # Recovering the original integral CM module from its action invariants

Equality of the actual integral action matrices forces the basis
equivalence to commute with the original scalar action. Equality on
the original integral basis of the CM field therefore gives full
ring-of-integers linearity. This is the first recovery step from the
finite joint invariants to DUB-17's original unitary double cosets.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix Module

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Equality of an original scalar-action matrix makes the actual integral basis equivalence commute with that scalar. -/
theorem cmAdelicLatticeBasisEquiv_scalar (H : Matrix ι ι K)
    (g h : cmFiniteAdelicUnitaryGroup K H)
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val))
    (c : Basis κ ℤ (numberFieldAdelicLattice K ι h.val)) (a : 𝓞 K)
    (ha : cmAdelicLatticeActionMatrix K H g b a = cmAdelicLatticeActionMatrix K H h c a)
    (x : numberFieldAdelicLattice K ι g.val) :
    b.equiv c (Equiv.refl κ) (a • x) = a • b.equiv c (Equiv.refl κ) x := by
  let e := b.equiv c (Equiv.refl κ)
  have hb (j : κ) : e (a • b j) = a • c j := by
    apply c.repr.injective
    ext i
    have he : c.repr (e (a • b j)) i = b.repr (a • b j) i := by
      simp [e, Basis.equiv]
    exact he.trans (congrArg (fun M : Matrix κ κ ℤ => M i j) ha)
  change e (a • x) = a • e x
  rw [← b.sum_repr x]
  simp only [Finset.smul_sum, smul_comm a, map_sum, map_zsmul, hb,
    e, Basis.equiv_apply, Equiv.refl_apply]

/-- Equality of the original integral-basis actions recovers all original ring-of-integers scalars. -/
theorem cmAdelicLatticeBasisEquiv_integralScalar (H : Matrix ι ι K)
    (g h : cmFiniteAdelicUnitaryGroup K H)
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val))
    (c : Basis κ ℤ (numberFieldAdelicLattice K ι h.val))
    (ha : cmAdelicLatticeIntegralActions K H g b = cmAdelicLatticeIntegralActions K H h c)
    (a : 𝓞 K) (x : numberFieldAdelicLattice K ι g.val) :
    b.equiv c (Equiv.refl κ) (a • x) = a • b.equiv c (Equiv.refl κ) x := by
  have hb (j : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :=
    cmAdelicLatticeBasisEquiv_scalar K H g h b c (RingOfIntegers.basis K j)
      (congrFun ha j) x
  rw [← (RingOfIntegers.basis K).sum_repr a]
  simp only [Finset.sum_smul, smul_assoc, map_sum, map_zsmul, hb]

end
end Dubon2026
