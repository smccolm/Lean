import Dubon2026.CMAdelicLatticeBasisEquiv
import Dubon2026.NumberFieldAdelicLatticeBasisEquiv

/-! # The original CM-linear equivalence recovered from equal action invariants

The original rational lattice equivalence commutes with all integral
scalars and hence, by the original rational integral basis, with every
CM-field scalar. This recovers a linear equivalence over the original
field, a required step in DUB-17's unitary double-coset recovery.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix Module

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Equality of integral action invariants makes the original rational equivalence commute with every integral scalar. -/
theorem cmAdelicLatticeRationalEquiv_integralScalar (H : Matrix ι ι K)
    (g h : cmFiniteAdelicUnitaryGroup K H)
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val))
    (c : Basis κ ℤ (numberFieldAdelicLattice K ι h.val))
    (ha : cmAdelicLatticeIntegralActions K H g b = cmAdelicLatticeIntegralActions K H h c)
    (a : 𝓞 K) (x : ι → K) :
    numberFieldAdelicLatticeRationalEquiv K g.val h.val b c ((a : K) • x) =
      (a : K) • numberFieldAdelicLatticeRationalEquiv K g.val h.val b c x := by
  let e := numberFieldAdelicLatticeRationalEquiv K g.val h.val b c
  let S := DistribSMul.toLinearMap ℚ (ι → K) (a : K)
  have he : e.toLinearMap.comp S = S.comp e.toLinearMap := by
    apply (numberFieldAdelicLatticeRationalBasis K ι g.val b).ext
    intro i
    rw [numberFieldAdelicLatticeRationalBasis_apply]
    change e (a • b i).val = (a : K) • e (b i).val
    rw [numberFieldAdelicLatticeRationalEquiv_integral,
      numberFieldAdelicLatticeRationalEquiv_integral]
    exact congrArg Subtype.val (cmAdelicLatticeBasisEquiv_integralScalar K H g h b c ha a (b i))
  exact LinearMap.congr_fun he x

/-- Equality of integral action invariants recovers commutation with every original CM-field scalar. -/
theorem cmAdelicLatticeRationalEquiv_fieldScalar (H : Matrix ι ι K)
    (g h : cmFiniteAdelicUnitaryGroup K H)
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val))
    (c : Basis κ ℤ (numberFieldAdelicLattice K ι h.val))
    (ha : cmAdelicLatticeIntegralActions K H g b = cmAdelicLatticeIntegralActions K H h c)
    (a : K) (x : ι → K) :
    numberFieldAdelicLatticeRationalEquiv K g.val h.val b c (a • x) =
      a • numberFieldAdelicLatticeRationalEquiv K g.val h.val b c x := by
  let e := numberFieldAdelicLatticeRationalEquiv K g.val h.val b c
  have he : e.toLinearMap.comp ((LinearMap.toSpanSingleton K (ι → K) x).restrictScalars ℚ) =
      (LinearMap.toSpanSingleton K (ι → K) (e x)).restrictScalars ℚ := by
    apply (integralBasis K).ext
    intro i
    change e (integralBasis K i • x) = integralBasis K i • e x
    rw [integralBasis_apply]
    exact cmAdelicLatticeRationalEquiv_integralScalar K H g h b c ha (RingOfIntegers.basis K i) x
  exact LinearMap.congr_fun he a

/-- The original field-linear lattice equivalence recovered from the equal integral action invariants. -/
def cmAdelicLatticeFieldEquiv (H : Matrix ι ι K)
    (g h : cmFiniteAdelicUnitaryGroup K H)
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val))
    (c : Basis κ ℤ (numberFieldAdelicLattice K ι h.val))
    (ha : cmAdelicLatticeIntegralActions K H g b = cmAdelicLatticeIntegralActions K H h c) :
    (ι → K) ≃ₗ[K] (ι → K) :=
  { (numberFieldAdelicLatticeRationalEquiv K g.val h.val b c).toAddEquiv with
    map_smul' := cmAdelicLatticeRationalEquiv_fieldScalar K H g h b c ha }

/-- The recovered field equivalence has precisely the original rational underlying map. -/
theorem cmAdelicLatticeFieldEquiv_apply (H : Matrix ι ι K)
    (g h : cmFiniteAdelicUnitaryGroup K H)
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val))
    (c : Basis κ ℤ (numberFieldAdelicLattice K ι h.val))
    (ha : cmAdelicLatticeIntegralActions K H g b = cmAdelicLatticeIntegralActions K H h c)
    (x : ι → K) :
    cmAdelicLatticeFieldEquiv K H g h b c ha x =
      numberFieldAdelicLatticeRationalEquiv K g.val h.val b c x := rfl

end
end Dubon2026
