import Dubon2026.SourceCurveFiberDegrees
import Mathlib.Algebra.BigOperators.Finprod

/-! DUB-17/18 -> original global residue identity -> normal-closure descent.
The pinned Dedekind sum of ramification times inertia becomes the exact sum
of normalized ramification orders over the actual place fiber, when the
actual base and extension residue fields are the constant field.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain IsLocalRing
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem sum_fiber_ramification (v : Place K F)
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField)) :
    ∑ᶠ w : {w : Place K E // w.restrict F = v},
      w.1.ord (algebraMap F E v.uniformizer) = (Module.finrank F E : ℤ) := by
  classical
  let R := integralClosureAt E v
  let p := maximalIdeal v.toValuationSubring
  let S := IsDedekindDomain.primesOverFinset p R
  let e := (fiberPrimeEquiv E v).trans (fiberPrimeFinsetEquiv E v)
  have hd := Ideal.sum_ramification_inertia R F E v.maximalIdeal_ne_bot
  have hi : ∀ P ∈ S, p.inertiaDeg P = 1 := by
    intro P hP
    let Q := (fiberPrimeFinsetEquiv E v).symm ⟨P, hP⟩
    exact fiberPrime_inertiaDeg_eq_one v hbase Q (htop _)
  have he : ∀ w : {w : Place K E // w.restrict F = v},
      w.1.ord (algebraMap F E v.uniformizer) = (p.ramificationIdx (e w).1 : ℤ) := by
    intro w
    rw [← fiberPrimePlace_fiberCenter w.2, fiberPrime_order_eq_ramificationIdx]
    rfl
  calc
    _ = ∑ᶠ w : {w : Place K E // w.restrict F = v},
        (p.ramificationIdx (e w).1 : ℤ) := finsum_congr he
    _ = ∑ᶠ P : {P // P ∈ S}, (p.ramificationIdx P.1 : ℤ) :=
      finsum_comp_equiv e (f := fun P => (p.ramificationIdx P.1 : ℤ))
    _ = ∑ P ∈ S, (p.ramificationIdx P : ℤ) := by
      rw [finsum_eq_sum_of_fintype]
      exact Finset.sum_coe_sort S (fun P => (p.ramificationIdx P : ℤ))
    _ = (∑ P ∈ S, p.ramificationIdx P * p.inertiaDeg P : ℕ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro P hP
      rw [hi P hP, Nat.cast_one, mul_one]
    _ = (Module.finrank F E : ℤ) := congrArg Nat.cast hd

end
end Dubon2026.SourceCurve.Place
