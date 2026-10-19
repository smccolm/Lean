import Dubon2026.AuxiliaryGroupAlgebraPowerSeries
import Mathlib.Algebra.BigOperators.Pi

/-! The original cyclic generators make the constructed coefficient action
surjective. This identifies the auxiliary algebra with the parameter ring
modulo its kernel, as required to transfer genuine auxiliary-module freeness
to the quotient-by-annihilator hypothesis of DUB-17's patching theorem. -/

namespace Dubon2026
noncomputable section

/-- Specified values on the original cyclic generators already force the
power-series parameter map onto the actual auxiliary group algebra. -/
theorem auxiliaryGroupAlgebra_parameter_surjective
    (O : Type) [CommRing O] {ι η : Type} [Fintype ι] [DecidableEq ι] [Fintype η]
    (Q : Finset Nat.Primes) (q : ℕ) [Fact q.Prime]
    (e : η ≃ Q × ι)
    (g : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q)
    (hgen : ∀ p, ∀ d : RationalPrimeTameCoefficientQuotient p.val.val q, ∃ n : ℕ, g p ^ n = d)
    (f : MvPowerSeries η O →ₐ[O]
      MonoidAlgebra O (∀ p : Q, ι → RationalPrimeTameCoefficientQuotient p.val.val q))
    (hf : ∀ j, f (MvPowerSeries.X j) = MonoidAlgebra.of O _
      (Pi.mulSingle (e j).1 (Pi.mulSingle (e j).2 (g (e j).1))) - 1) :
    Function.Surjective f := by
  classical
  let D := ∀ p : Q, ι → RationalPrimeTameCoefficientQuotient p.val.val q
  have hsingle (p : Q) (i : ι) :
      MonoidAlgebra.of O D (Pi.mulSingle p (Pi.mulSingle i (g p))) ∈ f.range := by
    refine ⟨MvPowerSeries.X (e.symm (p, i)) + 1, ?_⟩
    rw [map_add, map_one]
    change f (MvPowerSeries.X (e.symm (p, i))) + 1 = _
    rw [hf]
    rw [sub_add_cancel]
    exact congrArg (fun z : Q × ι =>
      MonoidAlgebra.of O D (Pi.mulSingle z.1 (Pi.mulSingle z.2 (g z.1))))
      (e.apply_symm_apply (p, i))
  have hbasis (d : D) : MonoidAlgebra.of O D d ∈ f.range := by
    induction d using Pi.mulSingle_induction with
    | one => simpa only [map_one] using f.range.one_mem
    | mul x y hx hy => simpa only [map_mul] using f.range.mul_mem hx hy
    | mulSingle p d =>
      induction d using Pi.mulSingle_induction with
      | one => simpa only [Pi.mulSingle_one, map_one] using f.range.one_mem
      | mul x y hx hy =>
        change MonoidAlgebra.of O D
          ((MonoidHom.mulSingle (fun p : Q => ι → RationalPrimeTameCoefficientQuotient p.val.val q) p)
            (x * y)) ∈ f.range
        rw [map_mul, map_mul]
        exact f.range.mul_mem hx hy
      | mulSingle i d =>
        obtain ⟨n, rfl⟩ := hgen p d
        change MonoidAlgebra.of O D
          ((MonoidHom.mulSingle (fun p : Q => ι → RationalPrimeTameCoefficientQuotient p.val.val q) p)
            ((MonoidHom.mulSingle (fun _ : ι => RationalPrimeTameCoefficientQuotient p.val.val q) i)
              (g p ^ n))) ∈ f.range
        rw [map_pow, map_pow, map_pow]
        exact f.range.pow_mem (hsingle p i) n
  intro x
  have hx : x ∈ f.range := by
    induction x using MonoidAlgebra.induction_on with
    | hM d => exact hbasis d
    | hadd x y hx hy => exact f.range.add_mem hx hy
    | hsmul r x hx => exact f.range.smul_mem hx r
  exact hx

end
end Dubon2026
