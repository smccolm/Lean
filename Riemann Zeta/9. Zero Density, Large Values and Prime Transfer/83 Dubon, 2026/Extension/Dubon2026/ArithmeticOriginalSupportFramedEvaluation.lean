import Dubon2026.ArithmeticOriginalSupportFramedFibers

/-! Evaluation of the actual descended framed lift along original
arithmetic restriction. This makes the support-fiber comparison usable
on the universal matrices when proving inverse coefficient maps. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators

/-- The original-support lift obtained by the proved inverse fiber
equivalence has exactly the supplied auxiliary lift on restriction. -/
theorem arithmeticOriginalSupportFramedFiberEquiv_symm_apply
    {ι O A : Type} [Fintype ι] [DecidableEq ι]
    [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A]
    [Algebra O A] [WithIdeal A] [T2Space A]
    (eA : ResidueField A ≃ₐ[O] ResidueField O)
    (a b : 𝓞 ℚ) (hb : b ≠ 0) (Q : Finset Nat.Primes)
    (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ)) (hab : a ∣ b)
    (haway : ∀ p : Q, ¬(p.val.val : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ResidueField O))
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (f : {f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup b)
        (σ.comp (rationalArithmeticSupportRestriction a b hab).toMonoidHom) //
      (∀ g, GeneralLinearGroup.det (f.val g) =
        Units.map (algebraMap O A) (δ (rationalArithmeticSupportRestriction a b hab g))) ∧
      ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
        f.val (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1})
    (g : rationalArithmeticGaloisGroup b) :
    ((arithmeticOriginalSupportFramedFiberEquiv eA a b hb Q hba hab haway σ δ).symm f).val.val
      (rationalArithmeticSupportRestriction a b hab g) = f.val.val g :=
  congrArg (fun t => t.val.val g)
    ((arithmeticOriginalSupportFramedFiberEquiv eA a b hb Q hba hab haway σ δ).apply_symm_apply f)

end
end Dubon2026
