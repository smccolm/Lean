import Dubon2026.ArithmeticOriginalSupportDescent
import Dubon2026.ArithmeticSupportInertia
import Dubon2026.OriginalResidualFramedFibers

/-! The actual fixed-determinant framed deformation fibers on original
support are equivalent to auxiliary-support fibers with trivial
auxiliary inertia. This is the functor-level comparison required to
identify the universal augmentation quotient for Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField BigOperators

variable {ι O A : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [T2Space A]

/-- Pullback along actual arithmetic restriction is an equivalence
between all original fixed-determinant framed lifts and exactly the
auxiliary lifts whose original auxiliary inertia action is trivial. -/
def arithmeticOriginalSupportFramedFiberEquiv
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (a b : 𝓞 ℚ) (hb : b ≠ 0) (Q : Finset Nat.Primes)
    (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ)) (hab : a ∣ b)
    (haway : ∀ p : Q, ¬(p.val.val : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (δ : rationalArithmeticGaloisGroup a →* Oˣ) :
    (let π := rationalArithmeticSupportRestriction a b hab
     {f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup a) σ //
       ∀ g, GeneralLinearGroup.det (f.val g) = Units.map (algebraMap O A) (δ g)} ≃
     {f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup b)
         (σ.comp π.toMonoidHom) //
       (∀ g, GeneralLinearGroup.det (f.val g) = Units.map (algebraMap O A) (δ (π g))) ∧
       ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
         f.val (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1}) := by
  let π := rationalArithmeticSupportRestriction a b hab
  have hs := rationalArithmeticSupportRestriction_surjective a b hab
  let pull := fun (f : {f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup a) σ //
      ∀ g, GeneralLinearGroup.det (f.val g) = Units.map (algebraMap O A) (δ g)}) =>
    (show {f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup b)
        (σ.comp π.toMonoidHom) //
      (∀ g, GeneralLinearGroup.det (f.val g) = Units.map (algebraMap O A) (δ (π g))) ∧
      ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
        f.val (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1} from by
      refine ⟨⟨f.val.val.comp π, ?_⟩, (fun g => f.property (π g)), ?_⟩
      · apply MonoidHom.ext
        intro g
        exact DFunLike.congr_fun f.val.property (π g)
      · intro p g hg
        change f.val.val (π (rationalPrimeArithmeticRestriction b p.val.val p.val.property g)) = 1
        rw [rationalArithmeticSupportRestriction_inertia_eq_one a b hab p.val.val p.val.property
          (haway p) g hg, map_one])
  apply Equiv.ofBijective pull
  constructor
  · intro f f' he
    apply Subtype.ext
    apply Subtype.ext
    apply DFunLike.ext
    intro g
    obtain ⟨x, rfl⟩ := hs g
    exact congrArg (fun t => t.val.val x) he
  · intro f
    obtain ⟨η, hη, _⟩ := adicArithmetic_original_support_descent a b hb Q hba hab f.val.val f.property.2
    have hr : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eA).toRingHom).comp
        η.toMonoidHom = σ := by
      apply MonoidHom.ext
      intro g
      obtain ⟨x, rfl⟩ := hs g
      change GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom (η (π x)) = σ (π x)
      rw [hη x]
      exact DFunLike.congr_fun f.val.property x
    have hd : ∀ g, GeneralLinearGroup.det (η g) = Units.map (algebraMap O A) (δ g) := by
      intro g
      obtain ⟨x, rfl⟩ := hs g
      rw [hη x]
      exact f.property.1 x
    refine ⟨⟨⟨η, hr⟩, hd⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply DFunLike.ext
    exact hη

end
end Dubon2026
