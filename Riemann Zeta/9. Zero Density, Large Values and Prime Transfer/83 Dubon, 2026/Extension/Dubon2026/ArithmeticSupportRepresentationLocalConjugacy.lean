import Dubon2026.ArithmeticSupportLocalConjugacy

/-! A whole-representation comparison under actual arithmetic support
restriction induces the exact conjugacy comparison at the separately
chosen original local embeddings. This is the local compatibility
needed to transport deformation conditions through the ring comparison. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

/-- The actual local embeddings need only be conjugate. The global
comparison constructs the required coefficient-valued conjugating
matrix at every prime, without a supplied local compatibility datum. -/
theorem arithmeticSupportRepresentation_local_conjugacy
    {ι A B : Type} [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B]
    (a b : 𝓞 ℚ) (hab : a ∣ b)
    (τa : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι A)
    (τb : rationalArithmeticGaloisGroup b →* GeneralLinearGroup ι B)
    (f : B →+* A)
    (h : ∀ g, GeneralLinearGroup.map f (τb g) =
      τa (rationalArithmeticSupportRestriction a b hab g))
    (p : ℕ) (hp : p.Prime) :
    ∃ c : GeneralLinearGroup ι A, ∀ g,
      GeneralLinearGroup.map f (τb (rationalPrimeArithmeticRestriction b p hp g)) =
        c⁻¹ * τa (rationalPrimeArithmeticRestriction a p hp g) * c := by
  obtain ⟨u, hu⟩ := rationalArithmeticSupportRestriction_local_conjugacy a b hab p hp
  refine ⟨τa u, ?_⟩
  intro g
  rw [h, hu g, map_mul, map_mul, map_inv]

end
end Dubon2026
