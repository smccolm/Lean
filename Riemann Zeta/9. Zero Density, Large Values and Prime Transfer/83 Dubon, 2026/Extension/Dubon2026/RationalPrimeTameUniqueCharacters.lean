import Dubon2026.RationalPrimeTameCharacters
import Dubon2026.DiagonalCharacterStrictUniqueness

/-! Unique character parameters of the actual finite local deformation,
using the existing whole-representation strict-conjugacy relation. This
joins existence and uniqueness for the ramified local-ring computation
on the dependency chain to Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing

attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- In the fixed residual Frobenius basis, every actual auxiliary Artinian
local lift has a unique whole character family modulo strict conjugacy. -/
theorem rationalPrime_artinian_tame_unique_characters
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {F A ι : Type} [Field F] [NumberField F]
    [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [Fintype ι] [DecidableEq ι] [CharP (ResidueField A) q]
    (hpone : (p : ResidueField A) = 1)
    (e : F →+* rationalPrimeLocalClosure p hp)
    (r : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* Gal(F/ℚ))
    (he : ∀ g x, e (r g x) = g (e x))
    (φ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hφ : ∀ x : ResidueField (algebraicLocalIntegerRing
      (rationalPrimeLocalClosure p hp)), φ • x = x ^ p)
    (ρ : (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker) →*
      GeneralLinearGroup ι A)
    (hres : ∀ g ∈ (rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker),
      GeneralLinearGroup.map (residue A) (ρ g) = 1)
    (α : ι → ResidueField A) (hα : Function.Injective α)
    (hF : (ρ (QuotientGroup.mk' r.ker φ)).val.map (residue A) = diagonal α) :
    ∃! χ : (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker) →*
      (ι → A)ˣ,
      MatrixStrictlyConjugate (residue A) ρ
        ((Units.map (diagonalRingHom ι A).toMonoidHom).comp χ) := by
  obtain ⟨_, U, χ, _, _, hU, hχ, _, _, _⟩ :=
    rationalPrime_artinian_tame_character_decomposition p q hp hq hpq hpone e r he φ hφ ρ hres α hα hF
  have hs : MatrixStrictlyConjugate (residue A) ρ
      ((Units.map (diagonalRingHom ι A).toMonoidHom).comp χ) := by
    refine ⟨U⁻¹, ?_, ?_⟩
    · rw [map_inv, hU, inv_one]
    · intro g
      apply Units.ext
      exact hχ g
  refine ⟨χ, hs, ?_⟩
  intro ψ hψ
  exact (diagonal_characters_strictlyConjugate_iff ψ χ).mp
    (matrixStrictlyConjugate_trans _ _ _ _ (matrixStrictlyConjugate_symm _ _ _ hψ) hs)

end
end Dubon2026
