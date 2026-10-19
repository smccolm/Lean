import Dubon2026.TameCharacterInertiaExponent

/-! The proved whole diagonal-character exponent is the exponent of the
same original matrix representation. This removes the remaining exponent
input of cyclotomic inertia descent at the selected auxiliary primes in
the local deformation-ring chain for Dubon Theorem 2.6. -/

namespace Dubon2026
open Matrix

/-- Cyclic inertia and the constructed tame diagonal characters prove
the full inertia exponent for the original, unconjugated representation. -/
theorem tame_diagonal_matrix_inertia_pow_eq_one
    {G A ι : Type} [Group G] [CommRing A] [Fintype ι] [DecidableEq ι]
    (I : Subgroup G) (t : G) (ρ : G →* GeneralLinearGroup ι A)
    (W : GeneralLinearGroup ι A) (χ : G →* (ι → A)ˣ)
    (hχ : ∀ g, diagonal (χ g).val = (MulAut.conj W (ρ g)).val)
    (hI : I.map ρ = Subgroup.zpowers (ρ t))
    (p : ℕ) (hp : 1 ≤ p) (ht : ∀ i, ((χ t).val i)^p = (χ t).val i) :
    ∀ g ∈ I, ρ g ^ (p - 1) = 1 := by
  have hχI := diagonal_characters_cyclic_inertia I t ρ W χ hχ hI
  have hχpow := cyclic_tame_characters_inertia_pow_eq_one I t χ hχI p hp ht
  let D := Units.map (diagonalRingHom ι A).toMonoidHom
  intro g hg
  apply (MulAut.conj W).injective
  rw [map_pow, map_one]
  have he : MulAut.conj W (ρ g) = D (χ g) := Units.ext (hχ g).symm
  rw [he, ← map_pow, hχpow g hg, map_one]

end Dubon2026
