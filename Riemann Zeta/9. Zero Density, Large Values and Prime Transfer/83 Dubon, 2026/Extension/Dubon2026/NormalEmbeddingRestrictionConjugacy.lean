import Dubon2026.EmbeddedNormalGaloisRestriction

/-! Normality compares separately chosen original local embeddings by
an actual global automorphism. This discharges the field-level conjugacy
needed to replace literal local residual compatibility in the Dubon
Theorem 2.6 auxiliary deformation comparison. -/

namespace Dubon2026
noncomputable section

variable {k E F L : Type*} [Field k] [Field E] [Field F] [Field L]
  [Algebra k E] [Normal k E] [Algebra k F] [Algebra F L] [Algebra k L]
  [IsScalarTower k F L]

/-- Two embeddings of the same actual normal field differ by a genuine
automorphism of that field, using pinned normal restriction. -/
theorem normal_embeddings_exists_automorphism (e f : E →ₐ[k] L) :
    ∃ u : Gal(E/k), ∀ x, e (u x) = f x := by
  letI : Algebra E L := e.toRingHom.toAlgebra
  letI : IsScalarTower k E L := IsScalarTower.of_algHom e
  refine ⟨f.restrictNormal' E, ?_⟩
  intro x
  exact f.restrictNormal_commutes E x

/-- The two genuine local restriction maps are conjugate by the same
global automorphism, simultaneously for every local automorphism. -/
theorem embeddedNormalGaloisRestriction_exists_conjugacy (e f : E →ₐ[k] L) :
    ∃ u : Gal(E/k), ∀ g : Gal(L/F),
      embeddedNormalGaloisRestriction f g =
        u⁻¹ * embeddedNormalGaloisRestriction e g * u := by
  obtain ⟨u, hu⟩ := normal_embeddings_exists_automorphism e f
  refine ⟨u, ?_⟩
  intro g
  apply AlgEquiv.ext
  intro x
  apply u.injective
  apply e.injective
  change e (u (embeddedNormalGaloisRestriction f g x)) =
    e (u (u.symm (embeddedNormalGaloisRestriction e g (u x))))
  rw [u.apply_symm_apply, hu, embeddedNormalGaloisRestriction_commutes,
    ← hu, embeddedNormalGaloisRestriction_commutes]

end
end Dubon2026
