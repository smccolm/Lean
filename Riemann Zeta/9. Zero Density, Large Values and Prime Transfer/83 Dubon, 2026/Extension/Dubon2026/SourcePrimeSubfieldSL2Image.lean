import Dubon2026.SourceResidualFiniteLinearAlternatives

/-! DUB-17/18 -> original split regular auxiliary primes. The prime-field
SL2 subgroup is already in the finite-subfield lower bound. Its eigenvalues
belong to the original residue field without a further coefficient descent. -/
namespace Dubon2026.SourceDickson
noncomputable section
open Matrix

/-- The finite-subfield SL2 lower bound contains the canonical prime-field
SL2 image, using the uniqueness of prime-field ring homomorphisms. -/
theorem prime_subfield_sl2_image_le
    (p : ℕ) [Fact p.Prime] {k E : Type} [Field k] [Field E]
    [CharP k p] [CharP E p] (θ : k →+* E) :
    ((GeneralLinearGroup.map (ZMod.castHom (dvd_refl p) E)).comp
      (SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod p))).range ≤
    ((GeneralLinearGroup.map θ).comp
      (SpecialLinearGroup.toGL (n := Fin 2) (R := k))).range := by
  rintro x ⟨A, rfl⟩
  let η := ZMod.castHom (dvd_refl p) k
  refine ⟨SpecialLinearGroup.map η A, ?_⟩
  apply Units.ext
  change (A.val.map η).map θ = A.val.map (ZMod.castHom (dvd_refl p) E)
  rw [Matrix.map_map]
  have he : θ.comp η = ZMod.castHom (dvd_refl p) E := Subsingleton.elim _ _
  change A.val.map (θ.comp η) = _
  rw [he]

end
end Dubon2026.SourceDickson
