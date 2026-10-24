import Dubon2026.SourceEllipticFiniteTorsionField

/-! Transfer the proved faithfulness of a division field to a containing
Galois stage. Native restriction of normal extensions and actual elliptic
point maps discharge the field-fixing obligation in the DUB-17/18 finite
inertia specialization, exceptional-fiber census, reverse genus and good
reduction chain. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_equivariant_torsion_reduction_ofJ, hLfix. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section

theorem fixes_division_field_of_fixes_torsion
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]
    (E : WeierstrassCurve F) (L M : IntermediateField F Ω) [IsGalois F L]
    (hL : L ≤ M) (n : ℕ)
    (faithful : ∀ τ : L ≃ₐ[F] L, (∀ P : (E.baseChange L).toAffine.Point,
      n • P = 0 → Point.map (τ : L →ₐ[F] L) P = P) → τ = 1)
    (σ : M ≃ₐ[F] M)
    (hfix : ∀ Q : (E.baseChange M).toAffine.Point, n • Q = 0 →
      Point.map (σ : M →ₐ[F] M) Q = Q) :
    ∀ x : M, (x : Ω) ∈ L → σ x = x := by
  let ι : L →ₐ[F] M := IntermediateField.inclusion hL
  letI : Algebra L M := (ι : L →+* M).toAlgebra
  haveI : IsScalarTower F L M := IsScalarTower.of_algHom ι
  let τ : L ≃ₐ[F] L := σ.restrictNormal L
  have hτ (z : L) : ι (τ z) = σ (ι z) := AlgEquiv.restrictNormal_commutes σ L z
  have hτ1 : τ = 1 := by
    apply faithful
    intro P hP
    apply Point.map_injective ι
    have hmap : Point.map ι (Point.map (τ : L →ₐ[F] L) P) =
        Point.map (σ : M →ₐ[F] M) (Point.map ι P) := by
      rcases P with _ | ⟨x, y, h⟩
      · rfl
      · simp only [Point.map_some]
        congr 1 <;> apply hτ
    rw [hmap]
    exact hfix _ (by rw [← map_nsmul, hP, map_zero])
  intro x hx
  have h := hτ ⟨x, hx⟩
  rw [hτ1, AlgEquiv.one_apply] at h
  have hxι : ι ⟨x, hx⟩ = x := Subtype.ext rfl
  rw [hxι] at h
  exact h.symm

end
end Dubon2026.SourceEllipticDivisionField
