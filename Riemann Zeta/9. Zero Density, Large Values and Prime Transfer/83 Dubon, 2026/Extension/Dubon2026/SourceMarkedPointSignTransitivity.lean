import Dubon2026.SourceMarkedCyclicGeneratorConjugacy
import Dubon2026.SourceMarkedTorsionGeneratorUnit

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> original marked
chart -> stabilizer comparison. Combine the actual cyclic-generator
conjugacy with unit moves to prove transitivity up to sign. The following
original-field consumer supplies all unit moves from its constructed diamond
embeddings. This avoids expanding the stronger full Tate monodromy route. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve

theorem exists_point_conjugacy_up_to_sign_of_unit_moves
    {K k Ω : Type*} [Field K] [IsAlgClosed K] [Field k] [Field Ω] [DecidableEq Ω]
    [Algebra K k] [Algebra K Ω] [Algebra k Ω] [IsScalarTower K k Ω] [IsAlgClosure k Ω]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (E : WeierstrassCurve k) [E.IsElliptic] (hE : Transcendental K E.j)
    (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤)
    (P : (E.baseChange Ω).toAffine.Point) (hP : addOrderOf P = N)
    (hunit : ∀ u : (ZMod N)ˣ, ∃ τ : Ω ≃ₐ[k] Ω,
      Affine.Point.map (W' := E) τ.toAlgHom P = (u : ZMod N).val • P ∨
      Affine.Point.map (W' := E) τ.toAlgHom P = -((u : ZMod N).val • P))
    (Q : (E.baseChange Ω).toAffine.Point) (hQ : addOrderOf Q = N) :
    ∃ σ : Ω ≃ₐ[k] Ω, Affine.Point.map (W' := E) σ.toAlgHom P = Q ∨
      Affine.Point.map (W' := E) σ.toAlgHom P = -Q := by
  obtain ⟨σ, n, hσ⟩ := exists_cyclic_generator_conjugacy N hN E hE hgen Q P hQ hP
  have hn : addOrderOf (n • P) = N := by
    rw [← hσ, addOrderOf_injective _ (Affine.Point.map_injective σ.toAlgHom), hQ]
  obtain ⟨u, hu⟩ := MarkedTorsion.exists_unit_multiple_of_equal_order N P hP n hn
  obtain ⟨τ, hτ⟩ := hunit u
  have hi : Affine.Point.map (W' := E) σ.symm.toAlgHom
      (Affine.Point.map (W' := E) σ.toAlgHom Q) = Q := by
    rw [Affine.Point.map_map, AlgEquiv.symm_comp]
    cases Q <;> rfl
  refine ⟨τ.trans σ.symm, ?_⟩
  change Affine.Point.map (W' := E) (σ.symm.toAlgHom.comp τ.toAlgHom) P = Q ∨
    Affine.Point.map (W' := E) (σ.symm.toAlgHom.comp τ.toAlgHom) P = -Q
  rw [← Affine.Point.map_map]
  rcases hτ with h | h
  · left
    rw [h, hu, ← hσ, hi]
  · right
    rw [h, map_neg, hu, ← hσ, hi]

end
end Dubon2026.SourceFunctionField.MarkedChart
