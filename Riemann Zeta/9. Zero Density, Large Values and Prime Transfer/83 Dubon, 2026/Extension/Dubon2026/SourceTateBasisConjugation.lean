import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Matrix.ToLin
import Dubon2026.SourceTateModule

/-! The exact basis transport needed by the original rational Tate
comparison. An intertwining equivalence transports operator matrices;
native tensor bases then retain the original integral entries. -/
namespace Dubon2026
noncomputable section

theorem toMatrix_transport_intertwining {R M P ι : Type*} [CommRing R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid P] [Module R P]
    [Fintype ι] [DecidableEq ι] (e : M ≃ₗ[R] P) (b : Module.Basis ι R P)
    (u : Module.End R M) (v : Module.End R P)
    (h : ∀ x, e (u x) = v (e x)) :
    LinearMap.toMatrix (b.map e.symm) (b.map e.symm) u = LinearMap.toMatrix b b v := by
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  congr 1
  ext x
  exact (h (e.symm x)).trans (congrArg v (e.apply_symm_apply x))

theorem tate_matrix_transport (p : ℕ) [Fact p.Prime] {M L ι : Type*}
    [AddCommGroup M] [AddCommMonoid L] [Module ℤ L] [Fintype ι] [DecidableEq ι]
    (e : TateModule p M ≃ₗ[ℤ_[p]] TensorProduct ℤ ℤ_[p] L)
    (b : Module.Basis ι ℤ L) (u : Module.End ℤ_[p] (TateModule p M))
    (v : Module.End ℤ L)
    (h : ∀ x, e (u x) = v.baseChange ℤ_[p] (e x)) :
    LinearMap.toMatrix ((Algebra.TensorProduct.basis ℤ_[p] b).map e.symm)
        ((Algebra.TensorProduct.basis ℤ_[p] b).map e.symm) u =
      (LinearMap.toMatrix b b v).map (Int.cast : ℤ → ℤ_[p]) :=
  (toMatrix_transport_intertwining e (Algebra.TensorProduct.basis ℤ_[p] b)
    u (v.baseChange ℤ_[p]) h).trans (LinearMap.toMatrix_baseChange ℤ_[p] v b b)

open Matrix in
theorem rankTwo_transfer_coordinates {K R V I : Type} [CommRing K] [Ring R]
    [AddCommMonoid V] [Module K V] {m : ℕ}
    (M : R → Matrix (Fin m) (Fin m) K) (w : I → R) (u : I → Module.End K V)
    (c : V ≃ₗ[K] (Fin m → K))
    (hc : ∀ a x, c (u a x) = M (w a) *ᵥ c x)
    (h : ∃ (T : Type) (_ : CommRing T) (_ : Algebra K T) (φ : R →+* T)
      (e : (Fin m → K) ≃ₗ[K] (Fin 2 → T)),
      Algebra.adjoin K (Set.range φ) = ⊤ ∧ ∀ t v, e (M t *ᵥ v) = φ t • e v) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra K T) (φ : R →+* T)
      (e : V ≃ₗ[K] (Fin 2 → T)),
      Algebra.adjoin K (Set.range φ) = ⊤ ∧ ∀ a x, e (u a x) = φ (w a) • e x := by
  obtain ⟨T, hT, hA, φ, e, hgen, hact⟩ := h
  refine ⟨T, hT, hA, φ, c.trans e, hgen, ?_⟩
  intro a x
  exact (congrArg e (hc a x)).trans (hact (w a) (c x))

end
end Dubon2026
