import Dubon2026.SourceHeckeMatrixRationalGenerators
import Dubon2026.SourceHeckeMatrixPadicAlgebra
/-! DUB-17/18 -> rank-two original Tate Hecke realization -> descent of
two real generators to rational and padic generators of the same integral
matrix action. Adapted from the W1D determinant argument in
S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. The actual original lattice
representation, real spanning and rank equality remain required inputs
until the native consumer supplies them.
-/
namespace Dubon2026.SourceHeckeMatrixDescent
noncomputable section
open Module Matrix
variable {R₀ : Type} [CommRing R₀] {n : ℕ} (Mℤ : R₀ →+* Matrix (Fin n) (Fin n) ℤ)

section Padic
variable (p : ℕ) [Fact p.Prime]
variable (hn : 2 * g Mℤ = n) (vq : Fin 2 → Fin n → ℚ)

/-- The two chosen rational generator vectors viewed over the p-adic field. -/
def vp : Fin 2 → Fin n → ℚ_[p] := fun a => (algebraMap ℚ ℚ_[p]) ∘ vq a

/-- Evaluate two p-adic operator coefficients on the two generator vectors. -/
def ψ : (Fin 2 → Tp Mℤ p) →ₗ[ℚ_[p]] (Fin n → ℚ_[p]) where
  toFun s := ∑ a, ((s a : Tp Mℤ p) : Matrix (Fin n) (Fin n) ℚ_[p]) *ᵥ vp p vq a
  map_add' s s' := by
    simp only [Pi.add_apply, Subalgebra.coe_add, Matrix.add_mulVec, Finset.sum_add_distrib]
  map_smul' r s := by
    simp only [Pi.smul_apply, Subalgebra.coe_smul, Matrix.smul_mulVec, RingHom.id_apply,
      Finset.smul_sum]

theorem ψ_apply (s : Fin 2 → Tp Mℤ p) :
    ψ Mℤ p vq s = ∑ a, ((s a : Tp Mℤ p) : Matrix (Fin n) (Fin n) ℚ_[p]) *ᵥ vp p vq a := rfl

theorem ψ_equivariant (t : R₀) (s : Fin 2 → Tp Mℤ p) :
    ψ Mℤ p vq (φ Mℤ p t • s) = MK Mℤ ℚ_[p] t *ᵥ ψ Mℤ p vq s := by
  simp only [ψ_apply, Pi.smul_apply, smul_eq_mul, Subalgebra.coe_mul, coe_φ, Matrix.mulVec_sum,
    Matrix.mulVec_mulVec]

theorem ψ_surjective (hv : IsUnit (Φ Mℤ hn ℚ vq)) : Function.Surjective (ψ Mℤ p vq) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  have hvp : IsUnit (Φ Mℤ hn ℚ_[p] (vp p vq)) := by
    have := (RingHom.mapMatrix (algebraMap ℚ ℚ_[p])).isUnit_map hv
    rwa [RingHom.mapMatrix_apply, Φ_map] at this
  rw [← span_cols_Φ_of_isUnit Mℤ hn ℚ_[p] (vp p vq) hvp, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨⟨a, k⟩, rfl⟩ := (σ Mℤ hn).surjective j
  rw [Φ_col]
  refine ⟨Pi.single a ⟨cK Mℤ ℚ_[p] k, cK_mem_Tp Mℤ p k⟩, ?_⟩
  rw [ψ_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem finrank_source_le : finrank ℚ_[p] (Fin 2 → Tp Mℤ p) ≤ 2 * g Mℤ := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.mul_le_mul_left 2 (finrank_Tp_le Mℤ p)

theorem ψ_bijective (hv : IsUnit (Φ Mℤ hn ℚ vq)) : Function.Bijective (ψ Mℤ p vq) := by
  have hsurj := ψ_surjective Mℤ p hn vq hv
  refine ⟨?_, hsurj⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker (ψ Mℤ p vq)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun] at hrk
  have hle := finrank_source_le Mℤ p
  rw [hn] at hle
  have hker : finrank ℚ_[p] (LinearMap.ker (ψ Mℤ p vq)) = 0 := by omega
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.mp hker

theorem exists_equiv (hv : IsUnit (Φ Mℤ hn ℚ vq)) :
    ∃ e : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin 2 → Tp Mℤ p),
      ∀ (t : R₀) (v : Fin n → ℚ_[p]), e (MK Mℤ ℚ_[p] t *ᵥ v) = φ Mℤ p t • e v := by
  let e := (LinearEquiv.ofBijective (ψ Mℤ p vq) (ψ_bijective Mℤ p hn vq hv)).symm
  refine ⟨e, fun t v => ?_⟩
  apply e.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change MK Mℤ ℚ_[p] t *ᵥ v = ψ Mℤ p vq (φ Mℤ p t • e v)
  rw [ψ_equivariant]
  congr 1
  exact (LinearEquiv.ofBijective (ψ Mℤ p vq) (ψ_bijective Mℤ p hn vq hv)).apply_symm_apply v |>.symm

end Padic

open scoped IsMulCommutative in
theorem descent (p : ℕ) [Fact p.Prime] (hn : 2 * g Mℤ = n)
    (hw : ∃ w : Fin 2 → Fin n → ℝ,
      Submodule.span ℝ (Set.range fun ta : R₀ × Fin 2 => MK Mℤ ℝ ta.1 *ᵥ w ta.2) = ⊤) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra ℚ_[p] T) (φ : R₀ →+* T)
      (e : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin 2 → T)),
      Algebra.adjoin ℚ_[p] (Set.range φ) = ⊤ ∧
        ∀ (t : R₀) (v : Fin n → ℚ_[p]), e (MK Mℤ ℚ_[p] t *ᵥ v) = φ t • e v := by
  letI := Tp_commutative Mℤ p
  letI : CommRing (Tp Mℤ p) := inferInstance
  obtain ⟨vq, hv⟩ := exists_rat_isUnit_Φ Mℤ hn hw
  obtain ⟨e, he⟩ := exists_equiv Mℤ p hn vq hv
  exact ⟨Tp Mℤ p, inferInstance, inferInstance, φ Mℤ p, e, adjoin_range_φ Mℤ p, he⟩


end
end Dubon2026.SourceHeckeMatrixDescent
