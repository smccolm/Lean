import Dubon2026.SourceCurvePrincipalDivisorTransport
import Dubon2026.SourceCurvePrincipalExtensionDegree
import Mathlib.RingTheory.Norm.Transitivity

/-! DUB-17/18 -> original Frobenius/inertia -> residue principal-divisor
degree zero. In a finite Galois extension, the sum of actual conjugate
divisors is the divisor of the actual norm. Invariance and the proved
pullback degree formula force the original divisor degree to vanish.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable,
HPDfdPort.degree_eq_zero_of_isGalois. Existing local pullback and place
transport replace the external divisor-action infrastructure. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]

private theorem ord_product {ι : Type*} (v : Place K E) (s : Finset ι)
    (g : ι → E) (hg : ∀ i ∈ s, g i ≠ 0) :
    v.ord (∏ i ∈ s, g i) = ∑ i ∈ s, v.ord (g i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      v.ord_mul (hg i (Finset.mem_cons_self i s))
        (Finset.prod_ne_zero_iff.mpr fun j hj => hg j (Finset.mem_cons_of_mem hj)),
      ih fun j hj => hg j (Finset.mem_cons_of_mem hj)]

theorem principal_degree_zero_of_galois [FiniteDimensional F E] [IsGalois F E]
    [HasPrincipalDivisors K F]
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {f : E} {D : Divisor K E} (hD : ∀ w : Place K E, D w = w.ord f) :
    Divisor.degree D = 0 := by
  classical
  by_cases hf : f = 0
  · subst f
    have he : D = 0 := by ext w; simpa using hD w
    rw [he, map_zero]
  let S : Divisor K E := ∑ σ : E ≃ₐ[F] E, divisorTransform (σ.restrictScalars K) D
  have hS : ∀ w : Place K E, S w = w.ord (algebraMap F E (Algebra.norm F f)) := by
    intro w
    rw [Algebra.norm_eq_prod_automorphisms F f,
      ord_product w Finset.univ (fun σ : E ≃ₐ[F] E => σ f)
        (fun σ _ => by simpa using hf)]
    change (∑ σ : E ≃ₐ[F] E, divisorTransform (σ.restrictScalars K) D) w = _
    rw [Finset.sum_apply']
    exact Finset.sum_congr rfl fun σ _ => divisorTransform_orders (σ.restrictScalars K) hD w
  have hn : Algebra.norm F f ≠ 0 := Algebra.norm_ne_zero_iff.mpr hf
  obtain ⟨D₀, hD₀, hz₀⟩ := HasPrincipalDivisors.exists_divisor (K := K) (Algebra.norm F f) hn
  have hz : Divisor.degree S = 0 := by
    rw [principal_degree_extension hF hE hD₀ hS, hz₀, mul_zero]
  have he : Divisor.degree S = (Module.finrank F E : ℤ) * Divisor.degree D := by
    change Divisor.degree (∑ σ : E ≃ₐ[F] E, divisorTransform (σ.restrictScalars K) D) = _
    rw [map_sum]
    simp only [degree_divisorTransform _ _ hE hE]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    exact_mod_cast (Nat.card_eq_fintype_card (α := E ≃ₐ[F] E)).symm.trans
      (IsGalois.card_aut_eq_finrank F E)
  have hpos : (Module.finrank F E : ℤ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := F) (M := E)).ne'
  rw [hz] at he
  exact (mul_eq_zero.mp he.symm).resolve_left hpos

end
end Dubon2026.SourceCurve
