import Dubon2026.SourceConjugateUniformizerOrders
import Dubon2026.SourceCurvePolynomialDerivativeOrder
import Dubon2026.SourceWildDisplacementSum

/-! Conditional local wild different bound for the exact DUB-17/18
characteristic-three order-six and characteristic-two order-twelve steps.
The polynomial, its integral fixed coefficients, derivative order and
finite sum are derived. The actual inertia action, fixed-field order gap,
residue character and its displacement bound remain explicit upstream
inputs, to be supplied on the actual modular auxiliary Galois field.
This adapts the FLT wild different argument, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, using existing local derivations
and native coefficient-wise polynomial differentiation. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential IntermediateField Polynomial
variable {K F G : Type*} [Field K] [Field F] [Algebra K F] [Group G] [Fintype G]
variable (v : Place K F)
variable [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K v.ResidueField] [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem wild_different_bound_of_inertia_data
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ρ : G →* (F ≃ₐ[K] F)) (χ : G →* Kˣ)
    (hρ : ∀ σ, v.ord (ρ σ v.uniformizer) = 1)
    (x : F) (hxZ : x ∈ fixedField ρ.range) (hx : v.ord x = (Nat.card G : ℤ))
    (hgap : ∀ z ∈ fixedField ρ.range, v.ord x ∣ v.ord z)
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    (hDx : v.coordinateDerivation x ≠ 0)
    (hker : ∀ σ, χ σ = 1 → v.OrdGe 2 (v.uniformizer - ρ σ v.uniformizer))
    (a : ℕ) (ha : p ^ a ∣ Nat.card G) :
    v.ord x - 1 + ((p : ℤ) ^ a - 1) ≤ v.ordDifferential (D K F x) := by
  classical
  have hxpos : 0 < v.ord x := by rw [hx]; exact_mod_cast (Nat.card_pos (α := G))
  let f := conjugateUniformizerPolynomial ρ v.uniformizer
  have hf := v.polynomial_derivative_order_of_fixed_coefficients
    (fixedField ρ.range) x hxZ hxpos hgap hres hDx f
    (conjugateUniformizerPolynomial_eval ρ v.uniformizer)
    (conjugateUniformizerPolynomial_coeff_fixed ρ v.uniformizer)
    (conjugateUniformizerPolynomial_coeff_mem ρ v.uniformizer
      v.toValuationSubring.toSubring (fun σ => v.mem_of_ord_nonneg (by rw [hρ σ]; omega)))
    ((conjugateUniformizerPolynomial_constant_order v ρ v.uniformizer hρ).trans hx.symm)
  have hprod : ∏ σ ∈ Finset.univ.erase (1 : G), (v.uniformizer - ρ σ v.uniformizer) ≠ 0 := by
    rw [← conjugateUniformizerPolynomial_derivative_eval]
    exact hf.1
  have hfac : ∀ σ ≠ 1, v.uniformizer - ρ σ v.uniformizer ≠ 0 := by
    intro σ hσ
    exact (Finset.prod_ne_zero_iff.mp hprod) σ (Finset.mem_erase.mpr ⟨hσ, Finset.mem_univ _⟩)
  have hbase : ∀ σ ≠ 1, 1 ≤ v.ord (v.uniformizer - ρ σ v.uniformizer) := by
    intro σ hσ
    have ht : v.OrdGe 1 v.uniformizer := Or.inr v.ord_uniformizer.ge
    have hσt : v.OrdGe 1 (ρ σ v.uniformizer) := Or.inr (hρ σ).ge
    exact (ht.sub hσt).le_ord (hfac σ hσ)
  have hwild : ∀ σ ≠ 1, σ ∈ χ.ker → 2 ≤ v.ord (v.uniformizer - ρ σ v.uniformizer) := by
    intro σ hσ hk
    exact (hker σ (MonoidHom.mem_ker.mp hk)).le_ord (hfac σ hσ)
  have hsum := displacement_sum_ge_wild_power p χ a ha
    (fun σ => v.ord (v.uniformizer - ρ σ v.uniformizer)) hbase hwild
  rw [← conjugateUniformizerPolynomial_derivative_order v ρ v.uniformizer hf.1, hf.2] at hsum
  simpa only [hx, ordDifferential, coordinateDerivation_apply] using hsum

end
end Dubon2026.SourceCurve.Place
