import Dubon2026.ArithmeticTorusPrimeCharacters
import Dubon2026.ContinuousGaloisFiniteFactors
import Mathlib.Topology.Algebra.Group.Units

/-! The finite local factor in the auxiliary character classification is
constructed from the actual continuous global Artinian deformation. Its
ramification set may be larger than that of the residual representation,
as required for the Taylor-Wiles primes on the path to Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

attribute [local instance] rationalArithmeticOriginalFiniteGalois rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- The actual global lift, with its possibly enlarged ramification set,
supplies the finite local factor and its literal embedding square. At each
selected auxiliary prime its whole original local restriction is a sum of
characters with the selected residual weights and tame power equation. -/
theorem rationalArithmetic_torus_global_lift_characters
    (a b : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime] (hlevel : 0 < level)
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes) (hgood : RationalArithmeticTorusAuxiliaryPrime a q degree level R p)
    {A : Type} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [TopologicalSpace A] [DiscreteTopology A]
    (eA : ResidueField A ≃+* ZMod q)
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) A)
    (hτ : Continuous τ)
    (hred : ∀ g, GeneralLinearGroup.map (eA.toRingHom.comp (residue A))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property g)) :
    ∃ (φ δ : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property))
      (u : (ZMod q)ˣ) (W : GeneralLinearGroup (Fin (degree + 1)) A)
      (χ : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property) →*
        (Fin (degree + 1) → A)ˣ),
      (∀ x : ResidueField (algebraicLocalIntegerRing (rationalPrimeLocalClosure p.val p.property)),
        φ • x = x ^ p.val) ∧ 2 * degree < orderOf u ∧ δ ∈ rationalPrimeNormInertia p.val p.property ∧
      (rationalPrimeNormInertia p.val p.property).map
        (τ.comp (rationalPrimeArithmeticRestriction b p.val p.property).toMonoidHom) =
          Subgroup.zpowers (τ (rationalPrimeArithmeticRestriction b p.val p.property δ)) ∧
      (∀ g, diagonal (χ g).val =
        (MulAut.conj W (τ (rationalPrimeArithmeticRestriction b p.val p.property g))).val) ∧
      (∀ i, eA (residue A ((χ φ).val i)) =
        (u : ZMod q) ^ i.val * (↑u⁻¹ : ZMod q) ^ (degree - i.val)) ∧
      (∀ i, residue A ((χ δ).val i) = 1) ∧
      ∀ i, ((χ δ).val i) ^ p.val = (χ δ).val i := by
  let τc : Gal(rationalUnramifiedExtension b/ℚ) →ₜ*
      GeneralLinearGroup (Fin (degree + 1)) A := ⟨τ, hτ⟩
  obtain ⟨F, ψ, hψ⟩ := continuous_galois_finite_factor τc
  letI : NumberField F := NumberField.of_module_finite ℚ F
  let f := rationalPrimeArithmeticOriginalEmbedding b p.val p.property
  let e : F →+* rationalPrimeLocalClosure p.val p.property :=
    f.comp (algebraMap F (rationalUnramifiedExtension b))
  let r := (AlgEquiv.restrictNormalHom F).comp
    (rationalPrimeArithmeticRestriction b p.val p.property).toMonoidHom
  have he (g : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property))
      (x : F) : e (r g x) = g (e x) := by
    have hr := (rationalPrimeArithmeticRestriction b p.val p.property g).restrictNormal_commutes F x
    exact (congrArg f hr).trans
      (rationalPrimeArithmeticRestriction_commutes b p.val p.property g (algebraMap F _ x))
  have hker : r.ker ≤ (ψ.comp r).ker := by
    intro g hg
    change ψ (r g) = 1
    rw [show r g = 1 from hg]
    exact ψ.map_one
  let ρ := QuotientGroup.lift r.ker (ψ.comp r) hker
  have hρ (g : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property)) :
      ρ (QuotientGroup.mk' r.ker g) = τ (rationalPrimeArithmeticRestriction b p.val p.property g) :=
    hψ _
  have hρred (g : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property)) :
      GeneralLinearGroup.map (eA.toRingHom.comp (residue A)) (ρ (QuotientGroup.mk' r.ker g)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property g) := by
    rw [hρ]
    exact hred g
  obtain ⟨φ, u, t, W, χ, hφ, hu, ht, himage, hχ, hχφ, hχt, hχtp⟩ :=
    rationalArithmetic_torus_prime_character_decomposition a q degree level hlevel R p hgood
      eA e r he ρ hρred
  obtain ⟨δ, hδ, hδt⟩ := ht
  let χ' := χ.comp (QuotientGroup.mk' r.ker)
  have hρhom : ρ.comp (QuotientGroup.mk' r.ker) =
      τ.comp (rationalPrimeArithmeticRestriction b p.val p.property).toMonoidHom := MonoidHom.ext hρ
  refine ⟨φ, δ, u, W, χ', hφ, hu, hδ, ?_, ?_, hχφ, ?_, ?_⟩
  · rw [← hρhom, ← Subgroup.map_map, himage, ← hδt, hρ]
  · intro g
    exact (hχ (QuotientGroup.mk' r.ker g)).trans (congrArg (fun M => (MulAut.conj W M).val) (hρ g))
  · intro i
    change residue A ((χ (QuotientGroup.mk' r.ker δ)).val i) = 1
    rw [hδt]
    exact hχt i
  · intro i
    change ((χ (QuotientGroup.mk' r.ker δ)).val i) ^ p.val = (χ (QuotientGroup.mk' r.ker δ)).val i
    rw [hδt]
    exact hχtp i

end
end Dubon2026
