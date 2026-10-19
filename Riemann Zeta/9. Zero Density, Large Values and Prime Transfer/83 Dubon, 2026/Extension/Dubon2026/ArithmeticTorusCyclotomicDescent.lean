import Dubon2026.ArithmeticTorusGlobalLiftCharacters
import Dubon2026.ContinuousGaloisFiniteFactorContaining
import Dubon2026.RationalPrimeArtinianCyclotomicDescent
import Dubon2026.TameDiagonalMatrixExponent
import Dubon2026.RationalArithmeticCyclotomicCharacter

/-! The selected auxiliary prime and actual global Artinian lift determine
a unique action of its fixed prime cyclotomic quotient on inertia. The
finite factor, primitive root, residual inertia triviality and inertia
exponent are all constructed. This supplies the actual quotient action
needed by the local deformation rings serving Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

attribute [local instance] rationalArithmeticOriginalFiniteGalois rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- At the same selected auxiliary prime, the actual global Artinian lift
has a unique inertia action through the fixed cyclotomic quotient. Its
enlarged ramification set contains that auxiliary prime, as in the ramified
deformation problem. No finite-factor or exponent witness is supplied. -/
theorem rationalArithmetic_torus_global_cyclotomic_descent
    (a b : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime] (hlevel : 0 < level)
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes) (hgood : RationalArithmeticTorusAuxiliaryPrime a q degree level R p)
    [NeZero p.val]
    (hpb : (p.val : 𝓞 ℚ) ∣ b)
    {A : Type} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [TopologicalSpace A] [DiscreteTopology A]
    (eA : ResidueField A ≃+* ZMod q)
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) A)
    (hτ : Continuous τ)
    (hred : ∀ g, GeneralLinearGroup.map (eA.toRingHom.comp (residue A))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property g)) :
    ∃! θ : (ZMod p.val)ˣ →* GeneralLinearGroup (Fin (degree + 1)) A,
      ∀ g ∈ rationalPrimeNormInertia p.val p.property,
        θ (rationalPrimeCyclotomicCharacter p.val p.property p.val g) =
          τ (rationalPrimeArithmeticRestriction b p.val p.property g) := by
  letI : CharP (ResidueField A) q := charP_of_injective_ringHom (f := eA.symm.toRingHom) eA.symm.injective q
  have hm : p.val ≡ 1 [MOD q] := hgood.2.1.of_dvd (dvd_pow_self q (Nat.ne_of_gt hlevel))
  have hpone : (p.val : ZMod q) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff p.val 1 q).mpr hm
  have hpq : p.val ≠ q := by
    intro h
    simp only [h, ZMod.natCast_self, zero_ne_one] at hpone
  have hp2 : p.val ≠ 2 := by
    intro h
    have he : (1 : ZMod q) + 1 = 1 + 0 := by simpa only [h, Nat.cast_ofNat, one_add_one_eq_two, add_zero] using hpone
    exact one_ne_zero (add_left_cancel he)
  obtain ⟨φ, δ, u, W, χ, _, _, hδ, himage, hχ, _, _, hχp⟩ :=
    rationalArithmetic_torus_global_lift_characters a b q degree level hlevel R p hgood eA τ hτ hred
  let τloc := τ.comp (rationalPrimeArithmeticRestriction b p.val p.property).toMonoidHom
  have hexp := tame_diagonal_matrix_inertia_pow_eq_one
    (rationalPrimeNormInertia p.val p.property) δ τloc W χ hχ himage
    p.val p.property.one_lt.le hχp
  let U := rationalUnramifiedExtension b
  obtain ⟨ζ, hζ⟩ := originalQUnramifiedUnion_exists_primitiveRoot
    (Ω := AlgebraicClosure ℚ) b p.val hpb
  let C := originalPrimitiveRootStage ℚ U hζ
  let τc : Gal(U/ℚ) →ₜ* GeneralLinearGroup (Fin (degree + 1)) A := ⟨τ, hτ⟩
  obtain ⟨F, hCF, ψ, hψ⟩ := continuous_galois_finite_factor_containing τc C
  letI : NumberField F := NumberField.of_module_finite ℚ F
  let ζF : F := IntermediateField.inclusion hCF (originalPrimitiveRootStageRoot ℚ U hζ)
  let f := rationalPrimeArithmeticOriginalEmbedding b p.val p.property
  let e : F →+* rationalPrimeLocalClosure p.val p.property := f.comp (algebraMap F U)
  have hζF : IsPrimitiveRoot (e ζF) p.val := hζ.map_of_injective f.injective
  let r := (AlgEquiv.restrictNormalHom F).comp
    (rationalPrimeArithmeticRestriction b p.val p.property).toMonoidHom
  have he (g : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property))
      (x : F) : e (r g x) = g (e x) := by
    have hr := (rationalPrimeArithmeticRestriction b p.val p.property g).restrictNormal_commutes F x
    exact (congrArg f hr).trans
      (rationalPrimeArithmeticRestriction_commutes b p.val p.property g (algebraMap F U x))
  have hker : r.ker ≤ (ψ.comp r).ker := by
    intro g hg
    change ψ (r g) = 1
    rw [show r g = 1 from hg]
    exact ψ.map_one
  let ρ := QuotientGroup.lift r.ker (ψ.comp r) hker
  have hρ (g : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property)) :
      ρ (QuotientGroup.mk' r.ker g) = τloc g := hψ _
  have hiner := rationalArithmetic_regular_auxiliary_inertia a q level R p (hgood.regular a q degree level R p)
  have hres : ∀ g ∈ (rationalPrimeNormInertia p.val p.property).map (QuotientGroup.mk' r.ker),
      GeneralLinearGroup.map (residue A) (ρ g) = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hρ]
    have hz := (hred g).trans (hiner hg)
    apply Units.ext
    ext i j
    apply eA.injective
    have hz' := congrArg (fun X : GeneralLinearGroup (Fin (degree + 1)) (ZMod q) => X.val i j) hz
    simpa [Matrix.one_apply] using hz'
  have hpow : ∀ g ∈ (rationalPrimeNormInertia p.val p.property).map (QuotientGroup.mk' r.ker),
      ρ g ^ (p.val - 1) = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hρ]
    exact hexp g hg
  obtain ⟨θ, hθ, huniq⟩ := rationalPrime_artinian_cyclotomic_inertia_descent
    p.val p.property hp2 q (Fact.out : q.Prime) ((Nat.coprime_primes p.property (Fact.out : q.Prime)).mpr hpq)
    e r he ζF hζF ρ hres hpow
  refine ⟨θ, fun g hg => (hθ g hg).trans (hρ g), ?_⟩
  intro θ' hθ'
  exact huniq θ' (fun g hg => (hθ' g hg).trans (hρ g).symm)

end
end Dubon2026
