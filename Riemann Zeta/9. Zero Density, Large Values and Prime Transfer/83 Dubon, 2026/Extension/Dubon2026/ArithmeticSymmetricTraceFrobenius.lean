import Dubon2026.ArithmeticRegularCocycleFrobenius
import Dubon2026.ArithmeticSymmetricTraceDetection

/-! The same original rational auxiliary prime has regular residual
Frobenius and detects the native twisted trace cohomology class. This is
the DUB-17 prime-selection dependency of arithmetic patching. Existence of
the residual scalar-kernel trace test remains explicit. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField MatrixGroups
attribute [local instance] rationalArithmeticOriginalFiniteGalois

/-- A large symmetric SL2 residual image and the scalar-kernel trace
test produce the same good congruence prime with regular actual Frobenius
and nonzero native cyclotomic adjoint H1 restriction. The common original
finite Galois factor, its representation equality and its unramifiedness
are retained, so regularity applies to Frobenius itself. -/
theorem rationalArithmetic_symmetric_trace_exists_regular_frobenius
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree level : ℕ) [Fact q.Prime]
    [NeZero (2 : ZMod q)] [NeZero (3 : ZMod q)]
    (hqa : (q : 𝓞 ℚ) ∣ a) (hsize : 2 * degree < Nat.card (ZMod q) - 1)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (hρ : Continuous ρ)
    (himage : ((homogeneousSymmetricGL (R := ZMod q) degree).comp
      Matrix.SpecialLinearGroup.toGL).range ≤ ρ.range)
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep ρ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
    ∃ ζ : U, IsPrimitiveRoot ζ (q ^ (level + 1)) ∧
      ∃ g : Gal(U/ℚ), g ζ = ζ ∧ (ρ g).val.charpoly.Separable ∧
        ∃ F : FiniteGaloisIntermediateField ℚ U,
          ∃ ψ : Gal(F/ℚ) →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q),
            (∀ w : Gal(U/ℚ), ψ (AlgEquiv.restrictNormalHom F w) = ρ w) ∧
            (letI : NumberField F := NumberField.of_module_finite ℚ F
             ∀ τ : Gal(U/ℚ), τ ζ = ζ →
               ∀ d : ZMod q, (ρ τ).val = d • (1 : Matrix (Fin (degree + 1)) (Fin (degree + 1)) (ZMod q)) →
                 ∀ M : matrixTraceZeroSubmodule (Fin (degree + 1)) (ZMod q),
                   (ρ g).val * M.val = M.val * (ρ g).val →
                   Matrix.trace ((c.val τ).val * M.val) ≠ 0 →
                   ∀ S : Finset ℕ, ∃ p : ℕ, ∃ hp : p.Prime,
                     p ∉ S ∧ ¬ (p : 𝓞 ℚ) ∣ a ∧ p ≡ 1 [MOD q ^ level] ∧
                     Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}) ∧
                     (∃ γ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp),
                       Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)}) =
                         ConjClasses.mk (AlgEquiv.restrictNormalHom F
                           (rationalPrimeArithmeticRestriction a p hp γ)) ∧
                       (ρ (rationalPrimeArithmeticRestriction a p hp γ)).val.charpoly.Separable) ∧
                     rationalPrimeCyclotomicAdjointH1Restriction a q hqa p hp ρ hρ
                       (Submodule.Quotient.mk c) ≠ 0) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  let χ := rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)
  let A := matrixTraceZeroCharacterRep ρ χ.toMonoidHom
  let hA := matrixTraceZeroCharacterAction_continuous ρ hρ χ.toMonoidHom χ.continuous
  let ρres : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup (Fin (degree + 1)) (ZMod q) := ⟨ρ, hρ⟩
  have hprimes := rationalArithmetic_exists_regular_detecting_cocycle
    a ha q (level + 1) hqa A hA ρres c
  obtain ⟨ζ, hζ, F, ψ, hψ, hF⟩ := hprimes
  have hregulars := galois_exists_root_fixing_symmetric_regular
    (F := ℚ) (Ω := U) (K := ZMod q) degree hsize ρ himage
    (m := q ^ (level + 1)) (ζ := ζ)
  have hregularζ := hregulars hζ
  obtain ⟨u, hu, g, hg, hdiag, hregular⟩ := hregularζ
  letI : Algebra ℚ F := F.algebra'
  letI : NumberField F := NumberField.of_module_finite ℚ F
  let ψres := (MonoidHom.fst (GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (Equiv.Perm A)).comp ψ
  have hψres : ∀ w : Gal(U/ℚ), ψres (AlgEquiv.restrictNormalHom F w) = ρ w := by
    intro w
    change (ψ (AlgEquiv.restrictNormalHom F w)).1 = ρ w
    rw [hψ]
    rfl
  refine ⟨ζ, hζ, g, hg, hregular, F, ψres, hψres, ?_⟩
  intro τ hτ d hscalar M hM hc S
  let H : Subgroup (rationalArithmeticGaloisGroup a) := MulAction.stabilizer Gal(U/ℚ) ζ
  have hgH : g ∈ H := MulAction.mem_stabilizer_iff.mpr hg
  have hτH : τ ∈ H := MulAction.mem_stabilizer_iff.mpr hτ
  have hχg : χ g = 1 :=
    rationalArithmeticCyclotomicCoefficient_eq_one_of_fixed_power_root a q level hqa (ZMod q) hζ g hg
  have hχτ : χ τ = 1 :=
    rationalArithmeticCyclotomicCoefficient_eq_one_of_fixed_power_root a q level hqa (ZMod q) hζ τ hτ
  have hdetect := traceCocycle_exists_detecting_kernel_translate ρ χ.toMonoidHom c.val
    H g τ hgH hτH hχg hχτ
  have hdetect' := hdetect d hscalar M hM hc
  obtain ⟨σ, hσH, hσ, hcσ⟩ := hdetect'
  have hσζ : (show Gal(U/ℚ) from σ) ζ = ζ := by
    change (show Gal(U/ℚ) from σ) ∈ MulAction.stabilizer Gal(U/ℚ) ζ at hσH
    exact MulAction.mem_stabilizer_iff.mp hσH
  have hσregular : (ρ σ).val.charpoly.Separable := by
    rcases hσ with hσ | hσ
    · rw [hσ]
      exact hregular
    · rw [hσ]
      apply symmetric_scalar_translate_charpoly_separable degree ρ g τ u _ hdiag d hscalar
      rwa [hu]
  have hselected := hF σ hσζ hcσ hσregular S
  obtain ⟨p, hp, hpS, hpa, hmod, hunr, hlocal, hne⟩ := hselected
  refine ⟨p, hp, hpS, hpa, hmod.of_dvd (pow_dvd_pow q (Nat.le_succ level)), hunr, hlocal, ?_⟩
  exact rationalPrimeCyclotomicAdjointH1Restriction_ne_zero_of_original
    a q hqa ρ hρ p hp (Submodule.Quotient.mk c) hne

end
end Dubon2026
