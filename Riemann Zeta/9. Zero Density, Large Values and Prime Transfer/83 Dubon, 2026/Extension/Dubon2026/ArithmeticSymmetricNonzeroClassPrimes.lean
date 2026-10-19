import Dubon2026.ArithmeticSymmetricKernelDetection
import Dubon2026.SymmetricRegularCommutingTrace
import Dubon2026.ArithmeticSymmetricTraceFrobenius

/-! Regular auxiliary primes detecting nonzero native twisted dual classes
of the original symmetric residual representation. The scalar-kernel and
commuting trace-test hypotheses are now derived. DUB-17 still needs the
actual modular rank-two representation and its large residual image, the
finite prime-family consumer, and arithmetic lifting/automorphy. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField MatrixGroups
attribute [local instance] rationalArithmeticOriginalFiniteGalois

/-- Every nonzero original continuous cyclotomic-adjoint class of the
actual symmetric power is detected at a good congruence prime outside
any finite set, with regular residual Frobenius at that same prime.
The finite Galois factor and literal original Frobenius equality are
retained. No scalar-kernel value or commuting trace witness is assumed. -/
theorem rationalArithmetic_symmetric_nonzero_class_regular_primes
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree level : ℕ) [Fact q.Prime]
    [NeZero (2 : ZMod q)] [NeZero (3 : ZMod q)]
    (hqa : (q : 𝓞 ℚ) ∣ a) (hsize : 2 * degree < q - 1)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) (ZMod q))
    (hρ : Continuous ρ)
    (himage : (SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod q)).range ≤ ρ.range)
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep
      ((homogeneousSymmetricGL degree).comp ρ)
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom))
    (hc : (Submodule.Quotient.mk c : ContinuousRepresentationH1
      (matrixTraceZeroCharacterRep ((homogeneousSymmetricGL degree).comp ρ)
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous ((homogeneousSymmetricGL degree).comp ρ)
        ((homogeneousSymmetricGL_continuous degree).comp hρ)
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) ≠ 0) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
    let R := (homogeneousSymmetricGL degree).comp ρ
    let hR := (homogeneousSymmetricGL_continuous degree).comp hρ
    ∃ F : FiniteGaloisIntermediateField ℚ U,
      ∃ ψ : Gal(F/ℚ) →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q),
        (∀ w : Gal(U/ℚ), ψ (AlgEquiv.restrictNormalHom F w) = R w) ∧
        (letI : NumberField F := NumberField.of_module_finite ℚ F
         ∀ S : Finset ℕ, ∃ p : ℕ, ∃ hp : p.Prime,
           p ∉ S ∧ ¬ (p : 𝓞 ℚ) ∣ a ∧ p ≡ 1 [MOD q ^ level] ∧
           Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}) ∧
           (∃ γ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp),
             Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)}) =
               ConjClasses.mk (AlgEquiv.restrictNormalHom F
                 (rationalPrimeArithmeticRestriction a p hp γ)) ∧
             (R (rationalPrimeArithmeticRestriction a p hp γ)).val.charpoly.Separable) ∧
           rationalPrimeCyclotomicAdjointH1Restriction a q hqa p hp R hR
             (Submodule.Quotient.mk c) ≠ 0) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  let R := (homogeneousSymmetricGL degree).comp ρ
  let hR := (homogeneousSymmetricGL_continuous degree).comp hρ
  let χ := rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)
  let A := matrixTraceZeroCharacterRep R χ.toMonoidHom
  let hA := matrixTraceZeroCharacterAction_continuous R hR χ.toMonoidHom χ.continuous
  let Rres : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup (Fin (degree + 1)) (ZMod q) := ⟨R, hR⟩
  have hprimes := rationalArithmetic_exists_regular_detecting_cocycle
    a ha q (level + 1) hqa A hA Rres c
  obtain ⟨ζ, hζ, F, ψ, hψ, hF⟩ := hprimes
  have hkernel := rationalArithmetic_symmetricH1_exists_nonzero_root_kernel
    a q degree level hqa ρ hρ himage c hc
  have hkernelζ := hkernel ζ hζ
  obtain ⟨τ, hτζ, hρτ, hcτ⟩ := hkernelζ
  have hdim : degree + 1 < q := by have := (Fact.out : q.Prime).two_le; omega
  have hsize' : 2 * degree < Nat.card (ZMod q) - 1 := by simpa only [Nat.card_zmod] using hsize
  have htests := finiteSymmetric_exists_regular_commuting_trace q degree hsize' hdim
  have htestτ := htests (c.val τ) hcτ
  obtain ⟨s, hs, M, hM, htrace⟩ := htestτ
  have himageR : ((homogeneousSymmetricGL (R := ZMod q) degree).comp
      SpecialLinearGroup.toGL).range ≤ R.range := by
    rintro y ⟨s, rfl⟩
    obtain ⟨g, hg⟩ := himage (show SpecialLinearGroup.toGL s ∈
      (SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod q)).range from ⟨s, rfl⟩)
    exact ⟨g, congrArg (homogeneousSymmetricGL degree) hg⟩
  have hlift := galois_symmetricSL2_exists_root_fixing_lift
    (F := ℚ) (Ω := U) (K := ZMod q) degree R himageR (m := q ^ (level + 1)) hζ s
  obtain ⟨g, hgζ, hg⟩ := hlift
  change R g = homogeneousSymmetricGL degree (SpecialLinearGroup.toGL s) at hg
  have hRg : (R g).val.charpoly.Separable := by rw [hg]; exact hs
  have hRτ : R τ = 1 := by change homogeneousSymmetricGL degree (ρ τ) = 1; rw [hρτ, map_one]
  let H : Subgroup (rationalArithmeticGaloisGroup a) := MulAction.stabilizer Gal(U/ℚ) ζ
  have hgH : g ∈ H := MulAction.mem_stabilizer_iff.mpr hgζ
  have hτH : τ ∈ H := MulAction.mem_stabilizer_iff.mpr hτζ
  have hχg : χ g = 1 := rationalArithmeticCyclotomicCoefficient_eq_one_of_fixed_power_root
    a q level hqa (ZMod q) hζ g hgζ
  have hχτ : χ τ = 1 := rationalArithmeticCyclotomicCoefficient_eq_one_of_fixed_power_root
    a q level hqa (ZMod q) hζ τ hτζ
  have hscalar : (R τ).val = (1 : ZMod q) • (1 : Matrix (Fin (degree + 1)) (Fin (degree + 1)) (ZMod q)) := by
    rw [hRτ]; simp
  have hMg : (R g).val * M.val = M.val * (R g).val := by rw [hg]; exact hM
  have hdetect := traceCocycle_exists_detecting_kernel_translate
    R χ.toMonoidHom c.val H g τ hgH hτH hχg hχτ
  have hdetect' := hdetect 1 hscalar M hMg htrace
  obtain ⟨σ, hσH, hσ, hcσ⟩ := hdetect'
  have hσζ : (show Gal(U/ℚ) from σ) ζ = ζ := by
    change (show Gal(U/ℚ) from σ) ∈ MulAction.stabilizer Gal(U/ℚ) ζ at hσH
    exact MulAction.mem_stabilizer_iff.mp hσH
  have hσregular : (R σ).val.charpoly.Separable := by
    rcases hσ with rfl | rfl
    · exact hRg
    · rw [map_mul, hRτ, one_mul]; exact hRg
  letI : Algebra ℚ F := F.algebra'
  letI : NumberField F := NumberField.of_module_finite ℚ F
  let ψres := (MonoidHom.fst (GeneralLinearGroup (Fin (degree + 1)) (ZMod q)) (Equiv.Perm A)).comp ψ
  have hψres : ∀ w : Gal(U/ℚ), ψres (AlgEquiv.restrictNormalHom F w) = R w := by
    intro w
    change (ψ (AlgEquiv.restrictNormalHom F w)).1 = R w
    rw [hψ]; rfl
  refine ⟨F, ψres, hψres, ?_⟩
  intro S
  have hselected := hF σ hσζ hcσ hσregular S
  obtain ⟨p, hp, hpS, hpa, hmod, hunr, hlocal, hne⟩ := hselected
  refine ⟨p, hp, hpS, hpa, hmod.of_dvd (pow_dvd_pow q (Nat.le_succ level)), hunr, hlocal, ?_⟩
  exact rationalPrimeCyclotomicAdjointH1Restriction_ne_zero_of_original
    a q hqa R hR p hp (Submodule.Quotient.mk c) hne

end
end Dubon2026
