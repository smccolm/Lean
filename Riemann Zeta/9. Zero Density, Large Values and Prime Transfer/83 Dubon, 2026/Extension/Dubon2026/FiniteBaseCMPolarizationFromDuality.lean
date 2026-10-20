import Dubon2026.FiniteBaseCMConjugation
import Dubon2026.PolarizedTwistedDual
import Dubon2026.FiniteBaseCMCharacterComparison

/-! Extend the actual CM trace matrices once their symmetric duality has
been proved. The existing arithmetic extension supplies the whole group,
its continuity, original component and prescribed similitude. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the CM duality extension. -/
local instance finiteBaseCMDualityExtensionUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]
  {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [TopologicalSpace R]

omit [TopologicalSpace R] in
/-- The original arithmetic character is invariant under actual CM
conjugation, so matrix duality gives the full matrix-multiplier identity. -/
theorem finiteBaseCM_duality_pair
    (τ : FiniteBaseCMKernel a F K →* GeneralLinearGroup ι R)
    (ν : finiteBaseArithmeticGaloisGroup a F →* Rˣ)
    (B : GeneralLinearGroup ι R)
    (hB : ∀ g, τ (finiteBaseCMConjugation a F K g) =
      B * polarizedTwistedDual τ (ν.comp (FiniteBaseCMKernel a F K).subtype) g * B⁻¹)
    (g : FiniteBaseCMKernel a F K) :
    (τ ((finiteBaseCMGroupSplitting a F K).conjAct (Multiplicative.ofAdd (1 : ZMod 2)) g),
      ν (((finiteBaseCMGroupSplitting a F K).conjAct (Multiplicative.ofAdd (1 : ZMod 2)) g).val)) =
      (B, 1) * polarizedSwitch (τ g, ν g.val) * (B, 1)⁻¹ := by
  have hc := DFunLike.congr_fun (finiteBaseCMConjugation_eq a F K) g
  change finiteBaseCMConjugation a F K g =
    (finiteBaseCMGroupSplitting a F K).conjAct (Multiplicative.ofAdd (1 : ZMod 2)) g at hc
  apply Prod.ext
  · change τ ((finiteBaseCMGroupSplitting a F K).conjAct (Multiplicative.ofAdd (1 : ZMod 2)) g) =
      B * (GeneralLinearGroup.scalar ι (ν g.val) * polarizedContragredient (τ g)) * B⁻¹
    rw [← hc]
    exact hB g
  · change ν (((finiteBaseCMGroupSplitting a F K).conjAct (Multiplicative.ofAdd (1 : ZMod 2)) g).val) =
      1 * ν g.val * 1⁻¹
    rw [← hc]
    change ν (finiteBaseRealConjugation a F * g.val * (finiteBaseRealConjugation a F)⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    simp only [one_mul, inv_one, mul_one]
    rw [mul_right_comm, mul_inv_cancel, one_mul]

variable [Nonempty ι] [Nontrivial R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]

/-- Actual continuous CM matrices with proved symmetric conjugate duality
extend to the original arithmetic group with its exact component,
real-place matrix and prescribed odd similitude. -/
theorem finiteBaseCM_polarized_of_duality
    (τ : FiniteBaseCMKernel a F K →ₜ* GeneralLinearGroup ι R)
    (ν : finiteBaseArithmeticGaloisGroup a F →* Rˣ)
    (hν : Continuous (ν.comp (FiniteBaseCMKernel a F K).subtype))
    (hνc : ν (finiteBaseRealConjugation a F) = -1)
    (B : GeneralLinearGroup ι R) (hsym : B.val.transpose = B.val)
    (hB : ∀ g, τ (finiteBaseCMConjugation a F K g) =
      B * polarizedTwistedDual τ.toMonoidHom (ν.comp (FiniteBaseCMKernel a F K).subtype) g * B⁻¹) :
    ∃ σT : finiteBaseArithmeticGaloisGroup a F →ₜ* PolarizedGaloisGroup ι R,
      (∀ g : FiniteBaseCMKernel a F K, σT g.val = polarizedIdentityComponent (τ g, ν g.val)) ∧
      σT (finiteBaseRealConjugation a F) = polarizedInvolution B ∧
      (∀ g, polarizedComponent (σT g) = finiteBaseQuadraticComponent a F K g) ∧
      (∀ g, polarizedSimilitude (σT g) = ν g) := by
  let r : FiniteBaseCMKernel a F K →ₜ* (GeneralLinearGroup ι R × Rˣ) :=
    ⟨τ.toMonoidHom.prod (ν.comp (FiniteBaseCMKernel a F K).subtype), τ.continuous.prodMk hν⟩
  have hp : ∀ g, r ((finiteBaseCMGroupSplitting a F K).conjAct
      (Multiplicative.ofAdd (1 : ZMod 2)) g) = (B, 1) * polarizedSwitch (r g) * (B, 1)⁻¹ :=
    finiteBaseCM_duality_pair a F K τ.toMonoidHom ν B hB
  refine ⟨finiteBaseCMPolarizedExtension a F K r B hsym hp, ?_, ?_, ?_, ?_⟩
  · exact finiteBaseCMPolarizedExtension_kernel a F K r B hsym hp
  · exact finiteBaseCMPolarizedExtension_real_place a F K r B hsym hp
  · exact finiteBaseCMPolarizedExtension_component a F K r B hsym hp
  · exact finiteBaseCMPolarizedExtension_similitude a F K r B hsym hp ν (fun _ => rfl) hνc

end
end Dubon2026
