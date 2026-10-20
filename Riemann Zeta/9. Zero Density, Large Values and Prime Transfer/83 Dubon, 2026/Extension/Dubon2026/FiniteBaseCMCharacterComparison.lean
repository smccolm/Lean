import Dubon2026.FiniteBaseCMPolarizedExtension

/-! Derive the full residual similitude comparison from its original CM
multiplier and its value at the actual real-place involution. This removes
the arbitrary whole-group character certificate in the DUB-17 consumer. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the source similitude comparison. -/
local instance finiteBaseCMCharacterUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]

/-- Original CM subgroup values and the actual real-place value determine an arithmetic character. -/
theorem finiteBaseCMCharacter_ext {T : Type*} [Group T]
    (f g : finiteBaseArithmeticGaloisGroup a F →* T)
    (hk : ∀ n : FiniteBaseCMKernel a F K, f n.val = g n.val)
    (hc : f (finiteBaseRealConjugation a F) = g (finiteBaseRealConjugation a F)) : f = g := by
  have hs (z : Multiplicative (ZMod 2)) :
      f (finiteBaseCMComponentSection a F z) = g (finiteBaseCMComponentSection a F z) := by
    change f (if z.toAdd = 0 then 1 else finiteBaseRealConjugation a F) =
      g (if z.toAdd = 0 then 1 else finiteBaseRealConjugation a F)
    by_cases hz : z.toAdd = 0
    · rw [if_pos hz, map_one, map_one]
    · rw [if_neg hz]
      exact hc
  apply MonoidHom.ext
  intro x
  conv_lhs => rw [← finiteBaseCMKernelCoordinate_reconstruct a F K x]
  conv_rhs => rw [← finiteBaseCMKernelCoordinate_reconstruct a F K x]
  rw [map_mul, map_mul, hk, hs]

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [CommRing R] [Nontrivial R]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
  (r : FiniteBaseCMKernel a F K →ₜ* (GeneralLinearGroup ι R × Rˣ))
  (B : GeneralLinearGroup ι R) (hB : B.val.transpose = B.val)
  (hpol : ∀ g, r ((finiteBaseCMGroupSplitting a F K).conjAct
      (Multiplicative.ofAdd (1 : ZMod 2)) g) = (B, 1) * polarizedSwitch (r g) * (B, 1)⁻¹)
  (ν : finiteBaseArithmeticGaloisGroup a F →* Rˣ)
  (hνk : ∀ g : FiniteBaseCMKernel a F K, (r g).2 = ν g.val)
  (hνc : ν (finiteBaseRealConjugation a F) = -1)

include hνk hνc in
/-- The actual extended representation has the original prescribed similitude on the entire arithmetic group. -/
theorem finiteBaseCMPolarizedExtension_similitude (g : finiteBaseArithmeticGaloisGroup a F) :
    polarizedSimilitude (finiteBaseCMPolarizedExtension a F K r B hB hpol g) = ν g := by
  have he : polarizedSimilitude.comp (finiteBaseCMPolarizedExtension a F K r B hB hpol).toMonoidHom = ν := by
    apply finiteBaseCMCharacter_ext a F K
    · intro n
      change polarizedSimilitude (finiteBaseCMPolarizedExtension a F K r B hB hpol n.val) = ν n.val
      rw [finiteBaseCMPolarizedExtension_kernel, polarizedSimilitude_identityComponent, hνk]
    · change polarizedSimilitude (finiteBaseCMPolarizedExtension a F K r B hB hpol
        (finiteBaseRealConjugation a F)) = ν (finiteBaseRealConjugation a F)
      rw [finiteBaseCMPolarizedExtension_odd, hνc]
  exact DFunLike.congr_fun he g

end
end Dubon2026
