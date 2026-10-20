import Dubon2026.FiniteBaseCMRepresentationExtension
import Dubon2026.PolarizedInvolutionAction

/-! The exact CHT extension of original CM matrices and multiplier by a
symmetric conjugate-duality matrix. The arithmetic component, real-place
involution, continuity and odd similitude are derived. The CM matrix
representation and its conjugate-duality identity remain explicit inputs
to be constructed from the modular form on DUB-17's remaining chain. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the polarized CM extension. -/
local instance finiteBaseCMPolarizedUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]
  {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [TopologicalSpace R]
  (r : FiniteBaseCMKernel a F K →ₜ* (GeneralLinearGroup ι R × Rˣ))

/-- The original CM matrices and multiplier enter the identity component continuously. -/
def finiteBaseCMIdentityRepresentation : FiniteBaseCMKernel a F K →ₜ* PolarizedGaloisGroup ι R :=
  ⟨polarizedIdentityComponent.comp r.toMonoidHom, by
    apply (continuous_polarized_iff_coordinates _).mpr
    exact ⟨r.continuous.fst, r.continuous.snd, continuous_const⟩⟩

variable (B : GeneralLinearGroup ι R) (hB : B.val.transpose = B.val)
  (hpol : ∀ g, r ((finiteBaseCMGroupSplitting a F K).conjAct
      (Multiplicative.ofAdd (1 : ZMod 2)) g) = (B, 1) * polarizedSwitch (r g) * (B, 1)⁻¹)

include hpol in
/-- The single original conjugate-duality identity gives every semidirect compatibility equation. -/
theorem finiteBaseCMPolarizedCompatibility (z : Multiplicative (ZMod 2)) :
    (finiteBaseCMIdentityRepresentation a F K r).toMonoidHom.comp
        ((finiteBaseCMGroupSplitting a F K).conjAct z).toMonoidHom =
      (MulAut.conj (polarizedInvolutionAction B hB z)).toMonoidHom.comp
        (finiteBaseCMIdentityRepresentation a F K r).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  change polarizedIdentityComponent (r ((finiteBaseCMGroupSplitting a F K).conjAct z g)) =
    polarizedInvolutionAction B hB z * polarizedIdentityComponent (r g) *
      (polarizedInvolutionAction B hB z)⁻¹
  by_cases hz : z.toAdd = 0
  · have hz' : z = 1 := hz
    subst z
    simp only [map_one, MulAut.one_apply, one_mul, inv_one, mul_one]
  · have hz' : z = Multiplicative.ofAdd (1 : ZMod 2) := by
      change z.toAdd = (1 : ZMod 2)
      generalize z.toAdd = x at hz ⊢
      fin_cases x
      · exact (hz rfl).elim
      · rfl
    rw [hz', polarizedInvolutionAction_generator, polarizedInvolution_conjugate, hpol]

variable [Nonempty ι] [Nontrivial R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]

/-- The original conjugate-dual CM representation gives an actual continuous polarized arithmetic representation. -/
@[irreducible] def finiteBaseCMPolarizedExtension :
    finiteBaseArithmeticGaloisGroup a F →ₜ* PolarizedGaloisGroup ι R :=
  finiteBaseCMRepresentationExtension a F K (finiteBaseCMIdentityRepresentation a F K r)
    (polarizedInvolutionAction B hB) (finiteBaseCMPolarizedCompatibility a F K r B hB hpol)

/-- The constructed polarized representation retains every original CM matrix and multiplier. -/
theorem finiteBaseCMPolarizedExtension_kernel (g : FiniteBaseCMKernel a F K) :
    finiteBaseCMPolarizedExtension a F K r B hB hpol g.val = polarizedIdentityComponent (r g) := by
  unfold finiteBaseCMPolarizedExtension
  exact finiteBaseCMRepresentationExtension_kernel a F K _ _ _ g

/-- Its component is the actual quadratic restriction character, with no component certificate assumed. -/
theorem finiteBaseCMPolarizedExtension_component (g : finiteBaseArithmeticGaloisGroup a F) :
    polarizedComponent (finiteBaseCMPolarizedExtension a F K r B hB hpol g) =
      finiteBaseQuadraticComponent a F K g := by
  unfold finiteBaseCMPolarizedExtension
  rw [finiteBaseCMRepresentationExtension_apply, map_mul]
  change 1 * polarizedComponent (polarizedInvolutionAction B hB (finiteBaseQuadraticComponent a F K g)) = _
  rw [one_mul, polarizedInvolutionAction_component]

/-- The original real-place section has the specified symmetric polarization matrix. -/
theorem finiteBaseCMPolarizedExtension_real_place :
    finiteBaseCMPolarizedExtension a F K r B hB hpol (finiteBaseRealConjugation a F) =
      polarizedInvolution B := by
  have he : finiteBaseCMComponentSection a F (Multiplicative.ofAdd (1 : ZMod 2)) =
      finiteBaseRealConjugation a F := by
    change (if (1 : ZMod 2) = 0 then 1 else finiteBaseRealConjugation a F) = finiteBaseRealConjugation a F
    norm_num
  rw [← he]
  unfold finiteBaseCMPolarizedExtension
  rw [finiteBaseCMRepresentationExtension_section, polarizedInvolutionAction_generator]

/-- The actual arithmetic real-place image has the source odd similitude. -/
theorem finiteBaseCMPolarizedExtension_odd :
    polarizedSimilitude (finiteBaseCMPolarizedExtension a F K r B hB hpol
      (finiteBaseRealConjugation a F)) = -1 := by
  rw [finiteBaseCMPolarizedExtension_real_place, polarizedInvolution_similitude]

end
end Dubon2026
