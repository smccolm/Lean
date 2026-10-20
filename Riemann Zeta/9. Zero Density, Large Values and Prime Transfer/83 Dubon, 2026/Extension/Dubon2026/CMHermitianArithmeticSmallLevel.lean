import Dubon2026.CMHermitianArithmeticFiniteness
import Dubon2026.NumberFieldFiniteAdelicMatrixProjection
import Dubon2026.SmallLevelFromFiniteStabilizers
import Mathlib.Topology.Algebra.Group.Units

/-! # Smallness for the original definite Hermitian arithmetic group

This derives the DUB-17 arithmetic stabilizer condition from definiteness
of the specified CM form, compactness of the finite level and its
torsion-free image at one finite place. The source form, local level and
finite double-coset realization are still required separately.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder

variable {K ι : Type*} [Field K] [NumberField K] [IsCMField K]
variable [Fintype ι] [DecidableEq ι]

/-- The original finite-adelic embedding of the matrices preserving the specified CM form. -/
def cmHermitianFiniteAdeleHom (H : Matrix ι ι K) :
    cmHermitianUnitaryGroup H →* (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ :=
  (Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix.toMonoidHom).comp
    (cmHermitianUnitaryGroup H).subtype

/-- The original Hermitian arithmetic embedding remains faithful at every finite completion. -/
theorem cmHermitian_finitePlace_faithful (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective
      ((numberFieldFiniteAdelicMatrixProjection K ι v).comp (cmHermitianFiniteAdeleHom H)) := by
  intro a b h
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact (algebraMap K (v.adicCompletion K)).injective
    (congrArg (fun u : (Matrix ι ι (v.adicCompletion K))ˣ => u.val i j) h)

/-- Compact levels have finite stabilizers in the original definite Hermitian arithmetic group. -/
theorem cmHermitian_compactLevel_stabilizer_finite
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (U : Subgroup (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ)
    (hU : IsCompact (U : Set (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ))
    (g : (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ) :
    Finite (U.comap ((MulAut.conj g⁻¹).toMonoidHom.comp (cmHermitianFiniteAdeleHom H))) := by
  let F : (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ →
      Matrix ι ι (FiniteAdeleRing (𝓞 K) K) := fun u => (g * u * g⁻¹).val
  have hF : Continuous F := Units.continuous_val.comp
    ((continuous_const.mul continuous_id).mul continuous_const)
  have hf := cmHermitian_compactArithmetic_finite H hH (F '' (U : Set _)) (hU.image hF)
  apply Set.Finite.to_subtype
  apply hf.subset
  intro a ha
  refine ⟨g⁻¹ * cmHermitianFiniteAdeleHom H a * g, ha, ?_⟩
  change (g * (g⁻¹ * cmHermitianFiniteAdeleHom H a * g) * g⁻¹).val = _
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  rfl

/-- The exact one-place smallness implication retains the supplied definite Hermitian form. -/
theorem cmHermitian_smallLevel_of_local_torsionFree
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (U : Subgroup (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ)
    (hU : IsCompact (U : Set (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ))
    (v : HeightOneSpectrum (𝓞 K))
    [IsMulTorsionFree (U.map (numberFieldFiniteAdelicMatrixProjection K ι v))] :
    ∀ (g : (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ) (u : U),
      g * u.val * g⁻¹ ∈ (cmHermitianFiniteAdeleHom H).range → u = 1 :=
  smallLevel_of_finite_stabilizers_local_torsionFree (cmHermitianFiniteAdeleHom H) U
    (numberFieldFiniteAdelicMatrixProjection K ι v) (cmHermitian_finitePlace_faithful H v)
    (cmHermitian_compactLevel_stabilizer_finite H hH U hU)

end
end Dubon2026
