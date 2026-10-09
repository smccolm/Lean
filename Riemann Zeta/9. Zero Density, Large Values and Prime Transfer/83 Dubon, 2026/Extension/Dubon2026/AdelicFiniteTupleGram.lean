import Dubon2026.AdelicFiniteTupleCoefficients
import Dubon2026.AdelicUnitReferenceVector

/-! # Genuine finite-family Gram factorization for the original normalized cusp orbit -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- Unitarity expresses the actual Gram entry as the original coefficient at the relative group element. -/
theorem unitary_orbit_inner {G V : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : Representation ℂ G V) (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (x : V) (a b : G) : inner ℂ (ρ a x) (ρ b x) = inner ℂ x (ρ (a⁻¹ * b) x) := by
  rw [representation_inner_inverse ρ hρ a, ← Module.End.mul_apply, ← map_mul]

/-- A genuine group homomorphism preserves the exact relative element in an orbit Gram entry. -/
theorem groupHom_relative {G H : Type*} [Group G] [Group H] (e : G →* H) (a b : G) :
    e (a⁻¹ * b) = (e a)⁻¹ * e b := by rw [map_mul, map_inv]

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The Gram entry between two genuine original unit-reference translates is their exact normalized original coefficient at the relative group element. -/
theorem adelicCyclicUnitReference_orbit_inner (a b : RationalAdelicGL2) :
    inner ℂ (adelicCyclicHilbertRepresentation f a (adelicCyclicUnitReference f))
      (adelicCyclicHilbertRepresentation f b (adelicCyclicUnitReference f)) =
      adelicNormalizedCuspCoefficient f (a⁻¹ * b) := by
  exact (@unitary_orbit_inner RationalAdelicGL2 (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation f)
    (adelicCyclicHilbertRepresentation_inner f) (adelicCyclicUnitReference f) a b).trans
    (adelicCyclicUnitReference_coefficient f (a⁻¹ * b))

variable {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v)
  (F : PrimitiveCuspForm N k)

/-- The entire genuine finite-family mixed Gram matrix is the product of its original local Gram matrices and its full remaining-coordinate Gram matrix. -/
theorem adelicCyclicUnitReference_finiteFamily_gram
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b₁ b₂ : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    inner ℂ
      (adelicCyclicHilbertRepresentation F.toCuspForm (adelicFiniteFamilyEquiv v hv b₁)
        (adelicCyclicUnitReference F.toCuspForm))
      (adelicCyclicHilbertRepresentation F.toCuspForm (adelicFiniteFamilyEquiv v hv b₂)
        (adelicCyclicUnitReference F.toCuspForm)) =
      (∏ i, inner ℂ
        (adelicCyclicHilbertRepresentation F.toCuspForm
          (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (b₁.1 i)))
          (adelicCyclicUnitReference F.toCuspForm))
        (adelicCyclicHilbertRepresentation F.toCuspForm
          (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (b₂.1 i)))
          (adelicCyclicUnitReference F.toCuspForm))) *
      inner ℂ
        (adelicCyclicHilbertRepresentation F.toCuspForm b₁.2.val (adelicCyclicUnitReference F.toCuspForm))
        (adelicCyclicHilbertRepresentation F.toCuspForm b₂.2.val (adelicCyclicUnitReference F.toCuspForm)) := by
  have he := groupHom_relative (adelicFiniteFamilyEquiv v hv).toMonoidHom b₁ b₂
  have h := adelicNormalizedCuspCoefficient_finiteFamilyEquiv v hv F hgood (b₁⁻¹ * b₂)
  have hleft := adelicCyclicUnitReference_orbit_inner F.toCuspForm
    (adelicFiniteFamilyEquiv v hv b₁) (adelicFiniteFamilyEquiv v hv b₂)
  apply hleft.trans ((congrArg (adelicNormalizedCuspCoefficient F.toCuspForm) he.symm).trans (h.trans _))
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro i _
    have hi := groupHom_relative
      (rationalAdelicFiniteGL2Embedding.comp (finiteAdelicLocalGL2Hom (v i))) (b₁.1 i) (b₂.1 i)
    exact (congrArg (adelicNormalizedCuspCoefficient F.toCuspForm) hi).trans
      (adelicCyclicUnitReference_orbit_inner F.toCuspForm _ _).symm
  · exact (congrArg (adelicNormalizedCuspCoefficient F.toCuspForm)
      (groupHom_relative (adelicFiniteFamilyAwayGroup v).subtype b₁.2 b₂.2)).trans
      (adelicCyclicUnitReference_orbit_inner F.toCuspForm _ _).symm

end
end Dubon2026
