import Dubon2026.CMFiniteAdelicSymmetricSmallLevel
import Dubon2026.SubfieldSymmetricAdjointCyclotomicDegree

/-! The source coefficient-subfield image bounds construct the actual
symmetric-adjoint smallness prime and compact open unitary level.
BLGG 6.1.2 discharges root noncontainment in BLGG 3.6.1's prime step. -/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField ComplexOrder

variable {k k' : Type} [Field k] [Field k'] [TopologicalSpace k] [DiscreteTopology k]

attribute [local instance] symmetricAdjointOperatorTopology symmetricAdjointOperatorDiscrete

/-- The exact original coefficient-subfield image conditions and source cyclotomic degree hypothesis construct a genuine smallness prime and original compact open unitary level. -/
theorem cmFiniteAdelic_exists_subfield_symmetric_small_level
    (K : Type) [Field K] [NumberField K] [IsCMField K]
    {ι : Type*} {Ω : Type} [Fintype ι] [DecidableEq ι]
    [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (f : k' →+* k) (ρ : Gal(Ω/K) →ₜ* GeneralLinearGroup (Fin 2) k)
    (n l : ℕ) [Fact l.Prime] [CharP k' l]
    {z : Ω} (hz : IsPrimitiveRoot z l)
    (hlower : ((GeneralLinearGroup.map f).comp
      (SpecialLinearGroup.toGL (n := Fin 2) (R := k'))).range ≤ ρ.toMonoidHom.range)
    (hupper : ∀ g : Gal(Ω/K), ∃ u : kˣ, ∃ a : GeneralLinearGroup (Fin 2) k',
      ρ g = GeneralLinearGroup.scalar (Fin 2) u * GeneralLinearGroup.map f a)
    (hdegree : 2 < Module.finrank K (originalPrimitiveRootStage K Ω hz)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∃ ψ : Gal(F/K) →* (Module.End k (Matrix (Fin (n + 1)) (Fin (n + 1)) k))ˣ × (ZMod l)ˣ,
      (∀ g : Gal(Ω/K), ψ (AlgEquiv.restrictNormalHom F g) =
        (continuousSymmetricAdjoint ρ n g, hz.autToPow K g)) ∧
      (letI : NumberField F := NumberField.of_module_finite K F
       ∀ S : Finset (Ideal (𝓞 K)),
         ∃ (v : HeightOneSpectrum (𝓞 K)) (p : ℕ),
           v.asIdeal ∉ S ∧ p.Prime ∧ Fintype.card ι * Module.finrank ℚ K < p - 1 ∧
           CharP (Valued.ResidueField (v.adicCompletion K)) p ∧
           Algebra.IsUnramifiedAt ℤ v.asIdeal ∧
           Chebotarev.UnramifiedIn K F v.asIdeal ∧
           (ψ (Chebotarev.frobeniusClass K F v.asIdeal).out).1 = 1 ∧
           (ψ (Chebotarev.frobeniusClass K F v.asIdeal).out).2 ≠ 1 ∧
           Fintype.card ι < Module.finrank K (CyclotomicField p K) ∧
           IsOpen (cmFiniteAdelicPrincipalLevel K H v : Set (cmFiniteAdelicUnitaryGroup K H)) ∧
           IsCompact (cmFiniteAdelicPrincipalLevel K H v : Set (cmFiniteAdelicUnitaryGroup K H)) ∧
           Finite (DoubleCoset.Quotient (G := cmFiniteAdelicUnitaryGroup K H)
             ((cmHermitianFiniteAdeleHom H).codRestrict (cmFiniteAdelicUnitaryGroup K H)
               (cmFiniteAdelicUnitaryGroup_principal K H)).range (cmFiniteAdelicPrincipalLevel K H v)) ∧
           ∀ (g : cmFiniteAdelicUnitaryGroup K H) (u : cmFiniteAdelicPrincipalLevel K H v),
             g * u.val * g⁻¹ ∈ ((cmHermitianFiniteAdeleHom H).codRestrict
               (cmFiniteAdelicUnitaryGroup K H) (cmFiniteAdelicUnitaryGroup_principal K H)).range →
                 u = 1) := by
  apply cmFiniteAdelic_exists_cyclotomic_small_level K H hH (continuousSymmetricAdjoint ρ n) hz
  rw [continuousSymmetricAdjoint_toMonoidHom]
  exact subfieldSymmetricAdjoint_primitiveRoot_not_mem_fixedField K Ω k k' l f ρ.toMonoidHom n
    hz hlower hupper hdegree

end
end Dubon2026
