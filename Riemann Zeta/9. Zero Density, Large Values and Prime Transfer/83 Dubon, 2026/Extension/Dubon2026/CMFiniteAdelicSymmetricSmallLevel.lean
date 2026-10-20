import Dubon2026.CMFiniteAdelicCyclotomicSmallLevel
import Dubon2026.SymmetricAdjointCyclotomicSeparation

/-! The actual residual symmetric-power adjoint supplies the source
smallness prime and compact open unitary level. Full SL2 image and the
large coefficient prime derive the primitive-root noncontainment condition. -/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField ComplexOrder

variable {k : Type} [Field k] [TopologicalSpace k] [DiscreteTopology k]

/-- The original finite-coefficient adjoint operators carry the discrete residual topology. -/
local instance symmetricAdjointOperatorTopology (n : ℕ) :
    TopologicalSpace (Module.End k (Matrix (Fin (n + 1)) (Fin (n + 1)) k))ˣ := ⊥

/-- The chosen topology on the original adjoint operators is discrete. -/
local instance symmetricAdjointOperatorDiscrete (n : ℕ) :
    DiscreteTopology (Module.End k (Matrix (Fin (n + 1)) (Fin (n + 1)) k))ˣ := ⟨rfl⟩

/-- The actual full symmetric-power adjoint, with its genuine discrete residual topology and continuity inherited from the original rank-two representation. -/
def continuousSymmetricAdjoint {G : Type} [Group G] [TopologicalSpace G]
    (ρ : G →ₜ* GeneralLinearGroup (Fin 2) k) (n : ℕ) :
    G →ₜ* (Module.End k (Matrix (Fin (n + 1)) (Fin (n + 1)) k))ˣ :=
  (⟨(matrixAdjointRepresentation (homogeneousSymmetricGL n)).asGroupHom,
    continuous_of_discreteTopology⟩ : GeneralLinearGroup (Fin 2) k →ₜ*
      (Module.End k (Matrix (Fin (n + 1)) (Fin (n + 1)) k))ˣ).comp ρ

/-- The constructed continuous map has exactly the original symmetric-power full adjoint as its underlying group homomorphism. -/
theorem continuousSymmetricAdjoint_toMonoidHom {G : Type} [Group G] [TopologicalSpace G]
    (ρ : G →ₜ* GeneralLinearGroup (Fin 2) k) (n : ℕ) :
    (continuousSymmetricAdjoint ρ n).toMonoidHom =
      (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp ρ.toMonoidHom)).asGroupHom :=
  (matrixAdjointRepresentation_comp_asGroupHom ρ.toMonoidHom (homogeneousSymmetricGL n)).symm

/-- The original residual rank-two image constructs the source auxiliary prime and actual small unitary level, with root noncontainment proved rather than supplied. -/
theorem cmFiniteAdelic_exists_symmetric_small_level
    (K : Type) [Field K] [NumberField K] [IsCMField K]
    {ι : Type*} {Ω : Type} [Fintype ι] [DecidableEq ι]
    [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    [NeZero (2 : k)] [NeZero (3 : k)]
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (ρ : Gal(Ω/K) →ₜ* GeneralLinearGroup (Fin 2) k) (n l : ℕ) [Fact l.Prime]
    {z : Ω} (hz : IsPrimitiveRoot z l)
    (himage : (SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range ≤ ρ.toMonoidHom.range)
    (hlarge : 2 * Module.finrank ℚ K < l - 1) :
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
  exact symmetricAdjoint_primitiveRoot_not_mem_fixedField K Ω k ρ.toMonoidHom n l hz himage hlarge

end
end Dubon2026
