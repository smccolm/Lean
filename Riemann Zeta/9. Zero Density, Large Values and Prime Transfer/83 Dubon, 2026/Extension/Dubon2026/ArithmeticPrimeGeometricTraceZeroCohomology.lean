import Dubon2026.ArithmeticPrimeGeometricCohomologySubmodule
import Dubon2026.ContinuousTraceZeroCohomology
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # The genuine prime-local geometric condition in continuous trace-zero cohomology -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

variable (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)))

/-- The original geometric condition on genuine continuous trace-zero adjoint classes,
obtained through their actual full-adjoint inclusion. -/
def arithmeticPrimeGeometricTraceZeroClasses :
    Submodule (IsLocalRing.ResidueField O) (ContinuousTraceZeroAdjointH1 σ hσ) :=
  (arithmeticPrimeGeometricFiniteFlatClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m).comap (continuousTraceZeroH1Inclusion σ hσ)

/-- The actual geometric trace-zero submodule and original geometric full-adjoint
submodule are linearly equivalent when the original matrix dimension is nonzero in
the residue field. The proved original determinant condition supplies the range
inclusion, and existing continuous trace-zero cohomology proves injectivity. -/
def arithmeticPrimeGeometricTraceZeroEquiv
    (hn : (Fintype.card ι : IsLocalRing.ResidueField O) ≠ 0) :
    (arithmeticPrimeGeometricTraceZeroClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m) ≃ₗ[IsLocalRing.ResidueField O]
      (arithmeticPrimeGeometricFiniteFlatClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m) := by
  have hinj : Function.Injective (continuousTraceZeroH1Inclusion σ hσ) := by
    intro x y h
    apply continuousTraceZeroH1ToFixedDeterminant_injective hn σ hσ
    exact Subtype.ext h
  have hrange : (arithmeticPrimeGeometricFiniteFlatClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m) ≤
      LinearMap.range (continuousTraceZeroH1Inclusion σ hσ) := by
    intro x hx
    obtain ⟨z, hz⟩ := continuousTraceZeroH1ToFixedDeterminant_surjective σ hσ
      ⟨x, arithmeticPrimeGeometricFiniteFlatClasses_le_fixedDeterminant (L := L) a ha p hp hpa σ hσ i₀ δ hδ m hx⟩
    exact ⟨z, congrArg Subtype.val hz⟩
  exact Submodule.comap_equiv_self_of_inj_of_le hinj hrange

/-- The actual geometric trace-zero subspace is finite dimensional through its proved
linear equivalence with the constructed intrinsic arithmetic geometric condition. -/
theorem arithmeticPrimeGeometricTraceZeroClasses_finiteDimensional
    (hn : (Fintype.card ι : IsLocalRing.ResidueField O) ≠ 0) :
    Module.Finite (IsLocalRing.ResidueField O) (arithmeticPrimeGeometricTraceZeroClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m) := by
  letI := arithmeticPrimeGeometricFiniteFlatClasses_finiteDimensional (L := L) a ha p hp hpa σ hσ i₀ δ hδ m
  exact Module.Finite.equiv (arithmeticPrimeGeometricTraceZeroEquiv (L := L) a ha p hp hpa σ hσ i₀ δ hδ m hn).symm

/-- The true original geometric local condition has the same dimension in the
trace-zero and full-adjoint presentations. This is a comparison, not a numerical
Selmer dimension formula. -/
theorem arithmeticPrimeGeometricTraceZeroClasses_finrank
    (hn : (Fintype.card ι : IsLocalRing.ResidueField O) ≠ 0) :
    Module.finrank (IsLocalRing.ResidueField O) (arithmeticPrimeGeometricTraceZeroClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m) =
      Module.finrank (IsLocalRing.ResidueField O) (arithmeticPrimeGeometricFiniteFlatClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m) := by
  exact (arithmeticPrimeGeometricTraceZeroEquiv (L := L) a ha p hp hpa σ hσ i₀ δ hδ m hn).finrank_eq

end
end Dubon2026
