import Dubon2026.NumberFieldFiniteAdeleDenominator
import Dubon2026.HeightOnePrimeLifting
import Dubon2026.RationalPrimePlace
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Noetherian.Basic

/-! # The integral lattice attached to an original finite adelic matrix

The carrier is exactly the number-field vectors whose inverse adelic
transform is integral at every original finite place. It is not a supplied
lattice certificate. This serves DUB-17's finite unitary arithmetic
double-coset obligation through the positive integral trace-lattice route.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- Original integral finite adeles as an algebra over the original ring of integers. -/
def numberFieldIntegralFiniteAdeleAlgebra :
    Subalgebra (𝓞 K) (FiniteAdeleRing (𝓞 K) K) where
  __ := (numberFieldIntegralFiniteAdeles K).toSubsemiring
  algebraMap_mem' d v := v.coe_mem_adicCompletionIntegers d

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The actual principal embedding on vectors, linear over the ring of integers. -/
def numberFieldAdelicVectorMap : (ι → K) →ₗ[𝓞 K] (ι → FiniteAdeleRing (𝓞 K) K) :=
  LinearMap.pi fun i =>
    ((Algebra.linearMap K (FiniteAdeleRing (𝓞 K) K)).restrictScalars (𝓞 K)).comp
      (LinearMap.proj i)

/-- The lattice cut out by the inverse of the original finite adelic matrix. -/
def numberFieldAdelicLattice (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K)) :
    Submodule (𝓞 K) (ι → K) :=
  (Submodule.pi Set.univ fun _ => (numberFieldIntegralFiniteAdeleAlgebra K).toSubmodule).comap
    (((g⁻¹).val.mulVecLin.restrictScalars (𝓞 K)).comp (numberFieldAdelicVectorMap K ι))

/-- Membership is precisely integrality of every component of the inverse adelic transform. -/
theorem numberFieldAdelicLattice_mem_iff
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K)) (x : ι → K) :
    x ∈ numberFieldAdelicLattice K ι g ↔
      ∀ i, (g⁻¹).val.mulVec (fun j => algebraMap K (FiniteAdeleRing (𝓞 K) K) (x j)) i ∈
        numberFieldIntegralFiniteAdeles K := by
  simp only [numberFieldAdelicLattice, Submodule.mem_comap, Submodule.mem_pi,
    Set.mem_univ, forall_const]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The principal vector embedding is injective. -/
theorem numberFieldAdelicVectorMap_injective :
    Function.Injective (numberFieldAdelicVectorMap K ι) := by
  obtain ⟨v, _⟩ := heightOnePrime_exists_liesOver (S := 𝓞 K)
    (rationalPrimePlace 2 Nat.prime_two)
  intro x y h
  funext i
  exact (algebraMap K (v.adicCompletion K)).injective
    (congrArg (fun z : ι → FiniteAdeleRing (𝓞 K) K => z i v) h)

end
end Dubon2026
