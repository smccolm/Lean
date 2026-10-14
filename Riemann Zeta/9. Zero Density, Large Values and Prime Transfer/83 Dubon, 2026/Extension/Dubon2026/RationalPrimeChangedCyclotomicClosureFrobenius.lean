import Dubon2026.LocalFieldArithmeticFrobeniusEquiv
import Dubon2026.RationalPrimeChangedCyclotomicClosureReciprocity

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction wittCyclotomicRootDVR
  rationalPrimeChangedIntegralRootDomain rationalPrimeChangedIntegralRootDVR

/-- The closure-model arithmetic Frobenius is the transported diagonal
automorphism on every element of the finite Witt compositum. -/
theorem rationalPrimeChangedCyclotomicClosureFrobenius_equiv
    (p : ℕ) (hp : p.Prime) (n a b : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (hcoprimeA : a.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hcoprimeB : b.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD
      (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)])
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha))]
    [ValuativeRel (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [TopologicalSpace (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha))]
    [(ValuativeRel.valuation (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha))]
    [Algebra.FormallyUnramified
      𝒪[rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha]
      𝒪[rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha]]
    (x : rationalPrimeChangedCyclotomicCompositum p hp n u) :
    rationalPrimeChangedCyclotomicClosureCompositumEquiv p hp n a u hu ha
        (rationalPrimeChangedCyclotomicDiagonalAlgEquiv
          p hp n a b u hu hcoprimeA hcoprimeB hab x) =
      localFieldArithmeticFrobenius
        (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)
        (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)
        (rationalPrimeChangedCyclotomicClosureCompositumEquiv p hp n a u hu ha x) := by
  let K := rationalPrimeLocalField p hp
  let E₀ : Type := rationalPrimeChangedAuxiliaryField p hp n u
  let M₀ : Type := rationalPrimeChangedCyclotomicCompositum p hp n u
  let E : Type := rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha
  let M : Type := rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha
  let eE := rationalPrimeChangedAuxiliaryClosureEquiv p hp n a u hu ha
  let eM := rationalPrimeChangedCyclotomicClosureCompositumEquiv p hp n a u hu ha
  obtain ⟨fdE₀, fdM₀, valE₀, topE₀, localE₀, extKE₀,
      valM₀, topM₀, localM₀, extKM₀, extE₀M₀, _⟩ :=
    rationalPrimeChangedCyclotomicWitt_exists_tower_local_structure
      p hp n a u hu ha
  letI := fdE₀
  letI := fdM₀
  letI := valE₀
  letI := topE₀
  letI := localE₀
  letI := extKE₀
  letI := valM₀
  letI := topM₀
  letI := localM₀
  letI := extKM₀
  letI := extE₀M₀
  letI : Algebra.FormallyUnramified 𝒪[E₀] 𝒪[M₀] :=
    rationalPrimeChangedCyclotomicCompositum_formallyUnramified p hp n a u hu ha
  have hcompat (z : E₀) :
      eM (algebraMap E₀ M₀ z) = algebraMap E M (eE z) :=
    rationalPrimeChangedCyclotomicClosureCompositumEquiv_auxiliary
      p hp n a u hu ha z
  have hF := localFieldArithmeticFrobenius_conjugate eE eM hcompat
  rw [rationalPrimeChangedCyclotomicDiagonalAlgEquiv_eq_arithmeticFrobenius
    p hp n a b u hu ha hcoprimeA hcoprimeB hab]
  calc
    eM (localFieldArithmeticFrobenius E₀ M₀ x) =
        localFieldGaloisConjugate eE eM hcompat
          (localFieldArithmeticFrobenius E₀ M₀) (eM x) := by simp
    _ = localFieldArithmeticFrobenius E M (eM x) := by rw [hF]

/-- The actual primitive root in the closure compositum, obtained from the
finite Witt model by the proved compositum equivalence. -/
def rationalPrimeChangedCyclotomicClosureRoot
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha :=
  rationalPrimeChangedCyclotomicClosureCompositumEquiv p hp n a u hu ha
    (rationalPrimeChangedCyclotomicCompositumRoot p hp n u)

/-- On the actual closure-compositum primitive root, arithmetic Frobenius
has the inverse-unit power action required by the ramified reciprocity step. -/
theorem rationalPrimeChangedCyclotomicClosureFrobenius_root
    (p : ℕ) (hp : p.Prime) (n a b : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (hcoprimeA : a.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hcoprimeB : b.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD
      (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)])
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha))]
    [ValuativeRel (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [TopologicalSpace (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha))]
    [(ValuativeRel.valuation (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha))]
    [Algebra.FormallyUnramified
      𝒪[rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha]
      𝒪[rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha]] :
    localFieldArithmeticFrobenius
        (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)
        (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)
        (rationalPrimeChangedCyclotomicClosureRoot p hp n a u hu ha) =
      (rationalPrimeChangedCyclotomicClosureRoot p hp n a u hu ha) ^ b := by
  change localFieldArithmeticFrobenius
      (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)
      (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)
      (rationalPrimeChangedCyclotomicClosureCompositumEquiv p hp n a u hu ha
        (rationalPrimeChangedCyclotomicCompositumRoot p hp n u)) =
    (rationalPrimeChangedCyclotomicClosureCompositumEquiv p hp n a u hu ha
      (rationalPrimeChangedCyclotomicCompositumRoot p hp n u)) ^ b
  rw [← rationalPrimeChangedCyclotomicClosureFrobenius_equiv
      p hp n a b u hu ha hcoprimeA hcoprimeB hab,
    rationalPrimeChangedCyclotomicDiagonalAlgEquiv_root
      p hp n a b u hu hcoprimeA hcoprimeB hab,
    map_pow]

/-- The literal primitive root as an element of the original finite cyclotomic stage. -/
def rationalPrimeOriginalCyclotomicStageRoot
    (p : ℕ) (hp : p.Prime) (n : ℕ) :
    rationalPrimeOriginalCyclotomicStage p hp n := by
  let K := rationalPrimeLocalField p hp
  let Ω := wittCyclotomicField
    (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n
  let ζ := rationalPrimeWittCyclotomicFieldPrimitiveRoot p hp n
  refine ⟨ζ, ?_⟩
  change ζ ∈ IntermediateField.adjoin K ({ζ} : Set Ω)
  exact IntermediateField.subset_adjoin K ({ζ} : Set Ω) (Set.mem_singleton ζ)

/-- The original finite cyclotomic stage includes in the finite Witt
changed/cyclotomic compositum through the literal supremum inclusion. -/
def rationalPrimeOriginalCyclotomicCompositumInclusion
    (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    rationalPrimeOriginalCyclotomicStage p hp n →ₐ[rationalPrimeLocalField p hp]
      rationalPrimeChangedCyclotomicCompositum p hp n u := by
  let K := rationalPrimeLocalField p hp
  let E := rationalPrimeChangedAuxiliaryField p hp n u
  let L := rationalPrimeOriginalCyclotomicStage p hp n
  let M := rationalPrimeChangedCyclotomicCompositum p hp n u
  let j : L →ₐ[K] M.toIntermediateField.restrictScalars K :=
    IntermediateField.inclusion (show L.toIntermediateField ≤
      M.toIntermediateField.restrictScalars K by
        change L.toIntermediateField ≤ E ⊔ L.toIntermediateField
        exact le_sup_right)
  exact (intermediateFieldRestrictScalarsAlgEquiv M.toIntermediateField).toAlgHom.comp j

theorem rationalPrimeChangedCyclotomicClosureCompositumEquiv_coe
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (x : rationalPrimeChangedCyclotomicCompositum p hp n u) :
    let K := rationalPrimeLocalField p hp
    let M := rationalPrimeChangedCyclotomicCompositum p hp n u
    let S := rationalPrimeChangedCyclotomicFiniteAmbient p hp n u
    let ι := rationalPrimeChangedCyclotomicFiniteAmbientEmbedding p hp n a u hu ha
    let hsource : M.toIntermediateField.restrictScalars K = S := by
      apply SetLike.coe_injective
      exact rationalPrimeChangedCyclotomicCompositum_coe p hp n u
    ((rationalPrimeChangedCyclotomicClosureCompositumEquiv p hp n a u hu ha x :
        rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha) :
      rationalPrimeLocalClosure p hp) =
      ι (IntermediateField.equivOfEq hsource x) := by
  rfl

theorem rationalPrimeOriginalCyclotomicClosureEquiv_coe
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (x : rationalPrimeOriginalCyclotomicStage p hp n) :
    ((rationalPrimeOriginalCyclotomicClosureEquiv p hp n a u hu ha x :
        rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha) :
      rationalPrimeLocalClosure p hp) =
      rationalPrimeChangedCyclotomicFiniteAmbientEmbedding p hp n a u hu ha
        ((IntermediateField.inclusion (show
          (rationalPrimeOriginalCyclotomicStage p hp n).toIntermediateField ≤
          rationalPrimeChangedCyclotomicFiniteAmbient p hp n u from le_sup_right)) x) := by
  exact finiteGaloisEmbeddingStageEquiv_coe _ x

theorem rationalPrimeOriginalCyclotomicSourceInclusion
    (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ)
    (x : rationalPrimeOriginalCyclotomicStage p hp n) :
    let K := rationalPrimeLocalField p hp
    let M := rationalPrimeChangedCyclotomicCompositum p hp n u
    let S := rationalPrimeChangedCyclotomicFiniteAmbient p hp n u
    let hsource : M.toIntermediateField.restrictScalars K = S := by
      apply SetLike.coe_injective
      exact rationalPrimeChangedCyclotomicCompositum_coe p hp n u
    IntermediateField.equivOfEq hsource
        (rationalPrimeOriginalCyclotomicCompositumInclusion p hp n u x) =
      IntermediateField.inclusion (show
        (rationalPrimeOriginalCyclotomicStage p hp n).toIntermediateField ≤ S from
          le_sup_right) x := by
  dsimp only
  apply Subtype.ext
  rfl

theorem rationalPrimeChangedCyclotomicClosureCompositumEquiv_cyclotomic
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (x : rationalPrimeOriginalCyclotomicStage p hp n) :
    rationalPrimeChangedCyclotomicClosureCompositumEquiv p hp n a u hu ha
        (rationalPrimeOriginalCyclotomicCompositumInclusion p hp n u x) =
      rationalPrimeOriginalCyclotomicClosureInclusion p hp n a u hu ha
        (rationalPrimeOriginalCyclotomicClosureEquiv p hp n a u hu ha x) := by
  apply Subtype.ext
  let K := rationalPrimeLocalField p hp
  let M₀ := rationalPrimeChangedCyclotomicCompositum p hp n u
  let S := rationalPrimeChangedCyclotomicFiniteAmbient p hp n u
  let ι := rationalPrimeChangedCyclotomicFiniteAmbientEmbedding p hp n a u hu ha
  let hsource : M₀.toIntermediateField.restrictScalars K = S := by
    apply SetLike.coe_injective
    exact rationalPrimeChangedCyclotomicCompositum_coe p hp n u
  change ((rationalPrimeChangedCyclotomicClosureCompositumEquiv p hp n a u hu ha
      (rationalPrimeOriginalCyclotomicCompositumInclusion p hp n u x) :
        rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha) :
      rationalPrimeLocalClosure p hp) =
    ((rationalPrimeOriginalCyclotomicClosureInclusion p hp n a u hu ha
      (rationalPrimeOriginalCyclotomicClosureEquiv p hp n a u hu ha x) :
        rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha) :
      rationalPrimeLocalClosure p hp)
  calc
    _ = ι (IntermediateField.equivOfEq hsource
        (rationalPrimeOriginalCyclotomicCompositumInclusion p hp n u x)) :=
      rationalPrimeChangedCyclotomicClosureCompositumEquiv_coe p hp n a u hu ha _
    _ = ι (IntermediateField.inclusion (show
          (rationalPrimeOriginalCyclotomicStage p hp n).toIntermediateField ≤ S from
            le_sup_right) x) := by
      rw [rationalPrimeOriginalCyclotomicSourceInclusion]
    _ = ((rationalPrimeOriginalCyclotomicClosureEquiv p hp n a u hu ha x :
          rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha) :
        rationalPrimeLocalClosure p hp) :=
      (rationalPrimeOriginalCyclotomicClosureEquiv_coe p hp n a u hu ha x).symm
    _ = ((rationalPrimeOriginalCyclotomicClosureInclusion p hp n a u hu ha
        (rationalPrimeOriginalCyclotomicClosureEquiv p hp n a u hu ha x) :
          rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha) :
        rationalPrimeLocalClosure p hp) := rfl

/-- The actual primitive root in the closure cyclotomic stage. -/
def rationalPrimeOriginalCyclotomicClosureRoot
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha :=
  rationalPrimeOriginalCyclotomicClosureEquiv p hp n a u hu ha
    (rationalPrimeOriginalCyclotomicStageRoot p hp n)

/-- The original cyclotomic-stage inclusion sends its literal root to the
same literal root in the finite Witt compositum. -/
theorem rationalPrimeOriginalCyclotomicCompositumInclusion_root
    (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    rationalPrimeOriginalCyclotomicCompositumInclusion p hp n u
        (rationalPrimeOriginalCyclotomicStageRoot p hp n) =
      rationalPrimeChangedCyclotomicCompositumRoot p hp n u := by
  apply Subtype.ext
  rfl

/-- The closure cyclotomic-stage inclusion sends its root to the transported
root in the closure compositum. -/
theorem rationalPrimeOriginalCyclotomicClosureRoot_inclusion
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    rationalPrimeOriginalCyclotomicClosureInclusion p hp n a u hu ha
        (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) =
      rationalPrimeChangedCyclotomicClosureRoot p hp n a u hu ha := by
  change rationalPrimeOriginalCyclotomicClosureInclusion p hp n a u hu ha
      (rationalPrimeOriginalCyclotomicClosureEquiv p hp n a u hu ha
        (rationalPrimeOriginalCyclotomicStageRoot p hp n)) =
    rationalPrimeChangedCyclotomicClosureCompositumEquiv p hp n a u hu ha
      (rationalPrimeChangedCyclotomicCompositumRoot p hp n u)
  calc
    _ = rationalPrimeChangedCyclotomicClosureCompositumEquiv p hp n a u hu ha
        (rationalPrimeOriginalCyclotomicCompositumInclusion p hp n u
          (rationalPrimeOriginalCyclotomicStageRoot p hp n)) :=
      (rationalPrimeChangedCyclotomicClosureCompositumEquiv_cyclotomic
        p hp n a u hu ha (rationalPrimeOriginalCyclotomicStageRoot p hp n)).symm
    _ = _ := congrArg
      (rationalPrimeChangedCyclotomicClosureCompositumEquiv p hp n a u hu ha)
      (rationalPrimeOriginalCyclotomicCompositumInclusion_root p hp n u)

end
end Dubon2026
