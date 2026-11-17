import Dubon2026.SourceGammaOnePrimitiveJointRing
import Dubon2026.SourceGammaOnePrimitiveBoundaryGaloisWords
import Dubon2026.SourceGammaOneDiamondQuotientGaloisHecke

/-! DUB-17/18 -> original all-weight association -> joint arithmetic
specialization. The actual geometric and primitive-boundary actions form
one continuous finite operator representation. It commutes with every
prime/diamond word carrying the original character. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup SourceCuspBoundary

private theorem continuous_pair_discrete {G X Y : Type} [TopologicalSpace G]
    (f : G → X) (g : G → Y) (hf : @Continuous _ _ _ ⊥ f) (hg : @Continuous _ _ _ ⊥ g) :
    @Continuous _ _ _ ⊥ (fun a => (f a, g a)) := by
  letI : TopologicalSpace X := ⊥
  letI : TopologicalSpace Y := ⊥
  letI : DiscreteTopology X := ⟨rfl⟩
  letI : DiscreteTopology Y := ⟨rfl⟩
  have he : (inferInstance : TopologicalSpace (X × Y)) = ⊥ := DiscreteTopology.eq_bot
  exact Eq.mp (congrArg (fun t : TopologicalSpace (X × Y) =>
    @Continuous G (X × Y) _ t (fun a => (f a, g a))) he) (hf.prodMk hg)

variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]
local notation "N" => p ^ (n + 1)
local notation "M" => Q * N ^ 2
local notation "Qbar" => AlgebraicClosure ℚ
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "T" => TateModule p (Pic0 Qbar (functionFieldOver (Gamma1 M) Qbar))
private local instance : Algebra ℤ_[p] (ZMod N) := (PadicInt.toZModPow (n + 1)).toAlgebra
private local instance : Module ℤ_[p] V := Module.restrictScalars ℤ_[p] (ZMod N) V
private local instance : IsScalarTower ℤ_[p] (ZMod N) V :=
  IsScalarTower.restrictScalars ℤ_[p] (ZMod N) V
private local instance : AddCommGroup (T →ₗ[ℤ_[p]] V) := inferInstance
private local instance : Module (ZMod N) (T →ₗ[ℤ_[p]] V) := inferInstance
local notation "J" => (T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w
local notation "S" => sourceBinaryHeckePrime (Q * N) ⊕ Gamma0 M

/-- The literal pair of the actual geometric and primitive-boundary
Galois representations in their original finite operator ring. -/
def binaryPrimitiveJointGaloisRep :
    (Qbar ≃ₐ[ℚ] Qbar) →* binaryPrimitiveJointOperatorRing Q p n w :=
  (binaryDiamondQuotientGaloisRep Q p n w).prod (binaryPrimitiveBoundaryGaloisRep Q N w)

/-- The original joint representation is continuous for the discrete
finite operator topology, by the two proved original factorizations. -/
theorem binaryPrimitiveJointGaloisRep_continuous :
    @Continuous _ _ _ ⊥ (binaryPrimitiveJointGaloisRep Q p n w).toFun :=
  continuous_pair_discrete _ _ (binaryDiamondQuotientGaloisRep_continuous Q p n w)
    (binaryPrimitiveBoundaryGaloisRep_continuous Q N w)

/-- The actual joint Galois representation commutes with the entire
original prime/diamond operator image, not only selected generators. -/
theorem binaryPrimitiveJointGaloisRep_word
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    (hH : ∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell))
    (σ : Qbar ≃ₐ[ℚ] Qbar) (a : FreeAlgebra ℤ S) :
    Commute (binaryPrimitiveJointGaloisRep Q p n w σ)
      (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq a) := by
  apply Prod.ext
  · apply LinearMap.ext
    intro z
    change binaryDiamondQuotientGaloisRep Q p n w σ
        (FreeAlgebra.lift ℤ (Sum.elim Hq (fun _ : Gamma0 M => 1)) a z) =
      FreeAlgebra.lift ℤ (Sum.elim Hq (fun _ : Gamma0 M => 1)) a
        (binaryDiamondQuotientGaloisRep Q p n w σ z)
    apply sourceHeckeWord_intertwine_addHom _ _
      (binaryDiamondQuotientGaloisRep Q p n w σ).toAddMonoidHom
    intro s y
    cases s with
    | inl ell =>
      exact LinearMap.congr_fun
        (binaryDiamondQuotientGaloisRep_prime_of_intertwining Q p n w σ ell
          (Hq ell) (hH ell)).eq y
    | inr g => rfl
  · apply LinearMap.ext
    intro f
    exact binaryPrimitiveBoundaryGaloisRep_word Q N w σ a f

end
end Dubon2026.SourceFunctionField.GammaOne
