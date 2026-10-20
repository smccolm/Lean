import Dubon2026.IntegralInducedTensor
import Dubon2026.CMFiniteAdelicSmallParabolicLevels

/-! Original arithmetic action on Geraghty's tensor coefficient module.
Each factor uses the original finite-place evaluation of the actual CM
unitary matrix, followed by the specified coefficient embedding on the
local integers. The actual regular-function right translations are then
tensored. No arbitrary finite-free representation is an input.

The source coefficient embeddings are explicit ring maps here.
IntegralCoefficientEmbedding and CMSourceIntegralWeight construct them from
actual field embeddings and prove their continuity.
CMSourceIntegralWeightContinuity proves joint continuity of the original tensor
action in its canonical coefficient-module topology.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField TensorProduct

universe u
variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable (R : Type u) [CommRing R] {I : Type u}
  (v : I → HeightOneSpectrum (𝓞 K))
  (e : ∀ i, Valued.integer ((v i).adicCompletion K) →+* R)
  (n : ℕ) (H : Matrix (Fin n) (Fin n) K)

/-- Each original unitary local integral matrix is evaluated in the specified coefficient embedding. -/
def cmIntegralCoefficientMatrixMap :
    cmFiniteAdelicIntegralLevel K H →* (I → GeneralLinearGroup (Fin n) R) where
  toFun g i := GeneralLinearGroup.map (e i) (cmFiniteAdelicIntegralLocalMap K H (v i) g)
  map_one' := funext fun i => by simp
  map_mul' g h := funext fun i => by simp

/-- The source arithmetic tensor action is constructed from the actual unitary evaluations and the actual induced coefficient factors. -/
def cmIntegralInducedTensorRepresentation (lam : I → Fin n → ℤ) :
    Representation R (cmFiniteAdelicIntegralLevel K H) (IntegralInducedTensor R n lam) :=
  (integralInducedTensorRepresentation R n lam).comp (cmIntegralCoefficientMatrixMap K R v e n H)

/-- The actual unitary arithmetic action has exactly the source tensor formula on pure tensors. -/
theorem cmIntegralInducedTensorRepresentation_tprod (lam : I → Fin n → ℤ)
    (g : cmFiniteAdelicIntegralLevel K H)
    (p : ∀ i, generalLinearIntegralInducedSubmodule R n (lam i)) :
    cmIntegralInducedTensorRepresentation K R v e n H lam g (PiTensorProduct.tprod R p) =
      PiTensorProduct.tprod R (fun i =>
        generalLinearIntegralInducedRepresentation R n (lam i)
          (GeneralLinearGroup.map (e i) (cmFiniteAdelicIntegralLocalMap K H (v i) g)) (p i)) :=
  integralInducedTensorRepresentation_tprod R n lam _ p

/-- The arithmetic action on each actual regular-function factor is evaluation at the original unitary matrix in the specified coefficient embedding. -/
theorem cmIntegralInducedFactor_eval (lam : I → Fin n → ℤ)
    (g : cmFiniteAdelicIntegralLevel K H) (i : I)
    (p : generalLinearIntegralInducedSubmodule R n (lam i))
    (A : Type u) [CommRing A] [Algebra R A] (x : GeneralLinearGroup (Fin n) A) :
    generalLinearRegularEval x
      (generalLinearIntegralInducedRepresentation R n (lam i)
        (cmIntegralCoefficientMatrixMap K R v e n H g i) p).val =
      generalLinearRegularEval
        (x * GeneralLinearGroup.map ((algebraMap R A).comp (e i))
          (cmFiniteAdelicIntegralLocalMap K H (v i) g)) p.val := by
  rw [generalLinearIntegralInducedRepresentation_eval]
  rfl

/-- The original small auxiliary level lies in the integral unitary level, so the source coefficient action restricts to it. -/
def cmSmallParabolicIntegralInclusion {S : Type*}
    (a : S → HeightOneSpectrum (𝓞 K)) (m : ℕ)
    (J : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (w : HeightOneSpectrum (𝓞 K)) :
    cmFiniteAdelicSmallParabolicZero K a m J w →* cmFiniteAdelicIntegralLevel K J :=
  (cmFiniteAdelicPrincipalIntegralMap K J w).comp
    (Subgroup.inclusion (cmFiniteAdelicSmallParabolicZero_le_principal K a m J w))

/-- The original upper auxiliary level acts on the literal integral tensor module by the source arithmetic action. -/
def cmSmallParabolicInducedTensorRepresentation {S : Type*}
    (a : S → HeightOneSpectrum (𝓞 K)) (m : ℕ)
    (J : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (w : HeightOneSpectrum (𝓞 K))
    (lam : I → Fin (m + 1) → ℤ) :
    Representation R (cmFiniteAdelicSmallParabolicZero K a m J w)
      (IntegralInducedTensor R (m + 1) lam) :=
  (cmIntegralInducedTensorRepresentation K R v e (m + 1) J lam).comp
    (cmSmallParabolicIntegralInclusion K a m J w)

end
end Dubon2026
