import Dubon2026.AdelicRealFiniteTensorAction
import Dubon2026.AdelicRealFiniteTensorCompletion
import Dubon2026.AdelicLocalFullAwayTensorCompletion

/-! # The genuine completed external real/finite action realizes the full original adelic representation -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UniformSpace
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The genuine independently constructed real/finite external action preserves its actual product norm. -/
theorem adelicRealFiniteTensorRepresentation_norm (hf : f ≠ 0) (hk : 0 < k)
    (b : GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (x : AdelicRealFiniteTensor f) : ‖adelicRealFiniteTensorRepresentation f b x‖ = ‖x‖ :=
  @linearMap_norm_of_isometric_intertwiner (AdelicRealFiniteTensor f) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance (adelicRealFiniteTensorIsometry f hf hk)
    (adelicRealFiniteTensorRepresentation f b) (adelicRealFiniteJointRepresentation f b)
    (adelicRealFiniteTensorIsometry_intertwines f hf hk b)
    (adelicCyclicHilbertOperator_norm f (rationalAdelicGL2RealFiniteEquiv.symm b)) x

/-- The independently constructed external action extends by its proved isometry to the actual real/finite Hilbert tensor. -/
def adelicRealFiniteHilbertTensorRepresentation (hf : f ≠ 0) (hk : 0 < k) :
    Representation ℂ (GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
      (AdelicRealFiniteHilbertTensor f) :=
  isometricRepresentationCompletion (adelicRealFiniteTensorRepresentation f)
    (adelicRealFiniteTensorRepresentation_norm f hf hk)

/-- The original completed real/finite tensor map intertwines the true external action on every Hilbert vector. -/
theorem adelicRealFiniteHilbertTensorIsometry_intertwines (hf : f ≠ 0) (hk : 0 < k)
    (b : GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (x : AdelicRealFiniteHilbertTensor f) :
    adelicRealFiniteHilbertTensorIsometry f hf hk (adelicRealFiniteHilbertTensorRepresentation f hf hk b x) =
      adelicRealFiniteJointRepresentation f b (adelicRealFiniteHilbertTensorIsometry f hf hk x) :=
  @isometricRepresentationCompletion_intertwines
    (GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (AdelicRealFiniteTensor f)
    inferInstance inferInstance inferInstance
    (adelicRealFiniteTensorRepresentation f) (adelicRealFiniteTensorRepresentation_norm f hf hk)
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicRealFiniteTensorIsometry f hf hk) b
    (adelicCyclicHilbertOperator f (rationalAdelicGL2RealFiniteEquiv.symm b))
    (adelicRealFiniteTensorIsometry_intertwines f hf hk b) x

/-- The actual completed external real/finite tensor action is strongly continuous in the genuine product topology. -/
theorem adelicRealFiniteHilbertTensorRepresentation_stronglyContinuous (hf : f ≠ 0) (hk : 0 < k)
    (x : AdelicRealFiniteHilbertTensor f) :
    Continuous (fun b => adelicRealFiniteHilbertTensorRepresentation f hf hk b x) :=
  @isometric_intertwiner_stronglyContinuous
    (GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (AdelicRealFiniteHilbertTensor f) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (fun b x => adelicRealFiniteHilbertTensorRepresentation f hf hk b x)
    (fun b x => adelicRealFiniteJointRepresentation f b x)
    (adelicRealFiniteHilbertTensorIsometry f hf hk)
    (adelicRealFiniteHilbertTensorIsometry_intertwines f hf hk)
    (fun y => (adelicCyclicHilbertRepresentation_stronglyContinuous f y).comp
      rationalAdelicGL2RealFiniteEquiv_symm_continuous) x

/-- The full original adelic Hilbert representation is equivariantly realized by the genuine completed external real/finite tensor. -/
theorem adelicRealFiniteHilbertTensorEquiv_intertwines (hf : f ≠ 0) (hk : 0 < k)
    (a : RationalAdelicGL2) (x : AdelicRealFiniteHilbertTensor f) :
    adelicRealFiniteHilbertTensorEquiv f hf hk
      (adelicRealFiniteHilbertTensorRepresentation f hf hk (rationalAdelicGL2RealFiniteEquiv a) x) =
      adelicCyclicHilbertRepresentation f a (adelicRealFiniteHilbertTensorEquiv f hf hk x) := by
  have he := adelicRealFiniteHilbertTensorIsometry_intertwines f hf hk (rationalAdelicGL2RealFiniteEquiv a) x
  change adelicRealFiniteHilbertTensorIsometry f hf hk
    (adelicRealFiniteHilbertTensorRepresentation f hf hk (rationalAdelicGL2RealFiniteEquiv a) x) =
      adelicCyclicHilbertRepresentation f a (adelicRealFiniteHilbertTensorIsometry f hf hk x)
  exact he.trans (congrArg (fun g : RationalAdelicGL2 => adelicCyclicHilbertRepresentation f g
    (adelicRealFiniteHilbertTensorIsometry f hf hk x)) (rationalAdelicGL2RealFiniteEquiv.symm_apply_apply a))

end
end Dubon2026
