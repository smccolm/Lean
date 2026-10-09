import Dubon2026.AdelicFiniteFixedRealRepresentation
import Dubon2026.FiniteIntertwinerMultiplicity

/-! # Genuine finite multiplicity for arbitrary finite-dimensional real types at every open finite level -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Every finite-dimensional representation of an actual real group containing the separating rotation has finite multiplicity in the original open-finite-subgroup fixed space. -/
theorem adelicRealType_finiteMultiplicity (hf : f ≠ 0) (hk : 0 < k)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ι : G →* GeneralLinearGroup (Fin 2) ℝ) (g : G)
    (hg : ι g = toGL (realRotationCurve (Real.pi * Real.sqrt 2))) (σ : Representation ℂ G V) :
    FiniteDimensional ℂ (Representation.IntertwiningMap σ ((adelicFiniteFixedRealRepresentation f J).comp ι)) := by
  have hrot : ∀ c : ℂ,
      FiniteDimensional ℂ (Module.End.eigenspace (adelicFiniteFixedRealRepresentation f J (ι g)) c) :=
    Eq.mpr (congrArg (fun a => ∀ c : ℂ,
      FiniteDimensional ℂ (Module.End.eigenspace (adelicFiniteFixedRealRepresentation f J a) c)) hg)
      (adelicFiniteFixedRealRepresentation_eigenspace_finiteDimensional f J hf hk hJ)
  exact finiteDimensional_intertwining_of_eigenspaces σ
    ((adelicFiniteFixedRealRepresentation f J).comp ι) g hrot

end
end Dubon2026
