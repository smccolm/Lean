import Dubon2026.SourceDifferentialTranscendence

/-! The actual rational-coordinate differential is a basis in any
separable rational-function extension, in every characteristic. This is
the direct polynomial/etale basis argument already used in
SourceDifferentialTranscendence, avoiding a further coordinate-equivalence
construction. It discharges the rank and nonzero-differential inputs of
the DUB-17/18 wild different estimate on the actual auxiliary fields. -/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial KaehlerDifferential
variable (K : Type*) [Field K] (M : Type*) [Field M]
variable [Algebra K M] [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]
variable [Algebra.IsSeparable (RatFunc K) M]

theorem exists_rationalCoordinate_differential_basis :
    ∃ b : Module.Basis Unit M Ω[M⁄K],
      b () = D K M (algebraMap (RatFunc K) M RatFunc.X) := by
  letI : Algebra K[X] M := ((algebraMap (RatFunc K) M).comp
    (algebraMap K[X] (RatFunc K))).toAlgebra
  letI : IsScalarTower K[X] (RatFunc K) M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K K[X] M := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap K M c = algebraMap (RatFunc K) M (algebraMap K[X] (RatFunc K) (C c))
    rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K),
      ← IsScalarTower.algebraMap_apply K (RatFunc K) M]
  letI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])
  letI : Algebra.FormallyEtale (RatFunc K) M :=
    Algebra.FormallyEtale.of_isSeparable (RatFunc K) M
  letI : Algebra.FormallyEtale K[X] M := Algebra.FormallyEtale.comp K[X] (RatFunc K) M
  let b₀ : Module.Basis Unit K[X] Ω[K[X]⁄K] :=
    (Module.Basis.singleton Unit K[X]).map (polynomialEquiv K).symm
  have hb₀ : b₀ () = D K K[X] X := by simp [b₀]
  let ψ := tensorKaehlerEquivOfFormallyEtale K K[X] M
  refine ⟨(b₀.baseChange M).map ψ, ?_⟩
  have hX : algebraMap K[X] M X = algebraMap (RatFunc K) M RatFunc.X := by
    change algebraMap (RatFunc K) M (algebraMap K[X] (RatFunc K) X) = _
    rw [RatFunc.algebraMap_X]
  simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb₀, ψ,
    tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, map_D, hX]

theorem D_rationalCoordinate_ne_zero :
    D K M (algebraMap (RatFunc K) M RatFunc.X) ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_rationalCoordinate_differential_basis K M
  rw [← hb]
  exact b.ne_zero ()

theorem finrank_rationalExtension_differentials : Module.finrank M Ω[M⁄K] = 1 := by
  obtain ⟨b, _⟩ := exists_rationalCoordinate_differential_basis K M
  simpa only [Fintype.card_unique] using Module.finrank_eq_card_basis b

end
end Dubon2026.SourceCurve
