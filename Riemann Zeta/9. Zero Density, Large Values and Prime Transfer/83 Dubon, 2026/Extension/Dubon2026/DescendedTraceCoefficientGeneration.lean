import Dubon2026.ClosedMatrixTraceAlgebra

/-! # The genuine descended representation generates the whole original trace coefficient ring -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O R K : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [CommRing K] [Algebra O R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- Every actual descended trace is precisely the same original trace under the true coefficient inclusion. -/
theorem descendedTrace_coe_eq (r : R →+* K) (ρ : G →* GeneralLinearGroup ι R)
    (τ : G →* GeneralLinearGroup ι (closedMatrixTraceAlgebra (O := O) ρ))
    (h : MatrixStrictlyConjugate r
      ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O) ρ).val.toRingHom).comp τ) ρ)
    (g : G) :
    (closedMatrixTraceAlgebra (O := O) ρ).val (Matrix.trace (τ g).val) =
      Matrix.trace (ρ g).val := by
  have ht := matrixStrictlyConjugate_trace r _ _ h g
  change Matrix.trace (ρ g).val = Matrix.trace
    ((τ g).val.map (closedMatrixTraceAlgebra (O := O) ρ).val) at ht
  rw [← AddMonoidHom.map_trace] at ht
  exact ht.symm

/-- The actual traces of the whole descended representation topologically generate the entire original trace coefficient ring, in its inherited original topology. -/
theorem descendedTraceAlgebra_eq_top (r : R →+* K) (ρ : G →* GeneralLinearGroup ι R)
    (τ : G →* GeneralLinearGroup ι (closedMatrixTraceAlgebra (O := O) ρ))
    (h : MatrixStrictlyConjugate r
      ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O) ρ).val.toRingHom).comp τ) ρ) :
    letI : IsTopologicalRing (closedMatrixTraceAlgebra (O := O) ρ) :=
      inferInstanceAs (IsTopologicalRing (closedMatrixTraceAlgebra (O := O) ρ).toSubring)
    closedMatrixTraceAlgebra (O := O) τ = ⊤ := by
  let S := closedMatrixTraceAlgebra (O := O) ρ
  letI : IsTopologicalRing S := inferInstanceAs (IsTopologicalRing S.toSubring)
  let B := Algebra.adjoin O (Set.range (fun g : G => Matrix.trace (τ g).val))
  let inc : S →A[O] R := ⟨S.val, continuous_subtype_val⟩
  have htrace : S.val ∘ (fun g : G => Matrix.trace (τ g).val) =
      (fun g : G => Matrix.trace (ρ g).val) :=
    funext (descendedTrace_coe_eq r ρ τ h)
  have hb : B.map S.val = Algebra.adjoin O (Set.range (fun g : G => Matrix.trace (ρ g).val)) := by
    rw [AlgHom.map_adjoin, ← Set.range_comp, htrace]
  have hmap : B.topologicalClosure.map S.val = S := by
    rw [← Subalgebra.topologicalClosure_map inc
      (isClosed_closedMatrixTraceAlgebra ρ).isClosedMap_subtype_val, hb]
    rfl
  have htop : (⊤ : Subalgebra O S).map S.val = S := by
    rw [Algebra.map_top, Subalgebra.range_val]
  exact Subalgebra.map_injective Subtype.val_injective (hmap.trans htop.symm)

/-- Strict conjugacy of the actual descended representations determines every coefficient of two continuous maps out of the original trace ring. -/
theorem descendedTraceCoefficientMaps_eq {A B : Type*} [CommRing A] [CommRing B]
    [Algebra O A] [TopologicalSpace A] [T2Space A]
    (r : R →+* K) (ρ : G →* GeneralLinearGroup ι R)
    (τ : G →* GeneralLinearGroup ι (closedMatrixTraceAlgebra (O := O) ρ))
    (h : MatrixStrictlyConjugate r
      ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O) ρ).val.toRingHom).comp τ) ρ)
    (f g : closedMatrixTraceAlgebra (O := O) ρ →ₐ[O] A)
    (hf : Continuous f) (hg : Continuous g) (rA : A →+* B)
    (hfg : MatrixStrictlyConjugate rA
      ((GeneralLinearGroup.map f.toRingHom).comp τ)
      ((GeneralLinearGroup.map g.toRingHom).comp τ)) : f = g := by
  letI : IsTopologicalRing (closedMatrixTraceAlgebra (O := O) ρ) :=
    inferInstanceAs (IsTopologicalRing (closedMatrixTraceAlgebra (O := O) ρ).toSubring)
  have heq := eqOn_closedMatrixTraceAlgebra_of_strictConjugate τ f g hf hg rA hfg
  apply AlgHom.ext
  intro x
  apply heq
  rw [descendedTraceAlgebra_eq_top r ρ τ h]
  trivial

end
end Dubon2026
