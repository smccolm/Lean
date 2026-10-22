import Dubon2026.SourceWeightTwoPeriodHecke
import Dubon2026.SourceResidualWeightTwoAlternatives

/-! DUB-17/18 -> residual modular Galois association.
The supplied nonzero original parabolic H1 eigenclass now gives an actual
native cusp form with exactly the same simultaneous good-prime eigenvalues.
The original integral lift and reduction map are retained in the residual
consumer. Galois realization of this cusp eigensystem remains required.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology SourceCuspBoundary

theorem sourceTrivialParabolicEigen_exists_cuspForm (N : ℕ) [NeZero N]
    (θ : sourceBinaryHeckePrime N → ℂ)
    (v : H1 (Rep.trivial ℂ (Gamma0 N) ℂ)) (hv : v ≠ 0)
    (hpar : (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)).hom v ∈ parabolicHoms N)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators ℂ N ell v = θ ell • v) :
    ∃ f : CuspForm (Gamma0 N) 2, f ≠ 0 ∧
      ∀ ell, cuspHeckeLinear N 2 ell.val f = θ ell • f := by
  let e := H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)
  obtain ⟨⟨f, g⟩, hfg⟩ := sourceWeightTwoParabolicPeriodPair_surjective N ⟨e.hom v, hpar⟩
  have hpair : sourceWeightTwoPeriodPair N (f, g) = e.hom v := congrArg Subtype.val hfg
  have hp (ell : sourceBinaryHeckePrime N) :
      (cuspHeckeLinear N 2 ell.val f, cuspHeckeLinear N 2 ell.val g) = θ ell • (f, g) := by
    apply sourceWeightTwoPeriodPair_injective N
    rw [sourceWeightTwoPeriodPair_hecke, map_smul, hpair]
    change e.hom (sourceTrivialCoefficientHeckeOperators ℂ N ell (e.inv (e.hom v))) = _
    rw [CategoryTheory.Iso.hom_inv_id_apply, heig, map_smul]
  by_cases hf : f = 0
  · refine ⟨g, ?_, fun ell => congrArg Prod.snd (hp ell)⟩
    intro hg
    rw [hf, hg, show ((0 : CuspForm (Gamma0 N) 2), (0 : CuspForm (Gamma0 N) 2)) = 0 from rfl,
      map_zero] at hpair
    have hz := congrArg e.inv hpair
    rw [map_zero, CategoryTheory.Iso.hom_inv_id_apply] at hz
    exact hv hz.symm
  · exact ⟨f, hf, fun ell => congrArg Prod.fst (hp ell)⟩

theorem sourceTrivialH1Eigen_cuspLift_or_dirichletPair
    (F : Type) [Field F] [IsAlgClosed F] (N : ℕ) [NeZero N]
    (values : sourceBinaryHeckePrime N → F)
    (x : H1 (Rep.trivial F (Gamma0 N) F)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators F N ell x = values ell • x) :
    (∃ (θ : sourceBinaryHeckePrime N → integralClosure ℤ ℂ)
      (φ : integralClosure ℤ ℂ →+* F) (f : CuspForm (Gamma0 N) 2), f ≠ 0 ∧
      (∀ ell, cuspHeckeLinear N 2 ell.val f = (θ ell : ℂ) • f) ∧
      ∀ ell, φ (θ ell) = values ell) ∨
    ∃ ψ₁ ψ₂ : (ZMod N)ˣ →* Fˣ,
      (∀ u, (ψ₁ u : F) * (ψ₂ u : F) = 1) ∧
      ∀ ell : sourceBinaryHeckePrime N,
        values ell = (ψ₁ (ZMod.unitOfCoprime ell.val ell.property.2) : F) +
          (ell.val : F) * (ψ₂ (ZMod.unitOfCoprime ell.val ell.property.2) : F) := by
  rcases sourceTrivialH1Eigen_parabolicLift_or_dirichletPair F N values x hx heig with
    ⟨θ, φ, v, hv, hpar, hvEig, hres⟩ | hchars
  · obtain ⟨f, hf, he⟩ := sourceTrivialParabolicEigen_exists_cuspForm N (fun ell => (θ ell : ℂ))
      v hv hpar hvEig
    exact Or.inl ⟨θ, φ, f, hf, he, hres⟩
  · exact Or.inr hchars

end
end Dubon2026
