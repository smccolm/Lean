import Dubon2026.HopfPointsVanishingIdeal
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Operations

/-! # A point vanishing on a finite joint kernel has an original point kernel -/

namespace Dubon2026
noncomputable section

variable {R A K : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [IsArtinianRing A] [Field K] [Algebra R K]

/-- A genuine point annihilating the finite original joint vanishing ideal has exactly the kernel of one original point. Finite prime-ideal selection and actual Artinian maximality supply that point. -/
theorem hopfPointVanishingIdeal_kernel_selection
    (X : Set (WithConv (A →ₐ[R] K))) [Finite X]
    (p : WithConv (A →ₐ[R] K))
    (hp : hopfPointsVanishingIdeal X ≤ RingHom.ker p.ofConv.toRingHom) :
    ∃ q : X, RingHom.ker q.val.ofConv.toRingHom = RingHom.ker p.ofConv.toRingHom := by
  classical
  letI := Fintype.ofFinite X
  have hI : hopfPointsVanishingIdeal X =
      Finset.univ.inf (fun q : X => RingHom.ker q.val.ofConv.toRingHom) := by
    ext a
    simp only [hopfPointsVanishingIdeal_mem_iff, Submodule.mem_finsetInf,
      Finset.mem_univ, true_implies, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom]
  rw [hI] at hp
  obtain ⟨q, _, hq⟩ := (RingHom.ker_isPrime p.ofConv.toRingHom).inf_le'.mp hp
  letI : (RingHom.ker q.val.ofConv.toRingHom).IsPrime :=
    RingHom.ker_isPrime q.val.ofConv.toRingHom
  letI : (RingHom.ker q.val.ofConv.toRingHom).IsMaximal := inferInstance
  refine ⟨q, ?_⟩
  exact (inferInstance : (RingHom.ker q.val.ofConv.toRingHom).IsMaximal).eq_of_le
    (RingHom.ker_isPrime p.ofConv.toRingHom).ne_top hq

end
end Dubon2026
