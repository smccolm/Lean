import Dubon2026.AdelicLocalSphericalEquiv

/-! # Original primitive local factors with the same Fourier eigenvalue -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N M p : ℕ} [NeZero N] [NeZero M] [NeZero p] [Fact p.Prime] {k l : ℤ}
    (F : PrimitiveCuspForm N k) (G : PrimitiveCuspForm M l)
    (hpN : p.Coprime N) (hpM : p.Coprime M)
    (h : normalizedCuspCoefficients F.toCuspForm p = normalizedCuspCoefficients G.toCuspForm p)

/-- Two actual original primitive cusp forms, possibly of different levels and weights, have equivalent completed good-prime local factors when their original normalized Fourier eigenvalues agree. -/
def adelicPrimitiveLocalEquiv :
    adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ≃ₗᵢ[ℂ]
      adelicLocalCyclicClosedSpan G.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) :=
  adelicLocalSphericalEquiv F hpN (adelicLocalCyclicRepresentation G.toCuspForm _)
    (adelicLocalCyclicRepresentation_inner G.toCuspForm _)
    (adelicLocalCyclicRepresentation_scalar G.toCuspForm _)
    (adelicLocalClosedUnitReference G.toCuspForm _)
    (adelicLocalClosedUnitReference_inner G.toCuspForm (primitiveCuspForm_ne_zero G) _)
    (adelicLocalClosedUnitReference_good_fixed G hpM)
    ((adelicLocalClosedUnitReference_hecke_eigen G hpM).trans
      (congrArg (fun z : ℂ => ((Real.sqrt p : ℂ) * z) • adelicLocalClosedUnitReference G.toCuspForm _) h.symm))
    (adelicLocalClosedUnitReference_cyclic G.toCuspForm (primitiveCuspForm_ne_zero G) _)

/-- The equivalence between the two original factors identifies every corresponding original unit orbit vector. -/
theorem adelicPrimitiveLocalEquiv_orbit
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    adelicPrimitiveLocalEquiv F G hpN hpM h
      (adelicLocalCyclicRepresentation F.toCuspForm _ g (adelicLocalClosedUnitReference F.toCuspForm _)) =
    adelicLocalCyclicRepresentation G.toCuspForm _ g (adelicLocalClosedUnitReference G.toCuspForm _) :=
  adelicLocalSphericalEquiv_orbit F hpN _ _ _ _ _ _ _ _ g

/-- The genuine original local representations are intertwined on every vector of their completed Hilbert factors. -/
theorem adelicPrimitiveLocalEquiv_intertwines
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (x : adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicPrimitiveLocalEquiv F G hpN hpM h (adelicLocalCyclicRepresentation F.toCuspForm _ g x) =
      adelicLocalCyclicRepresentation G.toCuspForm _ g (adelicPrimitiveLocalEquiv F G hpN hpM h x) :=
  adelicLocalSphericalEquiv_intertwines F hpN _ _ _ _ _ _ _ _ g x

end
end Dubon2026
