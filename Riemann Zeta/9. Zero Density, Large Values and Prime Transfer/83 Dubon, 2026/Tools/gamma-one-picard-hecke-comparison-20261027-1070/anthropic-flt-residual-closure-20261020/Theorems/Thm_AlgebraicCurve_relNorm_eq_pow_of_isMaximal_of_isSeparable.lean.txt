import Mathlib.RingTheory.Ideal.Norm.RelNorm
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_relNorm_eq_pow_of_isMaximal_of_isSeparable

theorem AlgebraicCurve.relNorm_eq_pow_of_isMaximal_of_isSeparable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsSeparable K L]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg' P := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_relNorm_eq_pow_of_isMaximal_of_isSeparable.solution
