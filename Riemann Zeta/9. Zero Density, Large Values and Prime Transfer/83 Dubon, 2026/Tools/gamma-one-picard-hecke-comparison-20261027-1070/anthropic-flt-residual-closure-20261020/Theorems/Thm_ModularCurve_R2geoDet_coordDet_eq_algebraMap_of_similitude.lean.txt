import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_R2geoDet_coordDet_eq_algebraMap_of_similitude

theorem ModularCurve.R2geoDet.coordDet_eq_algebraMap_of_similitude
    {K : Type} [Field K] [CharZero K]
    {A : Type} [CommRing A] [Algebra K A]
    {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
    (b : Module.Basis (Fin 2) A V)
    (B : V →ₗ[K] V →ₗ[K] K)
    (hbal : ∀ (a : A) (v w : V), B (a • v) w = B v (a • w))
    (halt : ∀ v : V, B v v = 0)
    (hnd : ∀ v : V, (∀ w : V, B v w = 0) → v = 0)
    (f : V →ₗ[K] V) (hfA : ∀ (a : A) (v : V), f (a • v) = a • f v)
    (c : K) (hsim : ∀ v w : V, B (f v) (f w) = c • B v w) :
    (b.repr (f (b 0))) 0 * (b.repr (f (b 1))) 1
      - (b.repr (f (b 1))) 0 * (b.repr (f (b 0))) 1
    = algebraMap K A c := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_R2geoDet_coordDet_eq_algebraMap_of_similitude.solution
