import Definitions.Def_CohCarrier_Level
import Mathlib.Algebra.Module.Hom
import Mathlib.RingTheory.Noetherian.Basic
import P2M.Util
import P2M.Sol.S_CohCarrier_H1_moduleFinite

set_option autoImplicit false
open CohCarrier

theorem CohCarrier.H1_moduleFinite (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (R : Type*) [CommRing R]
    (A : Type*) [AddCommGroup A] [Module R A] [IsNoetherianRing R] [Module.Finite R A] :
    Module.Finite R (H1 M H A) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_H1_moduleFinite.solution
