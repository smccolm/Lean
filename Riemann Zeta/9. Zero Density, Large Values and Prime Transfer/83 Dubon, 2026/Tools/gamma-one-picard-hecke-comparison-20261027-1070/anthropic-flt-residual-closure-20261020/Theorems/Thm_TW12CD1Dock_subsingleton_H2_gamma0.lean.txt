import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import P2M.Util
import P2M.Sol.S_TW12CD1Dock_subsingleton_H2_gamma0
set_option autoImplicit false
open CongruenceSubgroup
theorem TW12CD1Dock.subsingleton_H2_gamma0 {k : Type} [CommRing k] (M : ℕ) (h6 : IsUnit (6 : k))
    (A : Rep k ↥(Gamma0 M)) : Subsingleton (groupCohomology A 2) := by p2m_exact_reverting @_root_.P2MW.S_TW12CD1Dock_subsingleton_H2_gamma0.solution
