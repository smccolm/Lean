import RiemannZeta

/-!
# Release linter gate

Run the complete default declaration-linter set over the `RiemannZeta`
package.  The canonical verifier elaborates this file and treats every linter
diagnostic as a release failure.
-/

#lint in RiemannZeta
