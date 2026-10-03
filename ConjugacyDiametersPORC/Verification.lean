import ConjugacyDiametersPORC.MainTheorem

/-!
# Kernel-dependency checks for the main results

These checks run as part of the library build. Any additional axiom in either
main result's dependencies changes the message and makes the build fail.
-/

/--
info: 'ConjugacyDiametersPORC.diameter_eventuallyAffinePORC' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ConjugacyDiametersPORC.diameter_eventuallyAffinePORC

/--
info: 'ConjugacyDiametersPORC.diameter_eventual_recurrence_with_slope' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ConjugacyDiametersPORC.diameter_eventual_recurrence_with_slope
