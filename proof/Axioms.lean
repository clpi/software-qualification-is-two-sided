/-
  The dependency audit for the hinge width development. Every
  main theorem and every control is printed with the foundational
  principles it depends on; the family gate fails if any printed
  principle lies outside the allowed set
  {propext, Classical.choice, Quot.sound}.
-/

import Hinge
import Controls

open Hinge

#print axioms rim
#print axioms margin
#print axioms grow
#print axioms Controls.sentinel
#print axioms Controls.strict
#print axioms Controls.drop
