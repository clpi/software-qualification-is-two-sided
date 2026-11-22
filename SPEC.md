# Specification: qualification is two-sided

This spec states the model, the definitions, and the theorems of
the hinge width development at the resolution the proof core
(proof/Hinge.lean) implements. Where the spec and the proof core
disagree, the proof core is the record and this spec is the
defect.

## Model

- A configuration is a list of booleans, one per premise.
- The configuration space at length n is the explicit list of
  every boolean list of length n. It is finite by construction:
  qualification picks out named configurations under named
  criteria, so its space is a finite list, never an unbounded
  behavior space.
- A qualification is a boolean function on configurations.
- The distance between two configurations of equal length is the
  number of positions at which they differ — single-premise
  changes counted one by one. Configurations of unequal length
  never co-occur in one space.

## Definitions

- The hinge width of a configuration x under a qualification q
  at length n is the least distance from x to a configuration of
  the space that fails q. It is computed as the fold of minima
  over the failing configurations' distances, with the sentinel
  n + 1 when no configuration fails (every real distance is at
  most n, so the sentinel is distinguishable from every width).
- The boundary at x is: q qualifies x, and some failing
  configuration of the space sits at distance exactly one.
- A failing configuration exists when some configuration of the
  space fails q.
- A qualification q' strengthens q when every configuration
  qualified by q is qualified by q'.

## Theorems

- rim: if x is in the space, q qualifies x, and a failing
  configuration exists, then the width of x is one if and only
  if x is on the boundary.
- margin: under the same hypotheses, width minus one is zero if
  and only if x is on the boundary. The claim's "hinge width
  zero holds exactly at qualification boundaries" is this
  statement with width read as the margin; the width itself, a
  distance, is one at the boundary, and a qualified
  configuration's width is never zero (the only configuration at
  distance zero from x is x, and x qualifies).
- grow: if q' strengthens q, then for every configuration x and
  every length n, the width of x under q is at most the width of
  x under q'.

## Standing controls

- sentinel: at length zero under the all-true qualification, the
  sole configuration's width is the sentinel one and it is not
  on the boundary. The failing-existence hypothesis of rim is
  load-bearing.
- strict: at two premises, the configuration [true, true] has
  width one under the qualification "first premise holds" and
  width two under the strengthening "everything except
  [false, false]"; the strengthening premise is verified for the
  pair. The monotonicity of grow is not vacuous.
- drop: under the change to "everything except [true, true]",
  which is not a strengthening of "first premise holds", the
  width of [true, true] is zero. The strengthening hypothesis of
  grow is load-bearing.

## Proof obligations discharged in the core

- Membership in the space is exactly length n.
- Distance zero between equal-length configurations holds
  exactly at equality; distance is at most the length.
- The fold of minima over a list attains its sentinel or a
  member, is at most every member, and is at least any common
  lower bound of the members and the sentinel.
- The fold of minima over a list is at most the sentinel, and is
  monotone under list inclusion in the shrinking direction the
  width needs: a fold over a larger list is at most a fold over
  a sublist.
- Filtering a list by a weaker predicate yields a sublist of the
  filtering by a stronger one, after any common map.

## Fit to the measured instance

The decidability frontier instrument holds, per run, a finite
set of witnessed venues; an assignment chooses one per run, and
its width is the least number of single-run changes to a
dominated assignment. That is this spec's width with the
instrument's coordinate form in place of boolean premises. The
theorems above are proved for the boolean premise model; the
proofs turn only on finiteness of the space, attainment of the
minimum, distance zero holding exactly at equality, and the
failing set shrinking under strengthening — the four facts the
instrument's coordinate form shares. The instrument's widths are
computed measurements and are recorded in the commissioning
record, not in this repo.
