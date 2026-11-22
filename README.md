# software-qualification-is-two-sided

Every qualified configuration has a dual unqualified witness: a
nearest configuration that fails qualification. The distance to
that witness — the hinge width — is a computable quantity, and
width one holds exactly at the qualification boundary.

## The claim

For any qualified action there is a dual unqualified witness — a
nearest configuration that fails qualification — and the distance
to that witness, the hinge width, is a computable quantity that
predicts which qualifications are fragile under small premise
changes. This repo is the claim's proof home. The measurement
half of the claim (whether the narrowest decile of widths holds
the observed verdict flips) is executed against the decidability
frontier instance and recorded in the research register that
commissioned this repo; its outcome is stated under "The
instance" below, at its evidence level.

## What is proved here

The proof core (proof/Hinge.lean, pinned Lean 4.19.0, core only)
models a configuration as one boolean per premise and the
configuration space as the explicit finite list of every boolean
list of a fixed length — finite by the definition of
qualification, not by hypothesis. Distance is counted in
single-premise changes. Against that model it proves:

- `rim`: for a qualified configuration, in a space that holds a
  failing configuration, hinge width one holds exactly at the
  qualification boundary — a failing configuration one
  single-premise change away.
- `margin`: the margin, width minus one, is zero exactly at the
  boundary. This is the claim's "width zero at the boundary" in
  margin form; the width is a distance, so it is one at the
  boundary and the margin is the quantity that vanishes there.
  The off-by-one between the two forms is stated, not hidden.
- `grow`: width is monotone under premise strengthening, where
  strengthening enlarges the qualified set (every configuration
  qualified before remains qualified). The failing set only
  shrinks, so the least distance to it can only grow.

Three standing controls (proof/Controls.lean) witness that the
hypotheses are load-bearing: with no failing configuration in the
space, a qualified configuration's width is the sentinel and it
is not on the boundary (`sentinel`); under a strengthening at two
premises, one configuration's width grows strictly, from one to
two (`strict`); under a change that is not a strengthening, a
width falls to zero (`drop`).

Axiom audit at the founding pin: `rim` and `margin` depend on
propext, Classical.choice, and Quot.sound; `grow` depends on
propext and Quot.sound; `sentinel` depends on propext only;
`strict` and `drop` depend on no axioms. Nothing is admitted by
sorry. The gate (proof/check.sh) compiles every file cold with
warnings as errors and fails on any printed principle outside
{propext, Classical.choice, Quot.sound}.

## Premises

- The configuration space of the chosen subject is finite by the
  definition of qualification: to qualify is to pick out named
  configurations under named criteria. The model takes the space
  as an explicit list, so finiteness is by construction.
- Distance is counted in single-premise changes.
- Strengthening means the qualified set grows; a change that
  drops a previously qualified configuration is not a
  strengthening, and widths may fall under it (the `drop`
  control).

## The instance

The measurement subject is the decidability frontier's standing
instance: nine witnessed runs over six venues, one venue chosen
per run, 209,952 assignments, of which 209,352 stand on the
frontier (qualified) and 600 are dominated (failing). Hinge
widths were computed for the whole frontier two independent ways
with agreement on a sample of one thousand: width 1: 5,640;
2: 22,134; 3: 47,196; 4: 59,748; 5: 46,200; 6: 21,654; 7: 5,892;
8: 840; 9: 48. A companion tool in the frontier instrument's
ordering home (hinge.py) reports the width beside every verdict
and writes the standing warning naming the 5,640 width-one
assignments; the tool is authored, and its first run is pending
a named execution block recorded in the commissioning record —
until that run, no per-verdict width table exists in the store.

The registered flip test — whether the narrowest decile of
widths holds at least half the verdict flips observed across the
last three head changes — is void on this instance: the nine-run
subject first exists at the store's current state, so the
observed flip count across the last three head changes is zero
and neither registered outcome class (predicts, does not
predict) is earned. The first future head change that alters any
of the nine runs' witnessed cells creates the first observable
flip window, and the landed width table reduces that test to a
lookup. Full detail, including a labeled predecessor observation
outside the registered test, is in the commissioning record.

## What is not claimed

- No predictive verdict on the hinge width is claimed: the
  registered test had no flips to predict on this instance, and
  the width is not adopted as a fragility measure on vacuous
  evidence.
- The theorems are about the boolean premise model of SPEC.md.
  The instrument computes the same quantities on its own
  coordinate form (one witnessed venue per run); that computation
  is a measurement, not a theorem of this repo.
- No width figure is stated for any subject other than the
  frontier instance above.
