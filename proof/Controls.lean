/-
  Standing controls for the hinge width development. Each control
  is a concrete computation or a short case argument, and each
  shows one hypothesis of the main theorems doing real work:

  - sentinel: with no failing configuration in the space, a
    qualified configuration's width is the sentinel n + 1 and it
    is not on the boundary — the failing-existence hypothesis of
    rim is load-bearing.

  - strict: under a strengthening at two premises, one
    configuration's width grows strictly, from one to two — the
    monotonicity of grow is not vacuous.

  - drop: under a change that is not a strengthening, a width
    falls to zero — the strengthening hypothesis of grow is
    load-bearing.
-/

import Hinge

namespace Controls

open Hinge

/-- Qualified exactly when the first premise holds. -/
def low : Config → Bool := fun c => match c with
  | true :: _ => true
  | _ => false

/-- Qualified everywhere except the all-false configuration:
    a strengthening of low. -/
def high : Config → Bool := fun c => match c with
  | [false, false] => false
  | _ => true

/-- Fails exactly the all-true configuration: not a
    strengthening of low, which qualifies it. -/
def flip : Config → Bool := fun c => match c with
  | [true, true] => false
  | _ => true

theorem sentinel :
    width (fun _ => true) 0 [] = 1 ∧
    ¬ boundary (fun _ => true) 0 [] := by
  constructor
  · decide
  · rintro ⟨-, y, -, hqy, -⟩
    simp at hqy

theorem strict :
    width low 2 [true, true] = 1 ∧
    width high 2 [true, true] = 2 ∧
    (∀ y, low y = true → high y = true) := by
  refine ⟨by decide, by decide, ?_⟩
  intro y hy
  cases y with
  | nil =>
    change false = true at hy
    exact Bool.noConfusion hy
  | cons b bs =>
    cases b with
    | false =>
      change false = true at hy
      exact Bool.noConfusion hy
    | true => rfl

theorem drop :
    width flip 2 [true, true] = 0 ∧
    ¬ (∀ y, low y = true → flip y = true) := by
  constructor
  · decide
  · intro h
    have h2 := h [true, true] rfl
    change false = true at h2
    exact Bool.noConfusion h2

end Controls
