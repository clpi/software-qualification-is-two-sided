/-
  Qualification is two-sided: the hinge width development.

  A configuration is one boolean per premise. The configuration
  space of a subject is finite by the definition of qualification;
  here it is the explicit list of every boolean list of a fixed
  length, so finiteness is by construction, not a hypothesis.

  Distance is counted in single-premise changes: the number of
  positions at which two configurations differ.

  The hinge width of a configuration under a qualification is the
  least distance to a configuration that fails the qualification —
  the dual unqualified witness of the claim. Two theorems:

  - rim: for a qualified configuration, in a space that holds a
    failing configuration, hinge width one holds exactly at the
    qualification boundary (a failing configuration one change
    away). Equivalently the margin, width minus one, is zero
    exactly at the boundary — the register's "width zero" in
    margin form; the off-by-one between the two forms is stated
    here, not hidden.

  - grow: width is monotone under premise strengthening, where
    strengthening enlarges the qualified set: every configuration
    qualified before remains qualified. The failing set only
    shrinks, so the least distance to it can only grow.
-/

namespace Hinge

/-- A configuration: one boolean per premise. -/
abbrev Config := List Bool

/-- The finite configuration space: every boolean list of the
    given length, as an explicit list. -/
def space : Nat → List Config
  | 0 => [[]]
  | n + 1 => (space n).map (fun c => true :: c) ++ (space n).map (fun c => false :: c)

theorem memspace {n : Nat} {c : Config} : c ∈ space n ↔ c.length = n := by
  induction n generalizing c with
  | zero =>
    simp only [space, List.mem_singleton, List.length_eq_zero_iff]
  | succ n ih =>
    constructor
    · intro h
      simp only [space, List.mem_append, List.mem_map] at h
      rcases h with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ <;>
        rw [List.length_cons, ih.mp hd]
    · intro h
      cases c with
      | nil => simp at h
      | cons b d =>
        have hd : d.length = n := by
          rw [List.length_cons] at h
          omega
        have hdm : d ∈ space n := ih.mpr hd
        simp only [space, List.mem_append, List.mem_map]
        cases b
        · exact Or.inr ⟨d, hdm, rfl⟩
        · exact Or.inl ⟨d, hdm, rfl⟩

/-- Distance in single-premise changes: positions that differ. -/
def dist : Config → Config → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: as, b :: bs => (if a = b then 0 else 1) + dist as bs

theorem distself : ∀ (c : Config), dist c c = 0 := by
  intro c
  induction c with
  | nil => rfl
  | cons a as ih => simp [dist, ih]

theorem distzero {x y : Config} (hlen : x.length = y.length) :
    dist x y = 0 → x = y := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => intro _; rfl
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases y with
    | nil => simp at hlen
    | cons b bs =>
      intro h
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [dist] at h
      have hab : a = b := by
        by_cases hc : a = b
        · exact hc
        · rw [if_neg hc] at h
          exfalso
          omega
      have hrest : dist as bs = 0 := by
        rw [if_pos hab, Nat.zero_add] at h
        exact h
      rw [hab, ih hlen hrest]

theorem distlen {x y : Config} (hlen : x.length = y.length) :
    dist x y ≤ x.length := by
  induction x generalizing y with
  | nil =>
    have h0 : dist [] y = 0 := by cases y <;> rfl
    rw [h0]
    exact Nat.zero_le _
  | cons a as ih =>
    cases y with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      have h := ih hlen
      simp only [dist, List.length_cons]
      by_cases hc : a = b
      · rw [if_pos hc]; omega
      · rw [if_neg hc]; omega

/-- The hinge width: the least distance from x to a configuration
    failing q, over the finite space. The sentinel n + 1 stands for
    "no failing configuration": every real distance is at most n. -/
def width (q : Config → Bool) (n : Nat) (x : Config) : Nat :=
  (((space n).filter (fun y => !q y)).map (dist x)).foldr min (n + 1)

theorem foldrminle {s v : Nat} {l : List Nat} (h : v ∈ l) :
    l.foldr min s ≤ v := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
    simp only [List.foldr_cons]
    cases h with
    | head => exact Nat.min_le_left _ _
    | tail _ hm => exact Nat.le_trans (Nat.min_le_right _ _) (ih hm)

theorem minchoice (a b : Nat) : min a b = a ∨ min a b = b := by
  by_cases h : a ≤ b
  · exact Or.inl (Nat.min_eq_left h)
  · have h2 : b ≤ a := by omega
    exact Or.inr (Nat.min_eq_right h2)

theorem foldrminmem {s : Nat} {l : List Nat} :
    l.foldr min s = s ∨ l.foldr min s ∈ l := by
  induction l with
  | nil => exact Or.inl rfl
  | cons a as ih =>
    simp only [List.foldr_cons]
    rcases minchoice a (as.foldr min s) with h | h
    · rw [h]; exact Or.inr List.mem_cons_self
    · rw [h]
      rcases ih with h2 | h2
      · rw [h2]; exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ h2)

theorem foldrminge {s k : Nat} {l : List Nat}
    (hall : ∀ v ∈ l, k ≤ v) (hs : k ≤ s) : k ≤ l.foldr min s := by
  induction l with
  | nil => simpa using hs
  | cons a as ih =>
    simp only [List.foldr_cons]
    exact (Nat.le_min).mpr ⟨hall a List.mem_cons_self,
      ih (fun v hv => hall v (List.mem_cons_of_mem _ hv))⟩

theorem foldrles {s : Nat} {l : List Nat} : l.foldr min s ≤ s := by
  induction l with
  | nil => show s ≤ s; exact Nat.le_refl s
  | cons a as ih =>
    simp only [List.foldr_cons]
    omega

/-- A fold of minima over a larger list is at most the fold over
    any sublist: the larger fold either attains the sentinel or
    some member, and membership carries over the subset. -/
theorem foldrminsub {s : Nat} {l₁ l₂ : List Nat} (h : l₁ ⊆ l₂) :
    l₂.foldr min s ≤ l₁.foldr min s := by
  rcases foldrminmem (s := s) (l := l₁) with h1 | h1
  · rw [h1]
    exact foldrles
  · exact foldrminle (h h1)

/-- Filtering by a weaker predicate keeps a sublist: if every
    configuration passing r also passes p, the r-filtered mapped
    list is a sublist of the p-filtered mapped list. -/
theorem filtersub {p r : Config → Bool} (h : ∀ y, r y = true → p y = true)
    (l : List Config) (f : Config → Nat) :
    (l.filter r).map f ⊆ (l.filter p).map f := by
  intro v hv
  simp only [List.mem_map, List.mem_filter] at hv ⊢
  rcases hv with ⟨y, ⟨hy, hr⟩, rfl⟩
  exact ⟨y, ⟨hy, h y hr⟩, rfl⟩

/-- The qualification boundary: qualified, with a failing
    configuration one single-premise change away. -/
def boundary (q : Config → Bool) (n : Nat) (x : Config) : Prop :=
  q x = true ∧ ∃ y ∈ space n, q y = false ∧ dist x y = 1

/-- A failing configuration of the space exists. -/
def fails (q : Config → Bool) (n : Nat) : Prop :=
  ∃ y ∈ space n, q y = false

theorem negation {q : Config → Bool} {y : Config} (h : (!q y) = true) :
    q y = false := by
  cases hq : q y with
  | false => rfl
  | true => simp [hq] at h

/-- A qualified configuration's width is at least one: the only
    configuration at distance zero from x is x itself, and x
    qualifies, so no failing configuration sits at distance zero. -/
theorem positive {q : Config → Bool} {n : Nat} {x : Config}
    (hx : x ∈ space n) (hq : q x = true) : 1 ≤ width q n x := by
  have hxlen : x.length = n := memspace.mp hx
  unfold width
  apply foldrminge (s := n + 1) (k := 1)
  · intro v hv
    simp only [List.mem_map, List.mem_filter] at hv
    rcases hv with ⟨z, ⟨hz, hqz⟩, rfl⟩
    have hqzf : q z = false := negation hqz
    rcases Nat.eq_zero_or_pos (dist x z) with h0 | hpos
    · have hxz : x = z := distzero (by rw [hxlen, memspace.mp hz]) h0
      rw [← hxz, hq] at hqzf
      exact Bool.noConfusion hqzf
    · exact hpos
  · omega

theorem rim {q : Config → Bool} {n : Nat} {x : Config}
    (hx : x ∈ space n) (hq : q x = true) (hf : fails q n) :
    width q n x = 1 ↔ boundary q n x := by
  have hxlen : x.length = n := memspace.mp hx
  constructor
  · intro hw
    have hne : width q n x ≠ n + 1 := by
      rcases hf with ⟨y, hy, hqy⟩
      have hle : width q n x ≤ dist x y := by
        unfold width
        apply foldrminle
        simp only [List.mem_map, List.mem_filter]
        exact ⟨y, ⟨hy, by simp [hqy]⟩, rfl⟩
      have hdist : dist x y ≤ n := by
        have h2 := distlen (x := x) (y := y) (by rw [hxlen, memspace.mp hy])
        rwa [hxlen] at h2
      omega
    have hmem : width q n x ∈ ((space n).filter (fun y => !q y)).map (dist x) := by
      rcases foldrminmem (s := n + 1)
        (l := ((space n).filter (fun y => !q y)).map (dist x)) with h | h
      · exact absurd h hne
      · exact h
    simp only [List.mem_map, List.mem_filter] at hmem
    rcases hmem with ⟨y, ⟨hy, hqy⟩, hdist⟩
    exact ⟨hq, y, hy, negation hqy, by rw [hdist, hw]⟩
  · rintro ⟨_, y, hy, hqy, hdist⟩
    have hle : width q n x ≤ 1 := by
      have h2 := foldrminle (s := n + 1)
        (l := ((space n).filter (fun y => !q y)).map (dist x))
        (v := dist x y) (by
          simp only [List.mem_map, List.mem_filter]
          exact ⟨y, ⟨hy, by simp [hqy]⟩, rfl⟩)
      rwa [hdist] at h2
    have hge : 1 ≤ width q n x := positive hx hq
    omega

/-- The margin form: width minus one is zero exactly at the
    boundary. This is the register's "hinge width zero holds
    exactly at qualification boundaries", with the width of the
    claim (a distance) and its margin (the distance minus one)
    kept apart. -/
theorem margin {q : Config → Bool} {n : Nat} {x : Config}
    (hx : x ∈ space n) (hq : q x = true) (hf : fails q n) :
    width q n x - 1 = 0 ↔ boundary q n x := by
  have hge : 1 ≤ width q n x := positive hx hq
  constructor
  · intro h
    exact (rim hx hq hf).mp (by omega)
  · intro hb
    have hw : width q n x = 1 := (rim hx hq hf).mpr hb
    omega

/-- Monotonicity under premise strengthening: when the qualified
    set only grows (q y = true → q' y = true for every y), no
    configuration's hinge width decreases. -/
theorem grow {q q' : Config → Bool} (h : ∀ y, q y = true → q' y = true)
    (n : Nat) (x : Config) :
    width q n x ≤ width q' n x := by
  apply foldrminsub (s := n + 1)
  apply filtersub (l := space n) (f := dist x)
  intro y hy
  change (!q' y) = true at hy
  change (!q y) = true
  cases h1 : q y with
  | false => simp [h1]
  | true =>
    have h2 : q' y = true := h y h1
    simp [h2] at hy

end Hinge
