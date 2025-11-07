/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  · intro a h1 h2
    have h1 : -1 ≤ a-2 := by addarith[h1]
    have h2 : 1 ≥ a-2 := by addarith[h2]
    have h3 : (a-2)^2 ≤ 1^2 := sq_le_sq' (by exact h1) (by exact h2)
    have h3 : (a-2)^2 ≤ 1 := by
      calc
        (a-2)^2 ≤ 1^2 := by rel[h3]
        _ = 1 := by ring
    exact h3
  · intro y h
    have h1 := h 1 (by numbers) (by numbers)
    have h2 := h 3 (by numbers) (by numbers)
    rw [← sub_eq_zero]
    rw [← sq_eq_zero_iff]
    apply le_antisymm
    · calc
      (y-2)^2 = ((1-y)^2 + (3-y)^2 - 2) / 2 := by ring
      _ ≤ (1 + 1 - 2)/2 := by rel[h1, h2]
      _ = 0 := by numbers
    · extra

example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  · numbers
  · intro y hy
    calc
      y = (4 * y - 3 + 3) / 4 := by ring
      _ = (9 + 3) / 4 := by rw[hy]
      _ = 3 := by ring

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  · intro x; exact Nat.zero_le x
  · intro x hx
    exact Nat.le_zero.mp (hx 0)

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 3
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      3 * 1 < 11 - r := by addarith [hr2]
      _ = 3 * q := by rw [hr3]
  cancel 3 at this
  have :=
    calc
      3 * q = 11 - r := by rw [hr3]
      _ < 3 * 4 := by addarith [hr1]
  cancel 3 at this
  interval_cases q
  · sorry
  · addarith[hr3]
