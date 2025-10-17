/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init


example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)]
  use 8
  numbers


example : (-2 : ℤ) ∣ 6 := by
  dsimp [( · ∣ · )] at *
  use -3; numbers

example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  obtain ⟨k, hk⟩ := hab
  use k * (a * k + 2)
  calc
    b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) := by rw [hk]
    _ = a * (k * (a * k + 2)) := by ring


example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  dsimp[( · ∣ · )] at *
  obtain ⟨ k, hk ⟩ := hab
  obtain ⟨ t, ht ⟩ := hbc
  use k^2 * t
  calc
    c = b ^ 2 * t := by rw[ht]
    _ = (a * k) ^ 2 * t := by rw[hk]
    _ = a ^ 2 * (k^2 * t) := by ring

example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  dsimp[( · ∣ · )] at *
  obtain ⟨ k, hk ⟩ := h
  use y * k
  calc
    z = x * y * k := by rw[hk]
    _ = x * (y * k) := by ring

example : ¬(5 : ℤ) ∣ 12 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use 2
  constructor
  · numbers -- show `5 * 2 < 12`
  · numbers -- show `12 < 5 * (2 + 1)`


example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := hab
  have H1 :=
    calc
      0 < b := hb
      _ = a * k := hk
  cancel a at H1
  have H : 1 ≤ k := H1
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [H]
    _ = b := by rw [hk]


example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  dsimp[( · ∣ · )] at *
  obtain ⟨ k, hk ⟩ := hab
  have h : 0 < a * k := by
    calc
      0 < b := by rel[hb]
      _ = a * k := by rw[hk]
  cancel k at h

/-! # Exercises -/


example (t : ℤ) : t ∣ 0 := by
  use 0; ring;

example : ¬(3 : ℤ) ∣ -10 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor
  · numbers
  · numbers

example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  dsimp[( · ∣ · )] at *
  obtain ⟨ k, hk ⟩ := h
  use 3 * k - 4 * x * k ^ 2
  calc
    3 * y - 4 * y ^ 2
      = 3 * (x * k) - 4 * (x * k)^2 := by rw[hk]
    _ = x * (3 * k - 4 * x * k^2) := by ring

example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by
  obtain ⟨ k, hk ⟩ := h
  use 2 * m ^ 2 * k ^3 + k
  calc
    2 * n ^ 3 + n = 2 * (m * k)^3 + (m * k) := by rw[hk]
    _ = m * (2 * m^2 * k^3 + k) := by ring

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨ k, hk ⟩ := hab
  use 2 * a^2 * k^3 - a * k^2 + 3 * k
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b
      = 2 * (a * k)^3 - (a*k)^2 + 3 * (a * k) := by rw[hk]
    _ = a * (2 * a^2 * k^3 - a*k^2 + 3 * k) := by ring

example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨ a, ha ⟩ := h1
  obtain ⟨ b, hb ⟩ := h2
  use a^3 * b
  calc
    m = l ^ 3 * b := by rw[hb]
    _ = (k * a)^3 * b := by rw[ha]
    _ = k^3 * (a^3 * b) := by ring

example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by
  obtain ⟨ a, ha ⟩ := hpq
  obtain ⟨ b, hb ⟩ := hqr
  use a^2 * b
  calc
    r = q^2 * b := by rw[hb]
    _ = (p ^ 3 * a)^2 * b := by rw[ha]
    _ = p^6 * (a^2 * b) := by ring

example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by
  use 6
  constructor
  · numbers
  · use 7; numbers

example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  use 2, 1
  constructor
  · numbers
  · constructor
    · numbers
    · use 3
      numbers
