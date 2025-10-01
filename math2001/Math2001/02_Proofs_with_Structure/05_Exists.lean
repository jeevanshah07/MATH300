/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' : 0 < x * (-t) := by
      calc
        0 < (-x) * t := by addarith[hxt]
        _ = x * (-t) := by ring
    cancel x at hxt'
    apply ne_of_lt
    addarith[hxt']

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1, a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  · calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel[h]
  · calc
    q = (q + q) / 2 := by ring
    _ > (p + q) / 2 := by rel[h]

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3; numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6, 7; numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.25; constructor; repeat {numbers}

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3; numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have h := le_or_gt 0 x
  obtain h1 | h2 := h
  · use x+1
    calc
      (x+1)^2 = x^2 + 1 + 2*x := by ring
      _ > 2 * x := by extra
      _ = x + x := by ring
      _ ≥ 0 + x := by rel[h1]
      _ = x := by ring
  · use x-1
    calc
      (x-1)^2 = x^2 + 1 - 2*x := by ring
      _ ≥ 0 - 2 * x := by extra
      _ ≥ 0 := by addarith[h2]
      _ > x := by rel[h2]

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨ k, hk ⟩ := h
  have h1 : (k-1) * (t-1) < 0 := by
    calc
      (k-1)*(t-1) = (k*t + 1) - (k + t) := by ring
      _ < 0 := by addarith[hk]
  intro h
  have h2 : t-1 = 0 := by rw[h]; numbers
  have h3 : (k-1) * (t-1) =0 := by
    calc
      (k-1)*(t-1) = (k-1)*0 := by rw[h2]
      _ = 0 := by ring
  addarith[h1, h3]

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨ k, hk ⟩ := h
  have hn := le_or_succ_le k 2
  obtain h1 | h2 := hn
  · apply ne_of_lt
    calc
      m = 2 * k := by rw[hk]
      _ ≤ 2 * 2 := by rel[h1]
      _ < 5 := by numbers
  · apply ne_of_gt
    calc
      m = 2 * k := by rw[hk]
      _ ≥ 2 * 3 := by rel[h2]
      _ > 5 := by numbers

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  have h:= le_or_succ_le n 2
  obtain h1 | h2 := h
  · use 2
    calc
      n * 2 + 7 ≤ 2 * 2 + 7 := by rel[h1]
      _ = 11 := by numbers
      _ ≤ 11 + 5 := by extra
      _ = 2 * 2^3 := by numbers
  · use n
    calc
      2 * n^3 = 2*n^3 - n^2 - 7 + n^2 + 7 := by ring
      _ = n^2*(2*n-1) -7 + n^2 + 7 := by ring
      _ ≥ 3^2*(2*3-1) - 7 + n^2 + 7 := by rel[h2]
      _ = 38 + n^2 + 7 := by ring
      _ ≥ n^2 + 7 := by extra
      _ = n*n + 7 := by ring

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (b+c-a)/2, (a+c-b)/2, (a+b-c)/2
  constructor
  addarith[ha]
  constructor
  addarith[hb]
  constructor
  addarith[hc]
  constructor
  ring
  constructor
  ring
  ring
