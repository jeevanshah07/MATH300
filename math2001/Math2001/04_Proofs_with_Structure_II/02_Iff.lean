/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨ k, hk ⟩ := h
    use k
    addarith[hk]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨ k, hk ⟩ := h
    use k
    addarith [hk]

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have h1 : (x+3)*(x-2) = 0 := by
      calc
        (x+3)*(x-2) = x^2 + x - 6 := by ring
        _ = 0 := by rw[h]
    rw[mul_eq_zero] at h1
    obtain ha | hb := h1
    left; addarith[ha]
    right; addarith[hb]
  · intro h
    obtain ha | hb := h
    · calc
      x^2 + x - 6 = (-3)^2 + (-3) - 6 := by rw[ha]
      _ = 0 := by ring
    · calc
      x^2 + x - 6 = (2)^2 + (2) - 6 := by rw[hb]
      _ = 0 := by ring

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h
    have h' : -1 ≤ 2*a - 5 ∧ 2*a - 5 ≤ 1
    · apply abs_le_of_sq_le_sq'
      · calc
          (2*a-5)^2 = 4*(a^2-5*a+5) + 5 := by ring
          _ ≤ 4 * -1 + 5 := by rel[h]
          _ = 1^2 := by ring
      · numbers
    obtain ⟨ ha, hb ⟩ := h'
    have h1 : 2*2 ≤ 2*a := by addarith[ha]
    cancel 2 at h1
    have h2 : 2*a ≤ 2 * 3 := by addarith[hb]
    cancel 2 at h2
    interval_cases a
    · left; rfl
    · right; rfl
  · intro h
    obtain ha | hb := h
    · rw[ha]
      numbers
    · rw[hb]
      numbers

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain h | h := hn2
  · use 2; addarith[h]
  · use 3; addarith[h]

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain h | h := hn1
  · use 2; addarith[h]
  · use 3; addarith[h]

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h
    have h1: 2 * x = 2 * 6 := by addarith[h]
    cancel 2 at h1
  · intro h
    rw[h]; numbers

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro h
    obtain ⟨ k, hk ⟩ := h
    constructor
    · use 9 * k
      calc
        n = 63 * k := by rw[hk]
        _ = 7 * (9 * k) := by ring
    · use 7 * k
      calc
        n = 63 * k := by rw[hk]
        _ = 9 * (7 * k):= by ring
  · intro h
    obtain ⟨ ha, hb ⟩ := h
    obtain ⟨ k, hk ⟩ := ha
    obtain ⟨ t, ht ⟩ := hb
    use 4*t - 3*k
    calc
      n = 28*n - 27*n := by ring
      _ = 28*(9*t) - 27*n := by rw[ht]
      _ = 28*(9*t) - 27*(7*k) := by rw[hk]
      _ = 63*(4*t - 3*k) := by ring

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  · intro h
    obtain ⟨ k, hk ⟩ := h
    use k
    rw[hk]
    ring
  · intro h
    obtain ⟨ k, hk ⟩ := h
    use k
    addarith[hk]

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  rw [dvd_iff_modEq] at *
  calc
      2 * b ^ 3 - b ^ 2 + 3 * b ≡ 2 * 0 ^ 3 - 0 ^ 2 + 3 * 0 [ZMOD a] := by rel[hab]
      _ = 0 := by numbers

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h
    have h1 : k ≥ 0 := by exact Nat.zero_le k
    have h2 : k^2 < 3^2 := by
      calc
        k^2 ≤ 6 := by rel[h]
        _ < 3^2 := by numbers
    cancel 2 at h2
    interval_cases k
    · left; rfl
    · right; left; rfl;
    · right; right; rfl;
  · intro h
    obtain h1 | h1 | h1 := h
    repeat{rw[h1]; numbers}
