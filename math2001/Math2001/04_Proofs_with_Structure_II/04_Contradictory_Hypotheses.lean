/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  -- the case `1 < m`
  · have h1 : m ≤ p := Nat.le_of_dvd hp' hmp
    obtain ha | hb : m=p ∨ m < p := eq_or_lt_of_le h1
    · right; exact ha
    · specialize H m hm_left hb
      contradiction

example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  have ha1: a ≤ 2 ∨ a ≥ 3 := by apply le_or_gt a 2
  obtain ha2 | ha3 := ha1
  have hb1: b ≤ 1 ∨ b ≥ 2 := by apply le_or_gt b 1
  obtain hb2 | hb3 := hb1
  · have hc : c^2 < 3^2 := by
      calc
        c^2 = a^2 + b^2 := by rw[h_pyth]
        _ ≤ 2^2 + 1^2 := by rel[ha2, hb2]
        _ < 3^2 := by numbers
    cancel 2 at hc
    interval_cases a <;> interval_cases b <;> interval_cases c
    all_goals numbers at h_pyth
  · have hb' : b^2 < c^2 := by
      calc
        b^2 < a^2 + b^2 := by extra
        _ = c^2 := by rw[h_pyth]
    cancel 2 at hb'
    have hb' : b+1 ≤ c := by exact Nat.succ_le_of_lt hb'
    have hc' : c^2 < (b+1)^2 := by
      calc
        c^2 = a^2 + b^2 := by rw[h_pyth]
        _ ≤ 2^2 + b^2 := by rel[ha2]
        _ = b^2 + 2*2 := by ring
        _ ≤ b^2 + 2*b := by rel[hb3]
        _ < b^2 + 2*b + 1 := by extra
        _ = (b+1)^2 := by ring
    cancel 2 at hc'
    exact absurd hb' (Nat.not_le.mpr hc')
  · apply ha3

/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  cancel n at h

example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases n%5
  · have := calc
      0 = 0^2 := by numbers
      _ ≡ n^2 [ZMOD 5] := by rel[H]
      _ ≡ 4 [ZMOD 5] := by rel[hn]
    numbers at this
  · have := calc
      1 = 1^2 := by numbers
      _ ≡ n^2 [ZMOD 5] := by rel[H]
      _ ≡ 4 [ZMOD 5] := by rel[hn]
    numbers at this
  · left; exact H
  · right; exact H
  · have := calc
      1 ≡ 1 + 3*5 [ZMOD 5] := by extra
      _ = 4^2 := by numbers
      _ ≡ n^2 [ZMOD 5] := by rel[H]
      _ ≡ 4 [ZMOD 5] := by rel[hn]
    numbers at this

example : Prime 7 := by
  apply prime_test
  · numbers
  · intro m hm_left hm_right
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    · use 3
      constructor <;> numbers
    · use 2
      constructor <;> numbers
    repeat{use 1; constructor <;> numbers}

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain ha | hb := h3
  · have : x = -2 := by addarith[ha]
    subst this
    norm_num at h2
  · addarith[hb]

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  dsimp[Prime] at *
  obtain ⟨ h1, h2 ⟩ := h
  have h1 : p ≤ 2 ∨ p ≥ 3 := by apply le_or_gt p 2
  obtain ha | hb := h1
  · have h0 : 0 ≤ p := by apply Nat.zero_le
    interval_cases p
    · left; rfl
  · right
    have h2' := h2 2
    by_contra hn
    have : Even p := Nat.even_or_odd p |>.resolve_right hn
    obtain ⟨ k, hk ⟩ := this
    have : 2 ∣ p := by
      use k; exact hk
    have : 2=1 ∨ 2 = p := h2' this
    obtain this | that := this
    · numbers at this
    · subst that
      norm_num at hb
