/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
    calc 13 = 3 * k := hk
      _ ≥ 3 * 5 := by rel[h5]
    numbers at h

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨ n, hn ⟩ := h
  obtain ha | hb : n ≤ 1 ∨ n ≥ 2 := by apply le_or_gt n 1
  · have := calc
      2 = n^2 := by rw[hn]
      _ ≤ 1^2 := by rel[ha]
    numbers at this
  · have := calc
      2 = n^2 := by rw[hn]
      _ ≥ 2^2 := by rel[hb]
    numbers at this

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro h1 h2
    rw [Int.odd_iff_modEq] at h1
    rw [Int.even_iff_modEq] at h2
    have h := calc
      1 ≡ n [ZMOD 2] := by rel[h1]
      _ ≡ 0 [ZMOD 2] := by rel[h2]
    numbers at h
  · intro h1
    obtain ha | hb := Int.even_or_odd n
    · contradiction
    · apply hb


example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h := calc
      1 = 1^2 := by numbers
      _ ≡ n^2 [ZMOD 3] := by rel[hn]
      _ ≡ 2 [ZMOD 3] := by rel[h]
    numbers at h
  · have := calc
      1 ≡ 1 + 3*1 [ZMOD 3] := by extra
      _ = 2^2 := by ring
      _ ≡ n^2 [ZMOD 3] := by rel[hn]
      _ ≡ 2 [ZMOD 3] := by rel[h]
    numbers at this

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  have := calc b*q < a := by rel[hq₁]
    _ = b*k := by rw[hk]
  cancel b at this
  have := calc q+1 ≤ k := by exact this
    _ < q+1 := by rel[h1]
  addarith[this]

example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · use m; rw[hl]; ring
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : l < T
  · have := calc
      T * l ≤ m * l := by rel[hmT]
      _ = p := by rw[hl]
      _ < T^2 := by rel[hTp]
      _ = T*T := by ring
    cancel T at this
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro ht
  obtain ⟨ k, hk ⟩ := ht
  obtain ⟨ ha, hb ⟩ := hk
  have := calc
    4 ≥ k := by rel[ha]
    _ ≥ 5 := by rel[hb]
  numbers at this

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro ha
  obtain ⟨ k, hk ⟩ := ha
  obtain ⟨ h1, h2 ⟩ := hk
  have :=
    calc k^2 ≤ 8 := by rel[h1]
    _ < 3^2 := by numbers
  cancel 2 at this
  have := calc
    k^3 = k * k^2 := by ring
    _ ≤ 3 * 8 := by rel[this, h1]
    _ = 24 := by ring
  have := calc
    24 ≥ k^3 := by rel[this]
    _ ≥ 30 := by rel[h2]
  numbers at this

example : ¬ Int.Even 7 := by
  intro h
  rw[Int.even_iff_modEq] at h
  have := calc
    0 ≡ 7 [ZMOD 2] := by rel[h]
    _ = 2*3 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra
  numbers at this

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  intro h
  obtain ⟨ ha, hb ⟩ := h
  have hn : n = 4 := by addarith[hn]
  have := calc
    10 = n^2 := by rw[hb]
    _ = 4^2 := by rw[hn]
    _ = 16 := by ring
  numbers at this

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  intro h
  have hx : x^2 < 3^2 := by
    calc
      x^2 < 9 := by rel[hx]
      _ = 3^2 := by ring
  have : -3 < x ∧ x < 3 := by
    apply abs_lt_of_sq_lt_sq' hx (by numbers)
  obtain ⟨ ha, hb ⟩ := this
  obtain h1 | h2 := h
  · have := calc
      -3 ≥ x := by rel[h1]
      _ > -3 := by rel[ha]
    numbers at this
  · have := calc
      3 ≤ x := by rel[h2]
      _ < 3 := by rel[hb]
    numbers at this


example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  intro h
  obtain ⟨ n, hn ⟩ := h
  have : ¬ Nat.Even (2*n+1) := by
    rw[← Nat.odd_iff_not_even]
    use n; ring
  apply this
  have := calc 2*n+1 = n + (n+1) := by ring
    _ > n := by extra
  exact hn _ this

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro hn
  mod_cases n%4
  · have := calc
      0 = 0^2 := by ring
      _ ≡ n^2 [ZMOD 4] := by rel[H]
      _ ≡ 2 [ZMOD 4] := by rel[hn]
    numbers at this
  · have := calc
      1 = 1^2 := by ring
      _ ≡ n^2 [ZMOD 4] := by rel[H]
      _ ≡ 2 [ZMOD 4]:= by rel[hn]
    numbers at this
  · have := calc
      0 ≡ 0 + 4*1 [ZMOD 4] := by extra
      _ = 2^2 := by ring
      _ ≡ n^2 [ZMOD 4] := by rel[H]
      _ ≡ 2 [ZMOD 4] := by rel[hn]
    numbers at this
  · have := calc
      1 ≡ 1 + 4*2 [ZMOD 4] := by extra
      _ = 3^2 := by ring
      _ ≡ n^2 [ZMOD 4] := by rel[H]
      _ ≡ 2 [ZMOD 4] := by rel[hn]
    numbers at this

example : ¬ Prime 1 := by
  rintro ⟨ h, _ ⟩
  numbers at h

example : Prime 97 := by
  apply prime_test; numbers
  intro n h1 h2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases n
  repeat {use 48; constructor <;> numbers}
  repeat {use 47; constructor <;> numbers}
  repeat {use 46; constructor <;> numbers}
  repeat {use 45; constructor <;> numbers}
  repeat {use 44; constructor <;> numbers}
  repeat {use 43; constructor <;> numbers}
  repeat {use 42; constructor <;> numbers}
  repeat {use 43; constructor <;> numbers}
  repeat {use 42; constructor <;> numbers}
  repeat {use 41; constructor <;> numbers}
  repeat {use 40; constructor <;> numbers}
  repeat {use 39; constructor <;> numbers}
  repeat {use 38; constructor <;> numbers}
  repeat {use 37; constructor <;> numbers}
  repeat {use 36; constructor <;> numbers}
  repeat {use 35; constructor <;> numbers}
  repeat {use 34; constructor <;> numbers}
  repeat {use 33; constructor <;> numbers}
  repeat {use 32; constructor <;> numbers}
  repeat {use 31; constructor <;> numbers}
  repeat {use 30; constructor <;> numbers}
  repeat {use 29; constructor <;> numbers}
  repeat {use 28; constructor <;> numbers}
  repeat {use 27; constructor <;> numbers}
  repeat {use 26; constructor <;> numbers}
  repeat {use 25; constructor <;> numbers}
  repeat {use 24; constructor <;> numbers}
  repeat {use 23; constructor <;> numbers}
  repeat {use 22; constructor <;> numbers}
  repeat {use 21; constructor <;> numbers}
  repeat {use 20; constructor <;> numbers}
  repeat {use 19; constructor <;> numbers}
  repeat {use 18; constructor <;> numbers}
  repeat {use 17; constructor <;> numbers}
  repeat {use 16; constructor <;> numbers}
  repeat {use 15; constructor <;> numbers}
  repeat {use 14; constructor <;> numbers}
  repeat {use 13; constructor <;> numbers}
  repeat {use 12; constructor <;> numbers}
  repeat {use 11; constructor <;> numbers}
  repeat {use 10; constructor <;> numbers}
  repeat {use 9; constructor <;> numbers}
  repeat {use 8; constructor <;> numbers}
  repeat {use 7; constructor <;> numbers}
  repeat {use 6; constructor <;> numbers}
  repeat {use 5; constructor <;> numbers}
  repeat {use 4; constructor <;> numbers}
  repeat {use 3; constructor <;> numbers}
  repeat {use 2; constructor <;> numbers}
  repeat {use 1; constructor <;> numbers}
