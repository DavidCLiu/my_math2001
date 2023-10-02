import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use



example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp[Odd] at *
  obtain ⟨k,hk⟩ := hn
  use 7*k + 1
  calc
    7*n - 4 = 7 * (2 * k + 1) - 4 := by rw[hk]
    _ = 2 * (7*k + 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp[Odd] at *
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  use (2 * a * b + 3 * b + a + 1)
  calc
    x*y + 2*y = (2*a + 1)*(2*b + 1) + 2 * (2*b + 1) := by rw[ha,hb]
    _ = 2 * (2* a * b + 3 * b + a + 1) + 1 := by ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp[Even] at *
  obtain ⟨k,hk⟩ := hn
  use 2*k^2 + 2 * k - 3
  calc
    n^2 + 2*n - 5 = (k+k)^2 + 2*(k + k) - 5 := by rw[hk]
    _ = 4*k^2 + 4 * k - 5 := by ring
    _ = 2 * (2*k^2 + 2 * k - 3) + 1 := by ring

-- example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
--   dsimp[Even] at *
--   obtain hx|hx|hx := sprry

example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h1 : (a + b)/2 ≥ a ∨ (a + b)/2 ≤ b := by apply h
  obtain hxt1| hxt2 := h1
  . calc 
      b = 2 * ((a+b)/2) - a := by ring
      _ ≥ 2 * a - a := by rel[hxt1]
      _ = a := by ring
  . calc 
      a = 2 * ((a+b)/2) - b := by ring
      _ ≤  2 * b - b := by rel[hxt2]
      _ = b := by ring

example : ∃ c : ℝ, ∀ x y , x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x y hxy
  have h3 : -3 ≤ x + y ∧ x+y ≤ 3
  . apply abs_le_of_sq_le_sq'
    calc 
        (x + y)^2 ≤ (x + y)^2 + (x - y)^2 := by extra
        _ = 2 * (x^2 + y^2) := by ring
        _ ≤ 2 * 4 := by rel[hxy]
        _ ≤ 3 ^ 2 := by numbers
    numbers
  obtain ⟨hx,hy ⟩ := h3
  apply hx

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  

example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  sorry

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  sorry

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  sorry