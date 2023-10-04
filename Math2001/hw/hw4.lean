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

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

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

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain hae | hao := Int.even_or_odd a
  . obtain hbe | hbo := Int.even_or_odd b
    . left
      obtain ⟨ x,hx⟩ := hae
      obtain ⟨ y,hy⟩ := hbe
      have h1 : Even (a - b ) := by
        use x - y 
        calc
          a - b = 2*x - 2*y := by rw[hx,hy]
          _ = 2 * (x - y) := by ring
          _ = x - y + (x - y) := by ring
      apply h1
    . obtain hce | hco := Int.even_or_odd c
      . right
        left
        obtain ⟨ x,hx⟩ := hae
        obtain ⟨ y,hy⟩ := hce
        have h1 : Even (a + c ) := by
          use x + y 
          calc
            a + c = 2*x + 2*y := by rw[hx,hy]
            _ = 2 * (x + y) := by ring
            _ = x + y + (x + y) := by ring
        apply h1
      . obtain ⟨ x,hx⟩ := hbo
        obtain ⟨ y,hy⟩ := hco
        right
        right
        have h1 : Even (b - c ) := by
          use x - y 
          calc
            b - c = 2*x + 1 - (2*y + 1) := by rw[hx,hy]
            _ = 2 * (x - y) := by ring
            _ = x - y + (x - y) := by ring
        apply h1
  . obtain hbe | hbo := Int.even_or_odd b
    . obtain hce | hco := Int.even_or_odd c
      . obtain ⟨ x,hx⟩ := hbe
        obtain ⟨ y,hy⟩ := hce 
        right 
        right
        have h1 : Even (b - c ) := by
          use x - y 
          calc
            b - c = 2*x - 2*y := by rw[hx,hy]
            _ = 2 * (x - y) := by ring
            _ = x - y + (x - y) := by ring
        apply h1
      . obtain ⟨ x,hx⟩ := hao
        obtain ⟨ y,hy⟩ := hco
        right 
        left
        have h1 : Even (a + c ) := by
          use x + y + 1
          calc
            a + c = 2*x + 1 + (2*y + 1) := by rw[hx,hy]
            _ = 2 * (x + y + 1) := by ring
            _ = (x + y + 1) + (x + y + 1) := by ring
        apply h1  
    . obtain ⟨ x,hx⟩ := hao
      obtain ⟨ y,hy⟩ := hbo
      left
      have h1 : Even (a - b ) := by
        use x - y 
        calc
          a - b = 2*x + 1 - (2*y + 1) := by rw[hx,hy]
          _ = 2 * (x - y) := by ring
          _ = x - y + (x - y) := by ring
      apply h1


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
  have h3 : 1 ≤ 3 → 3 ≤ 5 → 3 ∣ n := hn 3
  simp at h3
  have h5 : 1 ≤ 5 → 5 ≤ 5 → 5 ∣ n := hn 5
  simp at h5
  obtain ⟨x, hx⟩ := h3
  obtain ⟨y, hy⟩ := h5
  dsimp [(· ∣ ·)]
  use 2*x - 3 * y
  calc
    n = 10*n - 9*n := by ring
    _ = 10 * (3*x) - 9*n := by rw[hx]
    _ = 10 * (3*x) - 9*(5*y) := by rw[hy]
    _ = 30*x - 45 * y := by ring
    _ = 15 * (2*x - 3 * y) := by ring




example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  dsimp
  use 7
  intro x hx
  calc 
    x^3 + 3* x = x * x^2 + 3 * x := by ring
    _ ≥ 7 * x^2 + 3 * x := by rel[hx]
    _ ≥ 7 * x^2 + 3 * 7 := by rel[hx]
    _ = 7 * x^2 + 21 := by ring
    _ = 7 * x ^ 2 + 12 + 9:= by ring
    _ ≥ 7 * x ^ 2 + 12 := by extra




example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  . intro h1
    have h2 : (x+3)*(x - 2) = 0 := by
      calc
        (x + 3)*(x - 2) = x^2 + 3*x - 2*x - 6 := by ring
        _ =  x ^ 2 + x - 6 := by ring
        _ = 0 := by rw[h1]
    have h3 : x + 3 = 0 ∨ x - 2 = 0 := by apply eq_zero_or_eq_zero_of_mul_eq_zero h2
    obtain h4 | h5 := h3
    . left
      have h6 : x = -3 := by
        calc
          x = x + 3 - 3 := by ring
          _ = 0 - 3:= by rw[h4]
          _ = -3 := by ring 
      apply h6
    . right
      have h6 : x = 2 := by
        calc
          x = x -2 +2 := by ring
          _ = 0 + 2:= by rw[h5]
          _ = 2 := by ring 
      apply h6
  . intro h2
    obtain hx | hx := h2
    . calc
        x^2 + x - 6 = (-3)^2 + - 3 - 6 := by rw[hx]
        _ = 0 := by ring 
    . calc
        x^2 + x - 6 = (2)^2 + 2 - 6 := by rw[hx]
        _ = 0 := by ring 

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  . intro h1
    have hu : 0 ≤1  := by ring
    have h3 : -1 ≤ 2*a - 5 ∧ 2* a - 5 ≤ 1
    . apply abs_le_of_sq_le_sq' 
      calc
        (2*a - 5)^2 = 4*(a^2 - 5*a + 5) + 5 := by ring
        _ ≤ 4 * - 1 + 5 := by rel[h1]
        _ = 1^2 := by ring
      numbers
    obtain ⟨ hx,hy ⟩ := h3
    have h4 : 2 * a ≥ 4:= by
      calc 
        2 * a = 2 * a - 5 + 5 := by ring 
        _ ≥ (-1 + 5):= by rel[hx]
        _ = 4:= by ring
    have h5 : a ≥ 2 := by 
      calc
        a = (2 * a) / 2 := by aesop
        _ ≥ (4) / 2 := by rel[h4]
        _ = 2 := by ring 

    interval_cases a
    . left
      numbers
    . right
      numbers
  . intro h1