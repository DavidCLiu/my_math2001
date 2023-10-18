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

-- Exercise 4a
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  . intro h1
    dsimp [(· ∣ ·)]
    obtain ⟨a, ha⟩ := h1
    constructor
    . use 9*a
      calc
        n = 63*a:= by rw[ha]
        _ = 7*(9*a) := by ring
    . use 7*a
      calc
        n = 63*a:= by rw[ha]
        _ = 9*(7*a) := by ring
  . intro h
    obtain ⟨h1,h2⟩ := h   
    obtain ⟨a, ha1⟩ := h1
    obtain ⟨a2, ha2⟩ := h2
    dsimp [(· ∣ ·)]
    use 4*a - 5*a2
    calc 
      n = 36*n - 35*n := by ring
      _ = 36 * (7 * a) - 35 * n := by rw[ha1]
      _ = 36 * (7 * a) - 35 * (9 * a2) := by rw[ha2]
      _ = 63*4*a - 63*5*a2:= by ring
      _ = 63*(4*a - 5 * a2) := by ring

-- Exercise 4b
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  . intro h1 
    have h2: k*k < 3*3 := by 
      calc
        k*k = k^2 := by ring
        _ ≤ 6 := by rel[h1]
        _ < 9 := by numbers
        _ = 3^2 := by ring  
    rw[←Nat.mul_self_lt_mul_self_iff] at h2
    interval_cases k
    . left
      ring
    . right
      left
      ring
    . right
      right
      ring
  . intro h1
    obtain h|h|h := h1
    . calc
        k^2 = k*k := by ring
        _ = 0*0:= by rw[h]
        _ ≤ 6 := by extra
    . calc
        k^2 = k*k := by ring
        _ = 1*1:= by rw[h]
        _ = 1 := by ring
        _ ≤ 6 := by aesop
    . calc
        k^2 = k*k := by ring
        _ = 2*2:= by rw[h]
        _ = 4 := by ring
        _ ≤ 6 := by aesop


-- Exercise 5a
example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  . intro a
    intro ha
    intro ha2
    have h1 : -1 ≤ a - 2 := by 
      calc
        a- 2 = a - 2 := by ring
        _ ≥ 1 - 2 := by rel[ha]  
        _ = -1 := by ring
    have h2 : a-2≤1 := by 
      calc
        a- 2 = a - 2 := by ring
        _ ≤ 3 - 2 := by rel[ha2]  
        _ = 1 := by ring
    have h3 : (a - 2)^2 ≤ 1 ^ 2 := by apply sq_le_sq' h1 h2
    have h4 : (a - 2)^2 ≤ 1 := by 
      calc
        (a - 2)^2 ≤ 1 ^ 2 := by rel[h3]
        _ = 1 := by ring
    apply h4
  . intro y
    intro hy
    have h1 := hy 1 (by numbers) (by numbers)
    have h2 := hy 3 (by numbers) (by numbers)
    have h3 : (y - 2)^2 ≤ 0 := by
      calc
        (y - 2)^2 = ((1 - y)^2 + (3 - y)^2 - 2) / 2 := by ring
        _ ≤ (1 + 1 - 2)/2 := by rel[h1,h2] 
        _ = 0 := by ring
    have h4 : (y - 2)^2 ≥ 0 := by extra
    have h5 : (y - 2)^2 = 0 := by apply le_antisymm' h3 h4
    cancel 2 at h5
    addarith[h5]


-- Exercise 5b
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  . numbers
  . intro y
    intro hy
    have h1 : 4*y = 4*3 := by addarith[hy] 
    cancel 4 at h1   

-- Exercise 5c
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  . intro a
    extra
  . intro y
    intro hy
    obtain h|h := Nat.eq_zero_or_pos y
    . apply h
    . specialize hy 0
      simp at hy
      apply hy
      
-- Exercise 6a
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
  . right
    have h2 : m ≤ p := by apply Nat.le_of_dvd hp' hmp
    obtain h1 | h1 : m = p ∨ m < p := eq_or_lt_of_le h2
    . apply h1
    . have h3 := H m hm_left h1
      contradiction 
    
-- Exercise 6b
example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain h | h := Nat.lt_or_ge a 3
  . obtain h1 | h1 := Nat.lt_or_ge b 2
    . have h3 : a ≤ 2 := by addarith[h]
      have h4 : b ≤ 1 := by addarith[h1]
      have h2 : c^2 < 3^2 := by
        calc
          c^2 = a^2 + b^2 := by rw[h_pyth]
          _ = a * a + b* b := by ring
          _ ≤ 2* 2 + b*b := by rel[h3]
          _ ≤ 2*2 + 1*1 := by rel[h4]
          _ < 3*3 := by numbers
      cancel 2 at h2
      interval_cases c
      . 
        interval_cases a
        . 
          interval_cases b
          . 
            contradiction
        . 
          interval_cases b
          . 
            contradiction
      . 
        interval_cases a
        . 
          interval_cases b
          . 
            contradiction
        . 
          interval_cases b
          . 
            contradiction
    . have h2 : b^2 < c^2 := by 
        calc
          b^2 < a^2 + b ^2 := by extra
          _ = c^2 := by rw[h_pyth]
      cancel 2 at h2
      have h3 : b + 1 ≤ c := by addarith[h2]
      have h5 : a ≤ 2 := by addarith[h]
      have h4 : c^2 < (b+1)^2 := by 
        calc
          c^2 = a^2 + b^2 := by rw[h_pyth]
          _ = a * a + b^2 := by ring
          _ ≤ 2*2 + b^2 := by rel[h5]
          _ = b^2 + 2*2 := by ring
          _ ≤ b^2 + 2*b := by rel[h1]
          _ < b^2 + 2*b + 1 := by extra
          _ = (b + 1)^2 := by ring
      cancel 2 at h4
      have h6: b + 1 < b + 1 := by 
        calc
          b+1 ≤ c := by rel[h3]
          _ < b + 1 := by rel[h4]
      have h7: 1 < 1 := by addarith[h6]
      contradiction
  . apply h

-- Exercise 6c
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  cancel n at h

-- Exercise 6d
example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain ⟨ h1,h2 ⟩ := h
  obtain h3 | h3 := lt_or_eq_of_le h1
  . obtain h_peven | h_podd := Nat.even_or_odd p
    . have h_notevenP : ¬Nat.Even p := by
        intro h4
        obtain ⟨y , hy⟩ := h4 
        have h5 : 2∣p := by
          use y
          rw[hy]
        obtain hx|hx := h2 2 h5
        . contradiction
        . have h6: 2 < 2 := by
            calc
              2 < p := by rel[h3]
              _ = 2 := by rw[hx] 
          contradiction
      right
      contradiction
    . right 
      apply h_podd
  . left
    rw[h3]



