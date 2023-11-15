import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Theory.Comparison
import Library.Theory.Prime
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use
import Mathlib.Tactic.GCongr
import Library.Tactic.Cancel

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

/- 2 points -/
theorem problem4a (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k hk
  . simp
  . calc
      B (k + 1) = (B k) + (k + 1 : ℚ )^2 := by rw[B]
      _ = k*(k + 1)*(2*k + 1)/6 + (k + 1 : ℚ)^2 := by rw[hk]
      _ = k*(k + 1)*(2*k + 1)/6 + (k : ℚ)^2 + 2*k + 1 := by ring
      _ = (k+1) * (k + 1 + 1) * (2 * (k + 1) + 1) / 6 := by ring

def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

/- 3 points -/
theorem problem4b (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k hk
  . simp
    calc
      S 0 = 1 := by rw[S]
      _ = 2- 1:= by ring
  . calc
      S (k + 1) = S k + 1 / 2 ^ (k + 1) := by rw[S]
      _ = (2 - 1/2^k) + 1 / 2 ^ (k + 1)  := by rw[hk]
      _ = 2 - 1/2^(k + 1) := by ring

/- 3 points -/
theorem problem4c (n : ℕ) : S n ≤ 2 := by
  simple_induction n with k hk
  . simp
  . calc
      S (k + 1) = 2 - 1/2^(k + 1) := by apply problem4b
      _ ≤ 2 := by aesop

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

/- 3 points -/
theorem problem4d (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  simple_induction n with k hk
  . simp
  . have h2 : k ≤ k + 1 := by extra
    have m : ℕ := (k)
    have h : (k+1)^m ≤ (k+1+1)^m := by
      simple_induction m with j hj
      . simp
      . calc
          (k+1)^(j+1)
            = (k+1) * (k+1)^j := by ring
          _ ≤ (k+1+1) * (k+1)^j := by simp
          _ ≤ (k+1+1) * (k+1+1)^j := by rel [hj]
          _ = (k+1+1)^(j+1) := by ring
    calc
      (k + 1 + 1)! = (k + 2) * (k + 1)! := by rw[factorial]
      _ ≤ (k + 2) * (k + 1)^k := by rel[hk]
      _ ≤ (k + 2) * (k + 1 + 1)^k := by rel [h,h2]
      _ = (k + 2)^(k + 1) := by ring




def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

/- 3 points -/
theorem problem5a (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  . simp
  . simp
  . calc
      q (k + 1 + 1) = 2 * q (k + 1) - q (k) + 6 * k + 6 := by rw [q]
      _ = 2 * (((k:ℤ) + 1) ^ 3 + 1) - ((k:ℤ) ^ 3 + 1) + 6 * k + 6 := by rw[IH1,IH2]
      _ = 2 * ((k:ℤ)^3 + 3*(k:ℤ)^2 + 3 * (k:ℤ) + 2) - (k:ℤ)^3 - 1 + 6 * k + 6 := by ring
      _ = 2 * (k:ℤ)^3 + 6* (k:ℤ)^2 + 6*(k:ℤ) + 4 - (k:ℤ)^3 + 6*(k:ℤ) + 5 := by ring
      _ = ((k:ℤ)+ 1 + 1)^3 + 1 := by ring


def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

/- 3 points -/
theorem problem5b : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  dsimp
  use 7
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  . simp
  . simp
  . calc
      r (k + 1 + 1) = 2 * r (k + 1) + r k := by rw[r]
      _ ≥ 2*2^(k + 1) + r k := by rel[IH2]
      _ ≥ 2*2^(k + 1) + 2^k := by rel[IH1]
      _ = 2^(k + 2) + 2^k := by ring
      _ ≥ 2^(k + 2) := by extra

/- 3 points -/
theorem problem5c (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain h1|h1 := Nat.even_or_odd n
  . obtain ⟨y, hy⟩ := h1
    rw [hy] at hn
    have hn : 0 < y := by linarith
    have IH := problem5c y hn
    obtain ⟨a, x, hx, ha⟩ := IH
    use a + 1
    use x
    constructor
    . apply hx
    . calc
        n = 2 * y := by rw[hy]
        _ = 2 * (2 ^ a * x) := by rw[ha]
        _ = 2 ^ (a + 1) * x := by ring
  . use 0
    use n
    simp
    apply h1
