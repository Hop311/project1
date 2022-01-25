
import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers

def tendsto (a : ℕ → ℝ) (t : ℝ) : Prop := ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε
