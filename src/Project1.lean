
import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers

def seq := ℕ → ℝ

def tendsto (a : seq) (t : ℝ) : Prop := ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

def convergent (a : seq) : Prop := ∃ t, tendsto a t

def bounded (a : seq) : Prop := ∃ M, ∀ n, |a n| < M

structure subindex :=
  (φ : ℕ → ℕ)
  (mono : strict_mono φ)

instance subindex_fun : has_coe_to_fun subindex (λ _, ℕ → ℕ) := ⟨subindex.φ⟩

def subseq (a : ℕ → ℝ) (s : subindex) : seq := λ n, a (s n)

theorem bolzano_weierstrass (a : seq) (h : bounded a) : ∃ s : subindex, convergent (subseq a s)  :=
begin
  sorry
end
