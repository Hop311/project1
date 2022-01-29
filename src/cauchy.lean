
import Project1

namespace my_analysis

  /-- Proposition that a sequence is Cauchy, that is that its terms grow arbitrarily close together. -/
  def seq.cauchy (s : seq) : Prop := ∀ ⦃ε⦄, ε > 0 → ∃ B : ℕ, ∀ ⦃m n⦄, B ≤ m → B ≤ n → |s m - s n| < ε

  /-- Proof that Cauchy sequences are bounded. -/
  theorem cauchy_is_bounded {s : seq} (hc : s.cauchy): s.bounded :=
  begin
    cases hc zero_lt_one with B h,
    have hb : ∀ ⦃n⦄, B ≤ n → |s n| < 1 + |s B|,
      intros n hn,
      have h₁ : |s n| ≤ |s n - s B| + |s B|,
        conv_lhs { rw [← sub_add_cancel (s n) (s B)] },
        exact abs_add (s n - s B) (s B),
      have h₂ : |s n - s B| < 1, from h hn (le_refl B),
      exact lt_of_le_of_lt h₁ (add_lt_add_of_lt_of_le h₂ (le_refl _)),
    apply (bounded_shift s B).mpr,
    use 1 + |s B|, intro n,
    exact le_of_lt (hb le_add_self)
  end

  /-- Proof that Cauchy and convergent are equivalent properties. -/
  theorem convergent_iff_cauchy {s : seq} : s.convergent ↔ s.cauchy :=
  begin
    split,
    { rintros ⟨x, hx⟩ ε hε,
      cases hx (half_pos hε) with B h,
      use B, intros m n hm hn,
      rw [← add_halves ε],
      refine lt_of_le_of_lt _ (add_lt_add (h hm) (h hn)),
      have : |s m - s n| = |(s m - x) + (x - s n)|, by ring_nf,
      rw [this, ← abs_neg (s n - x), neg_sub],
      exact abs_add (s m - x) (x - s n) },
    { intros hc,
      cases bolzano_weierstrass (cauchy_is_bounded hc) with si hcon,
      cases hcon with x hx,
      use x,
      sorry }
  end

end my_analysis