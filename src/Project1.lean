
import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers

--set_option trace.simplify.rewrite true

namespace my_analysis

  /-- Sequence of real numbers indexed by natural numbers. -/
  def seq := ℕ → ℝ

  /-- Sequence formed by taking the absolute value of each term. -/
  noncomputable def seq.abs (s : seq) : seq := λ k, |s k|

  /-- Proposition that a sequence converges to a specified limit. -/
  def tendsto (s : seq) (x : ℝ) : Prop := ∀ ⦃ε⦄, 0 < ε → ∃ B : ℕ, ∀ ⦃n⦄, B ≤ n → |s n - x| < ε
  notation s ` ⟶ ` limit := tendsto s limit

  /-- Proposition that there is a limit to which a sequence converges. -/
  def seq.convergent (s : seq) : Prop := ∃ t, s ⟶ t

  /-- Proposition that a sequence is bounded above and below, in this case within `[-M, M]`. -/
  def seq.bounded (s : seq) : Prop := ∃ M, ∀ n, |s n| ≤ M

  /-- Proposition that every term in a sequence is greater than or equal to any term before it. -/
  def seq.increasing (s : seq) : Prop := ∀ ⦃m n⦄, m < n → s m ≤ s n
  /-- Proposition that every term in a sequence is strictly greater than any term before it. -/
  def seq.strictly_increasing (s : seq) : Prop := ∀ ⦃m n⦄, m < n → s m < s n

  /-- Weakening of strictly increasing to just increasing. -/
  theorem seq.strictly_increasing.to_increasing {s : seq} (si : s.strictly_increasing) : s.increasing :=
    λ m n h, le_of_lt (si h)

  /-- Sequence formed by ignoring the first `n` elements, such that `s.shift 0 = s n`. -/
  def seq.shift (s : seq) (n : ℕ) : seq := λ m, s (m + n)

  /-- Shifting by `0` leaves the sequence unchanged. -/
  @[simp] theorem shift_zero (s : seq) : s.shift 0 = s :=
    by simp only [seq.shift, nat.add_zero]

  /-- For any `m` greater than the shift number `n`, `s m` has been moved to `s.shift n (m - n)`. -/
  theorem shift_ge (s : seq) {n m : ℕ} (h : n ≤ m) : s.shift n (m - n) = s m :=
    by simp only [seq.shift, nat.sub_add_cancel h]

  /-- tendsto is preserved by arbitrary finite shifts (including preserving the limit). -/
  theorem tendsto_shift (s : seq) (x : ℝ) : ∀ n, (s ⟶ x) ↔ (s.shift n ⟶ x) :=
  begin
    intro n, split,
    { intros h ε hε,
      cases h hε with B hB,
      use B, intros m hm,
      exact hB (le_add_right hm : B ≤ m + n) },
    { intros h ε hε,
      cases h hε with B hB,
      use B + n, intros m hm,
      rw [← shift_ge s (nat.le_of_add_le_right hm)],
      exact hB (le_tsub_of_add_le_right hm) }
  end

  /-- For any `n`, the elements `|s m|` for `m < n` are bounded. -/
  theorem finite_prefix_bounded (s : seq) (n : ℕ) : ∃ M, ∀ m < n, |s m| ≤ M :=
  begin
    by_cases h : n = 0,
    { use 0,
      intros m hm,
      rw [h] at hm,
      exact absurd hm (nat.not_lt_zero m) },
    { have h0 : (multiset.map s.abs (multiset.range n)).to_finset.nonempty,
        use |s 0|, simp only [multiset.mem_to_finset, multiset.mem_map, multiset.mem_range],
        use 0, exact ⟨pos_iff_ne_zero.mpr h, rfl⟩,
      use ((multiset.range n).map s.abs).to_finset.max' h0,
      intros m hm,
      apply (multiset.map s.abs (multiset.range n)).to_finset.le_max' (|s m|),
      simp only [multiset.mem_to_finset, multiset.mem_map, multiset.mem_range],
      use m, exact ⟨hm, rfl⟩ }
  end

  /-- bounded is preserved by arbitrary finite shifts (although the bound `M` itself might change). -/
  theorem bounded_shift (s : seq) : ∀ n, s.bounded ↔ (s.shift n).bounded :=
  begin
    intro n, split,
    { rintro ⟨M, h⟩,
      use M, intro k,
      exact h (k + n) },
    { rintro ⟨M₁, h₁⟩,
      cases finite_prefix_bounded s n with M₂ h₂,
      use max M₁ M₂,
      intro k,
      by_cases hk : k < n,
      { exact le_max_of_le_right (h₂ k hk) },
      { rw [← shift_ge s (not_lt.mp hk)],
        exact le_max_of_le_left (h₁ (k - n)) } }
  end

  theorem convergent_of_bounded_mono {s : seq} (h₁ : s.bounded) (h₁ : monotone s) : s.convergent :=
  begin
    sorry
  end

  structure subindex :=
    (φ : ℕ → ℕ)
    (mono : strict_mono φ)

  instance subindex_fun : has_coe_to_fun subindex (λ _, ℕ → ℕ) := ⟨subindex.φ⟩

  def subseq (s : seq) (si : subindex) : seq := λ n, s (si n)

  /-- Proposition that a sequence is Cauchy, that is that its terms grow arbitrarily close together. -/
  def seq.cauchy (s : seq) : Prop := ∀ ⦃ε⦄, ε > 0 → ∃ B : ℕ, ∀ ⦃m n⦄, B ≤ m → B ≤ n → |s m - s n| < ε

  /-- Proof that Cauchy sequences are bounded. -/
  theorem cauchy_is_bounded {s : seq} (hc : s.cauchy): s.bounded :=
  begin
    cases hc zero_lt_one with B h,
    have hb : ∀ ⦃n⦄, B ≤ n → |s n| < 1 + |s B|,
      intros n hn,
      have h₁ : |s n| ≤ |s n - s B| + |s B|,
        conv_lhs { rw [←sub_add_cancel (s n) (s B)] },
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
      rw [←add_halves ε],
      refine lt_of_le_of_lt _ (add_lt_add (h hm) (h hn)),
      have : |s m - s n| = |(s m - x) + (x - s n)|, by ring_nf,
      rw [this, ←abs_neg (s n - x), neg_sub],
      exact abs_add (s m - x) (x - s n) },
    { intros hc,
      simp only [seq.convergent],
      simp only [seq.cauchy] at hc,
      sorry }
  end

  theorem bolzano_weierstrass (s : seq) (h : s.bounded) : ∃ si : subindex, (subseq s si).convergent  :=
  begin
    sorry
  end

end my_analysis
