# Equational reasoning skeleton

When starting to do equational reasoning, you can start like this:
```agda
begin
    ?
  ≡⟨ ? ⟩
    ?
  ≡⟨ ? ⟩
    ?
  ≡⟨ ? ⟩
    ?
∎
```

This sets up a series of reasoning steps with holes for the expressions and the steps. 
Since the reasoning steps are holes, agda will always accept this, so you can make incremental progress while keeping your file compiling.

Now call "solve".
This will solve the term holes at the beginning and the end so you don't have to fill them in.
You can do this whenever the next step is fixed enough, so if you fill in the reasoning you want to do for a step, you can use "solve" and agda will fill in the next term.

# Goal information will show computed terms

Suppose you have a partial equational reasoning proof:
```agda
begin
    2 + (x + y)
  ≡⟨ ?2 ⟩
    ?
  ≡⟨ ? ⟩
    ?
  ≡⟨ ? ⟩
    ?
∎
```

The first term can be computed more.
To see this, you can ask for the goal context for `?2` and it will show something like this:
```
?2 = suc (suc (x + y)) = y_5244
```
i.e. your LHS and an unknown RHS (because it's a hole), but it will show the LHS fully computed, which you can copy into your file directly.

# Try and make your definitions compute as much as possible

For example, compare:
```agda
2 * foo b
```
vs
```agda
foo b * 2 
```

Because the definition of `*` analyzes its first argument, the first version can be computed by agda, since the first argument to `*` is a constructor.
However, in the second agda cannot compute the term further (unless it can do something with `foo b`).

Doing this lets agda do more definitional simplification, which means you have to do less work.

# The three (?) styles of proof all tend to use the same assumptions

Consider these three proofs of the same theorem:
```agda
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
  ≡⟨⟩
    (suc m * p) + n * p
  ∎

*-distrib-+‵ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+‵ zero n p = refl
*-distrib-+‵ (suc m) n p = Eq.trans ( cong (p +_) (*-distrib-+‵ m n p)) ( sym ( +-assoc p (m * p) (n * p)))

*-distrib-+‶ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+‶ zero n p = refl
*-distrib-+‶ (suc m) n p rewrite +-assoc p (m * p) (n * p) | *-distrib-+‶ m n p = refl
```

The use three approaches for doing "multiple steps":
- Equational reasoning
- `trans`
- `rewrite`

However, notably they all use the same steps!
That means you can write the proof however you find easiest and then relatively easily rewrite it into another form if you want.
For example, do the proof slowly with equational reasoning, and then turn it into a compact proof with `rewrite`.

# Avoid mutual recursion in proofs by recursing outside the lemma

Look at the second part of the proof of commutativity of `+`:
```agda
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎
```
We use two equalities: the `+-suc` lemma, and a recursive use of `+-comm`.

If you were doing this for the first time, you might be tempted to make _one_ lemma for both those steps.
It wouldn't look that different, it would just have `n` and `m` swapped.
But then you would find that you needed to call `+-comm` from the lemma, which needs mutual recursion.

Instead, you can do what's done here and use the recursive call before/after your lemma.

# When to use implicit parameters

Roughly: if it can be inferred easily from the result, e.g.
```
≤-refl : ∀ { n : ℕ } → n ≤ n
```
Agda will be able to infer the `n` from the `n ≤ n` in the result.

Note that it would have trouble if `≤` was a function: it can't generally infer `f` and `x` from `f x`.
