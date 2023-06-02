module plfa.part1.SkewBinary where

open import Data.Nat using (ℕ; zero; suc; _<_; _<?_; _≟_; _+_; _*_; _≤_; s≤s; z≤n; _^_; ⌊_/2⌋; _∸_)
open import Data.Nat.Properties using (<-cmp; n≤1+n; ≤-trans; +-comm; +-assoc; +-identityʳ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_)
import Data.Fin as Fin
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
open import Relation.Binary using (tri<; tri>; tri≈)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym)

-- Datatypes

-- l -> 2 = 2^(0+1) -1
-- n l l -> 3 = 2^(1+1) - 1
-- n (n l l) (n l l) -> 7 = 2^(2+1) - 1

-- (2^n - 1) + (2^n - 1) + 1
-- = 2*2^n - 2 + 1
-- 2^(n+1) + 1

module Tree where
  -- Binary tree with elements at the nodes and the leaves, indexed
  -- by the size. A tree of depth d has 2^(d+1) - 1 elements, i.e.
  -- exactly the number corresponding to a skew-binary digit in the
  -- d'th place.
  data Tree (A : Set) : ℕ → Set where
    leaf : A → Tree A 1
    node :
      ∀ {#subtree : ℕ} {#tree : ℕ}
      → A
      → Tree A #subtree
      → Tree A #subtree
      -- works better than 1 + 2 * #subtree, since the latter reduces
      -- to 1 + #subtree + (#subtree + 0), which is annoying
      → #tree ≡ 1 + #subtree + #subtree
      → Tree A #tree

  -- data TreeElem {A : Set} (target : A) : {s : ℕ} → Tree s A → Set where
  --   here-leaf : TreeElem target (leaf target)
  --   here-node : ∀ {s : ℕ} (tₗ : Tree s A) (tᵣ : Tree s A) → TreeElem target (node target tₗ tᵣ)
  --   thereₗ-node : ∀ {s : ℕ} (a : A) (tₗ : Tree s A) (tᵣ : Tree s A) (prf : TreeElem a tₗ) → TreeElem target (node a tₗ tᵣ)
  --   thereᵣ-node : ∀ {s : ℕ} (a : A) (tₗ : Tree s A) (tᵣ : Tree s A) (prf : TreeElem a tᵣ) → TreeElem target (node a tₗ tᵣ)

  indexTree : ∀ {A : Set} {s : ℕ} → Tree A s → Fin s → A
  indexTree (leaf a) zero = a
  indexTree (node a _ _ refl) zero = a
  indexTree (node {s} a tₗ tᵣ refl) (suc i) with Fin.splitAt s i
  ... | inj₁ i = indexTree tₗ i
  ... | inj₂ i rewrite +-identityʳ s = indexTree tᵣ i

open Tree

digit-size-at : ℕ → ℕ
digit-size-at place = (2 ^ (place + 1) ∸ 1)

module Original where
  data SBList (A : Set) : ℕ → Set where
    nil : SBList A 0
    consTree :
      ∀ {#tree : ℕ} {#tail : ℕ} {#list : ℕ}
      → Tree A #tree
      → SBList A #tail
      → #list ≡ #tree + #tail
      → SBList A #list

  cons : ∀ {A : Set} {s : ℕ} → A → SBList A s → SBList A (suc s)
  cons {A} a t@(consTree {s₁} t₁ (consTree {s₂} {#tail} t₂ sb refl) refl) with s₁ ≟ s₂
  ... | yes refl rewrite sym (+-assoc s₁ s₁ #tail) =
    consTree (node a t₁ t₂ refl) sb refl
  ... | no _                     = consTree (leaf a) t refl
  cons a t@(consTree _ nil refl) = consTree (leaf a) t refl
  cons a t@nil                   = consTree (leaf a) t refl

  uncons : ∀ {A : Set} {s : ℕ} → SBList A (suc s) → (A × SBList A s)
  uncons (consTree (leaf x) sb refl) = x , sb
  uncons (consTree {_} {#tail} (node {s} x tₗ tᵣ refl) sb refl) rewrite +-identityʳ s =
    x , consTree tₗ (consTree tᵣ sb refl) (+-assoc s s #tail)

  indexList : ∀ {A : Set} {s : ℕ} → SBList A s → Fin s → A
  indexList (consTree {s} t sb refl) i with Fin.splitAt s i
  ... | inj₁ i = indexTree t i
  ... | inj₂ i = indexList sb i

module OneTwo where
  data SBList (A : Set) : ℕ → Set where
    nil : SBList A 0
    one :
      ∀ {#tree : ℕ} {#tail : ℕ} {#list : ℕ}
      → Tree A #tree
      → SBList A #tail
      → #list ≡ #tree + #tail
      → SBList A #list
    two :
      ∀ {#tree : ℕ} {#tail : ℕ} {#list : ℕ}
      → Tree A #tree
      → Tree A #tree
      → SBList A #tail
      → #list ≡ #tree + #tree + #tail
      → SBList A #list

  consTree : ∀ {A : Set} {#tree : ℕ} {#list : ℕ} → Tree A #tree → SBList A #list → SBList A (#tree + #list)
  consTree t l@nil = one t l refl
  consTree {A} {#t} t l@(one {#u} {#tail} u l‵ refl) with #t ≟ #u
  ... | yes refl rewrite sym (+-assoc #t #t #tail) = two t u l‵ refl
  ... | no _ = one t l refl
  consTree {A} {#t} t l@(two {#u} t₁ t₂ l‵ refl) with #t ≟ #u
  ... | yes refl = {!!}
  ... | no _ = {!!}

  cons : ∀ {A : Set} {s : ℕ} → A → SBList A s → SBList A (suc s)
  cons a l@nil = one (leaf a) l refl
  cons a l@(one t l‵ refl) = one (leaf a) l refl
  cons a (two t₁ t₂ l‵ refl) = one (node a t₁ t₂ refl) l‵ refl

module NumeralIncreasingPlace where
  data Digit : Set where
    one : Digit
    two : Digit

  digit-toℕ : Digit → ℕ
  digit-toℕ one = 1
  digit-toℕ two = 2

  data Numeral : Set
  n-place : Numeral → ℕ

  data Numeral where
    ⟨⟩ : ∀ (place : ℕ) → Numeral
    _#_at_since_ : ∀ (n : Numeral) → Digit → (place : ℕ) → (prf : place < n-place n) → Numeral

  infixl 20 _#_at_since_

  n-place (⟨⟩ place) = place
  n-place (_ # _ at place since _) = place

  ≤-<-≡ : ∀ {a b : ℕ} → a ≤ b → a ≡ b ⊎ a < b
  ≤-<-≡ {zero} {zero} z≤n = inj₁ refl
  ≤-<-≡ {zero} {suc b} z≤n = inj₂ (s≤s z≤n)
  ≤-<-≡ (s≤s prf) with ≤-<-≡ prf
  ... | inj₁ refl = inj₁ refl
  ... | inj₂ y = inj₂ (s≤s y)

  incr : Numeral → Numeral
  incr n@(⟨⟩ _) = ⟨⟩ 1 # one at 0 since s≤s z≤n
  incr (n # one at place since prf) = n # two at place since prf
  incr (n # two at place since prf) with n-place n
  incr (n # two at place since s≤s prf) | suc p with ≤-<-≡ prf
  ... | inj₁ x = incr n
  -- suc place < n-place n
  -- suc (suc place) <= n-place n
  -- suc (suc place) <= suc p
  -- suc place <= p
  ... | inj₂ prf2 = n # one at (suc place) since {!!}

  _ : Numeral
  _ = ⟨⟩ 6

  _ : Numeral
  _ = ⟨⟩ 6 # one at 4 since s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

  -- _ : Numeral 1
  -- _ = ⟨⟩ 6 # one at 4 since s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))) # two at 1 since s≤s (s≤s z≤n)

  -- -- _ : Numeral 1
  -- -- _ = (⟨⟩ {6} one 5) two 3 two 1

  n-toℕ : Numeral → ℕ
  n-toℕ (⟨⟩ _) = 0
  n-toℕ (n # d at place since prf) = (n-toℕ n) + digit-toℕ d * digit-size-at place

  -- _ : n-toℕ (⟨⟩ 6) ≡ 0
  -- _ = refl

  -- _ : n-toℕ (⟨⟩ 6 # one at 0 since s≤s z≤n) ≡ 1
  -- _ = refl

  -- _ : n-toℕ (⟨⟩ 5 # one at 1 since s≤s (s≤s z≤n)) ≡ 3
  -- _ = refl

  _ : n-toℕ (⟨⟩ 4 # one at 2 since s≤s (s≤s (s≤s z≤n))) ≡ 7
  _ = refl

  -- _ : n-toℕ (⟨⟩ 3 # one at 2 since s≤s (s≤s (s≤s z≤n)) # one at 0 since s≤s z≤n) ≡ 8
  -- _ = refl

  data SBList (A : Set) : Numeral → Set where
    nil : ∀ (place : ℕ) → SBList A (⟨⟩ place)
    one :
      ∀ {#tree : ℕ} {#tail : Numeral} {place : ℕ}
      → (prf : place < n-place #tail)
      → Tree A (digit-size-at place)
      → SBList A #tail
      → SBList A (#tail # one at place since prf)
    two :
      ∀ {#tree : ℕ} {#tail : Numeral} {place : ℕ}
      → (prf : place < n-place #tail)
      → Tree A (digit-size-at place)
      → Tree A (digit-size-at place)
      → SBList A #tail
      → SBList A (#tail # one at place since prf)

module NumeralTrailingZeros where
  data Digit : Set where
    zero : Digit
    one : Digit
    two : Digit

  data Numeral : Set where
    ⟨⟩ : Numeral
    _#_ : Numeral → Digit → Numeral

  record Numeral0 : Set where
    constructor _#0_
    field
      n : Numeral
      zeros : ℕ

  infixl 20 _#_
  infix 19 _#0_

  _ : Numeral0
  _ = ⟨⟩ # one # two # one #0 3

  padZeros : Numeral → ℕ → Numeral
  padZeros n zero = n
  padZeros n (suc num) = padZeros (n # zero) num

  reifyZeros : Numeral0 → Numeral
  reifyZeros (x #0 zs) = padZeros x zs

  inc : Numeral → Numeral
  inc ⟨⟩ = ⟨⟩ # one
  inc (nt # zero) = nt # one
  inc (nt # one) = nt # two
  inc (nt # two) = inc nt # zero

  inc0 : Numeral0 → Numeral0
  inc0 n = inc (reifyZeros n) #0 0

  d-toℕ : Digit → ℕ
  d-toℕ zero = 0
  d-toℕ one = 1
  d-toℕ two = 2

  n-toℕ : Numeral → ℕ
  n-toℕ ⟨⟩ = 0
  n-toℕ (n # d) = n-toℕ n + d-toℕ d

  n0-toℕ : Numeral0 → ℕ
  n0-toℕ n = n-toℕ (reifyZeros n)

  data SBList (A : Set) : Numeral0 → Set where
    nil : (n : ℕ) → SBList A (⟨⟩ #0 n)
    one :
      ∀ {#tail : Numeral} {#tail0 : Numeral0} {#list0 : Numeral0} {m : ℕ} {n : ℕ}
      → Tree A (digit-size-at n)
      → SBList A #tail0
      → #tail0 ≡ #tail #0 (1 + m + n)
      → #list0 ≡ (padZeros #tail m) # zero #0 n
      → SBList A #list0
    two :
      ∀ {#tail : Numeral} {#tail0 : Numeral0} {#list0 : Numeral0} {m : ℕ} {n : ℕ}
      → Tree A (digit-size-at n)
      → Tree A (digit-size-at n)
      → SBList A #tail0
      → #tail0 ≡ #tail #0 (1 + m + n)
      → #list0 ≡ (padZeros #tail m) # zero #0 n
      → SBList A #list0

  cons : ∀ {A : Set} {n : Numeral0} → A → SBList A n → SBList A (inc0 n)
  cons a t = {!!}
