module plfa.part1.SkewBinary where

open import Data.Nat using (ℕ; zero; suc; _<_; _<?_; _≟_; _+_; _*_; _≤_; s≤s; z≤n; _^_; ⌊_/2⌋; _∸_)
open import Data.Nat.Properties using (<-cmp; n≤1+n; ≤-trans; +-comm; +-assoc)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
open import Relation.Binary using (tri<; tri>; tri≈)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym)

x : Dec (2 ≡ 3)
x = 2 ≟ 3

-- Helpers

minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m       zero    _         = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m

-- Datatypes

-- l -> 2 = 2^(0+1) -1
-- n l l -> 3 = 2^(1+1) - 1
-- n (n l l) (n l l) -> 7 = 2^(2+1) - 1

-- (2^n - 1) + (2^n - 1) + 1
-- = 2*2^n - 2 + 1
-- 2^(n+1) + 1

data Tree (A : Set) : ℕ → Set where
  leaf : A → Tree A 1
  node : ∀ {s : ℕ} → A → Tree A s → Tree A s → Tree A (1 + 2 * s)

-- data TreeElem {A : Set} (target : A) : {s : ℕ} → Tree s A → Set where
--   here-leaf : TreeElem target (leaf target)
--   here-node : ∀ {s : ℕ} (tₗ : Tree s A) (tᵣ : Tree s A) → TreeElem target (node target tₗ tᵣ)
--   thereₗ-node : ∀ {s : ℕ} (a : A) (tₗ : Tree s A) (tᵣ : Tree s A) (prf : TreeElem a tₗ) → TreeElem target (node a tₗ tᵣ)
--   thereᵣ-node : ∀ {s : ℕ} (a : A) (tₗ : Tree s A) (tᵣ : Tree s A) (prf : TreeElem a tᵣ) → TreeElem target (node a tₗ tᵣ)

indexTree : ∀ {A : Set} {s : ℕ} → Tree A s → Fin s → A
indexTree (leaf a) zero = a
indexTree (node a _ _) zero = a
indexTree (node {s} a tₗ tᵣ) (suc i) rewrite +-comm s zero with Fin.splitAt s i
... | inj₁ i = indexTree tₗ i
... | inj₂ i = indexTree tᵣ i

data SBList (A : Set) : ℕ → Set where
   head : ∀ {#tree : ℕ} {#tail : ℕ} → Tree A #tree → SBList A #tail → SBList A (#tree + #tail)
   nil : SBList A 0

-- weird error if I try to do this inline!
stupid : ∀ {A : Set} {s : ℕ} → Tree A (suc (s + (s + zero))) → Tree A (suc (s + s))
stupid {A} {s} t rewrite +-comm s zero = t

cons : ∀ {A : Set} {s : ℕ} → A → SBList A s → SBList A (suc s)
cons {A} a t@(head {s₁} t₁ (head {s₂} {#tail} t₂ sb)) with s₁ ≟ s₂
... | yes refl rewrite sym (+-assoc s₁ s₁ #tail) =
  let
    tree = node a t₁ t₂
    tree‵ = stupid {A} {s₁} tree
  in head tree‵ sb
... | no _            = head (leaf a) t
cons a t@(head _ nil) = head (leaf a) t
cons a t@nil          = head (leaf a) t

index : ∀ {A : Set} {s : ℕ} → SBList A s → Fin s → A
index (head {s} t sb) i with Fin.splitAt s i
... | inj₁ i = indexTree t i
... | inj₂ i = index sb i
