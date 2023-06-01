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

-- Binary tree with elements at the nodes and the leaves, indexed
-- by the size. A tree of depth d has 2^(d+1) - 1 elements, i.e.
-- exactly the number corresponding to a skew-binary digit in the
-- d'th place.
data Tree (A : Set) : ℕ → Set where
  leaf : A → Tree A 1
  node :
    ∀ {#subtree : ℕ} {#tree : ℕ}
    → #tree ≡ 1 + 2 * #subtree
    → A
    → Tree A #subtree
    → Tree A #subtree
    → Tree A #tree

-- data TreeElem {A : Set} (target : A) : {s : ℕ} → Tree s A → Set where
--   here-leaf : TreeElem target (leaf target)
--   here-node : ∀ {s : ℕ} (tₗ : Tree s A) (tᵣ : Tree s A) → TreeElem target (node target tₗ tᵣ)
--   thereₗ-node : ∀ {s : ℕ} (a : A) (tₗ : Tree s A) (tᵣ : Tree s A) (prf : TreeElem a tₗ) → TreeElem target (node a tₗ tᵣ)
--   thereᵣ-node : ∀ {s : ℕ} (a : A) (tₗ : Tree s A) (tᵣ : Tree s A) (prf : TreeElem a tᵣ) → TreeElem target (node a tₗ tᵣ)

indexTree : ∀ {A : Set} {s : ℕ} → Tree A s → Fin s → A
indexTree (leaf a) zero = a
indexTree (node refl a _ _) zero = a
indexTree (node {s} refl a tₗ tᵣ) (suc i) with Fin.splitAt s i
... | inj₁ i = indexTree tₗ i
... | inj₂ i rewrite +-identityʳ s = indexTree tᵣ i

data SBList (A : Set) : ℕ → Set where
  head :
    ∀ {#tree : ℕ} {#tail : ℕ} {#list : ℕ}
    → #list ≡ #tree + #tail
    → Tree A #tree
    → SBList A #tail
    → SBList A #list
  nil : SBList A 0

-- weird error if I try to do this inline!
stupid : ∀ {A : Set} {s : ℕ} → Tree A (suc (s + (s + zero))) → Tree A (suc (s + s))
stupid {A} {s} t rewrite +-identityʳ s = t

cons : ∀ {A : Set} {s : ℕ} → A → SBList A s → SBList A (suc s)
cons {A} a t@(head {s₁} refl t₁ (head {s₂} {#tail} refl t₂ sb)) with s₁ ≟ s₂
... | yes refl rewrite sym (+-assoc s₁ s₁ #tail) | +-identityʳ s₁ =
  let
    tree = node {A} {s₁} refl a t₁ t₂
    tree‵ = stupid {A} {s₁} tree
    newl = head refl tree‵ sb
  in newl
... | no _                 = head refl (leaf a) t
cons a t@(head refl _ nil) = head refl (leaf a) t
cons a t@nil               = head refl (leaf a) t

uncons : ∀ {A : Set} {s : ℕ} → SBList A (suc s) → (A × SBList A s)
uncons (head refl (leaf x) sb) = x , sb
uncons (head {_} {#tail} refl (node {s} refl x tₗ tᵣ) sb) rewrite +-identityʳ s =
  x , head (+-assoc s s #tail) tₗ (head refl tᵣ sb)

indexList : ∀ {A : Set} {s : ℕ} → SBList A s → Fin s → A
indexList (head {s} refl t sb) i with Fin.splitAt s i
... | inj₁ i = indexTree t i
... | inj₂ i = indexList sb i

