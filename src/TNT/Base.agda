{-# OPTIONS --without-K #-}

module TNT.Base where

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Agda.Builtin.Equality
open import Relation.Nullary.Decidable
open import Data.Empty

-- defination of congruence modulo

_≡_⟨mod_⟩ : ℕ → ℕ → (n : ℕ) → {≢0 : False (n ≟ 0)} → Set
(a ≡ b ⟨mod 0 ⟩){}
a ≡ b ⟨mod suc n ⟩ = a % suc n ≡ b % suc n

-- commutative

≡-comm : ∀ {ℓ} {A : Set ℓ} {a b : A} → a ≡ b → b ≡ a
≡-comm refl = refl

≡-mod-comm : ∀ {a b n : ℕ} → a ≡ b ⟨mod suc n ⟩ → b ≡ a ⟨mod suc n ⟩
≡-mod-comm refl₁ = ≡-comm refl₁

-- divisibility

a≡b⟨modn⟩⇒a%n-b%n≡0 : ∀ {a b n : ℕ} → a ≡ b ⟨mod suc n ⟩ → ∣ a % suc n - b % suc n ∣ ≡ 0
a≡b⟨modn⟩⇒a%n-b%n≡0 refl₁ = n≡m⇒∣n-m∣≡0 refl₁

a%n-b%n≡0⇒⟨a-b⟩%n≡0 : ∀ {a b n : ℕ} → ∣ a % suc n - b % suc n ∣ ≡ 0 → ∣ a - b ∣ % suc n ≡ 0
a%n-b%n≡0⇒⟨a-b⟩%n≡0 = {!!}

≡-mod-div : ∀ {a b n : ℕ} → a ≡ b ⟨mod suc n ⟩ → suc n ∣ ∣ a - b ∣
≡-mod-div {a} {b} {n} refl₁ = m%n≡0⇒n∣m ∣ a - b ∣ n (a%n-b%n≡0⇒⟨a-b⟩%n≡0 {a} {b} {n} (a≡b⟨modn⟩⇒a%n-b%n≡0 {a} {b} {n} refl₁))

-- transitivity

≡-trans : ∀ {ℓ} {A : Set ℓ} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
≡-trans refl refl = refl

≡-mod-trans : ∀ {a b c n : ℕ} → a ≡ b ⟨mod suc n ⟩ → b ≡ c ⟨mod suc n ⟩ → a ≡ c ⟨mod suc n ⟩
≡-mod-trans refl₁ refl₂ = ≡-trans refl₁ refl₂

