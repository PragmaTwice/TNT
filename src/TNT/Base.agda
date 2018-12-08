{-# OPTIONS --without-K #-}

module TNT.Base where

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
open import Agda.Builtin.Equality
open import Relation.Nullary.Decidable
open import Data.Empty

-- defination of congruence modulo

_≡_⟨mod_⟩ : ℕ → ℕ → (n : ℕ) → {≢0 : False (n ≟ 0)} → Set
(a ≡ b ⟨mod n ⟩){≢0} = (a % n){≢0} ≡ (b % n){≢0}

-- commutative

≡-comm : ∀ {ℓ} {A : Set ℓ} {a b : A} → a ≡ b → b ≡ a
≡-comm refl = refl

≡-mod-comm : ∀ {a b n : ℕ} → {≢0 : False (n ≟ 0)} → (a ≡ b ⟨mod n ⟩){≢0} → (b ≡ a ⟨mod n ⟩){≢0}
≡-mod-comm refl? = ≡-comm refl?

-- divisibility

≡-mod-div : ∀ {a b n : ℕ} → {≢0 : False (n ≟ 0)} → a ≥ b → (a ≡ b ⟨mod n ⟩){≢0} → n ∣ a ∸ b
≡-mod-div _ ()

-- transitivity

≡-trans : ∀ {ℓ} {A : Set ℓ} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
≡-trans refl refl = refl

≡-mod-trans : ∀ {a b c n : ℕ} → {≢0 : False (n ≟ 0)} → (a ≡ b ⟨mod n ⟩){≢0} → (b ≡ c ⟨mod n ⟩){≢0} → (a ≡ c ⟨mod n ⟩){≢0}
≡-mod-trans refl₁ refl₂ = ≡-trans refl₁ refl₂

