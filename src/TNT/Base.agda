module TNT.Base where

open import Data.Nat
open import Data.Nat.DivMod
open import Agda.Builtin.Equality
open import Relation.Nullary.Decidable

data _≡_⟨mod_⟩ : ℕ → ℕ → ℕ → Set where
  CM : ∀ {a b n : ℕ} → {≢0 : False (n ≟ 0)} → ((a % n){≢0}) ≡ ((b % n){≢0}) → a ≡ b ⟨mod n ⟩

4≡7mod3 : 4 ≡ 7 ⟨mod 3 ⟩
4≡7mod3 = CM refl

