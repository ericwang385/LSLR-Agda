{-# OPTIONS --cumulativity #-}
module Relation {𝓁} where

open import Type
open import Term
open import Eval
open import Relation.Binary using (Rel)
open import Level renaming (zero to lzero)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym)

-- 𝓔⟦_⟧_ : ∀{𝒦} → (A : 𝒦 ⊢ᵏ *) → (𝒦 ∋ᵏ * → Rel (𝒦 ⊢ᵏ *) 𝓁)  → Set 𝓁
-- 𝓔⟦_⟧_ {𝒦} (` α) ρ = (x y : 𝒦 ⊢ᵏ *) → (ρ α) x y
-- 𝓔⟦ Unit ⟧ ρ = {!   !}
-- 𝓔⟦ Int ⟧ ρ = {!   !}
-- 𝓔⟦ Bool ⟧ ρ = {!   !}
-- 𝓔⟦ A × A₁ ⟧ ρ = {!   !}
-- 𝓔⟦ A + A₁ ⟧ ρ = {!   !}
-- 𝓔⟦ A ⇒ A₁ ⟧ ρ = {!   !}
-- 𝓔⟦ A · A₁ ⟧ ρ = {!   !}
-- 𝓔⟦ Π A ⟧ ρ = {!   !}
-- 𝓔⟦ Σ A ⟧ ρ = {!   !}
-- 𝓔⟦ μ A ⟧ ρ = {!   !}

_[_]_~_ : (𝒦 ∋ᵏ * → Rel (𝒦 ⊢ᵏ *) 𝓁) → (A : 𝒦 ⊢ᵏ *) → {e : Γ ⊢ A} → Rel (Val e) 𝓁
ρ [ ` α ] x ~ y = {! ρ α  !}
ρ [ Unit ] x ~ y = x ≡ y
ρ [ Int ] x ~ y = x ≡ y
ρ [ Bool ] x ~ y = x ≡ y
ρ [ A × A₁ ] x ~ y = {!   !}
ρ [ A + A₁ ] x ~ y = {!   !}
ρ [ A ⇒ A₁ ] x ~ y = {!   !}
ρ [ A · A₁ ] x ~ y = {!   !}
ρ [ Π A ] x ~ y = {!   !}
ρ [ Σ A ] x ~ y = {!   !}
ρ [ μ A ] x ~ y = {!   !}
