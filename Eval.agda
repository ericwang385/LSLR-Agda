module Eval where

open import Type
open import Term

open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using () renaming (Bool to 𝔹)

data Val : Γ ⊢ A → Set where
    ` : ∀ {x : Γ ∋ A} → Val (` x)
    ⟨⟩ : ∀ {x : Γ ⊢ Unit} → Val x
    ± : (x : Γ ⊢ Int) → Val x
    bool : (x : Γ ⊢ Bool) → Val x
    pair : Val e₁ → Val e₂ → Val (⟨ e₁ , e₂ ⟩)
    lam : Val (ƛ e)
    tlam : Val (Λ e)
    pack : (α : 𝒦 ⊢ᵏ J) → (x : Γ ⊢ (A [ α ]ᵏ)) → (t : Γ ,ᵏ J ⊢ A) → Val x → Val (pack α , x as t)
    roll : ∀ A → (x : Γ ⊢ A [ μ A ]ᵏ) → Val x → Val (roll A x)

infix 5 _⟶_
data _⟶_ : Γ ⊢ A → Γ ⊢ A → Set where
    if-true : if true then e₁ else e₂ ⟶ e₁  
    if-false : if false then e₁ else e₂ ⟶ e₂
    pair-fst : Val e₁ → Val e₂ → fst ⟨ e₁ , e₂ ⟩ ⟶ e₁
    pair-snd : Val e₁ → Val e₂ → fst ⟨ e₁ , e₂ ⟩ ⟶ e₂
    lam : {e₁ : Γ , A ⊢ B} {e₂ : Γ ⊢ A} → Val e₂ → (ƛ e₁) · e₂ ⟶ (e₁ [ e₂ ])
    lamt : {e : Γ ,ᵏ J ⊢ B} {A : 𝒦 ⊢ᵏ J} → Λ e ·ᵏ A ⟶ e ᵏ[ A ]
    unpack : {α : 𝒦 ⊢ᵏ J} {e₁ : Γ ⊢ (A [ α ]ᵏ)} {R : Γ ,ᵏ J ⊢ A} → Val e₁ → unpack_as_,_of_ (pack α , e₁ as R) α R ⟶ e₁
    unroll : {e : Γ ⊢ A [ μ A ]ᵏ} → Val e → unroll (roll A e) ⟶ e  