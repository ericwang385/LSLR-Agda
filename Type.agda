{-# OPTIONS --allow-unsolved-metas #-}
module Type where

open import Function hiding (_∋_)
open import Relation.Binary.PropositionalEquality
  using (subst; _≡_; refl; cong; cong₂; trans; sym)

-- Kind Definition
data Kind : Set where
    * : Kind                    -- Type
    _⇒_ : Kind → Kind → Kind    -- Function Kind

data Ct (A : Set) : Set where
    Z : Ct A
    S : Ct A → A → Ct A

-- Kind Context
infixl 5 _,ᵏ_
data Ctxᵏ : Set where
    ∅ : Ctxᵏ
    _,ᵏ_ : Ctxᵏ → Kind → Ctxᵏ

variable
    K J : Kind
    𝒦 𝒦₁ 𝒦₂ 𝒦₃ : Ctxᵏ

infix  4 _∋ᵏ_
data _∋ᵏ_ : Ctxᵏ → Kind → Set where
    Z : ∀ {𝒦 J} → 𝒦 ,ᵏ J ∋ᵏ J
    S : ∀ {𝒦 J K} → 𝒦 ∋ᵏ J → 𝒦 ,ᵏ K ∋ᵏ J

infixr 7 _⇒_
infix 6 _·_
infix 6 Π
infix 6 Σ
infix 4 _⊢ᵏ_
data _⊢ᵏ_ 𝒦 : Kind → Set where
    ` : 𝒦 ∋ᵏ J → 𝒦 ⊢ᵏ J             -- Type Variable
    Unit : 𝒦 ⊢ᵏ *                    -- Unit Type
    Int : 𝒦 ⊢ᵏ *                     
    Bool : 𝒦 ⊢ᵏ *
    ƛ : 𝒦 ,ᵏ J ⊢ᵏ K → 𝒦 ⊢ᵏ J ⇒ K
    _×_ : 𝒦 ⊢ᵏ * → 𝒦 ⊢ᵏ * → 𝒦 ⊢ᵏ *  -- Product Type
    _+_ : 𝒦 ⊢ᵏ * → 𝒦 ⊢ᵏ * → 𝒦 ⊢ᵏ *  -- Sum Type
    _⇒_ : 𝒦 ⊢ᵏ * → 𝒦 ⊢ᵏ * → 𝒦 ⊢ᵏ *  -- Function Type
    _·_ : 𝒦 ⊢ᵏ J ⇒ K → 𝒦 ⊢ᵏ J → 𝒦 ⊢ᵏ K
    Π : 𝒦 ,ᵏ J ⊢ᵏ * → 𝒦 ⊢ᵏ *        -- Forall Type
    Σ : 𝒦 ,ᵏ J ⊢ᵏ * → 𝒦 ⊢ᵏ *        -- Exist Type
    μ : 𝒦 ,ᵏ * ⊢ᵏ * → 𝒦 ⊢ᵏ *        -- Recursive Type
    
variable
    A B : 𝒦 ⊢ᵏ *

Renᵏ : Ctxᵏ → Ctxᵏ → Set
Renᵏ 𝒦₁ 𝒦₂ = ∀{J} → 𝒦₁ ∋ᵏ J → 𝒦₂ ∋ᵏ J

liftᵏ : Renᵏ 𝒦₁ 𝒦₂ → Renᵏ (𝒦₁ ,ᵏ J) (𝒦₂ ,ᵏ J)
liftᵏ ρ Z = Z
liftᵏ ρ (S α) = S (ρ α)

liftᵏ-comp : {ρ : Renᵏ 𝒦₁ 𝒦₂} {ρ' : Renᵏ 𝒦₂ 𝒦₃} (α : 𝒦₁ ,ᵏ K ∋ᵏ J) → liftᵏ (ρ' ∘ ρ) α ≡ liftᵏ ρ' (liftᵏ ρ α)
liftᵏ-comp Z = refl
liftᵏ-comp (S ρ) = refl

liftᵏ-cong : {ρ ρ' : Renᵏ 𝒦₁ 𝒦₂} → (∀ {J} (α : 𝒦₁ ∋ᵏ J) → ρ α ≡ ρ' α) → ∀{J K} (α : 𝒦₁ ,ᵏ J ∋ᵏ K) → liftᵏ ρ α ≡ liftᵏ ρ' α
liftᵏ-cong f Z = refl
liftᵏ-cong f (S x) = cong S (f x)

renᵏ : Renᵏ 𝒦₁ 𝒦₂ → 𝒦₁ ⊢ᵏ J → 𝒦₂ ⊢ᵏ J
renᵏ ρ (` α) = ` (ρ α)
renᵏ ρ Unit = Unit
renᵏ ρ Int = Int
renᵏ ρ Bool = Bool
renᵏ ρ (ƛ A)  = ƛ (renᵏ (liftᵏ ρ) A)
renᵏ ρ (A × B) = renᵏ ρ A × renᵏ ρ B
renᵏ ρ (A + B) = renᵏ ρ A + renᵏ ρ B
renᵏ ρ (A ⇒ B) = renᵏ ρ A ⇒ renᵏ ρ B
renᵏ ρ (A · B) = renᵏ ρ A · renᵏ ρ B
renᵏ ρ (Π A) = Π (renᵏ (liftᵏ ρ) A)
renᵏ ρ (Σ A) = Σ (renᵏ (liftᵏ ρ) A)
renᵏ ρ (μ A) = μ (renᵏ (liftᵏ ρ) A)

renᵏ-cong : {ρ ρ' : Renᵏ 𝒦₁ 𝒦₂} → (∀ {J} (α : 𝒦₁ ∋ᵏ J) → ρ α ≡ ρ' α) → ∀{K} (A : 𝒦₁ ⊢ᵏ K) → renᵏ ρ A ≡ renᵏ ρ' A
renᵏ-cong f (` x) = cong ` (f x)
renᵏ-cong f Unit = refl
renᵏ-cong f Int = refl
renᵏ-cong f Bool = refl
renᵏ-cong f (ƛ A) = cong ƛ (renᵏ-cong (liftᵏ-cong f) A)
renᵏ-cong f (A × B) = cong₂ _×_ (renᵏ-cong f A) (renᵏ-cong f B)
renᵏ-cong f (A + B) = cong₂ _+_ (renᵏ-cong f A) (renᵏ-cong f B)
renᵏ-cong f (A ⇒ B) = cong₂ _⇒_ (renᵏ-cong f A) (renᵏ-cong f B)
renᵏ-cong f (A · B) = cong₂ _·_ (renᵏ-cong f A) (renᵏ-cong f B)
renᵏ-cong f (Π A) = cong Π (renᵏ-cong (liftᵏ-cong f) A)
renᵏ-cong f (Σ A) = cong Σ (renᵏ-cong (liftᵏ-cong f) A)
renᵏ-cong f (μ A) = cong μ (renᵏ-cong (liftᵏ-cong f) A)

renᵏ-comp : {ρ : Renᵏ 𝒦₁ 𝒦₂} {ρ' : Renᵏ 𝒦₂ 𝒦₃} (A : 𝒦₁ ⊢ᵏ J) → renᵏ (ρ' ∘ ρ) A ≡ renᵏ ρ' (renᵏ ρ A) 
renᵏ-comp (` x) = refl
renᵏ-comp Unit = refl
renᵏ-comp Int = refl
renᵏ-comp Bool = refl
renᵏ-comp (ƛ A) = cong ƛ ((trans (renᵏ-cong liftᵏ-comp A) (renᵏ-comp A)))
renᵏ-comp (A × B) = cong₂ _×_ (renᵏ-comp A) (renᵏ-comp B)
renᵏ-comp (A + B) = cong₂ _+_ (renᵏ-comp A) (renᵏ-comp B)
renᵏ-comp (A ⇒ B) = cong₂ _⇒_ (renᵏ-comp A) (renᵏ-comp B)
renᵏ-comp (A · B) = cong₂ _·_ (renᵏ-comp A) (renᵏ-comp B)
renᵏ-comp (Π A) = cong Π (trans (renᵏ-cong liftᵏ-comp A) (renᵏ-comp A))
renᵏ-comp (Σ A) = cong Σ (trans (renᵏ-cong liftᵏ-comp A) (renᵏ-comp A))
renᵏ-comp (μ A) = cong μ (trans (renᵏ-cong liftᵏ-comp A) (renᵏ-comp A))

weakenᵏ : ∀{K} → 𝒦 ⊢ᵏ J → 𝒦 ,ᵏ K ⊢ᵏ J
weakenᵏ = renᵏ S

Subᵏ : Ctxᵏ → Ctxᵏ → Set
Subᵏ 𝒦₁ 𝒦₂ = ∀ {J} → 𝒦₁ ∋ᵏ J → 𝒦₂ ⊢ᵏ J

liftsᵏ : Subᵏ 𝒦₁ 𝒦₂ → Subᵏ (𝒦₁ ,ᵏ J) (𝒦₂ ,ᵏ J)
liftsᵏ ρ Z = ` Z
liftsᵏ ρ (S α) = weakenᵏ (ρ α)

subᵏ : Subᵏ 𝒦₁ 𝒦₂ → 𝒦₁ ⊢ᵏ J → 𝒦₂ ⊢ᵏ J
subᵏ ρ (` α) = ρ α
subᵏ ρ Unit = Unit
subᵏ ρ Int = Int
subᵏ ρ Bool = Bool
subᵏ ρ (ƛ A) = ƛ (subᵏ (liftsᵏ ρ) A)
subᵏ ρ (A × B) = subᵏ ρ A × subᵏ ρ B
subᵏ ρ (A + B) = subᵏ ρ A + subᵏ ρ B
subᵏ ρ (A ⇒ B) = subᵏ ρ A ⇒ subᵏ ρ B
subᵏ ρ (A · B) = subᵏ ρ A · subᵏ ρ B
subᵏ ρ (Π A) = Π (subᵏ (liftsᵏ ρ) A)
subᵏ ρ (Σ A) = Σ (subᵏ (liftsᵏ ρ) A)
subᵏ ρ (μ A) = μ (subᵏ (liftsᵏ ρ) A)

extendᵏ : Subᵏ 𝒦₁ 𝒦₂ → 𝒦₂ ⊢ᵏ J → Subᵏ (𝒦₁ ,ᵏ J) 𝒦₂
extendᵏ ρ A Z = A
extendᵏ ρ A (S α) = ρ α

_[_]ᵏ : 𝒦 ,ᵏ K ⊢ᵏ J → 𝒦 ⊢ᵏ K → 𝒦 ⊢ᵏ J
B [ A ]ᵏ = subᵏ (extendᵏ ` A) B

ren[]ᵏ : (ρ : Renᵏ 𝒦₁ 𝒦₂) (A : 𝒦₁ ,ᵏ K ⊢ᵏ J) (B : 𝒦₁ ⊢ᵏ K) → renᵏ ρ (A [ B ]ᵏ) ≡ renᵏ (liftᵏ ρ) A [ renᵏ ρ B ]ᵏ
ren[]ᵏ ρ A B = trans {!   !} {!   !}

-- subᵏ-comp : {ρ : Subᵏ 𝒦₁ 𝒦₂}{ρ' : Subᵏ 𝒦₂ 𝒦₃} (A : 𝒦₁ ⊢ᵏ J) → subᵏ (subᵏ ρ' ∘ ρ) A ≡ subᵏ ρ' (subᵏ ρ A)
-- subᵏ-comp = {!   !}