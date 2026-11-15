{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module HoTT-UF-Agda where

open import Universes public

variable
 𝓤 𝓥 𝓦 𝓣 : Universe

data 𝟙 : 𝓤₀ ̇  where
  * : 𝟙

𝟙-induction : (A : 𝟙 → 𝓤 ̇ ) → A * → (x : 𝟙) → A x
𝟙-induction p pa * = pa

𝟙-recursion : (B : 𝓤 ̇ ) → B → 𝟙 → B
𝟙-recursion p b * = b

!𝟙' : (X : 𝓤 ̇ ) → X → 𝟙
!𝟙' X x = *

!𝟙 : {X : 𝓤 ̇ } → X → 𝟙
!𝟙 x = *

data 𝟘 : 𝓤₀ ̇  where

𝟘-induction : (A : 𝟘 → 𝓤 ̇ ) → (x : 𝟘) → A x
𝟘-induction p ()

𝟘-recursion : (A : 𝓤 ̇ ) → 𝟘 → A
𝟘-recursion p ()

!𝟘 : (A : 𝓤 ̇ ) → 𝟘 → A
!𝟘 = 𝟘-recursion

is-empty : 𝓤 ̇  → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇  → 𝓤 ̇
¬ X = X → 𝟘

randomtheorem : (P Q : 𝓤 ̇ ) → P → (P → 𝟘) → Q
randomtheorem P Q p np =
  𝟘-induction (λ (x : 𝟘) → Q) (np p)

data ℕ : 𝓤₀ ̇  where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-induction' : (A : ℕ → 𝓤 ̇ )
            → A zero
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n
ℕ-induction' p pZ pS zero = pZ
ℕ-induction' p pZ pS (succ n) =
  pS n (ℕ-induction' p pZ pS n)

ℕ-induction : (A : ℕ → 𝓤 ̇ )
            → A zero
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n
ℕ-induction p pZ pS = h
  where h : (n : ℕ) → p n
        h zero = pZ
        h (succ n) = pS n (h n)

ℕ-recursion : (X : 𝓤 ̇ )
             → X
             → (ℕ → X → X)
             → ℕ → X
ℕ-recursion p = ℕ-induction (λ _ → p)

ℕ-iteration : (X : 𝓤 ̇ )
              → X
              → (X → X)
              → ℕ → X
ℕ-iteration p pZ pS = ℕ-recursion p pZ (λ _ → pS)


module Arithmetic where

  _+_  _×_ : ℕ → ℕ → ℕ

  x + 0      = x
  x + succ y = succ (x + y)

  x × 0      = 0
  x × succ y = x + x × y

  infixl 20 _+_
  infixl 21 _×_


module Arithmetic' where

  _+_  _×_ : ℕ → ℕ → ℕ

  x + y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ x succ

  x × y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ 0 (x +_)

  infixl 20 _+_
  infixl 21 _×_


module ℕ-order where

  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
  0      ≤ y      = 𝟙
  succ x ≤ 0      = 𝟘
  succ x ≤ succ y = x ≤ y

  x ≥ y = y ≤ x

  infix 10 _≤_
  infix 10 _≥_

module ℕ-order' where

  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
  _≤_ = ℕ-iteration (ℕ → 𝓤₀ ̇ ) (λ y → 𝟙)
          (λ h₁ → ℕ-recursion (𝓤₀ ̇ ) 𝟘
                    (λ y h₂ → h₁ y))

  x ≥ y = y ≤ x

  infix 10 _≤_
  infix 10 _≥_

data _+_ {𝓤 𝓥}
         (X : 𝓤 ̇ )
         (Y : 𝓥 ̇ )
         : 𝓤 ⊔ 𝓥 ̇  where
  inl : X → X + Y
  inr : Y → X + Y

+-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X + Y → 𝓦 ̇ )
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
            → (z : X + Y) → A z
+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y

+-recursion : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
            → (X → A)
            → (Y → A)
            → X + Y → A
+-recursion {𝓤} {𝓥} {𝓦} {X} {Y} {A} =
  +-induction (λ _ → A)

𝟚 : 𝓤₀ ̇
𝟚 = 𝟙 + 𝟙

pattern ₀ = inl *
pattern ₁ = inr *

𝟚-induction : (A : 𝟚 → 𝓤 ̇ )
            → A ₀
            → A ₁
            → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁

𝟚-induction' : (A : 𝟚 → 𝓤 ̇ )
             → A ₀
             → A ₁
             → (n : 𝟚) → A n
𝟚-induction' A a₀ a₁ =
  +-induction A
    (𝟙-induction (λ (x : 𝟙) → A (inl x)) a₀)
    (𝟙-induction (λ (y : 𝟙) → A (inr y)) a₁)

record Σ
       {𝓤 𝓥}
       {X : 𝓤 ̇ }
       (Y : X → 𝓥 ̇ )
       : 𝓤 ⊔ 𝓥 ̇  where
  constructor
    _,_
  field
    x : X
    y : Y x

pr₁ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
    → Σ Y
    → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
    → (z : Σ Y)
    → Y (pr₁ z)
pr₂ (x , y) = y

-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
   → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y

syntax -Σ X (λ x → y) = Σ x ꞉ X , y

Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
            → ((x : X) → (y : Y x) → A (x , y))
            → ((x , y) : Σ Y) → A (x , y)
Σ-induction g (x , y) = g x y

curry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
      → (((x , y) : Σ Y) → A (x , y))
      → (x : X) → (y : Y x) → A (x , y)
curry f x y = f (x , y)

_×_ : 𝓤 ̇  → 𝓥 ̇  → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y  -- same as Σ (λ (x : X) → Y)

