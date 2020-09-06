{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.LawvereTheories where

-- Category of Lawvere Theories

open import Level

open import Categories.Category
open import Categories.Functor.Cartesian.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Theory.Lawvere
--
open import Categories.Functor.Core
open import Categories.Category.Finite.Fin
open import Categories.Category.Instance.FinSetoids
open import Categories.Category.Cartesian
open import Categories.Functor.Cartesian

LawvereTheories : (o ℓ e : Level) → Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
LawvereTheories o ℓ e = record
  { Obj = FiniteProduct o ℓ e
  ; _⇒_ = LT-Hom
  ; _≈_ = λ H₁ H₂ → F H₁ ≃ F H₂
  ; id = LT-id
  ; _∘_ = LT-∘
  ; assoc = λ { {f = f} {g} {h} → associator (F f) (F g) (F h)}
  ; sym-assoc = λ { {f = f} {g} {h} → sym-associator (F f) (F g) (F h)}
  ; identityˡ = unitorˡ
  ; identityʳ = unitorʳ
  ; identity² = unitor²
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = _ⓘₕ_
  }
  where open LT-Hom

shape : FinCatShape
shape = record
  { size = 5
  ; ∣_⇒_∣ = {!   !}
  ; hasShape = {!   !}
  }

record LawvereTheory (o ℓ e : Level) : Set (suc (suc(o ⊔ ℓ ⊔ e))) where
  field
    L : Category o ℓ e
  -- category with finite products
    cartL : Cartesian L

    cartℕ₀ : Cartesian (Category.op (FinSetoids o ℓ))
  -- product preserving bijection on objects functor
    T : Functor (Category.op (FinSetoids o ℓ)) L

    cartT : CartesianF cartℕ₀ cartL T

-- TOOD Sum of Lawvere Theories

-- TODO Tensor Product of Lawvere Theories

-- TODO Model Category for a given Lawvere Theory and Category C
