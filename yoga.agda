module Yoga where

open import Agda.Primitive

--------------------------------------------------------------------------------
-- preliminaries
--------------------------------------------------------------------------------

infixl 0 _←_  -- function space (flipped)
infix  0 _⥴_ -- natural transformation
infix  0 _⥳_ -- natural transformation (flipped)
infix  0 Π    -- dependent product
infix  0 ∐    -- dependent coproduct
infixr 2 _⋘_  -- composition
infixl 2 _⋙_  -- composition (flipped)
infixr 0 _·≪_ -- application
infixl 0 _≫·_ -- application (flipped) / cps / yoneda embedding
infixr 8 _,_  -- pair
infixr 0 _×_  -- product
infixr 0 _+_  -- sum
infix  1 _≡_  -- equality / paths
infix  0 !    -- bang / const
infix  0 ⸮    -- cobang / ask / force

_←_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
B ← A = A → B

_⥴_ : ∀ {d u v} {𝔡 : Set d} → (𝔡 → Set u) → (𝔡 → Set v) → Set (d ⊔ u ⊔ v)
f ⥴ g = ∀ {x} → f x → g x

_⥳_ : ∀ {d u v} {𝔡 : Set d} → (𝔡 → Set u) → (𝔡 → Set v) → Set (d ⊔ u ⊔ v)
g ⥳ f = ∀ {x} → f x → g x

Π : ∀ {a b} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
Π A B = (x : A) → B x

syntax Π A (λ x → B) = Π[ x ∶ A ] B

id : ∀ {a} {A : Set a} → A → A
id x = x

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const a b = a

_⋘_ : ∀ {a b c}
  → {A : Set a}
  → {B : A → Set b}
  → {C : {x : A} → B x → Set c}
  → (g : (∀ {x} (y : B x) → C y))
  → (f : (x : A) → B x)
  → ((x : A) → C (f x))
g ⋘ f = λ x → g (f x)

_⋙_ : ∀ {a b c}
  → {A : Set a }
  → {B : A → Set b}
  → {C : {x : A} → B x → Set c}
  → (f : (x : A) → B x)
  → (g : (∀ {x} (y : B x) → C y))
  → ((x : A) → C (f x))
f ⋙ g = g ⋘ f

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  → (A → B → C)
  → (B → A → C)
flip f x y = f y x

Yo : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Yo B = λ A → A → B

oY : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
oY = flip Yo

_·≪_ : ∀ {a b} {A : Set a} {B : A → Set b} → Π A B → Π A B
f ·≪ x = f x

_≫·_ : ∀ {a b} {A : Set a} {B : A → Set b} → Π A ·≪ oY (Π A B) ⋘ B
x ≫· f = f ·≪ x

record ⊤ : Set where
  constructor tt

! : ∀ {b} {B : Set b} → B → ⊤
! = const tt

⸮ : ∀ {b} {B : ⊤ → Set b} → Π ⊤ B → B tt
⸮ = _≫·_ tt

data Bool : Set where
  false : Bool
  true  : Bool

pick : ∀ {a} {A : Set a} → A → A → Bool → A
pick x y false = x
pick x y true  = y

record ∐ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
open ∐

syntax ∐ A (λ x → B) = ∐[ x ∶ A ] B

_×_ : ∀ {a b} → (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = ∐ A ·≪ const B

δ : ∀ {a} {A : Set a} → A → A × A
δ x = (x , x)

⟨_,_⟩ : ∀ {a b x} {A : Set a} {B : A → Set b} {X : Set x}
  → (f : X → A)
  → Π X (B ⋘ f)
  → (X → ∐ A B)
⟨ f , g ⟩ x = f x , g x

⟨_×_⟩ : ∀ {a b x₀} {A : Set a} {B : A → Set b} {X₀ : Set x₀} {X₁ : X₀ → Set b}
  → (f : X₀ → A)
  → (X₁ ⥴ B ⋘ f)
  → (∐ X₀ X₁ → ∐ A B)
⟨_×_⟩ f g (x , y) = f x , g y

_+_ : ∀ {i} → (A : Set i) (B : Set i) → Set i
A + B = ∐ Bool ·≪ pick A B

[_,_] : ∀ {a x} {A : Set a} {B : Set a} {X : Set x}
  → (A → X)
  → (B → X)
  → (A + B → X)
[ f , g ] (false , x) = f x
[ f , g ] (true  , x) = g x

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

∫↓ : ∀ {a b} {X : Set a} → (X → X → Set b) → Set (a ⊔ b)
∫↓ {X = X} P = ∀ {x} → P x x

∫↑ : ∀ {a b} {X : Set a} → (X → X → Set b) → Set (a ⊔ b)
∫↑ {X = X} P = ∐[ x ∶ X ] P x x

Ran
  : ∀ {x c v u p} {𝔵 : Set x} {𝔠 : Set c} {𝔳 : Set v}
  → (𝒸 : 𝔠 → 𝔠 → Set u)
  → (_⋔_ : Set u → 𝔳 → Set p)
  → (G : 𝔵 → 𝔠)
  → (H : 𝔵 → 𝔳)
  → (𝔠 → Set (p ⊔ x))
Ran 𝒸 _⋔_ G H A = ∫↓ λ x y → 𝒸 A (G x) ⋔ H y

Lan
  : ∀ {x c v u p} {𝔵 : Set x} {𝔠 : Set c} {𝔳 : Set v}
  → (𝒸 : 𝔠 → 𝔠 → Set u)
  → (_⊗_ : 𝔳 → Set u → Set p)
  → (G : 𝔵 → 𝔠)
  → (H : 𝔵 → 𝔳)
  → (𝔠 → Set (p ⊔ x))
Lan 𝒸 _⊗_ G H A = ∫↑ λ x y → H x ⊗ 𝒸 (G y) A

--------------------------------------------------------------------------------
-- Indexing
--------------------------------------------------------------------------------

𝒫 : ∀ {i} p → Set i → Set (i ⊔ lsuc p)
𝒫 p I = I → Set p

Prop′ : ∀ {a} → Set a → Set a
Prop′ I = I → ⊤

--------------------------------------------------------------------------------
-- Grothendieck's Yoga of Six Operations and Wirthmüller Contexts
--------------------------------------------------------------------------------

infixr 0 _⋔_ -- pitchfork / implication / function space / internal hom / power
infixr 0 _⊗_ -- tensor / conjunction / cartesian product / monoidal product / copower
infix  3 _↓! -- lower shriek / existential / dependent coproduct / pushforward / total space / proper image / lan / coend
infix  3 _↑! -- upper shriek / base change / precomposition / pullback / exceptional inverse image
infix  3 _↑* -- upper star / base change / precomposition / pullback / constant sheaf / inverse image
infix  3 _↓* -- lower star / universal / dependent product / global section space / direct image / ran / end

--        𝒞 ---- f ---> 𝒟
-- ==============================
-- 𝒫(𝒞) --[ f ↓! ⊣      ] -> 𝒫(𝒟) ≜ Lan (≡) (⊗) f ≅ λ φ. ∫↑ 𝓍. φ 𝓍 ⊗ (≡) (f 𝓍, -)
-- 𝒫(𝒞) <-[ f ↑! ≃ f ↑* ] -- 𝒫(𝒟) ≜         - ∘ f ≅ λ φ. φ ∘ f
-- 𝒫(𝒞) --[      ⊣ f ↓* ] -> 𝒫(𝒟) ≜ Ran (≡) (⋔) f ≅ λ φ. ∫↓ 𝓍. (≡) (-, f 𝓍) ⋔ φ 𝓍

_⋔_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
_⋔_ A B = A → B

_⊗_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
_⊗_ A B = A × B

_↓! : ∀ {x y} {X : Set x} {Y : Set y} → (X → Y) → 𝒫 x X → 𝒫 (x ⊔ y) Y
_↓! f = Lan _≡_ _⊗_ f

_↑! : ∀ {x y} {X : Set x} {Y : Set y} → (X → Y) → 𝒫 x Y → 𝒫 x X
_↑! f = λ φ → φ ⋘ f

_↑* : ∀ {x y} {X : Set x} {Y : Set y} → (X → Y) → 𝒫 x Y → 𝒫 x X
_↑* f = _↑! f

_↓* : ∀ {x y} {X : Set x} {Y : Set y} → (X → Y) → 𝒫 x X → 𝒫 (x ⊔ y) Y
_↓* f = Ran _≡_ _⋔_ f

--------------------------------------------------------------------------------
-- Hyperdoctrines
--------------------------------------------------------------------------------

infix 1 ∈  -- membership
infix 1 ∋  -- membership (flipped)
infix 1 ⊆  -- subset
infix 0 ∃  -- existential
infix 0 Δ  -- substitution
infix 0 ∀′ -- universal

∈ : ∀ {x y} {X : Set x} → X → 𝒫 y X → Set y
∈ = _≫·_

∋ : ∀ {x y} {X : Set x} → 𝒫 y X → X → Set y
∋ = flip ∈

⊆ : ∀ {y z x} {X : Set x} → 𝒫 y X × 𝒫 z X → Set (x ⊔ y ⊔ z)
⊆ (ψ , φ) = ∋ ψ ⥴ ∋ φ

∃ : ∀ {x y} {X : Set x} {Y : Set y} → (X → Y) → 𝒫 x X → 𝒫 (x ⊔ y) Y
∃ f = f ↓!

Δ : ∀ {x y} {X : Set x} {Y : Set y} → (X → Y) → 𝒫 x Y → 𝒫 x X
Δ f = f ↑*

∀′ : ∀ {x y} {X : Set x} {Y : Set y} → (X → Y) → 𝒫 x X → 𝒫 (x ⊔ y) Y
∀′ f = f ↓*

-- NOTE: Y can be Set y if we explicitly quantifier rather than using ⥴
↓!⇒↑! : ∀ {x} {X : Set x} {Y : Set x} {f : X → Y} → ⊆ ⋘ ⟨ ∃ f × id ⟩ ⥴ ⊆ ⋘ ⟨ id × Δ f ⟩
↓!⇒↑! p x = p (_ , x , refl)

↓!⇐↑! : ∀ {x} {X : Set x} {Y : Set x} {f : X → Y} → ⊆ ⋘ ⟨ ∃ f × id ⟩ ⥳ ⊆ ⋘ ⟨ id × Δ f ⟩
↓!⇐↑! p (_ , x , refl) = p x

↑*⇒↓* : ∀ {x} {X : Set x} {Y : Set x} {f : X → Y} → ⊆ ⋘ ⟨ Δ f × id ⟩ ⥴ ⊆ ⋘ ⟨ id × ∀′ f ⟩
↑*⇒↓* p x refl = p x

↑*⇐↓* : ∀ {x} {X : Set x} {Y : Set x} {f : X → Y} → ⊆ ⋘ ⟨ Δ f × id ⟩ ⥳ ⊆ ⋘ ⟨ id × ∀′ f ⟩
↑*⇐↓* p x = p x refl

--------------------------------------------------------------------------------
-- Extension isomorphisms
--------------------------------------------------------------------------------

∈⋘!·↓!⥴∐ : ∀ {x} {X : Set x} → ⸮ ⋘ ! ↓! ⥴ ∐ X
∈⋘!·↓!⥴∐ (x , φ , refl) = x , φ

∈⋘!·↓!⥳∐ : ∀ {x} {X : Set x} → ⸮ ⋘ ! ↓! ⥳ ∐ X
∈⋘!·↓!⥳∐ (x , φ) = x , φ , refl

∈⋘!·↓*⥴Π : ∀ {x} {X : Set x} → ⸮ ⋘ ! ↓* ⥴ Π X
∈⋘!·↓*⥴Π φ x = φ {x} refl

∈⋘!·↓*⥳Π : ∀ {x} {X : Set x} → ⸮ ⋘ ! ↓* ⥳ Π X
∈⋘!·↓*⥳Π f {x} refl = f x

--------------------------------------------------------------------------------
-- Frobenius reciprocity
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Beck-Chevalley condition
--------------------------------------------------------------------------------
