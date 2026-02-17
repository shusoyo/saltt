module mltt where

-- Identity types
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

J : {A : Set}
    (C : (x y : A) → x ≡ y → Set)
    (c : (z : A) → C z z refl)
    {x y : A}
    (p : x ≡ y)
    → C x y p
J {A} C c {x} {.x} refl = c x

sym : {A : Set} (x y : A) → x ≡ y → y ≡ x
sym {A} x y x≡y = J C c x≡y
  where
    C : (x y : A) → x ≡ y → Set
    C x y _ = y ≡ x

    c : (z : A) → C z z refl
    c z = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans {A} {x} {y} {z} p q = (J C c p) z q
  where
    C : (x y : A) → x ≡ y → Set
    C x y _ = (z : A) → y ≡ z → x ≡ z

    c : (w : A) → C w w refl -- C w w refl = (z : A) -> w = w -> w = z
    c w z refl = refl

cong : {A B : Set} {f : A → B} {x y : A} → x ≡ y → f x ≡ f y
cong {A} {B} {f} {x} {y} x≡y = (J C c x≡y) f
  where
    C : (x y : A) → x ≡ y → Set
    C x y _ = (f : A → B) → f x ≡ f y

    c : (z : A) → C z z refl -- C z z refl = (f : A → B) → f z ≡ f z
    c z f = refl