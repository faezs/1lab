<!--
```agda
open import 1Lab.Prelude

open import Data.Real.Multiplication
open import Data.Real.Arithmetic
open import Data.Real.Bounds
open import Data.Real.Rational
open import Data.Real.Order
open import Data.Real.Base
open import Data.Real.Smooth

open import Data.Fin.Properties using (finite-choice)
open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Fin hiding (_≤_ ; _<_)
open import Data.Dec
open import Data.Sum

import Data.Nat as Nat
```
-->

```agda
module Data.Real.Smooth.Bounds where
```

<!--
```agda
private module cut (x : ℝ) = is-cut (x .has-is-cut)

private
  ratℝ-mono : ∀ {p q} → p ≤ q → ratℝ p ≤ᴿ ratℝ q
  ratℝ-mono p≤q r r<p = <-≤-trans r<p p≤q
```
-->

# Bounds for Hadamard towers {defines="bounded-smooth-function bounds-tower"}

A raw [[Hadamard tower|hadamard-tower]] pins its quotients only off
the diagonal: where the coordinate difference is apart from zero,
the quotient's value is forced by ring cancellation, but *at* the
diagonal — precisely where the derivative lives — the tower
equation degenerates to $0 = 0$. To extract derivatives, and later
to compare towers for the same function, we enrich the towers with
**Bishop-style bound data**: on every rational box, every node of
the tower is bounded by a rational. Boundedness of the *next*
level's quotients is a Lipschitz modulus for the current level, so
the enriched towers admit the separation principle that the raw
ones cannot.

The bound data is property-like (a truncated rational bound per
box), so it composes freely along all seven closure combinators of
the raw calculus.

## Boxes and bounded functions

```agda
InBox : ∀ n → Ratio → (Fin n → ℝ) → Type
InBox n R x = (i : Fin n) → absᴿ (x i) ≤ᴿ ratℝ R

Bd : ∀ n → Fun n → Type
Bd n f =
  (R : Ratio) →
  ∥ Σ Ratio (λ M → (x : Fin n → ℝ) → InBox n R x → absᴿ (f x) ≤ᴿ ratℝ M) ∥
```

Constants, projections, and the ring operations transport bounds;
for products the rational bound of the bounding *reals* is
re-extracted from a cut witness, so no rational-versus-real
multiplication lemma is ever needed.

```agda
bd-const : ∀ {n} (c : ℝ) → Bd n (λ _ → c)
bd-const {n} c R = ∥-∥-map
  (λ (v , uv) → v , λ x _ → upper→≤ratℝ {absᴿ c} {v} uv)
  (cut.upper-inhab (absᴿ c))

bd-proj : ∀ {n} (j : Fin n) → Bd n (λ x → x j)
bd-proj j R = inc (R , λ x xb → xb j)

bd-neg : ∀ {n} (f : Fun n) → Bd n f → Bd n (λ x → -ᴿ f x)
bd-neg {n} f bf R = ∥-∥-map
  (λ (M , h) → M , λ x xb → abs-neg {f x} {ratℝ M} (h x xb))
  (bf R)

bd-add
  : ∀ {n} (f g : Fun n)
  → Bd n f → Bd n g → Bd n (λ x → f x +ᴿ g x)
bd-add {n} f g bf bg R = do
  (M , h) ← bf R
  (N , k) ← bg R
  pure $ M +ℚ N , λ x xb →
    subst (absᴿ (f x +ᴿ g x) ≤ᴿ_) (sym (ratℝ-+ M N))
      (abs-sum {f x} {g x} {ratℝ M} {ratℝ N} (h x xb) (k x xb))

bd-mul
  : ∀ {n} (f g : Fun n)
  → Bd n f → Bd n g → Bd n (λ x → f x *ᴿ g x)
bd-mul {n} f g bf bg R = do
  (M , h) ← bf R
  (N , k) ← bg R
  (V , p) ← bounded-above (ratℝ M *ᴿ ratℝ N)
  pure $ V , λ x xb →
    ≤ᴿ-trans {absᴿ (f x *ᴿ g x)} {ratℝ M *ᴿ ratℝ N} {ratℝ V}
      (abs-prod {f x} {g x} {ratℝ M} {ratℝ N} (h x xb) (k x xb))
      p

bd-rename
  : ∀ {n m} (ρ : Fin n → Fin m) (f : Fun n)
  → Bd n f → Bd m (λ y → f (λ j → y (ρ j)))
bd-rename ρ f bf R = ∥-∥-map
  (λ (M , h) → M , λ y yb → h (λ j → y (ρ j)) (λ j → yb (ρ j)))
  (bf R)
```

The composite bound is the one place where boxes genuinely move: a
box for the outer variables must contain the images of the inner
functions, and its radius is a finite maximum of the inner bounds —
extracted with [[finite choice|finite-choice]].

<!--
```agda
private
  maxFin : ∀ {m} → (Fin m → Ratio) → Ratio
  maxFin {zero}  h = 0
  maxFin {suc m} h = maxℚ (h fzero) (maxFin (λ j → h (fsuc j)))

  maxFin-≥ : ∀ {m} (h : Fin m → Ratio) (l : Fin m) → h l ≤ maxFin h
  maxFin-≥ {suc m} h l with fin-view l
  ... | zero   = maxℚ-≤l {h fzero} {maxFin (λ j → h (fsuc j))}
  ... | suc l' = ≤-trans (maxFin-≥ (λ j → h (fsuc j)) l')
    (maxℚ-≤r {h fzero} {maxFin (λ j → h (fsuc j))})
```
-->

```agda
bd-precomp
  : ∀ {n m} (g : Fun m) (G : Fin m → Fun n)
  → Bd m g → (∀ l → Bd n (G l))
  → Bd n (λ y → g (λ l → G l y))
bd-precomp {n} {m} g G bg bG R = do
  bs ← finite-choice m (λ l → bG l R)
  (N , k) ← bg (maxFin (λ l → bs l .fst))
  pure $ N , λ y yb → k (λ l → G l y) λ l →
    ≤ᴿ-trans {absᴿ (G l y)} {ratℝ (bs l .fst)}
      {ratℝ (maxFin (λ l' → bs l' .fst))}
      (bs l .snd y yb)
      (ratℝ-mono (maxFin-≥ (λ l' → bs l' .fst) l))
```

## The bounds tower

The bound tower is indexed by the raw tower it enriches, so all the
quotient algebra — Leibniz, chain rule, renaming — is inherited
rather than re-proved: only the bound bookkeeping is new.

```agda
BdTower : ∀ k n (f : Fun n) → TowerTo k n f → Type
BdTower zero    n f _ = Lift lzero ⊤
BdTower (suc k) n f T =
  (i : Fin n) →
    Bd (suc n) (T i .fst)
  × BdTower k (suc n) (T i .fst) (T i .snd .snd)
```

The structural combinators mirror their raw counterparts clause for
clause, so every goal reduces alongside the raw definition.

```agda
bdt-const : ∀ k n (c : ℝ) → BdTower k n (λ _ → c) (tower-const k n c)
bdt-const zero    n c = lift tt
bdt-const (suc k) n c i = bd-const 0ᴿ , bdt-const k (suc n) 0ᴿ

bdt-proj : ∀ k n (j : Fin n) → BdTower k n (λ x → x j) (tower-proj k n j)
bdt-proj zero    n j = lift tt
bdt-proj (suc k) n j i with Discrete-Fin .decide i j
... | yes _ = bd-const 1ᴿ , bdt-const k (suc n) 1ᴿ
... | no  _ = bd-const 0ᴿ , bdt-const k (suc n) 0ᴿ

bdt-trunc
  : ∀ k {n} {f : Fun n} (T : TowerTo (suc k) n f)
  → BdTower (suc k) n f T → BdTower k n f (tower-trunc k T)
bdt-trunc zero    T BT = lift tt
bdt-trunc (suc k) T BT i =
  BT i .fst , bdt-trunc k (T i .snd .snd) (BT i .snd)

bdt-neg
  : ∀ k n (f : Fun n) (T : TowerTo k n f)
  → BdTower k n f T
  → BdTower k n (λ x → -ᴿ f x) (tower-neg k n f T)
bdt-neg zero    n f T BT = lift tt
bdt-neg (suc k) n f T BT i =
    bd-neg (T i .fst) (BT i .fst)
  , bdt-neg k (suc n) (T i .fst) (T i .snd .snd) (BT i .snd)

bdt-add
  : ∀ k n (f g : Fun n) (T : TowerTo k n f) (S : TowerTo k n g)
  → BdTower k n f T → BdTower k n g S
  → BdTower k n (λ x → f x +ᴿ g x) (tower-add k n f g T S)
bdt-add zero    n f g T S BT BS = lift tt
bdt-add (suc k) n f g T S BT BS i =
    bd-add (T i .fst) (S i .fst) (BT i .fst) (BS i .fst)
  , bdt-add k (suc n) (T i .fst) (S i .fst)
      (T i .snd .snd) (S i .snd .snd)
      (BT i .snd) (BS i .snd)

bdt-rename
  : ∀ k {n m} (ρ : Fin n → Fin m)
  → (inj : ∀ a b → ρ a ≡ ρ b → a ≡ b)
  → (f : Fun n) (T : TowerTo k n f)
  → BdTower k n f T
  → BdTower k m (λ y → f (λ j → y (ρ j))) (tower-rename k ρ inj f T)
bdt-rename zero    ρ inj f T BT = lift tt
bdt-rename (suc k) {n} {m} ρ inj f T BT d
  with holds? (Σ[ j ∈ Fin n ] (ρ j ≡ d))
... | yes (j₀ , hit) =
    bd-rename (lift-ρ ρ) (T j₀ .fst) (BT j₀ .fst)
  , bdt-rename k (lift-ρ ρ) (lift-ρ-inj ρ inj)
      (T j₀ .fst) (T j₀ .snd .snd) (BT j₀ .snd)
... | no miss = bd-const 0ᴿ , bdt-const k (suc m) 0ᴿ

bdt-mul
  : ∀ k n (f g : Fun n) (T : TowerTo k n f) (S : TowerTo k n g)
  → Bd n f → Bd n g
  → BdTower k n f T → BdTower k n g S
  → BdTower k n (λ x → f x *ᴿ g x) (tower-mul k n f g T S)
bdt-mul zero    n f g T S bf bg BT BS = lift tt
bdt-mul (suc k) n f g T S bf bg BT BS i =
    bd-add
      (λ y → f (λ j → y (fsuc j)) *ᴿ S i .fst y)
      (λ y → g (λ j → y (σᵢ i j)) *ᴿ T i .fst y)
      (bd-mul (λ y → f (λ j → y (fsuc j))) (S i .fst)
        (bd-rename fsuc f bf) (BS i .fst))
      (bd-mul (λ y → g (λ j → y (σᵢ i j))) (T i .fst)
        (bd-rename (σᵢ i) g bg) (BT i .fst))
  , bdt-add k (suc n) _ _
      (tower-mul k (suc n) _ (S i .fst)
        (tower-rename k fsuc (λ a b → fsuc-inj) f (tower-trunc k T))
        (S i .snd .snd))
      (tower-mul k (suc n) _ (T i .fst)
        (tower-rename k (σᵢ i) (σᵢ-inj i) g (tower-trunc k S))
        (T i .snd .snd))
      (bdt-mul k (suc n) _ (S i .fst)
        (tower-rename k fsuc (λ a b → fsuc-inj) f (tower-trunc k T))
        (S i .snd .snd)
        (bd-rename fsuc f bf) (BS i .fst)
        (bdt-rename k fsuc (λ a b → fsuc-inj) f (tower-trunc k T)
          (bdt-trunc k T BT))
        (BS i .snd))
      (bdt-mul k (suc n) _ (T i .fst)
        (tower-rename k (σᵢ i) (σᵢ-inj i) g (tower-trunc k S))
        (T i .snd .snd)
        (bd-rename (σᵢ i) g bg) (BT i .fst)
        (bdt-rename k (σᵢ i) (σᵢ-inj i) g (tower-trunc k S)
          (bdt-trunc k S BS))
        (BT i .snd))
```

## Bounding the chain rule

The telescoping quotient of a composite is a fuel-indexed sum of
products; its bound recurses on the fuel in step with
`Comp.Qs`{.Agda}, using the composite bound for the outer quotients
evaluated on the mixed frames.

```agda
bdt-comp
  : ∀ k {n m} (F : Fin m → Fun n) (g : Fun m)
  → (TF : ∀ j → TowerTo k n (F j)) (Tg : TowerTo k m g)
  → (∀ j → Bd n (F j)) → Bd m g
  → (∀ j → BdTower k n (F j) (TF j)) → BdTower k m g Tg
  → BdTower k n (λ x → g (λ j → F j x)) (tower-comp k F g TF Tg)
bdt-comp zero F g TF Tg BF Bg BTF BTg = lift tt
bdt-comp (suc k) {n} {m} F g TF Tg BF Bg BTF BTg i =
  Qs-bd m 0 refl , Qs-bdt m 0 refl
  where
  module CC = Comp k F g TF Tg i

  Frame-bd : ∀ c (cf : Fin m) (l : Fin (suc m)) → Bd (suc n) (Frame F i c cf l)
  Frame-bd c cf l with fin-view l
  ... | zero = bd-rename (σᵢ i) (F cf) (BF cf)
  ... | suc l' with holds? (suc (l' .lower) Nat.≤ c)
  ...   | yes _ = bd-rename (σᵢ i) (F l') (BF l')
  ...   | no  _ = bd-rename fsuc (F l') (BF l')

  Frame-bdt
    : ∀ c (cf : Fin m) (l : Fin (suc m))
    → BdTower k (suc n) (Frame F i c cf l) (CC.Frame-tower c cf l)
  Frame-bdt c cf l with fin-view l
  ... | zero = bdt-rename k (σᵢ i) (σᵢ-inj i) (F cf)
    (tower-trunc k (TF cf)) (bdt-trunc k (TF cf) (BTF cf))
  ... | suc l' with holds? (suc (l' .lower) Nat.≤ c)
  ...   | yes _ = bdt-rename k (σᵢ i) (σᵢ-inj i) (F l')
    (tower-trunc k (TF l')) (bdt-trunc k (TF l') (BTF l'))
  ...   | no  _ = bdt-rename k fsuc (λ a b → fsuc-inj) (F l')
    (tower-trunc k (TF l')) (bdt-trunc k (TF l') (BTF l'))

  Qs-bd : ∀ fuel c eq → Bd (suc n) (CC.Qs fuel c eq)
  Qs-bd zero c eq = bd-const 0ᴿ
  Qs-bd (suc fuel) c eq =
    bd-add
      (λ y → CC.Fq cf y *ᴿ CC.gq cf (λ l → Frame F i c cf l y))
      (CC.Qs fuel (suc c) (sym (Nat.+-sucr c fuel) ∙ eq))
      (bd-mul (CC.Fq cf)
        (λ y → CC.gq cf (λ l → Frame F i c cf l y))
        (BTF cf i .fst)
        (bd-precomp (CC.gq cf) (Frame F i c cf)
          (BTg cf .fst) (λ l → Frame-bd c cf l)))
      (Qs-bd fuel (suc c) (sym (Nat.+-sucr c fuel) ∙ eq))
    where
    cf : Fin m
    cf = fin c ⦃ subst (suc c Nat.≤_) (sym (Nat.+-sucr c fuel) ∙ eq)
          (Nat.s≤s (le-plus c fuel)) ⦄

  Qs-bdt
    : ∀ fuel c eq
    → BdTower k (suc n) (CC.Qs fuel c eq) (CC.Qs-tower fuel c eq)
  Qs-bdt zero c eq = bdt-const k (suc n) 0ᴿ
  Qs-bdt (suc fuel) c eq = bdt-add k (suc n) _ _
    (tower-mul k (suc n) _ _
      (CC.Fdeep cf)
      (tower-comp k (Frame F i c cf) (CC.gq cf)
        (CC.Frame-tower c cf) (CC.gdeep cf)))
    (CC.Qs-tower fuel (suc c) (sym (Nat.+-sucr c fuel) ∙ eq))
    (bdt-mul k (suc n) _ _
      (CC.Fdeep cf)
      (tower-comp k (Frame F i c cf) (CC.gq cf)
        (CC.Frame-tower c cf) (CC.gdeep cf))
      (BTF cf i .fst)
      (bd-precomp (CC.gq cf) (Frame F i c cf)
        (BTg cf .fst) (λ l → Frame-bd c cf l))
      (BTF cf i .snd)
      (bdt-comp k (Frame F i c cf) (CC.gq cf)
        (CC.Frame-tower c cf) (CC.gdeep cf)
        (λ l → Frame-bd c cf l) (BTg cf .fst)
        (λ l → Frame-bdt c cf l) (BTg cf .snd)))
    (Qs-bdt fuel (suc c) (sym (Nat.+-sucr c fuel) ∙ eq))
    where
    cf : Fin m
    cf = fin c ⦃ subst (suc c Nat.≤_) (sym (Nat.+-sucr c fuel) ∙ eq)
          (Nat.s≤s (le-plus c fuel)) ⦄
```

## Bounded-smooth functions

A **bounded-smooth** function carries a raw tower of every depth, a
bound for itself, and a bound tower enriching every level. All
seven closure combinators of the raw calculus lift.

```agda
Smooth⁺ : (n : Nat) → Fun n → Type
Smooth⁺ n f =
  Σ[ S ∈ Smooth n f ]
    (Bd n f × (∀ k → BdTower k n f (S k)))

smooth⁺-const : ∀ {n} (c : ℝ) → Smooth⁺ n (λ _ → c)
smooth⁺-const {n} c =
  smooth-const c , bd-const c , λ k → bdt-const k n c

smooth⁺-proj : ∀ {n} (j : Fin n) → Smooth⁺ n (λ x → x j)
smooth⁺-proj {n} j =
  smooth-proj j , bd-proj j , λ k → bdt-proj k n j

smooth⁺-neg
  : ∀ {n} {f : Fun n} → Smooth⁺ n f → Smooth⁺ n (λ x → -ᴿ f x)
smooth⁺-neg {n} {f} (S , bf , BT) =
    smooth-neg S , bd-neg f bf
  , λ k → bdt-neg k n f (S k) (BT k)

smooth⁺-add
  : ∀ {n} {f g : Fun n}
  → Smooth⁺ n f → Smooth⁺ n g → Smooth⁺ n (λ x → f x +ᴿ g x)
smooth⁺-add {n} {f} {g} (S , bf , BT) (S' , bg , BS) =
    smooth-add S S' , bd-add f g bf bg
  , λ k → bdt-add k n f g (S k) (S' k) (BT k) (BS k)

smooth⁺-mul
  : ∀ {n} {f g : Fun n}
  → Smooth⁺ n f → Smooth⁺ n g → Smooth⁺ n (λ x → f x *ᴿ g x)
smooth⁺-mul {n} {f} {g} (S , bf , BT) (S' , bg , BS) =
    smooth-mul S S' , bd-mul f g bf bg
  , λ k → bdt-mul k n f g (S k) (S' k) bf bg (BT k) (BS k)

smooth⁺-rename
  : ∀ {n m} (ρ : Fin n → Fin m)
  → (inj : ∀ a b → ρ a ≡ ρ b → a ≡ b)
  → {f : Fun n} → Smooth⁺ n f
  → Smooth⁺ m (λ y → f (λ j → y (ρ j)))
smooth⁺-rename ρ inj {f} (S , bf , BT) =
    smooth-rename ρ inj S , bd-rename ρ f bf
  , λ k → bdt-rename k ρ inj f (S k) (BT k)

smooth⁺-comp
  : ∀ {n m} {F : Fin m → Fun n} {g : Fun m}
  → (∀ j → Smooth⁺ n (F j)) → Smooth⁺ m g
  → Smooth⁺ n (λ x → g (λ j → F j x))
smooth⁺-comp {n} {m} {F} {g} SF (Sg , bg , BSg) =
    smooth-comp (λ j → SF j .fst) Sg
  , bd-precomp g F bg (λ j → SF j .snd .fst)
  , λ k → bdt-comp k F g (λ j → SF j .fst k) (Sg k)
      (λ j → SF j .snd .fst) bg
      (λ j → SF j .snd .snd k) (BSg k)
```
