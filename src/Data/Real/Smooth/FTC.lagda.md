<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import 1Lab.Truncation
open import 1Lab.Prelude

open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring

open import Data.Rational.Properties
open import Data.Rational.Solver
open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Real.Multiplication
open import Data.Real.Complete
open import Data.Real.Arithmetic
open import Data.Real.Rational
open import Data.Real.Bounds
open import Data.Real.Order
open import Data.Real.Base
open import Data.Real.Ring
open import Data.Real.Smooth
open import Data.Real.Smooth.Bounds
open import Data.Real.Smooth.Derivative
  using (ratℝ-*-≤ ; abs-nonneg ; diff-zero→≡ ; ∂-of ; quot-smooth⁺ ; ∂-smooth⁺)
open import Data.Real.Smooth.Integral
open import Data.Real.Smooth.Convergence

open import Data.Fin using (Fin ; fzero ; fsuc ; fin-view ; Discrete-Fin ; Fin-absurd ; Fin-cases)
open import Data.Dec
open import Data.Sum

open import Data.Nat.Base using (Nat ; zero ; suc ; _+_)
import Data.Nat as Nat
import Data.Int.Base as ℤ
```
-->

```agda
module Data.Real.Smooth.FTC where
```

<!--
```agda
private module Identities {ℓ} (S : CRing ℓ) where
  private module R = CRing-on (S .snd)

  mul-sub : ∀ c x y → c R.* (y R.+ (R.- x)) ≡ (c R.* y) R.+ (R.- (c R.* x))
  mul-sub c x y = cring! S

  tele-cons
    : ∀ a b c → (b R.+ (R.- a)) R.+ (c R.+ (R.- b)) ≡ c R.+ (R.- a)
  tele-cons a b c = cring! S

private module RI = Identities ℝ-comm

private
  ≤ᴿ-prop : ∀ {a b : ℝ} → is-prop (a ≤ᴿ b)
  ≤ᴿ-prop {a} {b} = Π-is-hlevel 1 λ q → Π-is-hlevel 1 λ _ →
    (b .lower q) .is-tr
```
-->

# The Fundamental Theorem of Calculus, direction 1 {defines="fundamental-theorem-of-calculus"}

`Data.Real.Smooth.Convergence`{.Agda} **constructs** the Riemann
integral `∫L`{.Agda} of a Lipschitz-witnessed integrand over an
oriented dyadic box, and `Data.Real.Smooth.Derivative`{.Agda}
**constructs** the derivative `∂-of`{.Agda} of a
[[bounded-smooth function|bounded-smooth-function]] as the diagonal
value of its depth-two [[Hadamard quotient|hadamard-tower]]. This
module ties the two together: the integral of a derivative over
$[a,b]$ *is* the difference of the endpoint values.

The proof is purely algebraic, and is the reason the Hadamard
presentation of smoothness was worth the trouble. Writing $g$ for
the depth-two quotient of $F$ in the single direction, the defining
equation
$$
F(x) - F(x[0 \mapsto t]) = (x_{0} - t)\, g(t, x)
$$
instantiated at consecutive dyadic nodes $x_{i} < x_{i+1}$ reads
$$
F(x_{i+1}) - F(x_{i}) = h_{n}\, g(x_{i}, x_{i+1}),
$$
an **exact** identity: no limits, no error term. Summing it over the
partition telescopes to $F(b) - F(a)$ on the nose. The Riemann sum of
the derivative differs from that telescope only in that $g$ is
evaluated on the *diagonal* $g(x_{i}, x_{i})$ instead of at
$g(x_{i}, x_{i+1})$ — and the displacement between those two
arguments is one mesh width, so the total defect is bounded by
$2^{n} \cdot h_{n} \cdot (M_{2} h_{n}) = M_{2}\,\Delta^{2}\,2^{-n}$,
which vanishes. The Lipschitz modulus $M_{2}$ of $g$ in its second
argument is again supplied by the bound tower, one level up, through
`quot-smooth⁺`{.Agda}.

Consequently the difference $F(b) - F(a)$ **is** a Riemann limit of
$\partial F$, and by uniqueness of Riemann limits it is the
constructed integral. As a corollary that needs no Lipschitz witness
at all, a bounded-smooth function whose derivative vanishes
identically has equal endpoint values — the **constancy principle**,
which is what turns a differential law into finite-time evolution.

## Telescoping finite sums

Two elementary facts about `sumᴿ`{.Agda}: a sum of consecutive
differences collapses to the outer difference, and a sum of zeroes is
zero.

```agda
sumᴿ-telescope
  : ∀ K (u : Nat → ℝ)
  → sumᴿ K (λ i → u (suc i) +ᴿ (-ᴿ u i)) ≡ u K +ᴿ (-ᴿ u 0)
sumᴿ-telescope zero    u = sym (+ᴿ-invr (u 0))
sumᴿ-telescope (suc K) u =
    ap (_+ᴿ (u (suc K) +ᴿ (-ᴿ u K))) (sumᴿ-telescope K u)
  ∙ RI.tele-cons (u 0) (u K) (u (suc K))

sumᴿ-zero : ∀ K → sumᴿ K (λ _ → 0ᴿ) ≡ 0ᴿ
sumᴿ-zero zero    = refl
sumᴿ-zero (suc K) = ap (_+ᴿ 0ᴿ) (sumᴿ-zero K) ∙ +ᴿ-idr 0ᴿ
```

<!--
```agda
private
  *ᴿ-zeror : ∀ x → x *ᴿ 0ᴿ ≡ 0ᴿ
  *ᴿ-zeror x =
      sym (+ᴿ-idr (x *ᴿ 0ᴿ))
    ∙ ap ((x *ᴿ 0ᴿ) +ᴿ_) (sym (+ᴿ-invr (x *ᴿ 0ᴿ)))
    ∙ +ᴿ-assoc (x *ᴿ 0ᴿ) (x *ᴿ 0ᴿ) (-ᴿ (x *ᴿ 0ᴿ))
    ∙ ap (_+ᴿ (-ᴿ (x *ᴿ 0ᴿ)))
        ( sym (*ᴿ-distribˡ x 0ᴿ 0ᴿ)
        ∙ ap (x *ᴿ_) (+ᴿ-idr 0ᴿ))
    ∙ +ᴿ-invr (x *ᴿ 0ᴿ)

  neg0 : (-ᴿ 0ᴿ) ≡ 0ᴿ
  neg0 = ratℝ-neg 0 ∙ ap ratℝ neg-zero

  abs0 : absᴿ 0ᴿ ≡ 0ᴿ
  abs0 = ap (maxᴿ 0ᴿ) neg0 ∙ maxᴿ-idem 0ᴿ

  abs-ratℝ-≤ : ∀ {r s} → (-ℚ s) ≤ r → r ≤ s → absᴿ (ratℝ r) ≤ᴿ ratℝ s
  abs-ratℝ-≤ {r} {s} -s≤r r≤s = abs-≤ {ratℝ r} {ratℝ s}
    (ratℝ-mono r≤s)
    (subst (_≤ᴿ ratℝ r) (sym (ratℝ-neg s)) (ratℝ-mono -s≤r))

  neg≤self : ∀ {x} → 0 ≤ x → (-ℚ x) ≤ x
  neg≤self {x} 0≤x = ≤-trans (≤-resp refl neg-zero (negℚ-anti-≤ 0≤x)) 0≤x

  0≤half : ∀ {x} → 0 ≤ x → 0 ≤ half x
  0≤half {x} 0≤x = ≤-resp (*ℚ-zerol (invℚ 2)) refl
    (*ℚ-preserves-≤r (invℚ 2) 0≤x (<-weaken (invℚ-pos {2} 0<2)))
    where
    0<2 : 0 < 2
    0<2 = decide!
```
-->

<!--
```agda
private abstract
  nℚ-suc : ∀ n → nℚ (suc n) ≡ 1 +ℚ nℚ n
  nℚ-suc n =
    ℤ.pos (suc n) / 1        ≡˘⟨ ap (_/ 1) one+pos ⟩
    (1 ℤ.+ℤ ℤ.pos n) / 1     ≡˘⟨ +ℚ-common-denom 1 1 (ℤ.pos n) ⟩
    (1 / 1) +ℚ (ℤ.pos n / 1) ∎
    where
    one+pos : (1 ℤ.+ℤ ℤ.pos n) ≡ ℤ.pos (suc n)
    one+pos = refl

  nℚ-one : nℚ 1 ≡ 1
  nℚ-one = nℚ-suc 0 ∙ +ℚ-idr 1

  nℚ-nonneg : ∀ n → 0 ≤ nℚ n
  nℚ-nonneg zero    = ≤-refl
  nℚ-nonneg (suc n) = subst (0 ≤_) (sym (nℚ-suc n))
    (≤-resp (+ℚ-idl 0) refl
      (+ℚ-preserves-≤ (<-weaken 0<1') (nℚ-nonneg n)))

  nℚ-add : ∀ m n → nℚ (m + n) ≡ nℚ m +ℚ nℚ n
  nℚ-add zero    n = sym (+ℚ-idl (nℚ n))
  nℚ-add (suc m) n =
      nℚ-suc (m + n)
    ∙ ap (1 +ℚ_) (nℚ-add m n)
    ∙ +ℚ-associative 1 (nℚ m) (nℚ n)
    ∙ ap (_+ℚ nℚ n) (sym (nℚ-suc m))

  ≤→+ : ∀ {m n} → m Nat.≤ n → Σ Nat (λ k → m + k ≡ n)
  ≤→+ {zero}  {n}     _  = n , refl
  ≤→+ {suc m} {zero}  le = absurd (Nat.¬suc≤0 le)
  ≤→+ {suc m} {suc n} le =
    let (k , e) = ≤→+ {m} {n} (Nat.≤-peel le) in k , ap suc e

  nℚ-mono : ∀ {m n} → m Nat.≤ n → nℚ m ≤ nℚ n
  nℚ-mono {m} {n} le =
    let (k , e) = ≤→+ le in
    subst (nℚ m ≤_) (ap nℚ e)
      (subst (nℚ m ≤_) (sym (nℚ-add m k))
        (≤-resp (+ℚ-idr (nℚ m)) refl
          (+ℚ-preserves-≤ (≤-refl {nℚ m}) (nℚ-nonneg k))))
```
-->

## Powers of one half are antitone

The convergence estimate of `Data.Real.Smooth.Convergence`{.Agda}
produces a bound of the shape $C\,(1/2)^{n}$; to feed it to
`is-Rlim`{.Agda} we need the bound to be *eventually* small, i.e. that
$(1/2)^{n}$ decreases along the naturals. One step is
`invℚ`{.Agda}-antitonicity applied to $2^{n} < 2^{n+1}$; the general
case is an induction on the gap.

```agda
tpi-mono : ∀ {m n} → m Nat.≤ n → two-pow-inv n ≤ two-pow-inv m
```

<!--
```agda
private
  nz-pow2 : ∀ n → Nonzero (nℚ (pow2 n))
  nz-pow2 n = inc (positive→nonzero (to-positive (0<nℚ-pow2 n)))

  tpi-step : ∀ n → two-pow-inv (suc n) ≤ two-pow-inv n
  tpi-step n = <-weaken (invℚ-anti-< {nℚ (pow2 n)} {nℚ (pow2 (suc n))}
    ⦃ nz-pow2 n ⦄ ⦃ nz-pow2 (suc n) ⦄ (0<nℚ-pow2 n) pow2<)
    where
    pow2< : nℚ (pow2 n) < nℚ (pow2 (suc n))
    pow2< = <-resp refl (sym (nℚ-add (pow2 n) (pow2 n)))
      (add-pos-< (nℚ (pow2 n)) (nℚ (pow2 n)) (0<nℚ-pow2 n))

  tpi-drop : ∀ k m → two-pow-inv (k + m) ≤ two-pow-inv m
  tpi-drop zero    m = ≤-refl {two-pow-inv m}
  tpi-drop (suc k) m = ≤-trans (tpi-step (k + m)) (tpi-drop k m)

tpi-mono {m} {n} m≤n =
  let (k , e) = ≤→+ m≤n
  in subst (λ z → two-pow-inv z ≤ two-pow-inv m)
       (sym (Nat.+-commutative m k) ∙ e)
       (tpi-drop k m)
```
-->

## Lipschitz in the second coordinate

`Convergence`{.Agda} extracts a rational Lipschitz modulus for a
one-variable bounded-smooth function from its depth-one quotient
bound. The defect estimate below needs the same fact one level up:
a modulus for a *two*-variable bounded-smooth function in its
**second** coordinate only, with the first coordinate held fixed at a
rational tag. The record is the exact analogue of
`LipBound`{.Agda}, with the frozen coordinate `c` threaded through.

```agda
record Lip₂ (g : Fun 2) (R : Ratio) : Type where
  no-eta-equality
  field
    M₂   : Ratio
    0≤M₂ : 0 ≤ M₂
    lip₂ : (c p q d : Ratio)
         → (p +ℚ (-ℚ q)) ≤ d → (-ℚ d) ≤ (p +ℚ (-ℚ q))
         → absᴿ (ratℝ c) ≤ᴿ ratℝ R
         → absᴿ (ratℝ p) ≤ᴿ ratℝ R
         → absᴿ (ratℝ q) ≤ᴿ ratℝ R
         → absᴿ (g (cons (ratℝ c) (pt p)) +ᴿ (-ᴿ g (cons (ratℝ c) (pt q))))
           ≤ᴿ ratℝ (M₂ *ℚ d)
```

The extraction mirrors `Smooth⁺→LipBound`{.Agda}: take the depth-one
quotient of `g` in the direction `fsuc fzero`, which is a function of
three variables bounded on the box by `Bd`{.Agda}; the quotient
equation turns $g(c,p) - g(c,q)$ into $(p-q)$ times that quotient
evaluated at a point of the box. As there, the separation $p - q$
enters through a two-sided *rational* bracket, so `absℚ`{.Agda} never
appears.

<!--
```agda
private
  fin1-zero : (i : Fin 1) → fzero ≡ i
  fin1-zero = Fin-cases {P = λ k → fzero ≡ k} refl (λ i → absurd (Fin-absurd i))

  set-pt : ∀ (p q : Ratio) → set (pt p) fzero (ratℝ q) ≡ pt q
  set-pt p q = funext go where
    go : (j : Fin 1) → set (pt p) fzero (ratℝ q) j ≡ pt q j
    go j with Discrete-Fin .decide fzero j
    ... | yes _ = refl
    ... | no ¬e = absurd (¬e (fin1-zero j))

  set-mid
    : ∀ (c t : ℝ) (x : Fin 1 → ℝ)
    → set (cons c x) (fsuc fzero) t ≡ cons c (λ _ → t)
  set-mid c t x = funext go where
    go : (j : Fin 2) → set (cons c x) (fsuc fzero) t j ≡ cons c (λ _ → t) j
    go j with Discrete-Fin .decide (fsuc fzero) j
    ... | yes e = ap (cons c (λ _ → t)) e
    ... | no ¬e =
      Fin-cases
        {P = λ k → ¬ (fsuc fzero ≡ k) → cons c x k ≡ cons c (λ _ → t) k}
        (λ _ → refl)
        (λ i ne → absurd (ne (ap fsuc (fin1-zero i))))
        j ¬e
```
-->

```agda
Smooth⁺→Lip₂ : (g : Fun 2) (R : Ratio) → Smooth⁺ 2 g → ∥ Lip₂ g R ∥
Smooth⁺→Lip₂ g R Ag = ∥-∥-map mk-lip (Bd3 R)
  where
  i₂ : Fin 2
  i₂ = fsuc fzero

  g₂ : Fun 3
  g₂ = Ag .fst 1 i₂ .fst

  qeq₂ : Quot 2 g i₂ g₂
  qeq₂ = Ag .fst 1 i₂ .snd .fst

  Bd3 : Bd 3 g₂
  Bd3 = Ag .snd .snd 1 i₂ .fst

  mk-lip
    : Σ Ratio (λ M' → (z : Fin 3 → ℝ) → InBox 3 R z → absᴿ (g₂ z) ≤ᴿ ratℝ M')
    → Lip₂ g R
  mk-lip (M' , gbd) = record
    { M₂ = maxℚ M' 0 ; 0≤M₂ = maxℚ-≤r {M'} {0} ; lip₂ = liplemma }
    where
    liplemma
      : (c p q d : Ratio)
      → (p +ℚ (-ℚ q)) ≤ d → (-ℚ d) ≤ (p +ℚ (-ℚ q))
      → absᴿ (ratℝ c) ≤ᴿ ratℝ R
      → absᴿ (ratℝ p) ≤ᴿ ratℝ R
      → absᴿ (ratℝ q) ≤ᴿ ratℝ R
      → absᴿ (g (cons (ratℝ c) (pt p)) +ᴿ (-ᴿ g (cons (ratℝ c) (pt q))))
        ≤ᴿ ratℝ (maxℚ M' 0 *ℚ d)
    liplemma c p q d pq≤d -d≤pq |c|≤R |p|≤R |q|≤R =
      subst (λ z → absᴿ z ≤ᴿ ratℝ (maxℚ M' 0 *ℚ d)) (sym qeq-inst)
        (≤ᴿ-trans {absᴿ (X *ᴿ Y)} {ratℝ d *ᴿ ratℝ (maxℚ M' 0)}
          {ratℝ (maxℚ M' 0 *ℚ d)}
          (abs-prod {X} {Y} {ratℝ d} {ratℝ (maxℚ M' 0)} Xbound Ybound)
          (subst (λ w → (ratℝ d *ᴿ ratℝ (maxℚ M' 0)) ≤ᴿ w)
            (ap ratℝ (*ℚ-commutative d (maxℚ M' 0)))
            (ratℝ-*-≤ d (maxℚ M' 0))))
      where
      X : ℝ
      X = ratℝ p +ᴿ (-ᴿ ratℝ q)

      Y : ℝ
      Y = g₂ (cons (ratℝ q) (cons (ratℝ c) (pt p)))

      qeq-inst
        : g (cons (ratℝ c) (pt p)) +ᴿ (-ᴿ g (cons (ratℝ c) (pt q))) ≡ X *ᴿ Y
      qeq-inst =
          sym (ap (λ w → g (cons (ratℝ c) (pt p)) +ᴿ (-ᴿ g w))
                (set-mid (ratℝ c) (ratℝ q) (pt p)))
        ∙ qeq₂ (cons (ratℝ c) (pt p)) (ratℝ q)

      pq-path : X ≡ ratℝ (p +ℚ (-ℚ q))
      pq-path = ap (ratℝ p +ᴿ_) (ratℝ-neg q) ∙ sym (ratℝ-+ p (-ℚ q))

      Xbound : absᴿ X ≤ᴿ ratℝ d
      Xbound = subst (λ z → absᴿ z ≤ᴿ ratℝ d) (sym pq-path)
        (abs-ratℝ-≤ {p +ℚ (-ℚ q)} {d} -d≤pq pq≤d)

      inbox : InBox 3 R (cons (ratℝ q) (cons (ratℝ c) (pt p)))
      inbox = Fin-cases |q|≤R (Fin-cases |c|≤R (λ _ → |p|≤R))

      Ybound : absᴿ Y ≤ᴿ ratℝ (maxℚ M' 0)
      Ybound = ≤ᴿ-trans {absᴿ Y} {ratℝ M'} {ratℝ (maxℚ M' 0)}
        (gbd (cons (ratℝ q) (cons (ratℝ c) (pt p))) inbox)
        (ratℝ-mono (maxℚ-≤l {M'} {0}))
```

## The dyadic nodes

The successor node is the previous node shifted by one mesh; the
extreme nodes are the endpoints. These are the three rational
identities the telescope runs on.

```agda
node-step
  : ∀ a b n i → dyadic a b n (suc i) ≡ (dyadic a b n i +ℚ msh a b n)
node-step a b n i =
    ap (λ z → a +ℚ (z *ℚ msh a b n)) (nℚ-suc i)
  ∙ ap (a +ℚ_) (*ℚ-distribr (msh a b n) 1 (nℚ i))
  ∙ ap (λ z → a +ℚ (z +ℚ (nℚ i *ℚ msh a b n))) (*ℚ-idl (msh a b n))
  ∙ shuffle a (msh a b n) (nℚ i *ℚ msh a b n)
  where
  shuffle : ∀ A H M → (A +ℚ (H +ℚ M)) ≡ ((A +ℚ M) +ℚ H)
  shuffle A H M = rational!

dyadic-top : ∀ a b n → dyadic a b n (pow2 n) ≡ b
dyadic-top a b n = ap (a +ℚ_) (pow-msh a b n) ∙ collapse a b
  where
  collapse : ∀ p q → (p +ℚ (q +ℚ (-ℚ p))) ≡ q
  collapse p q = rational!

dyadic-bot : ∀ a b n → dyadic a b n 0 ≡ a
dyadic-bot a b n =
    ap (λ z → a +ℚ (z *ℚ msh a b n)) nℚ-zero
  ∙ ap (a +ℚ_) (*ℚ-zerol (msh a b n))
  ∙ +ℚ-idr a
  where
  nℚ-zero : nℚ 0 ≡ 0
  nℚ-zero = refl
```

# The exact telescope and its defect {defines="ftc-telescope"}

Fix a bounded-smooth $F$ on an oriented box $a \le b$. Write $g$ for
its depth-two quotient in the single direction, $\Delta = b - a$ for
the width and $R = \max(b, -a)$ for the box radius.

```agda
module _ (F : Fun 1) (A : Smooth⁺ 1 F) (a b : Ratio) (a≤b : a ≤ b) where
  private
    G : Fun 2
    G = A .fst 2 fzero .fst

    qeq : Quot 1 F fzero G
    qeq = A .fst 2 fzero .snd .fst

    ∂F : Fun 1
    ∂F = ∂-of F fzero A

    Δ : Ratio
    Δ = b +ℚ (-ℚ a)

    R : Ratio
    R = boxR a b

    msh-nn : ∀ n → 0 ≤ msh a b n
    msh-nn zero    = ≤-resp (+ℚ-invr a) refl
      (+ℚ-preserves-≤ a≤b (≤-refl { -ℚ a}))
    msh-nn (suc n) = 0≤half (msh-nn n)

    0≤Δ : 0 ≤ Δ
    0≤Δ = msh-nn zero
```

## Nodes stay in the box

Every node with index at most $2^{n}$ — including the top one — lies
in $[a,b]$, hence in $[-R, R]$.

```agda
    node-hi : ∀ n i → i Nat.≤ pow2 n → dyadic a b n i ≤ R
    node-hi n i i≤pn = ≤-trans dyadic≤b (maxℚ-≤l {b} { -ℚ a})
      where
      prod≤ : (nℚ i *ℚ msh a b n) ≤ Δ
      prod≤ = ≤-resp refl (pow-msh a b n)
        (*ℚ-preserves-≤r (msh a b n) (nℚ-mono i≤pn) (msh-nn n))

      adia : ∀ p q → (p +ℚ (q +ℚ (-ℚ p))) ≡ q
      adia p q = rational!

      dyadic≤b : dyadic a b n i ≤ b
      dyadic≤b = ≤-resp refl (adia a b)
        (+ℚ-preserves-≤ (≤-refl {a}) prod≤)

    node-lo : ∀ n i → (-ℚ R) ≤ dyadic a b n i
    node-lo n i = ≤-trans -R≤a a≤dyadic
      where
      -R≤a : (-ℚ R) ≤ a
      -R≤a = ≤-resp refl (negℚ-invol a) (negℚ-anti-≤ (maxℚ-≤r {b} { -ℚ a}))

      a≤dyadic : a ≤ dyadic a b n i
      a≤dyadic = ≤-resp (+ℚ-idr a) refl
        (+ℚ-preserves-≤ (≤-refl {a})
          (*ℚ-nonnegative (nℚ-nonneg i) (msh-nn n)))

    node-abs
      : ∀ n i → i Nat.≤ pow2 n → absᴿ (ratℝ (dyadic a b n i)) ≤ᴿ ratℝ R
    node-abs n i i≤pn = abs-ratℝ-≤ {dyadic a b n i} {R}
      (node-lo n i) (node-hi n i i≤pn)
```

## The exact telescope

Instantiating the quotient equation at $x := \mathrm{pt}\,x_{i+1}$
and $t := x_{i}$, and using that $x_{i+1} - x_{i}$ is exactly the
mesh, each consecutive difference of $F$ *equals* the mesh times the
off-diagonal quotient value. The sum therefore telescopes with no
error whatsoever.

```agda
    Goff : Nat → Nat → ℝ
    Goff n i = G (cons (ratℝ (dyadic a b n i)) (pt (dyadic a b n (suc i))))

    Gdiag : Nat → Nat → ℝ
    Gdiag n i = G (cons (ratℝ (dyadic a b n i)) (pt (dyadic a b n i)))

    Tel
      : ∀ n
      → sumᴿ (pow2 n) (λ i → ratℝ (msh a b n) *ᴿ Goff n i)
      ≡ (F (pt b) +ᴿ (-ᴿ F (pt a)))
    Tel n =
        ap (sumᴿ (pow2 n)) (funext (λ i → sym (blockeq i)))
      ∙ sumᴿ-telescope (pow2 n) u
      ∙ ap₂ (λ s t → F (pt s) +ᴿ (-ᴿ F (pt t)))
          (dyadic-top a b n) (dyadic-bot a b n)
      where
      u : Nat → ℝ
      u i = F (pt (dyadic a b n i))

      step : ∀ i → (dyadic a b n (suc i) +ℚ (-ℚ dyadic a b n i)) ≡ msh a b n
      step i = ap (_+ℚ (-ℚ dyadic a b n i)) (node-step a b n i)
        ∙ cancel (dyadic a b n i) (msh a b n)
        where
        cancel : ∀ p h → ((p +ℚ h) +ℚ (-ℚ p)) ≡ h
        cancel p h = rational!

      blockeq
        : ∀ i → u (suc i) +ᴿ (-ᴿ u i) ≡ ratℝ (msh a b n) *ᴿ Goff n i
      blockeq i =
          sym (ap (λ w → u (suc i) +ᴿ (-ᴿ F w))
                (set-pt (dyadic a b n (suc i)) (dyadic a b n i)))
        ∙ qeq (pt (dyadic a b n (suc i))) (ratℝ (dyadic a b n i))
        ∙ ap (_*ᴿ Goff n i) diffpath
        where
        diffpath
          : (ratℝ (dyadic a b n (suc i)) +ᴿ (-ᴿ ratℝ (dyadic a b n i)))
          ≡ ratℝ (msh a b n)
        diffpath =
            ap (ratℝ (dyadic a b n (suc i)) +ᴿ_) (ratℝ-neg (dyadic a b n i))
          ∙ sym (ratℝ-+ (dyadic a b n (suc i)) (-ℚ (dyadic a b n i)))
          ∙ ap ratℝ (step i)
```

## The defect is the off-diagonal displacement

Subtracting the Riemann sum of $\partial F$ — whose $i$-th block is
the *diagonal* value of the very same $g$ — from the telescope leaves
a sum of mesh-scaled displacements of $g$ in its second argument.

```agda
    blk : Nat → Nat → ℝ
    blk n i = ratℝ (msh a b n) *ᴿ (Goff n i +ᴿ (-ᴿ Gdiag n i))

    diff-eq
      : ∀ n
      → ((F (pt b) +ᴿ (-ᴿ F (pt a))) +ᴿ (-ᴿ Riemann ∂F a b n))
      ≡ sumᴿ (pow2 n) (blk n)
    diff-eq n =
        ap (λ z → z +ᴿ (-ᴿ Riemann ∂F a b n)) (sym (Tel n))
      ∙ sumᴿ-sub (pow2 n) SG SR
      ∙ ap (sumᴿ (pow2 n)) (funext (λ i →
          sym (RI.mul-sub (ratℝ (msh a b n)) (Gdiag n i) (Goff n i))))
      where
      SG SR : Nat → ℝ
      SG i = ratℝ (msh a b n) *ᴿ Goff n i
      SR i = ratℝ (msh a b n) *ᴿ ∂F (pt (dyadic a b n i))
```

## The estimate

With a second-coordinate Lipschitz modulus $M_{2}$ for $g$ on the
box, each block is bounded by $M_{2} h_{n}^{2}$; there are $2^{n}$ of
them, and $2^{n} h_{n}^{2} = \Delta h_{n} = \Delta^{2} (1/2)^{n}$.

```agda
  private
    module WithLip (L₂ : Lip₂ G R) where
      open Lip₂ L₂

      C : Ratio
      C = M₂ *ℚ (Δ *ℚ Δ)

      0≤C : 0 ≤ C
      0≤C = *ℚ-nonnegative 0≤M₂ (*ℚ-nonnegative 0≤Δ 0≤Δ)

      blk-bd
        : ∀ n i → i Nat.< pow2 n
        → absᴿ (blk n i) ≤ᴿ ratℝ (M₂ *ℚ (msh a b n *ℚ msh a b n))
      blk-bd n i i<pn =
        ≤ᴿ-trans {absᴿ (blk n i)} {ratℝ h *ᴿ ratℝ (M₂ *ℚ h)}
          {ratℝ (M₂ *ℚ (h *ℚ h))}
          (abs-prod {ratℝ h} {Goff n i +ᴿ (-ᴿ Gdiag n i)}
            {ratℝ h} {ratℝ (M₂ *ℚ h)} h-bound lip-bound)
          (subst (λ w → (ratℝ h *ᴿ ratℝ (M₂ *ℚ h)) ≤ᴿ w)
            (ap ratℝ (hcomm h M₂)) (ratℝ-*-≤ h (M₂ *ℚ h)))
        where
        h : Ratio
        h = msh a b n

        0≤h : 0 ≤ h
        0≤h = msh-nn n

        hcomm : ∀ h' M → h' *ℚ (M *ℚ h') ≡ M *ℚ (h' *ℚ h')
        hcomm h' M = rational!

        h-bound : absᴿ (ratℝ h) ≤ᴿ ratℝ h
        h-bound = abs-ratℝ-≤ {h} {h} (neg≤self 0≤h) (≤-refl {h})

        gap : (dyadic a b n (suc i) +ℚ (-ℚ dyadic a b n i)) ≡ h
        gap = ap (_+ℚ (-ℚ dyadic a b n i)) (node-step a b n i)
          ∙ cancel (dyadic a b n i) h
          where
          cancel : ∀ p k → ((p +ℚ k) +ℚ (-ℚ p)) ≡ k
          cancel p k = rational!

        lip-bound
          : absᴿ (Goff n i +ᴿ (-ᴿ Gdiag n i)) ≤ᴿ ratℝ (M₂ *ℚ h)
        lip-bound = lip₂
          (dyadic a b n i) (dyadic a b n (suc i)) (dyadic a b n i) h
          (subst (_≤ h) (sym gap) (≤-refl {h}))
          (subst ((-ℚ h) ≤_) (sym gap) (neg≤self 0≤h))
          (node-abs n i (Nat.<-weaken i<pn))
          (node-abs n (suc i) i<pn)
          (node-abs n i (Nat.<-weaken i<pn))

      closed
        : ∀ n
        → nℚ (pow2 n) *ℚ (M₂ *ℚ (msh a b n *ℚ msh a b n))
        ≡ C *ℚ two-pow-inv n
      closed n =
          rearr1 (nℚ (pow2 n)) M₂ (msh a b n)
        ∙ ap (λ z → M₂ *ℚ (z *ℚ msh a b n)) (pow-msh a b n)
        ∙ ap (λ z → M₂ *ℚ (Δ *ℚ z)) (msh-tpi n)
        ∙ rearr2 M₂ Δ (two-pow-inv n)
        where
        rearr1 : ∀ P M h → P *ℚ (M *ℚ (h *ℚ h)) ≡ M *ℚ ((P *ℚ h) *ℚ h)
        rearr1 P M h = rational!

        rearr2 : ∀ M D s → M *ℚ (D *ℚ (D *ℚ s)) ≡ (M *ℚ (D *ℚ D)) *ℚ s
        rearr2 M D s = rational!

        msh-tpi : ∀ m → msh a b m ≡ (Δ *ℚ two-pow-inv m)
        msh-tpi m =
            sym (*ℚ-idl (msh a b m))
          ∙ ap (_*ℚ msh a b m) (sym (*ℚ-invl {nℚ (pow2 m)} ⦃ nz-pow2 m ⦄))
          ∙ sym (*ℚ-associative (two-pow-inv m) (nℚ (pow2 m)) (msh a b m))
          ∙ ap (two-pow-inv m *ℚ_) (pow-msh a b m)
          ∙ *ℚ-commutative (two-pow-inv m) Δ

      defect
        : ∀ n
        → absᴿ ((F (pt b) +ᴿ (-ᴿ F (pt a))) +ᴿ (-ᴿ Riemann ∂F a b n))
          ≤ᴿ ratℝ (C *ℚ two-pow-inv n)
      defect n = subst
        (λ z → absᴿ ((F (pt b) +ᴿ (-ᴿ F (pt a))) +ᴿ (-ᴿ Riemann ∂F a b n))
               ≤ᴿ ratℝ z)
        (closed n)
        (subst
          (λ z → absᴿ z ≤ᴿ ratℝ (nℚ (pow2 n) *ℚ (M₂ *ℚ (msh a b n *ℚ msh a b n))))
          (sym (diff-eq n))
          (sumᴿ-bounded (pow2 n) (M₂ *ℚ (msh a b n *ℚ msh a b n))
            (blk n) (blk-bd n)))

      rlim : is-Rlim ∂F a b (F (pt b) +ᴿ (-ᴿ F (pt a)))
      rlim ε 0<ε = inc (pow2-mod C ε 0<ε , goal)
        where
        goal
          : (n : Nat) → pow2-mod C ε 0<ε Nat.≤ n
          → absᴿ ((F (pt b) +ᴿ (-ᴿ F (pt a))) +ᴿ (-ᴿ Riemann ∂F a b n))
            ≤ᴿ ratℝ ε
        goal n N≤n = ≤ᴿ-trans
          {absᴿ ((F (pt b) +ᴿ (-ᴿ F (pt a))) +ᴿ (-ᴿ Riemann ∂F a b n))}
          {ratℝ (C *ℚ two-pow-inv n)} {ratℝ ε}
          (defect n)
          (ratℝ-mono
            (≤-trans (*ℚ-preserves-≤l C 0≤C (tpi-mono N≤n))
              (mod-spec C ε 0<ε 0≤C)))
```

The Lipschitz witness for the quotient is only *merely* available —
`Bd`{.Agda} is a truncated existence statement — but `is-Rlim`{.Agda}
is a proposition, so the truncation is discharged with no choice.

```agda
  telescope-is-Rlim : is-Rlim ∂F a b (F (pt b) +ᴿ (-ᴿ F (pt a)))
  telescope-is-Rlim ε 0<ε =
    ∥-∥-rec squash (λ L₂ → WithLip.rlim L₂ ε 0<ε)
      (Smooth⁺→Lip₂ G R (quot-smooth⁺ A fzero))
```

# The theorem {defines="ftc-direction-one"}

The constructed integral of the derivative and the endpoint
difference are both Riemann limits of $\partial F$, hence equal.

```agda
  FTC₁
    : (L : LipBound ∂F a b)
    → ∫L ∂F a b L a≤b ≡ (F (pt b) +ᴿ (-ᴿ F (pt a)))
  FTC₁ L = Rlim-unique ∂F a b (∫L ∂F a b L a≤b) (F (pt b) +ᴿ (-ᴿ F (pt a)))
    (∫L-converges ∂F a b L a≤b) telescope-is-Rlim
```

## The constancy principle

If the derivative vanishes identically then every Riemann sum of it
is literally $0$, so $0$ is a Riemann limit; uniqueness against the
telescope forces the endpoint difference to vanish. No Lipschitz
witness, and hence no integral, is needed for this direction.

```agda
  private
    Riemann-zero
      : (∀ q → ∂F (pt q) ≡ 0ᴿ) → ∀ n → Riemann ∂F a b n ≡ 0ᴿ
    Riemann-zero hyp n =
        ap (sumᴿ (pow2 n)) (funext λ i →
            ap (ratℝ (msh a b n) *ᴿ_) (hyp (dyadic a b n i))
          ∙ *ᴿ-zeror (ratℝ (msh a b n)))
      ∙ sumᴿ-zero (pow2 n)

    zero-is-Rlim : (∀ q → ∂F (pt q) ≡ 0ᴿ) → is-Rlim ∂F a b 0ᴿ
    zero-is-Rlim hyp ε 0<ε = inc (0 , goal)
      where
      goal
        : (n : Nat) → 0 Nat.≤ n
        → absᴿ (0ᴿ +ᴿ (-ᴿ Riemann ∂F a b n)) ≤ᴿ ratℝ ε
      goal n _ = subst (λ z → absᴿ z ≤ᴿ ratℝ ε) (sym vanish)
        (subst (_≤ᴿ ratℝ ε) (sym abs0) (ratℝ-mono {0} {ε} (<-weaken 0<ε)))
        where
        vanish : (0ᴿ +ᴿ (-ᴿ Riemann ∂F a b n)) ≡ 0ᴿ
        vanish =
            ap (λ z → 0ᴿ +ᴿ (-ᴿ z)) (Riemann-zero hyp n)
          ∙ ap (0ᴿ +ᴿ_) neg0
          ∙ +ᴿ-idr 0ᴿ

  Constancy : (∀ q → ∂-of F fzero A (pt q) ≡ 0ᴿ) → F (pt b) ≡ F (pt a)
  Constancy hyp = diff-zero→≡
    (Rlim-unique ∂F a b (F (pt b) +ᴿ (-ᴿ F (pt a))) 0ᴿ
      telescope-is-Rlim (zero-is-Rlim hyp))
```

## Independence of the Lipschitz witness

The constructed integral does not depend on which Lipschitz modulus
was used to build it: both choices produce Riemann limits of the same
integrand.

```agda
∫L-indep
  : (f : Fun 1) (a b : Ratio) (L L' : LipBound f a b) (a≤b : a ≤ b)
  → ∫L f a b L a≤b ≡ ∫L f a b L' a≤b
∫L-indep f a b L L' a≤b = Rlim-unique f a b
  (∫L f a b L a≤b) (∫L f a b L' a≤b)
  (∫L-converges f a b L a≤b) (∫L-converges f a b L' a≤b)
```

The `LipBound`{.Agda} that `FTC₁`{.Agda} consumes as data
merely exists for every bounded-smooth `F`{.Agda}: its derivative
is bounded-smooth by `∂-smooth⁺`{.Agda}, and `Smooth⁺→LipBound`{.Agda}
applies. Only the *simultaneous* choice of such witnesses across the
whole function space is withheld, exactly as in
`Convergence`{.Agda}.

```agda
FTC₁-witness-exists
  : (F : Fun 1) (A : Smooth⁺ 1 F) (a b : Ratio)
  → ∥ LipBound (∂-of F fzero A) a b ∥
FTC₁-witness-exists F A a b =
  Smooth⁺→LipBound (∂-of F fzero A) a b (∂-smooth⁺ A fzero)
```

## What is and is not proven

Proven here, with no postulates and no choice:

* the **exact** dyadic telescope `Tel`{.Agda} — the Hadamard quotient
  of a bounded-smooth $F$ summed over the partition equals
  $F(b) - F(a)$ identically, at every level $n$;
* the defect identity `diff-eq`{.Agda}, exhibiting the difference
  between that telescope and the Riemann sum of `∂-of F fzero A` as a
  sum of second-coordinate displacements of the quotient;
* the second-coordinate Lipschitz extraction `Smooth⁺→Lip₂`{.Agda}
  and the resulting geometric estimate `defect`{.Agda};
* `telescope-is-Rlim`{.Agda}: $F(b) - F(a)$ *is* the Riemann limit of
  the derivative;
* `FTC₁`{.Agda}: the constructed integral `∫L`{.Agda} of a derivative
  equals $F(b) - F(a)$;
* `Constancy`{.Agda}: a pointwise-vanishing derivative forces
  $F(b) = F(a)$ over the whole oriented box — a *finite*-time
  consequence of an infinitesimal law;
* `∫L-indep`{.Agda}: the integral is independent of the Lipschitz
  witness used to construct it.

Delimited hypotheses, all of them module or record *parameters*
rather than axioms: the orientation `a ≤ b` (as in
`Convergence`{.Agda}, the reversed box is not treated), and — for
`FTC₁`{.Agda} only — a `LipBound`{.Agda} for the derivative supplied
as **data**. That witness merely exists for every bounded-smooth
integrand, since `∂-of F fzero A` is itself bounded-smooth by
`∂-smooth⁺`{.Agda} and `Smooth⁺→LipBound`{.Agda} then applies; taking
it as an argument keeps the statement choice-free, exactly as
`∫L`{.Agda} does. `Constancy`{.Agda} needs no such witness at all.

**Not** attempted here: the *second* direction of the Fundamental
Theorem, $\frac{\d}{\d x}\int_{0}^{x} f = f$. That direction needs a
fresh total Hadamard quotient manufactured out of the integral
remainder, with hand-proved roundedness and boundedness; there is no
template for it in this development and it remains open, exactly as
`Data.Real.Smooth.Integral`{.Agda} records. Nothing beyond the
one-dimensional case is treated either: partial derivatives and
iterated integrals over boxes of higher dimension are outside this
module's scope.
