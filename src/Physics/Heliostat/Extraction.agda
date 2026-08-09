-- Verified extraction: the runnable reflection formula that
-- `scratchpad/HelioUnified.agda` compiles and runs (over a plain `Num`
-- interface, at Float and at dual numbers for AD) is PROVED here to equal
-- the focusing-proved `Physics.Heliostat.Optics.euclid.reflect`, and hence
-- to inherit its focusing theorem.  This closes the transcription gap: the
-- extracted code is certified to compute the proved term.
module Physics.Heliostat.Extraction where

open import Cat.Prelude
open import Algebra.Ring.Solver
open import Algebra.Ring.Commutative
open import Physics.Heliostat.Optics

-- The plain numeric interface HelioUnified runs over (no ring laws — so it
-- instantiates at Float, and at the dual-number ring for forward-mode AD).
record Num {ℓ} (A : Type ℓ) : Type ℓ where
  field
    add mul : A → A → A
    neg     : A → A
    zer one : A

-- The extraction reflection over ANY Num — verbatim HelioUnified's `reflect`,
-- with the doubling written as x + x (as the compiled Float/Dual code computes).
module gen {ℓ} {A : Type ℓ} (N : Num A) where
  open Num N
  dotG : (A × A × A) → (A × A × A) → A
  dotG (x , y , z) (x' , y' , z') = add (add (mul x x') (mul y y')) (mul z z')
  svG : A → (A × A × A) → (A × A × A)
  svG s (x , y , z) = mul s x , mul s y , mul s z
  subG : (A × A × A) → (A × A × A) → (A × A × A)
  subG (x , y , z) (x' , y' , z') = add x (neg x') , add y (neg y') , add z (neg z')
  reflectG : (A × A × A) → (A × A × A) → (A × A × A)
  reflectG d n = subG (svG (dotG n n) d) (svG (add (dotG d n) (dotG d n)) n)

open gen

module _ {ℓ} (S : CRing ℓ) where
  private
    module S = CRing-on (S .snd)
    module E = euclid S

  -- the numeric interface realised by the ring's own operations
  ringNum : Num ⌞ S ⌟
  ringNum = record { add = S._+_ ; mul = S._*_ ; neg = S.-_ ; zer = S.0r ; one = S.1r }

  -- ★ the extracted formula computes exactly the proved reflection.
  -- Only the doubling differs (x+x vs (1+1)·x); a one-line ring identity.
  reflect-agrees : ∀ d n → reflectG ringNum d n ≡ E.reflect d n
  reflect-agrees d n =
    ap (λ s → subG ringNum (svG ringNum (dotG ringNum n n) d) (svG ringNum s n)) double
    where
      double : S._+_ (dotG ringNum d n) (dotG ringNum d n)
             ≡ S._*_ (S._+_ S.1r S.1r) (dotG ringNum d n)
      double = cring! S

  -- ★ therefore the extracted formula inherits the FOCUSING theorem:
  -- the axial ray, reflected off the paraboloid normal, passes through the focus.
  focusing-extracted
    : ∀ a b c g → E.four c S.* g ≡ S.1r
    → reflectG ringNum E.incoming (E.parab-normal a b c)
    ≡ E.four c E.·s (E.foc g E.-v E.surf a b c)
  focusing-extracted a b c g focal =
      reflect-agrees E.incoming (E.parab-normal a b c)
    ∙ E.focusing-abs a b c g focal
