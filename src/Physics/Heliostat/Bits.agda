-- Focusing at ANY number of bits.
--
-- `Optics.euclid.reflect` and `focusing-abs` are proved over an arbitrary
-- commutative ring.  Every fixed-width hardware arithmetic (n-bit modular /
-- wraparound) IS a commutative ring — so focusing is already proved for every
-- bit-width and representation, uniformly, with no per-width re-proof.
--
-- The only thing that varies with the representation is whether the FOCAL
-- SCALAR exists: the focal relation needs 4 to be a unit.  Since 4 = 2², that
-- is exactly "2 is a unit" — true in odd/ternary bases (ℤ/3ⁿ), false in every
-- binary base (ℤ/2ⁿ).  So the concentrator has an exact focus at every ternary
-- precision and at no binary one — the same reason ternary quantisation is the
-- sweet spot for low-bit networks.
module Physics.Heliostat.Bits where

open import 1Lab.Prelude
open import Algebra.Ring.Solver
open import Algebra.Ring.Commutative
open import Data.Nat.Base using (Nat)
open import Physics.Heliostat.Optics

module bit {ℓ} (S : CRing ℓ) where
  private module S = CRing-on (S .snd)
  private module E = euclid S

  two four : ⌞ S ⌟
  two  = S.1r S.+ S.1r
  four = E.four S.1r                                    -- = 2·2·1 = (1+1)²

  -- the focusing conclusion at S, for a chosen focal scalar g:
  Concl : ⌞ S ⌟ → Type ℓ
  Concl g = ∀ a b → E.reflect E.incoming (E.parab-normal a b S.1r)
                  ≡ E.four S.1r E.·s (E.foc g E.-v E.surf a b S.1r)

  -- a focal witness: an inverse to 4 (so the exact focus exists)
  Focal : Type ℓ
  Focal = Σ[ g ∈ ⌞ S ⌟ ] (four S.* g ≡ S.1r)

  -- an inverse to 2 (the odd-base / non-binary condition)
  Two-unit : Type ℓ
  Two-unit = Σ[ h ∈ ⌞ S ⌟ ] (two S.* h ≡ S.1r)

  -- ★ the concentrator focuses whenever 4 is a unit — from the ring-generic theorem.
  focuses : (fw : Focal) → Concl (fw .fst)
  focuses (g , inv) a b = E.focusing-abs a b S.1r g inv

  -- ★ 4 is a unit ⟺ 2 is a unit (4 = 2²).  So focusing needs only 2 invertible.
  two-unit→focal : Two-unit → Focal
  two-unit→focal (h , hh) = (h S.* h) , proof where
    proof : four S.* (h S.* h) ≡ S.1r
    proof =
      four S.* (h S.* h)             ≡⟨ cring! S ⟩
      (two S.* h) S.* (two S.* h)    ≡⟨ ap₂ S._*_ hh hh ⟩
      S.1r S.* S.1r                  ≡⟨ cring! S ⟩
      S.1r                           ∎

  focal→two-unit : Focal → Two-unit
  focal→two-unit (g , gg) = (two S.* g) , proof where
    proof : two S.* (two S.* g) ≡ S.1r
    proof =
      two S.* (two S.* g)    ≡⟨ cring! S ⟩
      four S.* g             ≡⟨ gg ⟩
      S.1r                   ∎

open bit

-- ════════════════════════════════════════════════════════════════════════
-- ★ FOCUSING AT ANY NUMBER OF BITS.
-- A "bit-width family" is any assignment of a ring to each width `n : Nat`
-- (n-bit modular arithmetic).  If 2 is invertible at every width, the beam-down
-- concentrator focuses exactly at every width — one line, from the ring-generic
-- proof.  This is the whole point: no per-precision re-proof is ever needed.
-- ════════════════════════════════════════════════════════════════════════
module _ {ℓ} (bits : Nat → CRing ℓ) (two-inv : ∀ n → bit.Two-unit (bits n)) where
  -- exact focus at EVERY bit-width, given only that 2 is invertible at each.
  focus-∀bits : ∀ n → bit.Concl (bits n) (bit.two-unit→focal (bits n) (two-inv n) .fst)
  focus-∀bits n = bit.focuses (bits n) (bit.two-unit→focal (bits n) (two-inv n))
