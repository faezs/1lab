-- The base ring as a FIELD: ℚ (and, once its field structure lands, ℝ).
--
-- Over ℤ the concentrator computes (Run.agda) but has no exact focus — 4 is
-- not a unit.  Over a field, 4 = 2² IS a unit (1/4 exists), so the focal
-- relation is solved by the ACTUAL focal length f = 1/(4q), and focusing holds
-- — as an instance of `Bits.focuses`.  This is the continuous end of the same
-- spectrum whose discrete end is ternary (ℤ/3ⁿ).
module Physics.Heliostat.Field where

open import 1Lab.Prelude
open import Data.Dec
open import Algebra.Ring.Commutative
open import Data.Rational.Base
open import Physics.Heliostat.Optics
open import Physics.Heliostat.Bits

-- 2 is a unit in ℚ: nonzero ⇒ invertible (ℚ is a field).
ℚ-two-unit : bit.Two-unit ℚ-ring
ℚ-two-unit = inverseℚ (bit.two ℚ-ring) two≠0 where
  two≠0 : bit.two ℚ-ring ≠ 0
  two≠0 = decide!

-- ★ FOCUSING OVER THE RATIONALS — focal witness = 1/(4q) ∈ ℚ.
ℚ-focuses : bit.Concl ℚ-ring (bit.two-unit→focal ℚ-ring ℚ-two-unit .fst)
ℚ-focuses = bit.focuses ℚ-ring (bit.two-unit→focal ℚ-ring ℚ-two-unit)
