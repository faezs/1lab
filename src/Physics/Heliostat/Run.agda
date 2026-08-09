-- Running the ACTUAL proved reflection.  `Physics.Heliostat.Optics.euclid.reflect`
-- is defined over any commutative ring; instantiated at the (inductive, hence
-- computing) integers `ℤ-comm`, it REDUCES on concrete inputs.  So the proved
-- definition — not a re-authored slice — executes here, by refl, in mikan.
module Physics.Heliostat.Run where

open import 1Lab.Prelude
open import Data.Int.Base
open import Algebra.Ring.Commutative
open import Physics.Heliostat.Optics

private module Z = euclid ℤ-comm

ray normal : Z.Vec3
ray    = pos 0 , pos 0 , negsuc 0      -- the incoming ray (0, 0, -1)
normal = pos 1 , pos 0 , pos 2         -- a mirror normal  (1, 0,  2)

-- ★ the proved euclid.reflect, RUN on integers by computation:
--   ⟨n,n⟩=5, ⟨d,n⟩=-2, so reflect = 5·(0,0,-1) − 2(-2)·(1,0,2) = (4, 0, 3).
run-reflect : Z.reflect ray normal ≡ (pos 4 , pos 0 , pos 3)
run-reflect = refl

-- a second point, to show it is really computing and not a fluke:
--   reflect (0,0,-1) off (2,1,1): ⟨n,n⟩=6, ⟨d,n⟩=-1, → 6·(0,0,-1) − 2(-1)·(2,1,1)
--                               = (0,0,-6) + (4,2,2) = (4, 2, -4).
run-reflect₂ : Z.reflect (pos 0 , pos 0 , negsuc 0) (pos 2 , pos 1 , pos 1)
             ≡ (pos 4 , pos 2 , negsuc 3)
run-reflect₂ = refl
