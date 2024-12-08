import Mathlib.RingTheory.LocalRing.Basic
namespace IsLocalRing
variable (R : Type*) [CommSemiring R] [IsLocalRing R]
def maximalIdeal : Ideal R where
  carrier := nonunits R
  zero_mem' := zero_mem_nonunits.2 <| zero_ne_one
  add_mem' {_ _} hx hy := nonunits_add hx hy
  smul_mem' _ _ := mul_mem_nonunits_right
end IsLocalRing
@[deprecated (since := "2024-11-11")] alias LocalRing.maximalIdeal := IsLocalRing.maximalIdeal