import Mathlib

open MulAction Subgroup Pointwise MulAut


variable {G : Type*} [Group G] (x : G) (H : Subgroup G)

#check conj x • (centralizer {x})

-- and

#check conj x • H

-- why can `conj x • H` not be promoted to its own type?

def foonction {G : Type*} [Group G] (x : G) (H : Subgroup G): ↥(conj x • H) →* H := by sorry
