import WeightedNetKAT.WNKA

open OmegaCompletePartialOrder
open scoped RightActions

namespace WeightedNetKAT

variable {F : Type} [Fintype F] [Listed F] [DecidableEq F]
variable {N : Type} [Listed N] [DecidableEq N]
variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

namespace rReachability

variable {Q 𝒮 : Type}
variable [Listed Q] [Fintype Q] [DecidableEq Q]
variable [Semiring 𝒮]
variable (𝒜 : WNKA F N 𝒮 Q)
variable (ℰ : EWNKA F N 𝒮 Q)
variable [Star 𝒮]



end rReachability

end WeightedNetKAT
