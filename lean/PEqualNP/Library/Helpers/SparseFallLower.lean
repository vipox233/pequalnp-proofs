import PEqualNP.Library.Helpers.MarkedInversionRank
import PEqualNP.Library.Helpers.PartialFallCompletion

namespace PEqualNP.SparseFallLower

open CircuitLowerBounds MetaComplexity PartialFallCompletion

/-- Every forced-fall packing under a physical circuit has length strictly below two to its NOT count. -/
theorem bound {n m : Nat} (P N : (Fin n → Bool) → Fin m → Prop)
    (C : Circuit) (fan : FanInTwo C) (tap : Fin m → Nat)
    (labels : ∀ x j, let w := (C.wires (List.ofFn x ++ [false,true])).getD (tap j) false
        (P x j → w=true) ∧ (N x j → w=false))
    (x : Fin n → Bool) (l : Nat) (pack : reach P N l x) :
    l < 2 ^ NotBracket.notCount C := by
  obtain ⟨h,mono,cap,order⟩ := MarkedInversionRank.circuit_rank (n:=n) C fan
  have rise (u v : Fin n → Bool) (j : Fin m) (uv : u≤v) (p : P u j) (n : N v j) : h u<h v := by
    apply lt_of_le_of_ne (mono uv)
    intro eq
    have pos := order u v uv eq (tap j) ((labels u j).1 p)
    exact Bool.noConfusion (pos.symm.trans ((labels v j).2 n))
  exact (length_le_of_rank mono rise _ _ pack).trans_lt (cap x)

end PEqualNP.SparseFallLower
