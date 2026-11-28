import PEqualNP.Library.Helpers.PartialFallCompletion

namespace PEqualNP.SparseFallDecoder

open PartialFallCompletion

/-- A nonzero threshold is witnessed at the negative endpoint of a sampled fall. -/
theorem threshold_sample {X J : Type} [Preorder X] {P N : X → J → Prop} {h : X → Nat}
    (mono : Monotone h) (exact_h : ∀ x l, reach P N l x ↔ l ≤ h x)
    (x : X) (i : Nat) (pos : 0 < i) :
    i ≤ h x ↔ ∃ v j, v ≤ x ∧ N v j ∧ i ≤ h v := by
  constructor
  · intro hx
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
    obtain ⟨u,v,j,prev,uv,vx,p,n⟩ := (exact_h x _).mpr hx
    exact ⟨v,j,vx,n,(exact_h v _).mp ⟨u,v,j,prev,uv,le_rfl,p,n⟩⟩
  · rintro ⟨v,j,vx,_,hs⟩
    exact hs.trans (mono vx)

def lowerRank (t h : Nat) : Nat := if h<t then h else h-t

theorem lower_lt {M h : Nat} (bound : h<M) (pos : 2≤M) :
    lowerRank ((M+1)/2) h < (M+1)/2 := by
  unfold lowerRank
  split <;> omega

/-- Each recursive threshold uses one AND and at most one OR after sharing the half bit. -/
theorem folded (t h i : Nat) :
    decide (i ≤ lowerRank t h) =
      (decide (t+i ≤ h) || (!decide (t≤h) && decide (i≤h))) := by
  by_cases half : h<t
  · have upper : ¬t+i≤h := by omega
    simp [lowerRank,half,upper,Nat.not_le.mpr half]
  · have upper : t ≤ h := by omega
    have reduce : i ≤ h-t ↔ t+i ≤ h := by omega
    simp [lowerRank,half,upper,reduce]

/-- Each original value selects the same-half predicate and one shared residue wire. -/
theorem unfolded (t h j : Nat) :
    decide (h=j) = (decide (lowerRank t h = lowerRank t j) &&
      (if j<t then !decide (t≤h) else decide (t≤h))) := by
  by_cases hj : j<t <;> by_cases hh : h<t
  · simp [lowerRank,hj,hh,Nat.not_le.mpr hh]
  · have hle : t≤h := by omega
    have ne : h≠j := by omega
    simp [ne,hj,hle]
  · have ne : h≠j := by omega
    simp [ne,hj,Nat.not_le.mpr hh]
  · have hle : t≤h := by omega
    have eq : h-t=j-t ↔ h=j := by omega
    simp [lowerRank,hj,hh,hle,eq]

/-- Number of non-NOT gates in one fold and its unfold, omitting out-of-range ORs. -/
def levelCost (M : Nat) :=
  let t := (M+1)/2
  (t-1) + (M-1-t) + M

theorem level_budget {M : Nat} (large : 2≤M) :
    levelCost M + 4*((M+1)/2-1) ≤ 4*(M-1) := by
  dsimp [levelCost]
  omega

/-- The complete recurrence uses at most r inversions and 4(M-1) binary gates. -/
def budgets : Nat → Nat → Nat × Nat
  | 0, _ => (0,0)
  | r+1, M => if M≤1 then (0,0) else
      let child := budgets r ((M+1)/2)
      (child.1+1,child.2+levelCost M)

theorem budget_bound (r M : Nat) (fits : M≤2^r) :
    (budgets r M).1≤r ∧ (budgets r M).2≤4*(M-1) := by
  induction r generalizing M with
  | zero => simp [budgets]
  | succ r ih =>
    by_cases small : M≤1
    · simp [budgets,small]
    · have lower : 2≤M := by omega
      rw [pow_succ] at fits
      have half : (M+1)/2≤2^r := by omega
      obtain ⟨a,b⟩ := ih _ half
      have budget := level_budget lower
      simp only [budgets,if_neg small]
      omega

end PEqualNP.SparseFallDecoder
