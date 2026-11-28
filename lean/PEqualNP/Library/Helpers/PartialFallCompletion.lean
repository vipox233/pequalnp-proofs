import Mathlib

namespace PEqualNP.PartialFallCompletion

variable {X J : Type} [Preorder X]

def reach (P N : X → J → Prop) (l : Nat) : X → Prop :=
  Nat.rec (motive := fun _ => X → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j) l

private theorem upward {P N : X → J → Prop} {l : Nat} {x y : X}
    (run : reach P N l x) (xy : x ≤ y) : reach P N l y := by
  cases l with
  | zero => trivial
  | succ l =>
    obtain ⟨u,v,j,old,uv,vx,p,n⟩ := run
    exact ⟨u,v,j,old,uv,vx.trans xy,p,n⟩

private theorem shorten {P N : X → J → Prop} {l t : Nat} {x : X}
    (le : l ≤ t) (run : reach P N t x) : reach P N l x := by
  induction le with
  | refl => exact run
  | step _ ih =>
    obtain ⟨u,v,j,old,uv,vx,_,_⟩ := run
    exact ih (upward old (uv.trans vx))

private theorem map_reach {P N A B : X → J → Prop}
    (pa : ∀ x j, P x j → A x j) (nb : ∀ x j, N x j → B x j)
    (l : Nat) (x : X) (run : reach P N l x) : reach A B l x := by
  induction l generalizing x with
  | zero => trivial
  | succ l ih =>
    obtain ⟨u,v,j,old,uv,vx,p,n⟩ := run
    exact ⟨u,v,j,ih _ old,uv,vx,pa _ _ p,nb _ _ n⟩

theorem length_le_of_rank {P N : X → J → Prop} {h : X → Nat}
    (mono : Monotone h)
    (rise : ∀ u v j, u ≤ v → P u j → N v j → h u < h v)
    (l : Nat) (x : X) (run : reach P N l x) : l ≤ h x := by
  induction l generalizing x with
  | zero => exact Nat.zero_le _
  | succ l ih =>
    obtain ⟨u,v,j,old,uv,vx,p,n⟩ := run
    exact (Nat.succ_le_of_lt ((ih _ old).trans_lt (rise _ _ j uv p n))).trans (mono vx)

/-- A single total completion preserves all prefix packing numbers of the partial table. -/
theorem complete (d : Nat) (P N : X → J → Prop) :
    (∀ x, ¬ reach P N (d+1) x) ↔
      ∃ (h : X → Nat) (f : X → J → Bool),
        Monotone h ∧ (∀ x, h x ≤ d) ∧
        (∀ x j, P x j → f x j = true) ∧ (∀ x j, N x j → f x j = false) ∧
        (∀ x j, f x j = true ↔ ∃ u, P u j ∧ u ≤ x ∧ h u = h x) ∧
        ∀ x l, (reach P N l x ↔ l ≤ h x) ∧
          (reach (fun a j => f a j = true) (fun a j => f a j = false) l x ↔ l ≤ h x) := by
  classical
  constructor
  · intro cap
    let levels (x : X) := (Finset.range (d+1)).filter (fun t => reach P N t x)
    have nonempty (x : X) : (levels x).Nonempty :=
      ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),True.intro⟩⟩
    let h (x : X) := (levels x).max' (nonempty x)
    have member (x : X) := Finset.max'_mem (levels x) (nonempty x)
    have hcap (x : X) : h x ≤ d :=
      Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp (member x)).1)
    have hr (x : X) : reach P N (h x) x := (Finset.mem_filter.mp (member x)).2
    have exact_h (x : X) (l : Nat) : reach P N l x ↔ l ≤ h x := by
      constructor
      · intro run
        have bound : l ≤ d := by
          by_contra! big
          exact cap x (shorten big run)
        exact Finset.le_max' _ l (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),run⟩)
      · intro le
        exact shorten le (hr x)
    have mono : Monotone h := fun a b ab => (exact_h b _).mp (upward (hr a) ab)
    have rise (u v : X) (j : J) (uv : u ≤ v) (p : P u j) (n : N v j) : h u < h v :=
      (exact_h v (h u+1)).mp ⟨u,v,j,hr u,uv,le_rfl,p,n⟩
    let f (x : X) (j : J) := decide (∃ u, P u j ∧ u ≤ x ∧ h u = h x)
    have formula (x : X) (j : J) : f x j = true ↔ ∃ u, P u j ∧ u ≤ x ∧ h u=h x := by simp [f]
    have ones (x : X) (j : J) (p : P x j) := (formula x j).mpr ⟨x,p,le_rfl,rfl⟩
    have zeros (x : X) (j : J) (n : N x j) : f x j=false := by
      by_contra! nonzero
      obtain ⟨u,p,ux,eq⟩ := (formula x j).mp (Bool.eq_true_of_not_eq_false nonzero)
      exact (rise u x j ux p n).ne eq
    have full_rise (u v : X) (j : J) (uv : u≤v) (p : f u j=true) (n : f v j=false) : h u<h v := by
      apply lt_of_le_of_ne (mono uv)
      intro same
      obtain ⟨y,pos,yu,eq⟩ := (formula u j).mp p
      exact Bool.noConfusion (n.symm.trans ((formula v j).mpr ⟨y,pos,yu.trans uv,eq.trans same⟩))
    refine ⟨h,f,mono,hcap,ones,zeros,formula,fun x l => ⟨exact_h x l,?_,?_⟩⟩
    · exact length_le_of_rank mono full_rise l x
    · intro le
      exact map_reach ones zeros l x ((exact_h x l).mpr le)
  · rintro ⟨h,f,_,bound,_,_,_,eq⟩ x run
    have := ((eq x (d+1)).1).mp run
    exact (Nat.not_succ_le_self d) (this.trans (bound x))

end PEqualNP.PartialFallCompletion
