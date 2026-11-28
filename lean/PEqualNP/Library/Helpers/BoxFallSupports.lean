import PEqualNP.Library.Helpers.BoxFallOrder
import PEqualNP.Library.Helpers.PartialFallCompletion

namespace PEqualNP.BoxFallSupports

open BoxFallOrder

variable {n m : Nat}
abbrev Word (n : Nat) := Finset (Fin n)
variable (a b c d : Fin m → Word n)

def feasible (S : Finset (Fin m)) : Prop :=
  ∃ js : List (Fin m), js.Nodup ∧ js.toFinset=S ∧ follows a b c d js Finset.univ

def enabled (S : Finset (Fin m)) (x : Word n) : Prop :=
  ∀ j ∈ S, a j ⊆ x ∧ c j ⊆ x

private theorem above {js : List (Fin m)} {x y : Word n} (xy : x⊆y)
    (tr : follows a b c d js x) : follows a b c d js y := by
  obtain ⟨one,pair⟩ := (criterion _ _ _ _ _ _).mp tr
  refine (criterion _ _ _ _ _ _).mpr ⟨?_,pair⟩
  intro j mem
  obtain ⟨ab,ad,cd,ax,cx⟩ := one j mem
  exact ⟨ab,ad,cd,ax.trans xy,cx.trans xy⟩

private theorem distinct {h : Nat} (cap : ¬pack a b c d (h+1) Finset.univ)
    {js : List (Fin m)} (tr : follows a b c d js Finset.univ) : js.Nodup := by
  obtain ⟨good,pairs⟩ := (criterion _ _ _ _ _ _).mp tr
  have forbidden (j : Fin m) (mem : j ∈ js) : ¬compatible a b c d j j := by
    intro self
    have copies (k : Nat) : (List.replicate k j).Pairwise (compatible a b c d) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [List.replicate_succ]
        exact List.pairwise_cons.mpr ⟨fun q hq => by
          have eq := List.eq_of_mem_replicate hq
          simpa [eq] using self,ih⟩
    apply cap
    apply (lengths _ _ _ _ _ _).mpr
    exact ⟨List.replicate (h+1) j,by simp,fun k hk => List.eq_of_mem_replicate hk ▸ good j mem,
      copies _⟩
  clear tr good
  induction js with
  | nil => simp
  | cons j tail ih =>
    obtain ⟨head,rest⟩ := List.pairwise_cons.mp pairs
    exact List.nodup_cons.mpr ⟨fun mem => forbidden j List.mem_cons_self (head j mem),
      ih rest (fun k hk => forbidden k (List.mem_cons_of_mem _ hk))⟩

theorem support_lengths {h : Nat} (cap : ¬pack a b c d (h+1) Finset.univ)
    (x : Word n) (l : Nat) : pack a b c d l x ↔
      ∃ S, feasible a b c d S ∧ S.card=l ∧ enabled a c S x := by
  constructor
  · intro p
    obtain ⟨js,sz,ok,pairs⟩ := (lengths _ _ _ _ _ _).mp p
    have tr := (criterion _ _ _ _ _ _).mpr ⟨ok,pairs⟩
    have top := above a b c d (Finset.subset_univ _) tr
    have nd := distinct a b c d cap top
    refine ⟨js.toFinset,⟨js,nd,rfl,top⟩,(List.toFinset_card_of_nodup nd).trans sz,?_⟩
    intro j mem
    exact (ok j (List.mem_toFinset.mp mem)).2.2.2
  · rintro ⟨_,⟨js,nd,rfl,top⟩,cnt,en⟩
    obtain ⟨ok,pairs⟩ := (criterion _ _ _ _ _ _).mp top
    refine (lengths _ _ _ _ _ _).mpr ⟨js,(List.toFinset_card_of_nodup nd).symm.trans cnt,?_,pairs⟩
    intro j mem
    obtain ⟨ab,ad,cd,_,_⟩ := ok j mem
    exact ⟨ab,ad,cd,en j (List.mem_toFinset.mpr mem)⟩

private theorem reach_iff (x : Word n) (l : Nat) :
    PartialFallCompletion.reach (fun u j => a j ⊆ u ∧ u ⊆ b j)
      (fun v j => c j ⊆ v ∧ v ⊆ d j) l x ↔ pack a b c d l x := by
  induction l generalizing x with
  | zero => rfl
  | succ l ih =>
    constructor
    · rintro ⟨u,v,j,old,uv,vx,⟨au,ub⟩,cv,vd⟩
      exact ⟨u,v,j,(ih u).mp old,uv,vx,au,ub,cv,vd⟩
    · rintro ⟨u,v,j,old,uv,vx,au,ub,cv,vd⟩
      exact ⟨u,v,j,(ih u).mpr old,uv,vx,⟨au,ub⟩,cv,vd⟩

/-- One maximum enabled set per tap can be used in place of a search over all words in its box. -/
theorem compact {k : Nat} (cap : ¬pack a b c d (k+1) Finset.univ) :
    ∃ (h : Word n → Nat) (f : Word n → Fin m → Bool),
      Monotone h ∧ (∀ x, h x ≤ k) ∧
      (∀ x j, a j ⊆ x ∧ x ⊆ b j → f x j=true) ∧
      (∀ x j, c j ⊆ x ∧ x ⊆ d j → f x j=false) ∧
      (∀ x l, l ≤ h x ↔ ∃ S, feasible a b c d S ∧ S.card=l ∧ enabled a c S x) ∧
      ∀ x j, f x j=true ↔ a j ⊆ x ∧ a j ⊆ b j ∧
        ∃ S, feasible a b c d S ∧ S.card=h x ∧ enabled a c S x ∧ enabled a c S (b j) := by
  have allcap (x : Word n) :
      ¬ PartialFallCompletion.reach (fun u j => a j ⊆ u ∧ u ⊆ b j)
        (fun v j => c j ⊆ v ∧ v ⊆ d j) (k+1) x := by
    intro r
    obtain ⟨js,sz,ok,pa⟩ := (lengths _ _ _ _ _ _).mp ((reach_iff _ _ _ _ _ _).mp r)
    have top := above a b c d (Finset.subset_univ _) ((criterion _ _ _ _ _ _).mpr ⟨ok,pa⟩)
    exact cap ((lengths _ _ _ _ _ _).mpr ⟨js,sz,(criterion _ _ _ _ _ _).mp top⟩)
  obtain ⟨h,f,mono,bound,ones,zeros,equal,rank⟩ := (PartialFallCompletion.complete k _ _).mp allcap
  have sizes (x : Word n) (l : Nat) : l ≤ h x ↔
      ∃ S, feasible a b c d S ∧ S.card=l ∧ enabled a c S x :=
    ((rank x l).1.symm.trans (reach_iff _ _ _ _ _ _)).trans (support_lengths _ _ _ _ cap _ _)
  refine ⟨h,f,mono,bound,ones,zeros,sizes,?_⟩
  intro x j
  rw [equal]
  constructor
  · rintro ⟨u,⟨au,ub⟩,ux,eq⟩
    obtain ⟨S,fe,card,en⟩ := (sizes u (h u)).mp le_rfl
    exact ⟨au.trans ux,au.trans ub,S,fe,card.trans eq,
      fun i hi => ⟨(en i hi).1.trans ux,(en i hi).2.trans ux⟩,
      fun i hi => ⟨(en i hi).1.trans ub,(en i hi).2.trans ub⟩⟩
  · rintro ⟨ax,ab,S,fe,card,ex,eb⟩
    have lower : h x ≤ h (x ⊓ b j) := (sizes _ _).mpr ⟨S,fe,card,
      fun i hi => ⟨le_inf (ex i hi).1 (eb i hi).1,le_inf (ex i hi).2 (eb i hi).2⟩⟩
    exact ⟨x ⊓ b j,⟨le_inf ax ab,inf_le_right⟩,inf_le_left,
      le_antisymm (mono inf_le_left) lower⟩

end PEqualNP.BoxFallSupports
