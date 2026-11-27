import Mathlib
import PEqualNP.Defs

open scoped Fin.NatCast
namespace PEqualNP.Outside.L_meta_29773_aux
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
lemma rank_extend (A B U W : Submodule K V) :
    Module.finrank K ↥((A ⊔ U) ⊓ (B ⊔ W)) ≤ Module.finrank K ↥(A ⊓ B) +
    Module.finrank K U + Module.finrank K W := by
  have h₁ := (A ⊔ U).finrank_sup_add_finrank_inf_eq (B ⊔ W)
  have h₂ := A.finrank_sup_add_finrank_inf_eq B
  have h₃ := A.finrank_sup_add_finrank_inf_eq U
  have h₄ := B.finrank_sup_add_finrank_inf_eq W
  have h₅ := Submodule.finrank_mono (sup_le_sup (le_sup_left : A ≤ A ⊔ U) (le_sup_left : B ≤ B ⊔ W))
  omega
def ranks (C : ℕ → Submodule K V) : ℕ → Submodule K V
  | 0 => ⊥
  | n+1 => ranks C n ⊔ C n
lemma ranks_mem (C : ℕ → Submodule K V) {i n} (hi : i < n) : C i ≤ ranks C n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n
    · subst i; exact le_sup_right
    · exact le_trans (ih (by omega)) le_sup_left
lemma ranks_bound (C : ℕ → Submodule K V) (n h) (hb : ∀ i < n, Module.finrank K (C i) ≤ h) :
    Module.finrank K (ranks C n) ≤ n*h := by
  induction n with
  | zero => rw [Nat.zero_mul]; exact (finrank_bot K V).le
  | succ n ih =>
    have ha := ih (fun i hi => hb i (by omega))
    have hh := hb n (by omega)
    have he := (ranks C n).finrank_sup_add_finrank_inf_eq (C n)
    simp only [ranks, Nat.succ_mul]
    exact (Nat.le_add_right _ _).trans (he.le.trans (Nat.add_le_add ha hh))

variable {k : Nat} [NeZero k]
def sided (p : Bool) (c : Nat) (j : Fin k) : Prop := if p then j.val < c else c ≤ j.val
def edge (p : Bool) (c : Nat) : Fin k := if p then ↑c else 0
lemma forward_step {p : Bool} {c : Nat} {j : Fin k} (hi : sided p c j)
    (ho : ¬ sided p c (j+1)) : j+1 = edge p c := by
  have hk := NeZero.pos k
  have hj := j.isLt
  have hone : (1 : Fin k).val = 1 % k := rfl
  by_cases h : k = 1
  · subst k; exact Subsingleton.elim _ _
  rw [Nat.mod_eq_of_lt (by omega)] at hone
  have hm : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  cases p <;> simp [sided, Fin.val_add_eq_ite, hm, hone] at hi ho
  all_goals
    apply Fin.ext
    simp [edge, Fin.val_add_eq_ite, hm, hone, Fin.val_natCast]
    (try split_ifs) <;> (try split_ifs at ho) <;> first | omega | rw [Nat.mod_eq_of_lt (by omega)]; omega
lemma backward_step {p : Bool} {c : Nat} {j : Fin k} (hi : sided p c j)
    (ho : ¬ sided p c (j-1)) : j-1 = edge (!p) c - 1 := by
  suffices j = edge (!p) c by rw [this]
  have h₁ : sided (!p) c (j-1) := by cases p <;> simp_all [sided]
  have h₂ : ¬ sided (!p) c ((j-1)+1) := by cases p <;> simp_all [sided]
  simpa using forward_step h₁ h₂
lemma walk_forward {p c} {j : Fin k} (hi : sided p c j) (d : Nat) :
    sided p c (j+(↑d : Fin k)) ∨ ∃ u < d, j+(↑d : Fin k) = edge p c + (↑u : Fin k) := by
  induction d with
  | zero => simp [hi]
  | succ d ih =>
    rw [Nat.cast_succ, ← add_assoc]
    by_cases hh : sided p c (j+(↑d : Fin k)+1)
    · exact Or.inl hh
    right
    rcases ih with hd | ⟨u, hu, he⟩
    · exact ⟨0, by omega, by simpa using forward_step hd hh⟩
    · exact ⟨u+1, by omega, by rw [he, Nat.cast_succ, add_assoc]⟩
lemma walk_backward {p c} {j : Fin k} (hi : sided p c j) (d : Nat) :
    sided p c (j-(↑d : Fin k)) ∨ ∃ u < d, j-(↑d : Fin k) = edge (!p) c - ((↑u : Fin k)+1) := by
  induction d with
  | zero => simp [hi]
  | succ d ih =>
    rw [Nat.cast_succ, ← sub_sub]
    by_cases hh : sided p c (j-(↑d : Fin k)-1)
    · exact Or.inl hh
    right
    rcases ih with hd | ⟨u, hu, he⟩
    · exact ⟨0, by omega, by simpa using backward_step hd hh⟩
    · exact ⟨u+1, by omega, by rw [he, Nat.cast_succ, sub_sub]⟩

variable {α : Type*}
def valid (B : ℕ → Set α) (v : ℕ) : Prop :=
  (∃ x, B v = {x}) ∨ ∃ a < v, ∃ b < v, Disjoint (B a) (B b) ∧ B v = B a ∪ B b
def built (P : Set α → Prop) (S : Set α) (m : Nat) : Prop :=
  ∃ B : ℕ → Set α, (∃ v < 2*m-1, B v = S) ∧ ∀ v < 2*m-1, P (B v) ∧ valid B v
lemma build_one {P : Set α → Prop} {x : α} (hp : P {x}) : built P {x} 1 := by
  exact ⟨fun _ => {x}, ⟨0, by decide, rfl⟩, fun _ _ => ⟨hp, Or.inl ⟨x,rfl⟩⟩⟩
lemma build_join {P : Set α → Prop} {S T : Set α} {m n : Nat}
    (hs : built P S m) (ht : built P T n) (hd : Disjoint S T) (hp : P (S ∪ T)) :
    built P (S ∪ T) (m+n) := by
  rcases hs with ⟨A, ⟨a, ha, ea⟩, hA⟩
  rcases ht with ⟨B, ⟨b, hb, eb⟩, hB⟩
  let u := 2*m-1
  let w := 2*n-1
  change a < u at ha
  change b < w at hb
  have root : u+w+1 = 2*(m+n)-1 := by dsimp [u,w] at *; omega
  let C := fun i => if i < u then A i else if i < u+w then B (i-u) else S ∪ T
  have eA (i) (h : i < u) : C i = A i := if_pos h
  have eB (i) (h : i < w) : C (u+i) = B i := by simp [C, h]
  have eC : C (u+w) = S ∪ T := by simp [C]
  refine ⟨C, ⟨u+w, by omega, eC⟩, ?_⟩
  intro v hv
  by_cases h : v < u
  · obtain ⟨hP, hx | ⟨i,hi,j,hj,hD,hU⟩⟩ := hA v h
    · exact ⟨eA v h ▸ hP, Or.inl ((eA v h) ▸ hx)⟩
    refine ⟨eA v h ▸ hP, Or.inr ⟨i,hi,j,hj,?_,?_⟩⟩
    · simpa only [eA i (by omega), eA j (by omega)] using hD
    · simpa only [eA i (by omega), eA j (by omega), eA v h] using hU
  by_cases h' : v < u+w
  · obtain ⟨i, rfl⟩ : ∃ i, v = u+i := ⟨v-u, by omega⟩
    have hi : i < w := by omega
    obtain ⟨hP, hx | ⟨j,hj,l,hl,hD,hU⟩⟩ := hB i hi
    · exact ⟨eB i hi ▸ hP, Or.inl ((eB i hi) ▸ hx)⟩
    refine ⟨eB i hi ▸ hP, Or.inr ⟨u+j,by omega,u+l,by omega,?_,?_⟩⟩
    · simpa only [eB j (by omega), eB l (by omega)] using hD
    · simpa only [eB j (by omega), eB l (by omega), eB i hi] using hU
  have ev : v = u+w := by omega
  subst v
  refine ⟨eC ▸ hp, Or.inr ⟨a,by omega,u+b,by omega,?_,?_⟩⟩
  · simpa only [eA a ha, eB b hb, ea, eb] using hd
  · rw [eC, eA a ha, eB b hb, ea, eb]

lemma build_groups {k m : Nat} (hk : 0 < k) (hm : 0 < m) (key : α → Fin k) (slot : α → ℕ)
    (bound : ∀ i, slot i < m) (uniqueCell : ∀ j t, t < m →
      ∃ i, ∀ x, (key x = j ∧ slot x = t) ↔ x = i)
    (P : Set α → Prop)
    (hCell : ∀ j a b, a < b → b ≤ m → P {x | key x = j ∧ a ≤ slot x ∧ slot x < b})
    (hPre : ∀ c ≤ k, P {x | (key x).val < c}) :
    built P Set.univ (m*k) := by
  have leaf (j : Fin k) (t : ℕ) (ht : t < m) :
      built P {x | key x = j ∧ slot x = t} 1 := by
    obtain ⟨i, hi⟩ := uniqueCell j t ht
    have e : {x | key x = j ∧ slot x = t} = ({i} : Set α) := Set.ext hi
    rw [e]
    apply build_one
    have h := hCell j t (t+1) (by omega) (by omega)
    convert h using 1
    rw [← e]
    ext x
    simp only [Set.mem_setOf_eq]
    omega
  have col (j : Fin k) (b : Nat) (hb : 0 < b) (hb' : b ≤ m) :
      built P {x | key x = j ∧ slot x < b} b := by
    induction b with
    | zero => omega
    | succ b ih =>
      by_cases h : b = 0
      · subst b
        simpa using leaf j 0 hm
      have h₁ := ih (by omega) (by omega)
      have h₂ := leaf j b (by omega)
      have e : {x | key x = j ∧ slot x < b} ∪ {x | key x = j ∧ slot x = b} =
          {x | key x = j ∧ slot x < b+1} := by ext x; simp; omega
      rw [← e]
      apply build_join h₁ h₂
      · exact Set.disjoint_left.mpr (by intro x hx hx'; exact (hx.2.ne hx'.2))
      · rw [e]; simpa using hCell j 0 (b+1) (by omega) hb'
  have pre (c : Nat) (hc : 0 < c) (hc' : c ≤ k) :
      built P {x | (key x).val < c} (m*c) := by
    induction c with
    | zero => omega
    | succ c ih =>
      let j : Fin k := ⟨c, by omega⟩
      have h₂ := col j m hm le_rfl
      simp only [bound, and_true] at h₂
      by_cases h : c = 0
      · subst c
        simpa [j, Nat.lt_one_iff, Fin.ext_iff] using h₂
      have h₁ := ih (by omega) (by omega)
      have e : {x | (key x).val < c} ∪ {x | key x = j} = {x | (key x).val < c+1} := by
        ext x; simp [j, Fin.ext_iff]; omega
      rw [← e, Nat.mul_succ]
      apply build_join h₁ h₂
      · exact Set.disjoint_left.mpr (by intro x hx hx'; change key x = j at hx'; change (key x).val < c at hx; rw [hx'] at hx; exact (lt_irrefl c hx))
      · rw [e]; exact hPre _ hc'
  simpa using pre k hk le_rfl

end PEqualNP.Outside.L_meta_29773_aux
open PEqualNP.Outside.L_meta_29773_aux
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.L_meta_29773 : (∀ (k r q : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let X := W × (Bool → Fin (r+1) → W)
  let G := Bool × Fin r × Fin k
  let I := Fin k ⊕ G
  let N := (2*r+3)*k
  let ix := fun s : Nat => (⟨s % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : Nat) (v : W) (j : Fin k) => v (ix (j.val+k-s % k))
  let start := fun (b : Bool) => if b then 3 else 1
  let feed := fun (b : Bool) (t : Nat) => if b then 3*(t+1)+1 else 2*t
  let mix := fun (b : Bool) (v : W) (j : Fin k) =>
    let d := if b then 2 else 1
    v j + v (ix (j.val+d)) + v (ix (j.val+k-d % k))
  let pair := fun (v z : X) => dotProduct v.1 z.1 +
    ∑ s : Fin (r+1), (dotProduct (v.2 false s) (z.2 false s) + dotProduct (v.2 true s) (z.2 true s))
  let form : I → Fin 3 → X → F := Sum.elim (fun j _ z => z.1 j) (fun g e z =>
    let b := g.1
    let t := g.2.1
    let j := g.2.2
    let y := mix b (z.2 b t.castSucc)
    if e.val = 0 then y (ix (j.val+1)) else if e.val = 1 then y (ix (j.val+2))
    else z.2 b t.succ j + y j + rot (feed b t.val) z.1 j)
  let leafCount := (2*r+1)*k
  let n := 2*leafCount-1
  let Bag := Fin n → I → Bool
  let arc := fun (j a : Fin k) (len : Fin (k+1)) =>
    (j.val+k-a.val) % k < len.val
  let geometric := fun (p : I → Bool) =>
    ∃ (rootSite : Fin k) (rootLen : Fin (k+1)) (slope origin : Bool → Fin k)
      (width : Bool → Fin (k+1)) (lo hi : Bool → Fin (r+1)), ∀ i : I,
        p i = Sum.elim (fun coord => decide (arc coord rootSite rootLen)) (fun g : G =>
          let b := g.1
          let time := g.2.1.val
          decide ((lo b).val ≤ time ∧ time < (hi b).val ∧
            arc g.2.2 (ix ((origin b).val+(slope b).val*time)) (width b))) i
  let layout := fun (bag : Bag) =>
    (∃ top : Fin n, ∀ i, bag top i = true) ∧ ∀ v : Fin n, geometric (bag v) ∧
      ((∃ one : I, ∀ i, bag v i = decide (i = one)) ∨
        ∃ l h : Fin n, l < v ∧ h < v ∧ (∀ i, bag l i = true → bag h i = false) ∧
          ∀ i, bag v i = (bag l i || bag h i))
  let dir := fun (obs : Fin q → X) =>
    {z : X // (∀ b, z.2 b 0 = rot (start b) z.1) ∧ ∀ i, pair (obs i) z = 0}
  let fits := fun (obs : Fin q → X) (bag : Bag) (cap : Nat) =>
    let D := dir obs
    let span := fun (p : I → Bool) => Submodule.span F
      {f : D → F | ∃ (j : I) (e : Fin 3), p j = true ∧ f = fun z : D => form j e z.val}
    layout bag ∧ ∀ v : Fin n, Module.finrank F
      ((span (bag v) ⊓ span (fun j => !(bag v j))) : Submodule F (D → F)) ≤ cap
  ∀ (obs : Fin q → X) (h s : Nat),
    let D := dir obs
    let stripe := fun (j : Fin k) (f : D → F) =>
      (f = fun z : D => z.val.1 j) ∨ ∃ (b : Bool) (t : Fin r),
        f = fun z : D => z.val.2 b t.succ (ix (j.val+feed b t.val))
    let cols := fun (p : Fin k → Bool) =>
      Submodule.span F {f : D → F | ∃ j : Fin k, p j = true ∧ stripe j f}
    (∀ j : Fin k, Module.finrank F (cols (fun i => decide (i = j))) ≤ h) →
    (∀ cut : Fin (k+1), Module.finrank F
      ((cols (fun i => decide (i.val < cut.val)) ⊓ cols (fun i => decide (cut.val ≤ i.val))) :
        Submodule F (D → F)) ≤ s) →
    ∃ bag : Bag, fits obs bag (s+18*h)) := by
  classical
  intro k r q hk F W X G I N ix rot start feed mix pair form leafCount n Bag arc geometric layout dir fits obs h s D stripe cols hh hs
  letI : NeZero k := ⟨hk.ne'⟩
  let key : I → Fin k := Sum.elim id (fun g : G => g.2.2 - (feed g.1 g.2.1.val : Fin k))
  let base := fun b : Bool => if b then r+1 else 1
  let slot : I → ℕ := Sum.elim (fun _ => 0) (fun g : G => base g.1 + g.2.1.val)
  have keyL (j : Fin k) : key (.inl j) = j := rfl
  have keyR (b : Bool) (t : Fin r) (j : Fin k) :
      key (.inr (b,t,j)) = j - (feed b t.val : Fin k) := rfl
  have sbound (i : I) : slot i < 2*r+1 := by
    rcases i with j | ⟨b,t,j⟩
    · dsimp [slot]; omega
    · cases b <;> dsimp [slot,base] <;> omega
  have uniqueCell (j : Fin k) (a : ℕ) (ha : a < 2*r+1) :
      ∃ i : I, ∀ x, (key x = j ∧ slot x = a) ↔ x = i := by
    by_cases h0 : a = 0
    · subst a
      refine ⟨.inl j, ?_⟩
      rintro (x | ⟨b,t,x⟩)
      · simp [key,slot]; exact ⟨congrArg Sum.inl, Sum.inl.inj⟩
      · cases b <;> simp [slot,base] <;> omega
    let b : Bool := decide (r < a)
    let t : Fin r := ⟨a-base b, by dsimp [b,base]; split <;> rename_i e <;> simp_all <;> omega⟩
    have ht : base b + t.val = a := by dsimp [b,base,t]; split <;> rename_i e <;> simp_all <;> omega
    refine ⟨.inr (b,t,j+(feed b t.val : Fin k)), ?_⟩
    rintro (x | ⟨b',t',x⟩)
    · simp [slot, Ne.symm h0]
    change (x - _ = j ∧ base b' + t'.val = a) ↔ _
    constructor
    · rintro ⟨he,ha'⟩
      have eb : b' = b := by cases b' <;> cases eb' : b <;> simp_all [base] <;> omega
      subst b'
      have et : t' = t := Fin.ext (by omega)
      subst t'
      rw [sub_eq_iff_eq_add] at he
      rw [he]
    · intro he
      cases he
      exact ⟨add_sub_cancel_right ..,ht⟩
  have ixcast (i : Nat) : ix i = (i : Fin k) := rfl
  have castVal (j : Fin k) : (j.val : Fin k) = j := by ext; simp
  have subval (j a : Fin k) : (j.val+k-a.val)%k = (j-a).val := by
    rw [Fin.val_sub]; congr 1; have := a.isLt; omega
  have arcEq (j a : Fin k) (w : Fin (k+1)) : arc j a w ↔ (j-a).val < w.val := by
    change (j.val+k-a.val)%k < _ ↔ _; rw [subval]
  have arcone (j a : Fin k) : (j-a).val < 1 ↔ j = a := by
    rw [Nat.lt_one_iff]; exact (Fin.ext_iff (a := j-a) (b := 0)).symm.trans sub_eq_zero
  have feedlin (b : Bool) (t : ℕ) :
      feed b t = feed b 0 + (if b then 3 else 2)*t := by cases b <;> dsimp [feed] <;> omega
  have castMul (u v : Nat) : ((u*v : Nat) : Fin k) = (u : Fin k)*(v : Fin k) := by
    apply Fin.ext; simp [Fin.val_mul]
  have geo (a : Fin k) (w : Fin (k+1)) (lo hi : Nat) :
      geometric (fun i => decide ((key i-a).val < w.val ∧ lo ≤ slot i ∧ slot i < hi)) := by
    let trunc := fun (b : Bool) (u : ℕ) => (⟨min r (u-base b), by omega⟩ : Fin (r+1))
    refine ⟨a, if lo = 0 ∧ 0 < hi then w else 0,
      fun b => ((if b then 3 else 2 : Nat) : Fin k), fun b => a + (feed b 0 : Fin k),
      fun _ => w, fun b => trunc b lo, fun b => trunc b hi, ?_⟩
    rintro (j | ⟨b,t,j⟩)
    · simp only [Sum.elim_inl, decide_eq_decide]
      change ((j-a).val < w.val ∧ lo ≤ 0 ∧ 0 < hi) ↔ _
      simp only [arcEq]
      split_ifs <;> (try simp only [Fin.val_zero]) <;> omega
    simp only [Sum.elim_inr, decide_eq_decide]
    change ((j - (feed b t.val : Fin k) - a).val < w.val ∧ lo ≤ base b+t.val ∧ base b+t.val < hi) ↔ _
    rw [arcEq, ixcast, Nat.cast_add, castMul, castVal, castVal]
    rw [feedlin b t.val, Nat.cast_add, castMul]
    have eqs : j - ((feed b 0 : Fin k) + ((if b then 3 else 2 : Nat) : Fin k) * (t.val : Fin k)) - a =
        j - (a + (feed b 0 : Fin k) + ((if b then 3 else 2 : Nat) : Fin k) * (t.val : Fin k)) := by abel
    rw [eqs]
    simp only [and_true, decide_eq_decide, trunc]
    omega
  let C := fun j : Fin k => cols (fun i => decide (i = j))
  have stripeMem (j : Fin k) (f : D → F) (hf : stripe j f) : f ∈ C j :=
    Submodule.subset_span ⟨j, by simp, hf⟩
  have plusIx (j : Fin k) (v : Nat) : ix (j.val+v) = j+(v : Fin k) := by
    rw [ixcast,Nat.cast_add,castVal]
  have minusIx (j : Fin k) (v : Nat) : ix (j.val+k-v%k) = j-(v : Fin k) := by
    apply Fin.ext
    exact subval j (v : Fin k)
  let prev := fun (b : Bool) (t : Nat) => if t = 0 then start b else feed b (t-1)
  let pad := fun (b : Bool) (t : Nat) => if t = 0 then (if b then 3 else 1) else (if b then 5 else 4)
  let dist := fun (b : Bool) => if b then 2 else 1
  have balance (b : Bool) (t : Nat) : (feed b t : Fin k) + 2 = (prev b t : Fin k) + (pad b t : Fin k) := by
    have e : feed b t + 2 = prev b t + pad b t := by
      cases b <;> by_cases ht : t = 0 <;> simp [feed,prev,start,pad,ht] <;> omega
    simpa only [Nat.cast_add,Nat.cast_ofNat] using congrArg (fun u : Nat => (u : Fin k)) e
  have pads (b : Bool) (t : Nat) : dist b ≤ pad b t ∧ pad b t + dist b ≤ 7 := by
    cases b <;> by_cases ht : t = 0 <;> simp [dist,pad,ht]
  have raw (x : Fin k) : (fun z : D => z.val.1 x) ∈ C x := stripeMem _ _ (Or.inl rfl)
  have newRead (b : Bool) (t : Fin r) (x : Fin k) :
      (fun z : D => z.val.2 b t.succ x) ∈ C (x-(feed b t.val : Fin k)) := by
    apply stripeMem
    refine Or.inr ⟨b,t,?_⟩
    rw [plusIx,sub_add_cancel]
  have oldRead (b : Bool) (t : Fin r) (x : Fin k) :
      (fun z : D => z.val.2 b t.castSucc x) ∈ C (x-(prev b t.val : Fin k)) := by
    rcases t with ⟨_ | u, ht⟩
    · have eqf : (fun z : D => z.val.2 b 0 x) = fun z : D => z.val.1 (x-(start b : Fin k)) := by
        funext z
        rw [z.property.1 b]
        exact congrArg z.val.1 (minusIx x (start b))
      change (fun z : D => z.val.2 b 0 x) ∈ C (x-(start b : Fin k))
      rw [eqf]; exact raw _
    · exact newRead b ⟨u,by omega⟩ x
  let near := fun (j x : Fin k) => ∃ v : Nat, v ≤ 9 ∧ x = j + (v : Fin k) - 2
  have near_refl (j : Fin k) : near j j := ⟨2, by decide, by simp⟩
  have localForm (i : I) (e : Fin 3) (M : Submodule F (D → F))
      (hm : ∀ x, near (key i) x → C x ≤ M) : (fun z : D => form i e z.val) ∈ M := by
    rcases i with j | ⟨b,t,j⟩
    · exact hm j (near_refl j) (raw j)
    let g := j-(feed b t.val : Fin k)
    change ∀ x, near g x → C x ≤ M at hm
    have hb := balance b t.val
    have hp := pads b t.val
    have old (x : Fin k) (v : Nat) (hv : v ≤ 9)
        (he : x = j + (v : Fin k) - (pad b t.val : Fin k)) :
        (fun z : D => z.val.2 b t.castSucc x) ∈ M := by
      apply hm _ _ (oldRead b t x)
      refine ⟨v,hv,?_⟩
      rw [he]; dsimp [g]; linear_combination (norm := abel) hb
    have mixed (v : Nat) (hv : v ≤ 2) :
        (fun z : D => mix b (z.val.2 b t.castSucc) (j+(v : Fin k))) ∈ M := by
      let p := pad b t.val
      let d := dist b
      change dist b ≤ p ∧ p + d ≤ 7 at hp
      have h₀ := old (j+(v : Fin k)) (v+p) (by omega) (by rw [Nat.cast_add]; dsimp [p]; abel)
      have h₁ := old (j+(v : Fin k)+(d : Fin k)) (v+p+d) (by omega) (by push_cast; dsimp [p]; abel)
      have hd : d ≤ v+p := by dsimp [d]; omega
      have h₂ := old (j+(v : Fin k)-(d : Fin k)) (v+p-d) (by omega)
        (by
          have eqn := congrArg (fun u : Nat => (u : Fin k)) (Nat.sub_add_cancel hd)
          simp only [Nat.cast_add] at eqn
          change j + (v : Fin k) - (d : Fin k) = j + ((v+p-d : Nat) : Fin k) - (p : Fin k)
          linear_combination (norm := abel) -eqn)
      change (fun z : D => z.val.2 b t.castSucc (j+(v : Fin k)) +
        z.val.2 b t.castSucc (ix ((j+(v : Fin k)).val+d)) +
        z.val.2 b t.castSucc (ix ((j+(v : Fin k)).val+k-d%k))) ∈ M
      rw [plusIx,minusIx]
      exact M.add_mem (M.add_mem h₀ h₁) h₂
    have h₀ : (fun z : D => mix b (z.val.2 b t.castSucc) j) ∈ M := by simpa using mixed 0 (by decide)
    have hnew := hm g (near_refl g) (newRead b t j)
    have hraw := hm g (near_refl g) (raw g)
    dsimp only [form,Sum.elim_inr]
    split_ifs
    · rw [plusIx]; exact mixed 1 (by decide)
    · rw [plusIx]; exact mixed 2 (by decide)
    · change (fun z : D => z.val.2 b t.succ j + mix b (z.val.2 b t.castSucc) j +
          z.val.1 (ix (j.val+k-feed b t.val % k))) ∈ M
      rw [minusIx]; exact M.add_mem (M.add_mem hnew h₀) hraw
  let span := fun (p : I → Bool) => Submodule.span F
    {f : D → F | ∃ (j : I) (e : Fin 3), p j = true ∧ f = fun z : D => form j e z.val}
  let flag := fun (S : Set I) (i : I) => decide (i ∈ S)
  let good := fun S : Set I => geometric (flag S) ∧
    Module.finrank F ↥(span (flag S) ⊓ span (fun i => !(flag S i))) ≤ s+18*h
  have cover (p : I → Bool) (M : Submodule F (D → F))
      (incl : ∀ i, p i = true → ∀ x, near (key i) x → C x ≤ M) : span p ≤ M := by
    apply Submodule.span_le.mpr
    rintro f ⟨i,e,hi,rfl⟩
    exact localForm i e M (incl i hi)
  letI : Fintype D := Fintype.ofFinite D
  have goodCell (j : Fin k) (a b : ℕ) (_ : a < b) (_ : b ≤ 2*r+1) :
      good {x | key x = j ∧ a ≤ slot x ∧ slot x < b} := by
    constructor
    · convert geo j ⟨1,by omega⟩ a b using 1
      funext x
      simp only [flag,Set.mem_setOf_eq, decide_eq_decide, arcone]
    let M := ranks (fun u : Nat => C (j+(u : Fin k)-2)) 10
    have he : span (flag {x | key x = j ∧ a ≤ slot x ∧ slot x < b}) ≤ M := by
      apply cover
      intro i hi x hx
      have hkey : key i = j := ((show key i = j ∧ a ≤ slot i ∧ slot i < b by simpa [flag] using hi)).1
      rcases hx with ⟨v,hv,rfl⟩
      rw [hkey]
      exact ranks_mem (fun u : Nat => C (j+(u : Fin k)-2)) (by omega : v < 10)
    have hm := ranks_bound (fun u : Nat => C (j+(u : Fin k)-2)) 10 h (fun u _ => hh _)
    exact (Submodule.finrank_mono (inf_le_left.trans he)).trans (hm.trans (by omega))
  let side := fun (p : Bool) (c : Nat) => cols (fun i => decide (sided p c i))
  let fringe := fun (p : Bool) (c : Nat) =>
    ranks (fun u : Nat => C (edge p c+(u : Fin k))) 7 ⊔
    ranks (fun u : Nat => C (edge (!p) c-((u : Fin k)+1))) 2
  have fringeBound (p : Bool) (c : Nat) : Module.finrank F (fringe p c) ≤ 9*h := by
    have h₁ := ranks_bound (fun u : Nat => C (edge p c+(u : Fin k))) 7 h (fun u _ => hh _)
    have h₂ := ranks_bound (fun u : Nat => C (edge (!p) c-((u : Fin k)+1))) 2 h (fun u _ => hh _)
    have eqn := Submodule.finrank_sup_add_finrank_inf_eq
      (ranks (fun u : Nat => C (edge p c+(u : Fin k))) 7)
      (ranks (fun u : Nat => C (edge (!p) c-((u : Fin k)+1))) 2)
    exact (Nat.le_add_right _ _).trans (eqn.le.trans ((Nat.add_le_add h₁ h₂).trans (by omega)))
  have sideMem (p : Bool) (c : ℕ) (x : Fin k) (hx : sided p c x) : C x ≤ side p c := by
    apply Submodule.span_mono
    rintro f ⟨j, hj, hf⟩
    have he : j = x := of_decide_eq_true hj
    exact ⟨j,decide_eq_true (he ▸ hx),hf⟩
  have sideCover (p : Bool) (c : Nat) (i : I) (hi : sided p c (key i))
      (x : Fin k) (hx : near (key i) x) : C x ≤ side p c ⊔ fringe p c := by
    obtain ⟨v,hv,rfl⟩ := hx
    by_cases hv' : 2 ≤ v
    · obtain ⟨u,rfl⟩ : ∃ u, v = u+2 := ⟨v-2, by omega⟩
      simp only [Nat.cast_add,Nat.cast_ofNat, ← add_assoc, add_sub_cancel_right]
      rcases walk_forward hi u with hx | ⟨l,hl,he⟩
      · exact (sideMem _ _ _ hx).trans le_sup_left
      rw [he]
      exact (ranks_mem (fun u : Nat => C (edge p c+(u : Fin k))) (by omega : l < 7)).trans
        (le_sup_left.trans le_sup_right)
    have aux (d : Nat) (hd : d ≤ 2) : C (key i-(d : Fin k)) ≤ side p c ⊔ fringe p c := by
      rcases walk_backward hi d with hx | ⟨l,hl,he⟩
      · exact (sideMem _ _ _ hx).trans le_sup_left
      rw [he]
      exact (ranks_mem (fun u : Nat => C (edge (!p) c-((u : Fin k)+1))) (by omega : l < 2)).trans
        (le_sup_right.trans le_sup_right)
    obtain rfl | rfl : v = 0 ∨ v = 1 := by omega
    · simpa using aux 2 (by decide)
    · have he : key i + ((1 : Nat) : Fin k) - 2 = key i - 1 := by rw [show (2 : Fin k) = 1+1 by norm_num]; push_cast; abel
      rw [he]; exact aux 1 (by decide)
  have goodPre (c : Nat) (hc : c ≤ k) : good {x | (key x).val < c} := by
    constructor
    · convert geo 0 ⟨c,by omega⟩ 0 (2*r+1) using 1
      funext x
      simp [flag,sbound]
    have coverL : span (flag {x | (key x).val < c}) ≤ side true c ⊔ fringe true c := by
      apply cover
      intro i hi
      exact sideCover true c i (by simpa [flag,sided] using hi)
    have coverR : span (fun i => !(flag {x | (key x).val < c} i)) ≤ side false c ⊔ fringe false c := by
      apply cover
      intro i hi
      apply sideCover
      simpa [flag,sided] using hi
    have sl : side true c = cols (fun i => decide (i.val < c)) := by
      apply congrArg cols; funext j; apply decide_eq_decide.mpr; rfl
    have sr : side false c = cols (fun i => decide (c ≤ i.val)) := by
      apply congrArg cols; funext j; apply decide_eq_decide.mpr; rfl
    have rank0 : Module.finrank F ↥(side true c ⊓ side false c) ≤ s := by
      rw [sl,sr]; exact hs ⟨c,by omega⟩
    have hr := rank_extend (side true c) (side false c) (fringe true c) (fringe false c)
    exact (Submodule.finrank_mono (inf_le_inf coverL coverR)).trans (hr.trans (by
      have := fringeBound true c; have := fringeBound false c; omega))
  obtain ⟨B, ⟨top,ht,et⟩, H⟩ := build_groups hk (by omega : 0 < 2*r+1) key slot sbound uniqueCell good goodCell goodPre
  refine ⟨fun v => flag (B v.val), ⟨⟨⟨top,ht⟩,?_⟩,?_⟩,fun v => (H v.val v.isLt).1.2⟩
  · intro i; simp [flag,et]
  intro v
  refine ⟨(H v.val v.isLt).1.1,?_⟩
  rcases (H v.val v.isLt).2 with ⟨i,hi⟩ | ⟨a,ha,b,hb,hd,he⟩
  · exact Or.inl ⟨i,fun x => by simp [flag,hi]⟩
  refine Or.inr ⟨⟨a,ha.trans v.isLt⟩,⟨b,hb.trans v.isLt⟩,ha,hb,?_,?_⟩
  · intro x hx; simpa [flag] using Set.disjoint_left.mp hd (of_decide_eq_true hx)
  · intro x; simp [flag,he]
