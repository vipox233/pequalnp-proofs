import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.CongrExclamation
import Mathlib.Tactic.Convert
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47146

abbrev Mask (n : Nat) := Finset (Fin n)
abbrev Point (r n : Nat) := Fin r × Fin n
abbrev State (r n : Nat) := Finset (Point r n)
abbrev Edge (n : Nat) := Fin n → Fin n → Bool

def Indep {n} (g : Edge n) (s : Mask n) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, g i j = false

noncomputable def alpha {n} (g : Edge n) (x : Mask n) : Nat := by
  classical
  exact (x.powerset.filter (Indep g)).sup Finset.card

theorem smaller {n} {g : Edge n} {s t : Mask n} (hs : Indep g s) (h : t ⊆ s) :
    Indep g t := fun i hi j hj => hs i (h hi) j (h hj)

theorem card_le_alpha {n} {g : Edge n} {s x : Mask n} (sub : s ⊆ x) (ind : Indep g s) :
    s.card ≤ alpha g x := by
  classical
  exact Finset.le_sup (f:=Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr sub,ind⟩)

theorem maximum {n} (g : Edge n) (x : Mask n) :
    ∃ s ⊆ x, Indep g s ∧ s.card = alpha g x := by
  classical
  let F := x.powerset.filter (Indep g)
  have nonempty : F.Nonempty := ⟨∅,by simp [F,Indep]⟩
  obtain ⟨s,hs,hc⟩ := Finset.exists_mem_eq_sup F nonempty Finset.card
  obtain ⟨hsub,hi⟩ := Finset.mem_filter.mp hs
  exact ⟨s,Finset.mem_powerset.mp hsub,hi,hc.symm⟩

theorem erase_sub {n} {x s : Mask n} {j} (h : s ⊆ insert j x) : s.erase j ⊆ x := by
  intro i hi
  obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hi
  exact (Finset.mem_insert.mp (h mem)).resolve_left ne

theorem insert_bounds {n} (g : Edge n) (x : Mask n) (j : Fin n) :
    alpha g x ≤ alpha g (insert j x) ∧ alpha g (insert j x) ≤ alpha g x+1 := by
  constructor
  · obtain ⟨s,h,ind,eq⟩ := maximum g x
    exact eq ▸ card_le_alpha (h.trans (Finset.subset_insert j x)) ind
  · obtain ⟨s,h,ind,eq⟩ := maximum g (insert j x)
    have le := card_le_alpha (erase_sub h) (smaller ind (Finset.erase_subset j s))
    by_cases hj : j∈s
    · rw [Finset.card_erase_of_mem hj] at le; omega
    · rw [Finset.erase_eq_of_notMem hj] at le; omega

theorem gain_witness {n} (g : Edge n) (x : Mask n) (j : Fin n)
    (gain : alpha g (insert j x)=alpha g x+1) :
    ∃ t ⊆ x, Indep g t ∧ t.card=alpha g x ∧ j∉t ∧ ∀ i ∈ t, g i j=false := by
  obtain ⟨s,hs,ind,eq⟩ := maximum g (insert j x)
  have hj : j∈s := by
    by_contra no
    have sub := erase_sub hs
    rw [Finset.erase_eq_of_notMem no] at sub
    have := card_le_alpha sub ind
    omega
  refine ⟨s.erase j,erase_sub hs,smaller ind (Finset.erase_subset j s),?_,Finset.notMem_erase _ _,?_⟩
  · rw [Finset.card_erase_of_mem hj]; omega
  · exact fun i hi => ind i (Finset.mem_of_mem_erase hi) j hj

def block {r n} (y : State r n) (a : Fin r) : Mask n :=
  Finset.univ.filter (fun i => (a,i)∈y)

def put {r n} (p : State r n) (a : Fin r) (s : Mask n) : State r n :=
  p ∪ s.image (Prod.mk a)

theorem read_put {r n} {p : State r n} {a} (fresh : ∀ i, (a,i)∉p) (s : Mask n) (i : Fin n) :
    (a,i) ∈ put p a s ↔ i∈s := by simp [put,fresh]

theorem block_put {r n} {p : State r n} {a} (fresh : ∀ i, (a,i)∉p) (s : Mask n) :
    block (put p a s) a=s := by ext i; simp [block,read_put fresh]

theorem put_mono {r n} (p : State r n) (a) {s t : Mask n} (sub : s⊆t) :
    put p a s ⊆ put p a t :=
  Finset.union_subset_union (Finset.Subset.refl _) (Finset.image_mono (Prod.mk a) sub)

def pack {r n} (f : State r n → Point r n → Bool) : Nat → State r n → Prop :=
  Nat.rec (motive := fun _ => State r n → Prop) (fun _ => True)
    (fun _ prev y => ∃ (u v : State r n) (k : Point r n), prev u ∧ u⊆v ∧ v⊆y ∧ f u k=true ∧ f v k=false)

theorem pack_up {r n} {f : State r n → Point r n → Bool} {h u v}
    (hp : pack f h u) (sub : u ⊆ v) : pack f h v := by
  cases h with
  | zero => trivial
  | succ h =>
    obtain ⟨s,t,k,prev,st,tu,hi,lo⟩ := hp
    exact ⟨s,t,k,prev,st,tu.trans sub,hi,lo⟩

theorem pack_down {r n} {f : State r n → Point r n → Bool} {h m y}
    (hp : pack f m y) (le : h ≤ m) : pack f h y := by
  induction le with
  | refl => exact hp
  | step _ ih =>
    obtain ⟨u,v,k,prev,uv,vy,_,_⟩ := hp
    exact ih (pack_up prev (uv.trans vy))

end PEqualNP.Outside.L_meta_47146

namespace PEqualNP.Outside.L_meta_47146

theorem adaptive {r} (F : (Fin r → Bool) → Fin r → Bool)
    (past : ∀ u v a, (∀ b, b<a → u b=v b) → F u a=F v a) :
    ∃! ans, ∀ a, ans a=F ans a := by
  classical
  have partialAnswers (k : Nat) : ∃ u : Fin r → Bool, ∀ a, a.val<k → u a=F u a := by
    induction k with
    | zero => exact ⟨fun _ => false,fun a h => by omega⟩
    | succ k ih =>
      obtain ⟨u,hu⟩ := ih
      by_cases hk : k<r
      · let i : Fin r := ⟨k,hk⟩
        let v := Function.update u i (F u i)
        have before (b : Fin r) (hb : b.val<k) : v b=u b := by
          have ne : b≠i := by intro e; have := congrArg Fin.val e; dsimp [i] at this; omega
          exact Function.update_of_ne ne _ _
        refine ⟨v,fun a ha => ?_⟩
        have eq := past v u a fun b hb => before b (by change b.val<a.val at hb; omega)
        by_cases h : a.val=k
        · have ai : a=i := Fin.ext h
          subst a
          exact (Function.update_self i _ u).trans eq.symm
        · exact (before a (by omega)).trans ((hu a (by omega)).trans eq.symm)
      · exact ⟨u,fun a _ => hu a (by have := a.isLt; omega)⟩
  obtain ⟨u,hu⟩ := partialAnswers r
  have good (a : Fin r) := hu a a.isLt
  refine ⟨u,good,?_⟩
  intro v hv
  have agree (k : Nat) : ∀ a : Fin r, a.val=k → v a=u a := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro a ak
      have ex := past v u a fun b hb => ih b.val (by change b.val<a.val at hb; omega) b rfl
      exact (hv a).trans (ex.trans (good a).symm)
  funext a
  exact agree a.val a rfl

theorem majority {r} (ans truth : Fin r → Bool) (e : Nat)
    (m : (Finset.univ.filter (fun a : Fin r => ans a ≠ truth a)).card ≤ e) (b : Bool)
    (same : ∀ a, truth a = b) (lt : 2*e < r) :
    decide (r < 2*(Finset.univ.filter (fun a : Fin r => ans a=true)).card) = b := by
  cases b with
  | false =>
    have eq : Finset.univ.filter (fun a : Fin r => ans a ≠ truth a) =
        Finset.univ.filter (fun a : Fin r => ans a=true) := by
      ext a; simp [same]
    rw [eq] at m
    exact decide_eq_false (by omega)
  | true =>
    let S := Finset.univ.filter (fun a : Fin r => ans a=true)
    have eq : Finset.univ.filter (fun a : Fin r => ans a ≠ truth a) = Sᶜ := by
      ext a; simp [same,S]
    rw [eq,Finset.card_compl] at m
    simp only [Fintype.card_fin] at m
    apply decide_eq_true
    change r<2*S.card
    omega

end PEqualNP.Outside.L_meta_47146

namespace PEqualNP.Outside.L_meta_47146

section
variable {r n : Nat} (g : Fin r → Edge n) (f : State r n → Point r n → Bool)
variable (hi : ∀ y a i, ((a,i) ∉ y ∧ ∀ k ∈ block y a, g a k i = false) → f y (a,i) = true)
variable (lo : ∀ y a i, (a,i) ∈ y → f y (a,i) = false)
variable {p : State r n} {a : Fin r} (fresh : ∀ i, (a,i)∉p) {t : Nat} (hp : pack f t p)

include hi lo fresh hp in
theorem independent_steps (s : Mask n) (ind : Indep (g a) s) :
    pack f (t+s.card) (put p a s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [put] using hp
  | @insert i s hnot ih =>
    have prev := ih (smaller ind (Finset.subset_insert i s))
    have on : f (put p a s) (a,i)=true := by
      apply hi
      rw [block_put fresh,read_put fresh]
      exact ⟨hnot,fun k hk => ind k (Finset.mem_insert_of_mem hk) i (Finset.mem_insert_self ..)⟩
    have off := lo (put p a (insert i s)) a i ((read_put fresh _ _).2 (Finset.mem_insert_self ..))
    rw [Finset.card_insert_of_notMem hnot,← Nat.add_assoc]
    exact ⟨_,_,_,prev,put_mono p a (Finset.subset_insert i s),Finset.Subset.refl _,on,off⟩

include hi lo fresh hp in
theorem full_at_x (x : Mask n) : pack f (t+alpha (g a) x) (put p a x) := by
  obtain ⟨s,sub,ind,eq⟩ := maximum (g a) x
  rw [← eq]
  exact pack_up (independent_steps g f hi lo fresh hp s ind) (put_mono p a sub)

def ending {n} (ans : Bool) (x : Mask n) (j : Fin n) := if ans then insert j x else x

noncomputable def truth {n} (g : Edge n) (x : Mask n) (j : Fin n) : Bool :=
  decide (alpha g (insert j x) = alpha g x + 1)

noncomputable def wrong {n} (ans : Bool) (g : Edge n) (x : Mask n) (j : Fin n) : Nat :=
  if ans ≠ truth g x j then 1 else 0

include hi lo fresh hp in
theorem local_bound (x : Mask n) (j : Fin n) (ans : Bool) (respond : ans=f (put p a x) (a,j)) :
    pack f (t+(alpha (g a) (ending ans x j)+wrong ans (g a) x j)) (put p a (ending ans x j)) := by
  have old := full_at_x g f hi lo fresh hp x
  cases ans with
  | true =>
    have step : pack f (t+alpha (g a) x+1) (put p a (insert j x)) :=
      ⟨_,_,_,old,put_mono p a (Finset.subset_insert j x),Finset.Subset.refl _,respond.symm,
        lo _ a j ((read_put fresh _ _).2 (Finset.mem_insert_self ..))⟩
    have bounds := insert_bounds (g a) x j
    by_cases inc : alpha (g a) (insert j x)=alpha (g a) x+1
    · simpa [ending,wrong,truth,inc,Nat.add_assoc] using step
    · have eq : alpha (g a) (insert j x)=alpha (g a) x := by omega
      simpa [ending,wrong,truth,inc,eq,Nat.add_assoc] using step
  | false =>
    by_cases inc : alpha (g a) (insert j x)=alpha (g a) x+1
    · obtain ⟨s,sub,ind,eq,notj,neighbors⟩ := gain_witness (g a) x j inc
      have prev := independent_steps g f hi lo fresh hp s ind
      rw [eq] at prev
      have on : f (put p a s) (a,j)=true := by
        apply hi
        rw [block_put fresh,read_put fresh]
        exact ⟨notj,neighbors⟩
      have step : pack f (t+alpha (g a) x+1) (put p a x) :=
        ⟨_,_,_,prev,put_mono p a sub,Finset.Subset.refl _,on,respond.symm⟩
      simpa [ending,wrong,truth,inc,Nat.add_assoc] using step
    · simpa [ending,wrong,truth,inc] using old

end
end PEqualNP.Outside.L_meta_47146

namespace PEqualNP.Outside.L_meta_47146

def query {r n} (x : Fin r → Mask n) (j : Fin r → Fin n) (ans : Fin r → Bool) (a : Fin r) : State r n :=
  Finset.univ.filter (fun p =>
    (p.1<a ∧ p.2∈ending (ans p.1) (x p.1) (j p.1)) ∨ (p.1=a ∧ p.2∈x a))

def pref {r n} (z : Fin r → Mask n) (k : Nat) : State r n :=
  Finset.univ.filter (fun p => p.1.val<k ∧ p.2∈z p.1)

theorem mem_put_iff {r n} (p : State r n) (s : Mask n) (a b : Fin r) (i : Fin n) :
    (b,i)∈put p a s ↔ (b,i)∈p ∨ (b=a ∧ i∈s) := by
  simp [put,eq_comm,and_comm]

theorem pref_fresh {r n} (z : Fin r → Mask n) (a : Fin r) :
    ∀ i, (a,i)∉pref z a.val := by simp [pref]

theorem query_eq {r n} (x : Fin r → Mask n) (j : Fin r → Fin n) (ans : Fin r → Bool) (a : Fin r) :
    query x j ans a=put (pref (fun b => ending (ans b) (x b) (j b)) a.val) a (x a) := by
  ext ⟨b,i⟩
  rw [mem_put_iff]
  simp only [query,pref,Finset.mem_filter,Finset.mem_univ,true_and,Fin.lt_def]

theorem pref_succ {r n} (z : Fin r → Mask n) (a : Fin r) :
    pref z (a.val+1)=put (pref z a.val) a (z a) := by
  ext ⟨b,i⟩
  rw [mem_put_iff]
  simp only [pref,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases eq : b=a
  · subst b; simp
  · have ne : b.val≠a.val := fun h => eq (Fin.ext h)
    have iff : b.val<a.val+1 ↔ b.val<a.val := by omega
    simp [eq,iff]

theorem causal {r n} (f : State r n → Point r n → Bool) (x : Fin r → Mask n)
    (j : Fin r → Fin n) : ∃! ans, ∀ a, ans a=f (query x j ans a) (a,j a) := by
  apply adaptive
  intro u v a agree
  have eq : query x j u a=query x j v a := by
    ext ⟨b,i⟩
    by_cases h : b<a
    · simp [query,h,agree b h]
    · simp [query,h]
  rw [eq]

def before {r} (k : Nat) : Finset (Fin r) := Finset.univ.filter (fun b => b.val<k)

theorem before_succ {r} (a : Fin r) :
    before (a.val+1)=insert a (before a.val) := by
  ext b
  simp only [before,Finset.mem_insert,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases h : b=a
  · subst b; simp
  · have ne : b.val≠a.val := fun e => h (Fin.ext e)
    simp [h]; omega

def finalState {r n} (z : Fin r → Mask n) : State r n :=
  Finset.univ.filter (fun p => p.2∈z p.1)

theorem full_prefix {r n} (z : Fin r → Mask n) : pref z r=finalState z := by
  ext ⟨b,i⟩
  simp [pref,finalState]

theorem final_block {r n} (z : Fin r → Mask n) (a : Fin r) :
    block (finalState z) a=z a := by ext i; simp [block,finalState]

theorem count_falls {r n} (g : Fin r → Edge n) (f : State r n → Point r n → Bool)
    (x : Fin r → Mask n) (j : Fin r → Fin n)
    (hi : ∀ y a i, ((a,i) ∉ y ∧ ∀ k ∈ block y a, g a k i = false) → f y (a,i) = true)
    (lo : ∀ y a i, (a,i) ∈ y → f y (a,i) = false)
    (ans : Fin r → Bool) (respond : ∀ a, ans a=f (query x j ans a) (a,j a)) :
    let z := fun a => ending (ans a) (x a) (j a)
    let y := finalState z
    pack f ((∑ a, alpha (g a) (block y a))+
      (Finset.univ.filter (fun a => ans a≠truth (g a) (x a) (j a))).card) y := by
  classical
  let z := fun a => ending (ans a) (x a) (j a)
  let cost := fun a => alpha (g a) (z a)+wrong (ans a) (g a) (x a) (j a)
  have bound (k : Nat) (hk : k≤r) : pack f (∑ b ∈ before k, cost b) (pref z k) := by
    induction k with
    | zero =>
      have eq : before (r:=r) 0=∅ := by ext b; simp [before]
      rw [eq,Finset.sum_empty]
      trivial
    | succ k ih =>
      let a : Fin r := ⟨k,by omega⟩
      have next := local_bound g f hi lo (pref_fresh z a) (ih (by omega)) (x a) (j a) (ans a)
        (by simpa only [query_eq] using respond a)
      change pack f (∑ b ∈ before (a.val+1), cost b) (pref z (a.val+1))
      have missing : a∉before a.val := by simp [before]
      rw [before_succ,Finset.sum_insert missing,pref_succ,Nat.add_comm]
      exact next
  have h := bound r (Nat.le_refl _)
  have allb : before (r:=r) r=Finset.univ := by ext b; simp [before]
  rw [allb,full_prefix] at h
  simp only [cost,Finset.sum_add_distrib] at h
  dsimp only
  simp only [final_block]
  have errors : (∑ a, wrong (ans a) (g a) (x a) (j a)) =
      (Finset.univ.filter (fun a => ans a≠truth (g a) (x a) (j a))).card := by
    simp [wrong,Finset.card_filter]
  rw [errors] at h
  exact h

theorem result {r n} (g : Fin r → Edge n) (f : State r n → Point r n → Bool)
    (x : Fin r → Mask n) (j : Fin r → Fin n) :
    (∀ y a i, ((a,i) ∉ y ∧ ∀ k ∈ block y a, g a k i = false) → f y (a,i) = true) →
    (∀ y a i, (a,i) ∈ y → f y (a,i) = false) →
    (∃! ans, ∀ a, ans a=f (query x j ans a) (a,j a)) ∧
    ∀ ans, (∀ a, ans a=f (query x j ans a) (a,j a)) →
      let z := fun a => ending (ans a) (x a) (j a)
      let rank := fun y => ∑ a, alpha (g a) (block y a)
      let errors := (Finset.univ.filter (fun a => ans a≠truth (g a) (x a) (j a))).card
      pack f (rank (finalState z)+errors) (finalState z) ∧
      ∀ e : Nat, (∀ y, ¬ pack f (rank y+e+1) y) →
        errors≤e ∧ ∀ b : Bool, (∀ a, truth (g a) (x a) (j a)=b) → 2*e<r →
          decide (r<2*(Finset.univ.filter (fun a => ans a=true)).card)=b := by
  intro hi lo
  refine ⟨causal f x j,?_⟩
  intro ans consistent
  have falls := count_falls g f x j hi lo ans consistent
  refine ⟨falls,?_⟩
  intro e limit
  let z := fun a => ending (ans a) (x a) (j a)
  let errors := (Finset.univ.filter (fun a => ans a≠truth (g a) (x a) (j a))).card
  have bound : errors ≤ e := by
    by_contra! larger
    apply limit (finalState z)
    apply pack_down (h := (∑ a, alpha (g a) (block (finalState z) a))+e+1) falls
    change (∑ a, alpha (g a) (block (finalState z) a))+e+1 ≤
      (∑ a, alpha (g a) (block (finalState z) a))+errors
    omega
  exact ⟨bound,majority ans (fun a => truth (g a) (x a) (j a)) e bound⟩

noncomputable def canonicalFilter {α : Type} (p : α → Prop) : Finset α → Finset α :=
  @Finset.filter α p (fun i => Classical.propDecidable (p i))

theorem normalizeFilter {α : Type} (p : α → Prop) [d : DecidablePred p] :
    @Finset.filter α p d = canonicalFilter p := by
  unfold canonicalFilter
  rw [Subsingleton.elim d (fun i => Classical.propDecidable (p i))]

noncomputable def canonicalChoice {α : Type} (p : Prop) (yes no : α) : α :=
  @ite α p (Classical.propDecidable p) yes no

theorem normalizeChoice {α : Type} (p : Prop) [d : Decidable p] (yes no : α) :
    @ite α p d yes no = canonicalChoice p yes no := by
  unfold canonicalChoice
  rw [Subsingleton.elim d (Classical.propDecidable p)]

noncomputable def canonicalDecision (p : Prop) : Bool := @decide p (Classical.propDecidable p)

theorem normalizeDecision (p : Prop) [d : Decidable p] : @decide p d = canonicalDecision p := by
  unfold canonicalDecision
  rw [Subsingleton.elim d (Classical.propDecidable p)]

end PEqualNP.Outside.L_meta_47146

open PEqualNP.Outside.L_meta_47146 in
theorem PEqualNP.Outside.L_meta_47146 :
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∀ (r n : Nat) (edge : Fin r → Fin n → Fin n → Bool),
    (∀ a i, edge a i i = false) → (∀ a i j, edge a i j = edge a j i) →
    let V := Fin r × Fin n
    let X := Finset (Fin n)
    let Y := Finset V
    let block := fun (y : Y) (a : Fin r) =>
      (Finset.univ : X).filter (fun i => (a,i) ∈ y)
    let alpha := fun (a : Fin r) (x : X) =>
      (x.powerset.filter (fun s => ∀ i ∈ s, ∀ j ∈ s, edge a i j = false)).sup Finset.card
    let rank := fun (y : Y) => ∑ a : Fin r, alpha a (block y a)
    ∀ (f : Y → V → Bool) (x : Fin r → X) (j : Fin r → Fin n),
      (∀ y a i, ((a,i) ∉ y ∧ ∀ k ∈ block y a, edge a k i = false) →
        f y (a,i) = true) →
      (∀ y a i, (a,i) ∈ y → f y (a,i) = false) →
      let pack := Nat.rec (motive := fun _ => Y → Prop) (fun _ => True)
        (fun _ prev y => ∃ (u v : Y) (k : V), prev u ∧ u ⊆ v ∧ v ⊆ y ∧
          f u k = true ∧ f v k = false)
      let gain := fun a => decide (alpha a (insert (j a) (x a)) = alpha a (x a)+1)
      let endAt := fun (ans : Fin r → Bool) a =>
        if ans a then insert (j a) (x a) else x a
      let query := fun (ans : Fin r → Bool) (a : Fin r) =>
        (Finset.univ : Y).filter (fun p =>
          (p.1 < a ∧ p.2 ∈ endAt ans p.1) ∨ (p.1 = a ∧ p.2 ∈ x a))
      let consistent := fun (ans : Fin r → Bool) =>
        ∀ a, ans a = f (query ans a) (a,j a)
      (∃! ans, consistent ans) ∧
      ∀ ans, consistent ans →
        let y := (Finset.univ : Y).filter (fun p => p.2 ∈ endAt ans p.1)
        let errors := (Finset.univ.filter (fun a : Fin r => ans a ≠ gain a)).card
        let ones := (Finset.univ.filter (fun a : Fin r => ans a = true)).card
        pack (rank y + errors) y ∧
        ∀ e : Nat, (∀ z, ¬ pack (rank z+e+1) z) →
          errors ≤ e ∧ ∀ b : Bool, (∀ a, gain a = b) → 2*e < r →
            decide (r < 2*ones) = b := by
  classical
  dsimp only
  intro r n edge _ _ f x j
  convert! result edge f x j using 0
  simp only [block,alpha,Indep,query,ending,finalState,truth,pack,normalizeFilter,
    normalizeChoice,normalizeDecision]
  congr!
