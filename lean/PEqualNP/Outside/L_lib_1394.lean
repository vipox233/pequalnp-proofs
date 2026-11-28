import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1394_aux

open scoped Classical

open Finset

variable {n q : ℕ}
abbrev Edges (n q : ℕ) := Fin q → Fin n → Fin n → Bool

abbrev Hit (E : Edges n q) (t : Fin q) (A : Finset (Fin n)) : Prop :=
  ∃ u ∈ A, ∃ v ∈ A, E t u v = true

def Live (E : Edges n q) (V : Finset (Fin n)) : Prop :=
  ∀ u ∈ V, ∃ t, ∃ v ∈ V, E t u v = true

def Blocked (E : Edges n q) (V : Finset (Fin n)) : Prop :=
  ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
    let P : Finset (Fin n) := {u,v}
    ∃ (t z : Fin q) (A B : Finset (Fin n)), A ⊆ V \ P ∧ B ⊆ V \ P ∧
      A.card ≤ 1 ∧ B.card ≤ 1 ∧ Hit E t (A ∪ P) ∧ Hit E z (B ∪ P) ∧
      ∃ J ⊆ P, ¬ (Hit E t (A ∪ J) ↔ Hit E z (B ∪ J))

def ConnectedOn (E : Edges n q) (V : Finset (Fin n)) : Prop :=
  ∀ U : Finset (Fin n), U.Nonempty → U ⊂ V →
    ∃ u ∈ U, ∃ v ∈ V \ U, ∃ t, E t u v = true

lemma hit_single_false (E : Edges n q) (hd : ∀ t v, E t v v = false)
    (t : Fin q) {A : Finset (Fin n)} (hA : A.card ≤ 1) : ¬ Hit E t A := by
  rintro ⟨u, hu, v, hv, h⟩
  have hsub : ({u,v} : Finset (Fin n)) ⊆ A := insert_subset hu (singleton_subset_iff.mpr hv)
  have hcard := Finset.card_le_card hsub
  by_cases huv : u = v
  · subst v; simp [hd] at h
  · simp [huv] at hcard
    omega

lemma complete_live {E : Edges n q} (h : ∀ u v, u ≠ v → ∃ t, E t u v = true)
    {V : Finset (Fin n)} (hc : 2 ≤ V.card) : Live E V := by
  intro u hu
  obtain ⟨v, hv, hn⟩ := Finset.exists_mem_ne hc u
  obtain ⟨t, ht⟩ := h u v hn.symm
  exact ⟨t,v,hv,ht⟩

lemma complete_blocked {E : Edges n q} (hd : ∀ t v, E t v v = false)
    (h : ∀ u v, u ≠ v → ∃ t, E t u v = true)
    {V : Finset (Fin n)} (hc : 3 ≤ V.card) : Blocked E V := by
  intro u hu v hv hn
  let P : Finset (Fin n) := {u,v}
  have hP : P.card = 2 := by simp [P,hn]
  have hPV : P ⊆ V := insert_subset hu (singleton_subset_iff.mpr hv)
  have hlt : P ⊂ V := Finset.ssubset_iff_subset_ne.mpr ⟨hPV, fun he => by rw [← he,hP] at hc; omega⟩
  obtain ⟨w, hw, hwn⟩ := Finset.exists_of_ssubset hlt
  have hun : u ≠ w := fun eq => hwn (by simp [P,← eq])
  obtain ⟨t, ht⟩ := h u v hn
  obtain ⟨z, hz⟩ := h u w hun
  refine ⟨t,z,∅,{w},empty_subset _,?_,by simp,by simp,?_,?_,{u},?_,?_⟩
  · exact singleton_subset_iff.mpr (mem_sdiff.mpr ⟨hw,hwn⟩)
  · exact ⟨u,by simp [P],v,by simp [P],ht⟩
  · exact ⟨u,by simp [P],w,by simp,hz⟩
  · simp [P]
  · intro he
    apply hit_single_false E hd t (by simp : (∅ ∪ {u} : Finset (Fin n)).card ≤ 1)
    exact he.mpr ⟨u,by simp,w,by simp,hz⟩

lemma complete_connected {E : Edges n q} (h : ∀ u v, u ≠ v → ∃ t, E t u v = true)
    (V : Finset (Fin n)) : ConnectedOn E V := by
  intro U hU hUV
  obtain ⟨u,hu⟩ := hU
  obtain ⟨v,hv,hn⟩ := Finset.exists_of_ssubset hUV
  exact ⟨u,hu,v,mem_sdiff.mpr ⟨hv,hn⟩,h u v (fun eq => hn (eq ▸ hu))⟩

lemma iterate {E : Edges n q} (F : Finset (Fin n) → ℕ → ℕ → Prop)
    (step : ∀ V p b, 2 ≤ V.card → Live E V → Blocked E V → F V p b →
      ∃ v ∈ V, ∃ s, s+2 ≤ p ∧ F (V.erase v) s b)
    (base : ∀ V p b, 2 ≤ V.card → ConnectedOn E V → F V p b → V.card ≤ p+1)
    (k p b : ℕ) (hk : k+2 ≤ n)
    (hl : ∀ V : Finset (Fin n), n < V.card+k → Live E V ∧ Blocked E V)
    (hc : ∀ V : Finset (Fin n), V.card+k = n → ConnectedOn E V)
    (hf : F univ p b) : n+k ≤ p+1 := by
  have aux : ∀ d V p, V.card+k = n+d → F V p b → V.card+d ≤ p+1 := by
    intro d
    induction d with
    | zero =>
      intro V p he hf
      have hV : 2 ≤ V.card := by omega
      have hC := hc V (by omega)
      have := base V p b hV hC hf
      omega
    | succ d ih =>
      intro V p he hf
      have hV : 2 ≤ V.card := by omega

      obtain ⟨hL,hB⟩ := hl V (by omega)
      obtain ⟨v,hv,s,hs,hf'⟩ := step V p b hV hL hB hf
      have hcard := Finset.card_erase_add_one hv
      have := ih (V.erase v) s (by omega) hf'
      omega
  simpa using aux k univ p (by simp) hf

abbrev Signal (n : ℕ) := Finset (Fin n) → Bool
def input {n : ℕ} (u : Fin n) : Signal n := fun A => decide (u ∈ A)
def fixed {n : ℕ} (b : Bool) : Signal n := fun _ => b
def neg {n : ℕ} (f : Signal n) : Signal n := fun A => !(f A)
def bin {n : ℕ} (o : Bool) (f g : Signal n) : Signal n :=
  fun A => if o then f A || g A else f A && g A

inductive Instr (n : ℕ)
  | unary (f : Signal n)
  | binary (o : Bool) (f g : Signal n)

def Instr.result : Instr n → Signal n
  | .unary f => neg f
  | .binary o f g => bin o f g

def Instr.pins : Instr n → List (Signal n)
  | .unary f => [f]
  | .binary _ f g => [f,g]

def Instr.isBin : Instr n → Bool
  | .unary _ => false
  | .binary .. => true

def target (E : Edges n q) (V : Finset (Fin n)) (t : Fin q) : Signal n :=
  fun A => decide (Hit E t (A ∩ V))

def Available (V : Finset (Fin n)) (S : List (Instr n)) (f : Signal n) : Prop :=
  (∃ b, f = fixed b) ∨ (∃ u ∈ V, f = input u) ∨ ∃ i ∈ S, f = i.result

lemma Available.cons {V : Finset (Fin n)} {S : List (Instr n)} {i : Instr n} {f : Signal n}
    (h : Available V S f) : Available V (i :: S) f := by
  rcases h with h|h|⟨j,hj,rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨j,List.mem_cons_of_mem _ hj,rfl⟩)

inductive Program (V : Finset (Fin n)) : List (Instr n) → Prop
  | nil : Program V []
  | cons {i S} : Program V S → (∀ f ∈ i.pins, Available V S f) → Program V (i :: S)

def AFits (E : Edges n q) (V : Finset (Fin n)) (p b : ℕ) : Prop :=
  ∃ S : List (Instr n), Program V S ∧ (∀ t, Available V S (target E V t)) ∧
    (S.filter Instr.isBin).length ≤ p ∧ (S.filter (fun i => !i.isBin)).length ≤ b

def restrict {n : ℕ} (W : Finset (Fin n)) (f : Signal n) : Signal n :=
  fun A => f (A ∩ W)

def Instr.restrict (W : Finset (Fin n)) : Instr n → Instr n
  | .unary f => .unary (L_lib_1394_aux.restrict W f)
  | .binary o f g => .binary o (L_lib_1394_aux.restrict W f) (L_lib_1394_aux.restrict W g)

lemma Instr.result_restrict (W : Finset (Fin n)) (i : Instr n) :
    (i.restrict W).result = L_lib_1394_aux.restrict W i.result := by cases i <;> rfl

lemma restrict_input (W : Finset (Fin n)) (u : Fin n) :
    restrict W (input u) = if u ∈ W then input u else fixed false := by
  by_cases h : u ∈ W <;> ext A <;> simp [restrict,input,fixed,h]

lemma restrict_target (E : Edges n q) {W V : Finset (Fin n)} (h : W ⊆ V) (t : Fin q) :
    restrict W (target E V t) = target E W t := by
  ext A
  simp [target,restrict,inter_assoc,inter_eq_left.mpr h]

def Bypass (i : Instr n) : Prop :=
  (∃ b, i.result = fixed b) ∨ ∃ f ∈ i.pins, i.result = f

lemma bin_bypass_fixed (o : Bool) (f g : Signal n)
    (h : (∃ b, f = fixed b) ∨ (∃ b, g = fixed b)) : Bypass (.binary o f g) := by
  rcases h with ⟨b,rfl⟩|⟨b,rfl⟩
  · cases o <;> cases b
    · exact Or.inl ⟨false,by ext A; simp [Instr.result,bin,fixed]⟩
    · exact Or.inr ⟨g, by simp [Instr.pins], by ext A; simp [Instr.result,bin,fixed]⟩
    · exact Or.inr ⟨g, by simp [Instr.pins], by ext A; simp [Instr.result,bin,fixed]⟩
    · exact Or.inl ⟨true,by ext A; simp [Instr.result,bin,fixed]⟩
  · cases o <;> cases b
    · exact Or.inl ⟨false,by ext A; simp [Instr.result,bin,fixed]⟩
    · exact Or.inr ⟨f, by simp [Instr.pins], by ext A; simp [Instr.result,bin,fixed]⟩
    · exact Or.inr ⟨f, by simp [Instr.pins], by ext A; simp [Instr.result,bin,fixed]⟩
    · exact Or.inl ⟨true,by ext A; simp [Instr.result,bin,fixed]⟩

lemma bin_bypass_same (o : Bool) (f g : Signal n) (h : g = f ∨ g = neg f) :
    Bypass (.binary o f g) := by
  rcases h with h|h <;> subst g
  · right
    exact ⟨f,by simp [Instr.pins],by cases o <;> ext A <;> simp [Instr.result,bin]⟩
  · left
    exact ⟨o,by cases o <;> ext A <;> cases h : f A <;> simp [Instr.result,bin,neg,fixed,h]⟩

lemma rewrite_program {V : Finset (Fin n)} {S : List (Instr n)} (hS : Program V S)
    (W : Finset (Fin n)) (skip : Instr n → Bool)
    (hs : ∀ i ∈ S, skip i = true → Bypass (i.restrict W)) :
    ∃ T, Program W T ∧
      (∀ f, Available V S f → Available W T (restrict W f)) ∧
      (T.filter Instr.isBin).length = ((S.filter (fun i => !skip i)).filter Instr.isBin).length ∧
      (T.filter (fun i => !i.isBin)).length =
        ((S.filter (fun i => !skip i)).filter (fun i => !i.isBin)).length := by
  induction hS with
  | nil =>
    refine ⟨[],Program.nil,?_,rfl,rfl⟩
    intro f h
    rcases h with ⟨b,rfl⟩|⟨u,hu,rfl⟩|⟨i,hi,_⟩
    · exact Or.inl ⟨b,rfl⟩
    · rw [restrict_input]
      split
      · exact Or.inr (Or.inl ⟨u,by assumption,rfl⟩)
      · exact Or.inl ⟨false,rfl⟩
    · simp at hi
  | @cons i S hS hav ih =>
    obtain ⟨T,hT,hf,hp,hb⟩ := ih (fun j hj => hs j (List.mem_cons_of_mem _ hj))
    have hpins : ∀ f ∈ (i.restrict W).pins, Available W T f := by
      cases i <;> simp only [Instr.restrict,Instr.pins,List.mem_cons,List.mem_nil_iff,
        or_false] at hav ⊢
      · rintro f rfl
        exact hf _ (hav _ rfl)
      · rintro f (rfl|rfl)
        · exact hf _ (hav _ (Or.inl rfl))
        · exact hf _ (hav _ (Or.inr rfl))
    have hcases (f : Signal n) (h : Available V (i::S) f) :
        f = i.result ∨ Available V S f := by
      rcases h with h|h|⟨j,hj,rfl⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · rcases List.mem_cons.mp hj with rfl|hj
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inr ⟨j,hj,rfl⟩))
    cases he : skip i
    · refine ⟨i.restrict W :: T,Program.cons hT hpins,?_,?_,?_⟩
      · intro f h
        rcases hcases f h with rfl|h
        · exact Or.inr (Or.inr ⟨i.restrict W,by simp, (Instr.result_restrict W i).symm⟩)
        · exact (hf _ h).cons
      · cases i <;> simp [List.filter_cons, he, Instr.restrict, Instr.isBin] at hp ⊢ <;> omega
      · cases i <;> simp [he, Instr.restrict, Instr.isBin] at hb ⊢ <;> omega
    · refine ⟨T,hT,?_,by simpa [he] using hp,by simpa [he] using hb⟩
      intro f h
      rcases hcases f h with rfl|h
      · rw [← Instr.result_restrict]
        rcases hs i (by simp) he with h|⟨g,hg,heq⟩
        · exact Or.inl h
        · exact heq ▸ hpins g hg
      · exact hf _ h


lemma available_cons_iff {V : Finset (Fin n)} {i : Instr n} {S : List (Instr n)}
    {f : Signal n} : Available V (i::S) f ↔ f = i.result ∨ Available V S f := by
  constructor
  · rintro (h|h|⟨j,hj,rfl⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · rcases List.mem_cons.mp hj with rfl|hj
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr ⟨j,hj,rfl⟩))
  · rintro (rfl|h)
    · exact Or.inr (Or.inr ⟨i,by simp,rfl⟩)
    · exact h.cons

def Signed (u : Fin n) (f : Signal n) : Prop := f = input u ∨ f = neg (input u)

lemma neg_neg (f : Signal n) : neg (neg f) = f := by ext A; simp [neg]

lemma Signed.negate {u : Fin n} {f : Signal n} (h : Signed u f) : Signed u (neg f) := by
  rcases h with rfl|rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg _)

lemma signed_same {u : Fin n} {f g : Signal n} (hf : Signed u f) (hg : Signed u g) :
    g = f ∨ g = neg f := by
  rcases hf with rfl|rfl <;> rcases hg with h|h <;> rw [h] <;> simp [neg_neg]

lemma available_unary {V : Finset (Fin n)} {S : List (Instr n)} (hS : Program V S)
    (hn : ∀ i ∈ S, Instr.isBin i = false) (f : Signal n) (hf : Available V S f) :
    (∃ b, f = fixed b) ∨ ∃ u ∈ V, Signed u f := by
  induction hS generalizing f with
  | nil =>
    rcases hf with h|⟨u,hu,rfl⟩|⟨i,hi,_⟩
    · exact Or.inl h
    · exact Or.inr ⟨u,hu,Or.inl rfl⟩
    · simp at hi
  | @cons i S hS hp ih =>
    have hn' := hn i (by simp)
    have ht : ∀ j ∈ S, Instr.isBin j = false :=
      fun j hj => hn j (List.mem_cons_of_mem _ hj)
    rcases available_cons_iff.mp hf with rfl|h
    · cases i with
      | binary => cases hn'
      | unary g =>
        rcases ih ht g (hp g (by simp [Instr.pins])) with ⟨b,rfl⟩|⟨u,hu,hs⟩
        · exact Or.inl ⟨!b,rfl⟩
        · exact Or.inr ⟨u,hu,hs.negate⟩
    · exact ih ht f h

lemma first_binary {V : Finset (Fin n)} {S : List (Instr n)} (hS : Program V S)
    (hb : ∃ i ∈ S, Instr.isBin i = true) :
    ∃ i ∈ S, Instr.isBin i = true ∧ ∀ f ∈ i.pins,
      (∃ b, f = fixed b) ∨ ∃ u ∈ V, Signed u f := by
  classical
  induction hS with
  | nil => simp at hb
  | @cons i S hS hp ih =>
    by_cases h : ∃ j ∈ S, Instr.isBin j = true
    · obtain ⟨j,hj,ht,hs⟩ := ih h
      exact ⟨j,List.mem_cons_of_mem _ hj,ht,hs⟩
    · have hn (j : Instr n) (hj : j ∈ S) : Instr.isBin j = false := by
        cases he : Instr.isBin j
        · rfl
        · exact False.elim (h ⟨j,hj,he⟩)
      obtain ⟨j,hj,ht⟩ := hb
      rcases List.mem_cons.mp hj with rfl|hj
      · exact ⟨j,by simp,ht,fun f hf => available_unary hS hn f (hp f hf)⟩
      · simp [hn j hj] at ht

lemma stable_except {V : Finset (Fin n)} {S : List (Instr n)} (hS : Program V S)
    (u v : Fin n) (i : Instr n) (A B : Finset (Fin n))
    (hag : ∀ w, w ≠ u → w ≠ v → input w A = input w B)
    (hfirst : i.result A = i.result B)
    (hother : ∀ j ∈ S, j.isBin = true → j ≠ i →
      ∀ f ∈ j.pins, ¬ Signed u f ∧ ¬ Signed v f)
    (f : Signal n) (hf : Available V S f) :
    f A = f B ∨ Signed u f ∨ Signed v f := by
  classical
  have hbase (g : Signal n) (hg : ∃ w ∈ V, g = input w) :
      g A = g B ∨ Signed u g ∨ Signed v g := by
    obtain ⟨w,hw,rfl⟩ := hg
    by_cases hu : w = u
    · subst w; exact Or.inr (Or.inl (Or.inl rfl))
    by_cases hv : w = v
    · subst w; exact Or.inr (Or.inr (Or.inl rfl))
    exact Or.inl (hag w hu hv)
  induction hS generalizing f with
  | nil =>
    rcases hf with ⟨b,rfl⟩|h|⟨j,hj,_⟩
    · exact Or.inl rfl
    · exact hbase f h
    · simp at hj
  | @cons j S hS hp ih =>
    have hi := ih (fun l hl => hother l (List.mem_cons_of_mem _ hl))
    rcases available_cons_iff.mp hf with rfl|h
    · by_cases hj : j = i
      · subst j; exact Or.inl hfirst
      cases j with
      | unary g =>
        rcases hi g (hp g (by simp [Instr.pins])) with h|h|h
        · exact Or.inl (by simpa [Instr.result,neg,h])
        · exact Or.inr (Or.inl h.negate)
        · exact Or.inr (Or.inr h.negate)
      | binary o g k =>
        have he (x : Signal n) (hx : x ∈ (Instr.binary o g k).pins) : x A = x B := by
          have hn := hother (.binary o g k) (by simp) rfl hj x hx
          rcases hi x (hp x hx) with h|h|h
          · exact h
          · exact False.elim (hn.1 h)
          · exact False.elim (hn.2 h)
        exact Or.inl (by simp [Instr.result,bin,he g (by simp [Instr.pins]),
          he k (by simp [Instr.pins])])
    · exact hi f h

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

def inp {n : ℕ} (A : Finset (Fin n)) : List Bool :=
  List.ofFn (fun j : Fin n => decide (j ∈ A)) ++ [false,true]

def Physical (E : Edges n q) (V : Finset (Fin n)) (p b : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Fin q → ℕ), FanInTwo C ∧ ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ (∀ t, tap t < n+2+C.size) ∧
    C.size - notCount C ≤ p ∧ notCount C ≤ b ∧
    ∀ A : Finset (Fin n), ∀ t, (C.wires (inp A)).getD (tap t) false = target E V t A

def value (gs : List Gate) (A : Finset (Fin n)) (j : ℕ) : Bool :=
  ((⟨gs,0⟩ : Circuit).wires (inp A)).getD j false

def Wire (gs : List Gate) (f : Signal n) : Prop :=
  ∃ j < n+2+gs.length, ∀ A, value gs A j = f A

lemma inp_length (A : Finset (Fin n)) : (inp A).length = n+2 := by simp [inp]

lemma wire_length (gs : List Gate) (x : List Bool) :
    ((⟨gs,0⟩ : Circuit).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp only [Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil,
      List.length_append,List.length_cons,List.length_nil]
    simp only [Nat.zero_add]
    rw [← Nat.add_assoc]
    exact congrArg (· + 1) ih

lemma value_snoc_old (gs : List Gate) (g : Gate) (A : Finset (Fin n)) (j : ℕ)
    (hj : j < n+2+gs.length) : value (gs ++ [g]) A j = value gs A j := by
  have hw := wire_length gs (inp A)
  rw [inp_length] at hw
  simp only [value,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left]
  simpa [Circuit.wires] using hw ▸ hj

lemma value_snoc_new (gs : List Gate) (g : Gate) (A : Finset (Fin n)) :
    value (gs ++ [g]) A (n+2+gs.length) = g.op.eval (g.inputs.map (value gs A)) := by
  have hw := wire_length gs (inp A)
  rw [inp_length] at hw
  unfold value
  rw [← hw]
  simp [Circuit.wires,List.foldl_append,List.getD_eq_getElem?_getD]

lemma wire_snoc_old {gs : List Gate} {g : Gate} {f : Signal n} (h : Wire gs f) :
    Wire (gs ++ [g]) f := by
  obtain ⟨j,hj,h⟩ := h
  exact ⟨j,by simp; omega,fun A => (value_snoc_old gs g A j hj).trans (h A)⟩

lemma wire_input (u : Fin n) : Wire [] (input u) := by
  refine ⟨u.val,by simp; omega,?_⟩
  intro A
  simp [value,Circuit.wires,inp,input,List.getD_eq_getElem?_getD,
    List.getElem?_append_left, u.isLt, List.getElem?_ofFn]

lemma wire_fixed (b : Bool) : Wire ([] : List Gate) (fixed (n := n) b) := by
  refine ⟨if b then n+1 else n,by cases b <;> simp,?_⟩
  intro A
  cases b <;> simp [value,Circuit.wires,inp,fixed,List.getD_eq_getElem?_getD,
    List.getElem?_append_right]

lemma wire_input_any (gs : List Gate) (u : Fin n) : Wire gs (input u) := by
  induction gs using List.reverseRecOn with
  | nil => exact wire_input u
  | append_singleton gs g ih => exact wire_snoc_old ih

lemma wire_fixed_any (gs : List Gate) (b : Bool) : Wire gs (fixed (n := n) b) := by
  induction gs using List.reverseRecOn with
  | nil => exact wire_fixed b
  | append_singleton gs g ih => exact wire_snoc_old ih

def Good (n : ℕ) (gs : List Gate) : Prop :=
  FanInTwo ⟨gs,0⟩ ∧ ReadsBack (n+2) ⟨gs,0⟩

lemma good_nil : Good n [] := by simp [Good,FanInTwo,ReadsBack]

lemma good_snoc {gs : List Gate} {g : Gate} :
    Good n (gs ++ [g]) ↔ Good n gs ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 ∧
      ∀ j ∈ g.inputs, j < n+2+gs.length := by
  have hold (i : ℕ) (hi : i < gs.length) :
      gateAt ⟨gs ++ [g],0⟩ i = gateAt ⟨gs,0⟩ i := by
    simp only [gateAt,List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi]
  have hnew : gateAt ⟨gs ++ [g],0⟩ gs.length = g := by
    simp [gateAt,List.getD_eq_getElem?_getD]
  constructor
  · rintro ⟨hf,hr⟩
    have hn := hf g (by simp)
    refine ⟨⟨fun j hj => hf j (by simp [hj]),?_⟩,?_,hn.2,?_⟩
    · intro i hi j hj
      have hi' : i < gs.length := hi
      apply hr i (by simp; omega) j
      simpa [hold i hi] using hj
    · simpa using hn.1
    · intro j hj
      exact hr gs.length (by simp) j (by simpa [hnew] using hj)
  · rintro ⟨⟨hf,hr⟩,hop,hl,hj⟩
    constructor
    · intro j he
      rcases List.mem_append.mp he with he|he
      · exact hf j he
      · obtain rfl : j = g := by simpa using he
        exact ⟨by simpa using hop,hl⟩
    · intro i hi j he
      by_cases h : i < gs.length
      · exact hr i h j (by simpa [← hold i h] using he)
      · have : i = gs.length := by simp at hi; omega
        subst i
        exact hj j (by simpa [hnew] using he)

def negCost (gs : List Gate) := notCount ⟨gs,0⟩
def posCost (gs : List Gate) := gs.length - negCost gs

lemma cost_snoc (gs : List Gate) (g : Gate) :
    negCost (gs ++ [g]) = negCost gs + (if g.op = .not then 1 else 0) ∧
    posCost (gs ++ [g]) = posCost gs + (if g.op = .not then 0 else 1) := by
  have hle : negCost gs ≤ gs.length := List.length_filter_le ..
  by_cases h : g.op = .not <;> simp [posCost,negCost,notCount,h] at hle ⊢ <;> omega

lemma program_to_physical {V : Finset (Fin n)} {S : List (Instr n)} (hS : Program V S) :
    ∃ gs, Good n gs ∧
      (∀ f, Available V S f → Wire gs f) ∧
      posCost gs = (S.filter Instr.isBin).length ∧
      negCost gs = (S.filter (fun i => !i.isBin)).length := by
  induction hS with
  | nil =>
    refine ⟨[],good_nil,?_,rfl,rfl⟩
    rintro f (⟨b,rfl⟩|⟨u,hu,rfl⟩|⟨i,hi,he⟩)
    · exact wire_fixed _
    · exact wire_input _
    · simp at hi
  | @cons i S hS hp ih =>
    obtain ⟨gs,hg,hw,hpC,hnC⟩ := ih
    suffices ∃ g : Gate, Good n (gs ++ [g]) ∧ Wire (gs ++ [g]) i.result ∧
        (g.op = .not ↔ i.isBin = false) by
      obtain ⟨g,hg',hv,hop⟩ := this
      refine ⟨gs++[g],hg',?_,?_,?_⟩
      · intro f hf
        rcases available_cons_iff.mp hf with rfl|h
        · exact hv
        · exact wire_snoc_old (hw f h)
      · rw [(cost_snoc gs g).2,hpC]
        cases h : i.isBin <;> simp_all
      · rw [(cost_snoc gs g).1,hnC]
        cases h : i.isBin <;> simp_all
    cases i with
    | unary f =>
      obtain ⟨w,hw,hv⟩ := hw f (hp f (by simp [Instr.pins]))
      let g : Gate := ⟨.not,[w]⟩
      refine ⟨g,good_snoc.mpr ⟨hg,by simp [g,hw]⟩,?_,by simp [g,Instr.isBin]⟩
      refine ⟨n+2+gs.length,by simp,fun A => ?_⟩
      simp [value_snoc_new,g,GateOp.eval,Instr.result,neg,hv]
    | binary o f k =>
      obtain ⟨w,hw,hv⟩ := hw f (hp f (by simp [Instr.pins]))
      obtain ⟨j,hj,he⟩ := ‹∀ f, Available V S f → Wire gs f› k (hp k (by simp [Instr.pins]))
      let g : Gate := ⟨if o then .or else .and,[w,j]⟩
      refine ⟨g,good_snoc.mpr ⟨hg,?_⟩,?_,?_⟩
      · cases o <;> simp [g,hw,hj]
      · refine ⟨n+2+gs.length,by simp,fun A => ?_⟩
        cases o <;> simp [value_snoc_new,g,GateOp.eval,Instr.result,bin,hv,he]
      · cases o <;> simp [g,Instr.isBin]

lemma abstract_to_fit {E : Edges n q} {V : Finset (Fin n)} {p b : ℕ}
    (h : AFits E V p b) : Physical E V p b := by
  classical
  obtain ⟨S,hS,hT,hp,hb⟩ := h
  obtain ⟨gs,⟨hf,hr⟩,hw,hpC,hnC⟩ := program_to_physical hS
  choose tap ht he using fun t => hw _ (hT t)
  refine ⟨⟨gs,0⟩,tap,hf,hr,by simp [Circuit.size],ht,?_,?_,fun A t => he t A⟩
  · change posCost gs ≤ p
    exact hpC.symm ▸ hp
  · change negCost gs ≤ b
    exact hnC.symm ▸ hb

def sig (V : Finset (Fin n)) (gs : List Gate) (j : ℕ) : Signal n :=
  fun A => value gs (A ∩ V) j

lemma sig_empty (V : Finset (Fin n)) (j : ℕ) (hj : j < n+2) :
    Available V [] (sig V [] j) := by
  by_cases h : j < n
  · let u : Fin n := ⟨j,h⟩
    have he : sig V [] j = restrict V (input u) := by
      ext A
      simp [sig,restrict,value,Circuit.wires,inp,input,List.getD_eq_getElem?_getD,
        List.getElem?_append_left,h,u,List.getElem?_ofFn]
    rw [he,restrict_input]
    split
    · exact Or.inr (Or.inl ⟨u,by assumption,rfl⟩)
    · exact Or.inl ⟨false,rfl⟩
  · have hj' : j = n ∨ j = n+1 := by omega
    rcases hj' with rfl|rfl
    · refine Or.inl ⟨false,?_⟩
      ext A
      simp [sig,value,Circuit.wires,inp,fixed,List.getD_eq_getElem?_getD,
        List.getElem?_append_right]
    · refine Or.inl ⟨true,?_⟩
      ext A
      simp [sig,value,Circuit.wires,inp,fixed,List.getD_eq_getElem?_getD,
        List.getElem?_append_right]

lemma gate_interpret (V : Finset (Fin n)) (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hl : g.inputs.length ≤ 2) :
    (g.op ≠ .not ∧ Available V [] (sig V (gs ++ [g]) (n+2+gs.length))) ∨
    (g.op ≠ .not ∧ ∃ j ∈ g.inputs,
      sig V (gs ++ [g]) (n+2+gs.length) = sig V gs j) ∨
    ∃ i : Instr n, i.result = sig V (gs ++ [g]) (n+2+gs.length) ∧
      (i.isBin = true ↔ g.op ≠ .not) ∧
      (∀ f ∈ i.pins, f = fixed false ∨ ∃ j ∈ g.inputs, f = sig V gs j) := by
  obtain ⟨op,l⟩ := g
  change op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not at hop
  change l.length ≤ 2 at hl
  rcases l with _|⟨j,_|⟨k,_|⟨a,l⟩⟩⟩
  · rcases hop with rfl|rfl|rfl
    · refine Or.inl ⟨by simp,Or.inl ⟨true,?_⟩⟩
      ext A; simp [sig,value_snoc_new,GateOp.eval,fixed]
    · refine Or.inl ⟨by simp,Or.inl ⟨false,?_⟩⟩
      ext A; simp [sig,value_snoc_new,GateOp.eval,fixed]
    · refine Or.inr (Or.inr ⟨.unary (fixed false),?_,by simp [Instr.isBin],?_⟩)
      · ext A; simp [Instr.result,neg,fixed,sig,value_snoc_new,GateOp.eval]
      · simp [Instr.pins]
  · rcases hop with rfl|rfl|rfl
    · refine Or.inr (Or.inl ⟨by simp,j,by simp,?_⟩)
      ext A; simp [sig,value_snoc_new,GateOp.eval]
    · refine Or.inr (Or.inl ⟨by simp,j,by simp,?_⟩)
      ext A; simp [sig,value_snoc_new,GateOp.eval]
    · refine Or.inr (Or.inr ⟨.unary (sig V gs j),?_,by simp [Instr.isBin],?_⟩)
      · ext A; simp [Instr.result,neg,sig,value_snoc_new,GateOp.eval]
      · simp [Instr.pins]
  · rcases hop with rfl|rfl|rfl
    · refine Or.inr (Or.inr ⟨.binary false (sig V gs j) (sig V gs k),?_,by simp [Instr.isBin],?_⟩)
      · ext A; simp [Instr.result,bin,sig,value_snoc_new,GateOp.eval]
      · intro f hf
        simp [Instr.pins] at hf
        rcases hf with rfl|rfl
        · exact Or.inr ⟨j,by simp,rfl⟩
        · exact Or.inr ⟨k,by simp,rfl⟩
    · refine Or.inr (Or.inr ⟨.binary true (sig V gs j) (sig V gs k),?_,by simp [Instr.isBin],?_⟩)
      · ext A; simp [Instr.result,bin,sig,value_snoc_new,GateOp.eval]
      · intro f hf
        simp [Instr.pins] at hf
        rcases hf with rfl|rfl
        · exact Or.inr ⟨j,by simp,rfl⟩
        · exact Or.inr ⟨k,by simp,rfl⟩
    · refine Or.inr (Or.inr ⟨.unary (sig V gs j),?_,by simp [Instr.isBin],?_⟩)
      · ext A; simp [Instr.result,neg,sig,value_snoc_new,GateOp.eval]
      · intro f hf
        obtain rfl : f = sig V gs j := by simpa [Instr.pins] using hf
        exact Or.inr ⟨j,by simp,rfl⟩
  · simp at hl

lemma physical_to_program (V : Finset (Fin n)) (gs : List Gate) (hg : Good n gs) :
    ∃ S, Program V S ∧
      (∀ j < n+2+gs.length, Available V S (sig V gs j)) ∧
      (S.filter Instr.isBin).length ≤ posCost gs ∧
      (S.filter (fun i => !i.isBin)).length ≤ negCost gs := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[],Program.nil,fun j hj => sig_empty V j (by simpa using hj),by simp,by simp⟩
  | append_singleton gs g ih =>
    obtain ⟨hg',hop,hl,hr⟩ := good_snoc.mp hg
    obtain ⟨S,hS,havail,hp,hb⟩ := ih hg'
    have hj (j : ℕ) (hj : j < n+2+(gs++[g]).length) :
        j < n+2+gs.length ∨ j = n+2+gs.length := by simp at hj; omega
    have hold (j : ℕ) (he : j < n+2+gs.length) :
        sig V (gs++[g]) j = sig V gs j :=
      funext fun A => value_snoc_old gs g (A ∩ V) j he
    have keep (h : Available V S (sig V (gs++[g]) (n+2+gs.length))) :
        ∀ j < n+2+(gs++[g]).length, Available V S (sig V (gs++[g]) j) := by
      intro j hj'
      rcases hj j hj' with he|rfl
      · rw [hold j he]; exact havail j he
      · exact h
    rcases gate_interpret V gs g hop hl with ⟨hn,h⟩|⟨hn,j,hj',he⟩|⟨i,hi,hc,hpins⟩
    · have hh : Available V S (sig V (gs++[g]) (n+2+gs.length)) := by
        rcases h with h|h|⟨i,hi,_⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · simp at hi
      exact ⟨S,hS,keep hh,by rw [(cost_snoc gs g).2]; omega,
        by rw [(cost_snoc gs g).1]; omega⟩
    · exact ⟨S,hS,keep (by rw [he]; exact havail j (hr j hj')),by rw [(cost_snoc gs g).2]; omega,
        by rw [(cost_snoc gs g).1]; omega⟩
    · have hpre : ∀ f ∈ i.pins, Available V S f := by
        intro f hf
        rcases hpins f hf with rfl|⟨j,hj,rfl⟩
        · exact Or.inl ⟨false,rfl⟩
        · exact havail j (hr j hj)
      refine ⟨i::S,Program.cons hS hpre,?_,?_,?_⟩
      · intro j hj'
        rcases hj j hj' with he|rfl
        · rw [hold j he]
          exact (havail j he).cons
        · exact available_cons_iff.mpr (Or.inl hi.symm)
      · rw [(cost_snoc gs g).2]
        cases h : i.isBin <;> simp_all
      · rw [(cost_snoc gs g).1]
        cases h : i.isBin <;> simp_all

lemma fit_to_abstract {E : Edges n q} {V : Finset (Fin n)} {p b : ℕ}
    (h : Physical E V p b) : AFits E V p b := by
  obtain ⟨⟨gs,out⟩,tap,hf,hr,ho,ht,hp,hb,he⟩ := h
  obtain ⟨S,hS,ha,hpC,hbC⟩ := physical_to_program V gs ⟨hf,hr⟩
  refine ⟨S,hS,?_,hpC.trans hp,hbC.trans hb⟩
  intro t
  have h : sig V gs (tap t) = target E V t := by
    ext A
    change ((⟨gs,out⟩ : Circuit).wires (inp (A ∩ V))).getD (tap t) false = _
    rw [he]
    simp [target,inter_assoc]
  rw [← h]
  exact ha _ (ht t)

lemma target_false_small {E : Edges n q} (hd : ∀ t v, E t v v = false)
    (V : Finset (Fin n)) (t : Fin q) {A : Finset (Fin n)} (hA : A.card ≤ 1) :
    target E V t A = false := by
  have h := hit_single_false E hd t (A := A ∩ V) ((card_le_card inter_subset_left).trans hA)
  simp [target,h]

lemma target_not_signed {E : Edges n q} (hd : ∀ t v, E t v v = false)
    (V : Finset (Fin n)) (t : Fin q) (u : Fin n) : ¬ Signed u (target E V t) := by
  rintro (h|h)
  · have e := congrFun h {u}
    rw [target_false_small hd V t (by simp)] at e
    simp [input] at e
  · have e := congrFun h ∅
    rw [target_false_small hd V t (by simp)] at e
    simp [neg,input] at e

lemma target_nonconstant {E : Edges n q} (hd : ∀ t v, E t v v = false)
    {V : Finset (Fin n)} (t : Fin q) (h : Hit E t V) :
    ¬ ∃ b, target E V t = fixed b := by
  rintro ⟨b,hb⟩
  have h0 := congrFun hb ∅
  have h1 := congrFun hb V
  rw [target_false_small hd V t (by simp)] at h0
  simp [target,fixed,h] at h1
  simp [fixed] at h0
  cases h0.symm.trans h1

lemma Bypass.restrict {W : Finset (Fin n)} {i : Instr n} (h : Bypass i) :
    Bypass (i.restrict W) := by
  rw [Bypass,Instr.result_restrict]
  rcases h with ⟨b,h⟩|⟨f,hf,h⟩
  · exact Or.inl ⟨b,by rw [h]; rfl⟩
  · refine Or.inr ⟨L_lib_1394_aux.restrict W f,?_,by rw [h]⟩
    cases i <;> simp only [Instr.pins,Instr.restrict,List.mem_cons,List.mem_nil_iff,or_false] at hf ⊢
    · rw [hf]
    · rcases hf with h|h <;> simp [h]

lemma restricted_signed_fixed {V : Finset (Fin n)} {u : Fin n} {f : Signal n}
    (hf : Signed u f) : ∃ b, restrict (V.erase u) f = fixed b := by
  rcases hf with rfl|rfl
  · exact ⟨false,by rw [restrict_input]; simp⟩
  · refine ⟨true,?_⟩
    ext A
    simp [restrict,neg,input,fixed]

lemma restrict_bypass_of_signed {V : Finset (Fin n)} {u : Fin n}
    {i : Instr n} (hi : i.isBin = true) {f : Signal n} (hf : f ∈ i.pins)
    (hs : Signed u f) : Bypass (i.restrict (V.erase u)) := by
  cases i with
  | unary => cases hi
  | binary o g k =>
    simp [Instr.pins] at hf
    rcases hf with rfl|rfl
    · exact bin_bypass_fixed o _ _ (Or.inl (restricted_signed_fixed hs))
    · exact bin_bypass_fixed o _ _ (Or.inr (restricted_signed_fixed hs))

lemma count_drop {α : Type*} (L : List α) (p d : α → Bool) :
    ((L.filter (fun i => !d i)).filter p).length + ((L.filter d).filter p).length =
      (L.filter p).length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases hd : d a <;> cases hp : p a <;> simp [hd,hp] at ih ⊢ <;> omega

lemma afits_rewrite {E : Edges n q} {V W : Finset (Fin n)} {S : List (Instr n)}
    (hWV : W ⊆ V) (hS : Program V S) (hT : ∀ t, Available V S (target E V t))
    (d : Instr n → Bool) (hd : ∀ i ∈ S, d i = true → Bypass (i.restrict W))
    (_hn : ∀ i ∈ S, d i = true → i.isBin = true) :
    AFits E W (((S.filter (fun i => !d i)).filter Instr.isBin).length)
      ((S.filter (fun i => !i.isBin)).length) := by
  obtain ⟨T,hP,ha,hp,hb⟩ := rewrite_program hS W d hd
  refine ⟨T,hP,?_,hp.le,?_⟩
  · intro t
    simpa only [restrict_target E hWV] using ha _ (hT t)
  · rw [hb]
    have h := count_drop S (fun i => !i.isBin) d
    omega

lemma reject_bypass {E : Edges n q} {V : Finset (Fin n)} {S : List (Instr n)} {b : ℕ}
    (hS : Program V S) (hT : ∀ t, Available V S (target E V t))
    (hb : (S.filter (fun i => !i.isBin)).length ≤ b)
    (hmin : ∀ r < (S.filter Instr.isBin).length, ¬ AFits E V r b)
    (i : Instr n) (hi : i ∈ S) (hbin : i.isBin = true) : ¬ Bypass i := by
  classical
  intro h
  let d : Instr n → Bool := fun j => decide (j = i)
  have he (j : Instr n) (hj : d j = true) : j = i := of_decide_eq_true hj
  have ha := afits_rewrite (Subset.rfl : V ⊆ V) hS hT d
    (fun j _ hj => he j hj ▸ h.restrict) (fun j _ hj => he j hj ▸ hbin)
  have hm : i ∈ (S.filter d).filter Instr.isBin := by simp [d,hi,hbin]
  have hpos : 0 < ((S.filter d).filter Instr.isBin).length :=
    List.length_pos_of_mem hm
  have hcount := count_drop S Instr.isBin d
  apply hmin (((S.filter (fun i => !d i)).filter Instr.isBin).length) (by omega)
  obtain ⟨T,hP,hO,hp,hb'⟩ := ha
  exact ⟨T,hP,hO,hp,hb'.trans hb⟩

lemma bool_section {α : Type*} (a z : α) (x y : α → Bool)
    (hy0 : y a = false) (hy1 : y z = true)
    (h : ∀ i j, x i = x j → y i = y j) (j : α) :
    y j = true ↔ x j ≠ x a := by
  have hz : x z ≠ x a := fun e => by simpa [hy0,hy1] using h z a e
  by_cases he : x j = x a
  · simp [he,h j a he,hy0]
  · have h' : x j = x z := by
      cases h1 : x j <;> cases h2 : x z <;> cases h3 : x a <;> simp_all
    simp [he,h j z h',hy1]

lemma section_forbidden {E : Edges n q} {V : Finset (Fin n)} {S : List (Instr n)}
    (hd : ∀ t v, E t v v = false) (hB : Blocked E V) (hS : Program V S)
    (hT : ∀ t, Available V S (target E V t))
    {u v : Fin n} (hu : u ∈ V) (hv : v ∈ V) (hn : u ≠ v)
    {o : Bool} {f g : Signal n} (hf : Signed u f) (hg : Signed v g) :
    ∃ j ∈ S, j.isBin = true ∧ j ≠ Instr.binary o f g ∧
      ∃ k ∈ j.pins, Signed u k ∨ Signed v k := by
  classical
  by_contra! h
  let P : Finset (Fin n) := {u,v}
  let x : Finset (Fin n) → Bool := (Instr.binary o f g).result
  have hother (j : Instr n) (hj : j ∈ S) (hb : j.isBin = true)
      (hj' : j ≠ Instr.binary o f g) (k : Signal n) (hk : k ∈ j.pins) :
      ¬ Signed u k ∧ ¬ Signed v k := h j hj hb hj' k hk
  have hx (A J : Finset (Fin n)) (hA : A ⊆ V \ P) :
      x (A ∪ J) = x J := by
    have hmem (w : Fin n) (hw : w ∈ P) : input w (A ∪ J) = input w J := by
      have hnot : w ∉ A := fun ha => (mem_sdiff.mp (hA ha)).2 hw
      simp [input,hnot]
    have e1 : f (A ∪ J) = f J := by
      rcases hf with rfl|rfl <;> simp [neg,hmem u (by simp [P])]
    have e2 : g (A ∪ J) = g J := by
      rcases hg with rfl|rfl <;> simp [neg,hmem v (by simp [P])]
    simp [x,Instr.result,bin,e1,e2]
  have factor (t : Fin q) (A : Finset (Fin n)) (hA : A ⊆ V \ P) (hcard : A.card ≤ 1)
      (hhit : Hit E t (A ∪ P)) (J : Finset (Fin n)) (hJ : J ⊆ P) :
      Hit E t (A ∪ J) ↔ x J ≠ x ∅ := by
    have hpv : P ⊆ V := insert_subset hu (singleton_subset_iff.mpr hv)
    have hinter (K : Finset (Fin n)) (hK : K ⊆ P) : (A ∪ K) ∩ V = A ∪ K :=
      inter_eq_left.mpr (union_subset ((hA.trans sdiff_subset)) (hK.trans hpv))
    let y : {K : Finset (Fin n) // K ⊆ P} → Bool := fun K => target E V t (A ∪ K.val)
    let xx : {K : Finset (Fin n) // K ⊆ P} → Bool := fun K => x K.val
    have hs (I K : {K : Finset (Fin n) // K ⊆ P}) (he : xx I = xx K) : y I = y K := by
      have hag (w : Fin n) (wu : w ≠ u) (wv : w ≠ v) :
          input w (A ∪ I.val) = input w (A ∪ K.val) := by
        have hi : w ∉ I.val := fun hw => by simpa [P,wu,wv] using I.property hw
        have hk : w ∉ K.val := fun hw => by simpa [P,wu,wv] using K.property hw
        simp [input,hi,hk]
      have he' : x (A ∪ I.val) = x (A ∪ K.val) := by rw [hx _ _ hA,hx _ _ hA]; exact he
      rcases stable_except hS u v (.binary o f g) _ _ hag he' hother _ (hT t) with h|h|h
      · exact h
      · exact False.elim (target_not_signed hd V t u h)
      · exact False.elim (target_not_signed hd V t v h)
    have h0 : y ⟨∅,empty_subset P⟩ = false := by
      simpa [y] using target_false_small hd V t hcard
    have h1 : y ⟨P,Subset.rfl⟩ = true := by simp [y,target,hinter _ Subset.rfl,hhit]
    have he := bool_section ⟨∅,empty_subset P⟩ ⟨P,Subset.rfl⟩ xx y h0 h1 hs ⟨J,hJ⟩
    simpa [xx,y,target,hinter J hJ] using he
  obtain ⟨t,z,A,B,ha,hb,hca,hcb,hta,htb,J,hJ,hcontra⟩ := hB u hu v hv hn
  exact hcontra ((factor t A ha hca hta J hJ).trans (factor z B hb hcb htb J hJ).symm)

lemma abstract_step {E : Edges n q} (hd : ∀ t v, E t v v = false)
    (V : Finset (Fin n)) (p b : ℕ) (hc : 2 ≤ V.card) (hl : Live E V)
    (hB : Blocked E V) (hF : AFits E V p b) :
    ∃ v ∈ V, ∃ s, s+2 ≤ p ∧ AFits E (V.erase v) s b := by
  classical
  let P : ℕ → Prop := fun r => AFits E V r b
  have hex : ∃ r, P r := ⟨p,hF⟩
  have hle : Nat.find hex ≤ p := Nat.find_min' hex hF
  obtain ⟨S,hS,hT,hp,hb⟩ := Nat.find_spec hex
  have hmin : ∀ r < (S.filter Instr.isBin).length, ¬ AFits E V r b :=
    fun r hr => Nat.find_min hex (by omega)
  have hbex : ∃ i ∈ S, Instr.isBin i = true := by
    by_contra! hn
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < V.card by omega)
    obtain ⟨t,v,hv,he⟩ := hl u hu
    rcases available_unary hS (fun i hi => Bool.eq_false_of_ne_true (hn i hi)) _ (hT t) with h|⟨w,hw,h⟩
    · exact target_nonconstant hd t ⟨u,hu,v,hv,he⟩ h
    · exact target_not_signed hd V t w h
  obtain ⟨i,hi,hib,hfirst⟩ := first_binary hS hbex
  cases i with
  | unary => cases hib
  | binary o f g =>
    let i : Instr n := .binary o f g
    have hnob := reject_bypass hS hT hb hmin i hi hib
    have hvf := hfirst f (by simp [Instr.pins])
    have hvg := hfirst g (by simp [Instr.pins])
    rcases hvf with he|⟨u,hu,hf⟩
    · exact False.elim (hnob (bin_bypass_fixed o f g (Or.inl he)))
    rcases hvg with he|⟨v,hv,hg⟩
    · exact False.elim (hnob (bin_bypass_fixed o f g (Or.inr he)))
    have hn : u ≠ v := by
      rintro rfl
      exact hnob (bin_bypass_same o f g (signed_same hf hg))
    obtain ⟨j,hj,hjb,hji,k,hk,hk'⟩ := section_forbidden hd hB hS hT hu hv hn hf hg (o := o)
    obtain ⟨w,hw,hB1,hB2⟩ : ∃ w ∈ V, Bypass (i.restrict (V.erase w)) ∧ Bypass (j.restrict (V.erase w)) := by
      rcases hk' with he|he
      · exact ⟨u,hu,restrict_bypass_of_signed hib (by simp [i,Instr.pins]) hf,
          restrict_bypass_of_signed hjb hk he⟩
      · exact ⟨v,hv,restrict_bypass_of_signed hib (by simp [i,Instr.pins]) hg,
          restrict_bypass_of_signed hjb hk he⟩
    let d : Instr n → Bool := fun l => decide (l = i ∨ l = j)
    have de (l : Instr n) (h : d l = true) : l = i ∨ l = j := of_decide_eq_true h
    have ha := afits_rewrite (erase_subset w V) hS hT d
      (fun l _ he => (de l he).elim (fun e => e ▸ hB1) (fun e => e ▸ hB2))
      (fun l _ he => (de l he).elim (fun e => e ▸ hib) (fun e => e ▸ hjb))
    let L := (S.filter d).filter Instr.isBin
    have hiL : i ∈ L := by simp [L,d,i,hi,hib]
    have hjL : j ∈ L := by simp [L,d,hj,hjb]
    have hsub : ({j,i} : Finset (Instr n)) ⊆ L.toFinset :=
      insert_subset (List.mem_toFinset.mpr hjL) (singleton_subset_iff.mpr (List.mem_toFinset.mpr hiL))
    have htwo := (card_le_card hsub).trans (List.toFinset_card_le (l := L))
    simp [show j ≠ i from hji] at htwo
    obtain ⟨T,hP,hO,hp',hb'⟩ := ha
    have hcount := count_drop S Instr.isBin d
    change 2 ≤ ((S.filter d).filter Instr.isBin).length at htwo
    exact ⟨w,hw,_,by omega,⟨T,hP,hO,hp',hb'.trans hb⟩⟩

def Depends (V : Finset (Fin n)) (c : Fin n → ℕ) (k : ℕ) (f : Signal n) : Prop :=
  ∀ A B, (∀ u ∈ V, c u = k → input u A = input u B) → f A = f B

def merge (a b k : ℕ) : ℕ := if k = b then a else k

lemma dep_merge {V : Finset (Fin n)} {c : Fin n → ℕ} {a b k : ℕ} {f : Signal n}
    (h : Depends V c k f) : Depends V (merge a b ∘ c) (merge a b k) f :=
  fun A B hAB => h A B (fun u hu he => hAB u hu (by simp [he]))

lemma card_merge (V : Finset (Fin n)) (c : Fin n → ℕ) (a b : ℕ) :
    (V.image c).card ≤ (V.image (merge a b ∘ c)).card + 1 := by
  have hsub : V.image c ⊆ insert b (V.image (merge a b ∘ c)) := by
    intro k hk
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hk
    by_cases h : c u = b
    · simp [h]
    · apply mem_insert_of_mem
      exact mem_image.mpr ⟨u,hu,by simp [merge,h]⟩
  exact (card_le_card hsub).trans (card_insert_le _ _)

lemma component_bound {V : Finset (Fin n)} {S : List (Instr n)} (hS : Program V S) :
    ∃ c : Fin n → ℕ, V.card ≤ (V.image c).card + (S.filter Instr.isBin).length ∧
      ∀ f, Available V S f → ∃ k, Depends V c k f := by
  induction hS with
  | nil =>
    refine ⟨Fin.val,?_,?_⟩
    · simp [card_image_of_injective _ Fin.val_injective]
    · rintro f (⟨b,rfl⟩|⟨u,hu,rfl⟩|⟨i,hi,_⟩)
      · exact ⟨0,fun A B _ => rfl⟩
      · exact ⟨u.val,fun A B h => h u hu rfl⟩
      · simp at hi
  | @cons i S hS hp ih =>
    obtain ⟨c,hc,ha⟩ := ih
    cases i with
    | unary f =>
      obtain ⟨k,hk⟩ := ha f (hp f (by simp [Instr.pins]))
      refine ⟨c,by simpa [Instr.isBin],?_⟩
      intro g hg
      rcases available_cons_iff.mp hg with rfl|hg
      · exact ⟨k,fun A B h => by simp [Instr.result,neg,hk A B h]⟩
      · exact ha g hg
    | binary o f g =>
      obtain ⟨a,haf⟩ := ha f (hp f (by simp [Instr.pins]))
      obtain ⟨b,hbg⟩ := ha g (hp g (by simp [Instr.pins]))
      have hcard := card_merge V c a b
      refine ⟨merge a b ∘ c,by simp [List.filter_cons,Instr.isBin]; omega,?_⟩
      intro k hk
      rcases available_cons_iff.mp hk with rfl|hk
      · have e : merge a b a = a := by simp [merge]
        have h₁ := dep_merge (a := a) (b := b) haf
        rw [e] at h₁
        have h₂ : Depends V (merge a b ∘ c) a g := by simpa [merge] using dep_merge (a := a) (b := b) hbg
        exact ⟨a,fun A B h => by simp [Instr.result,bin,h₁ A B h,h₂ A B h]⟩
      · obtain ⟨j,hj⟩ := ha k hk
        exact ⟨merge a b j,dep_merge hj⟩

lemma essential_edge {E : Edges n q} (hd : ∀ t v, E t v v = false)
    {V : Finset (Fin n)} {c : Fin n → ℕ} {k : ℕ} {t : Fin q}
    (hdep : Depends V c k (target E V t)) {u v : Fin n}
    (hu : u ∈ V) (hv : v ∈ V) (he : E t u v = true) : c u = k ∧ c v = k := by
  have hhit : target E V t {u,v} = true := by
    have hsub : ({u,v} : Finset (Fin n)) ⊆ V := insert_subset hu (singleton_subset_iff.mpr hv)
    have h : Hit E t {u,v} := ⟨u,by simp,v,by simp,he⟩
    simp [target,inter_eq_left.mpr hsub,h]
  constructor
  · by_contra hn
    have ht := hdep {u,v} {v} (fun w _ hw => by
      have : w ≠ u := fun h => hn (h ▸ hw)
      simp [input,this])
    rw [hhit,target_false_small hd V t (by simp)] at ht
    cases ht
  · by_contra hn
    have ht := hdep {u,v} {u} (fun w _ hw => by
      have : w ≠ v := fun h => hn (h ▸ hw)
      simp [input,this])
    rw [hhit,target_false_small hd V t (by simp)] at ht
    cases ht

lemma abstract_base {E : Edges n q} (hd : ∀ t v, E t v v = false)
    (V : Finset (Fin n)) (p b : ℕ) (hV : 2 ≤ V.card) (hC : ConnectedOn E V)
    (hF : AFits E V p b) : V.card ≤ p+1 := by
  obtain ⟨S,hS,hT,hp,hb⟩ := hF
  obtain ⟨c,hc,ha⟩ := component_bound hS
  obtain ⟨u,hu⟩ := card_pos.mp (show 0 < V.card by omega)
  let U := V.filter (fun v => c v = c u)
  have hne : U.Nonempty := ⟨u,by simp [U,hu]⟩
  have hs : U ⊆ V := filter_subset _ _
  have he : U = V := by
    by_contra hn
    obtain ⟨v,hv,w,hw,t,he⟩ := hC U hne (Finset.ssubset_iff_subset_ne.mpr ⟨hs,hn⟩)
    obtain ⟨k,hk⟩ := ha _ (hT t)
    obtain ⟨ev,ew⟩ := essential_edge hd hk (hs hv) (mem_sdiff.mp hw).1 he
    have he' : c w = c u := ew.trans (ev.symm.trans (mem_filter.mp hv).2)
    exact (mem_sdiff.mp hw).2 (mem_filter.mpr ⟨(mem_sdiff.mp hw).1,he'⟩)
  have hsub : V.image c ⊆ {c u} := by
    intro k hk
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hk
    have hv' : v ∈ U := he.symm ▸ hv
    exact mem_singleton.mpr (mem_filter.mp hv').2
  have hcard := card_le_card hsub
  simp at hcard
  omega
end PEqualNP.Outside.L_lib_1394_aux

open PEqualNP.Outside.L_lib_1394_aux

theorem PEqualNP.Outside.L_lib_1394 :
    ∀ (n q : Nat) (E : Fin q → Fin n → Fin n → Bool),
      (∀ t u v, E t u v = E t v u) → (∀ t v, E t v v = false) →
      let hit := fun (t : Fin q) (A : Finset (Fin n)) => ∃ u ∈ A, ∃ v ∈ A, E t u v = true
      let live := fun (V : Finset (Fin n)) => ∀ u ∈ V, ∃ t, ∃ v ∈ V, E t u v = true
      let blocked := fun (V : Finset (Fin n)) => ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
        let P : Finset (Fin n) := {u,v}
        ∃ (t z : Fin q) (A B : Finset (Fin n)), A ⊆ V \ P ∧ B ⊆ V \ P ∧
          A.card ≤ 1 ∧ B.card ≤ 1 ∧ hit t (A ∪ P) ∧ hit z (B ∪ P) ∧
          ∃ J ⊆ P, ¬ (hit t (A ∪ J) ↔ hit z (B ∪ J))
      let fit := fun (V : Finset (Fin n)) (p b : Nat) =>
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → Nat),
          PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
          C.output < n+2+C.size ∧ (∀ t, tap t < n+2+C.size) ∧
          C.size - PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
          ∀ A : Finset (Fin n), ∀ t,
            (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ A)) ++ [false,true])).getD (tap t) false =
              decide (hit t (A ∩ V))
      (∀ (V : Finset (Fin n)) (p b : Nat), 2 ≤ V.card → live V → blocked V → fit V p b →
        ∃ v ∈ V, ∃ s, s+2 ≤ p ∧ fit (V.erase v) s b) ∧
      (∀ k p b : Nat, k+2 ≤ n →
        (∀ V : Finset (Fin n), n < V.card+k → live V ∧ blocked V) →
        (∀ V : Finset (Fin n), V.card+k = n → ∀ U : Finset (Fin n), U.Nonempty → U ⊂ V →
          ∃ u ∈ U, ∃ v ∈ V \ U, ∃ t, E t u v = true) →
        fit Finset.univ p b → n+k ≤ p+1) ∧
      ∀ p b : Nat, 2 ≤ n → (∀ u v : Fin n, u ≠ v → ∃ t, E t u v = true) →
        fit Finset.univ p b → 2*n ≤ p+3 := by
  classical
  intro n q E _ hd
  let F : Finset (Fin n) → ℕ → ℕ → Prop := Physical E
  have step (V : Finset (Fin n)) (p b : ℕ) :
      2 ≤ V.card → Live E V → Blocked E V → F V p b →
      ∃ v ∈ V, ∃ s, s+2 ≤ p ∧ F (V.erase v) s b := by
    intro hc hl hB hF
    obtain ⟨v,hv,s,hs,h⟩ := abstract_step hd V p b hc hl hB (fit_to_abstract hF)
    exact ⟨v,hv,s,hs,abstract_to_fit h⟩
  have base (V : Finset (Fin n)) (p b : ℕ) :
      2 ≤ V.card → ConnectedOn E V → F V p b → V.card ≤ p+1 :=
    fun hc hC hf => abstract_base hd V p b hc hC (fit_to_abstract hf)
  have complete (p b : ℕ) (hn : 2 ≤ n)
      (hE : ∀ u v, u ≠ v → ∃ t, E t u v = true) (hF : F Finset.univ p b) :
      2*n ≤ p+3 := by
    have h := iterate F step base (n-2) p b (by omega) (fun V hV =>
      ⟨complete_live hE (by omega),complete_blocked hd hE (by omega)⟩)
      (fun V _ => complete_connected hE V) hF
    omega
  have h := And.intro step (And.intro (iterate F step base) complete)
  simpa only [F,Physical,inp,target,Hit,Live,Blocked,ConnectedOn] using h
