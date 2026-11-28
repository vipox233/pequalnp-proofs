import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29730_aux.Compiler

/- The scheduling kernel, Boolean primitives, and Fin-indexed composition below are
   adapted from lean/PEqualNP/Outside/L_meta_25484.lean at
   bc21b4f27602583bf81c0d856bd76641e8a9e9d7 (GateBridge and Build25484).
   The library exposes them to the one-file candidate and adds word and output interfaces. -/

namespace GateBridge

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

variable {α : Type*}

/-- Every label in `S` is already represented by a wire. The circuit's output is not yet fixed. -/
def Scheduled (n : ℕ) (F : α → (Fin n → Bool) → Bool) (k : ℕ) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : ℕ, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x

theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem start {n : ℕ} {F : α → (Fin n → Bool) → Bool}
    (input : Fin n → α) (h : ∀ i x, F (input i) x = x i) :
    Scheduled n F 0 (Set.range input) := by
  refine ⟨[], rfl, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp [FanInTwo]
  · intro a ha
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    refine ⟨i.val, by simpa using i.isLt, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn, h i x]

theorem restrict {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k S) (hsub : T ⊆ S) : Scheduled n F k T := by
  obtain ⟨gs, hs, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hr, hf, fun a ha => hw a (hsub ha)⟩

theorem realizeDeps {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : ℕ, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x)
    (deps : List α) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List ℕ, is.length = deps.length ∧ (∀ i ∈ is, i < n + k) ∧
      ∀ x : Fin n → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => F a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

/-- Append one gate, retaining every old label even if the new label was already available. -/
theorem push {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    (h : Scheduled n F k S) (op : GateOp) (deps : List α) (out : α)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, F out x = op.eval (deps.map fun a => F a x)) :
    Scheduled n F (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin n → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + k := by
    rw [wireLength]
    simpa using congrArg (n + ·) hgs
  have hsnoc (x : Fin n → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    change g' ∈ gs ++ [g] at hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · have heq : g' = g := List.mem_singleton.mp hg'
      subst g'
      refine ⟨hop, ?_⟩
      change is.length ≤ 2
      simpa only [his] using hlen
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨n + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

theorem finish {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α} {out : α}
    (h : Scheduled n F k S) (hout : out ∈ S) :
    ∃ C : Circuit, C.size = k ∧ ReadsBack n C ∧ FanInTwo C ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F out x := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨i, _, hi⟩ := hw out hout
  exact ⟨⟨gs, i⟩, hgs, hr, hf, hi⟩

end GateBridge

namespace Build

open PEqualNP.CircuitLowerBounds

variable {n : Nat}
abbrev Sig (n : Nat) := (Fin n → Bool) → Bool
def Build (A B : Set (Sig n)) (b : Nat) : Prop :=
  True ∧ (∀ {m S}, GateBridge.Scheduled n id m S → A ⊆ S →
    ∃ c ≤ b, GateBridge.Scheduled n id (m+c) (S ∪ B))

theorem Build.run {A B : Set (Sig n)} {b m S} (H : Build A B b)
    (HS : GateBridge.Scheduled n id m S) (hA : A ⊆ S) :
    ∃ c ≤ b, GateBridge.Scheduled n id (m+c) (S ∪ B) := H.2 HS hA

theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : Build A B 0 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

theorem relax {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c,hc,HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c,hc.trans h,GateBridge.restrict HS' (Set.union_subset_union le_rfl hB)⟩

theorem seq {A B C : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A (B ∪ C) (b+c) := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  obtain ⟨d,hd,K⟩ := H.run HS hA
  obtain ⟨e,he,K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d+e,Nat.add_le_add hd he,by simpa [Nat.add_assoc,Set.union_assoc] using K'⟩

theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨1,le_rfl,?_⟩
  have h := GateBridge.push HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridge.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

def an (f g : Sig n) : Sig n := fun x => f x && g x
def or (f g : Sig n) : Sig n := fun x => f x || g x
def nt (f : Sig n) : Sig n := fun x => !f x
def xo (f g : Sig n) : Sig n := fun x => xor (f x) (g x)

theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {an f g} 1 :=
  one .and [f,g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {or f g} 1 :=
  one .or [f,g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, or])

theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : Build A {nt f} 1 :=
  one .not [f] (by simp) (by simp) (by simpa using hf) _ (by simp [GateOp.eval, nt])

theorem xorG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {xo f g} 4 := by
  have he : xo f g = an (or f g) (nt (an f g)) := by
    funext x
    change xor (f x) (g x) = ((f x || g x) && !(f x && g x))
    cases f x <;> cases g x <;> rfl
  rw [he]
  have h₁ := andG hf hg
  have h₂ := orG (A := A ∪ {an f g}) (Or.inl hf) (Or.inl hg)
  have h₃ := notG (A := A ∪ ({an f g} ∪ {or f g})) (f := an f g) (by simp)
  have h₄ := andG (A := A ∪ (({an f g} ∪ {or f g}) ∪ {nt (an f g)}))
    (f := or f g) (g := nt (an f g)) (by simp) (by simp)
  exact relax (seq (seq (seq h₁ h₂) h₃) h₄) le_rfl (by simp) le_rfl

theorem constG {A : Set (Sig n)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b
  · exact one .or [] (by simp) (by simp) (by simp) _ (by intro; rfl)
  · exact one .and [] (by simp) (by simp) (by simp) _ (by intro; rfl)

theorem mixG {A : Set (Sig n)} {f g h : Sig n}
    (hf : f ∈ A) (hg : g ∈ A) (hh : h ∈ A) : Build A {xo (xo f g) h} 8 := by
  exact relax (seq (xorG hf hg)
    (xorG (A := A ∪ {xo f g}) (f := xo f g) (by simp) (Or.inl hh))) le_rfl (by simp) le_rfl

theorem nonlinG {A : Set (Sig n)} {f g h : Sig n}
    (hf : f ∈ A) (hg : g ∈ A) (hh : h ∈ A) :
    Build A {xo f (an (nt g) h)} 6 := by
  have h₁ := notG hg
  have h₂ := andG (A := A ∪ {nt g}) (f := nt g) (by simp) (Or.inl hh)
  have h₃ := xorG (A := A ∪ ({nt g} ∪ {an (nt g) h})) (Or.inl hf)
    (g := an (nt g) h) (by simp)
  exact relax (seq (seq h₁ h₂) h₃) le_rfl (by simp) le_rfl

theorem topological {α : Type*} [DecidableEq α] {A : Set (Sig n)}
    (F : α → Sig n) (rank cost : α → Nat) (s : Finset α)
    (H : ∀ i ∈ s, Build (A ∪ {f | ∃ j ∈ s, rank j < rank i ∧ f = F j}) {F i} (cost i)) :
    Build A {f | ∃ i ∈ s, f = F i} (∑ i ∈ s, cost i) := by
  classical
  induction s using Finset.strongInduction with
  | H s IH =>
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi, himax⟩ := Finset.exists_max_image s rank hs
      have Hsub : s.erase i ⊂ s := Finset.erase_ssubset hi
      have hstep (j : α) (hj : j ∈ s.erase i) (l : α) (hl : l ∈ s)
          (hlt : rank l < rank j) : l ∈ s.erase i := by
        refine Finset.mem_erase.mpr ⟨?_,hl⟩
        intro heq
        subst l
        exact (Nat.not_lt_of_ge (himax j (Finset.mem_of_mem_erase hj))) hlt
      have Hs := IH (s.erase i) Hsub fun j hj =>
        relax (H j (Finset.mem_of_mem_erase hj))
          (by rintro f (hf | ⟨l,hl,hlt,rfl⟩)
              · exact Or.inl hf
              · exact Or.inr ⟨l,hstep j hj l hl hlt,hlt,rfl⟩) le_rfl le_rfl
      have Hi := relax (H i hi) (C := A ∪ {f | ∃ j ∈ s.erase i, f = F j})
        (by rintro f (hf | ⟨j,hj,hlt,rfl⟩)
            · exact Or.inl hf
            · exact Or.inr ⟨j,Finset.mem_erase.mpr ⟨by aesop, hj⟩,rfl⟩) le_rfl le_rfl
      refine relax (seq Hs Hi) le_rfl ?_ ?_
      · rintro f ⟨j,hj,rfl⟩
        by_cases he : j = i
        · exact Or.inr (by simp [he])
        · exact Or.inl ⟨j,Finset.mem_erase.mpr ⟨he,hj⟩,rfl⟩
      · rw [Finset.sum_erase_add _ _ hi]
    · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp)

theorem flipG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) (b : Bool) :
    Build A {fun x => xor (f x) b} 1 := by
  cases b
  · have he : (fun x => xor (f x) false) = f := by funext x; cases f x <;> rfl
    rw [he]
    exact relax (idle (Set.singleton_subset_iff.mpr hf)) le_rfl le_rfl (by omega)
  · have he : (fun x => xor (f x) true) = nt f := by
      funext x
      change xor (f x) true = !f x
      cases f x <;> rfl
    rw [he]
    exact notG hf

theorem anyG {A : Set (Sig n)} (xs : List (Sig n))
    (hs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xs.any (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    exact idle (Set.singleton_subset_iff.mpr hfalse)
  | cons f xs IH =>
    have H := IH (fun g hg => hs g (List.mem_cons_of_mem f hg))
    have K := orG (A := A ∪ {fun x => xs.any (fun g => g x)})
      (Or.inl (hs f List.mem_cons_self)) (Or.inr rfl)
    exact relax (seq H K) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by simp)

theorem allG {α : Type*} [Fintype α] {A : Set (Sig n)}
    (F : α → Sig n) (c : Nat) (H : ∀ i, Build A {F i} c) :
    Build A (Set.range F) (Fintype.card α*c) := by
  classical
  have K := topological F (fun _ => 0) (fun _ => c) Finset.univ
    (fun i _ => relax (H i) Set.subset_union_left le_rfl le_rfl)
  refine relax (by simpa only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] using K) le_rfl ?_ le_rfl
  rintro _ ⟨i,rfl⟩
  exact ⟨i,Finset.mem_univ _,rfl⟩

theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c : Nat)
    (H : ∀ i, Build A {F i} c) : Build A (Set.range F) (k*c) := by
  simpa only [Fintype.card_fin] using allG F c H

theorem notAnyG {A : Set (Sig n)} (xs : List (Sig n))
    (hs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => !(xs.any (fun f => f x))} (xs.length+1) :=
  relax (seq (anyG xs hs hfalse) (notG (f := fun x => xs.any (fun f => f x))
    (Or.inr rfl))) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

def inputs (n : Nat) : Set (Sig n) := Set.range (fun i : Fin n => fun v => v i)

def base (n : Nat) : Set (Sig n) := inputs n ∪ {fun _ => false, fun _ => true}

theorem inputG (n : Nat) : Build (inputs n) {fun _ => false, fun _ => true} 2 := by
  simpa only [Set.singleton_union] using
    (seq (constG (A := inputs n) false) (constG (A := inputs n ∪ {fun _ => false}) true))

theorem thenG {A B C : Set (Sig n)} {b c : Nat}
    (h : Build A B b) (j : Build (A ∪ B) C c) : Build A C (b+c) :=
  relax (seq h j) le_rfl Set.subset_union_right le_rfl

theorem bothG {A B C : Set (Sig n)} {b c : Nat}
    (h : Build A B b) (j : Build A C c) : Build A (B ∪ C) (b+c) :=
  seq h (relax j Set.subset_union_left le_rfl le_rfl)

/-- A bounded straight-line loop retains the ambient inputs and the current state. -/
theorem loopG {A : Set (Sig n)} (F : Nat → Set (Sig n)) {b c t : Nat}
    (hbase : Build A (F 0) b)
    (hstep : ∀ j, j < t → Build (A ∪ F j) (F (j+1)) c) :
    Build A (F t) (b + t*c) := by
  induction t with
  | zero => simpa only [Nat.zero_mul, Nat.add_zero] using hbase
  | succ t ih =>
    have hprev := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
    refine relax (seq hprev (hstep t (Nat.lt_succ_self t))) le_rfl Set.subset_union_right ?_
    rw [Nat.succ_mul, Nat.add_assoc]

def mx (s f g : Sig n) : Sig n := fun x => if s x then g x else f x

theorem muxG {A : Set (Sig n)} {s f g : Sig n} (hs : s ∈ A) (hf : f ∈ A) (hg : g ∈ A) :
    Build A {mx s f g} 4 := by
  have he : mx s f g = or (an (nt s) f) (an s g) := by
    funext x
    change (if s x then g x else f x) = ((!(s x) && f x) || (s x && g x))
    cases s x <;> cases f x <;> cases g x <;> rfl
  rw [he]
  have h₁ := notG hs
  have h₂ := andG (A := A ∪ {nt s}) (f := nt s) (by simp) (Or.inl hf)
  have h₃ := andG (A := A ∪ ({nt s} ∪ {an (nt s) f}))
    (Or.inl hs) (Or.inl hg)
  have h₄ := orG (A := A ∪ (({nt s} ∪ {an (nt s) f}) ∪ {an s g}))
    (f := an (nt s) f) (g := an s g) (by simp) (by simp)
  exact relax (seq (seq (seq h₁ h₂) h₃) h₄) le_rfl (by simp) le_rfl

def eqb (f g : Sig n) : Sig n := fun x => f x == g x

theorem eqG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {eqb f g} 5 := by
  have he : eqb f g = nt (xo f g) := by
    funext x
    change (f x == g x) = !(xor (f x) (g x))
    cases f x <;> cases g x <;> rfl
  rw [he]
  exact relax (seq (xorG hf hg) (notG (A := A ∪ {xo f g}) (f := xo f g) (by simp)))
    le_rfl Set.subset_union_right le_rfl

theorem everyG {A : Set (Sig n)} (xs : List (Sig n))
    (hs : ∀ f ∈ xs, f ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A {fun x => xs.all (fun f => f x)} xs.length := by
  induction xs with
  | nil => exact idle (Set.singleton_subset_iff.mpr htrue)
  | cons f xs ih =>
    have H := ih (fun g hg => hs g (List.mem_cons_of_mem f hg))
    have K := andG (A := A ∪ {fun x => xs.all (fun g => g x)})
      (Or.inl (hs f List.mem_cons_self)) (Or.inr rfl)
    exact relax (seq H K) le_rfl Set.subset_union_right (by simp)

abbrev Word (n w : Nat) := Fin w → Sig n

def Available {w : Nat} (A : Set (Sig n)) (v : Word n w) : Prop := ∀ i, v i ∈ A

/-- A static projection or repeat of wires, with no gates. -/
def select {w t : Nat} (v : Word n w) (f : Fin t → Fin w) : Word n t := v ∘ f

theorem selectG {w t : Nat} {A : Set (Sig n)} {v : Word n w} (f : Fin t → Fin w)
    (hv : Available A v) : Build A (Set.range (select v f)) 0 :=
  idle (by rintro _ ⟨i, rfl⟩; exact hv (f i))

/-- Concatenation is just the embedding of the two ranges of wire indices. -/
def concat {w t : Nat} (a : Word n w) (b : Word n t) : Word n (w+t) := Fin.addCases a b

theorem concatG {w t : Nat} {A : Set (Sig n)} {a : Word n w} {b : Word n t}
    (ha : Available A a) (hb : Available A b) : Build A (Set.range (concat a b)) 0 := by
  apply idle
  rintro _ ⟨i, rfl⟩
  refine Fin.addCases (motive := fun j => concat a b j ∈ A) (fun j => ?_) (fun j => ?_) i
  · simpa only [concat, Fin.addCases_left] using ha j
  · simpa only [concat, Fin.addCases_right] using hb j

theorem wordConstG {w : Nat} {A : Set (Sig n)} (v : Fin w → Bool)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A (Set.range (fun (i : Fin w) (_ : Fin n → Bool) => v i)) 0 := by
  apply idle
  rintro _ ⟨i, rfl⟩
  cases hi : v i
  · simpa only [hi] using hfalse
  · simpa only [hi] using htrue

theorem wordNotG {w : Nat} {A : Set (Sig n)} {v : Word n w} (hv : Available A v) :
    Build A (Set.range (fun i => nt (v i))) w := by
  simpa only [Nat.mul_one] using finG (fun i => nt (v i)) 1 (fun i => notG (hv i))

theorem wordAndG {w : Nat} {A : Set (Sig n)} {v u : Word n w}
    (hv : Available A v) (hu : Available A u) :
    Build A (Set.range (fun i => an (v i) (u i))) w := by
  simpa only [Nat.mul_one] using finG (fun i => an (v i) (u i)) 1 (fun i => andG (hv i) (hu i))

theorem wordOrG {w : Nat} {A : Set (Sig n)} {v u : Word n w}
    (hv : Available A v) (hu : Available A u) :
    Build A (Set.range (fun i => or (v i) (u i))) w := by
  simpa only [Nat.mul_one] using finG (fun i => or (v i) (u i)) 1 (fun i => orG (hv i) (hu i))

theorem wordXorG {w : Nat} {A : Set (Sig n)} {v u : Word n w}
    (hv : Available A v) (hu : Available A u) :
    Build A (Set.range (fun i => xo (v i) (u i))) (w*4) :=
  finG _ 4 (fun i => xorG (hv i) (hu i))

theorem wordMuxG {w : Nat} {A : Set (Sig n)} {s : Sig n} {v u : Word n w}
    (hs : s ∈ A) (hv : Available A v) (hu : Available A u) :
    Build A (Set.range (fun i => mx s (v i) (u i))) (w*4) :=
  finG _ 4 (fun i => muxG hs (hv i) (hu i))

def wordEq {w : Nat} (v u : Word n w) : Sig n :=
  fun x => (List.ofFn (fun i => eqb (v i) (u i))).all (fun f => f x)

theorem wordEq_eq_true {w : Nat} {v u : Word n w} {x : Fin n → Bool} :
    wordEq v u x = true ↔ ∀ i, v i x = u i x := by
  simp only [wordEq, List.all_eq_true, List.mem_ofFn]
  constructor
  · intro h i
    simpa [eqb] using h (eqb (v i) (u i)) ⟨i, rfl⟩
  · rintro h _ ⟨i, rfl⟩
    simp [eqb, h i]

theorem wordEqG {w : Nat} {A : Set (Sig n)} {v u : Word n w}
    (hv : Available A v) (hu : Available A u) (htrue : (fun _ => true) ∈ A) :
    Build A {wordEq v u} (w*5+w) := by
  let E : Word n w := fun i => eqb (v i) (u i)
  have h₁ : Build A (Set.range E) (w*5) := finG E 5 (fun i => eqG (hv i) (hu i))
  have h₂ : Build (A ∪ Set.range E) {wordEq v u} (List.ofFn E).length :=
    everyG (List.ofFn E) (fun _ hf => Or.inr (Set.mem_range.mpr (List.mem_ofFn.mp hf))) (Or.inl htrue)
  exact relax (seq h₁ h₂) le_rfl Set.subset_union_right (by simp)

/-- Scan multiplexers over a statically enumerated table. Selectors are built separately
    and may be reused between output bits. With no true selector the result is `fallback`. -/
def scanMux (s v : Nat → Sig n) (fallback : Sig n) : Nat → Sig n
  | 0 => fallback
  | j+1 => mx (s j) (scanMux s v fallback j) (v j)

theorem scanMuxG {A : Set (Sig n)} {s v : Nat → Sig n} {fallback : Sig n} {t : Nat}
    (hs : ∀ j, j < t → s j ∈ A) (hv : ∀ j, j < t → v j ∈ A) (hf : fallback ∈ A) :
    Build A {scanMux s v fallback t} (t*4) := by
  have H := loopG (fun j => {scanMux s v fallback j}) (b := 0) (c := 4) (t := t)
    (idle (Set.singleton_subset_iff.mpr hf))
    (fun j hj => muxG (Or.inl (hs j hj)) (Or.inr rfl) (Or.inl (hv j hj)))
  simpa only [Nat.zero_add] using H

theorem scanMux_index {s v : Nat → Sig n} {fallback : Sig n} {x : Fin n → Bool}
    {j t : Nat} (hs : ∀ i, i < t → s i x = decide (j = i)) :
    scanMux s v fallback t x = if j < t then v j x else fallback x := by
  induction t with
  | zero => simp [scanMux]
  | succ t ih =>
    rw [scanMux, mx, hs t (Nat.lt_succ_self t)]
    by_cases he : j = t
    · subst j
      simp
    · have hj : j < t + 1 ↔ j < t := by omega
      simpa only [he, decide_false, Bool.false_eq_true, ite_false, hj] using
        ih (fun i hi => hs i (Nat.lt_succ_of_lt hi))

theorem scanWordG {w : Nat} {A : Set (Sig n)} {s : Nat → Sig n}
    {v : Nat → Word n w} {fallback : Word n w} {t : Nat}
    (hs : ∀ j, j < t → s j ∈ A) (hv : ∀ j, j < t → Available A (v j))
    (hf : Available A fallback) :
    Build A (Set.range (fun i => scanMux s (fun j => v j i) (fallback i) t)) (w*(t*4)) :=
  finG _ _ (fun i => scanMuxG hs (fun j hj => hv j hj i) (hf i))

/-- Extract one circuit and all requested wire indices at once. An index is chosen before
    quantifying over inputs; the circuit therefore realizes these signals simultaneously. -/
theorem finishMany {w b : Nat} {live : Sig n} {v : Word n w}
    (H : Build (inputs n) ({live} ∪ Set.range v) b) :
    ∃ (C : Circuit) (ws : Fin w → Fin (n+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      C.output < n+C.size ∧ C.size ≤ b ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = live x ∧
        ∀ i, (C.wires (List.ofFn x)).getD (ws i).val false = v i x := by
  have hs : GateBridge.Scheduled n id 0 (inputs n) :=
    GateBridge.start (F := id) (fun (i : Fin n) x => x i) (fun _ _ => rfl)
  obtain ⟨c, hc, hcirc⟩ := H.run hs le_rfl
  simp only [Nat.zero_add] at hcirc
  obtain ⟨gs, hgs, hback, hfan, hw⟩ := hcirc
  obtain ⟨j, hj, hval⟩ := hw live (Or.inr (Or.inl rfl))
  have hbits (i : Fin w) := hw (v i) (Or.inr (Or.inr ⟨i, rfl⟩))
  choose ws hws hvalues using hbits
  refine ⟨⟨gs, j⟩, (fun i => ⟨ws i, ?_⟩), hfan, hback, ?_, ?_, ?_⟩
  · simpa only [Circuit.size, hgs] using hws i
  · simpa only [Circuit.size, hgs] using hj
  · simpa only [Circuit.size, hgs] using hc
  · intro x
    exact ⟨hval x, fun i => hvalues i x⟩

def listInput (x : List Bool) (hx : x.length = n) : Fin n → Bool :=
  fun i => x.get (i.cast hx.symm)

@[simp] theorem ofFn_listInput (x : List Bool) (hx : x.length = n) :
    List.ofFn (listInput x hx) = x := by
  subst n
  exact List.ofFn_get x

theorem listInput_getD (x : List Bool) (hx : x.length = n) (i : Fin n) :
    listInput x hx i = x.getD i.val false := by
  rw [List.getD_eq_getElem _ _ (by simpa only [hx] using i.isLt)]
  rfl

/- The ripple adder and its arithmetic semantics are adapted from
   lean/PEqualNP/Outside/L_meta_25940.lean at bc21b4f27602583bf81c0d856bd76641e8a9e9d7. -/
theorem relaxKeep {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ C ∪ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c, hc, HS'⟩ := H.run HS (hA.trans hC)
  refine ⟨c, hc.trans h, GateBridge.restrict HS' ?_⟩
  intro f hf
  rcases hf with hs | hd
  · exact Or.inl hs
  · rcases hB hd with hc | hb
    · exact Or.inl (hC hc)
    · exact Or.inr hb

theorem xor_eq_or_and_not_and (a b : Bool) :
    xor a b = ((a || b) && !(a && b)) := by
  cases a <;> cases b <;> rfl


def faSum (a b c : Bool) : Bool := xor (xor a b) c

def faCarry (a b c : Bool) : Bool := (a && b) || (xor a b && c)

theorem fullAdderB {N : ℕ} {A : Set (Sig N)} {fa fb fc : Sig N}
    (ha : fa ∈ A) (hb : fb ∈ A) (hc : fc ∈ A) :
    Build A ({fun x => faSum (fa x) (fb x) (fc x), fun x => faCarry (fa x) (fb x) (fc x)}) 9 := by
  let abOr : Sig N := fun x => fa x || fb x
  let abAnd : Sig N := fun x => fa x && fb x
  let abNand : Sig N := fun x => !(abAnd x)
  let t1 : Sig N := fun x => abOr x && abNand x
  let tcOr : Sig N := fun x => t1 x || fc x
  let tcAnd : Sig N := fun x => t1 x && fc x
  let tcNand : Sig N := fun x => !(tcAnd x)
  let sOut : Sig N := fun x => tcOr x && tcNand x
  let cOut : Sig N := fun x => abAnd x || tcAnd x
  have h1 : Build A {abOr} 1 := orG ha hb
  have h2 : Build (A ∪ {abOr}) {abAnd} 1 := andG (Or.inl ha) (Or.inl hb)
  have h3 : Build (A ∪ ({abOr} ∪ {abAnd})) {abNand} 1 := notG (Or.inr (Or.inr rfl))
  have h4 : Build (A ∪ (({abOr} ∪ {abAnd}) ∪ {abNand})) {t1} 1 :=
    andG (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have h5 : Build (A ∪ ((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1})) {tcOr} 1 :=
    orG (Or.inr (Or.inr rfl)) (Or.inl hc)
  have h6 : Build (A ∪ (((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr})) {tcAnd} 1 :=
    andG (Or.inr (Or.inl (Or.inr rfl))) (Or.inl hc)
  have h7 : Build (A ∪ ((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd})) {tcNand} 1 :=
    notG (Or.inr (Or.inr rfl))
  have h8 : Build (A ∪ (((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand})) {sOut} 1 :=
    andG (Or.inr (Or.inl (Or.inl (Or.inr rfl)))) (Or.inr (Or.inr rfl))
  have h9 : Build (A ∪ ((((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand}) ∪ {sOut})) {cOut} 1 :=
    orG (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl))))))))
        (Or.inr (Or.inl (Or.inl (Or.inr rfl))))
  have hall := seq (seq (seq (seq (seq (seq (seq (seq h1 h2) h3) h4) h5) h6) h7) h8) h9
  have hsEq : sOut = fun x => faSum (fa x) (fb x) (fc x) := by
    funext x
    simp only [sOut, tcOr, tcNand, tcAnd, t1, abOr, abNand, abAnd, faSum]
    rw [xor_eq_or_and_not_and (fa x) (fb x), xor_eq_or_and_not_and _ (fc x)]
  have hcEq : cOut = fun x => faCarry (fa x) (fb x) (fc x) := by
    funext x
    simp only [cOut, tcAnd, t1, abOr, abNand, abAnd, faCarry]
    rw [xor_eq_or_and_not_and (fa x) (fb x)]
  refine relaxKeep hall le_rfl ?_ (by omega)
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · rw [← hsEq]
    exact Or.inr (Or.inl (Or.inr rfl))
  · rw [← hcEq]
    exact Or.inr (Or.inr rfl)

def rippleCarry (a b : ℕ) : ℕ → Bool
  | 0 => false
  | j + 1 => faCarry (a.testBit j) (b.testBit j) (rippleCarry a b j)

theorem testBit_eq_decide_div_mod (x j : ℕ) :
    x.testBit j = decide ((x / 2 ^ j) % 2 = 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  have hlt : (x / 2 ^ j) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hcases : (x / 2 ^ j) % 2 = 0 ∨ (x / 2 ^ j) % 2 = 1 := by omega
  rcases hcases with h | h <;> simp [h]

theorem mod_two_pow_succ_eq (a j : ℕ) :
    a % 2 ^ (j + 1) = a % 2 ^ j + (if a.testBit j then 2 ^ j else 0) := by
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdiv1 := Nat.div_add_mod a (2 ^ j)
  have hdiv2 := Nat.div_add_mod (a / 2 ^ j) 2
  have ha_eq : a = (a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2)) + 2 ^ (j + 1) * (a / 2 ^ j / 2) := by
    rw [Nat.pow_succ]
    have h1 : 2 ^ j * (a / 2 ^ j) = 2 ^ j * (2 * (a / 2 ^ j / 2) + (a / 2 ^ j) % 2) := by
      rw [hdiv2]
    rw [Nat.mul_add] at h1
    have h2 : 2 ^ j * (2 * (a / 2 ^ j / 2)) = 2 ^ j * 2 * (a / 2 ^ j / 2) := by ring
    omega
  have hlt_rem : a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) < 2 ^ (j + 1) := by
    have h1 : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ hpos
    have h2 : (a / 2 ^ j) % 2 ≤ 1 := by have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
    have h3 : 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j := by
      calc 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j * 1 := Nat.mul_le_mul_left _ h2
        _ = 2 ^ j := Nat.mul_one _
    rw [Nat.pow_succ]; omega
  have h1 : a % 2 ^ (j + 1) = a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) := by
    conv_lhs => rw [ha_eq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_rem]
  rw [h1, testBit_eq_decide_div_mod a j]
  have hcases : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  rcases hcases with h | h <;> simp [h]

theorem rippleCarry_spec (a b : ℕ) :
    ∀ j : ℕ,
      rippleCarry a b j = decide (2 ^ j ≤ a % 2 ^ j + b % 2 ^ j) ∧
      (a + b).testBit j = faSum (a.testBit j) (b.testBit j) (rippleCarry a b j) := by
  intro j
  have hcarry : ∀ k : ℕ, rippleCarry a b k = decide (2 ^ k ≤ a % 2 ^ k + b % 2 ^ k) := by
    intro k
    induction k with
    | zero => simp [rippleCarry, Nat.mod_one]
    | succ k ih =>
      unfold rippleCarry
      rw [ih, mod_two_pow_succ_eq a k, mod_two_pow_succ_eq b k]
      have ha_lt : a % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hb_lt : b % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      cases h1 : a.testBit k <;> cases h2 : b.testBit k <;>
        by_cases h3 : 2 ^ k ≤ a % 2 ^ k + b % 2 ^ k <;>
        simp [faCarry, h3, hp] <;> omega
  refine ⟨hcarry j, ?_⟩
  rw [hcarry j]
  have hdiv : (a + b) / 2 ^ j =
      a / 2 ^ j + b / 2 ^ j + (a % 2 ^ j + b % 2 ^ j) / 2 ^ j := by
    have ha := Nat.div_add_mod a (2 ^ j)
    have hb := Nat.div_add_mod b (2 ^ j)
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    have hsum : a + b = (a % 2 ^ j + b % 2 ^ j) + (a / 2 ^ j + b / 2 ^ j) * 2 ^ j := by
      have : 2 ^ j * (a / 2 ^ j) = (a / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      have : 2 ^ j * (b / 2 ^ j) = (b / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      rw [Nat.add_mul]; omega
    rw [hsum, Nat.add_mul_div_right _ _ hpos]
    omega
  have hcdiv : (a % 2 ^ j + b % 2 ^ j) / 2 ^ j = if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0 := by
    have ha_lt : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    have hb_lt : b % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    by_cases hle : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j
    · simp only [hle, ↓reduceIte]
      have hsub : a % 2 ^ j + b % 2 ^ j = (a % 2 ^ j + b % 2 ^ j - 2 ^ j) + 1 * 2 ^ j := by omega
      rw [hsub, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt (by omega)]
    · simp only [hle, ↓reduceIte]
      exact Nat.div_eq_of_lt (by omega)
  rw [testBit_eq_decide_div_mod (a + b) j, testBit_eq_decide_div_mod a j,
    testBit_eq_decide_div_mod b j, hdiv, hcdiv]
  have ha2 : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  have hb2 : (b / 2 ^ j) % 2 = 0 ∨ (b / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (b / 2 ^ j) (by omega : 0 < 2); omega
  have hmod : (a / 2 ^ j + b / 2 ^ j + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 =
      ((a / 2 ^ j) % 2 + (b / 2 ^ j) % 2 + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 := by
    omega
  rw [hmod]
  by_cases hc : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j <;>
  rcases ha2 with ha | ha <;>
  rcases hb2 with hb | hb <;>
  simp [faSum, hc, ha, hb]

def bitsOf {N : ℕ} (L : ℕ) (F : (Fin N → Bool) → ℕ) : Fin L → Sig N :=
  fun j x => (F x).testBit j.val

theorem rippleB {N : ℕ} {A : Set (Sig N)} (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) :
    ∀ L : ℕ,
      (∀ j : Fin L, (fun x => (F x).testBit j.val) ∈ A) →
      (∀ j : Fin L, (fun x => (G x).testBit j.val) ∈ A) →
      Build A
        ((Set.range (bitsOf L (fun x => F x + G x))) ∪ {fun x => rippleCarry (F x) (G x) L})
        (9 * L) := by
  intro L
  induction L with
  | zero =>
    intro _ _
    simp only [Nat.mul_zero]
    apply idle
    intro f hf
    rcases hf with ⟨j, _⟩ | rfl
    · exact Fin.elim0 j
    · exact hfalse
  | succ L ih =>
    intro hF hG
    have hprev := ih (fun j => hF j.castSucc) (fun j => hG j.castSucc)
    have hstep : Build
        (A ∪ (Set.range (bitsOf L (fun x => F x + G x)) ∪ {fun x => rippleCarry (F x) (G x) L}))
        ({fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L),
          fun x => faCarry ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L)}) 9 :=
      fullAdderB (Or.inl (hF (Fin.last L))) (Or.inl (hG (Fin.last L))) (Or.inr (Or.inr rfl))
    have hseq := seq hprev hstep
    refine relaxKeep hseq le_rfl ?_ (by omega)
    intro f hf
    rcases hf with ⟨j, rfl⟩ | rfl
    · by_cases hj : j.val < L
      · have hjeq : bitsOf (L + 1) (fun x => F x + G x) j =
            bitsOf L (fun x => F x + G x) ⟨j.val, hj⟩ := rfl
        rw [hjeq]
        exact Or.inr (Or.inl (Or.inl ⟨⟨j.val, hj⟩, rfl⟩))
      · have hjeq : j.val = L := by omega
        have hfeq : bitsOf (L + 1) (fun x => F x + G x) j =
            fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L) := by
          funext x
          unfold bitsOf
          rw [hjeq]
          exact (rippleCarry_spec (F x) (G x) L).2
        rw [hfeq]
        exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem sumTwoB {N : ℕ} {A : Set (Sig N)} (L : ℕ) (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A)
    (hG : ∀ j : Fin L, bitsOf L G j ∈ A) :
    Build A (Set.range (bitsOf L (fun x => F x + G x))) (9 * L) :=
  relaxKeep (rippleB F G hfalse L hF hG) le_rfl
    (fun _ hf => Or.inr (Or.inl hf)) le_rfl


def geWord (F T : (Fin n → Bool) → Nat) : Sig n := fun x => decide (T x ≤ F x)

def guardedSub (F T : (Fin n → Bool) → Nat) : (Fin n → Bool) → Nat :=
  fun x => if T x ≤ F x then F x - T x else F x

theorem rippleCarry_complement {a c w : Nat} (ha : a < 2^w) (hc : 0 < c) (hc' : c ≤ 2^w) :
    rippleCarry a (2^w-c) w = decide (c ≤ a) := by
  have hb : 2^w-c < 2^w := by omega
  rw [(rippleCarry_spec a (2^w-c) w).1, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : c ≤ a
  · have h' : 2^w ≤ a + (2^w-c) := by omega
    simp [h, h']
  · have h' : ¬ 2^w ≤ a + (2^w-c) := by omega
    simp [h, h']

theorem testBit_complement_sub {a c w i : Nat} (hc : c ≤ a) (hc' : c ≤ 2^w) (hi : i < w) :
    (a + (2^w-c)).testBit i = (a-c).testBit i := by
  rw [show a + (2^w-c) = 2^w + (a-c) by omega, Nat.testBit_two_pow_add_gt hi]

/-- A positive threshold may vary with the input. The supplied word is its two's
    complement `2^w - T`, so a final carry detects the branch `T ≤ F`. -/
theorem guardedSubG {w : Nat} {A : Set (Sig n)} {F T : (Fin n → Bool) → Nat}
    (hF : ∀ x, F x < 2^w) (hT : ∀ x, 0 < T x) (hT' : ∀ x, T x ≤ 2^w)
    (hf : Available A (bitsOf w F))
    (ht : Available A (bitsOf w (fun x => 2^w - T x)))
    (hfalse : (fun _ => false) ∈ A) :
    Build A (Set.range (bitsOf w (guardedSub F T)) ∪ {geWord F T}) (13*w) := by
  let S : Word n w := bitsOf w (fun x => F x + (2^w - T x))
  let B : Set (Sig n) := Set.range S ∪ {geWord F T}
  have he : (fun x => rippleCarry (F x) (2^w - T x) w) = geWord F T := by
    funext x
    exact rippleCarry_complement (hF x) (hT x) (hT' x)
  have ha : Build A B (9*w) := by
    unfold B S
    rw [← he]
    exact rippleB F (fun x => 2^w - T x) hfalse w hf ht
  have hm : Build (A ∪ B) (Set.range (fun i => mx (geWord F T) (bitsOf w F i) (S i))) (w*4) :=
    wordMuxG (Or.inr (Or.inr rfl)) (fun i => Or.inl (hf i)) (fun i => Or.inr (Or.inl ⟨i, rfl⟩))
  refine relax (seq ha hm) le_rfl ?_ (by omega)
  rintro f (⟨i, rfl⟩ | rfl)
  · apply Or.inr
    refine ⟨i, ?_⟩
    funext x
    by_cases h : T x ≤ F x
    · simpa [mx, geWord, bitsOf, S, guardedSub, h] using testBit_complement_sub h (hT' x) i.isLt
    · simp [mx, geWord, bitsOf, S, guardedSub, h]
  · exact Or.inl (Or.inr rfl)

theorem guardedSubConstG {w : Nat} {A : Set (Sig n)} {F : (Fin n → Bool) → Nat}
    (c : Nat) (hc : c ≤ 2^w) (hF : ∀ x, F x < 2^w) (hf : Available A (bitsOf w F))
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A (Set.range (bitsOf w (guardedSub F (fun _ => c))) ∪ {geWord F (fun _ => c)}) (13*w) := by
  by_cases hz : c = 0
  · subst c
    have he : guardedSub F (fun _ => 0) = F := by funext x; simp [guardedSub]
    have hg : geWord F (fun _ => 0) = (fun _ => true) := by funext x; simp [geWord]
    rw [he, hg]
    have h0 : Build A (Set.range (bitsOf w F) ∪ {fun _ => true}) 0 := by
      apply idle
      rintro _ (⟨i, rfl⟩ | rfl)
      · exact hf i
      · exact htrue
    exact relax h0 le_rfl le_rfl (Nat.zero_le _)
  · refine guardedSubG hF (fun _ => Nat.pos_of_ne_zero hz) (fun _ => hc) hf ?_ hfalse
    intro i
    have hcbit (b : Bool) : (fun _ : Fin n → Bool => b) ∈ A := by
      cases b
      · exact hfalse
      · exact htrue
    exact hcbit ((2^w-c).testBit i.val)

end Build

end PEqualNP.Outside.L_meta_29730_aux.Compiler

namespace PEqualNP.Outside.L_meta_29730_aux.WeightedAddress

open scoped BigOperators

def leaf (q hits : Nat) : Nat := if hits < q then 2 ^ q else 1

def total (q : Nat) : Nat → Nat → Nat
  | 0, hits => leaf q hits
  | m + 1, hits => total q m hits + total q m (hits + 1)

private theorem pascal (m : Nat) (f : Nat → Nat) :
    (∑ j ∈ Finset.range (m + 2), (m + 1).choose j * f j) =
    (∑ j ∈ Finset.range (m + 1), m.choose j * f j) +
    (∑ j ∈ Finset.range (m + 1), m.choose j * f (j + 1)) := by
  have hs := Finset.sum_range_succ (fun j => m.choose j * f j) (m + 1)
  have hs' := Finset.sum_range_succ' (fun j => m.choose j * f j) (m + 1)
  rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self m), zero_mul, add_zero] at hs
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, one_mul] at hs' ⊢
  simp_rw [Nat.choose_succ_succ', add_mul, Finset.sum_add_distrib]
  omega

theorem total_eq_sum (q m hits : Nat) :
    total q m hits = ∑ j ∈ Finset.range (m + 1), m.choose j * leaf q (hits + j) := by
  induction m generalizing hits with
  | zero => simp [total]
  | succ m ih =>
    rw [total, ih hits, ih (hits + 1), pascal m (fun j => leaf q (hits + j))]
    simp only [Nat.add_assoc, Nat.add_comm 1]

theorem root_eq_sum (q m : Nat) :
    total q m 0 = ∑ j ∈ Finset.range (m + 1), m.choose j * (if j < q then 2 ^ q else 1) := by
  simpa only [Nat.zero_add, leaf] using total_eq_sum q m 0

theorem total_pos (q m hits : Nat) : 0 < total q m hits := by
  induction m generalizing hits with
  | zero => simp [total, leaf]; split <;> positivity
  | succ m ih => simpa only [total] using Nat.add_pos_left (ih hits) (total q m (hits + 1))

theorem total_le (q m hits : Nat) : total q m hits ≤ 2 ^ (m + q) := by
  induction m generalizing hits with
  | zero =>
    simp only [total, leaf, Nat.zero_add]
    split
    · exact Nat.le_refl _
    · exact Nat.two_pow_pos q
  | succ m ih =>
    rw [total, show m + 1 + q = m + q + 1 by omega, pow_succ, Nat.mul_two]
    exact Nat.add_le_add (ih hits) (ih (hits + 1))

def pop (m word : Nat) : Nat := ((List.range m).filter word.testBit).length

@[simp] theorem pop_zero (word : Nat) : pop 0 word = 0 := rfl

theorem pop_bit (m : Nat) (b : Bool) (word : Nat) :
    pop (m + 1) (Nat.bit b word) = pop m word + b.toNat := by
  unfold pop
  rw [List.range_succ_eq_map]
  simp only [List.filter_cons, Nat.testBit_bit_zero, List.filter_map]
  have hp : (Nat.bit b word).testBit ∘ Nat.succ = word.testBit := by
    funext i
    simp [Nat.testBit_succ]
  rw [hp]
  cases b <;> simp

/-- One comparison and one conditional subtraction at each position. The chosen
    bit goes into the least significant position of the remaining word. -/
def unrankWith (T : Nat → Nat → Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, _, ticket => (0, ticket)
  | m + 1, hits, ticket =>
    let left := T m hits
    let b : Bool := decide (left ≤ ticket)
    let tail := unrankWith T m (hits + b.toNat) (if b then ticket - left else ticket)
    (Nat.bit b tail.1, tail.2)

def unrank (q : Nat) := unrankWith (total q)

/-- Forward version for a circuit: one round writes bit `pos`, increments
    the hit counter if needed, and conditionally subtracts the left size. -/
def unrankForward (T : Nat → Nat → Nat) : Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, _, ticket, word => (word, ticket)
  | m + 1, pos, hits, ticket, word =>
    let left := T m hits
    let b : Bool := decide (left ≤ ticket)
    unrankForward T m (pos + 1) (hits + b.toNat) (if b then ticket - left else ticket)
      (word + 2 ^ pos * b.toNat)

theorem unrankForward_eq (T : Nat → Nat → Nat) (m pos hits ticket word : Nat) :
    unrankForward T m pos hits ticket word =
      (word + 2 ^ pos * (unrankWith T m hits ticket).1, (unrankWith T m hits ticket).2) := by
  induction m generalizing pos hits ticket word with
  | zero => simp [unrankForward, unrankWith]
  | succ m ih =>
    simp only [unrankForward, unrankWith, ih, Nat.bit_val, pow_succ]
    congr 1
    ring

theorem unrankForward_root (T : Nat → Nat → Nat) (m ticket : Nat) :
    unrankForward T m 0 0 ticket 0 = unrankWith T m 0 ticket := by
  simpa using unrankForward_eq T m 0 0 ticket 0

def rank (q : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, residual => residual
  | m + 1, hits, word, residual =>
    let b := word.testBit 0
    (if b then total q m hits else 0) + rank q m (hits + b.toNat) (word / 2) residual

private theorem unrank_low (q m hits ticket : Nat) (ht : ticket < total q m hits) :
    unrank q (m + 1) hits ticket =
      (Nat.bit false (unrank q m hits ticket).1, (unrank q m hits ticket).2) := by
  simp [unrank, unrankWith, Nat.not_le_of_lt ht]

private theorem unrank_high (q m hits ticket : Nat) (ht : total q m hits ≤ ticket) :
    unrank q (m + 1) hits ticket =
      (Nat.bit true (unrank q m (hits + 1) (ticket - total q m hits)).1,
        (unrank q m (hits + 1) (ticket - total q m hits)).2) := by
  simp [unrank, unrankWith, ht]

/-- Unranking always gives a bounded word and residual and ranking returns the input. -/
theorem unrank_spec (q m hits ticket : Nat) (ht : ticket < total q m hits) :
    let out := unrank q m hits ticket
    out.1 < 2 ^ m ∧ out.2 < leaf q (hits + pop m out.1) ∧
      rank q m hits out.1 out.2 = ticket := by
  induction m generalizing hits ticket with
  | zero => simpa [unrank, unrankWith, rank, total] using ht
  | succ m ih =>
    change (unrank q (m + 1) hits ticket).1 < 2 ^ (m + 1) ∧
      (unrank q (m + 1) hits ticket).2 < leaf q (hits + pop (m + 1) (unrank q (m + 1) hits ticket).1) ∧
      rank q (m + 1) hits (unrank q (m + 1) hits ticket).1 (unrank q (m + 1) hits ticket).2 = ticket
    by_cases h : ticket < total q m hits
    · rw [unrank_low q m hits ticket h]
      simpa only [Nat.bit_lt_two_pow_succ_iff, pop_bit, Bool.toNat_false, Nat.add_zero,
        rank, Nat.testBit_bit_zero, Bool.false_eq_true, ite_false, Nat.zero_add,
        Nat.bit_div_two] using ih hits ticket h
    · have h' : total q m hits ≤ ticket := Nat.le_of_not_gt h
      have ht' : ticket - total q m hits < total q m (hits + 1) := by
        rw [total] at ht
        omega
      rw [unrank_high q m hits ticket h']
      dsimp only
      obtain ⟨hw, hr, hi⟩ := ih (hits + 1) (ticket - total q m hits) ht'
      refine ⟨(Nat.bit_lt_two_pow_succ_iff (b := true)).2 hw, ?_, ?_⟩
      · rw [pop_bit, Bool.toNat_true, ← Nat.add_assoc, Nat.add_right_comm hits]
        exact hr
      · simp only [rank, Nat.testBit_bit_zero, ite_true, Bool.toNat_true, Nat.bit_div_two, hi]
        omega

/-- Every bounded word/residual pair is reached, at its rank. -/
theorem rank_spec (q m hits word residual : Nat) (hw : word < 2 ^ m)
    (hr : residual < leaf q (hits + pop m word)) :
    rank q m hits word residual < total q m hits ∧
      unrank q m hits (rank q m hits word residual) = (word, residual) := by
  induction m generalizing hits word residual with
  | zero =>
    have hzero : word = 0 := by simpa using hw
    subst word
    simpa [total, rank, unrank, unrankWith] using hr
  | succ m ih =>
    obtain ⟨b, w, rfl⟩ : ∃ b w, word = Nat.bit b w :=
      ⟨word.testBit 0, word >>> 1, word.bit_testBit_zero_shiftRight_one.symm⟩
    have hw' := Nat.bit_lt_two_pow_succ_iff.mp hw
    rw [pop_bit] at hr
    cases b
    · simp only [Bool.toNat_false, Nat.add_zero] at hr
      obtain ⟨h, hi⟩ := ih hits w residual hw' hr
      simp only [rank, Nat.testBit_bit_zero, Bool.false_eq_true, ite_false, Nat.zero_add,
        Bool.toNat_false, Nat.add_zero, Nat.bit_div_two]
      rw [unrank_low q m hits _ h, hi]
      exact ⟨by rw [total]; omega, rfl⟩
    · rw [Bool.toNat_true, ← Nat.add_assoc, Nat.add_right_comm hits] at hr
      obtain ⟨h, hi⟩ := ih (hits + 1) w residual hw' hr
      simp only [rank, Nat.testBit_bit_zero, ite_true, Bool.toNat_true, Nat.bit_div_two]
      have hx : total q m hits + rank q m (hits + 1) w residual - total q m hits =
          rank q m (hits + 1) w residual := by omega
      have hle : total q m hits ≤ total q m hits + rank q m (hits + 1) w residual := by omega
      rw [unrank_high q m hits _ hle, hx, hi]
      exact ⟨by rw [total]; omega, rfl⟩

/-- The exactly weighted ticket interval is equivalent to the admissible output pairs. -/
def rootEquiv (q m : Nat) :
    Fin (total q m 0) ≃ {p : Nat × Nat // p.1 < 2 ^ m ∧ p.2 < leaf q (pop m p.1)} where
  toFun a := ⟨unrank q m 0 a, by
    have h := unrank_spec q m 0 a a.isLt
    exact ⟨h.1, by simpa only [Nat.zero_add] using h.2.1⟩⟩
  invFun p := ⟨rank q m 0 p.val.1 p.val.2, (rank_spec q m 0 _ _ p.property.1 (by
    simpa only [Nat.zero_add] using p.property.2)).1⟩
  left_inv a := Fin.ext (unrank_spec q m 0 a a.isLt).2.2
  right_inv p := Subtype.ext ((rank_spec q m 0 _ _ p.property.1 (by
    simpa only [Nat.zero_add] using p.property.2)).2)


end PEqualNP.Outside.L_meta_29730_aux.WeightedAddress

namespace PEqualNP.Outside.L_meta_29730_aux

-- Based on bc21b4f27602583bf81c0d856bd76641e8a9e9d7, lean/PEqualNP/Outside/L_meta_25709.lean
-- The low-hit freezing lemma is from the same revision, lean/PEqualNP/Outside/L_meta_29732.lean.

def ofBits (n : Nat) (f : Nat → Bool) : Nat :=
  (List.range n).foldl (fun acc i => acc ||| ((f i).toNat <<< i)) 0

lemma foldl_or_shift_testBit (f : Nat → Bool) (l : List Nat) (acc j : Nat) :
    (l.foldl (fun a i => a ||| ((f i).toNat <<< i)) acc).testBit j =
      (acc.testBit j || (j ∈ l && f j)) := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft, List.mem_cons]
    by_cases hja : j = a
    · subst hja
      have hb0 : ((f j).toNat).testBit 0 = f j := by cases f j <;> simp
      simp only [ge_iff_le, le_refl, Nat.sub_self, hb0, decide_true, Bool.true_and, true_or]
      cases acc.testBit j <;> cases f j <;> simp
    · have hne : (decide (j ≥ a) && ((f a).toNat).testBit (j - a)) = false := by
        by_cases hge : j ≥ a
        · have hpos : 0 < j - a := by omega
          have hzero : ((f a).toNat).testBit (j - a) = false := by
            cases f a
            · simp
            · simp only [Bool.toNat_true]
              rw [Nat.testBit_eq_false_of_lt]
              exact Nat.one_lt_two_pow (by omega)
          simp [hge, hzero]
        · simp [hge]
      have hne_dec : decide (j = a ∨ j ∈ t) = decide (j ∈ t) := by
        simp [hja]
      rw [hne, hne_dec]
      cases acc.testBit j <;> simp

lemma ofBits_testBit (n : Nat) (f : Nat → Bool) (j : Nat) :
    (ofBits n f).testBit j = if j < n then f j else false := by
  unfold ofBits
  rw [foldl_or_shift_testBit]
  simp [List.mem_range]

lemma lt_two_pow_of_testBit {x n : Nat} (h : ∀ j, n ≤ j → x.testBit j = false) : x < 2 ^ n := by
  have heq : x % 2 ^ n = x := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow]
    by_cases hj : j < n
    · simp [hj]
    · simp [hj, h j (by omega)]
  rw [← heq]
  exact Nat.mod_lt x (Nat.two_pow_pos n)

lemma ofBits_lt (n : Nat) (f : Nat → Bool) : ofBits n f < 2 ^ n := by
  apply lt_two_pow_of_testBit
  intro j hj
  rw [ofBits_testBit]
  simp [Nat.not_lt.mpr hj]

lemma xor_lt_two_pow {x y n : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n) : (x ^^^ y) < 2 ^ n := by
  apply lt_two_pow_of_testBit
  intro j hj
  rw [Nat.testBit_xor, Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj)),
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) hj))]
  rfl

lemma shiftRight_lt_two_pow {x k a : Nat} (hx : x < 2 ^ k) (ha : a ≤ k) :
    x >>> (k - a) < 2 ^ a := by
  apply lt_two_pow_of_testBit
  intro j hj
  rw [Nat.testBit_shiftRight]
  have hge : k ≤ k - a + j := by omega
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hge))

lemma testBit_one_shiftLeft (p j : Nat) : (1 <<< p).testBit j = decide (j = p) := by
  rw [Nat.testBit_shiftLeft]
  by_cases h : j = p
  · subst h
    simp
  · by_cases hge : p ≤ j
    · have hpos : 0 < j - p := by omega
      have hlt : 1 < 2 ^ (j - p) := Nat.one_lt_two_pow (by omega)
      simp [h, hge, Nat.testBit_lt_two_pow hlt]
    · simp [h, hge]

lemma flipBit_lt {x p k : Nat} (hx : x < 2 ^ k) (hp : p < k) : x ^^^ (1 <<< p) < 2 ^ k := by
  apply xor_lt_two_pow hx
  rw [Nat.shiftLeft_eq, one_mul]
  exact Nat.pow_lt_pow_right (by omega) hp

lemma testBit_flipBit (x p j : Nat) :
    (x ^^^ (1 <<< p)).testBit j = if j = p then !(x.testBit j) else x.testBit j := by
  rw [Nat.testBit_xor, testBit_one_shiftLeft]
  by_cases h : j = p <;> simp [h]

def bitAt (k x i : Nat) : Bool := x.testBit (i % k)

lemma bitAt_mod (k x i : Nat) : bitAt k x (i % k) = bitAt k x i := by
  simp [bitAt]

lemma bitAt_add_k (k x i : Nat) : bitAt k x (i + k) = bitAt k x i := by
  simp [bitAt, Nat.add_mod_right]

lemma bitAt_lt {k x i : Nat} (hi : i < k) : bitAt k x i = x.testBit i := by
  simp [bitAt, Nat.mod_eq_of_lt hi]

def rot (k offset x : Nat) : Nat :=
  ((x <<< (offset % k)) ||| (x >>> (k - offset % k))) % 2 ^ k

lemma rot_lt {k offset x : Nat} : rot k offset x < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma bitAt_rot_add {k offset x j : Nat} (hk : 0 < k) (hx : x < 2 ^ k) :
    bitAt k (rot k offset x) (j + offset) = bitAt k x j := by
  unfold bitAt rot
  set s := offset % k
  have hs : s < k := Nat.mod_lt offset hk
  set i := (j + offset) % k
  have hi : i < k := Nat.mod_lt _ hk
  simp only [Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hi_eq : i = (j % k + s) % k := by
    simp [i, s, Nat.add_mod]
  have hjk : j % k < k := Nat.mod_lt j hk
  by_cases hsum : j % k + s < k
  · have hi_val : i = j % k + s := by rw [hi_eq, Nat.mod_eq_of_lt hsum]
    have hge1 : s ≤ i := by omega
    have hge2 : k ≤ k - s + i := by omega
    have hzero : x.testBit (k - s + i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hge2))
    have hsub : i - s = j % k := by omega
    simp [hge1, hzero, hsub]
  · have hi_val : i = j % k + s - k := by
      rw [hi_eq]
      have hlt2 : j % k + s - k < k := by omega
      have hmod : (j % k + s) % k = (j % k + s - k) % k := by
        have hsum_eq : j % k + s = (j % k + s - k) + k := by omega
        conv_lhs => rw [hsum_eq]
        rw [Nat.add_mod_right]
      rw [hmod, Nat.mod_eq_of_lt hlt2]
    have hlt1 : ¬ s ≤ i := by omega
    have hadd : k - s + i = j % k := by omega
    simp [hlt1, hadd]

lemma bitAt_rot_sub {k offset x i : Nat} (hk : 0 < k) (hx : x < 2 ^ k) (hi : offset ≤ i) :
    bitAt k (rot k offset x) i = bitAt k x (i - offset) := by
  have h := bitAt_rot_add (k := k) (offset := offset) (x := x) (j := i - offset) hk hx
  rwa [Nat.sub_add_cancel hi] at h

lemma bitAt_rot_rev {k offset x i : Nat} (hk : 0 < k) (hx : x < 2 ^ k) :
    bitAt k (rot k (k - offset % k) x) i = bitAt k x (i + offset) := by
  have hs : offset % k < k := Nat.mod_lt offset hk
  have hmod : ((i + offset) + (k - offset % k)) % k = i % k := by
    have hdiv : offset = k * (offset / k) + offset % k := (Nat.div_add_mod offset k).symm
    have hrew : (i + offset) + (k - offset % k) = i + k * (offset / k + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [hrew, Nat.add_mul_mod_self_left]
  have h1 : bitAt k (rot k (k - offset % k) x) i =
      bitAt k (rot k (k - offset % k) x) ((i + offset) + (k - offset % k)) := by
    simp [bitAt, hmod]
  rw [h1]
  exact bitAt_rot_add hk hx

def mix (k gap value : Nat) : Nat :=
  value ^^^ rot k gap value ^^^ rot k (k - gap) value

lemma mix_lt {k gap v : Nat} (hv : v < 2 ^ k) : mix k gap v < 2 ^ k :=
  xor_lt_two_pow (xor_lt_two_pow hv rot_lt) rot_lt

lemma bitAt_mix {k gap v i : Nat} (hk : 0 < k) (hv : v < 2 ^ k) (hgap : gap < k) (hi : gap ≤ i) :
    bitAt k (mix k gap v) i =
      xor (xor (bitAt k v i) (bitAt k v (i - gap))) (bitAt k v (i + gap)) := by
  unfold mix
  have hmod : gap % k = gap := Nat.mod_eq_of_lt hgap
  have h1 : bitAt k (v ^^^ rot k gap v ^^^ rot k (k - gap) v) i =
      xor (xor (bitAt k v i) (bitAt k (rot k gap v) i)) (bitAt k (rot k (k - gap) v) i) := by
    simp [bitAt, Nat.testBit_xor]
  rw [h1, bitAt_rot_sub hk hv hi]
  have h2 : bitAt k (rot k (k - gap) v) i = bitAt k v (i + gap) := by
    have hr := bitAt_rot_rev (k := k) (offset := gap) (x := v) (i := i) hk hv
    rwa [hmod] at hr
  rw [h2]

def chi (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc site =>
    acc ||| ((xor (word.testBit site)
      (!(word.testBit ((site + 1) % k)) && word.testBit ((site + 2) % k))).toNat <<< site)) 0

lemma chi_eq_ofBits (k word : Nat) :
    chi k word = ofBits k (fun site =>
      xor (word.testBit site)
        (!(word.testBit ((site + 1) % k)) && word.testBit ((site + 2) % k))) := rfl

lemma chi_lt {k word : Nat} : chi k word < 2 ^ k := by
  rw [chi_eq_ofBits]
  exact ofBits_lt k _

lemma bitAt_chi {k word i : Nat} (hk : 0 < k) :
    bitAt k (chi k word) i =
      xor (bitAt k word i) (!(bitAt k word (i + 1)) && bitAt k word (i + 2)) := by
  unfold bitAt
  simp only [chi_eq_ofBits, ofBits_testBit, Nat.mod_lt i hk, ↓reduceIte]
  have h1 : (i % k + 1) % k = (i + 1) % k := by simp [Nat.add_mod]
  have h2 : (i % k + 2) % k = (i + 2) % k := by simp [Nat.add_mod]
  rw [h1, h2]

def step (k r : Nat) (constants : Nat → Fin (2 ^ k)) (col : Bool) (raw prev t : Nat) : Nat :=
  chi k (mix k (if col then 2 else 1) prev) ^^^
    rot k (if col then 3 * t + 1 else 2 * (t - 1)) raw ^^^
    (constants (if col then r + t else t)).val

lemma step_lt {k r : Nat} {c : Nat → Fin (2 ^ k)} {col : Bool} {raw prev t : Nat} :
    step k r c col raw prev t < 2 ^ k :=
  xor_lt_two_pow (xor_lt_two_pow chi_lt rot_lt) (c _).isLt

def stateStep (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name : Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun v tick => step k r c side key v (tick + 1))
    (rot k (if side then 3 else 1) key ^^^ name)

lemma stateStep_zero (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name : Nat) :
    stateStep k r c side key name 0 = rot k (if side then 3 else 1) key ^^^ name := rfl

lemma stateStep_succ (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name n : Nat) :
    stateStep k r c side key name (n + 1) =
      step k r c side key (stateStep k r c side key name n) (n + 1) := by
  unfold stateStep
  rw [List.range_succ, List.foldl_append]
  rfl

lemma stateStep_lt {k r : Nat} {c : Nat → Fin (2 ^ k)} {side : Bool} {key name n : Nat}
    (hname : name < 2 ^ k) :
    stateStep k r c side key name n < 2 ^ k := by
  cases n with
  | zero => exact xor_lt_two_pow rot_lt hname
  | succ n =>
    rw [stateStep_succ]
    exact step_lt

def AgreeOn (k lo hi x y : Nat) : Prop :=
  ∀ i, lo ≤ i → i < hi → bitAt k x i = bitAt k y i

lemma agreeOn_mono {k lo1 hi1 lo2 hi2 x y : Nat}
    (h : AgreeOn k lo1 hi1 x y) (hlo : lo1 ≤ lo2) (hhi : hi2 ≤ hi1) :
    AgreeOn k lo2 hi2 x y :=
  fun i h1 h2 => h i (le_trans hlo h1) (lt_of_lt_of_le h2 hhi)

lemma xor_congr_left {a a' b : Bool} : xor (xor a b) (xor a' b) = xor a a' := by
  cases a <;> cases a' <;> cases b <;> rfl

lemma xor_congr_right {a b b' : Bool} : xor (xor a b) (xor a b') = xor b b' := by
  cases a <;> cases b <;> cases b' <;> rfl

def leftRow (t : Nat) : Nat := max (t + 1) (2 * (t - 1))

lemma row_dep {k r : Nat} {c : Nat → Fin (2 ^ k)} {row : Nat} (hk : 2 ≤ k) (hrow : row < 2 ^ k) :
    ∀ t w w' i, w < 2 ^ k → w' < 2 ^ k → leftRow t ≤ i →
      AgreeOn k (i - leftRow t) (i + 3 * t) w w' →
      bitAt k (stateStep k r c false w row t) i =
        bitAt k (stateStep k r c false w' row t) i := by
  intro t
  induction t with
  | zero =>
    intro w w' i hw hw' hi hAg
    rw [stateStep_zero, stateStep_zero]
    simp only [Bool.false_eq_true, ↓reduceIte, bitAt, Nat.testBit_xor]
    have h1 : leftRow 0 = 1 := rfl
    have hr := hAg (i - 1) (by omega) (by omega)
    have hb1 : bitAt k (rot k 1 w) i = bitAt k w (i - 1) := bitAt_rot_sub (by omega) hw (by omega)
    have hb2 : bitAt k (rot k 1 w') i = bitAt k w' (i - 1) := bitAt_rot_sub (by omega) hw' (by omega)
    unfold bitAt at hb1 hb2 hr
    rw [hb1, hb2, hr]
  | succ t ih =>
    intro w w' i hw hw' hi hAg
    rw [stateStep_succ, stateStep_succ]
    unfold step
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
    have hlt1 : stateStep k r c false w row t < 2 ^ k := stateStep_lt hrow
    have hlt2 : stateStep k r c false w' row t < 2 ^ k := stateStep_lt hrow
    have hL : leftRow t + 1 ≤ leftRow (t + 1) := by unfold leftRow; omega
    have hraw : 2 * t ≤ leftRow (t + 1) := by unfold leftRow; omega
    have hM : ∀ d ≤ 2, bitAt k (mix k 1 (stateStep k r c false w row t)) (i + d) =
        bitAt k (mix k 1 (stateStep k r c false w' row t)) (i + d) := by
      intro d hd
      rw [bitAt_mix (by omega) hlt1 (by omega) (by omega),
        bitAt_mix (by omega) hlt2 (by omega) (by omega)]
      have h0 : bitAt k (stateStep k r c false w row t) (i + d) =
          bitAt k (stateStep k r c false w' row t) (i + d) :=
        ih w w' (i + d) hw hw' (by omega) (agreeOn_mono hAg (by omega) (by omega))
      have hm1 : bitAt k (stateStep k r c false w row t) (i + d - 1) =
          bitAt k (stateStep k r c false w' row t) (i + d - 1) :=
        ih w w' (i + d - 1) hw hw' (by omega) (agreeOn_mono hAg (by omega) (by omega))
      have hp1 : bitAt k (stateStep k r c false w row t) (i + d + 1) =
          bitAt k (stateStep k r c false w' row t) (i + d + 1) :=
        ih w w' (i + d + 1) hw hw' (by omega) (agreeOn_mono hAg (by omega) (by omega))
      rw [h0, hm1, hp1]
    have hM0 := hM 0 (by omega)
    simp only [Nat.add_zero] at hM0
    have hchi : bitAt k (chi k (mix k 1 (stateStep k r c false w row t))) i =
        bitAt k (chi k (mix k 1 (stateStep k r c false w' row t))) i := by
      rw [bitAt_chi (by omega), bitAt_chi (by omega), hM0, hM 1 (by omega), hM 2 (by omega)]
    have hrot : bitAt k (rot k (2 * t) w) i = bitAt k (rot k (2 * t) w') i := by
      rw [bitAt_rot_sub (by omega) hw (by omega), bitAt_rot_sub (by omega) hw' (by omega)]
      exact hAg (i - 2 * t) (by omega) (by omega)
    have hxor : ∀ a b d, bitAt k (a ^^^ b ^^^ d) i =
        xor (xor (bitAt k a i) (bitAt k b i)) (bitAt k d i) := by
      intro a b d
      simp [bitAt, Nat.testBit_xor]
    rw [hxor, hxor, hchi, hrot]

lemma row_pivot {k r : Nat} {c : Nat → Fin (2 ^ k)} {row : Nat} (hk : 2 ≤ k) (hrow : row < 2 ^ k) :
    ∀ t, t ≠ 3 → ∀ w w' i, w < 2 ^ k → w' < 2 ^ k → leftRow t ≤ i →
      AgreeOn k (i - leftRow t + 1) (i + 3 * t) w w' →
      xor (bitAt k (stateStep k r c false w row t) i)
          (bitAt k (stateStep k r c false w' row t) i) =
        xor (bitAt k w (i - leftRow t)) (bitAt k w' (i - leftRow t)) := by
  intro t ht
  induction t with
  | zero =>
    intro w w' i hw hw' hi _
    rw [stateStep_zero, stateStep_zero]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hxor : ∀ a b, bitAt k (a ^^^ b) i = xor (bitAt k a i) (bitAt k b i) := by
      intro a b; simp [bitAt, Nat.testBit_xor]
    rw [hxor, hxor, xor_congr_left]
    have hL : leftRow 0 = 1 := rfl
    rw [hL, bitAt_rot_sub (by omega) hw (by omega), bitAt_rot_sub (by omega) hw' (by omega)]
  | succ t ih =>
    intro w w' i hw hw' hi hAg
    rw [stateStep_succ, stateStep_succ]
    unfold step
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
    have hlt1 : stateStep k r c false w row t < 2 ^ k := stateStep_lt hrow
    have hlt2 : stateStep k r c false w' row t < 2 ^ k := stateStep_lt hrow
    have hxor3 : ∀ a b d, bitAt k (a ^^^ b ^^^ d) i =
        xor (xor (bitAt k a i) (bitAt k b i)) (bitAt k d i) := by
      intro a b d; simp [bitAt, Nat.testBit_xor]
    rw [hxor3, hxor3, xor_congr_left]
    by_cases ht3 : t < 3
    · have ht_ne3 : t ≠ 3 := by omega
      have hL_eq : leftRow (t + 1) = leftRow t + 1 := by
        simp only [leftRow, Nat.add_sub_cancel]
        omega
      have hraw_gt : i - leftRow (t + 1) + 1 ≤ i - 2 * t := by
        simp only [leftRow, Nat.add_sub_cancel] at hi ⊢
        omega
      have hraw_lt : i - 2 * t < i + 3 * (t + 1) := by omega
      have hrot : bitAt k (rot k (2 * t) w) i = bitAt k (rot k (2 * t) w') i := by
        rw [bitAt_rot_sub (by omega) hw (by unfold leftRow at hi; omega),
          bitAt_rot_sub (by omega) hw' (by unfold leftRow at hi; omega)]
        exact hAg (i - 2 * t) hraw_gt hraw_lt
      rw [hrot, xor_congr_left, bitAt_chi (by omega), bitAt_chi (by omega)]
      have hM_eq : ∀ d, 1 ≤ d → d ≤ 2 →
          bitAt k (mix k 1 (stateStep k r c false w row t)) (i + d) =
            bitAt k (mix k 1 (stateStep k r c false w' row t)) (i + d) := by
        intro d hd1 hd2
        rw [bitAt_mix (by omega) hlt1 (by omega) (by omega),
          bitAt_mix (by omega) hlt2 (by omega) (by omega)]
        have h0 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' (i + d) hw hw'
          (by omega) (agreeOn_mono hAg (by omega) (by omega))
        have hm1 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' (i + d - 1) hw hw'
          (by omega) (agreeOn_mono hAg (by omega) (by omega))
        have hp1 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' (i + d + 1) hw hw'
          (by omega) (agreeOn_mono hAg (by omega) (by omega))
        rw [h0, hm1, hp1]
      rw [hM_eq 1 (by omega) (by omega), hM_eq 2 (by omega) (by omega), xor_congr_left]
      rw [bitAt_mix (by omega) hlt1 (by omega) (by omega),
        bitAt_mix (by omega) hlt2 (by omega) (by omega)]
      have h0 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' i hw hw'
        (by omega) (agreeOn_mono hAg (by omega) (by omega))
      have hp1 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' (i + 1) hw hw'
        (by omega) (agreeOn_mono hAg (by omega) (by omega))
      rw [h0, hp1, xor_congr_left, xor_congr_right]
      have hpiv := ih ht_ne3 w w' (i - 1) hw hw' (by omega)
        (agreeOn_mono hAg (by omega) (by omega))
      have hsub_eq : i - 1 - leftRow t = i - leftRow (t + 1) := by omega
      rwa [hsub_eq] at hpiv
    · have ht_ge3 : 3 ≤ t := by omega
      have hL_eq : leftRow (t + 1) = 2 * t := by
        simp only [leftRow, Nat.add_sub_cancel]
        omega
      have hprev_lt : leftRow t + 1 < 2 * t := by
        simp only [leftRow]
        omega
      have hM_all : ∀ d ≤ 2,
          bitAt k (mix k 1 (stateStep k r c false w row t)) (i + d) =
            bitAt k (mix k 1 (stateStep k r c false w' row t)) (i + d) := by
        intro d hd
        rw [bitAt_mix (by omega) hlt1 (by omega) (by omega),
          bitAt_mix (by omega) hlt2 (by omega) (by omega)]
        have h0 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' (i + d) hw hw'
          (by omega) (agreeOn_mono hAg (by omega) (by omega))
        have hm1 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' (i + d - 1) hw hw'
          (by omega) (agreeOn_mono hAg (by omega) (by omega))
        have hp1 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' (i + d + 1) hw hw'
          (by omega) (agreeOn_mono hAg (by omega) (by omega))
        rw [h0, hm1, hp1]
      have hM0 := hM_all 0 (by omega)
      simp only [Nat.add_zero] at hM0
      have hchi : bitAt k (chi k (mix k 1 (stateStep k r c false w row t))) i =
          bitAt k (chi k (mix k 1 (stateStep k r c false w' row t))) i := by
        rw [bitAt_chi (by omega), bitAt_chi (by omega),
          hM0, hM_all 1 (by omega), hM_all 2 (by omega)]
      rw [hchi, xor_congr_right, hL_eq,
        bitAt_rot_sub (by omega) hw (by omega), bitAt_rot_sub (by omega) hw' (by omega)]

lemma row_mix_pivot {k r : Nat} {c : Nat → Fin (2 ^ k)} {row : Nat} (hk : 2 ≤ k) (hrow : row < 2 ^ k)
    {t : Nat} (ht1 : 1 ≤ t) (ht4 : t ≠ 4) {w w' i : Nat}
    (hw : w < 2 ^ k) (hw' : w' < 2 ^ k) (hi : leftRow (t - 1) + 1 ≤ i)
    (hAg : AgreeOn k (i - (leftRow (t - 1) + 1) + 1) (i + 3 * t - 2) w w') :
    xor (bitAt k (mix k 1 (stateStep k r c false w row (t - 1))) i)
        (bitAt k (mix k 1 (stateStep k r c false w' row (t - 1))) i) =
      xor (bitAt k w (i - (leftRow (t - 1) + 1))) (bitAt k w' (i - (leftRow (t - 1) + 1))) := by
  have hlt1 : stateStep k r c false w row (t - 1) < 2 ^ k := stateStep_lt hrow
  have hlt2 : stateStep k r c false w' row (t - 1) < 2 ^ k := stateStep_lt hrow
  rw [bitAt_mix (by omega) hlt1 (by omega) (by omega),
    bitAt_mix (by omega) hlt2 (by omega) (by omega)]
  have h0 := row_dep (r := r) (c := c) (row := row) hk hrow (t - 1) w w' i hw hw'
    (by omega) (agreeOn_mono hAg (by omega) (by omega))
  have hp1 := row_dep (r := r) (c := c) (row := row) hk hrow (t - 1) w w' (i + 1) hw hw'
    (by omega) (agreeOn_mono hAg (by omega) (by omega))
  rw [h0, hp1, xor_congr_left, xor_congr_right]
  have hpiv := row_pivot (r := r) (c := c) (row := row) hk hrow (t - 1) (by omega) w w' (i - 1) hw hw'
    (by omega) (agreeOn_mono hAg (by omega) (by omega))
  have hsub : i - 1 - leftRow (t - 1) = i - (leftRow (t - 1) + 1) := by omega
  rwa [hsub] at hpiv

def leftCol (t : Nat) : Nat := max (2 * t + 3) (3 * t + 1)

lemma col_dep {k r : Nat} {c : Nat → Fin (2 ^ k)} {col : Nat} (hk : 3 ≤ k) (hcol : col < 2 ^ k) :
    ∀ t w w' i, w < 2 ^ k → w' < 2 ^ k → leftCol t ≤ i →
      AgreeOn k (i - leftCol t) (if t = 0 then i - 2 else i + 4 * t - 2) w w' →
      bitAt k (stateStep k r c true w col t) i =
        bitAt k (stateStep k r c true w' col t) i := by
  intro t
  induction t with
  | zero =>
    intro w w' i hw hw' hi hAg
    rw [stateStep_zero, stateStep_zero]
    simp only [↓reduceIte]
    have hL : leftCol 0 = 3 := rfl
    have hxor : ∀ a b, bitAt k (a ^^^ b) i = xor (bitAt k a i) (bitAt k b i) := by
      intro a b; simp [bitAt, Nat.testBit_xor]
    rw [hxor, hxor, bitAt_rot_sub (by omega) hw (by omega), bitAt_rot_sub (by omega) hw' (by omega)]
    have h1 := hAg (i - 3) (by omega) (by simp; omega)
    rw [h1]
  | succ t ih =>
    intro w w' i hw hw' hi hAg
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte] at hAg
    rw [stateStep_succ, stateStep_succ]
    unfold step
    simp only [↓reduceIte]
    have hlt1 : stateStep k r c true w col t < 2 ^ k := stateStep_lt hcol
    have hlt2 : stateStep k r c true w' col t < 2 ^ k := stateStep_lt hcol
    have hL : leftCol t + 2 ≤ leftCol (t + 1) := by unfold leftCol; omega
    have hraw : 3 * (t + 1) + 1 ≤ leftCol (t + 1) := by unfold leftCol; omega
    have hN : ∀ d ≤ 2, bitAt k (mix k 2 (stateStep k r c true w col t)) (i + d) =
        bitAt k (mix k 2 (stateStep k r c true w' col t)) (i + d) := by
      intro d hd
      rw [bitAt_mix (by omega) hlt1 (by omega) (by omega),
        bitAt_mix (by omega) hlt2 (by omega) (by omega)]
      have h0 : bitAt k (stateStep k r c true w col t) (i + d) =
          bitAt k (stateStep k r c true w' col t) (i + d) :=
        ih w w' (i + d) hw hw' (by omega)
          (agreeOn_mono hAg (by omega) (by split_ifs <;> omega))
      have hm2 : bitAt k (stateStep k r c true w col t) (i + d - 2) =
          bitAt k (stateStep k r c true w' col t) (i + d - 2) :=
        ih w w' (i + d - 2) hw hw' (by omega)
          (agreeOn_mono hAg (by omega) (by split_ifs <;> omega))
      have hp2 : bitAt k (stateStep k r c true w col t) (i + d + 2) =
          bitAt k (stateStep k r c true w' col t) (i + d + 2) :=
        ih w w' (i + d + 2) hw hw' (by omega)
          (agreeOn_mono hAg (by omega) (by split_ifs <;> omega))
      rw [h0, hm2, hp2]
    have hN0 := hN 0 (by omega)
    simp only [Nat.add_zero] at hN0
    have hchi : bitAt k (chi k (mix k 2 (stateStep k r c true w col t))) i =
        bitAt k (chi k (mix k 2 (stateStep k r c true w' col t))) i := by
      rw [bitAt_chi (by omega), bitAt_chi (by omega),
        hN0, hN 1 (by omega), hN 2 (by omega)]
    have hrot : bitAt k (rot k (3 * (t + 1) + 1) w) i = bitAt k (rot k (3 * (t + 1) + 1) w') i := by
      rw [bitAt_rot_sub (by omega) hw (by omega), bitAt_rot_sub (by omega) hw' (by omega)]
      exact hAg (i - (3 * (t + 1) + 1)) (by omega) (by omega)
    have hxor3 : ∀ a b d, bitAt k (a ^^^ b ^^^ d) i =
        xor (xor (bitAt k a i) (bitAt k b i)) (bitAt k d i) := by
      intro a b d; simp [bitAt, Nat.testBit_xor]
    rw [hxor3, hxor3, hchi, hrot]

lemma col_pivot {k r : Nat} {c : Nat → Fin (2 ^ k)} {col : Nat} (hk : 3 ≤ k) (hcol : col < 2 ^ k)
    {t : Nat} (ht : 3 ≤ t) {w w' i : Nat} (hw : w < 2 ^ k) (hw' : w' < 2 ^ k)
    (hi : 3 * t + 1 ≤ i)
    (hAg : AgreeOn k (i - (3 * t + 1) + 1) (i + 4 * t - 2) w w') :
    xor (bitAt k (stateStep k r c true w col t) i)
        (bitAt k (stateStep k r c true w' col t) i) =
      xor (bitAt k w (i - (3 * t + 1))) (bitAt k w' (i - (3 * t + 1))) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [stateStep_succ, stateStep_succ]
  unfold step
  simp only [↓reduceIte]
  have hlt1 : stateStep k r c true w col t' < 2 ^ k := stateStep_lt hcol
  have hlt2 : stateStep k r c true w' col t' < 2 ^ k := stateStep_lt hcol
  have hprev : leftCol t' + 2 < 3 * (t' + 1) + 1 := by unfold leftCol; omega
  have hN : ∀ d ≤ 2, bitAt k (mix k 2 (stateStep k r c true w col t')) (i + d) =
      bitAt k (mix k 2 (stateStep k r c true w' col t')) (i + d) := by
    intro d hd
    rw [bitAt_mix (by omega) hlt1 (by omega) (by omega),
      bitAt_mix (by omega) hlt2 (by omega) (by omega)]
    have h0 := col_dep (r := r) (c := c) (col := col) hk hcol t' w w' (i + d) hw hw'
      (by omega) (agreeOn_mono hAg (by omega) (by split_ifs <;> omega))
    have hm2 := col_dep (r := r) (c := c) (col := col) hk hcol t' w w' (i + d - 2) hw hw'
      (by omega) (agreeOn_mono hAg (by omega) (by split_ifs <;> omega))
    have hp2 := col_dep (r := r) (c := c) (col := col) hk hcol t' w w' (i + d + 2) hw hw'
      (by omega) (agreeOn_mono hAg (by omega) (by split_ifs <;> omega))
    rw [h0, hm2, hp2]
  have hN0 := hN 0 (by omega)
  simp only [Nat.add_zero] at hN0
  have hchi : bitAt k (chi k (mix k 2 (stateStep k r c true w col t'))) i =
      bitAt k (chi k (mix k 2 (stateStep k r c true w' col t'))) i := by
    rw [bitAt_chi (by omega), bitAt_chi (by omega),
      hN0, hN 1 (by omega), hN 2 (by omega)]
  have hxor3 : ∀ a b d, bitAt k (a ^^^ b ^^^ d) i =
      xor (xor (bitAt k a i) (bitAt k b i)) (bitAt k d i) := by
    intro a b d; simp [bitAt, Nat.testBit_xor]
  rw [hxor3, hxor3, xor_congr_left, hchi, xor_congr_right,
    bitAt_rot_sub (by omega) hw hi, bitAt_rot_sub (by omega) hw' hi]

def solveBits (p : Nat → Nat) (f : Nat → Nat → Bool) (b : Nat → Bool)
    (w0 : Nat) : Nat → Nat
  | 0 => w0
  | t + 1 =>
    let w := solveBits p f b w0 t
    if f t w = b t then w else w ^^^ (1 <<< p t)

lemma flip_update {x p j : Nat} :
    (x ^^^ (1 <<< p)).testBit j = if j = p then !x.testBit j else x.testBit j :=
  testBit_flipBit x p j

lemma solveBits_spec {k base m : Nat} {p : Nat → Nat} {f : Nat → Nat → Bool}
    {b : Nat → Bool} {w0 : Nat} (hw0 : w0 < 2 ^ k)
    (hpos : ∀ t < m, base ≤ p t ∧ p t < k)
    (hanti : ∀ i j, i < j → j < m → p j < p i)
    (hpiv : ∀ t < m, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ j < k, j < base ∨ p t < j → w.testBit j = w'.testBit j) →
      xor (f t w) (f t w') = xor (w.testBit (p t)) (w'.testBit (p t)))
    (d : Nat) (hd : d ≤ m) :
    let w := solveBits p f b w0 d
    w < 2 ^ k ∧
    (∀ j, (∀ t < d, p t ≠ j) → w.testBit j = w0.testBit j) ∧
    ∀ t < d, f t w = b t := by
  dsimp only
  induction d with
  | zero => simp [solveBits, hw0]
  | succ d ih =>
    obtain ⟨hw, hfree, hfixed⟩ := ih (by omega)
    let w := solveBits p f b w0 d
    have hdm : d < m := by omega
    have hf : solveBits p f b w0 (d + 1) =
        (if f d w = b d then w else w ^^^ (1 <<< p d)) := rfl
    rw [hf]
    by_cases hmatch : f d w = b d
    · rw [if_pos hmatch]
      refine ⟨hw, fun j h => hfree j (fun t ht => h t (by omega)), ?_⟩
      intro t ht
      by_cases htd : t = d
      · simpa [htd] using hmatch
      · exact hfixed t (by omega)
    · rw [if_neg hmatch]
      let w' := w ^^^ (1 <<< p d)
      have hw' : w' < 2 ^ k := flipBit_lt hw (hpos d hdm).2
      change w' < 2 ^ k ∧ _ ∧ _
      refine ⟨hw', ?_, ?_⟩
      · intro j h
        have hne : j ≠ p d := (h d (by omega)).symm
        simpa only [w', flip_update, hne, ↓reduceIte] using hfree j (fun t ht => h t (by omega))
      · intro t ht
        have htm : t < m := by omega
        by_cases htd : t = d
        · subst t
          have hx := hpiv d hdm w w' hw hw' (by
            intro j _ hj
            have hne : j ≠ p d := by
              rcases hj with h | h
              · exact Nat.ne_of_lt (lt_of_lt_of_le h (hpos d hdm).1)
              · exact Nat.ne_of_gt h
            simp only [w', flip_update, hne, ↓reduceIte])
          have hbit : w'.testBit (p d) = !w.testBit (p d) := by
            simp only [w', flip_update, ↓reduceIte]
          rw [hbit] at hx
          have hx' : ∀ a b c t : Bool, xor a b = xor c (!c) → a ≠ t → b = t := by decide
          exact hx' _ _ _ _ hx hmatch
        · have hp := hanti t d (by omega) hdm
          have hx := hpiv t htm w w' hw hw' (by
            intro j _ hj
            have hne : j ≠ p d := by
              rcases hj with h | h
              · exact Nat.ne_of_lt (lt_of_lt_of_le h (hpos d hdm).1)
              · omega
            simp only [w', flip_update, hne, ↓reduceIte])
          have hbit : w'.testBit (p t) = w.testBit (p t) := by
            simp only [w', flip_update, Nat.ne_of_gt hp, ↓reduceIte]
          rw [hbit] at hx
          have heq : f t w' = f t w := by
            have hx' : ∀ x y z : Bool, xor x y = xor z z → y = x := by decide
            exact hx' _ _ _ hx
          exact heq.trans (hfixed t (by omega))

def solveTri (base m : Nat) (f : Nat → Nat) (target w0 : Nat) : Nat :=
  solveBits (fun d => base + (m - 1 - d))
    (fun d w => (f w).testBit (m - 1 - d)) (fun d => target.testBit (m - 1 - d)) w0 m

lemma solveTri_spec {k base m : Nat} (hbm : base + m ≤ k)
    (F : Nat → Nat) (hF_lt : ∀ w < 2 ^ k, F w < 2 ^ m)
    (hTri : ∀ j < m, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ s < k, (s < base ∨ base + j < s) → w.testBit s = w'.testBit s) →
      xor ((F w).testBit j) ((F w').testBit j) =
        xor (w.testBit (base + j)) (w'.testBit (base + j)))
    (w0 : Nat) (hw0 : w0 < 2 ^ k) (target : Nat) (htgt : target < 2 ^ m) :
    let w := solveTri base m F target w0
    w < 2 ^ k ∧
    (∀ s < k, (s < base ∨ base + m ≤ s) → w.testBit s = w0.testBit s) ∧ F w = target := by
  dsimp only [solveTri]
  obtain ⟨hw, hfree, hfix⟩ := solveBits_spec (base := base) (m := m)
    (p := fun d => base + (m - 1 - d))
    (f := fun d w => (F w).testBit (m - 1 - d))
    (b := fun d => target.testBit (m - 1 - d))
    hw0 (by intro d hd; omega) (by intro i j hij hj; omega)
    (by intro d hd; exact hTri (m - 1 - d) (by omega)) m le_rfl
  refine ⟨hw, ?_, ?_⟩
  · intro s _ hs
    apply hfree
    intro t ht
    omega
  · apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < m
    · have h := hfix (m - 1 - j) (by omega)
      have he : m - 1 - (m - 1 - j) = j := by omega
      simpa only [he] using h
    · have h1 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : m ≤ j)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hF_lt _ hw) h1),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le htgt h1)]

lemma triangular_solve {k base m : Nat} (hbm : base + m ≤ k)
    (F : Nat → Nat) (hF_lt : ∀ w < 2 ^ k, F w < 2 ^ m)
    (hTri : ∀ j < m, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ s < k, (s < base ∨ base + j < s) → w.testBit s = w'.testBit s) →
      xor ((F w).testBit j) ((F w').testBit j) =
        xor (w.testBit (base + j)) (w'.testBit (base + j)))
    (w0 : Nat) (hw0 : w0 < 2 ^ k) (target : Nat) (htgt : target < 2 ^ m) :
    ∃! w : Fin (2 ^ k),
      (∀ s < k, (s < base ∨ base + m ≤ s) → w.val.testBit s = w0.testBit s) ∧
      F w.val = target := by
  have hex : ∀ d ≤ m, ∃ w < 2 ^ k,
      (∀ s < k, (s < base ∨ base + m ≤ s) → w.testBit s = w0.testBit s) ∧
      (∀ j, m - d ≤ j → j < m → (F w).testBit j = target.testBit j) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨w0, hw0, fun _ _ _ => rfl, ?_⟩
      intro j hj1 hj2
      omega
    | succ d ih =>
      intro hd
      rcases ih (by omega) with ⟨w, hw, hout, htop⟩
      let j0 := m - (d + 1)
      have hj0 : j0 < m := by omega
      by_cases hmatch : (F w).testBit j0 = target.testBit j0
      · refine ⟨w, hw, hout, ?_⟩
        intro j hj1 hj2
        by_cases heq : j = j0
        · rw [heq]; exact hmatch
        · exact htop j (by omega) hj2
      · let w' := w ^^^ (1 <<< (base + j0))
        have hw' : w' < 2 ^ k := flipBit_lt hw (by omega)
        refine ⟨w', hw', ?_, ?_⟩
        · intro s hs hso
          rw [testBit_flipBit]
          have hne : s ≠ base + j0 := by omega
          simp [hne, hout s hs hso]
        · intro j hj1 hj2
          by_cases heq : j = j0
          · subst heq
            have hAg : ∀ s < k, (s < base ∨ base + j0 < s) → w.testBit s = w'.testBit s := by
              intro s _ hso
              rw [testBit_flipBit]
              have hne : s ≠ base + j0 := by omega
              simp [hne]
            have hxor := hTri j0 hj0 w w' hw hw' hAg
            have hflip : w'.testBit (base + j0) = !(w.testBit (base + j0)) := by
              simp [w']
            rw [hflip] at hxor
            cases hb1 : (F w).testBit j0 <;> cases hb2 : (F w').testBit j0 <;>
              cases ht : target.testBit j0 <;> cases hwb : w.testBit (base + j0) <;>
              simp_all
          · have hgt : j0 < j := by omega
            have hAg : ∀ s < k, (s < base ∨ base + j < s) → w.testBit s = w'.testBit s := by
              intro s _ hso
              rw [testBit_flipBit]
              have hne : s ≠ base + j0 := by omega
              simp [hne]
            have hxor := hTri j hj2 w w' hw hw' hAg
            have hsame : w'.testBit (base + j) = w.testBit (base + j) := by
              have hne : base + j ≠ base + j0 := by omega
              simp only [w', testBit_flipBit, hne, ↓reduceIte]
            rw [hsame] at hxor
            have hFeq : (F w').testBit j = (F w).testBit j := by
              cases h1 : (F w).testBit j <;> cases h2 : (F w').testBit j <;> simp_all
            rw [hFeq]
            exact htop j (by omega) hj2
  rcases hex m (le_refl _) with ⟨w, hw, hout, hall⟩
  have hFw : F w = target := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < m
    · exact hall j (by omega) hj
    · have hge : m ≤ j := by omega
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hF_lt w hw) (Nat.pow_le_pow_right (by omega) hge)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le htgt (Nat.pow_le_pow_right (by omega) hge))]
  refine ⟨⟨w, hw⟩, ⟨hout, hFw⟩, ?_⟩
  rintro ⟨w2, hw2⟩ ⟨hout2, hFw2⟩
  apply Fin.ext
  have htop_eq : ∀ d ≤ m, ∀ j, m - d ≤ j → j < m → w2.testBit (base + j) = w.testBit (base + j) := by
    intro d
    induction d with
    | zero => intro _ j hj1 hj2; omega
    | succ d ih =>
      intro hd j hj1 hj2
      by_cases heq : j = m - (d + 1)
      · subst heq
        have hAg : ∀ s < k, (s < base ∨ base + (m - (d + 1)) < s) → w2.testBit s = w.testBit s := by
          intro s hs hso
          rcases hso with hlt | hgt
          · rw [hout2 s hs (Or.inl hlt), hout s hs (Or.inl hlt)]
          · by_cases hge : base + m ≤ s
            · rw [hout2 s hs (Or.inr hge), hout s hs (Or.inr hge)]
            · have hsub := ih (by omega) (s - base) (by omega) (by omega)
              have hrew : base + (s - base) = s := by omega
              rwa [hrew] at hsub
        have hxor := hTri (m - (d + 1)) (by omega) w2 w hw2 hw hAg
        rw [hFw2, hFw] at hxor
        cases h1 : w2.testBit (base + (m - (d + 1))) <;>
          cases h2 : w.testBit (base + (m - (d + 1))) <;> simp_all
      · exact ih (by omega) j (by omega) hj2
  apply Nat.eq_of_testBit_eq
  intro s
  by_cases hsk : s < k
  · by_cases hin : base ≤ s ∧ s < base + m
    · have h1 := htop_eq m (le_refl _) (s - base) (by omega) (by omega)
      have hrew : base + (s - base) = s := by omega
      rwa [hrew] at h1
    · have hso : s < base ∨ base + m ≤ s := by omega
      rw [hout2 s hsk hso, hout s hsk hso]
  · have hge : k ≤ s := by omega
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hw2 (Nat.pow_le_pow_right (by omega) hge)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hge))]

def histStep (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (ref : Nat)
    (triple : Nat × Nat × Nat) (idx : Nat) : Nat × Nat × Nat :=
  let time := idx + 1
  let place := k - q + 3 * (r - time) + min (q - 1) triple.2.2
  let bit := (mix k 1 triple.1).testBit ((place + 1) % k)
  let next := step k r sched false ref triple.1 time
  if time = 4 then (next, triple.2.1, triple.2.2)
  else (next, 2 * triple.2.1 + bit.toNat, triple.2.2 + bit.toNat)

def histFold (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref n : Nat) : Nat × Nat × Nat :=
  (List.range n).foldl (histStep k r q sched ref) (rot k 1 ref ^^^ row, 0, 0)

lemma histFold_zero (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref : Nat) :
    histFold k r q sched row ref 0 = (rot k 1 ref ^^^ row, 0, 0) := rfl

lemma histFold_succ (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref n : Nat) :
    histFold k r q sched row ref (n + 1) =
      histStep k r q sched ref (histFold k r q sched row ref n) n := by
  unfold histFold
  rw [List.range_succ, List.foldl_append]
  rfl

lemma histFold_fst (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref n : Nat) :
    (histFold k r q sched row ref n).1 = stateStep k r sched false ref row n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [histFold_succ, stateStep_succ]
    unfold histStep
    dsimp only
    split_ifs <;> simp [ih]

def recCount (n : Nat) : Nat := if n < 4 then n else n - 1

def bitWeight (m code : Nat) : Nat :=
  ((List.range m).filter (fun jj => code.testBit jj)).length

lemma bitWeight_step (m code : Nat) (b : Bool) :
    bitWeight (m + 1) (2 * code + b.toNat) = bitWeight m code + b.toNat := by
  unfold bitWeight
  rw [List.range_succ_eq_map, List.filter_cons]
  have h0 : (2 * code + b.toNat).testBit 0 = b := by
    cases b <;> simp [Nat.testBit_zero]
  have hsucc : ∀ j, (2 * code + b.toNat).testBit (j + 1) = code.testBit j := by
    intro j
    rw [Nat.testBit_succ]
    have hdiv : (2 * code + b.toNat) / 2 = code := by
      cases b
      · simp
      · simp only [Bool.toNat_true]; omega
    rw [hdiv]
  rw [List.filter_map]
  have hcomp : ((fun jj => (2 * code + b.toNat).testBit jj) ∘ Nat.succ) =
      (fun jj => code.testBit jj) := by
    funext j
    exact hsucc j
  rw [hcomp, h0]
  cases b <;> simp [List.length_map]

lemma histFold_code_weight (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref n : Nat) :
    (histFold k r q sched row ref n).2.1 < 2 ^ (recCount n) ∧
    (histFold k r q sched row ref n).2.2 =
      bitWeight (recCount n) (histFold k r q sched row ref n).2.1 := by
  induction n with
  | zero =>
    simp [histFold_zero, recCount, bitWeight]
  | succ n ih =>
    rw [histFold_succ]
    unfold histStep
    dsimp only
    by_cases h4 : n + 1 = 4
    · have hrec : recCount (n + 1) = recCount n := by unfold recCount; split_ifs <;> omega
      rw [hrec]
      simp only [h4, ↓reduceIte]
      exact ih
    · have hrec : recCount (n + 1) = recCount n + 1 := by unfold recCount; split_ifs <;> omega
      rw [hrec]
      simp only [h4, ↓reduceIte]
      constructor
      · have hb : ((mix k 1 (histFold k r q sched row ref n).1).testBit
            ((k - q + 3 * (r - (n + 1)) + min (q - 1) (histFold k r q sched row ref n).2.2 + 1) % k)).toNat ≤ 1 := by
          cases (mix k 1 (histFold k r q sched row ref n).1).testBit _ <;> decide
        have h1 := ih.1
        rw [Nat.pow_succ]
        omega
      · rw [bitWeight_step, ih.2]

lemma histFold_code_testBit (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref : Nat) :
    ∀ n m, m ≤ n →
      ∀ j < recCount m,
        (histFold k r q sched row ref n).2.1.testBit (j + (recCount n - recCount m)) =
          (histFold k r q sched row ref m).2.1.testBit j := by
  intro n
  induction n with
  | zero =>
    intro m hm j hj
    have hm0 : m = 0 := by omega
    subst hm0
    simp
  | succ n ih =>
    intro m hm j hj
    by_cases hmeq : m = n + 1
    · subst hmeq
      simp
    · have hmn : m ≤ n := by omega
      rw [histFold_succ]
      unfold histStep
      dsimp only
      by_cases h4 : n + 1 = 4
      · have hrec : recCount (n + 1) = recCount n := by unfold recCount; split_ifs <;> omega
        rw [hrec]
        simp only [h4, ↓reduceIte]
        exact ih m hmn j hj
      · have hrec : recCount (n + 1) = recCount n + 1 := by unfold recCount; split_ifs <;> omega
        have hrm : recCount m ≤ recCount n := by unfold recCount; split_ifs <;> omega
        simp only [h4, ↓reduceIte]
        have hidx : j + (recCount (n + 1) - recCount m) =
            (j + (recCount n - recCount m)) + 1 := by omega
        rw [hidx, Nat.testBit_succ]
        set bb := (mix k 1 (histFold k r q sched row ref n).1).testBit
          ((k - q + 3 * (r - (n + 1)) + min (q - 1) (histFold k r q sched row ref n).2.2 + 1) % k)
        have hdiv : (2 * (histFold k r q sched row ref n).2.1 + bb.toNat) / 2 =
            (histFold k r q sched row ref n).2.1 := by
          cases bb
          · simp
          · simp only [Bool.toNat_true]; omega
        rw [hdiv]
        exact ih m hmn j hj

lemma histFold_emit_bit (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref n ell : Nat)
    (hn : n + 1 ≤ ell) (h4 : n + 1 ≠ 4) :
    (histFold k r q sched row ref ell).2.1.testBit (recCount ell - recCount (n + 1)) =
      (mix k 1 (stateStep k r sched false ref row n)).testBit
        ((k - q + 3 * (r - (n + 1)) + min (q - 1) (histFold k r q sched row ref n).2.2 + 1) % k) := by
  have h1 := histFold_code_testBit k r q sched row ref ell (n + 1) hn 0
    (by unfold recCount; split_ifs <;> omega)
  simp only [Nat.zero_add] at h1
  rw [h1, histFold_succ]
  unfold histStep
  simp only [h4, ↓reduceIte, histFold_fst]
  cases (mix k 1 (stateStep k r sched false ref row n)).testBit _ <;> simp [Nat.testBit_zero]

def roundOf (s : Nat) : Nat := if s < 3 then s + 1 else s + 2

def targetCount (tries hist s : Nat) : Nat :=
  ((List.range s).filter (fun j => hist.testBit (tries - 1 - j))).length

lemma targetCount_zero (tries hist : Nat) : targetCount tries hist 0 = 0 := rfl

lemma targetCount_succ (tries hist s : Nat) :
    targetCount tries hist (s + 1) =
      targetCount tries hist s + (hist.testBit (tries - 1 - s)).toNat := by
  unfold targetCount
  rw [List.range_succ, List.filter_append, List.length_append]
  simp only [List.filter_cons, List.filter_nil]
  cases hist.testBit (tries - 1 - s) <;> simp

lemma targetCount_le (tries hist s : Nat) : targetCount tries hist s ≤ s := by
  induction s with
  | zero => simp [targetCount_zero]
  | succ s ih =>
    rw [targetCount_succ]
    cases hist.testBit (tries - 1 - s) <;> simp <;> omega

lemma histFold_cnt_of_prefix (k r q ell : Nat) (sched : Nat → Fin (2 ^ k)) (row ref hist : Nat)
    (_hell : 5 ≤ ell) :
    ∀ s ≤ ell - 1,
      (∀ j < s,
        (mix k 1 (stateStep k r sched false ref row (roundOf j - 1))).testBit
          ((k - q + 3 * (r - roundOf j) +
            min (q - 1) (histFold k r q sched row ref (roundOf j - 1)).2.2 + 1) % k) =
          hist.testBit (ell - 1 - 1 - j)) →
      (histFold k r q sched row ref (if s < 3 then s else s + 1)).2.2 =
        targetCount (ell - 1) hist s := by
  intro s
  induction s with
  | zero =>
    intro _ _
    simp [histFold_zero, targetCount_zero]
  | succ s ih =>
    intro hs hpre
    have hprev := ih (by omega) (fun j hj => hpre j (by omega))
    have hbit := hpre s (by omega)
    rw [targetCount_succ, ← hprev]
    by_cases hs2 : s < 2
    · have hs3 : s + 1 < 3 := by omega
      have hs3' : s < 3 := by omega
      have hro : roundOf s = s + 1 := by unfold roundOf; simp [hs3']
      simp only [hs3, hs3', ↓reduceIte] at hprev ⊢
      rw [hro, Nat.add_sub_cancel] at hbit
      rw [histFold_succ]
      unfold histStep
      have hne4 : s + 1 ≠ 4 := by omega
      simp only [hne4, ↓reduceIte, histFold_fst, hbit]
    · by_cases hs2eq : s = 2
      · subst hs2eq
        have hro : roundOf 2 = 3 := by unfold roundOf; decide
        rw [hro] at hbit
        simp only [show ¬ (2 + 1 < 3) by omega, show (2 < 3) by omega, ↓reduceIte] at hprev ⊢
        rw [histFold_succ]
        unfold histStep
        simp only [show 3 + 1 = 4 by decide, ↓reduceIte]
        rw [histFold_succ]
        unfold histStep
        simp only [show 2 + 1 ≠ 4 by decide, ↓reduceIte, histFold_fst]
        rw [hbit]
      · have hsge3 : 3 ≤ s := by omega
        have hro : roundOf s = s + 2 := by unfold roundOf; split_ifs <;> omega
        simp only [show ¬ (s + 1 < 3) by omega, show ¬ (s < 3) by omega, ↓reduceIte] at hprev ⊢
        rw [hro] at hbit
        have hsub : s + 2 - 1 = s + 1 := by omega
        rw [hsub] at hbit
        rw [histFold_succ]
        unfold histStep
        have hne4 : s + 1 + 1 ≠ 4 := by omega
        simp only [hne4, ↓reduceIte, histFold_fst]
        have heq1 : s + 1 + 1 = s + 2 := by omega
        rw [heq1, hbit]

lemma histFold_eq_iff_bits (k r q ell : Nat) (sched : Nat → Fin (2 ^ k)) (row ref hist : Nat)
    (hell : 5 ≤ ell) (hhist : hist < 2 ^ (ell - 1)) :
    (histFold k r q sched row ref ell).2.1 = hist ↔
      ∀ s < ell - 1,
        (mix k 1 (stateStep k r sched false ref row (roundOf s - 1))).testBit
          ((k - q + 3 * (r - roundOf s) +
            min (q - 1) (histFold k r q sched row ref (roundOf s - 1)).2.2 + 1) % k) =
          hist.testBit (ell - 1 - 1 - s) := by
  have hrec_ell : recCount ell = ell - 1 := by unfold recCount; split_ifs <;> omega
  have hlt_code : (histFold k r q sched row ref ell).2.1 < 2 ^ (ell - 1) := by
    rw [← hrec_ell]
    exact (histFold_code_weight k r q sched row ref ell).1
  constructor
  · intro heq s hs
    have hro_lt : roundOf s ≤ ell := by unfold roundOf; split_ifs <;> omega
    have hro_ne4 : roundOf s ≠ 4 := by unfold roundOf; split_ifs <;> omega
    have hro_pos : 1 ≤ roundOf s := by unfold roundOf; split_ifs <;> omega
    have hrec_ro : recCount (roundOf s) = s + 1 := by unfold roundOf recCount; split_ifs <;> omega
    have hem := histFold_emit_bit k r q sched row ref (roundOf s - 1) ell
      (by omega) (by omega)
    rw [Nat.sub_add_cancel hro_pos, hrec_ell, hrec_ro, heq] at hem
    have hidx : ell - 1 - (s + 1) = ell - 1 - 1 - s := by omega
    rw [hidx] at hem
    exact hem.symm
  · intro hbits
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < ell - 1
    · let s := ell - 1 - 1 - j
      have hs : s < ell - 1 := by omega
      have hj_eq : ell - 1 - 1 - s = j := by omega
      have hro_lt : roundOf s ≤ ell := by unfold roundOf; split_ifs <;> omega
      have hro_ne4 : roundOf s ≠ 4 := by unfold roundOf; split_ifs <;> omega
      have hro_pos : 1 ≤ roundOf s := by unfold roundOf; split_ifs <;> omega
      have hrec_ro : recCount (roundOf s) = s + 1 := by unfold roundOf recCount; split_ifs <;> omega
      have hem := histFold_emit_bit k r q sched row ref (roundOf s - 1) ell
        (by omega) (by omega)
      rw [Nat.sub_add_cancel hro_pos, hrec_ell, hrec_ro] at hem
      have hidx : ell - 1 - (s + 1) = j := by omega
      rw [hidx] at hem
      rw [hem, hbits s hs, hj_eq]
    · have hge : ell - 1 ≤ j := by omega
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt_code (Nat.pow_le_pow_right (by omega) hge)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hhist (Nat.pow_le_pow_right (by omega) hge))]

def pivOf (r q ell hist s : Nat) : Nat :=
  if s < 3 then
    (5 * r - 3) + 1 - q - 4 * (s + 1) + min (q - 1) (targetCount (ell - 1) hist s)
  else
    (5 * r - 3) + 5 - q - 5 * (s + 2) + min (q - 1) (targetCount (ell - 1) hist s)

lemma pivOf_lt (r q ell hist s : Nat) (hq : 0 < q) (hell5 : 5 ≤ ell) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (hs : s < ell - 1) :
    pivOf r q ell hist s < 5 * r - 3 - q := by
  unfold pivOf
  have hc : targetCount (ell - 1) hist s ≤ s := targetCount_le _ _ _
  split_ifs <;> omega

lemma pivOf_strictAnti (r q ell hist : Nat) (hq : 0 < q) (hell5 : 5 ≤ ell)
    (h5 : 5 * ell + q ≤ 5 * r + 2) :
    ∀ s1 s2, s1 < s2 → s2 < ell - 1 → pivOf r q ell hist s2 < pivOf r q ell hist s1 := by
  have hstep : ∀ s, s + 1 < ell - 1 → pivOf r q ell hist (s + 1) < pivOf r q ell hist s := by
    intro s hs
    unfold pivOf
    have hc1 := targetCount_succ (ell - 1) hist s
    have hble : (hist.testBit (ell - 1 - 1 - s)).toNat ≤ 1 := by
      cases hist.testBit _ <;> decide
    have hcle := targetCount_le (ell - 1) hist s
    have hcle1 := targetCount_le (ell - 1) hist (s + 1)
    split_ifs <;> omega
  intro s1 s2 hlt hs2
  obtain ⟨d, rfl⟩ : ∃ d, s2 = s1 + (d + 1) := ⟨s2 - s1 - 1, by omega⟩
  induction d with
  | zero => exact hstep s1 (by omega)
  | succ d ih =>
    exact lt_trans (hstep (s1 + (d + 1)) (by omega)) (ih (by omega) (by omega))

lemma pivOf_bit_pivot {k r q ell : Nat} {sched : Nat → Fin (2 ^ k)} {row : Nat}
    (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k) (hell5 : 5 ≤ ell) (hellr : ell ≤ r)
    (h5 : 5 * ell + q ≤ 5 * r + 2) (hrow : row < 2 ^ k)
    (hist : Nat) {s : Nat} (hs : s < ell - 1)
    {tag1 tag2 : Nat} (htag1 : tag1 < 2 ^ (5 * r - 3 - q)) (htag2 : tag2 < 2 ^ (5 * r - 3 - q))
    (hAgTag : ∀ j, pivOf r q ell hist s < j → j < 5 * r - 3 - q →
      tag1.testBit j = tag2.testBit j) :
    xor ((mix k 1 (stateStep k r sched false (rot k (k - (2 * r - 2)) tag1) row (roundOf s - 1))).testBit
          ((k - q + 3 * (r - roundOf s) + min (q - 1) (targetCount (ell - 1) hist s) + 1) % k))
        ((mix k 1 (stateStep k r sched false (rot k (k - (2 * r - 2)) tag2) row (roundOf s - 1))).testBit
          ((k - q + 3 * (r - roundOf s) + min (q - 1) (targetCount (ell - 1) hist s) + 1) % k)) =
      xor (tag1.testBit (pivOf r q ell hist s)) (tag2.testBit (pivOf r q ell hist s)) := by
  set start := k - (2 * r - 2)
  set ref1 := rot k start tag1
  set ref2 := rot k start tag2
  set t := roundOf s
  set d := min (q - 1) (targetCount (ell - 1) hist s)
  set place := k - q + 3 * (r - t) + d
  have hk_pos : 0 < k := by omega
  have huq_lt_k : 5 * r - 3 - q < k := by omega
  have htag1_k : tag1 < 2 ^ k :=
    lt_trans htag1 (Nat.pow_lt_pow_right (by omega) huq_lt_k)
  have htag2_k : tag2 < 2 ^ k :=
    lt_trans htag2 (Nat.pow_lt_pow_right (by omega) huq_lt_k)
  have href1_k : ref1 < 2 ^ k := rot_lt
  have href2_k : ref2 < 2 ^ k := rot_lt
  have ht1 : 1 ≤ t := by simp only [t, roundOf]; split_ifs <;> omega
  have ht4 : t ≠ 4 := by simp only [t, roundOf]; split_ifs <;> omega
  have htle : t ≤ ell := by simp only [t, roundOf]; split_ifs <;> omega
  have hdl : d ≤ q - 1 := Nat.min_le_left _ _
  have hdc : d ≤ s := le_trans (Nat.min_le_right _ _) (targetCount_le _ _ _)
  have hplace_ge : leftRow (t - 1) + 1 ≤ place + 1 := by
    simp only [place, leftRow, t, roundOf]
    split_ifs <;> omega
  have hpi_eq : place + 1 - (leftRow (t - 1) + 1) = start + pivOf r q ell hist s := by
    have hL : leftRow (t - 1) + 1 = if s < 3 then t + 1 else 2 * t - 3 := by
      simp only [leftRow, t, roundOf]
      split_ifs <;> omega
    rw [hL]
    simp only [place, start, pivOf, t, d, roundOf]
    split_ifs <;> omega
  have hhi_le : place + 1 + 3 * t - 2 ≤ start + k := by
    simp only [place, start]
    omega
  have hAgRef : AgreeOn k (place + 1 - (leftRow (t - 1) + 1) + 1) (place + 1 + 3 * t - 2)
      ref1 ref2 := by
    intro i hi1 hi2
    have hge_start : start ≤ i := by omega
    have hsub_lt_k : i - start < k := by omega
    have hsub_gt_piv : pivOf r q ell hist s < i - start := by omega
    rw [bitAt_rot_sub hk_pos htag1_k hge_start, bitAt_rot_sub hk_pos htag2_k hge_start,
      bitAt_lt hsub_lt_k, bitAt_lt hsub_lt_k]
    by_cases hlt_uq : i - start < 5 * r - 3 - q
    · exact hAgTag (i - start) hsub_gt_piv hlt_uq
    · have hge_uq : 5 * r - 3 - q ≤ i - start := by omega
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le htag1 (Nat.pow_le_pow_right (by omega) hge_uq)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le htag2 (Nat.pow_le_pow_right (by omega) hge_uq))]
  have hpiv := row_mix_pivot (r := r) (c := sched) (row := row) (by omega) hrow ht1 ht4
    href1_k href2_k hplace_ge hAgRef
  unfold bitAt at hpiv
  rw [hpi_eq] at hpiv
  have h1 : bitAt k ref1 (start + pivOf r q ell hist s) = tag1.testBit (pivOf r q ell hist s) := by
    rw [Nat.add_comm, bitAt_rot_add hk_pos htag1_k,
      bitAt_lt (lt_trans (pivOf_lt r q ell hist s hq hell5 h5 hs) huq_lt_k)]
  have h2 : bitAt k ref2 (start + pivOf r q ell hist s) = tag2.testBit (pivOf r q ell hist s) := by
    rw [Nat.add_comm, bitAt_rot_add hk_pos htag2_k,
      bitAt_lt (lt_trans (pivOf_lt r q ell hist s hq hell5 h5 hs) huq_lt_k)]
  unfold bitAt at h1 h2
  rw [h1, h2] at hpiv
  exact hpiv


lemma agree_step_false {k r : Nat} {c : Nat → Fin (2 ^ k)}
    {w w' X X' t lo hi loW hiW : Nat}
    (hk : 2 ≤ k) (hw : w < 2 ^ k) (hw' : w' < 2 ^ k) (hX : X < 2 ^ k) (hX' : X' < 2 ^ k)
    (hAgX : AgreeOn k lo hi X X') (hAgW : AgreeOn k loW hiW w w')
    (ht : 1 ≤ t) (hlo_ge : 2 * (t - 1) ≤ max (lo + 1) (loW + 2 * (t - 1))) :
    AgreeOn k (max (lo + 1) (loW + 2 * (t - 1))) (min (hi - 3) (hiW + 2 * (t - 1)))
      (step k r c false w X t) (step k r c false w' X' t) := by
  intro i hi1 hi2
  unfold step
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hxor3 : ∀ a b d, bitAt k (a ^^^ b ^^^ d) i =
      xor (xor (bitAt k a i) (bitAt k b i)) (bitAt k d i) := by
    intro a b d; simp [bitAt, Nat.testBit_xor]
  rw [hxor3, hxor3]
  have hM : ∀ d ≤ 2, bitAt k (mix k 1 X) (i + d) = bitAt k (mix k 1 X') (i + d) := by
    intro d hd
    rw [bitAt_mix (by omega) hX (by omega) (by omega),
      bitAt_mix (by omega) hX' (by omega) (by omega)]
    rw [hAgX (i + d) (by omega) (by omega),
      hAgX (i + d - 1) (by omega) (by omega),
      hAgX (i + d + 1) (by omega) (by omega)]
  have hM0 := hM 0 (by omega)
  simp only [Nat.add_zero] at hM0
  have hchi : bitAt k (chi k (mix k 1 X)) i = bitAt k (chi k (mix k 1 X')) i := by
    rw [bitAt_chi (by omega), bitAt_chi (by omega),
      hM0, hM 1 (by omega), hM 2 (by omega)]
  have hrot : bitAt k (rot k (2 * (t - 1)) w) i = bitAt k (rot k (2 * (t - 1)) w') i := by
    rw [bitAt_rot_sub (by omega) hw (by omega), bitAt_rot_sub (by omega) hw' (by omega)]
    exact hAgW (i - 2 * (t - 1)) (by omega) (by omega)
  rw [hchi, hrot]

lemma agree_step_false_guard {k r : Nat} {c : Nat → Fin (2 ^ k)}
    {w w' X X' t lo hi loW hiW : Nat}
    (hk : 2 ≤ k) (hw : w < 2 ^ k) (hw' : w' < 2 ^ k) (hX : X < 2 ^ k) (hX' : X' < 2 ^ k)
    (hAgX : AgreeOn k lo hi X X') (hAgW : AgreeOn k loW hiW w w')
    (ht : 1 ≤ t) (hlo_ge : 2 * (t - 1) ≤ max (lo + 1) (loW + 2 * (t - 1)))
    (hguard_bit : lo + 1 ≤ hi - 3 → bitAt k (mix k 1 X) (hi - 2) = true) :
    AgreeOn k (max (lo + 1) (loW + 2 * (t - 1))) (min (hi - 2) (hiW + 2 * (t - 1)))
      (step k r c false w X t) (step k r c false w' X' t) := by
  intro i hi1 hi2
  by_cases hlt : i < hi - 3
  · exact agree_step_false hk hw hw' hX hX' hAgX hAgW ht hlo_ge i hi1 (by omega)
  · have hieq : i = hi - 3 := by omega
    subst hieq
    have hguard_lo : lo + 1 ≤ hi - 3 := le_trans (le_max_left _ _) hi1
    unfold step
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hxor3 : ∀ a b d, bitAt k (a ^^^ b ^^^ d) (hi - 3) =
        xor (xor (bitAt k a (hi - 3)) (bitAt k b (hi - 3))) (bitAt k d (hi - 3)) := by
      intro a b d; simp [bitAt, Nat.testBit_xor]
    rw [hxor3, hxor3]
    have hM0 : bitAt k (mix k 1 X) (hi - 3) = bitAt k (mix k 1 X') (hi - 3) := by
      rw [bitAt_mix (by omega) hX (by omega) (by omega),
        bitAt_mix (by omega) hX' (by omega) (by omega)]
      rw [hAgX (hi - 3) (by omega) (by omega),
        hAgX (hi - 3 - 1) (by omega) (by omega),
        hAgX (hi - 3 + 1) (by omega) (by omega)]
    have hM1 : bitAt k (mix k 1 X) (hi - 3 + 1) = bitAt k (mix k 1 X') (hi - 3 + 1) := by
      rw [bitAt_mix (by omega) hX (by omega) (by omega),
        bitAt_mix (by omega) hX' (by omega) (by omega)]
      rw [hAgX (hi - 3 + 1) (by omega) (by omega),
        hAgX (hi - 3 + 1 - 1) (by omega) (by omega),
        hAgX (hi - 3 + 1 + 1) (by omega) (by omega)]
    have hgb : bitAt k (mix k 1 X) (hi - 3 + 1) = true := by
      have heq2 : hi - 3 + 1 = hi - 2 := by omega
      rw [heq2]
      exact hguard_bit hguard_lo
    have hchi : bitAt k (chi k (mix k 1 X)) (hi - 3) = bitAt k (chi k (mix k 1 X')) (hi - 3) := by
      rw [bitAt_chi (by omega), bitAt_chi (by omega), ← hM1, hgb, hM0]
      simp
    have hrot : bitAt k (rot k (2 * (t - 1)) w) (hi - 3) =
        bitAt k (rot k (2 * (t - 1)) w') (hi - 3) := by
      rw [bitAt_rot_sub (by omega) hw (by omega), bitAt_rot_sub (by omega) hw' (by omega)]
      exact hAgW (hi - 3 - 2 * (t - 1)) (by omega) (by omega)
    rw [hchi, hrot]

def loU (k r t : Nat) : Nat :=
  if t = 0 then k - 2 * r + 3
  else if t = 1 then k - 2 * r + 4
  else if t = 2 then k - 2 * r + 5
  else k - 2 * (r - t)

lemma histFold_cnt_le (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref t : Nat) :
    (histFold k r q sched row ref t).2.2 ≤ t := by
  have hcw := (histFold_code_weight k r q sched row ref t).2
  have hbl : bitWeight (recCount t) (histFold k r q sched row ref t).2.1 ≤ recCount t := by
    unfold bitWeight
    exact le_trans (List.length_filter_le _ _) (by simp)
  have hrec : recCount t ≤ t := by unfold recCount; split_ifs <;> omega
  omega

lemma loU_step {k r t : Nat} (hr : 5 ≤ r) (hk : 7 * r ≤ k) (ht : t + 1 ≤ r) :
    max (loU k r t + 1) (k - (2 * r - 2) + 2 * t) ≤ loU k r (t + 1) := by
  rw [max_le_iff]
  rcases t with _ | _ | _ | t
  · simp [loU]; omega
  · simp [loU]; omega
  · simp [loU]; omega
  · have h1 : loU k r (t + 3) = k - 2 * (r - (t + 3)) := by
      simp [loU, show t + 3 ≠ 1 by omega, show t + 3 ≠ 2 by omega]
    have h2 : loU k r (t + 4) = k - 2 * (r - (t + 4)) := by
      simp [loU, show t + 4 ≠ 1 by omega, show t + 4 ≠ 2 by omega]
    change loU k r (t + 3) + 1 ≤ loU k r (t + 4) ∧ k - (2 * r - 2) + 2 * (t + 3) ≤ loU k r (t + 4)
    rw [h1, h2]
    omega

lemma loU_ge {k r t : Nat} :
    2 * t ≤ max (loU k r t + 1) (k - (2 * r - 2) + 2 * t) := by
  rw [le_max_iff]
  right
  omega

lemma agree_row_vs_ref {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row : Fin (2 ^ k))
    (seedTag : Fin (2 ^ (5 * r - 3 - q)))
    (w : Nat) (hw : w < 2 ^ k)
    (hproj : AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w
      (rot k (k - (2 * r - 2)) seedTag.val)) :
    ∀ t ≤ ell,
      AgreeOn k (loU k r t)
        (k - q + 3 * (r - t) + min q (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) t).2.2)
        (stateStep k r sched false w row.val t)
        (stateStep k r sched false (rot k (k - (2 * r - 2)) seedTag.val) row.val t) := by
  set ref := rot k (k - (2 * r - 2)) seedTag.val
  have href : ref < 2 ^ k := rot_lt
  intro t ht
  induction t with
  | zero =>
    intro i hi1 hi2
    simp only [loU, histFold_zero, ↓reduceIte, Nat.sub_zero, Nat.min_zero, Nat.add_zero] at hi1 hi2
    rw [stateStep_zero, stateStep_zero]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hxor : ∀ a b, bitAt k (a ^^^ b) i = xor (bitAt k a i) (bitAt k b i) := by
      intro a b; simp [bitAt, Nat.testBit_xor]
    rw [hxor, hxor, bitAt_rot_sub (by omega) hw (by omega),
      bitAt_rot_sub (by omega) href (by omega)]
    rw [hproj (i - 1) (by omega) (by omega)]
  | succ t ih =>
    have hprev := ih (by omega)
    have hX1 : stateStep k r sched false w row.val t < 2 ^ k := stateStep_lt row.isLt
    have hX2 : stateStep k r sched false ref row.val t < 2 ^ k := stateStep_lt row.isLt
    set c_t := (histFold k r q sched row.val ref t).2.2
    have hc_le : c_t ≤ t := histFold_cnt_le k r q sched row.val ref t
    rw [stateStep_succ, stateStep_succ]
    have hlo_step := loU_step (k := k) (r := r) (t := t) (by omega) (by omega) (by omega)
    have hlo_ge := loU_ge (k := k) (r := r) (t := t)
    by_cases hguard : t + 1 ≠ 4 ∧ c_t < q ∧
        (mix k 1 (stateStep k r sched false ref row.val t)).testBit
          ((k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1) % k) = true
    · have hmin_eq : min q (histFold k r q sched row.val ref (t + 1)).2.2 = min q c_t + 1 := by
        rw [histFold_succ]
        unfold histStep
        simp only [hguard.1, ↓reduceIte, histFold_fst]
        rw [hguard.2.2]
        simp only [Bool.toNat_true]
        omega
      have hhi_eq : k - q + 3 * (r - t) + min q c_t - 2 =
          k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1 := by omega
      have hgb_w : loU k r t + 1 ≤ k - q + 3 * (r - t) + min q c_t - 3 →
          bitAt k (mix k 1 (stateStep k r sched false w row.val t))
            (k - q + 3 * (r - t) + min q c_t - 2) = true := by
        intro hguard_lo
        have hMeq : bitAt k (mix k 1 (stateStep k r sched false w row.val t))
            (k - q + 3 * (r - t) + min q c_t - 2) =
            bitAt k (mix k 1 (stateStep k r sched false ref row.val t))
              (k - q + 3 * (r - t) + min q c_t - 2) := by
          rw [bitAt_mix (by omega) hX1 (by omega) (by omega),
            bitAt_mix (by omega) hX2 (by omega) (by omega)]
          rw [hprev _ (by omega) (by omega),
            hprev _ (by omega) (by omega),
            hprev _ (by omega) (by omega)]
        rw [hMeq, hhi_eq]
        exact hguard.2.2
      have hst := agree_step_false_guard (r := r) (c := sched) (t := t + 1) (by omega) hw href hX1 hX2
        hprev hproj (by omega) (by simp) hgb_w
      simp only [Nat.add_sub_cancel] at hst
      rw [hmin_eq]
      exact agreeOn_mono hst hlo_step (by rw [le_min_iff]; omega)
    · have hmin_eq : min q (histFold k r q sched row.val ref (t + 1)).2.2 = min q c_t := by
        rw [histFold_succ]
        unfold histStep
        by_cases h4 : t + 1 = 4
        · simp [h4, c_t]
        · simp only [h4, ↓reduceIte, histFold_fst]
          by_cases hcq : c_t < q
          · have hb_false : (mix k 1 (stateStep k r sched false ref row.val t)).testBit
                ((k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1) % k) = false := by
              cases hb : (mix k 1 (stateStep k r sched false ref row.val t)).testBit _
              · rfl
              · exact absurd ⟨h4, hcq, hb⟩ hguard
            rw [hb_false]
            simp [c_t]
          · omega
      have hst := agree_step_false (r := r) (c := sched) (t := t + 1) (by omega) hw href hX1 hX2
        hprev hproj (by omega) (by simp)
      simp only [Nat.add_sub_cancel] at hst
      rw [hmin_eq]
      exact agreeOn_mono hst hlo_step (by rw [le_min_iff]; omega)

lemma loU_sub_step {k r a t : Nat} (hr : 5 ≤ r) (hk : 7 * r ≤ k) (ha : a ≤ k - (5 * r - 3))
    (ht : t + 1 ≤ r) :
    max (loU k r t - a + 1) (k - a - (2 * r - 2) + 2 * t) ≤ loU k r (t + 1) - a := by
  rw [max_le_iff]
  rcases t with _ | _ | _ | t
  · simp [loU]; omega
  · simp [loU]; omega
  · simp [loU]; omega
  · have h1 : loU k r (t + 3) = k - 2 * (r - (t + 3)) := by
      simp [loU, show t + 3 ≠ 1 by omega, show t + 3 ≠ 2 by omega]
    have h2 : loU k r (t + 4) = k - 2 * (r - (t + 4)) := by
      simp [loU, show t + 4 ≠ 1 by omega, show t + 4 ≠ 2 by omega]
    change loU k r (t + 3) - a + 1 ≤ loU k r (t + 4) - a ∧
      k - a - (2 * r - 2) + 2 * (t + 3) ≤ loU k r (t + 4) - a
    rw [h1, h2]
    omega

lemma loU_sub_ge {k r a t : Nat} :
    2 * t ≤ max (loU k r t - a + 1) (k - a - (2 * r - 2) + 2 * t) := by
  rw [le_max_iff]
  right
  omega

lemma agree_row_freeze {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row : Fin (2 ^ k))
    (seedTag : Fin (2 ^ (5 * r - 3 - q)))
    (hwt : q ≤ bitWeight (ell - 1)
      (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) ell).2.1)
    {w w' : Nat} (hw : w < 2 ^ k) (hw' : w' < 2 ^ k)
    (hproj1 : AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w
      (rot k (k - (2 * r - 2)) seedTag.val))
    (hproj2 : AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w'
      (rot k (k - (2 * r - 2)) seedTag.val))
    (hAgA : AgreeOn k (k - min ((k + 1) / 2) (k - (5 * r - 3)) - (2 * r - 2)) (k - (2 * r - 2)) w w') :
    (stateStep k r sched false w row.val r >>> (k - min ((k + 1) / 2) (k - (5 * r - 3)))) =
      (stateStep k r sched false w' row.val r >>> (k - min ((k + 1) / 2) (k - (5 * r - 3)))) := by
  set a := min ((k + 1) / 2) (k - (5 * r - 3))
  set ref := rot k (k - (2 * r - 2)) seedTag.val
  have ha_le : a ≤ k - (5 * r - 3) := Nat.min_le_right _ _
  have hAgW : AgreeOn k (k - a - (2 * r - 2)) (k + 3 * r - 1 - q) w w' := by
    intro i hi1 hi2
    by_cases hmid : i < k - (2 * r - 2)
    · exact hAgA i hi1 hmid
    · rw [hproj1 i (by omega) hi2, hproj2 i (by omega) hi2]
  have href_ag := agree_row_vs_ref hq hqr hk7 hell5 hellr h5 sched row seedTag w hw hproj1
  have hstep_all : ∀ t ≤ r,
      AgreeOn k (loU k r t - a)
        (k - q + 3 * (r - t) + min q (histFold k r q sched row.val ref (min t ell)).2.2)
        (stateStep k r sched false w row.val t)
        (stateStep k r sched false w' row.val t) := by
    intro t ht
    induction t with
    | zero =>
      intro i hi1 hi2
      simp only [loU, Nat.zero_min, histFold_zero, ↓reduceIte, Nat.sub_zero, Nat.min_zero,
        Nat.add_zero] at hi1 hi2
      rw [stateStep_zero, stateStep_zero]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hxor : ∀ x y, bitAt k (x ^^^ y) i = xor (bitAt k x i) (bitAt k y i) := by
        intro x y; simp [bitAt, Nat.testBit_xor]
      rw [hxor, hxor, bitAt_rot_sub (by omega) hw (by omega),
        bitAt_rot_sub (by omega) hw' (by omega)]
      rw [hAgW (i - 1) (by omega) (by omega)]
    | succ t ih =>
      have hprev := ih (by omega)
      have hX1 : stateStep k r sched false w row.val t < 2 ^ k := stateStep_lt row.isLt
      have hX2 : stateStep k r sched false w' row.val t < 2 ^ k := stateStep_lt row.isLt
      rw [stateStep_succ, stateStep_succ]
      have hlo_step := loU_sub_step (k := k) (r := r) (a := a) (t := t) (by omega) (by omega) ha_le (by omega)
      have hlo_ge := loU_sub_ge (k := k) (r := r) (a := a) (t := t)
      by_cases htle : t + 1 ≤ ell
      · have hmin1 : min (t + 1) ell = t + 1 := Nat.min_eq_left htle
        have hmin0 : min t ell = t := Nat.min_eq_left (by omega)
        rw [hmin1]
        rw [hmin0] at hprev
        set c_t := (histFold k r q sched row.val ref t).2.2
        have hc_le : c_t ≤ t := histFold_cnt_le k r q sched row.val ref t
        have href_t : AgreeOn k (loU k r t) (k - q + 3 * (r - t) + min q c_t)
            (stateStep k r sched false w row.val t)
            (stateStep k r sched false ref row.val t) := href_ag t (by omega)
        have hXref : stateStep k r sched false ref row.val t < 2 ^ k := stateStep_lt row.isLt
        by_cases hguard : t + 1 ≠ 4 ∧ c_t < q ∧
            (mix k 1 (stateStep k r sched false ref row.val t)).testBit
              ((k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1) % k) = true
        · have hmin_eq : min q (histFold k r q sched row.val ref (t + 1)).2.2 = min q c_t + 1 := by
            rw [histFold_succ]
            unfold histStep
            simp only [hguard.1, ↓reduceIte, histFold_fst]
            rw [hguard.2.2]
            simp only [Bool.toNat_true]
            omega
          have hhi_eq : k - q + 3 * (r - t) + min q c_t - 2 =
              k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1 := by omega
          have hlo_ref : loU k r t ≤ k - q + 3 * (r - t) + min q c_t - 3 := by
            unfold loU
            split_ifs <;> omega
          have hgb_w : loU k r t - a + 1 ≤ k - q + 3 * (r - t) + min q c_t - 3 →
              bitAt k (mix k 1 (stateStep k r sched false w row.val t))
                (k - q + 3 * (r - t) + min q c_t - 2) = true := by
            intro _
            have hMeq : bitAt k (mix k 1 (stateStep k r sched false w row.val t))
                (k - q + 3 * (r - t) + min q c_t - 2) =
                bitAt k (mix k 1 (stateStep k r sched false ref row.val t))
                  (k - q + 3 * (r - t) + min q c_t - 2) := by
              rw [bitAt_mix (by omega) hX1 (by omega) (by omega),
                bitAt_mix (by omega) hXref (by omega) (by omega)]
              rw [href_t _ (by omega) (by omega),
                href_t _ (by omega) (by omega),
                href_t _ (by omega) (by omega)]
            rw [hMeq, hhi_eq]
            exact hguard.2.2
          have hst := agree_step_false_guard (r := r) (c := sched) (t := t + 1) (by omega) hw hw' hX1 hX2
            hprev hAgW (by omega) (by simp) hgb_w
          simp only [Nat.add_sub_cancel] at hst
          rw [hmin_eq]
          exact agreeOn_mono hst hlo_step (by rw [le_min_iff]; omega)
        · have hmin_eq : min q (histFold k r q sched row.val ref (t + 1)).2.2 = min q c_t := by
            rw [histFold_succ]
            unfold histStep
            by_cases h4 : t + 1 = 4
            · simp [h4, c_t]
            · simp only [h4, ↓reduceIte, histFold_fst]
              by_cases hcq : c_t < q
              · have hb_false : (mix k 1 (stateStep k r sched false ref row.val t)).testBit
                    ((k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1) % k) = false := by
                  cases hb : (mix k 1 (stateStep k r sched false ref row.val t)).testBit _
                  · rfl
                  · exact absurd ⟨h4, hcq, hb⟩ hguard
                rw [hb_false]
                simp [c_t]
              · omega
          have hst := agree_step_false (r := r) (c := sched) (t := t + 1) (by omega) hw hw' hX1 hX2
            hprev hAgW (by omega) (by simp)
          simp only [Nat.add_sub_cancel] at hst
          rw [hmin_eq]
          exact agreeOn_mono hst hlo_step (by rw [le_min_iff]; omega)
      · have hmin1 : min (t + 1) ell = ell := Nat.min_eq_right (by omega)
        have hmin0 : min t ell = ell := Nat.min_eq_right (by omega)
        rw [hmin1]
        rw [hmin0] at hprev
        have hc_ell : (histFold k r q sched row.val ref ell).2.2 ≤ ell :=
          histFold_cnt_le k r q sched row.val ref ell
        have hst := agree_step_false (r := r) (c := sched) (t := t + 1) (by omega) hw hw' hX1 hX2
          hprev hAgW (by omega) (by simp)
        simp only [Nat.add_sub_cancel] at hst
        exact agreeOn_mono hst hlo_step (by rw [le_min_iff]; omega)
  have hfin := hstep_all r (le_refl _)
  have hlo_r : loU k r r - a = k - a := by unfold loU; split_ifs <;> omega
  have hmin_r : min r ell = ell := Nat.min_eq_right hellr
  have hrec_ell : recCount ell = ell - 1 := by unfold recCount; split_ifs <;> omega
  have hcnt_eq : (histFold k r q sched row.val ref ell).2.2 =
      bitWeight (ell - 1) (histFold k r q sched row.val ref ell).2.1 := by
    rw [← hrec_ell]
    exact (histFold_code_weight k r q sched row.val ref ell).2
  have hmin_q : min q (histFold k r q sched row.val ref ell).2.2 = q := by
    rw [hcnt_eq]
    exact Nat.min_eq_left hwt
  rw [hlo_r, hmin_r, hmin_q, Nat.sub_self, Nat.mul_zero, Nat.add_zero,
    Nat.sub_add_cancel (by omega)] at hfin
  have hXr1 : stateStep k r sched false w row.val r < 2 ^ k := stateStep_lt row.isLt
  have hXr2 : stateStep k r sched false w' row.val r < 2 ^ k := stateStep_lt row.isLt
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  by_cases hj : j < a
  · have hlt : k - a + j < k := by omega
    have hbit := hfin (k - a + j) (by omega) hlt
    rwa [bitAt_lt hlt, bitAt_lt hlt] at hbit
  · have hge : k ≤ k - a + j := by omega
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hXr1 (Nat.pow_le_pow_right (by omega) hge)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hXr2 (Nat.pow_le_pow_right (by omega) hge))]

lemma project_iff_agree {k r q : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (seedTag : Fin (2 ^ (5 * r - 3 - q))) (w : Nat) (hw : w < 2 ^ k) :
    rot k (k - (k - (2 * r - 2)) % k) w % 2 ^ (5 * r - 3 - q) = seedTag.val ↔
      AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w (rot k (k - (2 * r - 2)) seedTag.val) := by
  set start := k - (2 * r - 2)
  have hk_pos : 0 < k := by omega
  have huq_lt : 5 * r - 3 - q < k := by omega
  have hseed_k : seedTag.val < 2 ^ k :=
    lt_trans seedTag.isLt (Nat.pow_lt_pow_right (by omega) huq_lt)
  constructor
  · intro heq i hi1 hi2
    have hs_lt : i - start < 5 * r - 3 - q := by omega
    have hbit : (rot k (k - start % k) w % 2 ^ (5 * r - 3 - q)).testBit (i - start) =
        seedTag.val.testBit (i - start) := by rw [heq]
    simp only [Nat.testBit_mod_two_pow, hs_lt, decide_true, Bool.true_and] at hbit
    have h1 : bitAt k (rot k (k - start % k) w) (i - start) = bitAt k w i := by
      have hr := bitAt_rot_rev (k := k) (offset := start) (x := w) (i := i - start) hk_pos hw
      rwa [Nat.sub_add_cancel hi1] at hr
    have h2 : bitAt k (rot k start seedTag.val) i = seedTag.val.testBit (i - start) := by
      rw [bitAt_rot_sub hk_pos hseed_k hi1, bitAt_lt (lt_trans hs_lt huq_lt)]
    rw [h2, ← hbit, ← h1, bitAt_lt (lt_trans hs_lt huq_lt)]
  · intro hAg
    apply Nat.eq_of_testBit_eq
    intro s
    rw [Nat.testBit_mod_two_pow]
    by_cases hs : s < 5 * r - 3 - q
    · simp only [hs, decide_true, Bool.true_and]
      have h1 : bitAt k (rot k (k - start % k) w) s = bitAt k w (s + start) :=
        bitAt_rot_rev (k := k) (offset := start) (x := w) (i := s) hk_pos hw
      have h2 : bitAt k (rot k start seedTag.val) (s + start) = seedTag.val.testBit s := by
        rw [bitAt_rot_add hk_pos hseed_k, bitAt_lt (lt_trans hs huq_lt)]
      rw [← bitAt_lt (lt_trans hs huq_lt), h1, hAg (s + start) (by omega) (by omega), h2]
    · simp only [hs, decide_false, Bool.false_and]
      have hge : 5 * r - 3 - q ≤ s := by omega
      exact (Nat.testBit_lt_two_pow
        (lt_of_lt_of_le seedTag.isLt (Nat.pow_le_pow_right (by omega) hge))).symm

lemma project_iff_outside {k r q : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (seedTag : Fin (2 ^ (5 * r - 3 - q))) (w : Nat) :
    AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w (rot k (k - (2 * r - 2)) seedTag.val) ↔
      ∀ s < k, (s < 3 * r - 1 - q ∨ k - (2 * r - 2) ≤ s) →
        w.testBit s = (rot k (k - (2 * r - 2)) seedTag.val).testBit s := by
  constructor
  · intro hAg s hsk hso
    rcases hso with hlt | hge
    · have h1 := hAg (k + s) (by omega) (by omega)
      rw [Nat.add_comm, bitAt_add_k, bitAt_add_k, bitAt_lt hsk, bitAt_lt hsk] at h1
      exact h1
    · have h1 := hAg s hge (by omega)
      rwa [bitAt_lt hsk, bitAt_lt hsk] at h1
  · intro hout i hi1 hi2
    by_cases hik : i < k
    · rw [bitAt_lt hik, bitAt_lt hik]
      exact hout i hik (Or.inr hi1)
    · have hsub : i - k < 3 * r - 1 - q := by omega
      have hsk : i - k < k := by omega
      have hrew : i = (i - k) + k := by omega
      rw [hrew, bitAt_add_k, bitAt_add_k, bitAt_lt hsk, bitAt_lt hsk]
      exact hout (i - k) hsk (Or.inl hsub)

def recoverRaw (k r q missed : Nat) (sched : Nat → Fin (2 ^ k))
    (row col seed spare rowBits colBits : Nat) : Nat :=
  let h := (k + 1) / 2
  let z := k - h
  let u := 5 * r - 3
  let start := k - (2 * r - 2)
  let a := min h (k - u)
  let g := z - u
  let baseA := k - a - (2 * r - 2)
  let baseQG := 3 * r - 1 - q
  let w0 := if missed = 0 then rot k start seed else
    ofBits k (fun s => if start - missed ≤ s ∧ s < start then spare.testBit (s - (start - missed))
      else (rot k start seed).testBit s)
  let w1 := solveTri baseA (a - missed) (fun w =>
    let part := stateStep k r sched false w row r >>> (k - a)
    if missed = 0 then part else part % 2 ^ (a - missed)) rowBits w0
  solveTri baseQG (q + g) (fun w =>
    (stateStep k r sched true w col r >>> (6 * r - q)) % 2 ^ (q + g)) colBits w1

def recoverGood (k r q missed : Nat) (sched : Nat → Fin (2 ^ k))
    (row col tag spare rowBits colBits : Nat) (w : Fin (2 ^ k)) : Prop :=
  let h := (k + 1) / 2
  let z := k - h
  let a := min h (k - (5 * r - 3))
  let start := k - (2 * r - 2)
  rot k (k - start % k) w.val % 2 ^ (5 * r - 3 - q) = tag ∧
    (if missed = 0 then
      (stateStep k r sched false w.val row r >>> (k - a)) = rowBits
    else
      (w.val >>> (start - missed)) % 2 ^ missed = spare ∧
      (stateStep k r sched false w.val row r >>> (k - a)) % 2 ^ (a - missed) = rowBits) ∧
    (stateStep k r sched true w.val col r >>> (6 * r - q)) % 2 ^ (q + (z - (5 * r - 3))) = colBits

lemma part2_unique {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row col : Fin (2 ^ k))
    (seedTag : Fin (2 ^ (5 * r - 3 - q)))
    (rowBits : Fin (2 ^ (min ((k + 1) / 2) (k - (5 * r - 3)))))
    (colBits : Fin (2 ^ (q + ((k - (k + 1) / 2) - (5 * r - 3)))))
    (hwt : q ≤ bitWeight (ell - 1)
      (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) ell).2.1) :
    let P := recoverGood k r q 0 sched row.val col.val seedTag.val 0 rowBits.val colBits.val
    ∃ w : Fin (2 ^ k),
      w.val = recoverRaw k r q 0 sched row.val col.val seedTag.val 0 rowBits.val colBits.val ∧
      P w ∧ ∀ w', P w' → w' = w := by
  simp only [recoverGood, ↓reduceIte]
  let h := (k + 1) / 2
  let z := k - h
  let u := 5 * r - 3
  let start := k - (2 * r - 2)
  let a := min h (k - u)
  let g := z - u
  have hsum_ag : a + g = k - u := by
    simp only [a, g, z, h, u]
    omega
  set baseQG := 3 * r - 1 - q
  set baseA := k - a - (2 * r - 2)
  have hmid_eq : baseQG + (q + g) = baseA := by
    simp only [baseQG, baseA]
    omega
  have hA_end : baseA + a = start := by
    simp only [baseA, start]
    omega
  have hrow_tri : ∀ j < a, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ s < k, (s < baseA ∨ baseA + j < s) → w.testBit s = w'.testBit s) →
      xor ((stateStep k r sched false w row.val r >>> (k - a)).testBit j)
          ((stateStep k r sched false w' row.val r >>> (k - a)).testBit j) =
        xor (w.testBit (baseA + j)) (w'.testBit (baseA + j)) := by
    intro j hj w w' hw hw' hout
    rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    have hi_lt : k - a + j < k := by omega
    rw [← bitAt_lt hi_lt, ← bitAt_lt hi_lt]
    have hL : leftRow r = 2 * (r - 1) := by unfold leftRow; omega
    have hAg : AgreeOn k (k - a + j - leftRow r + 1) (k - a + j + 3 * r) w w' := by
      intro i hi1 hi2
      by_cases hik : i < k
      · rw [bitAt_lt hik, bitAt_lt hik]
        exact hout i hik (Or.inr (by omega))
      · have hlt_base : i - k < baseA := by omega
        have hsk : i - k < k := by omega
        have hrew : i = (i - k) + k := by omega
        rw [hrew, bitAt_add_k, bitAt_add_k, bitAt_lt hsk, bitAt_lt hsk]
        exact hout (i - k) hsk (Or.inl hlt_base)
    have hpiv := row_pivot (r := r) (c := sched) (row := row.val) (by omega) row.isLt r (by omega)
      w w' (k - a + j) hw hw' (by omega) hAg
    have hidx : k - a + j - leftRow r = baseA + j := by omega
    rw [hidx] at hpiv
    simpa [bitAt_lt hi_lt, bitAt_lt (show baseA + j < k by omega)] using hpiv
  have hcol_tri : ∀ j < q + g, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ s < k, (s < baseQG ∨ baseQG + j < s) → w.testBit s = w'.testBit s) →
      xor (((stateStep k r sched true w col.val r >>> (6 * r - q)) % 2 ^ (q + g)).testBit j)
          (((stateStep k r sched true w' col.val r >>> (6 * r - q)) % 2 ^ (q + g)).testBit j) =
        xor (w.testBit (baseQG + j)) (w'.testBit (baseQG + j)) := by
    intro j hj w w' hw hw' hout
    simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and, Nat.testBit_shiftRight]
    have h6rg : 6 * r + g ≤ k := by
      simp only [g, z, h, u]
      omega
    have hi_lt : 6 * r - q + j < k := by omega
    rw [← bitAt_lt hi_lt, ← bitAt_lt hi_lt]
    have hwrap : 6 * r - q + j + 4 * r - 2 ≤ k + baseQG := by
      simp only [baseQG, g, z, h, u] at hj ⊢
      omega
    have hAg : AgreeOn k (6 * r - q + j - (3 * r + 1) + 1) (6 * r - q + j + 4 * r - 2) w w' := by
      intro i hi1 hi2
      by_cases hik : i < k
      · rw [bitAt_lt hik, bitAt_lt hik]
        exact hout i hik (Or.inr (by omega))
      · have hlt_base : i - k < baseQG := by omega
        have hsk : i - k < k := by omega
        have hrew : i = (i - k) + k := by omega
        rw [hrew, bitAt_add_k, bitAt_add_k, bitAt_lt hsk, bitAt_lt hsk]
        exact hout (i - k) hsk (Or.inl hlt_base)
    have hpiv := col_pivot (r := r) (c := sched) (col := col.val) (by omega) col.isLt (t := r) (by omega)
      hw hw' (i := 6 * r - q + j) (by omega) hAg
    have hidx : 6 * r - q + j - (3 * r + 1) = baseQG + j := by omega
    rw [hidx] at hpiv
    simpa [bitAt_lt hi_lt, bitAt_lt (show baseQG + j < k by omega)] using hpiv
  let w0 := rot k start seedTag.val
  have hw0 : w0 < 2 ^ k := rot_lt
  obtain ⟨hw1, hw1_out, hw1_row⟩ := solveTri_spec (k := k) (base := baseA) (m := a) (by omega)
    (fun w => stateStep k r sched false w row.val r >>> (k - a))
    (fun w _ => shiftRight_lt_two_pow (stateStep_lt row.isLt) (by omega))
    hrow_tri w0 hw0 rowBits.val rowBits.isLt
  let w1 : Fin (2 ^ k) := ⟨_, hw1⟩
  obtain ⟨hw2, hw2_out, hw2_col⟩ := solveTri_spec (k := k) (base := baseQG) (m := q + g) (by omega)
    (fun w => (stateStep k r sched true w col.val r >>> (6 * r - q)) % 2 ^ (q + g))
    (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _))
    hcol_tri w1.val w1.isLt colBits.val colBits.isLt
  let w2 : Fin (2 ^ k) := ⟨_, hw2⟩
  have hw1_proj_ag : AgreeOn k start (k + 3 * r - 1 - q) w1.val w0 := by
    rw [project_iff_outside hq hqr hk7 seedTag w1.val]
    intro s hsk hso
    apply hw1_out s hsk
    rcases hso with hlt | hge
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hw2_proj_ag : AgreeOn k start (k + 3 * r - 1 - q) w2.val w0 := by
    rw [project_iff_outside hq hqr hk7 seedTag w2.val]
    intro s hsk hso
    have h1 : w2.val.testBit s = w1.val.testBit s := by
      apply hw2_out s hsk
      rcases hso with hlt | hge
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [h1]
    exact (project_iff_outside hq hqr hk7 seedTag w1.val).mp hw1_proj_ag s hsk hso
  have hw2_proj : rot k (k - start % k) w2.val % 2 ^ (u - q) = seedTag.val :=
    (project_iff_agree hq hqr hk7 seedTag w2.val w2.isLt).mpr hw2_proj_ag
  have hw2_agA : AgreeOn k baseA start w2.val w1.val := by
    intro i hi1 hi2
    have hik : i < k := by omega
    rw [bitAt_lt hik, bitAt_lt hik]
    exact hw2_out i hik (Or.inr (by omega))
  have hw2_row : (stateStep k r sched false w2.val row.val r >>> (k - a)) = rowBits.val := by
    have hfr := agree_row_freeze hq hqr hk7 hell5 hellr h5 sched row seedTag hwt
      w2.isLt w1.isLt hw2_proj_ag hw1_proj_ag hw2_agA
    rw [hfr, hw1_row]
  refine ⟨w2, rfl, ⟨hw2_proj, hw2_row, hw2_col⟩, ?_⟩
  rintro w3 ⟨hw3_proj, hw3_row, hw3_col⟩
  have hw3_proj_ag : AgreeOn k start (k + 3 * r - 1 - q) w3.val w0 :=
    (project_iff_agree hq hqr hk7 seedTag w3.val w3.isLt).mp hw3_proj
  let wMix := ofBits k (fun j => if baseA ≤ j ∧ j < start then w3.val.testBit j else w2.val.testBit j)
  have hwMix_lt : wMix < 2 ^ k := ofBits_lt k _
  have hwMix_proj_ag : AgreeOn k start (k + 3 * r - 1 - q) wMix w0 := by
    rw [project_iff_outside hq hqr hk7 seedTag wMix]
    intro s hsk hso
    have hnotA : ¬ (baseA ≤ s ∧ s < start) := by
      rcases hso with hlt | hge <;> omega
    simp only [wMix, ofBits_testBit, hsk, hnotA, ↓reduceIte]
    exact (project_iff_outside hq hqr hk7 seedTag w2.val).mp hw2_proj_ag s hsk hso
  have hwMix_agA : AgreeOn k baseA start wMix w3.val := by
    intro i hi1 hi2
    have hik : i < k := by omega
    simp [bitAt_lt hik, wMix, ofBits_testBit, hik, hi1, hi2]
  have hwMix_row : (stateStep k r sched false wMix row.val r >>> (k - a)) = rowBits.val := by
    have hfr := agree_row_freeze hq hqr hk7 hell5 hellr h5 sched row seedTag hwt
      hwMix_lt w3.isLt hwMix_proj_ag hw3_proj_ag hwMix_agA
    rw [hfr, hw3_row]
  have hwMix_eq_w2 : (⟨wMix, hwMix_lt⟩ : Fin (2 ^ k)) = w2 := by
    have huniqA := triangular_solve (k := k) (base := baseA) (m := a) (by omega)
      (fun w => stateStep k r sched false w row.val r >>> (k - a))
      (fun w _ => shiftRight_lt_two_pow (stateStep_lt row.isLt) (by omega))
      hrow_tri w2.val w2.isLt rowBits.val rowBits.isLt
    rcases huniqA with ⟨wU, _, hU⟩
    have h1 : (⟨wMix, hwMix_lt⟩ : Fin (2 ^ k)) = wU := by
      apply hU
      refine ⟨?_, hwMix_row⟩
      intro s hsk hso
      have hnotA : ¬ (baseA ≤ s ∧ s < start) := by rcases hso with hlt | hge <;> omega
      simp only [wMix, ofBits_testBit, hsk, hnotA, ↓reduceIte]
    have h2 : w2 = wU := hU w2 ⟨fun _ _ _ => rfl, hw2_row⟩
    rw [h1, h2]
  have hw3_eq_w2_A : ∀ s < k, (s < baseQG ∨ baseQG + (q + g) ≤ s) →
      w3.val.testBit s = w2.val.testBit s := by
    intro s hsk hso
    rcases hso with hlt | hge
    · rw [(project_iff_outside hq hqr hk7 seedTag w3.val).mp hw3_proj_ag s hsk (Or.inl hlt),
        (project_iff_outside hq hqr hk7 seedTag w2.val).mp hw2_proj_ag s hsk (Or.inl hlt)]
    · by_cases hst : start ≤ s
      · rw [(project_iff_outside hq hqr hk7 seedTag w3.val).mp hw3_proj_ag s hsk (Or.inr hst),
          (project_iff_outside hq hqr hk7 seedTag w2.val).mp hw2_proj_ag s hsk (Or.inr hst)]
      · have hval : wMix = w2.val := congrArg Fin.val hwMix_eq_w2
        have hbit : wMix.testBit s = w2.val.testBit s := by rw [hval]
        have hin : baseA ≤ s ∧ s < start := ⟨by omega, by omega⟩
        simp only [wMix, ofBits_testBit, hsk, hin, ↓reduceIte] at hbit
        exact hbit
  have huniqQG := triangular_solve (k := k) (base := baseQG) (m := q + g) (by omega)
    (fun w => (stateStep k r sched true w col.val r >>> (6 * r - q)) % 2 ^ (q + g))
    (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _))
    hcol_tri w2.val w2.isLt colBits.val colBits.isLt
  rcases huniqQG with ⟨wU, _, hU⟩
  have h1 : w3 = wU := hU w3 ⟨hw3_eq_w2_A, hw3_col⟩
  have h2 : w2 = wU := hU w2 ⟨fun _ _ _ => rfl, hw2_col⟩
  rw [h1, h2]

lemma agree_row_freeze_lo {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row : Fin (2 ^ k))
    (seedTag : Fin (2 ^ (5 * r - 3 - q)))
    (hwt : bitWeight (ell - 1)
      (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) ell).2.1 < q)
    {w w' : Nat} (hw : w < 2 ^ k) (hw' : w' < 2 ^ k)
    (hproj1 : AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w
      (rot k (k - (2 * r - 2)) seedTag.val))
    (hproj2 : AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w'
      (rot k (k - (2 * r - 2)) seedTag.val))
    (hAgA : AgreeOn k (k - min ((k + 1) / 2) (k - (5 * r - 3)) - (2 * r - 2)) (k - (2 * r - 2)) w w') :
    (stateStep k r sched false w row.val r >>> (k - min ((k + 1) / 2) (k - (5 * r - 3)))) %
        2 ^ (min ((k + 1) / 2) (k - (5 * r - 3)) - (q - bitWeight (ell - 1)
          (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) ell).2.1)) =
      (stateStep k r sched false w' row.val r >>> (k - min ((k + 1) / 2) (k - (5 * r - 3)))) %
        2 ^ (min ((k + 1) / 2) (k - (5 * r - 3)) - (q - bitWeight (ell - 1)
          (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) ell).2.1)) := by
  set a := min ((k + 1) / 2) (k - (5 * r - 3))
  set ref := rot k (k - (2 * r - 2)) seedTag.val
  have ha_le : a ≤ k - (5 * r - 3) := Nat.min_le_right _ _
  have hAgW : AgreeOn k (k - a - (2 * r - 2)) (k + 3 * r - 1 - q) w w' := by
    intro i hi1 hi2
    by_cases hmid : i < k - (2 * r - 2)
    · exact hAgA i hi1 hmid
    · rw [hproj1 i (by omega) hi2, hproj2 i (by omega) hi2]
  have href_ag := agree_row_vs_ref hq hqr hk7 hell5 hellr h5 sched row seedTag w hw hproj1
  have hstep_all : ∀ t ≤ r,
      AgreeOn k (loU k r t - a)
        (k - q + 3 * (r - t) + min q (histFold k r q sched row.val ref (min t ell)).2.2)
        (stateStep k r sched false w row.val t)
        (stateStep k r sched false w' row.val t) := by
    intro t ht
    induction t with
    | zero =>
      intro i hi1 hi2
      simp only [loU, Nat.zero_min, histFold_zero, ↓reduceIte, Nat.sub_zero, Nat.min_zero,
        Nat.add_zero] at hi1 hi2
      rw [stateStep_zero, stateStep_zero]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hxor : ∀ x y, bitAt k (x ^^^ y) i = xor (bitAt k x i) (bitAt k y i) := by
        intro x y; simp [bitAt, Nat.testBit_xor]
      rw [hxor, hxor, bitAt_rot_sub (by omega) hw (by omega),
        bitAt_rot_sub (by omega) hw' (by omega)]
      rw [hAgW (i - 1) (by omega) (by omega)]
    | succ t ih =>
      have hprev := ih (by omega)
      have hX1 : stateStep k r sched false w row.val t < 2 ^ k := stateStep_lt row.isLt
      have hX2 : stateStep k r sched false w' row.val t < 2 ^ k := stateStep_lt row.isLt
      rw [stateStep_succ, stateStep_succ]
      have hlo_step := loU_sub_step (k := k) (r := r) (a := a) (t := t) (by omega) (by omega) ha_le (by omega)
      have hlo_ge := loU_sub_ge (k := k) (r := r) (a := a) (t := t)
      by_cases htle : t + 1 ≤ ell
      · have hmin1 : min (t + 1) ell = t + 1 := Nat.min_eq_left htle
        have hmin0 : min t ell = t := Nat.min_eq_left (by omega)
        rw [hmin1]
        rw [hmin0] at hprev
        set c_t := (histFold k r q sched row.val ref t).2.2
        have hc_le : c_t ≤ t := histFold_cnt_le k r q sched row.val ref t
        have href_t : AgreeOn k (loU k r t) (k - q + 3 * (r - t) + min q c_t)
            (stateStep k r sched false w row.val t)
            (stateStep k r sched false ref row.val t) := href_ag t (by omega)
        have hXref : stateStep k r sched false ref row.val t < 2 ^ k := stateStep_lt row.isLt
        by_cases hguard : t + 1 ≠ 4 ∧ c_t < q ∧
            (mix k 1 (stateStep k r sched false ref row.val t)).testBit
              ((k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1) % k) = true
        · have hmin_eq : min q (histFold k r q sched row.val ref (t + 1)).2.2 = min q c_t + 1 := by
            rw [histFold_succ]
            unfold histStep
            simp only [hguard.1, ↓reduceIte, histFold_fst]
            rw [hguard.2.2]
            simp only [Bool.toNat_true]
            omega
          have hhi_eq : k - q + 3 * (r - t) + min q c_t - 2 =
              k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1 := by omega
          have hlo_ref : loU k r t ≤ k - q + 3 * (r - t) + min q c_t - 3 := by
            unfold loU
            split_ifs <;> omega
          have hgb_w : loU k r t - a + 1 ≤ k - q + 3 * (r - t) + min q c_t - 3 →
              bitAt k (mix k 1 (stateStep k r sched false w row.val t))
                (k - q + 3 * (r - t) + min q c_t - 2) = true := by
            intro _
            have hMeq : bitAt k (mix k 1 (stateStep k r sched false w row.val t))
                (k - q + 3 * (r - t) + min q c_t - 2) =
                bitAt k (mix k 1 (stateStep k r sched false ref row.val t))
                  (k - q + 3 * (r - t) + min q c_t - 2) := by
              rw [bitAt_mix (by omega) hX1 (by omega) (by omega),
                bitAt_mix (by omega) hXref (by omega) (by omega)]
              rw [href_t _ (by omega) (by omega),
                href_t _ (by omega) (by omega),
                href_t _ (by omega) (by omega)]
            rw [hMeq, hhi_eq]
            exact hguard.2.2
          have hst := agree_step_false_guard (r := r) (c := sched) (t := t + 1) (by omega) hw hw' hX1 hX2
            hprev hAgW (by omega) (by simp) hgb_w
          simp only [Nat.add_sub_cancel] at hst
          rw [hmin_eq]
          exact agreeOn_mono hst hlo_step (by rw [le_min_iff]; omega)
        · have hmin_eq : min q (histFold k r q sched row.val ref (t + 1)).2.2 = min q c_t := by
            rw [histFold_succ]
            unfold histStep
            by_cases h4 : t + 1 = 4
            · simp [h4, c_t]
            · simp only [h4, ↓reduceIte, histFold_fst]
              by_cases hcq : c_t < q
              · have hb_false : (mix k 1 (stateStep k r sched false ref row.val t)).testBit
                    ((k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1) % k) = false := by
                  cases hb : (mix k 1 (stateStep k r sched false ref row.val t)).testBit _
                  · rfl
                  · exact absurd ⟨h4, hcq, hb⟩ hguard
                rw [hb_false]
                simp [c_t]
              · omega
          have hst := agree_step_false (r := r) (c := sched) (t := t + 1) (by omega) hw hw' hX1 hX2
            hprev hAgW (by omega) (by simp)
          simp only [Nat.add_sub_cancel] at hst
          rw [hmin_eq]
          exact agreeOn_mono hst hlo_step (by rw [le_min_iff]; omega)
      · have hmin1 : min (t + 1) ell = ell := Nat.min_eq_right (by omega)
        have hmin0 : min t ell = ell := Nat.min_eq_right (by omega)
        rw [hmin1]
        rw [hmin0] at hprev
        have hc_ell : (histFold k r q sched row.val ref ell).2.2 ≤ ell :=
          histFold_cnt_le k r q sched row.val ref ell
        have hst := agree_step_false (r := r) (c := sched) (t := t + 1) (by omega) hw hw' hX1 hX2
          hprev hAgW (by omega) (by simp)
        simp only [Nat.add_sub_cancel] at hst
        exact agreeOn_mono hst hlo_step (by rw [le_min_iff]; omega)
  have hfin := hstep_all r (le_refl _)
  have hlo_r : loU k r r - a = k - a := by unfold loU; split_ifs <;> omega
  have hmin_r : min r ell = ell := Nat.min_eq_right hellr
  have hrec_ell : recCount ell = ell - 1 := by unfold recCount; split_ifs <;> omega
  have hcnt_eq : (histFold k r q sched row.val ref ell).2.2 =
      bitWeight (ell - 1) (histFold k r q sched row.val ref ell).2.1 := by
    rw [← hrec_ell]
    exact (histFold_code_weight k r q sched row.val ref ell).2
  set cw := bitWeight (ell - 1) (histFold k r q sched row.val ref ell).2.1 with hcw
  have hmin_q : min q (histFold k r q sched row.val ref ell).2.2 = cw := by
    rw [hcnt_eq]
    exact Nat.min_eq_right hwt.le
  rw [hlo_r, hmin_r, hmin_q, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hfin
  have hXr1 : stateStep k r sched false w row.val r < 2 ^ k := stateStep_lt row.isLt
  have hXr2 : stateStep k r sched false w' row.val r < 2 ^ k := stateStep_lt row.isLt
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  by_cases hj : j < a - (q - cw)
  · simp only [hj, decide_true, Bool.true_and]
    have hlt : k - a + j < k := by omega
    have hbit := hfin (k - a + j) (by omega) (by omega)
    rwa [bitAt_lt hlt, bitAt_lt hlt] at hbit
  · simp [hj]

lemma spare_bit {x p m spare s : Nat} (h : (x >>> p) % 2 ^ m = spare) (h1 : p ≤ s) (h2 : s < p + m) :
    x.testBit s = spare.testBit (s - p) := by
  have hb := congrArg (fun y => y.testBit (s - p)) h
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight] at hb
  have hlt : s - p < m := by omega
  have he : p + (s - p) = s := by omega
  simp only [hlt, decide_true, Bool.true_and, he] at hb
  exact hb

lemma part2_lo {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row col : Fin (2 ^ k))
    (seedTag : Fin (2 ^ (5 * r - 3 - q))) (c : Nat)
    (hc : c = bitWeight (ell - 1)
      (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) ell).2.1)
    (hwt : c < q) (m : Nat) (hm : m = q - c)
    (spare : Fin (2 ^ m))
    (rowPart : Fin (2 ^ (min ((k + 1) / 2) (k - (5 * r - 3)) - m)))
    (colBits : Fin (2 ^ (q + ((k - (k + 1) / 2) - (5 * r - 3))))) :
    let P := recoverGood k r q m sched row.val col.val seedTag.val spare.val rowPart.val colBits.val
    ∃ w : Fin (2 ^ k),
      w.val = recoverRaw k r q m sched row.val col.val seedTag.val spare.val rowPart.val colBits.val ∧
      P w ∧ ∀ w', P w' → w' = w := by
  have hmp : m ≠ 0 := by omega
  simp only [recoverGood, hmp, ↓reduceIte]
  let h := (k + 1) / 2
  let z := k - h
  let u := 5 * r - 3
  let start := k - (2 * r - 2)
  let a := min h (k - u)
  let g := z - u
  have hsum_ag : a + g = k - u := by
    simp only [a, g, z, h, u]
    omega
  have hma : m ≤ a := by
    simp only [a, h, u]
    omega
  set baseQG := 3 * r - 1 - q
  set baseA := k - a - (2 * r - 2)
  have hmid_eq : baseQG + (q + g) = baseA := by
    simp only [baseQG, baseA]
    omega
  have hm_start : m ≤ start := by
    simp only [start]
    omega
  have hA_end : baseA + a = start := by
    simp only [baseA, start]
    omega
  have hfreeze : ∀ {w w' : Nat}, w < 2 ^ k → w' < 2 ^ k →
      AgreeOn k start (k + 3 * r - 1 - q) w (rot k start seedTag.val) →
      AgreeOn k start (k + 3 * r - 1 - q) w' (rot k start seedTag.val) →
      AgreeOn k baseA start w w' →
      (stateStep k r sched false w row.val r >>> (k - a)) % 2 ^ (a - m) =
        (stateStep k r sched false w' row.val r >>> (k - a)) % 2 ^ (a - m) := by
    intro w w' hw hw' h1 h2 h3
    have hfr := agree_row_freeze_lo hq hqr hk7 hell5 hellr h5 sched row seedTag (hc ▸ hwt)
      hw hw' h1 h2 h3
    rw [← hc, ← hm] at hfr
    exact hfr
  have hrow_tri0 : ∀ j < a, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ s < k, (s < baseA ∨ baseA + j < s) → w.testBit s = w'.testBit s) →
      xor ((stateStep k r sched false w row.val r >>> (k - a)).testBit j)
          ((stateStep k r sched false w' row.val r >>> (k - a)).testBit j) =
        xor (w.testBit (baseA + j)) (w'.testBit (baseA + j)) := by
    intro j hj w w' hw hw' hout
    rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    have hi_lt : k - a + j < k := by omega
    rw [← bitAt_lt hi_lt, ← bitAt_lt hi_lt]
    have hL : leftRow r = 2 * (r - 1) := by unfold leftRow; omega
    have hAg : AgreeOn k (k - a + j - leftRow r + 1) (k - a + j + 3 * r) w w' := by
      intro i hi1 hi2
      by_cases hik : i < k
      · rw [bitAt_lt hik, bitAt_lt hik]
        exact hout i hik (Or.inr (by omega))
      · have hlt_base : i - k < baseA := by omega
        have hsk : i - k < k := by omega
        have hrew : i = (i - k) + k := by omega
        rw [hrew, bitAt_add_k, bitAt_add_k, bitAt_lt hsk, bitAt_lt hsk]
        exact hout (i - k) hsk (Or.inl hlt_base)
    have hpiv := row_pivot (r := r) (c := sched) (row := row.val) (by omega) row.isLt r (by omega)
      w w' (k - a + j) hw hw' (by omega) hAg
    have hidx : k - a + j - leftRow r = baseA + j := by omega
    rw [hidx] at hpiv
    simpa [bitAt_lt hi_lt, bitAt_lt (show baseA + j < k by omega)] using hpiv
  have hrow_tri : ∀ j < a - m, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ s < k, (s < baseA ∨ baseA + j < s) → w.testBit s = w'.testBit s) →
      xor (((stateStep k r sched false w row.val r >>> (k - a)) % 2 ^ (a - m)).testBit j)
          (((stateStep k r sched false w' row.val r >>> (k - a)) % 2 ^ (a - m)).testBit j) =
        xor (w.testBit (baseA + j)) (w'.testBit (baseA + j)) := by
    intro j hj w w' hw hw' hout
    simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and]
    exact hrow_tri0 j (by omega) w w' hw hw' hout
  have hcol_tri : ∀ j < q + g, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ s < k, (s < baseQG ∨ baseQG + j < s) → w.testBit s = w'.testBit s) →
      xor (((stateStep k r sched true w col.val r >>> (6 * r - q)) % 2 ^ (q + g)).testBit j)
          (((stateStep k r sched true w' col.val r >>> (6 * r - q)) % 2 ^ (q + g)).testBit j) =
        xor (w.testBit (baseQG + j)) (w'.testBit (baseQG + j)) := by
    intro j hj w w' hw hw' hout
    simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and, Nat.testBit_shiftRight]
    have h6rg : 6 * r + g ≤ k := by
      simp only [g, z, h, u]
      omega
    have hi_lt : 6 * r - q + j < k := by omega
    rw [← bitAt_lt hi_lt, ← bitAt_lt hi_lt]
    have hwrap : 6 * r - q + j + 4 * r - 2 ≤ k + baseQG := by
      simp only [baseQG, g, z, h, u] at hj ⊢
      omega
    have hAg : AgreeOn k (6 * r - q + j - (3 * r + 1) + 1) (6 * r - q + j + 4 * r - 2) w w' := by
      intro i hi1 hi2
      by_cases hik : i < k
      · rw [bitAt_lt hik, bitAt_lt hik]
        exact hout i hik (Or.inr (by omega))
      · have hlt_base : i - k < baseQG := by omega
        have hsk : i - k < k := by omega
        have hrew : i = (i - k) + k := by omega
        rw [hrew, bitAt_add_k, bitAt_add_k, bitAt_lt hsk, bitAt_lt hsk]
        exact hout (i - k) hsk (Or.inl hlt_base)
    have hpiv := col_pivot (r := r) (c := sched) (col := col.val) (by omega) col.isLt (t := r) (by omega)
      hw hw' (i := 6 * r - q + j) (by omega) hAg
    have hidx : 6 * r - q + j - (3 * r + 1) = baseQG + j := by omega
    rw [hidx] at hpiv
    simpa [bitAt_lt hi_lt, bitAt_lt (show baseQG + j < k by omega)] using hpiv

  let w0 := ofBits k (fun s => if start - m ≤ s ∧ s < start then spare.val.testBit (s - (start - m))
    else (rot k start seedTag.val).testBit s)
  have hw0 : w0 < 2 ^ k := ofBits_lt k _
  have hw0_out : ∀ s < k, (s < baseQG ∨ start ≤ s) →
      w0.testBit s = (rot k start seedTag.val).testBit s := by
    intro s hsk hso
    have hn : ¬ (start - m ≤ s ∧ s < start) := by rcases hso with h1 | h1 <;> omega
    simp only [w0, ofBits_testBit, hsk, hn, ↓reduceIte]
  have hw0_sp : ∀ s, start - m ≤ s → s < start →
      w0.testBit s = spare.val.testBit (s - (start - m)) := by
    intro s h1 h2
    have hsk : s < k := by omega
    simp only [w0, ofBits_testBit, hsk, h1, h2, and_self, ↓reduceIte]
  obtain ⟨hw1, hw1_out, hw1_row⟩ := solveTri_spec (k := k) (base := baseA) (m := a - m) (by omega)
    (fun w => (stateStep k r sched false w row.val r >>> (k - a)) % 2 ^ (a - m))
    (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _))
    hrow_tri w0 hw0 rowPart.val rowPart.isLt
  let w1 : Fin (2 ^ k) := ⟨_, hw1⟩
  obtain ⟨hw2, hw2_out, hw2_col⟩ := solveTri_spec (k := k) (base := baseQG) (m := q + g) (by omega)
    (fun w => (stateStep k r sched true w col.val r >>> (6 * r - q)) % 2 ^ (q + g))
    (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _))
    hcol_tri w1.val w1.isLt colBits.val colBits.isLt
  let w2 : Fin (2 ^ k) := ⟨_, hw2⟩
  have hw1_proj_ag : AgreeOn k start (k + 3 * r - 1 - q) w1.val (rot k start seedTag.val) := by
    rw [project_iff_outside hq hqr hk7 seedTag w1.val]
    intro s hsk hso
    rw [hw1_out s hsk (by rcases hso with h1 | h1 <;> omega)]
    exact hw0_out s hsk hso
  have hw2_eq_w1 : ∀ s < k, (s < baseQG ∨ baseA ≤ s) → w2.val.testBit s = w1.val.testBit s := by
    intro s hsk hso
    exact hw2_out s hsk (by rcases hso with h1 | h1 <;> omega)
  have hw2_proj_ag : AgreeOn k start (k + 3 * r - 1 - q) w2.val (rot k start seedTag.val) := by
    rw [project_iff_outside hq hqr hk7 seedTag w2.val]
    intro s hsk hso
    rw [hw2_eq_w1 s hsk (by rcases hso with h1 | h1 <;> omega)]
    exact (project_iff_outside hq hqr hk7 seedTag w1.val).mp hw1_proj_ag s hsk hso
  have hw2_proj : rot k (k - start % k) w2.val % 2 ^ (u - q) = seedTag.val :=
    (project_iff_agree hq hqr hk7 seedTag w2.val w2.isLt).mpr hw2_proj_ag
  have hw2_sp_bit : ∀ s, start - m ≤ s → s < start →
      w2.val.testBit s = spare.val.testBit (s - (start - m)) := by
    intro s h1 h2
    have hsk : s < k := by omega
    rw [hw2_eq_w1 s hsk (Or.inr (by omega)), hw1_out s hsk (Or.inr (by omega))]
    exact hw0_sp s h1 h2
  have hw2_sp : (w2.val >>> (start - m)) % 2 ^ m = spare.val := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    by_cases hj : j < m
    · simp only [hj, decide_true, Bool.true_and]
      rw [hw2_sp_bit (start - m + j) (by omega) (by omega)]
      congr 1
      omega
    · simp only [hj, decide_false, Bool.false_and]
      exact (Nat.testBit_lt_two_pow
        (lt_of_lt_of_le spare.isLt (Nat.pow_le_pow_right (by omega) (by omega)))).symm
  have hw2_agA : AgreeOn k baseA start w2.val w1.val := by
    intro i hi1 hi2
    have hik : i < k := by omega
    rw [bitAt_lt hik, bitAt_lt hik]
    exact hw2_eq_w1 i hik (Or.inr hi1)
  have hw2_row : (stateStep k r sched false w2.val row.val r >>> (k - a)) % 2 ^ (a - m) =
      rowPart.val := by
    rw [hfreeze w2.isLt w1.isLt hw2_proj_ag hw1_proj_ag hw2_agA]
    exact hw1_row
  refine ⟨w2, ?_, ⟨hw2_proj, ⟨hw2_sp, hw2_row⟩, hw2_col⟩, ?_⟩
  · simp only [w2, w1, w0, recoverRaw, hmp, ↓reduceIte, start, h, z, a, g, baseQG, baseA, u]
  rintro w3 ⟨hw3_proj, ⟨hw3_sp, hw3_row⟩, hw3_col⟩
  have hw3_proj_ag : AgreeOn k start (k + 3 * r - 1 - q) w3.val (rot k start seedTag.val) :=
    (project_iff_agree hq hqr hk7 seedTag w3.val w3.isLt).mp hw3_proj
  have hw3_sp_bit : ∀ s, start - m ≤ s → s < start →
      w3.val.testBit s = spare.val.testBit (s - (start - m)) := by
    intro s h1 h2
    exact spare_bit hw3_sp h1 (by omega)
  let wMix := ofBits k (fun j => if baseA ≤ j ∧ j < start then w3.val.testBit j else w2.val.testBit j)
  have hwMix_lt : wMix < 2 ^ k := ofBits_lt k _
  have hwMix_proj_ag : AgreeOn k start (k + 3 * r - 1 - q) wMix (rot k start seedTag.val) := by
    rw [project_iff_outside hq hqr hk7 seedTag wMix]
    intro s hsk hso
    have hnotA : ¬ (baseA ≤ s ∧ s < start) := by
      rcases hso with hlt | hge <;> omega
    simp only [wMix, ofBits_testBit, hsk, hnotA, ↓reduceIte]
    exact (project_iff_outside hq hqr hk7 seedTag w2.val).mp hw2_proj_ag s hsk hso
  have hwMix_agA : AgreeOn k baseA start wMix w3.val := by
    intro i hi1 hi2
    have hik : i < k := by omega
    simp [bitAt_lt hik, wMix, ofBits_testBit, hik, hi1, hi2]
  have hwMix_row : (stateStep k r sched false wMix row.val r >>> (k - a)) % 2 ^ (a - m) =
      rowPart.val := by
    rw [hfreeze hwMix_lt w3.isLt hwMix_proj_ag hw3_proj_ag hwMix_agA]
    exact hw3_row
  have hwMix_eq_w2 : (⟨wMix, hwMix_lt⟩ : Fin (2 ^ k)) = w2 := by
    have huniqA := triangular_solve (k := k) (base := baseA) (m := a - m) (by omega)
      (fun w => (stateStep k r sched false w row.val r >>> (k - a)) % 2 ^ (a - m))
      (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _))
      hrow_tri w2.val w2.isLt rowPart.val rowPart.isLt
    rcases huniqA with ⟨wU, _, hU⟩
    have h1 : (⟨wMix, hwMix_lt⟩ : Fin (2 ^ k)) = wU := by
      apply hU
      refine ⟨?_, hwMix_row⟩
      intro s hsk hso
      show wMix.testBit s = w2.val.testBit s
      by_cases hin : baseA ≤ s ∧ s < start
      · simp only [wMix, ofBits_testBit, hsk, hin, and_self, ↓reduceIte]
        have hs1 : start - m ≤ s := by rcases hso with h1 | h1 <;> omega
        rw [hw3_sp_bit s hs1 hin.2, hw2_sp_bit s hs1 hin.2]
      · simp only [wMix, ofBits_testBit, hsk, hin, ↓reduceIte]
    have h2 : w2 = wU := hU w2 ⟨fun _ _ _ => rfl, hw2_row⟩
    rw [h1, h2]
  have hw3_eq_w2_A : ∀ s < k, (s < baseQG ∨ baseQG + (q + g) ≤ s) →
      w3.val.testBit s = w2.val.testBit s := by
    intro s hsk hso
    rcases hso with hlt | hge
    · rw [(project_iff_outside hq hqr hk7 seedTag w3.val).mp hw3_proj_ag s hsk (Or.inl hlt),
        (project_iff_outside hq hqr hk7 seedTag w2.val).mp hw2_proj_ag s hsk (Or.inl hlt)]
    · by_cases hst : start ≤ s
      · rw [(project_iff_outside hq hqr hk7 seedTag w3.val).mp hw3_proj_ag s hsk (Or.inr hst),
          (project_iff_outside hq hqr hk7 seedTag w2.val).mp hw2_proj_ag s hsk (Or.inr hst)]
      · have hval : wMix = w2.val := congrArg Fin.val hwMix_eq_w2
        have hbit : wMix.testBit s = w2.val.testBit s := by rw [hval]
        have hin : baseA ≤ s ∧ s < start := ⟨by omega, by omega⟩
        simp only [wMix, ofBits_testBit, hsk, hin, and_self, ↓reduceIte] at hbit
        exact hbit
  have huniqQG := triangular_solve (k := k) (base := baseQG) (m := q + g) (by omega)
    (fun w => (stateStep k r sched true w col.val r >>> (6 * r - q)) % 2 ^ (q + g))
    (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _))
    hcol_tri w2.val w2.isLt colBits.val colBits.isLt
  rcases huniqQG with ⟨wU, _, hU⟩
  have h1 : w3 = wU := hU w3 ⟨hw3_eq_w2_A, hw3_col⟩
  have h2 : w2 = wU := hU w2 ⟨fun _ _ _ => rfl, hw2_col⟩
  rw [h1, h2]

def solveGuard (k r q ell : Nat) (sched : Nat → Fin (2 ^ k)) (row hist tag : Nat) : Nat :=
  solveBits (pivOf r q ell hist)
    (fun s w =>
      (mix k 1 (stateStep k r sched false (rot k (k - (2 * r - 2)) w) row (roundOf s - 1))).testBit
        ((k - q + 3 * (r - roundOf s) + min (q - 1) (targetCount (ell - 1) hist s) + 1) % k))
    (fun s => hist.testBit (ell - 1 - 1 - s)) tag (ell - 1)

lemma solveGuard_spec {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row : Fin (2 ^ k))
    (hist : Fin (2 ^ (ell - 1))) (tag : Fin (2 ^ (5 * r - 3 - q))) :
    let out := solveGuard k r q ell sched row.val hist.val tag.val
    out < 2 ^ (5 * r - 3 - q) ∧
    (∀ j, (∀ s < ell - 1, pivOf r q ell hist.val s ≠ j) → out.testBit j = tag.val.testBit j) ∧
    (histFold k r q sched row.val (rot k (k - (2 * r - 2)) out) ell).2.1 = hist.val := by
  dsimp only [solveGuard]
  obtain ⟨hout, hfree, hfix⟩ := solveBits_spec (k := 5 * r - 3 - q) (base := 0)
    (p := pivOf r q ell hist.val) (m := ell - 1)
    (f := fun s w =>
      (mix k 1 (stateStep k r sched false (rot k (k - (2 * r - 2)) w) row.val (roundOf s - 1))).testBit
        ((k - q + 3 * (r - roundOf s) + min (q - 1) (targetCount (ell - 1) hist.val s) + 1) % k))
    (b := fun s => hist.val.testBit (ell - 1 - 1 - s)) tag.isLt
    (fun t ht => ⟨Nat.zero_le _, pivOf_lt r q ell hist.val t hq hell5 h5 ht⟩)
    (pivOf_strictAnti r q ell hist.val hq hell5 h5)
    (by
      intro t ht w w' hw hw' h
      exact pivOf_bit_pivot (sched := sched) hq hqr hk7 hell5 hellr h5 row.isLt hist.val ht hw hw'
        (fun j h1 h2 => h j h2 (Or.inr h1))) (ell - 1) le_rfl
  let out := solveGuard k r q ell sched row.val hist.val tag.val
  change out < 2 ^ (5 * r - 3 - q) ∧ _ ∧ _
  refine ⟨hout, hfree, ?_⟩
  let ref := rot k (k - (2 * r - 2)) out
  apply (histFold_eq_iff_bits k r q ell sched row.val ref hist.val hell5 hist.isLt).mpr
  have pre : ∀ d ≤ ell - 1, ∀ s < d,
      (mix k 1 (stateStep k r sched false ref row.val (roundOf s - 1))).testBit
        ((k - q + 3 * (r - roundOf s) +
          min (q - 1) (histFold k r q sched row.val ref (roundOf s - 1)).2.2 + 1) % k) =
          hist.val.testBit (ell - 1 - 1 - s) := by
    intro d
    induction d with
    | zero => intro _ s hs; omega
    | succ d ih =>
      intro hd s hs
      by_cases hsd : s = d
      · subst s
        have hc := histFold_cnt_of_prefix k r q ell sched row.val ref hist.val hell5 d
          (by omega) (ih (by omega))
        have hr : roundOf d - 1 = if d < 3 then d else d + 1 := by
          unfold roundOf; split_ifs <;> omega
        rw [← hr] at hc
        rw [hc]
        exact hfix d (by omega)
      · exact ih (by omega) s (by omega)
  exact pre (ell - 1) le_rfl

def isFree (t : Nat) (p : Nat → Nat) (j : Nat) : Bool :=
  (List.range t).all (fun s => p s != j)

lemma isFree_spec (t : Nat) (p : Nat → Nat) (j : Nat) :
    isFree t p j = true ↔ ∀ s < t, p s ≠ j := by
  simp [isFree, List.all_eq_true, bne_iff_ne]

def freeIdx (f : Nat → Bool) (j : Nat) : Nat := ((List.range j).filter f).length

lemma freeIdx_succ (f : Nat → Bool) (j : Nat) :
    freeIdx f (j + 1) = freeIdx f j + (f j).toNat := by
  unfold freeIdx
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : f j <;> simp [h]

lemma freeIdx_mono (f : Nat → Bool) : Monotone (freeIdx f) := by
  apply monotone_nat_of_le_succ
  intro j
  simp [freeIdx_succ]

lemma freeIdx_lt (f : Nat → Bool) {j m : Nat} (hj : j < m) (hf : f j = true) :
    freeIdx f j < freeIdx f m := by
  have hm := freeIdx_mono f (show j + 1 ≤ m by omega)
  simp only [freeIdx_succ, hf, Bool.toNat_true] at hm
  omega

lemma freeIdx_cover (f : Nat → Bool) (m i : Nat) (hi : i < freeIdx f m) :
    ∃ j < m, f j = true ∧ freeIdx f j = i := by
  induction m with
  | zero => simp [freeIdx] at hi
  | succ m ih =>
    by_cases h : i < freeIdx f m
    · obtain ⟨j, hj, hfj, hij⟩ := ih h
      exact ⟨j, by omega, hfj, hij⟩
    · have hs := freeIdx_succ f m
      have hf : f m = true := by
        cases hx : f m
        · simp only [hx, Bool.toNat_false, Nat.add_zero] at hs; omega
        · rfl
      simp only [hf, Bool.toNat_true] at hs
      exact ⟨m, by omega, hf, by omega⟩

lemma freeIdx_card {m t : Nat} (p : Nat → Nat)
    (hpos : ∀ s < t, p s < m) (hanti : ∀ s s', s < s' → s' < t → p s' < p s) :
    freeIdx (isFree t p) m = m - t := by
  classical
  let fp : Fin t → Nat := fun s => p s.val
  have hfpinj : Function.Injective fp := by
    intro x y he
    apply Fin.ext
    change p x.val = p y.val at he
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact (Nat.ne_of_lt (hanti _ _ h y.isLt)) he.symm
    · exact (Nat.ne_of_lt (hanti _ _ h x.isLt)) he
  let blocked : Finset Nat := Finset.univ.image fp
  have hsub : blocked ⊆ Finset.range m := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hpos i.val i.isLt)
  have hcard : blocked.card = t := by
    simp [blocked, Finset.card_image_of_injective _ hfpinj]
  let freeList := (List.range m).filter (isFree t p)
  have hn : freeList.Nodup := (List.nodup_range (n := m)).filter _
  have he : freeList.toFinset = Finset.range m \ blocked := by
    ext j
    simp only [freeList, List.mem_toFinset, List.mem_filter, List.mem_range,
      isFree_spec, Finset.mem_sdiff, Finset.mem_range, blocked, Finset.mem_image,
      Finset.mem_univ, true_and, not_exists, fp]
    constructor
    · rintro ⟨h, hp⟩
      exact ⟨h, fun s => hp s.val s.isLt⟩
    · rintro ⟨h, hp⟩
      exact ⟨h, fun s hs => hp ⟨s, hs⟩⟩
  exact (List.toFinset_card_of_nodup hn).symm.trans (by
    rw [he, Finset.card_sdiff_of_subset hsub, Finset.card_range, hcard])

def packFree (m t : Nat) (p : Nat → Nat) (addr : Nat) : Nat :=
  ofBits m fun j => isFree t p j && addr.testBit (freeIdx (isFree t p) j)

lemma packFree_at {m t : Nat} {p : Nat → Nat} {addr j : Nat} (hj : j < m)
    (hf : isFree t p j = true) :
    (packFree m t p addr).testBit j = addr.testBit (freeIdx (isFree t p) j) := by
  simp [packFree, ofBits_testBit, hf, hj]

lemma freeCode_existsUnique (f : Nat → Bool) (m tag : Nat) :
    ∃! code : Fin (2 ^ freeIdx f m),
      ∀ j < m, f j = true → code.val.testBit (freeIdx f j) = tag.testBit j := by
  classical
  let pick := fun i => if h : i < freeIdx f m then
    tag.testBit (Classical.choose (freeIdx_cover f m i h)) else false
  let code : Fin (2 ^ freeIdx f m) := ⟨ofBits (freeIdx f m) pick, ofBits_lt _ _⟩
  have hbits : ∀ j < m, f j = true → code.val.testBit (freeIdx f j) = tag.testBit j := by
    intro j hj hf
    have hlt := freeIdx_lt f hj hf
    simp only [code, ofBits_testBit, hlt, ↓reduceIte, pick, dite_true]
    obtain ⟨hj', hf', he⟩ := Classical.choose_spec (freeIdx_cover f m (freeIdx f j) hlt)
    congr 1
    rcases lt_trichotomy (Classical.choose (freeIdx_cover f m (freeIdx f j) hlt)) j with h | h | h
    · have hlt' := freeIdx_lt f h hf'
      omega
    · exact h
    · have hlt' := freeIdx_lt f h hf
      omega
  refine ⟨code, hbits, ?_⟩
  intro b hb
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < freeIdx f m
  · obtain ⟨j, hj, hf, he⟩ := freeIdx_cover f m i h
    rw [← he, hb j hj hf, hbits j hj hf]
  · have h1 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : freeIdx f m ≤ i)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt h1),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le code.isLt h1)]

lemma pivotUnique {k m : Nat} {p : Nat → Nat} {f : Nat → Nat → Bool}
    {w w' : Nat} (hw : w < 2 ^ k) (hw' : w' < 2 ^ k)
    (hpos : ∀ t < m, p t < k)
    (hanti : ∀ i j, i < j → j < m → p j < p i)
    (hpiv : ∀ t < m,
      (∀ j < k, p t < j → w.testBit j = w'.testBit j) →
      xor (f t w) (f t w') = xor (w.testBit (p t)) (w'.testBit (p t)))
    (hfree : ∀ j < k, (∀ t < m, p t ≠ j) → w.testBit j = w'.testBit j)
    (hfixed : ∀ t < m, f t w = f t w') : w = w' := by
  have eqPrefix : ∀ d ≤ m, ∀ j < k,
      (∀ s < m, d ≤ s → p s ≠ j) → w.testBit j = w'.testBit j := by
    intro d
    induction d with
    | zero => exact fun _ j hj h => hfree j hj (fun s hs => h s hs (Nat.zero_le _))
    | succ d ih =>
      intro hd j hj hp
      by_cases he : p d = j
      · subst j
        have hb := hpiv d (by omega) (fun i hi hi_gt =>
          ih (by omega) i hi (by
            intro t ht hdt
            by_cases he : d = t
            · subst t; exact Nat.ne_of_lt hi_gt
            · exact Nat.ne_of_lt (lt_trans (hanti d t (by omega) ht) hi_gt)))
        rw [hfixed d (by omega)] at hb
        have aux : ∀ a b c : Bool, xor a a = xor b c → b = c := by decide
        exact aux _ _ _ hb
      · apply ih (by omega) j hj
        intro t ht hdt
        by_cases he' : t = d
        · simpa [he'] using he
        · exact hp t ht (by omega)
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k
  · exact eqPrefix m le_rfl j hj (fun t ht hmt => by omega)
  · have h1 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : k ≤ j)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hw h1),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hw' h1)]

lemma guardUnique {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row : Fin (2 ^ k))
    (hist : Fin (2 ^ (ell - 1))) (tag tag' : Fin (2 ^ (5 * r - 3 - q)))
    (h1 : (histFold k r q sched row.val (rot k (k - (2 * r - 2)) tag.val) ell).2.1 = hist.val)
    (h2 : (histFold k r q sched row.val (rot k (k - (2 * r - 2)) tag'.val) ell).2.1 = hist.val)
    (hfree : ∀ j < 5 * r - 3 - q, isFree (ell - 1) (pivOf r q ell hist.val) j = true →
      tag.val.testBit j = tag'.val.testBit j) :
    tag = tag' := by
  apply Fin.ext
  let f := fun s w =>
    (mix k 1 (stateStep k r sched false (rot k (k - (2 * r - 2)) w) row.val (roundOf s - 1))).testBit
      ((k - q + 3 * (r - roundOf s) + min (q - 1) (targetCount (ell - 1) hist.val s) + 1) % k)
  apply pivotUnique (p := pivOf r q ell hist.val) (f := f) (m := ell - 1) tag.isLt tag'.isLt
    (fun s hs => pivOf_lt r q ell hist.val s hq hell5 h5 hs)
    (pivOf_strictAnti r q ell hist.val hq hell5 h5)
    (fun _ h ha => pivOf_bit_pivot (sched := sched) hq hqr hk7 hell5 hellr h5 row.isLt hist.val h
      tag.isLt tag'.isLt (fun j hlo hhi => ha j hhi hlo))
    (fun j hj hp => hfree j hj ((isFree_spec _ _ _).mpr hp))
  intro s hs
  suffices ∀ (w : Fin (2 ^ (5 * r - 3 - q))),
      (histFold k r q sched row.val (rot k (k - (2 * r - 2)) w.val) ell).2.1 = hist.val →
      f s w.val = hist.val.testBit (ell - 1 - 1 - s) by
    rw [this tag h1, this tag' h2]
  intro w hh
  let ref := rot k (k - (2 * r - 2)) w.val
  have hbits := (histFold_eq_iff_bits k r q ell sched row.val ref hist.val hell5 hist.isLt).mp hh
  have hc := histFold_cnt_of_prefix k r q ell sched row.val ref hist.val hell5 s
    (by omega) (fun j hj => hbits j (by omega))
  have hr : roundOf s - 1 = if s < 3 then s else s + 1 := by
    unfold roundOf; split_ifs <;> omega
  rw [← hr] at hc
  have hb := hbits s hs
  rwa [hc] at hb

def labelOf (k r q raw : Nat) : Nat :=
  rot k (k - ((k - (2 * r - 2)) % k)) raw % 2 ^ (5 * r - 3 - q)

def guardCode (k r q ell : Nat) (sched : Nat → Fin (2 ^ k)) (row tag : Nat) : Nat :=
  (histFold k r q sched row (rot k (k - (2 * r - 2)) tag) ell).2.1

def selectedLabel (k r q ell : Nat) (sched : Nat → Fin (2 ^ k))
    (row hist code : Nat) : Nat :=
  solveGuard k r q ell sched row hist (packFree (5 * r - 3 - q) (ell - 1) (pivOf r q ell hist) code)

def leftPart (k r missed ta : Nat) : Nat :=
  let h := (k + 1) / 2
  let a := min h (k - (5 * r - 3))
  (ta >>> (h - a)) % 2 ^ (a - missed)

def rightPart (k r q tb : Nat) : Nat :=
  let z := k - (k + 1) / 2
  (tb >>> (6 * r - q - z)) % 2 ^ (q + (z - (5 * r - 3)))

def passesKey (k r : Nat) (sched : Nat → Fin (2 ^ k)) (row col ta tb raw : Nat) : Prop :=
  let z := k - (k + 1) / 2
  stateStep k r sched false raw row r >>> z = ta ∧
  stateStep k r sched true raw col r >>> z = tb

def testKey (k r : Nat) (sched : Nat → Fin (2 ^ k)) (row col ta tb raw : Nat) : Bool :=
  let z := k - (k + 1) / 2
  ((stateStep k r sched false raw row r >>> z) == ta) &&
  ((stateStep k r sched true raw col r >>> z) == tb)

lemma testKey_spec (k r : Nat) (sched : Nat → Fin (2 ^ k)) (row col ta tb raw : Nat) :
    testKey k r sched row col ta tb raw = true ↔ passesKey k r sched row col ta tb raw := by
  simp [testKey, passesKey]

def keyTuple (k r q ell : Nat) (sched : Nat → Fin (2 ^ k))
    (row col ta tb hist code spare : Nat) : Bool × Nat :=
  let tag := selectedLabel k r q ell sched row hist code
  let missed := q - bitWeight (ell - 1) hist
  let raw := recoverRaw k r q missed sched row col tag spare (leftPart k r missed ta) (rightPart k r q tb)
  let live := (spare < 2 ^ missed) && testKey k r sched row col ta tb raw
  (live, if live then raw else 0)

lemma label_select {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row : Fin (2 ^ k))
    (hist : Fin (2 ^ (ell - 1))) (code : Nat) :
    let tag := selectedLabel k r q ell sched row.val hist.val code
    tag < 2 ^ (5 * r - 3 - q) ∧ guardCode k r q ell sched row.val tag = hist.val ∧
    ∀ j < 5 * r - 3 - q, isFree (ell - 1) (pivOf r q ell hist.val) j = true →
      tag.testBit j = code.testBit (freeIdx (isFree (ell - 1) (pivOf r q ell hist.val)) j) := by
  let pack := packFree (5 * r - 3 - q) (ell - 1) (pivOf r q ell hist.val) code
  have hpack : pack < 2 ^ (5 * r - 3 - q) := ofBits_lt _ _
  obtain ⟨hw, hfree, he⟩ := solveGuard_spec hq hqr hk7 hell5 hellr h5 sched row hist ⟨pack, hpack⟩
  refine ⟨hw, he, ?_⟩
  intro j hj hf
  exact (hfree j ((isFree_spec _ _ _).mp hf)).trans (packFree_at hj hf)

lemma recovery_passing {k r q missed : Nat} (hkr : 7 * r + q ≤ k)
    (hcol : k - (k + 1) / 2 + q ≤ 6 * r)
    (sched : Nat → Fin (2 ^ k)) (row col : Fin (2 ^ k))
    (ta tb : Fin (2 ^ ((k + 1) / 2))) (key : Fin (2 ^ k))
    (hp : passesKey k r sched row.val col.val ta.val tb.val key.val) :
    recoverGood k r q missed sched row.val col.val (labelOf k r q key.val)
      ((key.val >>> (k - (2 * r - 2) - missed)) % 2 ^ missed)
      (leftPart k r missed ta.val) (rightPart k r q tb.val) key := by
  let h := (k + 1) / 2
  let z := k - h
  let a := min h (k - (5 * r - 3))
  have hl : k - a = z + (h - a) := by
    dsimp [z, h, a]
    omega
  have hc : 6 * r - q = z + (6 * r - q - z) := by
    dsimp [z, h]
    omega
  have hrowEq : (stateStep k r sched false key.val row.val r >>> (k - a)) =
      (ta.val >>> (h - a)) := by
    rw [hl, Nat.shiftRight_add, hp.1]
  have hcolEq : (stateStep k r sched true key.val col.val r >>> (6 * r - q)) =
      (tb.val >>> (6 * r - q - z)) := by
    nth_rw 1 [hc]
    rw [Nat.shiftRight_add, hp.2]
  refine ⟨rfl, ?_, ?_⟩
  · change (if missed = 0 then _ else _)
    by_cases he : missed = 0
    · subst missed
      simp only [↓reduceIte, leftPart, Nat.sub_zero]
      rw [← hrowEq, Nat.mod_eq_of_lt
        (shiftRight_lt_two_pow (stateStep_lt row.isLt) (by dsimp [a, h]; omega))]
    · simp only [he, ↓reduceIte, leftPart, true_and]
      rw [hrowEq]
  · change (_ >>> (6 * r - q)) % _ = _
    rw [hcolEq]
    rfl

lemma recovery_address {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row col : Fin (2 ^ k)) (ta tb : Fin (2 ^ ((k + 1) / 2)))
    (hist : Fin (2 ^ (ell - 1))) (code spare : Nat)
    (hspare : spare < 2 ^ (q - bitWeight (ell - 1) hist.val)) :
    let tag := selectedLabel k r q ell sched row.val hist.val code
    let missed := q - bitWeight (ell - 1) hist.val
    let a := leftPart k r missed ta.val
    let b := rightPart k r q tb.val
    let P := recoverGood k r q missed sched row.val col.val tag spare a b
    ∃ w : Fin (2 ^ k),
      w.val = recoverRaw k r q missed sched row.val col.val tag spare a b ∧
      P w ∧ ∀ w', P w' → w' = w := by
  have htag := label_select hq hqr hk7 hell5 hellr h5 sched row hist code
  let tv := selectedLabel k r q ell sched row.val hist.val code
  let tag : Fin (2 ^ (5 * r - 3 - q)) := ⟨tv, htag.1⟩
  let count := bitWeight (ell - 1) hist.val
  let m := q - count
  have he : count = bitWeight (ell - 1) (guardCode k r q ell sched row.val tag.val) :=
    congrArg (bitWeight (ell - 1)) htag.2.1.symm
  let RowBits : Fin (2 ^ (min ((k + 1) / 2) (k - (5 * r - 3)) - m)) :=
    ⟨leftPart k r m ta.val, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  let ColBits : Fin (2 ^ (q + ((k - (k + 1) / 2) - (5 * r - 3)))) :=
    ⟨rightPart k r q tb.val, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  by_cases hm : m = 0
  · have hwt : q ≤ count := by omega
    have hzero : spare = 0 := by rw [show q - bitWeight (ell - 1) hist.val = m from rfl, hm] at hspare; simpa using hspare
    have hrow : leftPart k r 0 ta.val < 2 ^ min ((k + 1) / 2) (k - (5 * r - 3)) :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    simp only [show q - bitWeight (ell - 1) hist.val = 0 from hm, hzero]
    exact part2_unique hq hqr hk7 hell5 hellr h5 sched row col tag ⟨_, hrow⟩ ColBits (he ▸ hwt)
  · have hlt : count < q := by omega
    exact part2_lo hq hqr hk7 hell5 hellr h5 sched row col tag count he hlt m rfl ⟨spare, hspare⟩
      RowBits ColBits

lemma livePair_true (b : Bool) (v raw : Nat) :
    (b, if b then v else 0) = (true, raw) ↔ b = true ∧ v = raw := by
  cases b <;> simp

lemma keyTuple_hit_iff (k r q ell : Nat) (sched : Nat → Fin (2 ^ k))
    (row col ta tb hist code spare raw : Nat) :
    let tag := selectedLabel k r q ell sched row hist code
    let missed := q - bitWeight (ell - 1) hist
    keyTuple k r q ell sched row col ta tb hist code spare = (true, raw) ↔
      spare < 2 ^ missed ∧ passesKey k r sched row col ta tb raw ∧
        recoverRaw k r q missed sched row col tag spare
          (leftPart k r missed ta) (rightPart k r q tb) = raw := by
  simp only [keyTuple, livePair_true, Bool.and_eq_true, decide_eq_true_eq, testKey_spec]
  constructor
  · rintro ⟨⟨hs, hp⟩, he⟩
    exact ⟨hs, he ▸ hp, he⟩
  · rintro ⟨hs, hp, he⟩
    exact ⟨⟨hs, he.symm ▸ hp⟩, he⟩

lemma keyTuple_inactive (k r q ell : Nat) (sched : Nat → Fin (2 ^ k))
    (row col ta tb hist code spare : Nat)
    (h : (keyTuple k r q ell sched row col ta tb hist code spare).1 = false) :
    (keyTuple k r q ell sched row col ta tb hist code spare).2 = 0 := by
  unfold keyTuple at h ⊢
  dsimp only at h ⊢
  simp [h]

lemma tuple_hit {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hc : k - (k + 1) / 2 + q ≤ 6 * r) (hell5 : 5 ≤ ell) (hellr : ell ≤ r)
    (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row col : Fin (2 ^ k)) (ta tb : Fin (2 ^ ((k + 1) / 2)))
    (key : Fin (2 ^ k)) (hpass : passesKey k r sched row.val col.val ta.val tb.val key.val)
    (hist : Fin (2 ^ (ell - 1))) (code spare : Nat) :
    let label := labelOf k r q key.val
    let mask := isFree (ell - 1) (pivOf r q ell hist.val)
    let missed := q - bitWeight (ell - 1) hist.val
    keyTuple k r q ell sched row.val col.val ta.val tb.val hist.val code spare = (true, key.val) ↔
      guardCode k r q ell sched row.val label = hist.val ∧
      (∀ j < 5 * r - 3 - q, mask j = true → code.testBit (freeIdx mask j) = label.testBit j) ∧
      spare = (key.val >>> (k - (2 * r - 2) - missed)) % 2 ^ missed := by
  let label := labelOf k r q key.val
  let mask := isFree (ell - 1) (pivOf r q ell hist.val)
  let missed := q - bitWeight (ell - 1) hist.val
  let tail := (key.val >>> (k - (2 * r - 2) - missed)) % 2 ^ missed
  let tag := selectedLabel k r q ell sched row.val hist.val code
  let left := leftPart k r missed ta.val
  let right := rightPart k r q tb.val
  let raw := recoverRaw k r q missed sched row.val col.val tag spare left right
  change keyTuple k r q ell sched row.val col.val ta.val tb.val hist.val code spare = (true, key.val) ↔
    guardCode k r q ell sched row.val label = hist.val ∧
      (∀ j < 5 * r - 3 - q, mask j = true → code.testBit (freeIdx mask j) = label.testBit j) ∧ spare = tail
  have hhit := keyTuple_hit_iff k r q ell sched row.val col.val ta.val tb.val hist.val code spare key.val
  dsimp only at hhit
  rw [hhit]
  have labelSpec := label_select hq hqr hk7 hell5 hellr h5 sched row hist code
  change tag < 2 ^ (5 * r - 3 - q) ∧ guardCode k r q ell sched row.val tag = hist.val ∧
    (∀ j < 5 * r - 3 - q, mask j = true → tag.testBit j = code.testBit (freeIdx mask j)) at labelSpec
  constructor
  · rintro ⟨hspare, _, hkey⟩
    obtain ⟨w, hw, hgood, _⟩ := recovery_address hq hqr hk7 hell5 hellr h5 sched row col ta tb hist code spare hspare
    have hwkey : w = key := Fin.ext (hw.trans hkey)
    subst w
    have htag : label = tag := hgood.1
    refine ⟨?_, ?_, ?_⟩
    · rw [htag]
      exact labelSpec.2.1
    · intro j hj hm
      rw [htag]
      exact (labelSpec.2.2 j hj hm).symm
    · by_cases hz : missed = 0
      · have hsp : spare = 0 := by
          change spare < 2 ^ missed at hspare
          rw [hz] at hspare
          simpa using hspare
        simp only [tail, hz, hsp, Nat.pow_zero, Nat.mod_one]
      · have ht := hgood.2.1
        change (if missed = 0 then _ else _) at ht
        rw [if_neg hz] at ht
        exact ht.1.symm
  · rintro ⟨hhist, hcode, htail⟩
    have hlt : label < 2 ^ (5 * r - 3 - q) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have eqtag : tag = label := by
      let t : Fin (2 ^ (5 * r - 3 - q)) := ⟨tag, labelSpec.1⟩
      let l : Fin (2 ^ (5 * r - 3 - q)) := ⟨label, hlt⟩
      have he := guardUnique hq hqr hk7 hell5 hellr h5 sched row hist t l labelSpec.2.1 hhist
        (fun j hj hm => (labelSpec.2.2 j hj hm).trans (hcode j hj hm))
      exact congrArg Fin.val he
    have htlt : tail < 2 ^ missed := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hspare : spare < 2 ^ missed := htail.symm ▸ htlt
    obtain ⟨w, hw, _, huniq⟩ := recovery_address hq hqr hk7 hell5 hellr h5 sched row col ta tb hist code spare hspare
    have hgood := recovery_passing (missed := missed) hk7 hc sched row col ta tb key hpass
    have hprev : recoverGood k r q missed sched row.val col.val tag spare left right key := by
      rw [eqtag, htail]
      exact hgood
    have hk : key = w := huniq key hprev
    exact ⟨hspare, hpass, hw.symm.trans (congrArg Fin.val hk).symm⟩

def usedSlots (r q ell S : Nat) : Nat := 2 ^ (5 * r - 3 - q - (ell - 1)) * S

def decodeKey (k r q ell S : Nat) (unrank : Nat → Nat × Nat) (sched : Nat → Fin (2 ^ k))
    (row col ta tb addr : Nat) : Bool × Nat :=
  if addr < usedSlots r q ell S then
    let d := 5 * r - 3 - q - (ell - 1)
    let hr := unrank (addr >>> d)
    keyTuple k r q ell sched row col ta tb hr.1 (addr % 2 ^ d) hr.2
  else (false, 0)

lemma decodeKey_live (k r q ell S : Nat) (unrank : Nat → Nat × Nat) (sched : Nat → Fin (2 ^ k))
    (row col ta tb addr : Nat)
    (h : (decodeKey k r q ell S unrank sched row col ta tb addr).1 = true) :
    addr < usedSlots r q ell S ∧
    passesKey k r sched row col ta tb (decodeKey k r q ell S unrank sched row col ta tb addr).2 := by
  by_cases ha : addr < usedSlots r q ell S
  · refine ⟨ha, ?_⟩
    simp only [decodeKey, ha, ↓reduceIte] at h ⊢
    let d := 5 * r - 3 - q - (ell - 1)
    let p := unrank (addr >>> d)
    let out := keyTuple k r q ell sched row col ta tb p.1 (addr % 2 ^ d) p.2
    have he : out = (true, out.2) := Prod.ext h rfl
    exact ((keyTuple_hit_iff k r q ell sched row col ta tb p.1 (addr % 2 ^ d) p.2 out.2).mp he).2.1
  · simp [decodeKey, ha] at h

lemma decodeKey_dead (k r q ell S : Nat) (unrank : Nat → Nat × Nat) (sched : Nat → Fin (2 ^ k))
    (row col ta tb addr : Nat)
    (h : (decodeKey k r q ell S unrank sched row col ta tb addr).1 = false) :
    (decodeKey k r q ell S unrank sched row col ta tb addr).2 = 0 := by
  by_cases ha : addr < usedSlots r q ell S
  · simp only [decodeKey, ha, ↓reduceIte] at h ⊢
    exact keyTuple_inactive k r q ell sched row col ta tb _ _ _ h
  · simp [decodeKey, ha]

lemma decodeKey_unique {k r q ell S : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hc : k - (k + 1) / 2 + q ≤ 6 * r) (hell5 : 5 ≤ ell) (hellr : ell ≤ r)
    (h5 : 5 * ell + q ≤ 5 * r + 2)
    (unrank : Nat → Nat × Nat)
    (hrange : ∀ j < S, (unrank j).1 < 2 ^ (ell - 1))
    (huniq : ∀ (hist spare : Nat), hist < 2 ^ (ell - 1) →
      spare < (if bitWeight (ell - 1) hist < q then 2 ^ q else 1) →
      ∃! j : Fin S, unrank j.val = (hist, spare))
    (sched : Nat → Fin (2 ^ k)) (row col : Fin (2 ^ k)) (ta tb : Fin (2 ^ ((k + 1) / 2)))
    (key : Fin (2 ^ k)) (hp : passesKey k r sched row.val col.val ta.val tb.val key.val) :
    ∃! addr : Fin (2 ^ Nat.clog 2 (usedSlots r q ell S)),
      decodeKey k r q ell S unrank sched row.val col.val ta.val tb.val addr.val = (true, key.val) := by
  let m := 5 * r - 3 - q
  let t := ell - 1
  let d := m - t
  let cap := 2 ^ d
  let label := labelOf k r q key.val
  let history := guardCode k r q ell sched row.val label
  have hh : history < 2 ^ t := by
    have hb := (histFold_code_weight k r q sched row.val
      (rot k (k - (2 * r - 2)) label) ell).1
    have he : recCount ell = t := by simp only [recCount, t]; split_ifs <;> omega
    change (histFold k r q sched row.val (rot k (k - (2 * r - 2)) label) ell).2.1 < 2 ^ t
    exact he ▸ hb
  let hist : Fin (2 ^ t) := ⟨history, hh⟩
  let mask := isFree t (pivOf r q ell history)
  have hm : freeIdx mask m = d := freeIdx_card _
    (fun s hs => pivOf_lt r q ell history s hq hell5 h5 hs)
    (pivOf_strictAnti r q ell history hq hell5 h5)
  have hcode := freeCode_existsUnique mask m label
  rw [hm] at hcode
  obtain ⟨lo, hlo, huniqueLo⟩ := hcode
  let miss := q - bitWeight t history
  let tail := (key.val >>> (k - (2 * r - 2) - miss)) % 2 ^ miss
  have htail : tail < (if bitWeight t history < q then 2 ^ q else 1) := by
    have hlt : tail < 2 ^ miss := Nat.mod_lt _ (Nat.two_pow_pos _)
    split_ifs with h
    · exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
    · have he : miss = 0 := Nat.sub_eq_zero_of_le (by omega)
      simpa [he] using hlt
  obtain ⟨hi, hhi, huniqueHi⟩ := huniq history tail hh htail
  let val := cap * hi.val + lo.val
  have hcap : 0 < cap := Nat.two_pow_pos _
  have hval : val < usedSlots r q ell S := calc
    val < cap * hi.val + cap := Nat.add_lt_add_left lo.isLt _
    _ = cap * (hi.val + 1) := by rw [Nat.mul_succ]
    _ ≤ usedSlots r q ell S := Nat.mul_le_mul_left cap (Nat.succ_le_of_lt hi.isLt)
  have hvalWidth : val < 2 ^ Nat.clog 2 (usedSlots r q ell S) :=
    lt_of_lt_of_le hval (Nat.le_pow_clog (by decide) _)
  have hvallo : val % cap = lo.val := by
    dsimp only [val]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt lo.isLt]
  have hvalhi : val >>> d = hi.val := by
    rw [Nat.shiftRight_eq_div_pow]
    change (cap * hi.val + lo.val) / cap = hi.val
    rw [Nat.mul_add_div hcap, Nat.div_eq_of_lt lo.isLt, Nat.add_zero]
  have hcase : keyTuple k r q ell sched row.val col.val ta.val tb.val history lo.val tail = (true, key.val) :=
    (tuple_hit hq hqr hk7 hc hell5 hellr h5 sched row col ta tb key hp hist lo.val tail).mpr ⟨rfl, hlo, rfl⟩
  refine ⟨⟨val, hvalWidth⟩, ?_, ?_⟩
  · simp only [decodeKey, hval, ↓reduceIte]
    change keyTuple k r q ell sched row.val col.val ta.val tb.val (unrank (val >>> d)).1
      (val % cap) (unrank (val >>> d)).2 = (true, key.val)
    rwa [hvalhi, hvallo, hhi]
  · intro addr ha
    have haLive := congrArg Prod.fst ha
    have has := (decodeKey_live k r q ell S unrank sched row.val col.val ta.val tb.val addr.val haLive).1
    have hah : addr.val >>> d < S := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul hcap, Nat.mul_comm]
      exact has
    let ah : Fin S := ⟨addr.val >>> d, hah⟩
    let al : Fin cap := ⟨addr.val % cap, Nat.mod_lt _ hcap⟩
    let other := unrank ah.val
    have hhh : other.1 < 2 ^ t := hrange ah.val ah.isLt
    let ohist : Fin (2 ^ t) := ⟨other.1, hhh⟩
    simp only [decodeKey, has, ↓reduceIte] at ha
    change keyTuple k r q ell sched row.val col.val ta.val tb.val ohist.val al.val other.2 = (true, key.val) at ha
    have haSpec := (tuple_hit hq hqr hk7 hc hell5 hellr h5 sched row col ta tb key hp ohist al.val other.2).mp ha
    have hhist : ohist = hist := Fin.ext haSpec.1.symm
    rw [hhist] at haSpec
    have haHi : ah = hi := huniqueHi ah (Prod.ext (congrArg Fin.val hhist) haSpec.2.2)
    have haLo : al = lo := huniqueLo al haSpec.2.1
    apply Fin.ext
    have hd := Nat.div_add_mod addr.val cap
    rw [← Nat.shiftRight_eq_div_pow addr.val d] at hd
    change cap * ah.val + al.val = addr.val at hd
    rw [haHi, haLo] at hd
    exact hd.symm


open PEqualNP.Outside.L_meta_29730_aux.Compiler.Build

variable {n : Nat}

def wireBits (w : Nat) (v : (Fin n → Bool) → Nat) : Word n w :=
  fun i x => (v x).testBit i.val

def wireAt (k : Nat) (v : (Fin n → Bool) → Nat) (j : Nat) : Sig n :=
  fun x => bitAt k (v x) j

lemma wireAt_mem {k : Nat} (hk : 0 < k) {v : (Fin n → Bool) → Nat} {A : Set (Sig n)}
    (hv : Available A (wireBits k v)) (j : Nat) : wireAt k v j ∈ A :=
  hv ⟨j % k, Nat.mod_lt _ hk⟩

lemma wireBits_mem {k : Nat} {v : (Fin n → Bool) → Nat} {A : Set (Sig n)}
    (hv : Available A (wireBits k v)) {j : Nat} (hj : j < k) : (fun x => (v x).testBit j) ∈ A :=
  hv ⟨j, hj⟩

lemma madeBits {k : Nat} {v : (Fin n → Bool) → Nat} {A : Set (Sig n)} :
    Available (A ∪ Set.range (wireBits k v)) (wireBits k v) :=
  fun i => Or.inr ⟨i, rfl⟩

lemma avail_mono {k : Nat} {v : Word n k} {A B : Set (Sig n)}
    (ha : Available A v) (hab : A ⊆ B) : Available B v :=
  fun i => hab (ha i)

lemma rotWire {k : Nat} (hk : 0 < k) (offset : Nat) {v : (Fin n → Bool) → Nat}
    {A : Set (Sig n)} (hb : ∀ x, v x < 2 ^ k) (hv : Available A (wireBits k v)) :
    Available A (wireBits k (fun x => rot k offset (v x))) := by
  intro i
  let j := k + i.val - offset % k
  have hle : offset % k ≤ k + i.val := by have := Nat.mod_lt offset hk; omega
  have heq : wireBits k (fun x => rot k offset (v x)) i = wireAt k v j := by
    funext x
    change (rot k offset (v x)).testBit i.val = bitAt k (v x) j
    have he : rot k (offset % k) (v x) = rot k offset (v x) := by simp [rot]
    calc
      _ = bitAt k (rot k offset (v x)) i.val := (bitAt_lt i.isLt).symm
      _ = bitAt k (rot k (offset % k) (v x)) (k + i.val) := by
        rw [he, Nat.add_comm k i.val, bitAt_add_k]
      _ = bitAt k (v x) j := bitAt_rot_sub hk (hb x) hle
  rw [heq]
  exact wireAt_mem hk hv j

lemma xorWords {k : Nat} {v u : (Fin n → Bool) → Nat} {A : Set (Sig n)}
    (hv : Available A (wireBits k v)) (hu : Available A (wireBits k u)) :
    Build A (Set.range (wireBits k (fun x => v x ^^^ u x))) (k * 4) := by
  have he : wireBits k (fun x => v x ^^^ u x) =
      (fun i : Fin k => xo (wireBits k v i) (wireBits k u i)) := by
    funext i x
    simp only [wireBits, xo, Nat.testBit_xor]
  rw [he]
  exact wordXorG (w := k) hv hu

lemma mixWords {k : Nat} (hk : 0 < k) (gap : Nat) {v : (Fin n → Bool) → Nat}
    {A : Set (Sig n)} (hb : ∀ x, v x < 2 ^ k) (hv : Available A (wireBits k v)) :
    Build A (Set.range (wireBits k (fun x => mix k gap (v x)))) (k * 8) := by
  apply finG _ 8
  intro i
  have he : wireBits k (fun x => mix k gap (v x)) i =
      xo (xo (wireBits k v i) (wireBits k (fun x => rot k gap (v x)) i))
        (wireBits k (fun x => rot k (k - gap) (v x)) i) := by
    funext x
    simp only [wireBits, mix, xo, Nat.testBit_xor]
  rw [he]
  exact mixG (hv i) (rotWire hk gap hb hv i) (rotWire hk (k - gap) hb hv i)

lemma chiWords {k : Nat} (hk : 0 < k) {v : (Fin n → Bool) → Nat}
    {A : Set (Sig n)} (hv : Available A (wireBits k v)) :
    Build A (Set.range (wireBits k (fun x => chi k (v x)))) (k * 6) := by
  apply finG _ 6
  intro i
  have he : wireBits k (fun x => chi k (v x)) i =
      xo (wireAt k v i.val) (an (nt (wireAt k v (i.val + 1))) (wireAt k v (i.val + 2))) := by
    funext x
    change (chi k (v x)).testBit i.val = _
    rw [← bitAt_lt (x := chi k (v x)) i.isLt]
    exact bitAt_chi hk
  rw [he]
  exact nonlinG (wireAt_mem hk hv i.val) (wireAt_mem hk hv (i.val + 1))
    (wireAt_mem hk hv (i.val + 2))

lemma cipherStepWords {k r : Nat} (hk : 0 < k) (side : Bool) (t : Nat)
    {sched : (Fin n → Bool) → Nat → Fin (2 ^ k)} {raw prev : (Fin n → Bool) → Nat}
    {A : Set (Sig n)} (hrb : ∀ x, raw x < 2 ^ k) (hpb : ∀ x, prev x < 2 ^ k)
    (hr : Available A (wireBits k raw)) (hp : Available A (wireBits k prev))
    (hc : Available A (wireBits k (fun x => (sched x (if side then r + t else t)).val))) :
    Build A (Set.range (wireBits k (fun x => step k r (sched x) side (raw x) (prev x) t))) (k * 22) := by
  let mixPrev := fun x => mix k (if side then 2 else 1) (prev x)
  let chiPrev := fun x => chi k (mixPrev x)
  let rotRaw := fun x => rot k (if side then 3 * t + 1 else 2 * (t - 1)) (raw x)
  let c := fun x => (sched x (if side then r + t else t)).val
  have hm : Build A (Set.range (wireBits k mixPrev)) (k * 8) := mixWords hk _ hpb hp
  have hn : Build A (Set.range (wireBits k chiPrev)) (k * 8 + k * 6) :=
    thenG hm (chiWords hk madeBits)
  let D := A ∪ Set.range (wireBits k chiPrev)
  have hrot : Available D (wireBits k rotRaw) := avail_mono (rotWire hk _ hrb hr) Set.subset_union_left
  have hc' : Available D (wireBits k c) := avail_mono hc Set.subset_union_left
  have hrest : Build D (Set.range (wireBits k (fun x => step k r (sched x) side (raw x) (prev x) t))) (k * 8) := by
    apply finG _ 8
    intro i
    have he : wireBits k (fun x => step k r (sched x) side (raw x) (prev x) t) i =
        xo (xo (wireBits k chiPrev i) (wireBits k rotRaw i)) (wireBits k c i) := by
      funext x
      simp only [step, wireBits, xo, Nat.testBit_xor, chiPrev, mixPrev, rotRaw, c]
    rw [he]
    exact mixG (madeBits (A := A) (k := k) (v := chiPrev) i) (hrot i) (hc' i)
  exact relax (thenG hn hrest) le_rfl le_rfl (by omega)

lemma cipherStateWords {k r t : Nat} (hk : 0 < k) (side : Bool)
    {sched : (Fin n → Bool) → Nat → Fin (2 ^ k)} {raw name : (Fin n → Bool) → Nat}
    {A : Set (Sig n)} (hrb : ∀ x, raw x < 2 ^ k) (hnb : ∀ x, name x < 2 ^ k)
    (hr : Available A (wireBits k raw)) (hn : Available A (wireBits k name))
    (hc : ∀ j < t, Available A (wireBits k (fun x => (sched x (if side then r + (j + 1) else j + 1)).val))) :
    Build A (Set.range (wireBits k (fun x => stateStep k r (sched x) side (raw x) (name x) t)))
      (k * 4 + t * (k * 22)) := by
  apply loopG (fun j => Set.range (wireBits k (fun x => stateStep k r (sched x) side (raw x) (name x) j)))
  · simp only [stateStep_zero]
    exact xorWords (rotWire hk _ hrb hr) hn
  · intro j hj
    simp only [stateStep_succ]
    exact cipherStepWords hk side (j + 1) hrb (fun x => stateStep_lt (hnb x))
      (avail_mono hr Set.subset_union_left) madeBits (avail_mono (hc j hj) Set.subset_union_left)

lemma constWire {k : Nat} {A : Set (Sig n)} (w : Nat)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    Available A (wireBits k (fun _ => w)) := by
  intro i
  change (fun (_ : Fin n → Bool) => w.testBit i.val) ∈ A
  cases h : w.testBit i.val
  · simpa only [h] using hfalse
  · simpa only [h] using htrue

lemma bitRange {k : Nat} {v : (Fin n → Bool) → Nat} {A : Set (Sig n)}
    (hv : Available A (wireBits k v)) (hz : (fun _ => false) ∈ A) (a w : Nat) :
    Available A (wireBits w (fun x => ((ofBits k (fun j => (v x).testBit j)) >>> a))) := by
  intro i
  change (fun x => (ofBits k (fun j => (v x).testBit j) >>> a).testBit i.val) ∈ A
  simp only [Nat.testBit_shiftRight, ofBits_testBit]
  by_cases h : a + i.val < k
  · simp only [h, ↓reduceIte]
    exact wireBits_mem hv h
  · simpa only [h, ↓reduceIte] using hz

lemma ofBits_id {k v : Nat} (hv : v < 2 ^ k) : ofBits k v.testBit = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [ofBits_testBit]
  by_cases h : i < k
  · simp [h]
  · have hv' : v < 2 ^ i := lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega))
    simp [h, Nat.testBit_lt_two_pow hv']

lemma wordRange {k : Nat} {v : (Fin n → Bool) → Nat} {A : Set (Sig n)}
    (hv : Available A (wireBits k v)) (hb : ∀ x, v x < 2 ^ k) (hz : (fun _ => false) ∈ A) (a w : Nat) :
    Available A (wireBits w (fun x => v x >>> a)) := by
  simpa only [ofBits_id (hb _)] using bitRange hv hz a w

lemma cipherMatchG {k r : Nat} (hk : 0 < k) (side : Bool) (h z : Nat)
    {sched : (Fin n → Bool) → Nat → Fin (2 ^ k)} {raw name target : (Fin n → Bool) → Nat}
    {A : Set (Sig n)} (hrb : ∀ x, raw x < 2 ^ k) (hnb : ∀ x, name x < 2 ^ k)
    (hr : Available A (wireBits k raw)) (hn : Available A (wireBits k name))
    (hc : ∀ j < r, Available A (wireBits k (fun x => (sched x (if side then r + (j + 1) else j + 1)).val)))
    (ht : Available A (wireBits h target)) (htb : ∀ x, target x < 2 ^ h)
    (hh : z + h = k) (hz : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A {fun x => (stateStep k r (sched x) side (raw x) (name x) r >>> z) == target x}
      (k * 4 + r * (k * 22) + (h * 5 + h)) := by
  let f := fun x => stateStep k r (sched x) side (raw x) (name x) r
  have hstate : Build A (Set.range (wireBits k f)) (k * 4 + r * (k * 22)) :=
    cipherStateWords hk side hrb hnb hr hn hc
  let D := A ∪ Set.range (wireBits k f)
  have hf : Available D (wireBits h (fun x => f x >>> z)) :=
    wordRange madeBits (fun x => stateStep_lt (hnb x)) (Or.inl hz) z h
  have ht' : Available D (wireBits h target) := avail_mono ht Set.subset_union_left
  have heq : wordEq (wireBits h (fun x => f x >>> z)) (wireBits h target) =
      (fun x => (f x >>> z) == target x) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [wordEq_eq_true, beq_iff_eq]
    constructor
    · intro he
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < h
      · exact he ⟨i, hi⟩
      · have hi' : h ≤ i := by omega
        have hfa : f x >>> z < 2 ^ h := by
          rw [show z = k - h by omega]
          exact shiftRight_lt_two_pow (stateStep_lt (hnb x)) (by omega)
        have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hi'
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hfa hp),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (htb x) hp)]
    · intro he i
      exact congrArg (fun w : Nat => w.testBit i.val) he
  have H := wordEqG hf ht' (Or.inl htrue)
  rw [heq] at H
  exact thenG hstate H

def equalsIndex (v : (Fin n → Bool) → Nat) (j : Nat) : Sig n :=
  fun x => decide (v x = j)

def unaryWord (w : Nat) (v : (Fin n → Bool) → Nat) : Word n w :=
  fun i => equalsIndex v i.val

lemma unary_const {w : Nat} {A : Set (Sig n)} (c : Nat)
    (hz : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    Available A (unaryWord w (fun _ => c)) := by
  intro i
  change (fun _ : Fin n → Bool => decide (c = i.val)) ∈ A
  by_cases h : c = i.val
  · simpa only [h, decide_true] using ht
  · simpa only [h, decide_false] using hz

lemma unary_inc {w : Nat} {A : Set (Sig n)} {v : (Fin n → Bool) → Nat} {b : Sig n}
    (hv : Available A (unaryWord w v)) (hb : b ∈ A) (hz : (fun _ => false) ∈ A) :
    Build A (Set.range (unaryWord w (fun x => v x + (b x).toNat))) (w * 4) := by
  apply finG _ 4
  intro i
  let lo : Sig n := if h : 0 < i.val then unaryWord w v ⟨i.val - 1, by omega⟩ else fun _ => false
  have hl : lo ∈ A := by
    by_cases h : 0 < i.val
    · simpa only [lo, h, dite_true] using hv ⟨i.val - 1, by omega⟩
    · simpa only [lo, h, dite_false] using hz
  have he : unaryWord w (fun x => v x + (b x).toNat) i = mx b (unaryWord w v i) lo := by
    funext x
    cases hb' : b x
    · simp [mx, unaryWord, equalsIndex, hb']
    · by_cases hi : 0 < i.val
      · have hf : v x + 1 = i.val ↔ v x = i.val - 1 := by omega
        simp [mx, unaryWord, equalsIndex, hb', lo, hi, hf]
      · have hf : v x + 1 ≠ i.val := by omega
        simp [mx, unaryWord, equalsIndex, hb', lo, hi, hf]
  rw [he]
  exact muxG hb (hv i) hl

lemma unaryLookupG {w t : Nat} {A : Set (Sig n)} {v : (Fin n → Bool) → Nat}
    {f : Nat → Word n w} (hv : Available A (unaryWord t v)) (hlim : ∀ x, v x < t)
    (hf : ∀ j < t, Available A (f j)) (hz : (fun _ => false) ∈ A) :
    Build A (Set.range (fun (i : Fin w) x => f (v x) i x)) (w * (t * 4)) := by
  have he : (fun (i : Fin w) => scanMux (equalsIndex v) (fun j => f j i) (fun _ => false) t) =
      (fun (i : Fin w) x => f (v x) i x) := by
    funext i x
    rw [scanMux_index (j := v x) (fun _ _ => rfl), if_pos (hlim x)]
  rw [← he]
  exact scanWordG (w := w) (s := equalsIndex v) (t := t) (v := f) (fallback := fun _ _ => false)
    (fun j hj => hv ⟨j, hj⟩) hf (fun _ => hz)

lemma unarySelectG {t : Nat} {A : Set (Sig n)} {v : (Fin n → Bool) → Nat}
    {f : Nat → Sig n} (hv : Available A (unaryWord t v)) (hlim : ∀ x, v x < t)
    (hf : ∀ j < t, f j ∈ A) (hz : (fun _ => false) ∈ A) :
    Build A {fun x => f (v x) x} (t * 4) := by
  have HG := scanMuxG (s := equalsIndex v) (t := t) (v := f) (fallback := fun _ => false)
    (fun j hj => hv ⟨j, hj⟩) hf hz
  have he : scanMux (equalsIndex v) f (fun _ => false) t = (fun x => f (v x) x) := by
    funext x
    rw [scanMux_index (j := v x) (fun _ _ => rfl), if_pos (hlim x)]
  rwa [he] at HG

def countSignals (f : Nat → Sig n) (j : Nat) (x : Fin n → Bool) : Nat :=
  freeIdx (fun i => f i x) j

lemma countSignalsG {w t : Nat} {A : Set (Sig n)} {f : Nat → Sig n}
    (hf : ∀ j < t, f j ∈ A) (hz : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    Build A (Set.range (unaryWord w (countSignals f t))) (t * (w * 4)) := by
  have h := loopG (fun j => Set.range (unaryWord w (countSignals f j))) (t := t) (b := 0)
    (c := w * 4) (idle (by
      rintro _ ⟨i, rfl⟩
      exact unary_const (w := w) 0 hz ht i)) (by
      intro j hj
      have he : countSignals f (j + 1) = (fun x => countSignals f j x + (f j x).toNat) := by
        funext x
        exact freeIdx_succ _ _
      rw [he]
      exact unary_inc (fun i => Or.inr ⟨i, rfl⟩) (Or.inl (hf j hj)) (Or.inl hz))
  simpa only [Nat.zero_add] using h

lemma countSignals_bound (f : Nat → Sig n) (j : Nat) (x : Fin n → Bool) : countSignals f j x ≤ j := by
  exact (List.length_filter_le _ _).trans (by simp)

lemma maskFlipG {k t : Nat} {A : Set (Sig n)} {bit : Sig n}
    {pivot raw : (Fin n → Bool) → Nat} (hb : bit ∈ A)
    (hp : Available A (unaryWord t pivot)) (hr : Available A (wireBits k raw))
    (ht : k ≤ t) :
    Build A (Set.range (wireBits k (fun x => if bit x then raw x ^^^ (1 <<< pivot x) else raw x))) (k * 5) := by
  apply finG _ 5
  intro i
  let q := equalsIndex pivot i.val
  have hq : q ∈ A := hp ⟨i.val, lt_of_lt_of_le i.isLt ht⟩
  have h1 := andG hb hq
  have h2 := xorG (A := A ∪ {an bit q}) (Or.inl (hr i)) (Or.inr rfl : an bit q ∈ _)
  have he : wireBits k (fun x => if bit x then raw x ^^^ (1 <<< pivot x) else raw x) i = xo (wireBits k raw i) (an bit q) := by
    funext x
    change (if bit x then raw x ^^^ (1 <<< pivot x) else raw x).testBit i.val =
      xor ((raw x).testBit i.val) (bit x && q x)
    by_cases h : bit x = true
    · rw [if_pos h, Nat.testBit_xor, testBit_one_shiftLeft]
      simp [h, q, equalsIndex, eq_comm]
    · have hfalse : bit x = false := by cases he : bit x <;> simp_all
      simp [hfalse]
  rw [he]
  exact thenG h1 h2

lemma solveBits_bound {k m : Nat} {p : Nat → Nat} {f : Nat → Nat → Bool}
    {b : Nat → Bool} {w0 : Nat} (hw : w0 < 2 ^ k) (hp : ∀ j < m, p j < k) :
    solveBits p f b w0 m < 2 ^ k := by
  induction m with
  | zero => exact hw
  | succ m ih =>
    have h := ih (fun j hj => hp j (Nat.lt.step hj))
    rw [solveBits]
    split
    · exact h
    · exact flipBit_lt h (hp _ (Nat.lt_succ_self _))

lemma solveLoopWords {k t : Nat} {A : Set (Sig n)} {w0 : (Fin n → Bool) → Nat}
    (p : (Fin n → Bool) → Nat → Nat) (f : (Fin n → Bool) → Nat → Nat → Bool)
    (b : (Fin n → Bool) → Nat → Bool) (c : Nat)
    (hbase : Available A (wireBits k w0))
    (hstep : ∀ j < t,
      let old := fun x => solveBits (p x) (f x) (b x) (w0 x) j
      Build (A ∪ Set.range (wireBits k old))
        ({(fun x => xor (f x j (old x)) (b x j))} ∪ Set.range (unaryWord k (fun x => p x j))) c) :
    Build A (Set.range (wireBits k (fun x => solveBits (p x) (f x) (b x) (w0 x) t))) (t * (c + k * 5)) := by
  have H := loopG (fun j => Set.range (wireBits k (fun x => solveBits (p x) (f x) (b x) (w0 x) j)))
    (t := t) (b := 0) (c := c + k * 5)
    (idle (by rintro _ ⟨i, rfl⟩; exact hbase i)) (by
      intro j hj
      let old := fun x => solveBits (p x) (f x) (b x) (w0 x) j
      let bit := fun x => xor (f x j (old x)) (b x j)
      let B := A ∪ Set.range (wireBits k old)
      have h1 := hstep j hj
      have h2 := maskFlipG (A := B ∪ ({bit} ∪ Set.range (unaryWord k (fun x => p x j))))
        (pivot := fun x => p x j) (raw := old) (bit := bit) (Or.inr (Or.inl rfl))
        (fun i => Or.inr (Or.inr ⟨i, rfl⟩)) (fun i => Or.inl (Or.inr ⟨i, rfl⟩)) le_rfl
      have he : (fun x => solveBits (p x) (f x) (b x) (w0 x) (j + 1)) =
          (fun x => if bit x then old x ^^^ (1 <<< p x j) else old x) := by
        funext x
        rw [solveBits]
        change (if f x j (old x) = b x j then old x else old x ^^^ (1 <<< p x j)) =
          (if xor (f x j (old x)) (b x j) then old x ^^^ (1 <<< p x j) else old x)
        cases h : f x j (old x) <;> cases hb : b x j <;> simp [h, hb]
      rw [he]
      exact thenG h1 h2)
  simpa only [Nat.zero_add] using H

def familyOut {ι : Type*} (s : Finset ι) (B : ι → Set (Sig n)) : Set (Sig n) :=
  {f | ∃ i ∈ s, f ∈ B i}

lemma familyG {ι : Type*} [Fintype ι] {A : Set (Sig n)} (B : ι → Set (Sig n)) (c : Nat)
    (h : ∀ i, Build A (B i) c) : Build A (familyOut Finset.univ B) (Fintype.card ι * c) := by
  classical
  suffices ∀ s, Build A (familyOut s B) (s.card * c) by simpa [Finset.card_univ] using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa [familyOut] using (idle (A := A) (B := ∅) (by simp))
  | @insert i s hi ih =>
    have hnew := bothG ih (h i)
    refine relax hnew le_rfl ?_ (by rw [Finset.card_insert_of_notMem hi, Nat.succ_mul])
    rintro v ⟨j, hj, hv⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inr hv
    · exact Or.inl ⟨j, hj, hv⟩

lemma family_mem {ι : Type*} [Fintype ι] {B : ι → Set (Sig n)} {i : ι} {f : Sig n}
    (h : f ∈ B i) : f ∈ familyOut Finset.univ B := ⟨i, Finset.mem_univ i, h⟩

lemma freeIdx_le (f : Nat → Bool) (j : Nat) : freeIdx f j ≤ j :=
  countSignals_bound (n := 0) (fun i _ => f i) j Fin.elim0

lemma capWords {k t : Nat} {A : Set (Sig n)} {v : (Fin n → Bool) → Nat}
    (hv : Available A (wireBits k v)) (hb : ∀ x, v x < 2 ^ k) (hz : (fun _ => false) ∈ A) :
    Available A (wireBits t v) := by
  simpa only [Nat.shiftRight_zero] using wordRange hv hb hz 0 t

def pivotAt (r q s count : Nat) : Nat :=
  if s < 3 then (5 * r - 3) + 1 - q - 4 * (s + 1) + min (q - 1) count
  else (5 * r - 3) + 5 - q - 5 * (s + 2) + min (q - 1) count

lemma prefixCountG {r ell : Nat} {A : Set (Sig n)} {hist : (Fin n → Bool) → Nat}
    (ha : Available A (wireBits (ell - 1) hist)) (hz : (fun _ => false) ∈ A)
    (ht : (fun _ => true) ∈ A) (s : Nat) (hs : s < ell - 1) :
    Build A (Set.range (unaryWord r (fun x => targetCount (ell - 1) (hist x) s))) (s * (r * 4)) := by
  exact countSignalsG (w := r) (t := s) (f := fun j x => (hist x).testBit (ell - 1 - 1 - j))
    (fun j hj => wireBits_mem ha (by omega)) hz ht

lemma prefixCount_bound (t s : Nat) (hist : (Fin n → Bool) → Nat) (x : Fin n → Bool) :
    targetCount t (hist x) s ≤ s := targetCount_le _ _ _

lemma guardPivotsG {m r q ell : Nat} {A : Set (Sig n)} {hist : (Fin n → Bool) → Nat}
    (ha : Available A (wireBits (ell - 1) hist)) (hz : (fun _ => false) ∈ A)
    (ht : (fun _ => true) ∈ A) :
    Build A (familyOut Finset.univ (fun (s : Fin (ell - 1)) =>
      Set.range (unaryWord m (fun x => pivOf r q ell (hist x) s.val))))
      ((ell - 1) * (ell * (ell * 4) + m * (ell * 4))) := by
  suffices H : ∀ s : Fin (ell - 1),
      Build A (Set.range (unaryWord m (fun x => pivOf r q ell (hist x) s.val)))
        (ell * (ell * 4) + m * (ell * 4)) by
    simpa only [Fintype.card_fin] using (familyG _ _ H)
  intro s
  have hc : Build A (Set.range (unaryWord ell (fun x => targetCount (ell - 1) (hist x) s.val)))
      (ell * (ell * 4)) := relax (prefixCountG ha hz ht s.val s.isLt) le_rfl le_rfl
        (Nat.mul_le_mul_right (ell * 4) (show s.val ≤ ell by omega))
  refine thenG hc ?_
  have hm : ∀ x, targetCount (ell - 1) (hist x) s.val < ell := fun x =>
    lt_of_le_of_lt (targetCount_le _ _ _) (by omega)
  exact unaryLookupG (v := fun x => targetCount (ell - 1) (hist x) s.val)
    (f := fun j => unaryWord m (fun _ => pivotAt r q s.val j))
    (fun i => Or.inr ⟨i, rfl⟩) hm
    (fun j _ => unary_const (pivotAt r q s.val j) (Or.inl hz) (Or.inl ht)) (Or.inl hz)

lemma freeMaskG {m t : Nat} {A : Set (Sig n)} {p : (Fin n → Bool) → Nat → Nat}
    (hp : ∀ s < t, Available A (unaryWord m (fun x => p x s)))
    (hz : (fun _ => false) ∈ A) :
    Build A (Set.range (fun (i : Fin m) x => isFree t (p x) i.val)) (m * (t + 1)) := by
  apply finG _ (t + 1)
  intro i
  let ls := (List.range t).map (fun j => equalsIndex (fun x => p x j) i.val)
  have H := notAnyG ls (by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    exact hp j (List.mem_range.mp hj) i) hz
  have he : (fun x => !(ls.any (fun f => f x))) = (fun x => isFree t (p x) i.val) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [Bool.not_eq_true', List.any_eq_false, isFree_spec]
    constructor
    · intro h j hj heq
      have hj' : equalsIndex (fun x => p x j) i.val ∈ ls :=
        List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
      exact h _ hj' (by simp [equalsIndex, heq])
    · intro h f hf htrue
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
      exact h j (List.mem_range.mp hj) (of_decide_eq_true htrue)
  rw [he] at H
  simpa only [ls, List.length_map, List.length_range] using H

lemma packFreeG {m t d : Nat} {A : Set (Sig n)}
    {p : (Fin n → Bool) → Nat → Nat} {code : (Fin n → Bool) → Nat}
    (hc : Available A (wireBits d code)) (hcb : ∀ x, code x < 2 ^ d)
    (hm : ∀ (i : Fin m), (fun x => isFree t (p x) i.val) ∈ A)
    (hz : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    Build A (Set.range (wireBits m (fun x => packFree m t (p x) (code x))))
      (m * (m * ((m + 1) * 4) + (m + 1) * 4 + 1)) := by
  apply finG _ (m * ((m + 1) * 4) + (m + 1) * 4 + 1)
  intro i
  let mask := fun j x => isFree t (p x) j
  let cnt := countSignals mask i.val
  have hc' : Build A (Set.range (unaryWord (m + 1) cnt)) (m * ((m + 1) * 4)) :=
    relax (countSignalsG (w := m + 1) (f := mask) (t := i.val)
      (fun j hj => hm ⟨j, lt_trans hj i.isLt⟩) hz ht) le_rfl le_rfl
      (Nat.mul_le_mul_right ((m + 1) * 4) i.isLt.le)
  let D := A ∪ Set.range (unaryWord (m + 1) cnt)
  let pick := fun x => (code x).testBit (cnt x)
  have hidx (x : Fin n → Bool) : cnt x < m + 1 :=
    lt_trans (lt_of_le_of_lt (countSignals_bound mask i.val x) i.isLt) (Nat.lt_succ_self m)
  have hcode : Available A (wireBits (m + 1) code) := capWords hc hcb hz
  have hlook : Build D {pick} ((m + 1) * 4) :=
    unarySelectG (v := cnt) (f := fun j x => (code x).testBit j)
      (fun j => Or.inr ⟨j, rfl⟩) hidx (fun _ hj => Or.inl (wireBits_mem hcode hj)) (Or.inl hz)
  have hstep : Build (D ∪ {pick}) {an (mask i.val) pick} 1 :=
    andG (Or.inl (Or.inl (hm i))) (Or.inr rfl)
  have h := thenG hc' (thenG hlook hstep)
  have he : an (mask i.val) pick = wireBits m (fun x => packFree m t (p x) (code x)) i := by
    funext x
    simp only [an, mask, pick, cnt, countSignals, wireBits, packFree, ofBits_testBit, i.isLt, ↓reduceIte]
  rw [he] at h
  simpa only [Nat.add_assoc] using h

lemma solveGuardG {k r q ell : Nat} (hk : 0 < k) (hq : 0 < q) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    {A : Set (Sig n)} {sched : (Fin n → Bool) → Nat → Fin (2 ^ k)}
    {row hist tag : (Fin n → Bool) → Nat}
    (hrow : Available A (wireBits k row)) (hrowB : ∀ x, row x < 2 ^ k)
    (hhist : Available A (wireBits (ell - 1) hist))
    (htag : Available A (wireBits (5 * r - 3 - q) tag)) (htagB : ∀ x, tag x < 2 ^ (5 * r - 3 - q))
    (hp : ∀ s < ell - 1, Available A (unaryWord (5 * r - 3 - q) (fun x => pivOf r q ell (hist x) s)))
    (hc : ∀ j < r, Available A (wireBits k (fun x => (sched x (j + 1)).val)))
    (hz : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    Build A (Set.range (wireBits (5 * r - 3 - q) (fun x => solveGuard k r q ell (sched x) (row x) (hist x) (tag x))))
      ((ell - 1) * (ell * (ell * 4) + (k * 4 + r * (k * 22)) + k * 8 + ell * 4 + 4 + (5 * r - 3 - q) * 5)) := by
  let m := 5 * r - 3 - q
  let piv := fun x => pivOf r q ell (hist x)
  let b := fun x s => (hist x).testBit (ell - 1 - 1 - s)
  let F := fun x s w =>
    (mix k 1 (stateStep k r (sched x) false (rot k (k - (2 * r - 2)) w) (row x) (roundOf s - 1))).testBit
      ((k - q + 3 * (r - roundOf s) + min (q - 1) (targetCount (ell - 1) (hist x) s) + 1) % k)
  apply solveLoopWords piv F b _ htag
  intro s hs
  change s < ell - 1 at hs
  let old := fun x => solveBits (piv x) (F x) (b x) (tag x) s
  let D := A ∪ Set.range (wireBits m old)
  let cnt := fun x => targetCount (ell - 1) (hist x) s
  have holdB : ∀ x, old x < 2 ^ m := fun x => solveBits_bound (m := s) (htagB x)
    (fun j hj => pivOf_lt r q ell (hist x) j hq hell5 h5 (lt_trans hj hs))
  have hm : m ≤ k := by dsimp [m]; omega
  have holdK : ∀ x, old x < 2 ^ k := fun x => lt_of_lt_of_le (holdB x) (Nat.pow_le_pow_right (by decide) hm)
  have hold : Available D (wireBits k old) := capWords madeBits holdB (Or.inl hz)
  let ref := fun x => rot k (k - (2 * r - 2)) (old x)
  have href : Available D (wireBits k ref) := rotWire hk _ holdK hold
  have hcnt : Build D (Set.range (unaryWord ell cnt)) (ell * (ell * 4)) :=
    relax (prefixCountG (avail_mono hhist Set.subset_union_left) (Or.inl hz) (Or.inl ht) s hs)
      le_rfl le_rfl (Nat.mul_le_mul_right (ell * 4) (show s ≤ ell by omega))
  let state := fun x => stateStep k r (sched x) false (ref x) (row x) (roundOf s - 1)
  have hround : roundOf s - 1 ≤ r := by unfold roundOf; split_ifs <;> omega
  have hstate : Build D (Set.range (wireBits k state)) (k * 4 + r * (k * 22)) :=
    relax (cipherStateWords (r := r) hk false (sched := sched) (raw := ref) (name := row) (t := roundOf s - 1)
      (fun _ => rot_lt) hrowB href (avail_mono hrow Set.subset_union_left)
      (fun j hj => avail_mono (hc j (lt_of_lt_of_le hj hround)) Set.subset_union_left)) le_rfl le_rfl
      (Nat.add_le_add_left (Nat.mul_le_mul_right (k * 22) hround) (k * 4))
  have hmix : Build D (Set.range (wireBits k (fun x => mix k 1 (state x)))) (k * 4 + r * (k * 22) + k * 8) :=
    thenG hstate (mixWords hk 1 (fun x => stateStep_lt (hrowB x)) madeBits)
  let E := D ∪ (Set.range (unaryWord ell cnt) ∪ Set.range (wireBits k (fun x => mix k 1 (state x))))
  have H := bothG hcnt hmix
  have hlook : Build E {fun x => F x s (old x)} (ell * 4) := by
    exact unarySelectG (v := cnt) (fun i => Or.inr (Or.inl ⟨i, rfl⟩))
      (fun x => lt_of_le_of_lt (targetCount_le _ _ _) (by omega))
      (f := fun j => wireAt k (fun x => mix k 1 (state x))
        (k - q + 3 * (r - roundOf s) + min (q - 1) j + 1))
      (fun j _ => wireAt_mem hk (fun i => Or.inr (Or.inr ⟨i, rfl⟩)) _) (Or.inl (Or.inl hz))
  let D' := E ∪ {fun x => F x s (old x)}
  have hxor : Build D' {fun x => xor (F x s (old x)) (b x s)} 4 :=
    xorG (Or.inr rfl) (Or.inl (Or.inl (Or.inl (wireBits_mem hhist (by omega)))))
  have hmade := thenG H (thenG hlook hxor)
  refine relaxKeep hmade le_rfl ?_ ?_
  · rintro w (hw | ⟨i, rfl⟩)
    · exact Or.inr hw
    · exact Or.inl (Or.inl (hp s hs i))
  · simp only [Nat.add_assoc, Nat.le_refl]

def unrankAt (T : Nat → Nat → Nat) (m ticket : Nat) : Nat → Nat × Nat × Nat
  | 0 => (0, ticket, 0)
  | j + 1 =>
    let s := unrankAt T m ticket j
    let left := T (m - 1 - j) s.1
    let b : Bool := decide (left ≤ s.2.1)
    (s.1 + b.toNat, if b then s.2.1 - left else s.2.1, s.2.2 + 2 ^ j * b.toNat)

lemma unrankAt_eq (T : Nat → Nat → Nat) (m ticket : Nat) :
    ∀ j ≤ m,
      let s := unrankAt T m ticket j
      WeightedAddress.unrankForward T (m - j) j s.1 s.2.1 s.2.2 =
        WeightedAddress.unrankForward T m 0 0 ticket 0 := by
  intro j
  induction j with
  | zero => simp [unrankAt]
  | succ j ih =>
    intro hj
    have he : m - j = (m - (j + 1)) + 1 := by omega
    have he' : m - (j + 1) = m - 1 - j := by omega
    have h := ih (by omega)
    dsimp only at h ⊢
    rw [he, WeightedAddress.unrankForward, he'] at h
    simpa only [unrankAt, he'] using h

lemma unrankAt_root (T : Nat → Nat → Nat) (m ticket : Nat) :
    let s := unrankAt T m ticket m
    (s.2.2, s.2.1) = WeightedAddress.unrankWith T m 0 ticket := by
  have h := unrankAt_eq T m ticket m le_rfl
  rw [WeightedAddress.unrankForward_root] at h
  simpa only [Nat.sub_self, WeightedAddress.unrankForward] using h

lemma unrankAt_bounds (T : Nat → Nat → Nat) (m ticket j : Nat) :
    let s := unrankAt T m ticket j
    s.1 ≤ j ∧ s.2.1 ≤ ticket ∧ s.2.2 < 2 ^ j := by
  induction j with
  | zero => simp [unrankAt]
  | succ j ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    let s := unrankAt T m ticket j
    let l := T (m - 1 - j) s.1
    change s.1 + (decide (l ≤ s.2.1)).toNat ≤ j + 1 ∧
      (if decide (l ≤ s.2.1) then s.2.1 - l else s.2.1) ≤ ticket ∧
      s.2.2 + 2 ^ j * (decide (l ≤ s.2.1)).toNat < 2 ^ (j + 1)
    change s.1 ≤ j at h1
    change s.2.1 ≤ ticket at h2
    change s.2.2 < 2 ^ j at h3
    by_cases h : l ≤ s.2.1
    · have hout : s.2.2 + 2 ^ j < 2 ^ j * 2 := by omega
      simpa [h, Nat.pow_succ] using
        And.intro (Nat.add_le_add_right h1 1) (And.intro ((Nat.sub_le s.2.1 l).trans h2) hout)
    · have hout : s.2.2 < 2 ^ j * 2 := by omega
      simpa [h, Nat.pow_succ] using
        And.intro (Nat.le_succ_of_le h1) (And.intro h2 hout)

lemma storeBit {j word : Nat} (hw : word < 2 ^ j) (b : Bool) (i : Nat) :
    (word + 2 ^ j * b.toNat).testBit i = if i = j then b else word.testBit i := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add b.toNat hw i]
  by_cases hij : i = j
  · subst i
    simp only [lt_irrefl, if_false, Nat.sub_self, ↓reduceIte]
    cases b <;> decide
  · by_cases hi : i < j
    · simp only [hij, hi, ↓reduceIte]
    · have hj : j < i := by omega
      have he : word.testBit i = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega)))
      simp only [hij, hi, he, ↓reduceIte]
      have hb : b.toNat ≤ 1 := by cases b <;> decide
      have hp : 1 < 2 ^ (i - j) := Nat.one_lt_two_pow (by omega)
      exact Nat.testBit_lt_two_pow (lt_of_le_of_lt hb hp)

lemma weightedWordsG {q m w : Nat} (hwm : m + q ≤ w)
    {A : Set (Sig n)} {ticket : (Fin n → Bool) → Nat}
    (hb : ∀ x, ticket x < 2 ^ w) (hv : Available A (wireBits w ticket))
    (hz : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    Build A (Set.range (wireBits m (fun x => (WeightedAddress.unrank q m 0 (ticket x)).1)) ∪
      Set.range (wireBits w (fun x => (WeightedAddress.unrank q m 0 (ticket x)).2)))
      (m * (w * ((m + 1) * 4) + 13 * w + (m + 1) * 4)) := by
  let T := WeightedAddress.total q
  let s := fun j (x : Fin n → Bool) => unrankAt T m (ticket x) j
  let S := fun j => Set.range (unaryWord (m + 1) (fun x => (s j x).1)) ∪
    (Set.range (wireBits w (fun x => (s j x).2.1)) ∪ Set.range (wireBits m (fun x => (s j x).2.2)))
  have hp : Build A (S 0) 0 := by
    apply idle
    rintro f (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact unary_const (w := m + 1) 0 hz ht i
    · exact hv i
    · exact constWire (k := m) 0 hz ht i
  have hstep : ∀ j < m, Build (A ∪ S j) (S (j + 1))
      (w * ((m + 1) * 4) + 13 * w + (m + 1) * 4) := by
    intro j hj
    let E := A ∪ S j
    let hits := fun x => (s j x).1
    let res := fun x => (s j x).2.1
    let hist := fun x => (s j x).2.2
    let th := fun x => T (m - 1 - j) (hits x)
    let remain := fun x => 2 ^ w - th x
    have bhits : ∀ x, hits x < m + 1 := fun x => lt_of_le_of_lt (unrankAt_bounds T m (ticket x) j).1 (by omega)
    have bres : ∀ x, res x < 2 ^ w := fun x => lt_of_le_of_lt (unrankAt_bounds T m (ticket x) j).2.1 (hb x)
    have bhist : ∀ x, hist x < 2 ^ j := fun x => (unrankAt_bounds T m (ticket x) j).2.2
    have hc : Build E (Set.range (wireBits w remain)) (w * ((m + 1) * 4)) :=
      unaryLookupG (v := hits) (f := fun u => wireBits w (fun _ => 2 ^ w - T (m - 1 - j) u))
        (fun i => Or.inr (Or.inl ⟨i, rfl⟩)) bhits
        (fun _ _ => constWire _ (Or.inl hz) (Or.inl ht)) (Or.inl hz)
    let B := Set.range (wireBits w (guardedSub res th)) ∪ {geWord res th}
    have hwidth : m - 1 - j + q ≤ w := by omega
    have hth : ∀ x, th x ≤ 2 ^ w := fun x =>
      (WeightedAddress.total_le q (m - 1 - j) (hits x)).trans
        (Nat.pow_le_pow_right (by decide) hwidth)
    have hge : Build E B (w * ((m + 1) * 4) + 13 * w) := by
      apply thenG hc
      exact guardedSubG (F := res) (T := th) bres (fun _ => WeightedAddress.total_pos q _ _) hth
        (fun i => Or.inl (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))) madeBits (Or.inl (Or.inl hz))
    have hinc : Build (E ∪ B)
        (Set.range (unaryWord (m + 1) (fun x => hits x + (geWord res th x).toNat))) ((m + 1) * 4) :=
      unary_inc (fun i => Or.inl (Or.inr (Or.inl ⟨i, rfl⟩))) (Or.inr (Or.inr rfl)) (Or.inl (Or.inl hz))
    refine relaxKeep (seq hge hinc) le_rfl ?_ le_rfl
    rintro f (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, rfl⟩)
    · apply Or.inr; apply Or.inl; apply Or.inl
      refine ⟨i, ?_⟩
      funext x
      change (guardedSub res th x).testBit i.val =
        (if geWord res th x then res x - th x else res x).testBit i.val
      by_cases h : th x ≤ res x <;> simp [guardedSub, geWord, h]
    · have he : wireBits m (fun x => (s (j + 1) x).2.2) i =
          if i.val = j then geWord res th else wireBits m hist i := by
        funext x
        change (hist x + 2 ^ j * (geWord res th x).toNat).testBit i.val = _
        rw [storeBit (bhist x)]
        split <;> rfl
      rw [he]
      by_cases hh : i.val = j
      · rw [if_pos hh]
        exact Or.inr (Or.inl (Or.inr rfl))
      · rw [if_neg hh]
        exact Or.inl (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)))
  have H := loopG S hp hstep
  simp only [Nat.zero_add] at H
  refine relax H le_rfl ?_ le_rfl
  rintro f (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · apply Or.inr; apply Or.inr
    refine ⟨i, ?_⟩
    funext x
    exact congrArg (fun p : Nat × Nat => p.1.testBit i.val) (unrankAt_root T m (ticket x))
  · apply Or.inr; apply Or.inl
    refine ⟨i, ?_⟩
    funext x
    exact congrArg (fun p : Nat × Nat => p.2.testBit i.val) (unrankAt_root T m (ticket x))

def cipherPart (k r offset width : Nat) (mask : Bool) (sched : Nat → Fin (2 ^ k))
    (side : Bool) (word name : Nat) : Nat :=
  let raw := stateStep k r sched side word name r >>> offset
  if mask then raw % 2 ^ width else raw

lemma solveTri_bound {k base w : Nat} (hp : base + w ≤ k) (F : Nat → Nat) (target seed : Nat)
    (hs : seed < 2 ^ k) : solveTri base w F target seed < 2 ^ k :=
  solveBits_bound (m := w) (p := fun j => base + (w - 1 - j)) hs (by
    intro j hj
    change base + (w - 1 - j) < k
    omega)

lemma solveCipherG {k r base off w : Nat} (hk : 0 < k) (hb : base + w ≤ k)
    (hoff : off + w ≤ k) (side mask : Bool)
    {A : Set (Sig n)} {sched : (Fin n → Bool) → Nat → Fin (2 ^ k)}
    {name seed target : (Fin n → Bool) → Nat}
    (hn : Available A (wireBits k name)) (hnb : ∀ x, name x < 2 ^ k)
    (hs : Available A (wireBits k seed)) (hsb : ∀ x, seed x < 2 ^ k)
    (ht : Available A (wireBits w target))
    (hc : ∀ j < r, Available A (wireBits k (fun x => (sched x (if side then r + (j + 1) else j + 1)).val)))
    (hz : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A (Set.range (wireBits k (fun x => solveTri base w
      (fun u => cipherPart k r off w mask (sched x) side u (name x)) (target x) (seed x))))
      (w * ((k * 4 + r * (k * 22)) + 4 + k * 5)) := by
  let p := fun (_ : Fin n → Bool) d => base + (w - 1 - d)
  let F := fun x d old => (cipherPart k r off w mask (sched x) side old (name x)).testBit (w - 1 - d)
  let b := fun x d => (target x).testBit (w - 1 - d)
  refine solveLoopWords (t := w) p F b ((k * 4 + r * (k * 22)) + 4) hs ?_
  intro j hj
  let old := fun x => solveBits (p x) (F x) (b x) (seed x) j
  let D := A ∪ Set.range (wireBits k old)
  have hold : ∀ x, old x < 2 ^ k := by
    intro x
    change solveBits (p x) (F x) (b x) (seed x) j < 2 ^ k
    refine solveBits_bound (m := j) (hsb x) ?_
    intro s hs'
    dsimp only [p]
    omega
  let state := fun x => stateStep k r (sched x) side (old x) (name x) r
  have hstate : Build D (Set.range (wireBits k state)) (k * 4 + r * (k * 22)) :=
    cipherStateWords hk side (sched := sched) (raw := old) (name := name)
      hold hnb madeBits (avail_mono hn Set.subset_union_left)
      (fun u hu => avail_mono (hc u hu) Set.subset_union_left)
  let P := D ∪ Set.range (wireBits k state)
  have hF : (fun x => F x j (old x)) ∈ P := by
    have he : (fun x => F x j (old x)) = (fun x => (state x).testBit (off + (w - 1 - j))) := by
      funext x
      have hw : w - 1 - j < w := by omega
      cases mask <;> simp [F, state, cipherPart, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, hw]
    rw [he]
    exact wireBits_mem (madeBits (A := D) (v := state)) (j := off + (w - 1 - j)) (by omega)
  have hb' : (fun x => b x j) ∈ P :=
    Or.inl (Or.inl (wireBits_mem (j := w - 1 - j) ht (by omega)))
  have hx : Build P {fun x => xor (F x j (old x)) (b x j)} 4 := xorG hF hb'
  have h := thenG hstate hx
  refine relaxKeep h le_rfl ?_ le_rfl
  rintro u (hu | ⟨i, rfl⟩)
  · exact Or.inr hu
  · exact Or.inl (unary_const (A := D) (w := k) (base + (w - 1 - j)) (Or.inl hz) (Or.inl htrue) i)

lemma recoverRaw_bound {k r q : Nat} (hk : 7 * r + q ≤ k) (hqr : q + 2 ≤ r)
    (missed : Nat) (sched : Nat → Fin (2 ^ k)) (row col tag spare rowBits colBits : Nat) :
    recoverRaw k r q missed sched row col tag spare rowBits colBits < 2 ^ k := by
  have ha : min ((k + 1) / 2) (k - (5 * r - 3)) ≤ k :=
    (Nat.min_le_right _ _).trans (Nat.sub_le _ _)
  dsimp only [recoverRaw]
  refine solveTri_bound ?_ _ _ _ ?_
  · omega
  refine solveTri_bound ?_ _ _ _ ?_
  · omega
  split
  · exact rot_lt
  · exact ofBits_lt _ _

lemma recoverStaticG {k r q w d : Nat} (hk7 : 7 * r + q ≤ k) (hqr : q + 2 ≤ r)
    (hr : 5 ≤ r) (hw : k ≤ w) (hd : d ≤ q)
    {A : Set (Sig n)} {sched : (Fin n → Bool) → Nat → Fin (2 ^ k)}
    {row col tag spare ta tb : (Fin n → Bool) → Nat}
    (hrow : Available A (wireBits k row)) (hrowB : ∀ x, row x < 2 ^ k)
    (hcol : Available A (wireBits k col)) (hcolB : ∀ x, col x < 2 ^ k)
    (htag : Available A (wireBits (5 * r - 3 - q) tag)) (htagB : ∀ x, tag x < 2 ^ (5 * r - 3 - q))
    (hsp : Available A (wireBits w spare))
    (hta : Available A (wireBits ((k + 1) / 2) ta)) (htaB : ∀ x, ta x < 2 ^ ((k + 1) / 2))
    (htb : Available A (wireBits ((k + 1) / 2) tb)) (htbB : ∀ x, tb x < 2 ^ ((k + 1) / 2))
    (hC : ∀ j, 1 ≤ j → j ≤ 2 * r → Available A (wireBits k (fun x => (sched x j).val)))
    (hz : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    Build A (Set.range (wireBits k (fun x => recoverRaw k r q d (sched x) (row x) (col x) (tag x) (spare x)
      (leftPart k r d (ta x)) (rightPart k r q (tb x))))) (2 * k * ((k * 4 + r * (k * 22)) + 4 + k * 5)) := by
  let h := (k + 1) / 2
  let z := k - h
  let u := 5 * r - 3
  let start := k - (2 * r - 2)
  let a := min h (k - u)
  let g := z - u
  let baseA := k - a - (2 * r - 2)
  let baseQG := 3 * r - 1 - q
  have hk : 0 < k := by omega
  let rotTag := fun x => rot k start (tag x)
  have htagBK : ∀ x, tag x < 2 ^ k := fun x =>
    lt_of_lt_of_le (htagB x) (Nat.pow_le_pow_right (by decide) (by omega))
  have hrot : Available A (wireBits k rotTag) := rotWire hk _ htagBK (capWords htag htagB hz)
  let seed := fun x => if d = 0 then rotTag x else
    ofBits k (fun s => if start - d ≤ s ∧ s < start then (spare x).testBit (s - (start - d))
      else (rotTag x).testBit s)
  have hseed : Available A (wireBits k seed) := by
    intro i
    by_cases he : d = 0
    · have hw : wireBits k seed i = wireBits k rotTag i := by
        funext x
        change (seed x).testBit i.val = (rotTag x).testBit i.val
        simp [seed, he]
      rw [hw]
      exact hrot i
    · by_cases hh : start - d ≤ i.val ∧ i.val < start
      · have hi : i.val - (start - d) < w := by omega
        have hw : wireBits k seed i = (fun x => (spare x).testBit (i.val - (start - d))) := by
          funext x
          change (seed x).testBit i.val = (spare x).testBit (i.val - (start - d))
          rw [show seed x = _ from if_neg he, ofBits_testBit, if_pos i.isLt, if_pos hh]
        rw [hw]
        exact wireBits_mem hsp hi
      · have hw : wireBits k seed i = wireBits k rotTag i := by
          funext x
          change (seed x).testBit i.val = (rotTag x).testBit i.val
          rw [show seed x = _ from if_neg he, ofBits_testBit, if_pos i.isLt, if_neg hh]
        rw [hw]
        exact hrot i
  have hseedB : ∀ x, seed x < 2 ^ k := by
    intro x
    unfold seed
    split
    · exact rot_lt
    · exact ofBits_lt _ _
  let L := fun x => leftPart k r d (ta x)
  let R := fun x => rightPart k r q (tb x)
  have hL : Available A (wireBits (a - d) L) := by
    intro i
    change (fun x => ((ta x >>> (h - a)) % 2 ^ (a - d)).testBit i.val) ∈ A
    simp only [Nat.testBit_mod_two_pow, i.isLt, decide_true, Bool.true_and]
    exact wordRange hta htaB hz (h - a) (a - d) i
  have hR : Available A (wireBits (q + g) R) := by
    intro i
    change (fun x => ((tb x >>> (6 * r - q - z)) % 2 ^ (q + g)).testBit i.val) ∈ A
    simp only [Nat.testBit_mod_two_pow, i.isLt, decide_true, Bool.true_and]
    exact wordRange htb htbB hz (6 * r - q - z) (q + g) i
  let rowF := fun x word => cipherPart k r (k - a) (a - d) (decide (d ≠ 0)) (sched x) false word (row x)
  let colF := fun x word => cipherPart k r (6 * r - q) (q + g) true (sched x) true word (col x)
  let mid := fun x => solveTri baseA (a - d) (rowF x) (L x) (seed x)
  let out := fun x => solveTri baseQG (q + g) (colF x) (R x) (mid x)
  let cost := (k * 4 + r * (k * 22)) + 4 + k * 5
  have haK : a ≤ k := (Nat.min_le_right _ _).trans (Nat.sub_le _ _)
  have hA : baseA + (a - d) ≤ k := by dsimp only [baseA]; omega
  have hQ : baseQG + (q + g) ≤ k := by dsimp only [baseQG, g, z, h, u]; omega
  have hoffA : k - a + (a - d) ≤ k := by omega
  have hoffQ : 6 * r - q + (q + g) ≤ k := by dsimp [g, z, h, u]; omega
  have hmG : Build A (Set.range (wireBits k mid)) ((a - d) * cost) :=
    solveCipherG hk hA hoffA false (decide (d ≠ 0)) (sched := sched)
      hrow hrowB hseed hseedB hL (by
        intro j hj
        exact hC (j + 1) (by omega) (by omega)) hz ht
  let D := A ∪ Set.range (wireBits k mid)
  have hmidB : ∀ x, mid x < 2 ^ k := fun x => solveTri_bound hA _ _ _ (hseedB x)
  have hoG : Build D (Set.range (wireBits k out)) ((q + g) * cost) :=
    solveCipherG hk hQ hoffQ true true (sched := sched)
      (avail_mono hcol Set.subset_union_left) hcolB (madeBits (A := A) (v := mid)) hmidB
      (avail_mono hR Set.subset_union_left) (by
        intro j hj
        exact avail_mono (hC (r+(j+1)) (by omega) (by omega)) Set.subset_union_left)
      (Or.inl hz) (Or.inl ht)
  have he : out = (fun x => recoverRaw k r q d (sched x) (row x) (col x) (tag x) (spare x)
      (leftPart k r d (ta x)) (rightPart k r q (tb x))) := by
    funext x
    by_cases hd' : d = 0 <;>
      simp [out, recoverRaw, colF, mid, rowF, cipherPart, L, R, seed, rotTag, baseA, baseQG, h, z, a, g, u, start, hd']
  rw [← he]
  refine relax (thenG hmG hoG) le_rfl le_rfl ?_
  rw [← Nat.add_mul]
  exact Nat.mul_le_mul_right cost (by omega)

def guardCost (k r q ell : Nat) : Nat :=
  let m := 5 * r - 3 - q
  let t := ell - 1
  t * (ell * (ell * 4) + m * (ell * 4)) + m * (t + 1) +
    m * (m * ((m + 1) * 4) + (m + 1) * 4 + 1) +
    t * (ell * (ell * 4) + (k * 4 + r * (k * 22)) + k * 8 + ell * 4 + 4 + m * 5)

lemma selectedLabelG {k r q ell : Nat} (hk : 0 < k) (hq : 0 < q) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    {A : Set (Sig n)} {sched : (Fin n → Bool) → Nat → Fin (2 ^ k)}
    {row hist code : (Fin n → Bool) → Nat}
    (hrow : Available A (wireBits k row)) (hbrow : ∀ x, row x < 2 ^ k)
    (hhist : Available A (wireBits (ell - 1) hist))
    (hcode : Available A (wireBits (5 * r - 3 - q - (ell - 1)) code))
    (hbcode : ∀ x, code x < 2 ^ (5 * r - 3 - q - (ell - 1)))
    (hc : ∀ j < r, Available A (wireBits k (fun x => (sched x (j + 1)).val)))
    (hz : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    Build A (Set.range (wireBits (5 * r - 3 - q)
      (fun x => selectedLabel k r q ell (sched x) (row x) (hist x) (code x)))) (guardCost k r q ell) := by
  let m := 5 * r - 3 - q
  let t := ell - 1
  let p := fun x => pivOf r q ell (hist x)
  let F := familyOut Finset.univ (fun (s : Fin t) => Set.range (unaryWord m (fun x => p x s.val)))
  let M := Set.range (fun (i : Fin m) x => isFree t (p x) i.val)
  let tag := fun x => packFree m t (p x) (code x)
  let P := Set.range (wireBits m tag)
  have hpiv : Build A F _ :=
    guardPivotsG (m := m) (r := r) (q := q) (ell := ell) (hist := hist) hhist hz ht
  have hFp : ∀ s < t, Available F (unaryWord m (fun x => p x s)) := fun s hs i =>
    ⟨⟨s, hs⟩, Finset.mem_univ _, ⟨i, rfl⟩⟩
  have hm : Build (A ∪ F) M _ := freeMaskG (m := m) (t := t) (p := p)
    (fun s hs => avail_mono (hFp s hs) Set.subset_union_right) (Or.inl hz)
  let D := A ∪ (F ∪ M)
  have hpack : Build D P _ := packFreeG (m := m) (t := t) (p := p)
    (avail_mono hcode Set.subset_union_left) hbcode
    (fun i => Or.inr (Or.inr ⟨i, rfl⟩)) (Or.inl hz) (Or.inl ht)
  have hsolve : Build (A ∪ ((F ∪ M) ∪ P)) (Set.range (wireBits m
      (fun x => solveGuard k r q ell (sched x) (row x) (hist x) (tag x)))) _ :=
    solveGuardG hk hq hk7 hell5 hellr h5 (sched := sched) (hist := hist) (tag := tag)
      (avail_mono hrow Set.subset_union_left) hbrow (avail_mono hhist Set.subset_union_left)
      (fun i => Or.inr (Or.inr ⟨i, rfl⟩)) (fun _ => ofBits_lt _ _)
      (fun s hs i => Or.inr (Or.inl (Or.inl (hFp s hs i))))
      (fun j hj => avail_mono (hc j hj) Set.subset_union_left) (Or.inl hz) (Or.inl ht)
  exact thenG (seq (seq hpiv hm) hpack) hsolve

lemma ltConstG {w : Nat} {A : Set (Sig n)} {v : (Fin n → Bool) → Nat}
    (c : Nat) (hcap : c ≤ 2 ^ w) (hb : ∀ x, v x < 2 ^ w) (hv : Available A (wireBits w v))
    (hz : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    Build A {fun x => decide (v x < c)} (13 * w + 1) := by
  have hh := guardedSubConstG c hcap hb hv hz ht
  have hn := notG (A := A ∪ (Set.range (bitsOf w (guardedSub v (fun _ => c))) ∪ {geWord v (fun _ => c)}))
    (f := geWord v (fun _ => c)) (Or.inr (Or.inr rfl))
  have h := thenG hh hn
  have he : nt (geWord v (fun _ => c)) = (fun x => decide (v x < c)) := by
    funext x
    by_cases hle : c ≤ v x
    · simp [nt, geWord, hle, Nat.not_lt_of_ge hle]
    · have hlt : v x < c := by omega
      simp [nt, geWord, hle, hlt]
  rwa [he] at h

def divRecoveryCost (k r q ell w : Nat) : Nat :=
  (ell - 1) * (ell * 4) +
    (q + 1) * (2 * k * (k * 4 + r * (k * 22) + 4 + k * 5) + (13 * w + 1)) +
    (k * (ell * 4) + ell * 4)

lemma recoverDynamicG {k r q ell w : Nat} (hk7 : 7 * r + q ≤ k) (hqr : q + 2 ≤ r)
    (hr : 5 ≤ r) (hell : 0 < ell) (hw : k ≤ w)
    {A : Set (Sig n)} {sched : (Fin n → Bool) → Nat → Fin (2 ^ k)}
    {row col tag spare ta tb hist : (Fin n → Bool) → Nat}
    (hrow : Available A (wireBits k row)) (hrowB : ∀ x, row x < 2 ^ k)
    (hcol : Available A (wireBits k col)) (hcolB : ∀ x, col x < 2 ^ k)
    (htag : Available A (wireBits (5 * r - 3 - q) tag)) (htagB : ∀ x, tag x < 2 ^ (5 * r - 3 - q))
    (hsp : Available A (wireBits w spare)) (hspB : ∀ x, spare x < 2 ^ w)
    (hta : Available A (wireBits ((k + 1) / 2) ta)) (htaB : ∀ x, ta x < 2 ^ ((k + 1) / 2))
    (htb : Available A (wireBits ((k + 1) / 2) tb)) (htbB : ∀ x, tb x < 2 ^ ((k + 1) / 2))
    (hhist : Available A (wireBits (ell - 1) hist))
    (hC : ∀ j, 1 ≤ j → j ≤ 2 * r → Available A (wireBits k (fun x => (sched x j).val)))
    (hz : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    let miss := fun x => q - bitWeight (ell - 1) (hist x)
    let raw := fun x => recoverRaw k r q (miss x) (sched x) (row x) (col x) (tag x) (spare x)
      (leftPart k r (miss x) (ta x)) (rightPart k r q (tb x))
    Build A (Set.range (wireBits k raw) ∪ {fun x => decide (spare x < 2 ^ miss x)}) (divRecoveryCost k r q ell w) := by
  let hits := fun x => bitWeight (ell - 1) (hist x)
  let raw := fun m x => recoverRaw k r q m (sched x) (row x) (col x) (tag x) (spare x)
      (leftPart k r m (ta x)) (rightPart k r q (tb x))
  let valid := fun m (x : Fin n → Bool) => decide (spare x < 2 ^ m)
  let C := Set.range (unaryWord ell hits)
  let F := fun (m : Fin (q + 1)) => Set.range (wireBits k (raw m.val)) ∪ {valid m.val}
  let B := familyOut Finset.univ F
  have hc : Build A C ((ell - 1) * (ell * 4)) :=
    countSignalsG (w := ell) (t := ell - 1) (f := fun j x => (hist x).testBit j)
      (fun j hj => wireBits_mem hhist hj) hz ht
  let branchCost := 2 * k * (k * 4 + r * (k * 22) + 4 + k * 5) + (13 * w + 1)
  have hbranch (m : Fin (q + 1)) : Build A (F m) branchCost := by
    have hm : m.val ≤ q := Nat.lt_succ_iff.mp m.isLt
    have hmw : m.val ≤ w := by omega
    exact bothG
      (recoverStaticG hk7 hqr hr hw hm (sched := sched) hrow hrowB hcol hcolB htag htagB
        hsp hta htaB htb htbB hC hz ht)
      (ltConstG (2 ^ m.val) (Nat.pow_le_pow_right (by decide) hmw) hspB hsp hz ht)
  have hbranches : Build A B ((q + 1) * branchCost) := by
    simpa only [Fintype.card_fin] using familyG F branchCost hbranch
  let D := A ∪ (C ∪ B)
  let pick (j : Nat) : Fin (q + 1) := ⟨q - j, by omega⟩
  have hlim : ∀ x, hits x < ell := fun x =>
    lt_of_le_of_lt (freeIdx_le (fun j => (hist x).testBit j) (ell - 1)) (by omega)
  have hsel : Available D (unaryWord ell hits) := fun i => Or.inr (Or.inl ⟨i, rfl⟩)
  have hv := unaryLookupG (f := fun j => wireBits k (raw (q - j))) hsel hlim
    (fun j _ i => Or.inr (Or.inr
      (family_mem (B := F) (i := pick j) (Or.inl ⟨i, rfl⟩)))) (Or.inl hz)
  have hvalid := unarySelectG (f := fun j => valid (q - j)) hsel hlim
    (fun j _ => Or.inr (Or.inr
      (family_mem (B := F) (i := pick j) (Or.inr rfl)))) (Or.inl hz)
  exact thenG (bothG hc hbranches) (bothG hv hvalid)

def tupleCost (k r q ell w : Nat) : Nat :=
  guardCost k r q ell + divRecoveryCost k r q ell w +
    (2 * (k * 4 + r * (k * 22) + (((k + 1) / 2) * 5 + (k + 1) / 2)) + (2 + k))

lemma keyTupleG {k r q ell w : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2) (hw : k ≤ w)
    {A : Set (Sig n)} {sched : (Fin n → Bool) → Nat → Fin (2 ^ k)}
    {row col hist code spare ta tb : (Fin n → Bool) → Nat}
    (hrow : Available A (wireBits k row)) (hrowB : ∀ x, row x < 2 ^ k)
    (hcol : Available A (wireBits k col)) (hcolB : ∀ x, col x < 2 ^ k)
    (hhist : Available A (wireBits (ell - 1) hist))
    (hcode : Available A (wireBits (5 * r - 3 - q - (ell - 1)) code))
    (hbcode : ∀ x, code x < 2 ^ (5 * r - 3 - q - (ell - 1)))
    (hsp : Available A (wireBits w spare)) (hspB : ∀ x, spare x < 2 ^ w)
    (hta : Available A (wireBits ((k + 1) / 2) ta)) (htaB : ∀ x, ta x < 2 ^ ((k + 1) / 2))
    (htb : Available A (wireBits ((k + 1) / 2) tb)) (htbB : ∀ x, tb x < 2 ^ ((k + 1) / 2))
    (hC : ∀ j, 1 ≤ j → j ≤ 2 * r → Available A (wireBits k (fun x => (sched x j).val)))
    (hz : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    let out := fun x => keyTuple k r q ell (sched x) (row x) (col x) (ta x) (tb x) (hist x) (code x) (spare x)
    Build A ({fun x => (out x).1} ∪ Set.range (wireBits k (fun x => (out x).2))) (tupleCost k r q ell w) := by
  have hk : 0 < k := by omega
  let label := fun x => selectedLabel k r q ell (sched x) (row x) (hist x) (code x)
  let miss := fun x => q - bitWeight (ell - 1) (hist x)
  let raw := fun x => recoverRaw k r q (miss x) (sched x) (row x) (col x) (label x) (spare x)
    (leftPart k r (miss x) (ta x)) (rightPart k r q (tb x))
  let valid : Sig n := fun x => decide (spare x < 2 ^ miss x)
  let B := Set.range (wireBits (5 * r - 3 - q) label)
  let R := Set.range (wireBits k raw) ∪ {valid}
  have hl : Build A B (guardCost k r q ell) := selectedLabelG hk hq hk7 hell5 hellr h5 hrow hrowB hhist hcode hbcode
    (fun j hj => hC (j+1) (by omega) (by omega)) hz ht
  have hb : ∀ x, label x < 2 ^ (5 * r - 3 - q) := fun x =>
    solveBits_bound (m := ell - 1) (p := pivOf r q ell (hist x)) (ofBits_lt _ _)
      (fun j hj => pivOf_lt r q ell (hist x) j hq hell5 h5 hj)
  have hr : Build (A ∪ B) R (divRecoveryCost k r q ell w) :=
    recoverDynamicG hk7 hqr (by omega) (by omega) hw
      (avail_mono hrow Set.subset_union_left) hrowB (avail_mono hcol Set.subset_union_left) hcolB madeBits hb
      (avail_mono hsp Set.subset_union_left) hspB (avail_mono hta Set.subset_union_left) htaB
      (avail_mono htb Set.subset_union_left) htbB (avail_mono hhist Set.subset_union_left)
      (fun j h1 h2 => avail_mono (hC j h1 h2) Set.subset_union_left) (Or.inl hz) (Or.inl ht)
  have head := thenG hl hr
  let D := A ∪ R
  let h := (k + 1) / 2
  let z := k - h
  have hzh : z + h = k := by dsimp only [z, h]; omega
  let la : Sig n := fun x => (stateStep k r (sched x) false (raw x) (row x) r >>> z) == ta x
  let ra : Sig n := fun x => (stateStep k r (sched x) true (raw x) (col x) r >>> z) == tb x
  let c := k * 4 + r * (k * 22) + (h * 5 + h)
  have hraw : Available D (wireBits k raw) := fun i => Or.inr (Or.inl ⟨i, rfl⟩)
  have hrawB : ∀ x, raw x < 2 ^ k := fun x =>
    recoverRaw_bound hk7 hqr (miss x) (sched x) (row x) (col x) (label x) (spare x)
      (leftPart k r (miss x) (ta x)) (rightPart k r q (tb x))
  have ha : Build D {la} c := cipherMatchG hk false h z (sched := sched) hrawB hrowB hraw
    (avail_mono hrow Set.subset_union_left) (fun j hj => avail_mono (hC (j+1) (by omega) (by omega)) Set.subset_union_left)
    (avail_mono hta Set.subset_union_left) htaB hzh (Or.inl hz) (Or.inl ht)
  have hb' : Build D {ra} c := cipherMatchG hk true h z (sched := sched) hrawB hcolB hraw
    (avail_mono hcol Set.subset_union_left) (fun j hj => avail_mono (hC (r+(j+1)) (by omega) (by omega)) Set.subset_union_left)
    (avail_mono htb Set.subset_union_left) htbB hzh (Or.inl hz) (Or.inl ht)
  let P := D ∪ ({la} ∪ {ra})
  have htest : Build P {an la ra} 1 := andG (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  let live := an valid (an la ra)
  have hlive : Build (P ∪ {an la ra}) {live} 1 := andG (Or.inl (Or.inl (Or.inr (Or.inr rfl)))) (Or.inr rfl)
  have H := seq head (thenG (bothG ha hb') (thenG htest hlive))
  have hmask : Build (A ∪ (R ∪ {live})) (Set.range (wireBits k (fun x => if live x then raw x else 0))) k := by
    have he : (fun i : Fin k => an live (wireBits k raw i)) =
        wireBits k (fun x => if live x then raw x else 0) := by
      funext i x
      cases hx : live x <;> simp [wireBits, an, hx]
    rw [← he]
    exact wordAndG (v := fun _ => live)
      (fun _ => Or.inr (Or.inr rfl)) (fun i => Or.inr (Or.inl (Or.inl ⟨i, rfl⟩)))
  change Build A ({live} ∪ Set.range (wireBits k (fun x => if live x then raw x else 0)))
    (tupleCost k r q ell w)
  refine relax (seq H hmask) le_rfl ?_ ?_
  · rintro f (hf | hf)
    · exact Or.inl (Or.inr hf)
    · exact Or.inr hf
  · change guardCost k r q ell + divRecoveryCost k r q ell w + (c + c + (1 + 1)) + k ≤
      guardCost k r q ell + divRecoveryCost k r q ell w + (2 * c + (2 + k))
    simp only [Nat.two_mul]
    omega

def rootSlots (q ell : Nat) : Nat := WeightedAddress.total q (ell - 1) 0

def addrWidth (r q ell : Nat) : Nat := Nat.clog 2 (usedSlots r q ell (rootSlots q ell))

lemma rootSlots_bound {k r q ell : Nat} (hkr : 7 * r + q ≤ k) (hqr : q + 2 ≤ r)
    (hr : 5 ≤ r) (hell : ell ≤ r) : usedSlots r q ell (rootSlots q ell) ≤ 2 ^ k := by
  unfold usedSlots rootSlots
  refine (Nat.mul_le_mul_left _ (WeightedAddress.total_le _ _ _)).trans ?_
  rw [← Nat.pow_add]
  exact Nat.pow_le_pow_right (by decide) (by omega)

lemma addrWidth_bound {k r q ell : Nat} (hkr : 7 * r + q ≤ k) (hqr : q + 2 ≤ r)
    (hr : 5 ≤ r) (hell : ell ≤ r) : addrWidth r q ell ≤ k :=
  (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr (rootSlots_bound hkr hqr hr hell)

lemma residual_bound {q m val w : Nat} (hval : val < 2 ^ w) :
    (WeightedAddress.unrank q m 0 val).2 < 2 ^ w := by
  have he := congrArg Prod.snd (unrankAt_root (WeightedAddress.total q) m val)
  exact lt_of_le_of_lt (he ▸ (unrankAt_bounds (WeightedAddress.total q) m val m).2.1) hval

lemma completeUnrank (q m h s : Nat) (hh : h < 2 ^ m)
    (hs : s < (if bitWeight m h < q then 2 ^ q else 1)) :
    ∃! a : Fin (WeightedAddress.total q m 0), WeightedAddress.unrank q m 0 a.val = (h, s) := by
  let E := WeightedAddress.rootEquiv q m
  have H : s < WeightedAddress.leaf q (WeightedAddress.pop m h) := hs
  let p : {p : Nat × Nat // p.1 < 2 ^ m ∧ p.2 < WeightedAddress.leaf q (WeightedAddress.pop m p.1)} :=
    ⟨(h, s), hh, H⟩
  refine ⟨E.symm p, congrArg Subtype.val (E.apply_symm_apply p), ?_⟩
  intro a ha
  apply E.injective
  exact Subtype.ext (ha.trans (congrArg Subtype.val (E.apply_symm_apply p)).symm)

def decoderCost (k r q ell : Nat) : Nat :=
  let w := k + 1
  let t := ell - 1
  t * (w * ((t + 1) * 4) + 13 * w + (t + 1) * 4) + tupleCost k r q ell w + (13 * w + 1) + (1 + k)

lemma decodeWordsG {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hkr : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    {A : Set (Sig n)} {sched : (Fin n → Bool) → Nat → Fin (2 ^ k)}
    {row col ta tb addr : (Fin n → Bool) → Nat}
    (hrow : Available A (wireBits k row)) (hrowB : ∀ x, row x < 2 ^ k)
    (hcol : Available A (wireBits k col)) (hcolB : ∀ x, col x < 2 ^ k)
    (hta : Available A (wireBits ((k + 1) / 2) ta)) (htaB : ∀ x, ta x < 2 ^ ((k + 1) / 2))
    (htb : Available A (wireBits ((k + 1) / 2) tb)) (htbB : ∀ x, tb x < 2 ^ ((k + 1) / 2))
    (haddr : Available A (wireBits (addrWidth r q ell) addr))
    (haddrB : ∀ x, addr x < 2 ^ addrWidth r q ell)
    (hC : ∀ j, 1 ≤ j → j ≤ 2 * r → Available A (wireBits k (fun x => (sched x j).val)))
    (hz : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    let D := fun x => decodeKey k r q ell (rootSlots q ell) (WeightedAddress.unrank q (ell - 1) 0)
      (sched x) (row x) (col x) (ta x) (tb x) (addr x)
    Build A ({fun x => (D x).1} ∪ Set.range (wireBits k (fun x => (D x).2))) (decoderCost k r q ell) := by
  let w := k + 1
  let t := ell - 1
  let d := 5 * r - 3 - q - t
  let high := fun x => addr x >>> d
  let low := fun x => addr x % 2 ^ d
  let hist := fun x => (WeightedAddress.unrank q t 0 (high x)).1
  let spare := fun x => (WeightedAddress.unrank q t 0 (high x)).2
  let cap := usedSlots r q ell (rootSlots q ell)
  let inRange : Sig n := fun x => decide (addr x < cap)
  have hW := addrWidth_bound hkr hqr (by omega) hellr
  have hB : ∀ x, addr x < 2 ^ w := fun x =>
    lt_of_lt_of_le (haddrB x) (Nat.pow_le_pow_right (by decide) (by omega))
  have hH : Available A (wireBits w high) := wordRange haddr haddrB hz d w
  have hHB : ∀ x, high x < 2 ^ w := fun x => (Nat.shiftRight_le _ _).trans_lt (hB x)
  have hL : Available A (wireBits d low) := by
    intro i
    have he : wireBits d low i = wireBits d addr i := by
      funext x
      change ((addr x) % 2 ^ d).testBit i.val = (addr x).testBit i.val
      simp only [Nat.testBit_mod_two_pow, i.isLt, decide_true, Bool.true_and]
    rw [he]
    exact capWords haddr haddrB hz i
  have hLB : ∀ x, low x < 2 ^ d := fun _ => Nat.mod_lt _ (Nat.two_pow_pos _)
  let B := Set.range (wireBits t hist) ∪ Set.range (wireBits w spare)
  have hu : Build A B (t * (w * ((t + 1) * 4) + 13 * w + (t + 1) * 4)) :=
    weightedWordsG (by omega) hHB hH hz ht
  let tup := fun x => keyTuple k r q ell (sched x) (row x) (col x) (ta x) (tb x) (hist x) (low x) (spare x)
  let O := {fun x => (tup x).1} ∪ Set.range (wireBits k (fun x => (tup x).2))
  have ho : Build (A ∪ B) O (tupleCost k r q ell w) :=
    keyTupleG hq hqr hkr hell5 hellr h5 (by omega)
      (avail_mono hrow Set.subset_union_left) hrowB (avail_mono hcol Set.subset_union_left) hcolB
      (fun i => Or.inr (Or.inl ⟨i, rfl⟩)) (avail_mono hL Set.subset_union_left) hLB
      (fun i => Or.inr (Or.inr ⟨i, rfl⟩)) (fun x => residual_bound (hHB x))
      (avail_mono hta Set.subset_union_left) htaB (avail_mono htb Set.subset_union_left) htbB
      (fun j h1 h2 => avail_mono (hC j h1 h2) Set.subset_union_left) (Or.inl hz) (Or.inl ht)
  have hslot : Build A {inRange} (13 * w + 1) :=
    ltConstG cap ((rootSlots_bound hkr hqr (by omega) hellr).trans (Nat.pow_le_pow_right (by decide) (by omega)))
      hB (capWords haddr haddrB hz) hz ht
  let P := A ∪ (O ∪ {inRange})
  let L := fun x => (tup x).1
  let raw := fun x => (tup x).2
  let LG := an inRange L
  let W := fun i => an inRange (wireBits k raw i)
  have hl : Build P {LG} 1 := andG (Or.inr (Or.inr rfl)) (Or.inr (Or.inl (Or.inl rfl)))
  have hv : Build P (Set.range W) k :=
    wordAndG (v := fun _ => inRange) (u := wireBits k raw)
      (fun _ => Or.inr (Or.inr rfl)) (fun i => Or.inr (Or.inl (Or.inr ⟨i, rfl⟩)))
  let D := fun x => decodeKey k r q ell (rootSlots q ell) (WeightedAddress.unrank q t 0)
    (sched x) (row x) (col x) (ta x) (tb x) (addr x)
  have he1 : LG = fun x => (D x).1 := by
    funext x
    by_cases h : addr x < cap <;> simp [LG, an, L, inRange, D, decodeKey, h, cap, tup, hist, spare, high, low, d, t]
  have he2 : W = wireBits k (fun x => (D x).2) := by
    funext i x
    by_cases h : addr x < cap <;> simp [W, an, inRange, wireBits, raw, D, decodeKey, h, cap, tup, hist, spare, high, low, d, t]
  simpa only [he1, he2, decoderCost, w, t] using thenG (bothG (thenG hu ho) hslot) (bothG hl hv)

lemma decoderCost_le {k r q ell : Nat} (hqr : q + 2 ≤ r) (hk : 7 * r + q ≤ k) (he : ell ≤ r) :
    2 + decoderCost k r q ell ≤ 1048576 * (k + 1) ^ 6 * (r + 1) := by
  let K := k + 1
  let R := r + 1
  have hK : 1 ≤ K := by omega
  have hR : 1 ≤ R := by omega
  have hkK : k ≤ K := by omega
  have hrR : r ≤ R := by omega
  have hm : 5 * r - 3 - q ≤ K := by omega
  have hm' : 5 * r - 3 - q + 1 ≤ K := by omega
  have hell : ell ≤ K := by omega
  have ht : ell - 1 ≤ K := by omega
  have ht' : ell - 1 + 1 ≤ K := by omega
  have hh : (k + 1) / 2 ≤ K := by omega
  have hq : q + 1 ≤ K := by omega
  have hsum : 2 + decoderCost k r q ell ≤
      2 + (K * (K * (K * 4) + 13 * K + K * 4) +
      ((K * (K * (K * 4) + K * (K * 4)) + K * K + K * (K * (K * 4) + K * 4 + 1) +
          K * (K * (K * 4) + (K * 4 + R * (K * 22)) + K * 8 + K * 4 + 4 + K * 5)) +
        (K * (K * 4) + K * (2 * K * (K * 4 + R * (K * 22) + 4 + K * 5) + (13 * K + 1)) +
          (K * (K * 4) + K * 4)) +
        (2 * (K * 4 + R * (K * 22) + (K * 5 + K)) + (2 + K))) + (13 * K + 1) + (1 + K)) := by
    dsimp only [decoderCost, tupleCost, guardCost, divRecoveryCost]
    change _ ≤ _
    gcongr <;> assumption
  have h1 : K ≤ K ^ 2 := by
    rw [pow_two]
    simpa using Nat.mul_le_mul_left K hK
  have h2 : K ^ 2 ≤ K ^ 3 := Nat.pow_le_pow_right hK (by decide)
  have h3 : K ^ 3 ≤ K ^ 3 * R := by simpa using Nat.mul_le_mul_left (K ^ 3) hR
  have h4 : K ^ 2 * R ≤ K ^ 3 * R := Nat.mul_le_mul_right R h2
  have h5 : K * R ≤ K ^ 3 * R := Nat.mul_le_mul_right R (h1.trans h2)
  have h6 : K ^ 3 * R ≤ K ^ 6 * R := Nat.mul_le_mul_right R (Nat.pow_le_pow_right hK (by decide))
  apply hsum.trans
  change _ ≤ 1048576 * K ^ 6 * R
  nlinarith only [hK, h1, h2, h3, h4, h5, h6]

def bitsList (len v : Nat) : List Bool := (List.range len).map (fun pos => v.testBit pos)

def constBlock (m k : Nat) (f : Nat → Nat) : List Bool :=
  (List.range m).flatMap (fun j => bitsList k (f j))

def dataSize (k r w : Nat) : Nat := 2 * r * k + 2 * k + 2 * ((k + 1) / 2) + w

def keyInput (k r w : Nat) (schedule : Nat → Fin (2 ^ k)) (row col ta tb addr : Nat) : List Bool :=
  let h := (k + 1) / 2
  constBlock (2 * r) k (fun j => (schedule (j + 1)).val) ++
    bitsList k row ++ bitsList k col ++ bitsList h ta ++ bitsList h tb ++ bitsList w addr

lemma bitsList_length (w v : Nat) : (bitsList w v).length = w := by simp [bitsList]

lemma bitsList_at (w v p : Nat) (hp : p < w) : (bitsList w v).getD p false = v.testBit p := by
  unfold bitsList
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hp]

lemma constBlock_length (m k : Nat) (f : Nat → Nat) : (constBlock m k f).length = m * k := by
  induction m with
  | zero => simp [constBlock]
  | succ m ih =>
    rw [show constBlock (m + 1) k f = constBlock m k f ++ bitsList k (f m) by simp [constBlock, List.range_succ]]
    simp [ih, bitsList_length, Nat.succ_mul]

lemma constBlock_at (m k : Nat) (f : Nat → Nat) (j p : Nat) (hj : j < m) (hp : p < k) :
    (constBlock m k f).getD (j * k + p) false = (f j).testBit p := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [show constBlock (m + 1) k f = constBlock m k f ++ bitsList k (f m) by simp [constBlock, List.range_succ]]
    by_cases h : j < m
    · have hl : j * k + p < (constBlock m k f).length := by
        rw [constBlock_length]
        exact (Nat.add_lt_add_left hp _).trans_le (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right k (by omega))
      rw [List.getD_append _ _ _ _ hl]
      exact ih h
    · have he : j = m := by omega
      subst j
      rw [List.getD_append_right _ _ _ _ (by rw [constBlock_length]; omega), constBlock_length,
        show m * k + p - m * k = p by omega]
      exact bitsList_at k _ p hp

lemma keyInput_length (k r w : Nat) (schedule : Nat → Fin (2 ^ k)) (row col ta tb addr : Nat) :
    (keyInput k r w schedule row col ta tb addr).length = dataSize k r w := by
  simp only [keyInput, dataSize, List.length_append, constBlock_length, bitsList_length]
  omega

def readList (off len : Nat) (x : List Bool) : Nat := ofBits len (fun j => x.getD (off + j) false)

def readWord (off len : Nat) (x : Fin n → Bool) : Nat := readList off len (List.ofFn x)

lemma readWord_lt (off len : Nat) (x : Fin n → Bool) : readWord off len x < 2 ^ len := ofBits_lt _ _

lemma readWord_avail (off len : Nat) : Available (base n) (wireBits len (readWord off len)) := by
  intro i
  by_cases h : off + i.val < n
  · have he : wireBits len (readWord off len) i = fun x => x ⟨off + i.val, h⟩ := by
      funext x
      simp [wireBits, readWord, readList, ofBits_testBit, i.isLt, List.getD_eq_getElem?_getD, h]
    rw [he]
    exact Or.inl ⟨⟨off + i.val, h⟩, rfl⟩
  · have he : wireBits len (readWord off len) i = fun (_ : Fin n → Bool) => false := by
      funext x
      simp [wireBits, readWord, readList, ofBits_testBit, i.isLt, List.getD_eq_getElem?_getD, h]
    rw [he]
    exact Or.inr (Or.inl rfl)

lemma readList_block (l t : List Bool) (w v : Nat) (hv : v < 2 ^ w) :
    readList l.length w (l ++ bitsList w v ++ t) = v := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w
  · simp only [readList, ofBits_testBit, hj, ↓reduceIte]
    rw [List.append_assoc, List.getD_append_right l _ _ _ (by omega),
      show l.length + j - l.length = j by omega]
    rw [List.getD_append _ _ _ _ (by simpa only [bitsList_length] using hj)]
    exact bitsList_at w v j hj
  · have hb : v < 2 ^ j := lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega))
    simp [readList, ofBits_testBit, hj, Nat.testBit_lt_two_pow hb]

lemma readList_schedule (m k : Nat) (f : Nat → Fin (2 ^ k)) (l : List Bool) (j : Nat) (hj : j < m) :
    readList (j * k) k (constBlock m k (fun t => (f t).val) ++ l) = (f j).val := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < k
  · simp only [readList, ofBits_testBit, hp, ↓reduceIte]
    rw [List.getD_append _ _ _ _ (by
      rw [constBlock_length]
      exact (Nat.add_lt_add_left hp _).trans_le (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right k (by omega)))]
    exact constBlock_at m k _ j p hj hp
  · have hb : (f j).val < 2 ^ p := lt_of_lt_of_le (f j).isLt (Nat.pow_le_pow_right (by decide) (by omega))
    simp [readList, ofBits_testBit, hp, Nat.testBit_lt_two_pow hb]

def readSched (k r : Nat) (x : Fin n → Bool) (j : Nat) : Fin (2 ^ k) :=
  if 1 ≤ j ∧ j ≤ 2 * r then ⟨readWord ((j - 1) * k) k x, readWord_lt _ _ _⟩
  else ⟨0, Nat.two_pow_pos _⟩

def cropSched {k : Nat} (r : Nat) (schedule : Nat → Fin (2 ^ k)) (j : Nat) : Fin (2 ^ k) :=
  if 1 ≤ j ∧ j ≤ 2 * r then schedule j else ⟨0, Nat.two_pow_pos _⟩

lemma stateStep_schedule {k r : Nat} (c d : Nat → Fin (2 ^ k)) (side : Bool) (raw name : Nat)
    (h : ∀ j, 1 ≤ j → j ≤ 2 * r → c j = d j) (t : Nat) (ht : t ≤ r) :
    stateStep k r c side raw name t = stateStep k r d side raw name t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [stateStep_succ, stateStep_succ, ih (by omega)]
    unfold step
    have he := h (if side then r + (t + 1) else t + 1) (by cases side <;> simp <;> omega)
      (by cases side <;> simp <;> omega)
    rw [he]

lemma passesKey_schedule {k r : Nat} (c d : Nat → Fin (2 ^ k)) (raw row col ta tb : Nat)
    (h : ∀ j, 1 ≤ j → j ≤ 2 * r → c j = d j) :
    passesKey k r c row col ta tb raw ↔ passesKey k r d row col ta tb raw := by
  simp only [passesKey, stateStep_schedule c d false raw row h r le_rfl,
    stateStep_schedule c d true raw col h r le_rfl]

lemma sum_word {v k : Nat} (hv : v < 2 ^ k) :
    (∑ i : Fin k, (v.testBit i.val).toNat * 2 ^ i.val) = v := by
  induction k generalizing v with
  | zero => simp at hv; simp [hv]
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Nat.mul_one, Fin.val_succ, Nat.testBit_add_one, Nat.pow_succ, ← Nat.mul_assoc,
      ← Finset.sum_mul]
    have hdiv : v / 2 < 2 ^ k := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [Nat.pow_succ] using hv)
    rw [@ih (v / 2) hdiv, Nat.mul_comm (v / 2) 2]
    simpa only [Nat.toNat_testBit, Nat.pow_zero, Nat.div_one] using Nat.mod_add_div v 2

lemma decodeKey_output_lt {k r q ell S : Nat} (hkr : 7 * r + q ≤ k) (hqr : q + 2 ≤ r)
    (unrank : Nat → Nat × Nat) (sched : Nat → Fin (2 ^ k)) (row col ta tb addr : Nat) :
    (decodeKey k r q ell S unrank sched row col ta tb addr).2 < 2 ^ k := by
  unfold decodeKey
  split
  · simp only [keyTuple]
    split
    · exact recoverRaw_bound hkr hqr _ _ _ _ _ _ _ _
    · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _

lemma keyInput_read (k r w : Nat) (schedule : Nat → Fin (2 ^ k))
    (row col : Fin (2 ^ k)) (ta tb : Fin (2 ^ ((k + 1) / 2))) (addr : Fin (2 ^ w)) :
    let inp := keyInput k r w schedule row.val col.val ta.val tb.val addr.val
    let h := (k + 1) / 2
    let off := 2 * r * k
    (∀ j, 1 ≤ j → j ≤ 2 * r → readList ((j - 1) * k) k inp = (schedule j).val) ∧
    readList off k inp = row.val ∧ readList (off + k) k inp = col.val ∧
    readList (off + 2 * k) h inp = ta.val ∧ readList (off + 2 * k + h) h inp = tb.val ∧
    readList (off + 2 * k + 2 * h) w inp = addr.val := by
  let h := (k + 1) / 2
  let block := constBlock (2 * r) k (fun j => (schedule (j + 1)).val)
  let left := bitsList k row.val
  let right := bitsList k col.val
  let ltar := bitsList h ta.val
  let rtar := bitsList h tb.val
  let last := bitsList w addr.val
  let inp := keyInput k r w schedule row.val col.val ta.val tb.val addr.val
  have step (s : List Bool) (a v : Nat) (hv : v < 2 ^ a) (t : List Bool)
      (he : inp = s ++ bitsList a v ++ t) (off : Nat) (hoff : s.length = off) :
      readList off a inp = v := by rw [he, ← hoff, readList_block s t a v hv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj hjr
    have h' := readList_schedule (2 * r) k (fun i => schedule (i + 1))
      (left ++ right ++ ltar ++ rtar ++ last) (j - 1) (by omega)
    simpa only [keyInput, left, right, ltar, rtar, last, h, List.append_assoc, Nat.sub_add_cancel hj] using h'
  · exact step block k row.val row.isLt (right ++ ltar ++ rtar ++ last)
      (by simp [inp, keyInput, block, right, ltar, rtar, last, h, List.append_assoc]) _ (constBlock_length _ _ _)
  · exact step (block ++ left) k col.val col.isLt (ltar ++ rtar ++ last)
      (by simp [inp, keyInput, block, left, ltar, rtar, last, h, List.append_assoc]) _
      (by simp [block, constBlock_length, left, bitsList_length])
  · exact step (block ++ left ++ right) h ta.val ta.isLt (rtar ++ last)
      (by simp [inp, keyInput, block, left, right, ltar, rtar, last, h, List.append_assoc]) _
      (by simp only [block, List.length_append, constBlock_length, left, right, bitsList_length]; omega)
  · exact step (block ++ left ++ right ++ ltar) h tb.val tb.isLt last
      (by simp [inp, keyInput, block, left, right, ltar, rtar, last, h, List.append_assoc]) _
      (by simp only [block, List.length_append, constBlock_length, left, right, ltar, bitsList_length]; omega)
  · exact step (block ++ left ++ right ++ ltar ++ rtar) w addr.val addr.isLt []
      (by simp [inp, keyInput, block, left, right, ltar, rtar, last, h, List.append_assoc]) _
      (by simp only [block, List.length_append, constBlock_length, left, right, ltar, rtar, bitsList_length]; omega)

theorem completeDecoder (k r q ell : Nat) (hq : 0 < q) (hqr : q + 2 ≤ r)
    (hkr : 7 * r + q ≤ k) (hc : k - (k + 1) / 2 + q ≤ 6 * r)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2) :
    let w := addrWidth r q ell
    let n := dataSize k r w
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (wires : Fin k → Fin (n + C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      C.output < n + C.size ∧ C.size ≤ 1048576 * (k + 1) ^ 6 * (r + 1) ∧
      ∀ (schedule : Nat → Fin (2 ^ k)) (leftName rightName : Fin (2 ^ k)) (ta tb : Fin (2 ^ ((k + 1) / 2))),
      let input := fun (a : Fin (2 ^ w)) => keyInput k r w schedule leftName.val rightName.val ta.val tb.val a.val
      let live := fun a => C.eval (input a)
      let keyAt := fun a => ∑ i : Fin k, ((C.wires (input a)).getD (wires i).val false).toNat * 2 ^ i.val
      let passes := passesKey k r schedule leftName.val rightName.val ta.val tb.val
      (∀ a, live a = true → a.val < usedSlots r q ell (rootSlots q ell) ∧ passes (keyAt a)) ∧
      (∀ a, live a = false → keyAt a = 0) ∧
      (∀ key : Fin (2 ^ k), passes key.val → ∃! a, live a = true ∧ keyAt a = key.val) := by
  dsimp only
  let w := addrWidth r q ell
  let n := dataSize k r w
  let h := (k + 1) / 2
  let off := 2 * r * k
  let row := readWord (n := n) off k
  let col := readWord (n := n) (off + k) k
  let la := readWord (n := n) (off + 2 * k) h
  let ra := readWord (n := n) (off + 2 * k + h) h
  let addr := readWord (n := n) (off + 2 * k + 2 * h) w
  let sched := readSched (n := n) k r
  let output := fun x => decodeKey k r q ell (rootSlots q ell) (WeightedAddress.unrank q (ell - 1) 0)
    (sched x) (row x) (col x) (la x) (ra x) (addr x)
  have H : Build (base n) ({fun x => (output x).1} ∪ Set.range (wireBits k (fun x => (output x).2)))
      (decoderCost k r q ell) := by
    apply decodeWordsG hq hqr hkr hell5 hellr h5 (sched := sched)
      (row := row) (col := col) (ta := la) (tb := ra) (addr := addr)
      (readWord_avail _ _) (readWord_lt _ _) (readWord_avail _ _) (readWord_lt _ _)
      (readWord_avail _ _) (readWord_lt _ _) (readWord_avail _ _) (readWord_lt _ _)
      (readWord_avail _ _) (readWord_lt _ _)
    · intro j hj1 hj2
      simp only [sched, readSched, hj1, hj2, and_self, ↓reduceIte]
      exact readWord_avail _ _
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have G : Build (inputs n) ({fun x => (output x).1} ∪ Set.range (wireBits k (fun x => (output x).2)))
      (2 + decoderCost k r q ell) := thenG (inputG n) H
  obtain ⟨C, wires, hfan, hread, hout, hsize, hEval⟩ :=
    finishMany (live := fun x => (output x).1) (v := wireBits k (fun x => (output x).2)) G
  refine ⟨C, wires, hfan, hread, hout, hsize.trans (decoderCost_le hqr hkr hellr), ?_⟩
  intro schedule leftName rightName ta tb
  let norm := cropSched r schedule
  let U := WeightedAddress.unrank q (ell - 1) 0
  let S := rootSlots q ell
  let input := fun (a : Fin (2 ^ w)) => keyInput k r w schedule leftName.val rightName.val ta.val tb.val a.val
  let D := fun (a : Fin (2 ^ w)) => decodeKey k r q ell S U norm leftName.val rightName.val ta.val tb.val a.val
  let live := fun (a : Fin (2 ^ w)) => C.eval (input a)
  let keyAt := fun (a : Fin (2 ^ w)) => ∑ i : Fin k, ((C.wires (input a)).getD (wires i).val false).toNat * 2 ^ i.val
  have hwire (a : Fin (2 ^ w)) : live a = (D a).1 ∧ keyAt a = (D a).2 := by
    have hlen : (input a).length = n := keyInput_length _ _ _ _ _ _ _ _ _
    let env := listInput (input a) hlen
    have henv : List.ofFn env = input a := ofFn_listInput _ _
    obtain ⟨hsched, hrow, hcol, hla, hra, haddr⟩ := keyInput_read k r w schedule leftName rightName ta tb a
    have hn : sched env = norm := by
      funext j
      change readSched k r env j = cropSched r schedule j
      by_cases hj : 1 ≤ j ∧ j ≤ 2 * r
      · simp only [readSched, cropSched, hj, ↓reduceIte]
        apply Fin.ext
        change readList ((j - 1) * k) k (List.ofFn env) = (schedule j).val
        rw [henv]
        exact hsched j hj.1 hj.2
      · simp [readSched, cropSched, hj]
    have hD : output env = D a := by
      have frow : row env = leftName.val := by
        change readList off k (List.ofFn env) = _
        rw [henv]
        exact hrow
      have fcol : col env = rightName.val := by
        change readList (off + k) k (List.ofFn env) = _
        rw [henv]
        exact hcol
      have fla : la env = ta.val := by
        change readList (off + 2 * k) h (List.ofFn env) = _
        rw [henv]
        exact hla
      have fra : ra env = tb.val := by
        change readList (off + 2 * k + h) h (List.ofFn env) = _
        rw [henv]
        exact hra
      have faddr : addr env = a.val := by
        change readList (off + 2 * k + 2 * h) w (List.ofFn env) = _
        rw [henv]
        exact haddr
      dsimp only [output, D]
      rw [hn, frow, fcol, fla, fra, faddr]
    have hv := hEval env
    rw [henv] at hv
    have hf (i : Fin k) : (C.wires (input a)).getD (wires i).val false = (D a).2.testBit i.val := by
      have he := hv.2 i
      change _ = (output env).2.testBit i.val at he
      rwa [hD] at he
    refine ⟨hv.1.trans (congrArg Prod.fst hD), ?_⟩
    change (∑ i : Fin k, ((C.wires (input a)).getD (wires i).val false).toNat * 2 ^ i.val) = _
    simp only [hf]
    exact sum_word (decodeKey_output_lt hkr hqr U norm leftName.val rightName.val ta.val tb.val a.val)
  have hpass (raw : Nat) : passesKey k r norm leftName.val rightName.val ta.val tb.val raw ↔
      passesKey k r schedule leftName.val rightName.val ta.val tb.val raw :=
    passesKey_schedule norm schedule _ _ _ _ _ (by intro j h1 h2; simp [norm, cropSched, h1, h2])
  change (∀ a, live a = true → a.val < usedSlots r q ell S ∧
    passesKey k r schedule leftName.val rightName.val ta.val tb.val (keyAt a)) ∧
    (∀ a, live a = false → keyAt a = 0) ∧
    (∀ key : Fin (2 ^ k), passesKey k r schedule leftName.val rightName.val ta.val tb.val key.val →
      ∃! a, live a = true ∧ keyAt a = key.val)
  refine ⟨?_, ?_, ?_⟩
  · intro a hl
    rw [(hwire a).1] at hl
    have hh := decodeKey_live k r q ell S U norm leftName.val rightName.val ta.val tb.val a.val hl
    exact ⟨hh.1, (hwire a).2.symm ▸ (hpass (D a).2).mp hh.2⟩
  · intro a hl
    rw [(hwire a).1] at hl
    exact (hwire a).2.trans (decodeKey_dead k r q ell S U norm leftName.val rightName.val ta.val tb.val a.val hl)
  · intro key hp
    obtain ⟨a, ha, hu⟩ := decodeKey_unique hq hqr hkr hc hell5 hellr h5 U
      (fun a ha => (WeightedAddress.unrank_spec q (ell - 1) 0 a ha).1)
      (completeUnrank q (ell - 1)) norm leftName rightName ta tb key ((hpass _).mpr hp)
    refine ⟨a, ⟨(hwire a).1.trans (congrArg Prod.fst ha), (hwire a).2.trans (congrArg Prod.snd ha)⟩, ?_⟩
    intro b hb
    apply hu b
    exact Prod.ext ((hwire b).1.symm.trans hb.1) ((hwire b).2.symm.trans hb.2)

end PEqualNP.Outside.L_meta_29730_aux

theorem PEqualNP.Outside.L_meta_29730 :
∀ (k r q ell : Nat), 0 < q → q+2 ≤ r → 7*r+q ≤ k → k-(k+1)/2+q ≤ 6*r →
  5 ≤ ell → ell ≤ r → 5*ell+q ≤ 5*r+2 →
  let h := (k+1)/2
  let z := k-h
  let u := 5*r-3
  let tries := ell-1
  let rot := fun (offset x : Nat) =>
    ((x <<< (offset % k)) ||| (x >>> (k-offset % k))) % 2^k
  let mix := fun (gap value : Nat) => value ^^^ rot gap value ^^^ rot (k-gap) value
  let chi := fun (word : Nat) => (List.range k).foldl (fun acc site =>
    acc ||| ((xor (word.testBit site)
      (!(word.testBit ((site+1) % k)) && word.testBit ((site+2) % k))).toNat <<< site)) 0
  let step := fun (constants : Nat → Fin (2^k)) (col : Bool) (raw prev t : Nat) =>
    chi (mix (if col then 2 else 1) prev) ^^^ rot (if col then 3*t+1 else 2*(t-1)) raw ^^^
      (constants (if col then r+t else t)).val
  let state := fun (c : Nat → Fin (2^k)) (side : Bool) (key name : Nat) =>
    (List.range r).foldl (fun v tick => step c side key v (tick+1))
      (rot (if side then 3 else 1) key ^^^ name)
  let slots := 2^(u-q-tries) * (∑ j ∈ Finset.range (tries+1),
    Nat.choose tries j * (if j < q then 2^q else 1))
  let width := Nat.clog 2 slots
  let n := 2*r*k+2*k+2*h+width
  let bits := fun (len v : Nat) => (List.range len).map (fun pos => v.testBit pos)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (wires : Fin k → Fin (n+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      C.output < n+C.size ∧ C.size ≤ 1048576*(k+1)^6*(r+1) ∧
    ∀ (schedule : Nat → Fin (2^k)) (leftName rightName : Fin (2^k)) (ta tb : Fin (2^h)),
      let passes := fun (raw : Nat) =>
        state schedule false raw leftName.val >>> z = ta.val ∧
        state schedule true raw rightName.val >>> z = tb.val
      let input := fun (addr : Fin (2^width)) =>
        (List.range (2*r)).flatMap (fun j => bits k (schedule (j+1)).val) ++
        bits k leftName.val ++ bits k rightName.val ++ bits h ta.val ++ bits h tb.val ++ bits width addr.val
      let live := fun addressArg => C.eval (input addressArg)
      let keyAt := fun loc => ∑ i : Fin k,
        ((C.wires (input loc)).getD (wires i).val false).toNat * 2^i.val
      (∀ address : Fin (2^width), live address = true → address.val < slots ∧ passes (keyAt address)) ∧
      (∀ address : Fin (2^width), live address = false → keyAt address = 0) ∧
      (∀ key : Fin (2^k), passes key.val →
        ∃! ticket : Fin (2^width), live ticket = true ∧ keyAt ticket = key.val) := by
  intro k r q ell hq hqr hkr hc hell5 hellr h5
  dsimp only
  rw [← PEqualNP.Outside.L_meta_29730_aux.WeightedAddress.root_eq_sum q (ell - 1)]
  exact PEqualNP.Outside.L_meta_29730_aux.completeDecoder k r q ell hq hqr hkr hc hell5 hellr h5
