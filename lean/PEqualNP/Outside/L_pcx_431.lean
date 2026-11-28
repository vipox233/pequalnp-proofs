import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_431_aux

namespace Compiler

-- Scheduling and ripple adder adapted from lean/PEqualNP/Outside/L_meta_29730.lean at
-- f81300d6daabfec729ac6fe2f9070c2b5b0c8c1e. That file credits L_meta_25484.lean
-- and L_meta_25940.lean at bc21b4f27602583bf81c0d856bd76641e8a9e9d7.
namespace GateBridge

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def Legal (op : GateOp) (arity : ℕ) : Prop :=
  ((op = .and ∨ op = .or) ∧ arity = 2) ∨ (op = .not ∧ arity = 1)

variable {α : Type*}

/-- Every label in `S` is already represented by a wire. The circuit's output is not yet fixed. -/
def Scheduled (n : ℕ) (F : α → (Fin n → Bool) → Bool) (k : ℕ) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ (∀ g ∈ gs, Legal g.op g.inputs.length) ∧
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
  · simp
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
    (hop : Legal op deps.length) (hdeps : ∀ a ∈ deps, a ∈ S)
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
      change Legal op is.length
      simpa only [his] using hop
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨n + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

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
    (hop : GateBridge.Legal op deps.length)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨1,le_rfl,?_⟩
  have h := GateBridge.push HS op deps f hop (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridge.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

def an (f g : Sig n) : Sig n := fun x => f x && g x
def or (f g : Sig n) : Sig n := fun x => f x || g x
def nt (f : Sig n) : Sig n := fun x => !f x
def xo (f g : Sig n) : Sig n := fun x => xor (f x) (g x)

theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {an f g} 1 :=
  one .and [f,g] (by simp [GateBridge.Legal]) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {or f g} 1 :=
  one .or [f,g] (by simp [GateBridge.Legal]) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, or])

theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : Build A {nt f} 1 :=
  one .not [f] (by simp [GateBridge.Legal]) (by simpa using hf) _ (by simp [GateOp.eval, nt])

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

def inputs (n : Nat) : Set (Sig n) := Set.range (fun i : Fin n => fun v => v i)

def base (n : Nat) : Set (Sig n) := inputs n ∪ {fun _ => false, fun _ => true}

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
theorem wordMuxG {w : Nat} {A : Set (Sig n)} {s : Sig n} {v u : Word n w}
    (hs : s ∈ A) (hv : Available A v) (hu : Available A u) :
    Build A (Set.range (fun i => mx s (v i) (u i))) (w*4) :=
  finG _ 4 (fun i => muxG hs (hv i) (hu i))
def listInput (x : List Bool) (hx : x.length = n) : Fin n → Bool :=
  fun i => x.get (i.cast hx.symm)

theorem ofFn_listInput (x : List Bool) (hx : x.length = n) :
    List.ofFn (listInput x hx) = x := by
  subst n
  exact List.ofFn_get x

theorem listInput_getD (x : List Bool) (hx : x.length = n) (i : Fin n) :
    listInput x hx i = x.getD i.val false := by
  rw [List.getD_eq_getElem _ _ (by simpa only [hx] using i.isLt)]
  rfl
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

end Build
end Compiler

-- The Hall-deficiency argument below is adapted from
-- lean/PEqualNP/Outside/L_lib_429.lean at f81300d6daabfec729ac6fe2f9070c2b5b0c8c1e:
-- only the helper namespace and names change; the crossing application is new.
private def coverNbr {m n : ℕ} (M : Fin m → Fin n → Bool) (X : Finset (Fin m)) : Finset (Fin n) :=
  Finset.univ.filter (fun x => ∃ a ∈ X, M a x = true)

private theorem crossingKonig (m n : ℕ) (M : Fin m → Fin n → Bool) :
    ∃ (R : Finset (Fin m)) (C : Finset (Fin n)) (S : Finset (Fin m × Fin n)),
      (∀ a x, M a x = true → a ∈ R ∨ x ∈ C) ∧
      (∀ e ∈ S, M e.1 e.2 = true) ∧ Set.InjOn Prod.fst (S : Set (Fin m × Fin n)) ∧
      Set.InjOn Prod.snd (S : Set (Fin m × Fin n)) ∧ R.card + C.card ≤ S.card := by
  obtain ⟨X0, -, hX0⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin m)))
    (fun X => (X.card : ℤ) - ((coverNbr M X).card : ℤ)) Finset.univ_nonempty
  have hemp := hX0 ∅ (Finset.mem_univ _)
  have hnb0 : (coverNbr M ∅).card = 0 := by
    rw [Finset.card_eq_zero]
    ext x
    simp [coverNbr]
  simp only [Finset.card_empty, hnb0, Nat.cast_zero, sub_zero] at hemp
  set d := X0.card - (coverNbr M X0).card with hd
  let t : Fin m → Finset (Fin n ⊕ Fin d) := fun a =>
    (Finset.univ.filter (fun x => M a x = true)).disjSum Finset.univ
  have hall : ∀ s : Finset (Fin m), s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with hs | hs
    · rw [hs]
      simp
    · obtain ⟨a0, ha0⟩ := hs
      have hsub : (coverNbr M s).disjSum (Finset.univ : Finset (Fin d)) ⊆ s.biUnion t := by
        intro z hz
        rw [Finset.mem_biUnion]
        rcases z with x | z
        · rw [Finset.inl_mem_disjSum] at hz
          simp only [coverNbr, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          obtain ⟨a, ha, hax⟩ := hz
          refine ⟨a, ha, ?_⟩
          simp only [t, Finset.inl_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hax
        · refine ⟨a0, ha0, ?_⟩
          simp only [t, Finset.inr_mem_disjSum, Finset.mem_univ]
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_disjSum, Finset.card_univ, Fintype.card_fin] at h1
      have h2 := hX0 s (Finset.mem_univ _)
      omega
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hfM : ∀ a x, f a = Sum.inl x → M a x = true := by
    intro a x hax
    have h1 := hft a
    rw [hax] at h1
    simp only [t, Finset.inl_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and] at h1
    exact h1
  let S : Finset (Fin m × Fin n) := Finset.univ.filter (fun e => f e.1 = Sum.inl e.2)
  have hmemS : ∀ e, e ∈ S ↔ f e.1 = Sum.inl e.2 := by
    intro e
    simp [S]
  have hinj1 : Set.InjOn Prod.fst (S : Set (Fin m × Fin n)) := by
    intro e he e' he' heq
    rw [Finset.mem_coe, hmemS] at he he'
    have h1 : (Sum.inl e.2 : Fin n ⊕ Fin d) = Sum.inl e'.2 := by
      rw [← he, ← he', heq]
    exact Prod.ext heq (Sum.inl_injective h1)
  have hinj2 : Set.InjOn Prod.snd (S : Set (Fin m × Fin n)) := by
    intro e he e' he' heq
    rw [Finset.mem_coe, hmemS] at he he'
    have h1 : f e.1 = f e'.1 := by
      rw [he, he', heq]
    exact Prod.ext (hfinj h1) heq
  let D : Finset (Fin m) := Finset.univ.filter (fun a => ∃ z, f a = Sum.inr z)
  have hD : D.card ≤ d := by
    have h1 : D.image f ⊆ (∅ : Finset (Fin n)).disjSum (Finset.univ : Finset (Fin d)) := by
      intro w hw
      rw [Finset.mem_image] at hw
      obtain ⟨a, ha, rfl⟩ := hw
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨z, hz⟩ := ha
      rw [hz, Finset.inr_mem_disjSum]
      exact Finset.mem_univ z
    have h2 := Finset.card_le_card h1
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_disjSum, Finset.card_empty,
      Finset.card_univ, Fintype.card_fin] at h2
    omega
  have hcov : (Finset.univ : Finset (Fin m)) ⊆ D ∪ S.image Prod.fst := by
    intro a _
    rw [Finset.mem_union]
    rcases hfa : f a with x | z
    · right
      rw [Finset.mem_image]
      exact ⟨(a, x), (hmemS (a, x)).2 hfa, rfl⟩
    · left
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨z, hfa⟩
  have hcard1 := Finset.card_le_card hcov
  have hcard2 := Finset.card_union_le D (S.image Prod.fst)
  rw [Finset.card_image_of_injOn hinj1] at hcard2
  rw [Finset.card_univ, Fintype.card_fin] at hcard1
  refine ⟨Finset.univ \ X0, coverNbr M X0, S, ?_, ?_, hinj1, hinj2, ?_⟩
  · intro a x hax
    by_cases ha : a ∈ X0
    · right
      simp only [coverNbr, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha, hax⟩
    · left
      simp [ha]
  · intro e he
    exact hfM e.1 e.2 ((hmemS e).1 he)
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ X0), Finset.card_univ, Fintype.card_fin]
    have hX0le : X0.card ≤ m := by
      have h3 := Finset.card_le_card (Finset.subset_univ X0)
      rw [Finset.card_univ, Fintype.card_fin] at h3
      exact h3
    omega

variable {n : ℕ}

def Left (q : ℕ) : Finset (Bool × Fin n) := Finset.univ.filter (fun p => p.2.val < q)

@[local simp] theorem mem_Left {q : ℕ} {p : Bool × Fin n} : p ∈ Left q ↔ p.2.val < q := by
  simp [Left]

theorem Left_mono : Monotone (Left (n := n)) := by
  intro q r h p hp
  exact mem_Left.2 (lt_of_lt_of_le (mem_Left.1 hp) h)

abbrev Edge (σ τ : Equiv.Perm (Fin n)) (p q : Bool × Fin n) : Prop :=
  (p.1 = false ∧ q.1 = true ∧ (q.2 = p.2 ∨ q.2 = σ p.2 ∨ q.2 = τ p.2)) ∨
  (q.1 = false ∧ p.1 = true ∧ (p.2 = q.2 ∨ p.2 = σ q.2 ∨ p.2 = τ q.2))

theorem Edge_symm (σ τ : Equiv.Perm (Fin n)) {p q : Bool × Fin n} :
    Edge σ τ p q → Edge σ τ q p := by
  intro h
  exact h.symm

theorem crossing_cover (h : ℕ) (σ τ : Equiv.Perm (Fin n))
    (bound : ∀ (q : Fin (n+1)) (M : Finset (Fin n × Fin n)),
      (∀ e ∈ M, decide (e.1.val < q.val) ≠ decide (e.2.val < q.val) ∧
        (e.2 = σ e.1 ∨ e.2 = τ e.1)) →
      Set.InjOn Prod.fst (↑M : Set (Fin n × Fin n)) →
      Set.InjOn Prod.snd (↑M : Set (Fin n × Fin n)) → M.card ≤ h)
    (q : Fin (n+1)) :
    ∃ C : Finset (Bool × Fin n), C.card ≤ h ∧
      ∀ x ∈ Left q.val, ∀ y ∉ Left q.val, Edge σ τ x y → x ∈ C ∨ y ∈ C := by
  let M (i j : Fin n) : Bool := decide
    (decide (i.val < q.val) ≠ decide (j.val < q.val) ∧ (j = σ i ∨ j = τ i))
  obtain ⟨A, B, S, cover, matchEdge, fstInj, sndInj, cardAB⟩ := crossingKonig n n M
  have cardS := bound q S (fun e he => of_decide_eq_true (matchEdge e he)) fstInj sndInj
  let C := (A.image (Prod.mk false)) ∪ (B.image (Prod.mk true))
  have cardC : C.card ≤ h :=
    (Finset.card_union_le _ _).trans ((Nat.add_le_add Finset.card_image_le
      Finset.card_image_le).trans (cardAB.trans cardS))
  refine ⟨C, cardC, ?_⟩
  have hc : ∀ i j, decide (i.val < q.val) ≠ decide (j.val < q.val) →
      (j = i ∨ j = σ i ∨ j = τ i) → (false, i) ∈ C ∨ (true, j) ∈ C := by
    intro i j hij he
    rcases he with rfl | he
    · exact (hij rfl).elim
    · rcases cover i j (decide_eq_true ⟨hij, he⟩) with hi | hj
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi))
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))
  intro ⟨x, i⟩ hx ⟨y, j⟩ hy he
  have hi : i.val < q.val := mem_Left.1 hx
  have hj : ¬ j.val < q.val := fun hj => hy (mem_Left.2 hj)
  have hij : decide (i.val < q.val) ≠ decide (j.val < q.val) := by simp [hi, hj]
  rcases he with ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩
  · exact hc i j hij he
  · exact (hc j i (Ne.symm hij) he).symm

private def permNeighbor (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n) : Bool × Fin n :=
  if p.1 then (false, σ.symm p.2) else (true, σ p.2)

private theorem edge_mem_permNeighbors (σ τ : Equiv.Perm (Fin n)) {p q : Bool × Fin n}
    (hne : p.2 ≠ q.2) (he : Edge σ τ p q) :
    q ∈ ({permNeighbor σ p, permNeighbor τ p} : Finset (Bool × Fin n)) := by
  obtain ⟨x, i⟩ := p
  obtain ⟨y, j⟩ := q
  rcases he with ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩
  · rcases he with h | h | h
    · exact (hne h.symm).elim
    · change j = σ i at h
      simp [permNeighbor, h]
    · change j = τ i at h
      simp [permNeighbor, h]
  · rcases he with h | h | h
    · exact (hne h).elim
    · change i = σ j at h
      simp [permNeighbor, h]
    · change i = τ j at h
      simp [permNeighbor, h]

theorem edge_degree_of_ne (σ τ : Equiv.Perm (Fin n)) (p : Bool × Fin n)
    (S : Finset (Bool × Fin n)) (hne : ∀ q ∈ S, p.2 ≠ q.2) :
    (S.filter (Edge σ τ p)).card ≤ 2 := by
  have hs : S.filter (Edge σ τ p) ⊆ {permNeighbor σ p, permNeighbor τ p} := by
    intro q hq
    obtain ⟨hq, he⟩ := Finset.mem_filter.mp hq
    exact edge_mem_permNeighbors σ τ (hne q hq) he
  exact (Finset.card_le_card hs).trans (by
    simpa using Finset.card_insert_le (permNeighbor σ p) ({permNeighbor τ p} : Finset _))

theorem edge_degree_across (σ τ : Equiv.Perm (Fin n)) (p : Bool × Fin n)
    (S : Finset (Bool × Fin n)) (q : ℕ)
    (hS : ∀ v ∈ S, (p ∈ Left q) ≠ (v ∈ Left q)) :
    (S.filter (Edge σ τ p)).card ≤ 2 := by
  apply edge_degree_of_ne
  intro v hv he
  exact hS v hv (propext (by simp [he]))

namespace DegreeExchange

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

private abbrev Move (α β : Type*) := β ⊕ α

/-- `A` and `B` are the remaining vertices on each side; `k` is the number of
new vertices already introduced. Each state, including the final one, fits in
`width`. Erasure and membership enforce that each vertex is moved exactly once. -/
private inductive Plan (R : α → β → Prop) (width : ℕ) :
    Finset α → Finset β → ℕ → List (Move α β) → Prop
  | done {k} (fit : k ≤ width) : Plan R width ∅ ∅ k []
  | introduce {A B k b ms} (fit : A.card + k ≤ width) (hb : b ∈ B)
      (tail : Plan R width A (B.erase b) (k + 1) ms) :
      Plan R width A B k (.inl b :: ms)
  | retire {A B k a ms} (fit : A.card + k ≤ width) (ha : a ∈ A)
      (ready : ∀ b ∈ B, ¬R a b) (tail : Plan R width (A.erase a) B k ms) :
      Plan R width A B k (.inr a :: ms)

private theorem plan_length {R : α → β → Prop} {width A B k ms}
    (p : Plan R width A B k ms) : ms.length = A.card + B.card := by
  induction p with
  | done => simp
  | introduce _ hb _ ih =>
      rw [Finset.card_erase_of_mem hb] at ih
      have := Finset.card_pos.mpr ⟨_, hb⟩
      simp only [List.length_cons]
      omega
  | retire _ ha _ _ ih =>
      rw [Finset.card_erase_of_mem ha] at ih
      have := Finset.card_pos.mpr ⟨_, ha⟩
      simp only [List.length_cons]
      omega

variable (R : α → β → Prop) [DecidableRel R]

omit [DecidableEq α] [DecidableEq β] in
private theorem card_le_of_degrees (A : Finset α) (B : Finset β)
    (hA : ∀ a ∈ A, 2 ≤ (B.filter (R a)).card)
    (hB : ∀ b ∈ B, (A.filter (fun a => R a b)).card ≤ 2) : A.card ≤ B.card := by
  classical
  have h₁ : 2 * A.card ≤ ∑ a ∈ A, (B.filter (R a)).card := by
    simpa [Nat.mul_comm] using (Finset.sum_le_sum hA)
  have h₂ : (∑ b ∈ B, (A.filter (fun a => R a b)).card) ≤ 2 * B.card := by
    simpa [Nat.mul_comm] using (Finset.sum_le_sum hB)
  have hcount : (∑ a ∈ A, (B.filter (R a)).card) =
      ∑ b ∈ B, (A.filter (fun a => R a b)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  omega

private theorem make_plan (K : ℕ) (A : Finset α) (B : Finset β) (k : ℕ)
    (hB : ∀ b ∈ B, (A.filter (fun a => R a b)).card ≤ 2)
    (htotal : B.card + k ≤ K) (hlive : A.card + k ≤ K + 1) :
    ∃ ms, Plan R (K + 2) A B k ms := by
  have restrictOld : ∀ a, ∀ b ∈ B,
      ((A.erase a).filter (fun a' => R a' b)).card ≤ 2 := by
    intro a b hb
    refine (Finset.card_le_card ?_).trans (hB b hb)
    intro a' ha'
    rw [Finset.mem_filter] at ha' ⊢
    exact ⟨Finset.mem_of_mem_erase ha'.1, ha'.2⟩
  by_cases hsmall : A.card ≤ B.card
  · by_cases hne : B.Nonempty
    · obtain ⟨b, hb⟩ := hne
      have hcard := Finset.card_erase_of_mem hb
      have hpos := Finset.card_pos.mpr ⟨b, hb⟩
      obtain ⟨ms, p⟩ := make_plan K A (B.erase b) (k + 1)
        (fun b' hb' => hB b' (Finset.mem_of_mem_erase hb')) (by omega) (by omega)
      exact ⟨_, .introduce (by omega) hb p⟩
    · have hBe : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hAe : A = ∅ := Finset.card_eq_zero.mp (by simpa [hBe] using hsmall)
      subst A
      subst B
      simp only [Finset.card_empty, zero_add] at htotal
      exact ⟨[], .done (by omega)⟩
  · obtain ⟨a, ha, hdeg⟩ : ∃ a ∈ A, (B.filter (R a)).card ≤ 1 := by
      by_contra! h
      exact hsmall (card_le_of_degrees R A B (fun a ha => by have := h a ha; omega) hB)
    have hcardA := Finset.card_erase_of_mem ha
    have hposA := Finset.card_pos.mpr ⟨a, ha⟩
    by_cases hzero : (B.filter (R a)).card = 0
    · have he : B.filter (R a) = ∅ := Finset.card_eq_zero.mp hzero
      have ready : ∀ b ∈ B, ¬R a b := by
        intro b hb hr
        have : b ∈ B.filter (R a) := Finset.mem_filter.mpr ⟨hb, hr⟩
        simp [he] at this
      obtain ⟨ms, p⟩ := make_plan K (A.erase a) B k (restrictOld a) htotal (by omega)
      exact ⟨_, .retire (by omega) ha ready p⟩
    · obtain ⟨b, he⟩ := Finset.card_eq_one.mp
        (show (B.filter (R a)).card = 1 by omega)
      have hmem : b ∈ B.filter (R a) := by rw [he]; exact Finset.mem_singleton_self b
      have hb : b ∈ B := (Finset.mem_filter.mp hmem).1
      have hcardB := Finset.card_erase_of_mem hb
      have hposB := Finset.card_pos.mpr ⟨b, hb⟩
      have ready : ∀ b' ∈ B.erase b, ¬R a b' := by
        intro b' hb' hr
        have hm : b' ∈ B.filter (R a) := Finset.mem_filter.mpr
          ⟨Finset.mem_of_mem_erase hb', hr⟩
        rw [he, Finset.mem_singleton] at hm
        exact (Finset.ne_of_mem_erase hb') hm
      obtain ⟨ms, p⟩ := make_plan K (A.erase a) (B.erase b) (k + 1)
        (fun b' hb' => restrictOld a b' (Finset.mem_of_mem_erase hb')) (by omega) (by omega)
      exact ⟨_, .introduce (by omega) hb (.retire (by omega) ha ready p)⟩
termination_by A.card + B.card
decreasing_by all_goals omega

private theorem exchange (old : Finset α) (new : Finset β)
    (hnew : ∀ b ∈ new, (old.filter (fun a => R a b)).card ≤ 2) :
    ∃ ms, Plan R (max old.card new.card + 2) old new 0 ms ∧
      ms.length = old.card + new.card := by
  obtain ⟨ms, p⟩ := make_plan R (max old.card new.card) old new 0 hnew
    (by simp)
    (by have := le_max_left old.card new.card; omega)
  exact ⟨ms, p, plan_length p⟩

end DegreeExchange



open DegreeExchange
private structure CutSeparation {V : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → Prop) (L A B : Finset V) : Prop where
  union_eq : A ∪ B = Finset.univ
  left_subset : L ⊆ A
  right_subset : Finset.univ \ L ⊆ B
  no_edge : ∀ x ∈ A \ B, ∀ y ∈ B \ A, ¬ E x y

private structure MinimumCutSeparation {V : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → Prop) (L A B : Finset V) : Prop
    extends CutSeparation E L A B where
  min_order : ∀ X Y, CutSeparation E L X Y → (A ∩ B).card ≤ (X ∩ Y).card

private structure LeftmostCutSeparation {V : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → Prop) (L A B : Finset V) : Prop
    extends MinimumCutSeparation E L A B where
  min_left : ∀ X Y, CutSeparation E L X Y → (X ∩ Y).card = (A ∩ B).card → A.card ≤ X.card

section CutBasics
variable {V : Type*} [Fintype V] [DecidableEq V] {E : V → V → Prop}
variable {L M A B X Y : Finset V}

private theorem cutSeparation_mem (H : CutSeparation E L A B) (v : V) :
    v ∈ A ∨ v ∈ B := by
  have hv : v ∈ A ∪ B := H.union_eq ▸ Finset.mem_univ v
  exact Finset.mem_union.mp hv

private theorem cutSeparation_of_cover (C : Finset V)
    (hc : ∀ x ∈ L, ∀ y ∉ L, E x y → x ∈ C ∨ y ∈ C) :
    ∃ A B, CutSeparation E L A B ∧ A ∩ B = C := by
  refine ⟨L ∪ C, (Finset.univ \ L) ∪ C, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · ext v
    by_cases hv : v ∈ L <;> simp [hv]
  · exact Finset.subset_union_left
  · exact Finset.subset_union_left
  · intro x hx y hy he
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_sdiff.mp hx
    have hy₂ := (Finset.mem_sdiff.mp hy).2
    have hxc : x ∉ C := fun h => hx₂ (Finset.mem_union_right _ h)
    have hyc : y ∉ C := fun h => hy₂ (Finset.mem_union_right _ h)
    have hxl : x ∈ L := (Finset.mem_union.mp hx₁).resolve_right hxc
    have hyl : y ∉ L := fun h => hy₂ (Finset.mem_union_left _ h)
    exact (hc x hxl y hyl he).elim hxc hyc
  · ext v
    by_cases hv : v ∈ L <;> simp [hv]

private theorem cutSeparation_crossing_cover (H : CutSeparation E L A B) :
    ∀ x ∈ L, ∀ y ∉ L, E x y → x ∈ A ∩ B ∨ y ∈ A ∩ B := by
  intro x hx y hy he
  by_cases hxb : x ∈ B
  · exact Or.inl (Finset.mem_inter.mpr ⟨H.left_subset hx, hxb⟩)
  · have hyb := H.right_subset (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩)
    by_cases hya : y ∈ A
    · exact Or.inr (Finset.mem_inter.mpr ⟨hya, hyb⟩)
    · exact (H.no_edge x (Finset.mem_sdiff.mpr ⟨H.left_subset hx, hxb⟩) y
        (Finset.mem_sdiff.mpr ⟨hyb, hya⟩) he).elim

private theorem minimumCutSeparation_card_le_cover (H : MinimumCutSeparation E L A B)
    (C : Finset V) (hc : ∀ x ∈ L, ∀ y ∉ L, E x y → x ∈ C ∨ y ∈ C) :
    (A ∩ B).card ≤ C.card := by
  obtain ⟨S, T, HS, hC⟩ := cutSeparation_of_cover C hc
  simpa only [hC] using H.min_order S T HS

private theorem cutSeparation_meet (hlm : L ⊆ M)
    (H : CutSeparation E L A B) (K : CutSeparation E M X Y) :
    CutSeparation E L (A ∩ X) (B ∪ Y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_univ, iff_true]
    rcases cutSeparation_mem H v with ha | hb
    · rcases cutSeparation_mem K v with hx | hy
      · exact Or.inl ⟨ha, hx⟩
      · exact Or.inr (Or.inr hy)
    · exact Or.inr (Or.inl hb)
  · intro v hv
    exact Finset.mem_inter.mpr ⟨H.left_subset hv, K.left_subset (hlm hv)⟩
  · intro v hv
    exact Finset.mem_union_left _ (H.right_subset hv)
  · intro x hx y hy he
    obtain ⟨hxa, hxx⟩ := Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1
    have hxb : x ∉ B := fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ h)
    have hxy : x ∉ Y := fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_right _ h)
    have hn := (Finset.mem_sdiff.mp hy).2
    by_cases ha : y ∈ A
    · have hk : y ∉ X := fun h => hn (Finset.mem_inter.mpr ⟨ha, h⟩)
      exact K.no_edge x (Finset.mem_sdiff.mpr ⟨hxx, hxy⟩) y
        (Finset.mem_sdiff.mpr ⟨(cutSeparation_mem K y).resolve_left hk, hk⟩) he
    · exact H.no_edge x (Finset.mem_sdiff.mpr ⟨hxa, hxb⟩) y
        (Finset.mem_sdiff.mpr ⟨(cutSeparation_mem H y).resolve_left ha, ha⟩) he

private theorem cutSeparation_join (hlm : L ⊆ M)
    (H : CutSeparation E L A B) (K : CutSeparation E M X Y) :
    CutSeparation E M (A ∪ X) (B ∩ Y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_univ, iff_true]
    rcases cutSeparation_mem H v with ha | hb
    · exact Or.inl (Or.inl ha)
    · rcases cutSeparation_mem K v with hx | hy
      · exact Or.inl (Or.inr hx)
      · exact Or.inr ⟨hb, hy⟩
  · intro v hv
    exact Finset.mem_union_right _ (K.left_subset hv)
  · intro v hv
    have hv' : v ∈ Finset.univ \ L := Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, fun h => (Finset.mem_sdiff.mp hv).2 (hlm h)⟩
    exact Finset.mem_inter.mpr ⟨H.right_subset hv', K.right_subset hv⟩
  · intro x hx y hy he
    obtain ⟨hyb, hyy⟩ := Finset.mem_inter.mp (Finset.mem_sdiff.mp hy).1
    have hya : y ∉ A := fun h => (Finset.mem_sdiff.mp hy).2 (Finset.mem_union_left _ h)
    have hyx : y ∉ X := fun h => (Finset.mem_sdiff.mp hy).2 (Finset.mem_union_right _ h)
    have hn := (Finset.mem_sdiff.mp hx).2
    by_cases hb : x ∈ B
    · have hk : x ∉ Y := fun h => hn (Finset.mem_inter.mpr ⟨hb, h⟩)
      exact K.no_edge x (Finset.mem_sdiff.mpr ⟨(cutSeparation_mem K x).resolve_right hk, hk⟩) y
        (Finset.mem_sdiff.mpr ⟨hyy, hyx⟩) he
    · exact H.no_edge x (Finset.mem_sdiff.mpr ⟨(cutSeparation_mem H x).resolve_right hb, hb⟩) y
        (Finset.mem_sdiff.mpr ⟨hyb, hya⟩) he

private theorem cutSeparation_card (H : CutSeparation E L A B) :
    Fintype.card V + (A ∩ B).card = A.card + B.card := by
  simpa [H.union_eq] using Finset.card_union_add_card_inter A B

private theorem leftmostCutSeparation_exists (C : Finset V)
    (hc : ∀ x ∈ L, ∀ y ∉ L, E x y → x ∈ C ∨ y ∈ C) :
    ∃ A B, LeftmostCutSeparation E L A B ∧ (A ∩ B).card ≤ C.card := by
  classical
  obtain ⟨S, T, HS, hC⟩ := cutSeparation_of_cover C hc
  have hex : ∃ k, ∃ A B, CutSeparation E L A B ∧ (A ∩ B).card = k :=
    ⟨C.card, S, T, HS, congrArg Finset.card hC⟩
  let k := Nat.find hex
  have hmin : ∀ X Y, CutSeparation E L X Y → k ≤ (X ∩ Y).card := by
    intro X Y H
    exact Nat.find_min' hex ⟨X, Y, H, rfl⟩
  have hlim : k ≤ C.card := by simpa only [hC] using hmin S T HS
  have hex' : ∃ a, ∃ A B, CutSeparation E L A B ∧ (A ∩ B).card = k ∧ A.card = a := by
    obtain ⟨A, B, H, hk⟩ := Nat.find_spec hex
    exact ⟨A.card, A, B, H, hk, rfl⟩
  obtain ⟨A, B, H, hk, ha⟩ := Nat.find_spec hex'
  refine ⟨A, B, ⟨⟨H, ?_⟩, ?_⟩, hk ▸ hlim⟩
  · intro X Y K
    rw [hk]
    exact hmin X Y K
  · intro X Y K hXY
    rw [ha]
    exact Nat.find_min' hex' ⟨X, Y, K, hXY.trans hk, rfl⟩

-- The right-hand separation need not be leftmost. At an equal cut this proves
-- that the chosen optimum has the least first side and the greatest second side.
private theorem leftmostCutSeparation_le_of_subset (hlm : L ⊆ M)
    (H : LeftmostCutSeparation E L A B) (K : MinimumCutSeparation E M X Y) :
    A ⊆ X ∧ Y ⊆ B := by
  have hm := cutSeparation_meet hlm H.toCutSeparation K.toCutSeparation
  have hj := cutSeparation_join hlm H.toCutSeparation K.toCutSeparation
  have h₀ := cutSeparation_card H.toCutSeparation
  have h₁ := cutSeparation_card K.toCutSeparation
  have h₂ := cutSeparation_card hm
  have h₃ := cutSeparation_card hj
  have h₄ := Finset.card_union_add_card_inter A X
  have h₅ := Finset.card_union_add_card_inter B Y
  have h₆ := H.min_order _ _ hm
  have h₇ := K.min_order _ _ hj
  have horder : ((A ∩ X) ∩ (B ∪ Y)).card = (A ∩ B).card := by omega
  have ha : A ∩ X = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    (H.min_left _ _ hm horder)
  have hbcard : (B ∪ Y).card = B.card := by
    rw [horder, ha] at h₂
    omega
  have hb : B = B ∪ Y := Finset.eq_of_subset_of_card_le Finset.subset_union_left hbcard.le
  exact ⟨by rw [← ha]; exact Finset.inter_subset_right,
    by rw [hb]; exact Finset.subset_union_right⟩

private theorem nestedCutSeparations {n h : ℕ} (left : Fin (n + 1) → Finset V)
    (hleft : Monotone left)
    (hcover : ∀ q, ∃ C : Finset V, C.card ≤ h ∧
      ∀ x ∈ left q, ∀ y ∉ left q, E x y → x ∈ C ∨ y ∈ C) :
    ∃ A B : Fin (n + 1) → Finset V, Monotone A ∧ Antitone B ∧
      ∀ q, LeftmostCutSeparation E (left q) (A q) (B q) ∧ ((A q) ∩ (B q)).card ≤ h := by
  classical
  have H : ∀ q, ∃ A B, LeftmostCutSeparation E (left q) A B ∧ (A ∩ B).card ≤ h := by
    intro q
    obtain ⟨C, hC, hc⟩ := hcover q
    obtain ⟨A, B, H, hab⟩ := leftmostCutSeparation_exists C hc
    exact ⟨A, B, H, hab.trans hC⟩
  choose A B H using H
  refine ⟨A, B, ?_, ?_, H⟩
  · intro q r hqr
    exact (leftmostCutSeparation_le_of_subset (hleft hqr) (H q).1
      (H r).1.toMinimumCutSeparation).1
  · intro q r hqr
    exact (leftmostCutSeparation_le_of_subset (hleft hqr) (H q).1
      (H r).1.toMinimumCutSeparation).2

end CutBasics

private abbrev SepPath {α : Type*} (R : α → α → Prop) (a b : α) := Relation.ReflTransGen R a b

section ExchangePath
variable {V : Type*} [Fintype V] [DecidableEq V]

def Good (E : V → V → Prop) (width : ℕ) (P : Finset V × Finset V) : Prop :=
  P.1 ∪ P.2 = Finset.univ ∧
  (∀ x ∈ P.1 \ P.2, ∀ y ∈ P.2 \ P.1, ¬ E x y) ∧
  (P.1 ∩ P.2).card ≤ width

def Step (E : V → V → Prop) (width : ℕ) (P Q : Finset V × Finset V) : Prop :=
  Good E width P ∧ Good E width Q ∧
  ((∃ v ∉ P.1, Q = (insert v P.1, P.2)) ∨
    (∃ v ∈ P.1 ∩ P.2, Q = (P.1, P.2.erase v)))

variable {E : V → V → Prop}

private theorem good_mem {w A B} (H : Good E w (A,B)) (v : V) :
    v ∈ A ∨ v ∈ B :=
  Finset.mem_union.mp (H.1 ▸ Finset.mem_univ v)

omit [Fintype V] in
private theorem planFit {T U : Finset V} {z k : ℕ} {ms : List (Move V V)}
    (p : Plan E z T U k ms) : T.card + k ≤ z := by
  cases p with
  | done h => simpa using h
  | introduce h => exact h
  | retire h => exact h

private theorem runExchange {A B X Y T U : Finset V} {w z k : ℕ} {ms : List (Move V V)}
    (ha : A ⊆ X)
    (hold : B \ Y ⊆ A) (HX : Good E w (X,Y))
    (p : Plan E z T U k ms) (hT : T ⊆ B \ Y) (hU : U ⊆ X \ A)
    (hk : ((X \ A) \ U).card = k) (hw : (A ∩ Y).card + z ≤ w)
    (H : Good E w (X \ U,Y ∪ T)) :
    SepPath (Step E w) (X \ U,Y ∪ T) (X,Y) := by
  have fit : ∀ {T' U' : Finset V} {k' : ℕ}, T'.card + k' ≤ z →
      ((X \ A) \ U').card = k' →
      ((X \ U') ∩ (Y ∪ T')).card ≤ w := by
    intro T' U' k' hfit hcount
    have hsub : (X \ U') ∩ (Y ∪ T') ⊆ (A ∩ Y) ∪ (T' ∪ ((X \ A) \ U')) := by
      intro v hv
      grind
    have h₁ := Finset.card_le_card hsub
    have h₂ := Finset.card_union_le (A ∩ Y) (T' ∪ ((X \ A) \ U'))
    have h₃ := Finset.card_union_le T' ((X \ A) \ U')
    omega
  induction p with
  | done => simpa using (Relation.ReflTransGen.refl : SepPath (Step E w) (X,Y) (X,Y))
  | @introduce T U k b ms _ hbu p ih =>
      have hbxa := hU hbu
      have hbx := (Finset.mem_sdiff.mp hbxa).1
      have hbA := (Finset.mem_sdiff.mp hbxa).2
      have heq : X \ U.erase b = insert b (X \ U) := by
        ext v
        grind
      have hu' : U.erase b ⊆ X \ A := fun _ hv => hU (Finset.mem_of_mem_erase hv)
      have hc : ((X \ A) \ U.erase b).card = k + 1 := by
        have he : (X \ A) \ U.erase b = insert b ((X \ A) \ U) := by
          ext v
          grind
        rw [he, Finset.card_insert_of_notMem (by grind), hk]
      have hn : Good E w (X \ U.erase b,Y ∪ T) := by
        refine ⟨?_, ?_, fit (planFit p) hc⟩
        · ext v
          have hv := good_mem H v
          have hu := Finset.mem_univ v
          grind
        · intro x hx y hy
          have hxy := H.2.1
          have hbx' := good_mem H b
          have hx' : x ∈ (X \ U) \ (Y ∪ T) := by grind
          have hy' : y ∈ (Y ∪ T) \ (X \ U) := by grind
          exact hxy x hx' y hy'
      exact (Relation.ReflTransGen.single ⟨H, hn, Or.inl ⟨b, by grind,
        by rw [heq]⟩⟩).trans (ih hT hu' hc hn)
  | @retire T U k a ms _ hat ready p ih =>
      have hay := hT hat
      have haa : a ∈ A := hold hay
      have hex : a ∈ X \ U := by
        have hax := ha haa
        have hno : a ∉ U := fun hu => (Finset.mem_sdiff.mp (hU hu)).2 haa
        grind
      have heq : Y ∪ T.erase a = (Y ∪ T).erase a := by
        ext v
        grind
      have ht' : T.erase a ⊆ B \ Y := fun _ hv => hT (Finset.mem_of_mem_erase hv)
      have hn : Good E w (X \ U,Y ∪ T.erase a) := by
        refine ⟨?_, ?_, fit (planFit p) hk⟩
        · ext v
          have hv := good_mem H v
          have hu := Finset.mem_univ v
          grind
        · intro x hx y hy
          have hy' : y ∈ (Y ∪ T) \ (X \ U) := by grind
          by_cases hxa : x = a
          · subst x
            by_cases hyu : y ∈ U
            · exact ready y hyu
            · have hyY : y ∈ Y := by
                by_contra hyn
                have hyt : y ∈ T := by grind
                have hya := ha (hold (hT hyt))
                grind
              exact HX.2.1 a (by grind) y (by grind)
          · exact H.2.1 x (by grind) y hy'
      exact (Relation.ReflTransGen.single ⟨H, hn, Or.inr ⟨a, by grind,
        by rw [heq]⟩⟩).trans (ih ht' hU hk hn)

private theorem good_swap (hs : ∀ ⦃x y⦄, E x y → E y x) {w : ℕ} {A B : Finset V}
    (H : Good E w (A,B)) : Good E w (B,A) := by
  refine ⟨by simpa [Finset.union_comm] using H.1, ?_,
    by simpa [Finset.inter_comm] using H.2.2⟩
  exact fun x hx y hy he => H.2.1 y hy x hx (hs he)

private theorem good_freeze {h : ℕ} {A B F : Finset V}
    (hf : F ⊆ B) (H : Good E h (A,B)) : Good E (h + F.card) (A ∪ F,B) := by
  refine ⟨?_, ?_, ?_⟩
  · ext v
    have hv := good_mem H v
    have hu := Finset.mem_univ v
    grind
  · intro x hx y hy
    have hx' : x ∈ A \ B := by
      have h := (Finset.mem_sdiff.mp hx).2
      have : x ∉ F := fun hm => h (hf hm)
      grind
    exact H.2.1 x hx' y (by grind)
  · have hsub : (A ∪ F) ∩ B ⊆ (A ∩ B) ∪ F := by
      intro v hv
      grind
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right H.2.2 _))

private theorem freezePaths (hs : ∀ ⦃x y⦄, E x y → E y x) {A B F : Finset V} {w : ℕ}
    (hf : F ⊆ B) (H : Good E w (A,B)) (HF : Good E w (A ∪ F,B)) :
    SepPath (Step E w) (A,B) (A ∪ F,B) ∧
      SepPath (Step E w) (B,A ∪ F) (B,A) := by
  induction F using Finset.induction_on with
  | empty => simpa only [Finset.union_empty] using
      (⟨.refl, .refl⟩ : SepPath (Step E w) (A,B) (A,B) ∧ SepPath (Step E w) (B,A) (B,A))
  | @insert v F hv ih =>
      have hf' : F ⊆ B := fun _ ha => hf (Finset.mem_insert_of_mem ha)
      have HM : Good E w (A ∪ F,B) := by
        refine ⟨?_, ?_, (Finset.card_le_card ?_).trans HF.2.2⟩
        · ext a
          have ha := good_mem H a
          have hu := Finset.mem_univ a
          grind
        · intro x hx y hy
          have hxA : x ∈ A \ B := by
            have h := (Finset.mem_sdiff.mp hx).2
            have : x ∉ F := fun hm => h (hf' hm)
            grind
          exact H.2.1 x hxA y (by grind)
        · intro a ha
          grind
      obtain ⟨forward, backward⟩ := ih hf' HM
      have he : A ∪ insert v F = insert v (A ∪ F) := by
        ext a
        grind
      by_cases hm : v ∈ A ∪ F
      · simpa [he, Finset.insert_eq_of_mem hm] using And.intro forward backward
      · have hb := hf (Finset.mem_insert_self v F)
        have hmv : v ∈ B ∩ (A ∪ insert v F) := by grind
        have herase : (A ∪ insert v F).erase v = A ∪ F := by
          rw [he]
          exact Finset.erase_insert hm
        exact ⟨forward.tail ⟨HM, HF, Or.inl ⟨v, hm, by rw [he]⟩⟩,
          (Relation.ReflTransGen.single ⟨good_swap hs HF, good_swap hs HM,
            Or.inr ⟨v, hmv, by rw [herase]⟩⟩).trans backward⟩

private theorem exchangePath [DecidableRel E] {A B X Y : Finset V} {h : ℕ}
    (ha : A ⊆ X) (hb : Y ⊆ B)
    (hold : B \ Y ⊆ A) (hnew : X \ A ⊆ Y)
    (H : Good E h (A,B)) (HX : Good E h (X,Y))
    (deg : ∀ b ∈ X \ A, ((B \ Y).filter (fun a => E a b)).card ≤ 2) :
    SepPath (Step E (h + 2)) (A,B) (X,Y) := by
  have hOld : (A ∩ Y) ∪ (B \ Y) = A ∩ B := by
    ext v
    have h₁ : v ∈ Y → v ∈ B := fun hy => hb hy
    have h₂ : v ∈ B \ Y → v ∈ A := fun hy => hold hy
    grind
  have hNew : (A ∩ Y) ∪ (X \ A) = X ∩ Y := by
    ext v
    have h₁ : v ∈ A → v ∈ X := fun hv => ha hv
    have h₂ : v ∈ X \ A → v ∈ Y := fun hv => hnew hv
    grind
  have hord : (A ∩ Y).card + (B \ Y).card ≤ h := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (by
      intro v hv hv'
      grind)), hOld]
    exact H.2.2
  have hnrd : (A ∩ Y).card + (X \ A).card ≤ h := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (by
      intro v hv hv'
      grind)), hNew]
    exact HX.2.2
  have hbound : (A ∩ Y).card + (max (B \ Y).card (X \ A).card + 2) ≤ h + 2 := by
    omega
  obtain ⟨ms, p, _⟩ := exchange E (B \ Y) (X \ A) deg
  have hxx : X \ (X \ A) = A := by
    ext v
    have h₁ : v ∈ A → v ∈ X := fun hv => ha hv
    grind
  have hyy : Y ∪ (B \ Y) = B := by
    ext v
    have h₁ : v ∈ Y → v ∈ B := fun hv => hb hv
    grind
  have hp : SepPath (Step E (h + 2)) (X \ (X \ A), Y ∪ (B \ Y)) (X,Y) :=
    runExchange ha hold ⟨HX.1, HX.2.1, by have := HX.2.2; omega⟩ p
      (fun _ hv => hv) (fun _ hv => hv) (by simp) hbound (by
        rw [hxx, hyy]
        exact ⟨H.1, H.2.1, by have := H.2.2; omega⟩)
  simpa only [hxx, hyy] using hp

end ExchangePath

section RankPath
variable {n h : ℕ}
variable {E : (Bool × Fin n) → (Bool × Fin n) → Prop} [DecidableRel E]

private def rankLeft (q : Fin (n + 1)) : Finset (Bool × Fin n) :=
  Finset.univ.filter (fun x => x.2.val < q.val)

private theorem rankLeft_mem {q : Fin (n + 1)} {x : Bool × Fin n} :
    x ∈ rankLeft q ↔ x.2.val < q.val := by simp [rankLeft]

private theorem pathScheduleAdjacent (hs : ∀ ⦃x y⦄, E x y → E y x)
    (degree : ∀ (T : Finset (Bool × Fin n)) (b : Bool × Fin n),
      (∀ a ∈ T, a.2 ≠ b.2) → (T.filter (fun a => E a b)).card ≤ 2)
    (q : Fin n) {A B X Y : Finset (Bool × Fin n)}
    (ha : A ⊆ X) (hb : Y ⊆ B)
    (H : CutSeparation E (rankLeft q.castSucc) A B)
    (HX : CutSeparation E (rankLeft q.succ) X Y)
    (hw : (A ∩ B).card ≤ h) (hxw : (X ∩ Y).card ≤ h) :
    SepPath (Step E (h + 4)) (A,B) (X,Y) := by
  let F : Finset (Bool × Fin n) := {(false,q), (true,q)}
  have hFm (v : Bool × Fin n) : v ∈ F ↔ v.2 = q := by
    rcases v with ⟨b,r⟩
    cases b <;> simp [F]
  have hFc : F.card = 2 := by simp [F]
  have hFB : F ⊆ B := by
    intro v hv
    have he := congrArg Fin.val ((hFm v).mp hv)
    apply H.right_subset
    simp [rankLeft_mem, he]
  have hFX : F ⊆ X := by
    intro v hv
    have he := congrArg Fin.val ((hFm v).mp hv)
    apply HX.left_subset
    simp [rankLeft_mem, he]
  have hfA : A ∪ F ⊆ X := Finset.union_subset ha hFX
  have hfB : Y ∪ F ⊆ B := Finset.union_subset hb hFB
  have oldRank (v : Bool × Fin n) (hv : v ∈ B \ (Y ∪ F)) : v.2.val < q.val := by
    have hyn : v ∉ Y := fun hh => (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left _ hh)
    have hfn : v ∉ F := fun hh => (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_right _ hh)
    have hlt : v.2.val < q.val + 1 := by
      by_contra hh
      exact hyn (HX.right_subset (by simp [rankLeft_mem, hh]))
    have hne : v.2.val ≠ q.val := fun he => hfn ((hFm v).mpr (Fin.ext he))
    omega
  have newRank (v : Bool × Fin n) (hv : v ∈ X \ (A ∪ F)) : q.val < v.2.val := by
    have han : v ∉ A := fun hh => (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left _ hh)
    have hfn : v ∉ F := fun hh => (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_right _ hh)
    have hlt : ¬ v.2.val < q.val := fun hh => han (H.left_subset (rankLeft_mem.mpr hh))
    have hne : v.2.val ≠ q.val := fun he => hfn ((hFm v).mpr (Fin.ext he))
    omega
  have hold : B \ (Y ∪ F) ⊆ A ∪ F := fun v hv =>
    Finset.mem_union_left _ (H.left_subset (rankLeft_mem.mpr (oldRank v hv)))
  have hnew : X \ (A ∪ F) ⊆ Y ∪ F := by
    intro v hv
    have hh := newRank v hv
    exact Finset.mem_union_left _ (HX.right_subset (by
      simp only [Finset.mem_sdiff, Finset.mem_univ, rankLeft_mem, true_and, Fin.val_succ]
      omega))
  have H₀ : Good E h (A,B) := ⟨H.union_eq, H.no_edge, hw⟩
  have H₁ : Good E h (X,Y) := ⟨HX.union_eq, HX.no_edge, hxw⟩
  have HF₀ : Good E (h + 2) (A ∪ F,B) := by
    simpa only [hFc] using good_freeze hFB H₀
  have HF₁ : Good E (h + 2) (X,Y ∪ F) := good_swap hs (by
    simpa only [hFc] using good_freeze hFX (good_swap hs H₁))
  have widen {P : Finset (Bool × Fin n) × Finset (Bool × Fin n)} {w : ℕ}
      (HP : Good E w P) (hle : w ≤ h + 4) : Good E (h + 4) P :=
    ⟨HP.1, HP.2.1, HP.2.2.trans hle⟩
  have start := (freezePaths hs hFB (widen H₀ (by omega)) (widen HF₀ (by omega))).1
  have finish := (freezePaths hs hFX (widen (good_swap hs H₁) (by omega))
    (widen (good_swap hs HF₁) (by omega))).2
  have mid := exchangePath hfA hfB hold hnew HF₀ HF₁ (by
    intro b hb
    apply degree
    intro a ha hab
    have h₁ := oldRank a ha
    have h₂ := newRank b hb
    have he := congrArg Fin.val hab
    omega)
  exact start.trans (mid.trans finish)

/-- A rank-cut cover of width `h` gives a single-vertex schedule of width `h + 4`. -/
theorem pathSchedule (hs : ∀ ⦃x y⦄, E x y → E y x)
    (hcover : ∀ q : Fin (n + 1), ∃ C : Finset (Bool × Fin n), C.card ≤ h ∧
      ∀ x y, x.2.val < q.val → ¬ y.2.val < q.val → E x y → x ∈ C ∨ y ∈ C)
    (degree : ∀ (T : Finset (Bool × Fin n)) (b : Bool × Fin n),
      (∀ a ∈ T, a.2 ≠ b.2) → (T.filter (fun a => E a b)).card ≤ 2) :
    Relation.ReflTransGen (Step E (h + 4)) (∅,Finset.univ) (Finset.univ,∅) := by
  have hmono : Monotone (rankLeft (n := n)) := by
    intro q r hqr x hx
    exact rankLeft_mem.mpr (lt_of_lt_of_le (rankLeft_mem.mp hx) hqr)
  obtain ⟨A,B,hA,hB,hsep⟩ := nestedCutSeparations (E := E) rankLeft hmono (by
    intro q
    obtain ⟨C,hC,h⟩ := hcover q
    exact ⟨C,hC,fun x hx y hy => h x y (rankLeft_mem.mp hx)
      (fun hn => hy (rankLeft_mem.mpr hn))⟩)
  have zeroLeft : rankLeft (0 : Fin (n + 1)) = ∅ := by ext v; simp [rankLeft_mem]
  have lastLeft : rankLeft (Fin.last n) = Finset.univ := by
    ext v
    simp [rankLeft_mem, v.2.isLt]
  have Hzero := (hsep 0).1
  have Hlast := (hsep (Fin.last n)).1
  have zeroB : B 0 = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    exact Hzero.right_subset (by simp [zeroLeft])
  have lastA : A (Fin.last n) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    exact Hlast.left_subset (by simp [lastLeft])
  have zeroA : A 0 = ∅ := by
    have ht : CutSeparation E (rankLeft (0 : Fin (n + 1))) ∅ Finset.univ :=
      ⟨by simp, by simp [zeroLeft], by simp, by simp⟩
    simpa [zeroB] using Hzero.min_order _ _ ht
  have lastB : B (Fin.last n) = ∅ := by
    have ht : CutSeparation E (rankLeft (Fin.last n)) Finset.univ ∅ :=
      ⟨by simp, by simp, by simp [lastLeft], by simp⟩
    simpa [lastA] using Hlast.min_order _ _ ht
  have reach (q : Fin (n + 1)) : SepPath (Step E (h + 4)) (A 0,B 0) (A q,B q) := by
    induction q using Fin.induction with
    | zero => exact .refl
    | succ q ih =>
      have hqr : q.castSucc ≤ q.succ := by simp [Fin.le_def]
      exact ih.trans (pathScheduleAdjacent hs degree q (hA hqr) (hB hqr)
        (hsep q.castSucc).1.toCutSeparation (hsep q.succ).1.toCutSeparation
        (hsep q.castSucc).2 (hsep q.succ).2)
  simpa only [zeroA, zeroB, lastA, lastB] using reach (Fin.last n)

end RankPath


namespace CountDP

open Finset

variable {V : Type*} [DecidableEq V]

abbrev Stats := Fin 3 → ℕ

def bucket (S L : Finset V) (permit : V → Bool → Bool) (weight : Finset V → Stats)
    (s : Finset V) (t : Stats) : Finset (Finset V) :=
  S.powerset.filter (fun w => w ∩ L = s ∧
    (∀ v ∈ S, permit v (decide (v ∈ w)) = true) ∧ weight w = t)

theorem mem_bucket {S L : Finset V} {permit : V → Bool → Bool} {weight : Finset V → Stats}
    {s w : Finset V} {t : Stats} :
    w ∈ bucket S L permit weight s t ↔ w ⊆ S ∧ w ∩ L = s ∧
      (∀ v ∈ S, permit v (decide (v ∈ w)) = true) ∧ weight w = t := by
  simp [bucket]

theorem bucket_le (S L : Finset V) (permit : V → Bool → Bool) (weight : Finset V → Stats)
    (s : Finset V) (t : Stats) : (bucket S L permit weight s t).card ≤ 2 ^ S.card := by
  rw [← Finset.card_powerset]
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem bucket_empty (permit : V → Bool → Bool) (weight : Finset V → Stats)
    (s : Finset V) (t : Stats) (hs : s ⊆ ∅) :
    (bucket ∅ ∅ permit weight s t).card = if weight ∅ = t then 1 else 0 := by
  have he : s = ∅ := Finset.subset_empty.mp hs
  subst s
  by_cases ht : weight ∅ = t <;> simp [bucket, ht, Finset.filter_singleton]

private def extend (v : V) (b : Prop) [Decidable b] (w : Finset V) : Finset V :=
  if b then insert v w else w

private theorem extend_mem_other {v u : V} (h : u ≠ v) (b : Prop) [Decidable b] (w : Finset V) :
    u ∈ extend v b w ↔ u ∈ w := by
  by_cases hb : b <;> simp [extend, hb, h]

private theorem equiv_decide {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    decide P = decide Q := by
  by_cases hp : P
  · simp [hp, h.mp hp]
  · have hq : ¬ Q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

private theorem insert_bucket_image {S L s : Finset V} {v : V} (hv : v ∉ S) (hLS : L ⊆ S)
    (hs : s ⊆ insert v L) {permit : V → Bool → Bool} {weight : Finset V → Stats} {t : Stats}
    (hw : ∀ w : Finset V, weight w = weight (w.erase v))
    (hp : permit v (decide (v ∈ s)) = true) :
    (bucket S L permit weight (s.erase v) t).image (extend v (v ∈ s)) =
      bucket (insert v S) (insert v L) permit weight s t := by
  have hvL : v ∉ L := fun h => hv (hLS h)
  ext w
  rw [Finset.mem_image, mem_bucket]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨huS, huL, huP, huW⟩ := mem_bucket.mp hu
    have hvu : v ∉ u := fun h => hv (huS h)
    have hvExt : v ∈ extend v (v ∈ s) u ↔ v ∈ s := by
      by_cases h : v ∈ s <;> simp [extend, h, hvu]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p h
      by_cases he : p = v
      · simp [he]
      · exact Finset.mem_insert_of_mem (huS ((extend_mem_other he _ _).mp h))
    · ext p
      by_cases h : p = v
      · subst p
        simpa only [Finset.mem_inter, Finset.mem_insert_self, and_true] using hvExt
      · have h' : p ∈ u ∩ L ↔ p ∈ s := by rw [huL]; simp [h]
        simpa [Finset.mem_inter, h, extend_mem_other h] using h'
    · intro p h
      rcases Finset.mem_insert.mp h with h | h
      · subst p
        rw [equiv_decide hvExt]
        exact hp
      · have hne : p ≠ v := fun he => hv (he ▸ h)
        rw [equiv_decide (extend_mem_other hne _ _)]
        exact huP p h
    · rw [hw]
      have he : (extend v (v ∈ s) u).erase v = u := by
        by_cases h : v ∈ s <;> simp [extend, h, hvu]
      rw [he, huW]
  · rintro ⟨hwS, hwL, hwP, hwW⟩
    have hvw : v ∈ w ↔ v ∈ s := by
      rw [← hwL, Finset.mem_inter]; simp
    refine ⟨w.erase v, mem_bucket.mpr ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro p h
      obtain ⟨hne, hpw⟩ := Finset.mem_erase.mp h
      exact (Finset.mem_insert.mp (hwS hpw)).resolve_left hne
    · ext p
      by_cases h : p = v
      · simp [h]
      · rw [← hwL]
        simp [h]
    · intro p hpS
      have hne : p ≠ v := fun he => hv (he ▸ hpS)
      simpa [hne] using hwP p (Finset.mem_insert_of_mem hpS)
    · rwa [← hw]
    · by_cases h : v ∈ s
      · simp [extend, h, Finset.insert_erase (hvw.mpr h)]
      · simp [extend, h, Finset.erase_eq_of_notMem (fun hh => h (hvw.mp hh))]

theorem bucket_introduce {S L s : Finset V} {v : V} (hv : v ∉ S) (hLS : L ⊆ S)
    (hs : s ⊆ insert v L) (permit : V → Bool → Bool) (weight : Finset V → Stats) (t : Stats)
    (hw : ∀ w : Finset V, weight w = weight (w.erase v)) :
    (bucket (insert v S) (insert v L) permit weight s t).card =
      if permit v (decide (v ∈ s)) then (bucket S L permit weight (s.erase v) t).card else 0 := by
  by_cases hp : permit v (decide (v ∈ s)) = true
  · rw [ite_eq_left hp, ← insert_bucket_image hv hLS hs hw hp]
    apply Finset.card_image_of_injOn
    intro a ha b hb he
    have hav : v ∉ a := fun h => hv ((mem_bucket.mp ha).1 h)
    have hbv : v ∉ b := fun h => hv ((mem_bucket.mp hb).1 h)
    have hh := congrArg (fun w => w.erase v) he
    by_cases hs' : v ∈ s <;> simpa [extend, hs', hav, hbv] using hh
  · rw [ite_eq_right hp, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hm
    obtain ⟨_, hL, hP, _⟩ := mem_bucket.mp hm
    have he : v ∈ w ↔ v ∈ s := by rw [← hL, Finset.mem_inter]; simp
    exact hp (equiv_decide he ▸ hP v (Finset.mem_insert_self _ _))

theorem bucket_forget {S L s : Finset V} {v : V} (hv : v ∈ L) (hs : s ⊆ L.erase v)
    (permit : V → Bool → Bool) (weight : Finset V → Stats) (t : Stats) :
    (bucket S (L.erase v) permit weight s t).card =
      (bucket S L permit weight s t).card + (bucket S L permit weight (insert v s) t).card := by
  have hvs : v ∉ s := fun h => (Finset.notMem_erase v L) (hs h)
  have hvfilter (w : Finset V) :
      (w ∩ L.erase v = s ↔ w ∩ L = if v ∈ w then insert v s else s) := by
    have hErase : w ∩ L.erase v = (w ∩ L).erase v := by ext p; simp; tauto
    rw [hErase]
    by_cases hw : v ∈ w
    · have hi : v ∈ w ∩ L := Finset.mem_inter.mpr ⟨hw, hv⟩
      rw [ite_eq_left hw]
      constructor
      · intro h
        rw [← h, Finset.insert_erase hi]
      · intro h
        rw [h, Finset.erase_insert hvs]
    · have hi : v ∉ w ∩ L := fun h => hw (Finset.mem_inter.mp h).1
      rw [ite_eq_right hw, Finset.erase_eq_of_notMem hi]
  have hu : bucket S (L.erase v) permit weight s t =
      bucket S L permit weight s t ∪ bucket S L permit weight (insert v s) t := by
    ext w
    simp only [Finset.mem_union, mem_bucket, hvfilter]
    by_cases hw : v ∈ w
    · have hh : w ∩ L ≠ s := by
        intro he
        exact hvs (he ▸ Finset.mem_inter.mpr ⟨hw, hv⟩)
      simp [hw, hh]
    · have hh : w ∩ L ≠ insert v s := by
        intro he
        exact hw (Finset.mem_inter.mp (he ▸ Finset.mem_insert_self v s)).1
      simp [hw, hh]
  rw [hu, Finset.card_union_of_disjoint]
  refine Finset.disjoint_left.mpr ?_
  intro w h₁ h₂
  exact hvs (((mem_bucket.mp h₂).2.1.symm.trans (mem_bucket.mp h₁).2.1) ▸ Finset.mem_insert_self v s)

theorem bucket_add_weight (S L s : Finset V) (permit : V → Bool → Bool)
    (weight delta : Finset V → Stats) (t : Stats)
    (hd : ∀ w, w ∩ L = s → delta w = delta s) :
    bucket S L permit (fun w => weight w + delta w) s t =
      if ∀ k, delta s k ≤ t k then bucket S L permit weight s (fun k => t k - delta s k) else ∅ := by
  ext w
  by_cases ht : ∀ k, delta s k ≤ t k
  · simp only [ite_eq_left ht, mem_bucket]
    constructor
    · rintro ⟨hw, hl, hp, he⟩
      rw [hd w hl] at he
      refine ⟨hw, hl, hp, funext fun k => ?_⟩
      have hk := congrFun he k
      change weight w k + delta s k = t k at hk
      omega
    · rintro ⟨hw, hl, hp, he⟩
      rw [hd w hl]
      refine ⟨hw, hl, hp, funext fun k => ?_⟩
      have hk := congrFun he k
      change weight w k = t k - delta s k at hk
      change weight w k + delta s k = t k
      have := ht k
      omega
  · simp only [ite_eq_right ht, mem_bucket, Finset.notMem_empty, iff_false]
    rintro ⟨_, hl, _, he⟩
    apply ht
    intro k
    rw [hd w hl] at he
    have hk := congrFun he k
    change weight w k + delta s k = t k at hk
    omega

end CountDP

namespace CountCircuit

open Finset CountDP Compiler.Build

variable {V : Type*} [DecidableEq V] {N b m width : ℕ}

abbrev Features (V : Type*) := Fin 3 → Finset (V × V)
abbrev Test := Fin 3 → Bool → Bool → Bool
abbrev BucketIndex (b : ℕ) := Fin 3 → Fin (b+1)

abbrev coords (t : BucketIndex b) : Stats := fun k => (t k).val

def inner (edges : Features V) (S : Finset V) (k : Fin 3) : Finset (V × V) :=
  (edges k).filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)

def active (test : Test) (w : Finset V) (k : Fin 3) (e : V × V) : Bool :=
  test k (decide (e.1 ∈ w)) (decide (e.2 ∈ w))

def weight (edges : Features V) (test : Test) (S w : Finset V) : Stats :=
  fun k => ((inner edges S k).filter (fun e => active test w k e = true)).card

def delta (edges : Features V) (test : Test) (S : Finset V) (v : V) (w : Finset V) : Stats :=
  fun k => ((inner edges (insert v S) k \ inner edges S k).filter (fun e => active test w k e = true)).card

theorem weight_insert (edges : Features V) (test : Test) (S : Finset V) (v : V) :
    weight edges test (insert v S) = fun w => weight edges test S w + delta edges test S v w := by
  funext w k
  let A := (inner edges S k).filter (fun e => active test w k e = true)
  let B := (inner edges (insert v S) k).filter (fun e => active test w k e = true)
  have hAB : A ⊆ B := by
    intro e he
    simp only [A, B, inner, Finset.mem_filter] at he ⊢
    exact ⟨⟨he.1.1, Finset.mem_insert_of_mem he.1.2.1, Finset.mem_insert_of_mem he.1.2.2⟩, he.2⟩
  have h : (inner edges (insert v S) k \ inner edges S k).filter (fun e => active test w k e = true) = B \ A := by
    ext e
    simp only [A, B, Finset.mem_sdiff, Finset.mem_filter]
    tauto
  change B.card = A.card + ((inner edges (insert v S) k \ inner edges S k).filter
    (fun e => active test w k e = true)).card
  rw [h, Finset.card_sdiff_of_subset hAB, Nat.add_sub_of_le (Finset.card_le_card hAB)]

theorem weight_erase (edges : Features V) (test : Test) (S : Finset V) {v : V}
    (hv : v ∉ S) (w : Finset V) : weight edges test S w = weight edges test S (w.erase v) := by
  funext k
  unfold weight
  congr 1
  apply Finset.filter_congr
  intro e he
  have eS : e.1 ∈ S ∧ e.2 ∈ S := (Finset.mem_filter.mp he).2
  have h₁ : e.1 ≠ v := fun h => hv (h ▸ eS.1)
  have h₂ : e.2 ≠ v := fun h => hv (h ▸ eS.2)
  simp [active, h₁, h₂]

theorem delta_agree (edges : Features V) (test : Test) (S L : Finset V) (v : V)
    (hLive : ∀ k e, e ∈ inner edges (insert v S) k \ inner edges S k →
        e.1 ∈ insert v L ∧ e.2 ∈ insert v L)
    (s w : Finset V) (h : w ∩ insert v L = s) : delta edges test S v w = delta edges test S v s := by
  funext k
  unfold delta
  congr 1
  apply Finset.filter_congr
  intro e he
  have heL := hLive k e he
  simp [active, ← h, heL.1, heL.2]

def fBucket (edges : Features V) (test : Test) (permit : V → Bool → Sig N)
    (S L s : Finset V) (t : Stats) (x : Fin N → Bool) : ℕ :=
  (bucket S L (fun v a => permit v a x) (weight edges test S) s t).card

def table (edges : Features V) (test : Test) (permit : V → Bool → Sig N)
    (b m : ℕ) (S L : Finset V) : Set (Sig N) :=
  familyOut Finset.univ (fun i : L.powerset × BucketIndex b =>
    Set.range (bitsOf m (fBucket edges test permit S L i.1.val (coords i.2))))

theorem table_mem {edges : Features V} {test : Test} {permit : V → Bool → Sig N}
    {S L s : Finset V} (hs : s ⊆ L) (t : BucketIndex b) (j : Fin m) :
    bitsOf m (fBucket edges test permit S L s (coords t)) j ∈ table edges test permit b m S L := by
  let i : L.powerset × BucketIndex b := (⟨s, Finset.mem_powerset.mpr hs⟩, t)
  exact ⟨i, Finset.mem_univ i, ⟨j, rfl⟩⟩

def stepCost (b m width : ℕ) : ℕ := 2^width * (b+1)^3 * (9*m)

theorem buildTable {A : Set (Sig N)} {edges : Features V} {test : Test}
    {permit : V → Bool → Sig N} {S L : Finset V} (hL : L.card ≤ width)
    (H : ∀ i : L.powerset × BucketIndex b,
      Build A (Set.range (bitsOf m (fBucket edges test permit S L i.1.val (coords i.2)))) (9*m)) :
    Build A (table edges test permit b m S L) (stepCost b m width) := by
  apply relax (familyG _ _ H) le_rfl le_rfl
  have h : Fintype.card (L.powerset × BucketIndex b) = 2^L.card * (b+1)^3 := by
    simp [BucketIndex]
  rw [h]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hL))

theorem bitConst {A : Set (Sig N)} (c : ℕ) (hf : (fun _ => false) ∈ A)
    (ht : (fun _ => true) ∈ A) : Build A (Set.range (bitsOf m (fun _ => c))) 0 :=
  wordConstG (fun j => c.testBit j.val) hf ht

theorem bitGate {A : Set (Sig N)} {p : Sig N} {F : (Fin N → Bool) → ℕ}
    (hp : p ∈ A) (hF : Available A (bitsOf m F)) :
    Build A (Set.range (bitsOf m (fun x => if p x then F x else 0))) m := by
  apply relax (wordAndG (v := fun _ => p) (u := bitsOf m F) (fun _ => hp) hF) le_rfl ?_ le_rfl
  rintro _ ⟨j, rfl⟩
  refine ⟨j, ?_⟩
  funext x
  cases hp' : p x <;> simp [bitsOf, an, hp']

theorem buildEmpty {A : Set (Sig N)} (edges : Features V) (test : Test)
    (permit : V → Bool → Sig N) (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    Build A (table edges test permit b m ∅ ∅) 0 := by
  apply idle
  rintro f ⟨i, _, j, rfl⟩
  have h (x : Fin N → Bool) : fBucket edges test permit ∅ ∅ i.1.val (coords i.2) x =
      if weight edges test ∅ ∅ = coords i.2 then 1 else 0 :=
    bucket_empty _ _ _ _ (Finset.mem_powerset.mp i.1.property)
  by_cases hh : weight edges test ∅ ∅ = coords i.2
  · have h' : bitsOf m (fBucket edges test permit ∅ ∅ i.1.val (coords i.2)) j =
        fun _ => (1 : ℕ).testBit j.val := by funext x; simp [bitsOf, h, hh]
    rw [h']
    cases hb : (1 : ℕ).testBit j.val
    · simpa only [hb] using hf
    · simpa only [hb] using ht
  · convert hf using 1
    funext x
    simp [bitsOf, h, hh]

theorem buildIntroduce {A : Set (Sig N)} (edges : Features V) (test : Test)
    (permit : V → Bool → Sig N) (S L : Finset V) (v : V) (hLS : L ⊆ S) (hv : v ∉ S)
    (hL : (insert v L).card ≤ width)
    (hLive : ∀ k e, e ∈ inner edges (insert v S) k \ inner edges S k →
        e.1 ∈ insert v L ∧ e.2 ∈ insert v L)
    (hP : ∀ v a, permit v a ∈ A) (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    Build (A ∪ table edges test permit b m S L)
      (table edges test permit b m (insert v S) (insert v L)) (stepCost b m width) := by
  apply buildTable hL
  intro i
  let s := i.1.val
  let t := coords i.2
  have hs : s ⊆ insert v L := Finset.mem_powerset.mp i.1.property
  have hs' : s.erase v ⊆ L := by
    intro u hu
    obtain ⟨hne, hu⟩ := Finset.mem_erase.mp hu
    exact (Finset.mem_insert.mp (hs hu)).resolve_left hne
  by_cases hOK : ∀ k, delta edges test S v s k ≤ t k
  · let u : BucketIndex b := fun k => ⟨t k - delta edges test S v s k,
      (Nat.sub_le _ _).trans_lt (i.2 k).isLt⟩
    have hC : fBucket edges test permit (insert v S) (insert v L) s t = fun x =>
        if permit v (decide (v ∈ s)) x then fBucket edges test permit S L (s.erase v) (coords u) x else 0 := by
      funext x
      unfold fBucket
      rw [weight_insert, bucket_add_weight _ _ _ _ _ _ _ (fun w => delta_agree edges test S L v hLive s w), ite_eq_left hOK]
      exact bucket_introduce hv hLS hs _ _ _ (weight_erase edges test S hv)
    change Build _ (Set.range (bitsOf m (fBucket edges test permit (insert v S) (insert v L) s t))) _
    rw [hC]
    exact relax (bitGate (Or.inl (hP v _)) (fun j => Or.inr (table_mem hs' u j))) le_rfl le_rfl (by omega)
  · have hC : fBucket edges test permit (insert v S) (insert v L) s t = fun _ => 0 := by
      funext x
      unfold fBucket
      rw [weight_insert, bucket_add_weight _ _ _ _ _ _ _ (fun w => delta_agree edges test S L v hLive s w), ite_eq_right hOK, Finset.card_empty]
    change Build _ (Set.range (bitsOf m (fBucket edges test permit (insert v S) (insert v L) s t))) _
    rw [hC]
    exact relax (bitConst 0 (Or.inl hf) (Or.inl ht)) le_rfl le_rfl (Nat.zero_le _)

theorem buildForget {A : Set (Sig N)} (edges : Features V) (test : Test)
    (permit : V → Bool → Sig N) (S L : Finset V) (v : V) (hv : v ∈ L)
    (hL : (L.erase v).card ≤ width) (hf : (fun _ => false) ∈ A) :
    Build (A ∪ table edges test permit b m S L)
      (table edges test permit b m S (L.erase v)) (stepCost b m width) := by
  apply buildTable hL
  intro i
  let s := i.1.val
  let t := coords i.2
  have hs : s ⊆ L.erase v := Finset.mem_powerset.mp i.1.property
  have hs' : s ⊆ L := hs.trans (Finset.erase_subset v L)
  have hs'' : insert v s ⊆ L := Finset.insert_subset hv hs'
  have h : fBucket edges test permit S (L.erase v) s t =
      fun x => fBucket edges test permit S L s t x + fBucket edges test permit S L (insert v s) t x := by
    funext x
    exact bucket_forget hv hs _ _ _
  change Build _ (Set.range (bitsOf m (fBucket edges test permit S (L.erase v) s t))) _
  rw [h]
  exact sumTwoB m _ _ (Or.inl hf) (fun j => Or.inr (table_mem hs' i.2 j))
    (fun j => Or.inr (table_mem hs'' i.2 j))

end CountCircuit

namespace PathCount

open Finset CountDP CountCircuit Compiler.Build

variable {V : Type*} [Fintype V] [DecidableEq V] {N b m width : ℕ}

abbrev State (V : Type*) := Finset V × Finset V

abbrev clean (E : V → V → Prop) (width : ℕ) (P : State V) : Prop := Good E width P

abbrev transition (E : V → V → Prop) (width : ℕ) (P Q : State V) : Prop := Step E width P Q

private def progress (P : State V) : ℕ := P.1.card + (univ \ P.2).card

private theorem introduce_live {E : V → V → Prop} (edges : Features V)
    (hAdj : ∀ k e, e ∈ edges k → E e.1 e.2 ∧ E e.2 e.1) {P : State V}
    (hP : clean E width P) {v : V} (hv : v ∉ P.1) (hvB : v ∈ P.2) :
    ∀ k e, e ∈ inner edges (insert v P.1) k \ inner edges P.1 k →
      e.1 ∈ insert v (P.1 ∩ P.2) ∧ e.2 ∈ insert v (P.1 ∩ P.2) := by
  intro k e he
  obtain ⟨heNew, heOld⟩ := Finset.mem_sdiff.mp he
  obtain ⟨he, h₁, h₂⟩ := Finset.mem_filter.mp heNew
  have hvR := Finset.mem_sdiff.mpr ⟨hvB, hv⟩
  have hE := hAdj k e he
  have hOne : e.1 = v ∨ e.2 = v := by
    rcases Finset.mem_insert.mp h₁ with h | h
    · exact Or.inl h
    · rcases Finset.mem_insert.mp h₂ with h' | h'
      · exact Or.inr h'
      · exact (heOld (Finset.mem_filter.mpr ⟨he, h, h'⟩)).elim
  rcases hOne with h | h
  · refine ⟨Finset.mem_insert.mpr (Or.inl h), ?_⟩
    rcases Finset.mem_insert.mp h₂ with hh | hh
    · exact Finset.mem_insert.mpr (Or.inl hh)
    · refine Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hh, ?_⟩)
      by_contra hn
      exact hP.2.1 _ (Finset.mem_sdiff.mpr ⟨hh, hn⟩) _ hvR (h ▸ hE.2)
  · refine ⟨?_, Finset.mem_insert.mpr (Or.inl h)⟩
    rcases Finset.mem_insert.mp h₁ with hh | hh
    · exact Finset.mem_insert.mpr (Or.inl hh)
    · refine Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hh, ?_⟩)
      by_contra hn
      exact hP.2.1 _ (Finset.mem_sdiff.mpr ⟨hh, hn⟩) _ hvR (h ▸ hE.1)

theorem pathTable {A : Set (Sig N)} {E : V → V → Prop} (edges : Features V) (test : Test)
    (hAdj : ∀ k e, e ∈ edges k → E e.1 e.2 ∧ E e.2 e.1) (permit : V → Bool → Sig N)
    (hPermit : ∀ v a, permit v a ∈ A) (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (P : State V) (path : Relation.ReflTransGen (transition E width) (∅, univ) P) :
    Build A (table edges test permit b m P.1 (P.1 ∩ P.2)) (progress P * stepCost b m width) := by
  induction path with
  | refl =>
    simpa [progress] using (buildEmpty (b := b) (m := m) edges test permit hf ht)
  | @tail Q R _ hstep ih =>
    obtain ⟨hQ, hR, hmove⟩ := hstep
    rcases hmove with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · have hvB : v ∈ Q.2 := by
        have hu : v ∈ Q.1 ∪ Q.2 := hQ.1 ▸ Finset.mem_univ _
        exact (Finset.mem_union.mp hu).resolve_left hv
      have he : insert v (Q.1 ∩ Q.2) = insert v Q.1 ∩ Q.2 := by
        ext u
        by_cases hu : u = v <;> simp [hu, hvB]
      have hFit : (insert v (Q.1 ∩ Q.2)).card ≤ width := by rw [he]; exact hR.2.2
      have h := buildIntroduce (b := b) (m := m) edges test permit Q.1 (Q.1 ∩ Q.2) v
        Finset.inter_subset_left hv hFit (introduce_live edges hAdj hQ hv hvB) hPermit hf ht
      rw [he] at h
      have hp : progress (insert v Q.1, Q.2) = progress Q + 1 := by
        simp [progress, Finset.card_insert_of_notMem hv]; omega
      rw [hp, Nat.add_mul, Nat.one_mul]
      exact thenG ih h
    · have he : (Q.1 ∩ Q.2).erase v = Q.1 ∩ Q.2.erase v := by ext u; simp; tauto
      have hFit : ((Q.1 ∩ Q.2).erase v).card ≤ width := by rw [he]; exact hR.2.2
      have h := buildForget (b := b) (m := m) edges test permit Q.1 (Q.1 ∩ Q.2) v hv hFit hf
      rw [he] at h
      have hp : progress (Q.1, Q.2.erase v) = progress Q + 1 := by
        have hvB := (Finset.mem_inter.mp hv).2
        simp only [progress, Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_erase_of_mem hvB]
        have hp := Finset.card_pos.mpr ⟨v, hvB⟩
        have hs := Finset.card_le_card (Finset.subset_univ Q.2)
        omega
      rw [hp, Nat.add_mul, Nat.one_mul]
      exact thenG ih h

theorem rootTable {A : Set (Sig N)} {E : V → V → Prop} (edges : Features V) (test : Test)
    (hAdj : ∀ k e, e ∈ edges k → E e.1 e.2 ∧ E e.2 e.1) (permit : V → Bool → Sig N)
    (hPermit : ∀ v a, permit v a ∈ A) (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (path : Relation.ReflTransGen (transition E width) (∅, univ) (univ, ∅)) :
    Build A (table edges test permit b m univ ∅) (2 * Fintype.card V * stepCost b m width) := by
  simpa [progress, Nat.two_mul] using pathTable edges test hAdj permit hPermit hf ht _ path

end PathCount

def rankCandidates {m : ℕ} (S : Finset (Fin (2 ^ m))) (cut : ℕ)
    (pref : Fin m → Bool) : Finset (Fin (2 ^ m)) :=
  S.filter (fun w => ∀ j : Fin m, cut ≤ j.val → w.val.testBit j.val = pref j)

def rankSetBit {m : ℕ} (pref : Fin m → Bool) (j : Fin m) (b : Bool) : Fin m → Bool :=
  fun k => if k = j then b else pref k

abbrev RankState (m : ℕ) := (Fin m → Bool) × ℕ

abbrev RankState.pref {m : ℕ} (s : RankState m) : Fin m → Bool := s.1

abbrev RankState.residual {m : ℕ} (s : RankState m) : ℕ := s.2

@[local simp] private theorem RankState.pref_pair {m : ℕ} (p : Fin m → Bool) (r : ℕ) :
    RankState.pref (p, r) = p := rfl

@[local simp] private theorem RankState.residual_pair {m : ℕ} (p : Fin m → Bool) (r : ℕ) :
    RankState.residual (p, r) = r := rfl

def rankAdvance {m : ℕ} (j : Fin m) (falseCount : ℕ) (s : RankState m) : RankState m :=
  if s.residual < falseCount then
    ⟨rankSetBit s.pref j false, s.residual⟩
  else
    ⟨rankSetBit s.pref j true, s.residual - falseCount⟩

/-- `count j pref` counts words matching bits above `j`, with bit `j` false.
The stage parameter counts how many bits have already been inspected. -/
def rankStage {m : ℕ} (count : Fin m → (Fin m → Bool) → ℕ) (r : ℕ) : ℕ → RankState m
  | 0 => ⟨fun _ => false, r⟩
  | i + 1 =>
      let s := rankStage count r i
      if hi : i < m then
        let j : Fin m := ⟨m - (i + 1), by omega⟩
        rankAdvance j (count j s.pref) s
      else s

theorem rankStage_succ {m : ℕ} (count : Fin m → (Fin m → Bool) → ℕ) (r i : ℕ)
    (hi : i < m) :
    let s := rankStage count r i
    let j : Fin m := ⟨m - (i + 1), by omega⟩
    rankStage count r (i + 1) = rankAdvance j (count j s.pref) s := by
  simp only [rankStage, dite_eq_left hi]

theorem rankStage_residual_le {m : ℕ} (count : Fin m → (Fin m → Bool) → ℕ) (r i : ℕ) :
    (rankStage count r i).residual ≤ r := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    by_cases hi : i < m
    · rw [rankStage_succ count r i hi]
      unfold rankAdvance
      split
      · exact ih
      · exact (Nat.sub_le _ _).trans ih
    · simpa only [rankStage, dite_eq_right hi] using ih

def rankCount {m : ℕ} (S : Finset (Fin (2 ^ m))) (j : Fin m) (pref : Fin m → Bool) : ℕ :=
  (rankCandidates S j.val (rankSetBit pref j false)).card

private theorem rankCandidates_top {m : ℕ} (S : Finset (Fin (2 ^ m)))
    (pref : Fin m → Bool) : rankCandidates S m pref = S := by
  ext w
  simp only [rankCandidates, Finset.mem_filter, and_iff_left_iff_imp]
  intro _ j hj
  exact (Nat.not_le_of_lt j.isLt hj).elim

private theorem rankCandidates_next {m : ℕ} (S : Finset (Fin (2 ^ m)))
    (j : Fin m) (pref : Fin m → Bool) (b : Bool) :
    rankCandidates S j.val (rankSetBit pref j b) =
      (rankCandidates S (j.val + 1) pref).filter (fun w => w.val.testBit j.val = b) := by
  ext w
  simp only [rankCandidates, Finset.mem_filter]
  constructor
  · rintro ⟨hw, hp⟩
    refine ⟨⟨hw, fun k hk => ?_⟩, ?_⟩
    · have hne : k ≠ j := fun he => by subst k; omega
      simpa [rankSetBit, hne] using hp k (by omega)
    · simpa [rankSetBit] using hp j le_rfl
  · rintro ⟨⟨hw, hp⟩, hb⟩
    refine ⟨hw, fun k hk => ?_⟩
    by_cases h : k = j
    · subst k
      simpa [rankSetBit] using hb
    · have hne : k.val ≠ j.val := fun he => h (Fin.ext he)
      simpa [rankSetBit, h] using hp k (by omega)

theorem rankCount_filter {m : ℕ} (S : Finset (Fin (2 ^ m))) (j : Fin m)
    (pref : Fin m → Bool) :
    rankCount S j pref =
      ((rankCandidates S (j.val + 1) pref).filter (fun w => w.val.testBit j.val = false)).card :=
  congrArg Finset.card (rankCandidates_next S j pref false)

theorem rankCount_le {m : ℕ} (S : Finset (Fin (2 ^ m))) (j : Fin m) (pref : Fin m → Bool) :
    rankCount S j pref ≤ 2 ^ m := by
  exact (Finset.card_filter_le _ _).trans (by simpa using (Finset.card_le_univ S))

private theorem rankBefore {m : ℕ} {S : Finset (Fin (2 ^ m))}
    {j : Fin m} {pref : Fin m → Bool} {x y : Fin (2 ^ m)}
    (hx : x ∈ rankCandidates S (j.val + 1) pref)
    (hy : y ∈ rankCandidates S (j.val + 1) pref)
    (hxb : x.val.testBit j.val = false) (hyb : y.val.testBit j.val = true) : x.val < y.val := by
  apply Nat.lt_of_testBit j.val hxb hyb
  intro k hk
  by_cases hkm : k < m
  · exact ((Finset.mem_filter.mp hx).2 ⟨k,hkm⟩ hk).trans
      ((Finset.mem_filter.mp hy).2 ⟨k,hkm⟩ hk).symm
  · have hm : m ≤ k := Nat.le_of_not_gt hkm
    have hp : 2 ^ m ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hm
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le x.isLt hp),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le y.isLt hp)]

private theorem rankSplit {α : Type*} (A : Finset α) (b : α → Bool) :
    (A.filter (fun x => b x = false)).card + (A.filter (fun x => b x = true)).card = A.card := by
  convert Finset.card_filter_add_card_filter_not (s := A) (fun x => b x = false) using 2
  congr 1
  ext x
  simp only [Finset.mem_filter]
  cases b x <;> simp

private theorem rankSplitEarlier {α : Type*} (A : Finset α) (b : α → Bool)
    (p : α → Prop) [DecidablePred p] :
    ((A.filter (fun x => b x = false)).filter p).card +
      ((A.filter (fun x => b x = true)).filter p).card = (A.filter p).card := by
  simp only [Finset.filter_comm _ p A]
  exact rankSplit (A.filter p) b

private theorem rankEarlier_false {m : ℕ} {S : Finset (Fin (2 ^ m))}
    {j : Fin m} {pref : Fin m → Bool} {w : Fin (2 ^ m)}
    (hw : w ∈ rankCandidates S j.val (rankSetBit pref j false)) :
    ((rankCandidates S (j.val+1) pref).filter (fun y => y.val < w.val)).card =
      ((rankCandidates S j.val (rankSetBit pref j false)).filter (fun y => y.val < w.val)).card := by
  rw [rankCandidates_next] at hw ⊢
  obtain ⟨hw, hb⟩ := Finset.mem_filter.mp hw
  congr 1
  ext y
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hy, hlt⟩
    refine ⟨⟨hy, ?_⟩, hlt⟩
    cases h : y.val.testBit j.val
    · rfl
    · exact (Nat.not_lt_of_ge (rankBefore hw hy hb h).le hlt).elim
  · rintro ⟨⟨hy, _⟩, hlt⟩
    exact ⟨hy, hlt⟩

private theorem rankEarlier_true {m : ℕ} {S : Finset (Fin (2 ^ m))}
    {j : Fin m} {pref : Fin m → Bool} {w : Fin (2 ^ m)}
    (hw : w ∈ rankCandidates S j.val (rankSetBit pref j true)) :
    ((rankCandidates S (j.val+1) pref).filter (fun y => y.val < w.val)).card =
      (rankCandidates S j.val (rankSetBit pref j false)).card +
      ((rankCandidates S j.val (rankSetBit pref j true)).filter (fun y => y.val < w.val)).card := by
  simp only [rankCandidates_next] at hw ⊢
  obtain ⟨hw, hb⟩ := Finset.mem_filter.mp hw
  rw [← rankSplitEarlier (rankCandidates S (j.val + 1) pref)
    (fun y => y.val.testBit j.val) (fun y => y.val < w.val)]
  congr 2
  apply Finset.filter_eq_self.mpr
  intro y hy
  obtain ⟨hy, hby⟩ := Finset.mem_filter.mp hy
  exact rankBefore hy hw hby hb

/-- While the input index is valid the remaining rank is valid, and passing to
any surviving word shifts its local rank by exactly the amount subtracted. -/
theorem rankStage_invariant {m : ℕ} (S : Finset (Fin (2 ^ m)))
    (count : Fin m → (Fin m → Bool) → ℕ) (hcount : ∀ j p, count j p = rankCount S j p)
    (r : ℕ) (hr : r < S.card) (i : ℕ) (hi : i ≤ m) :
    let s := rankStage count r i
    let A := rankCandidates S (m-i) s.pref
    s.residual < A.card ∧ ∀ w ∈ A,
      (S.filter (fun y => y.val < w.val)).card + s.residual =
        (A.filter (fun y => y.val < w.val)).card + r := by
  induction i with
  | zero => simp [rankStage, rankCandidates_top, hr]
  | succ i ih =>
    have him : i < m := by omega
    obtain ⟨hbound, hshift⟩ := ih (by omega)
    let j : Fin m := ⟨m - (i + 1), by omega⟩
    have hj : m-i = j.val+1 := by dsimp [j]; omega
    simp only [hj] at hbound hshift
    let s := rankStage count r i
    change s.residual < (rankCandidates S (j.val+1) s.pref).card at hbound
    let nf := rankCount S j s.pref
    have hnf : count j s.pref = nf := hcount _ _
    simp only [rankStage_succ count r i him]
    change (rankAdvance j (count j s.pref) s).residual <
        (rankCandidates S j.val (rankAdvance j (count j s.pref) s).pref).card ∧
      ∀ w ∈ rankCandidates S j.val (rankAdvance j (count j s.pref) s).pref,
        (S.filter (fun y => y.val < w.val)).card + (rankAdvance j (count j s.pref) s).residual =
          ((rankCandidates S j.val (rankAdvance j (count j s.pref) s).pref).filter
            (fun y => y.val < w.val)).card + r
    rw [hnf]
    by_cases hb : s.residual < nf
    · simp only [rankAdvance, ite_eq_left hb]
      refine ⟨hb, fun w hw => ?_⟩
      have hp := hshift w ((Finset.mem_filter.mp ((rankCandidates_next S j s.pref false) ▸ hw)).1)
      rw [rankEarlier_false hw] at hp
      exact hp
    · simp only [rankAdvance, ite_eq_right hb, RankState.pref_pair, RankState.residual_pair]
      constructor
      · have hc := rankSplit (rankCandidates S (j.val+1) s.pref) (fun y => y.val.testBit j.val)
        rw [← rankCandidates_next, ← rankCandidates_next] at hc
        change nf + _ = _ at hc
        omega
      · intro w hw
        have hp := hshift w ((Finset.mem_filter.mp ((rankCandidates_next S j s.pref true) ▸ hw)).1)
        rw [rankEarlier_true hw] at hp
        change _ + s.residual = (nf + _) + r at hp
        omega

private theorem rankCandidates_zero_unique {m : ℕ} {S : Finset (Fin (2 ^ m))}
    {pref : Fin m → Bool} {x y : Fin (2 ^ m)}
    (hx : x ∈ rankCandidates S 0 pref) (hy : y ∈ rankCandidates S 0 pref) : x = y := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hkm : k < m
  · exact ((Finset.mem_filter.mp hx).2 ⟨k,hkm⟩ (Nat.zero_le _)).trans
      ((Finset.mem_filter.mp hy).2 ⟨k,hkm⟩ (Nat.zero_le _)).symm
  · have hm : m ≤ k := Nat.le_of_not_gt hkm
    have hp : 2 ^ m ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hm
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le x.isLt hp),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le y.isLt hp)]

/-- All final bits agree with the word of zero-based rank `r` in ascending order. -/
theorem rankStage_select {m : ℕ} (S : Finset (Fin (2 ^ m)))
    (count : Fin m → (Fin m → Bool) → ℕ) (hcount : ∀ j p, count j p = rankCount S j p)
    (r : ℕ) (hr : r < S.card) :
    ∃ w ∈ S, (∀ j : Fin m, w.val.testBit j.val = (rankStage count r m).pref j) ∧
      (S.filter (fun y => y.val < w.val)).card = r := by
  obtain ⟨hbound, hshift⟩ := rankStage_invariant S count hcount r hr m le_rfl
  simp only [Nat.sub_self] at hbound hshift
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt hbound)
  have hsingleton : rankCandidates S 0 (rankStage count r m).pref = {w} := by
    ext y
    simp only [Finset.mem_singleton]
    exact ⟨fun hy => rankCandidates_zero_unique hy hw, fun h => h ▸ hw⟩
  have hz := hshift w hw
  rw [hsingleton] at hbound hz
  simp only [Finset.card_singleton] at hbound
  rw [Finset.filter_singleton, ite_eq_right (Nat.lt_irrefl _), Finset.card_empty, zero_add] at hz
  have hwr := Finset.mem_filter.mp hw
  exact ⟨w, hwr.1, fun j => hwr.2 j (Nat.zero_le _), by omega⟩

theorem rankValue_bits {m x : ℕ} (hx : x < 2 ^ m) :
    (∑ j : Fin m, (x.testBit j.val).toNat * 2 ^ j.val) = x := by
  induction m generalizing x with
  | zero => simpa using (show x = 0 by simpa using hx).symm
  | succ m ih =>
    have hdiv : x / 2 < 2 ^ m :=
      (Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa only [pow_succ] using hx)
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, pow_zero, mul_one, Nat.testBit_add_one, pow_succ]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    rw [ih hdiv, Nat.toNat_testBit]
    simp only [pow_zero, Nat.div_one]
    omega

/-- Masking final bits by the validity flag yields zero for invalid indices. -/
theorem rankStage_word {m : ℕ} (S : Finset (Fin (2 ^ m)))
    (count : Fin m → (Fin m → Bool) → ℕ) (hcount : ∀ j p, count j p = rankCount S j p)
    (r : ℕ) :
    let picked := ∑ j : Fin m, (decide (r < S.card) && (rankStage count r m).pref j).toNat * 2 ^ j.val
    if r < S.card then
      ∃ w ∈ S, w.val = picked ∧ (S.filter (fun y => y.val < w.val)).card = r
    else picked = 0 := by
  by_cases hr : r < S.card
  · obtain ⟨w, hw, hbits, hrank⟩ := rankStage_select S count hcount r hr
    simp only [hr, ite_true, decide_true, Bool.true_and]
    refine ⟨w, hw, ?_, hrank⟩
    simp_rw [← hbits]
    exact (rankValue_bits w.isLt).symm
  · simp [hr]

namespace WireArithmetic

open Compiler.Build

private theorem bit_twice_add_one_zero (a : ℕ) : (2 * a + 1).testBit 0 = true := by
  rw [show 2 * a + 1 = 2 ^ 1 * a + 1 by rfl]
  rw [Nat.testBit_two_pow_mul_add a (b := 1) (i := 1) (by decide)]
  rfl

private theorem bit_twice_add_one_succ (a j : ℕ) :
    (2 * a + 1).testBit (j + 1) = a.testBit j := by
  rw [show 2 * a + 1 = 2 ^ 1 * a + 1 by rfl]
  rw [Nat.testBit_two_pow_mul_add a (b := 1) (i := 1) (by decide)]
  simp

private theorem bit_twice_succ (a j : ℕ) : (2 * a).testBit (j + 1) = a.testBit j := by
  rw [show 2 * a = 2 ^ 1 * a + 0 by rfl]
  rw [Nat.testBit_two_pow_mul_add a (b := 0) (i := 1) (by decide)]
  simp

/-- The low `w` bits of the two's-complement sum, and its underflow flag. -/
theorem subSumB {N w : ℕ} {A : Set (Sig N)} (F T : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hF : Available A (bitsOf w F)) (hT : Available A (bitsOf w T))
    (hFb : ∀ x, F x < 2 ^ w) (hTb : ∀ x, T x < 2 ^ w) :
    Build A (Set.range (bitsOf w (fun x => F x + (2 ^ w - (T x + 1)) + 1)) ∪
      {fun x => decide (F x < T x)}) (10 * w + 10) := by
  let C : (Fin N → Bool) → ℕ := fun x => 2 ^ w - (T x + 1)
  have hC (x) : T x + C x + 1 = 2 ^ w := by
    have := hTb x
    dsimp [C]
    omega
  have hCb (x) : C x < 2 ^ w := by have := hC x; omega
  have hcbit (j : Fin w) : bitsOf w C j = nt (bitsOf w T j) := by
    funext x
    simpa [bitsOf, C, nt, j.isLt] using Nat.testBit_two_pow_sub_succ (hTb x) j.val
  have Hc : Build A (Set.range (bitsOf w C)) w := by
    rw [show bitsOf w C = _ from funext hcbit]
    exact wordNotG hT
  let B := A ∪ Set.range (bitsOf w C)
  -- The two forced low 1 bits inject the initial carry, without a second ripple pass.
  let U : (Fin N → Bool) → ℕ := fun x => 2 * F x + 1
  let V : (Fin N → Bool) → ℕ := fun x => 2 * C x + 1
  have liftBits {G : (Fin N → Bool) → ℕ} (hG : Available B (bitsOf w G)) :
      Available B (bitsOf (w + 1) (fun x => 2 * G x + 1)) := by
    intro j
    by_cases hj : j.val = 0
    · have he : bitsOf (w + 1) (fun x => 2 * G x + 1) j = fun _ => true := by
        funext x
        change (2 * G x + 1).testBit j.val = true
        rw [hj, bit_twice_add_one_zero]
      rw [he]
      exact Or.inl htrue
    · let i : Fin w := ⟨j.val - 1, by omega⟩
      have hi : j.val = i.val + 1 := by dsimp [i]; omega
      have he : bitsOf (w + 1) (fun x => 2 * G x + 1) j = bitsOf w G i := by
        funext x
        change (2 * G x + 1).testBit j.val = (G x).testBit i.val
        rw [hi, bit_twice_add_one_succ]
      rw [he]
      exact hG i
  have Hsum := rippleB U V (A := B) (Or.inl hfalse) (w + 1)
    (liftBits (fun j => Or.inl (hF j))) (liftBits (fun j => Or.inr ⟨j, rfl⟩))
  let Carry : Sig N := fun x => rippleCarry (U x) (V x) (w + 1)
  have hflag : nt Carry = fun x => decide (F x < T x) := by
    funext x
    have hu : U x < 2 ^ (w + 1) := by
      have := hFb x
      rw [Nat.pow_succ]
      dsimp [U]
      omega
    have hv : V x < 2 ^ (w + 1) := by
      have := hCb x
      rw [Nat.pow_succ]
      dsimp [V]
      omega
    have he : 2 ^ (w + 1) ≤ U x + V x ↔ T x ≤ F x := by
      rw [Nat.pow_succ]
      have := hC x
      dsimp [U, V]
      omega
    simp only [nt, Carry, (rippleCarry_spec (U x) (V x) (w + 1)).1,
      Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv, he]
    by_cases h : T x ≤ F x
    · simp [h, Nat.not_lt_of_ge h]
    · simp [h, Nat.lt_of_not_ge h]
  have Hnot := notG
    (A := A ∪ (Set.range (bitsOf w C) ∪
      (Set.range (bitsOf (w + 1) (fun x => U x + V x)) ∪ {Carry})))
    (f := Carry) (Or.inr (Or.inr (Or.inr rfl)))
  refine relax (seq (seq Hc Hsum) Hnot) le_rfl ?_ (by omega)
  intro f hf
  rcases hf with ⟨j, rfl⟩ | rfl
  · let i : Fin (w + 1) := ⟨j.val + 1, by omega⟩
    have he : bitsOf w (fun x => F x + C x + 1) j =
        bitsOf (w + 1) (fun x => U x + V x) i := by
      funext x
      change (F x + C x + 1).testBit j.val = (U x + V x).testBit (j.val + 1)
      rw [show U x + V x = 2 * (F x + C x + 1) by dsimp [U, V]; omega, bit_twice_succ]
    change bitsOf w (fun x => F x + C x + 1) j ∈ _
    rw [he]
    exact Or.inl (Or.inr (Or.inl ⟨i, rfl⟩))
  · rw [← hflag]
    exact Or.inr rfl

/-- An unsigned comparison on two available `w`-bit words. -/
theorem wordLtB {N w : ℕ} {A : Set (Sig N)} (F T : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hF : Available A (bitsOf w F)) (hT : Available A (bitsOf w T))
    (hFb : ∀ x, F x < 2 ^ w) (hTb : ∀ x, T x < 2 ^ w) :
    Build A {fun x => decide (F x < T x)} (10 * w + 10) :=
  relax (subSumB F T hfalse htrue hF hT hFb hTb) le_rfl Set.subset_union_right le_rfl

/-- Subtract when there is no underflow; otherwise retain the first operand. -/
theorem guardedSubB {N w : ℕ} {A : Set (Sig N)} (F T : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hF : Available A (bitsOf w F)) (hT : Available A (bitsOf w T))
    (hFb : ∀ x, F x < 2 ^ w) (hTb : ∀ x, T x < 2 ^ w) :
    Build A (Set.range (bitsOf w (fun x => if T x ≤ F x then F x - T x else F x)) ∪
      {fun x => decide (F x < T x)}) (14 * w + 10) := by
  let D := bitsOf w (fun x => F x + (2 ^ w - (T x + 1)) + 1)
  let L : Sig N := fun x => decide (F x < T x)
  have H := subSumB F T hfalse htrue hF hT hFb hTb
  have Hmux := wordMuxG (A := A ∪ (Set.range D ∪ {L})) (s := L) (v := D) (u := bitsOf w F)
    (Or.inr (Or.inr rfl)) (fun j => Or.inr (Or.inl ⟨j, rfl⟩)) (fun j => Or.inl (hF j))
  refine relax (seq H Hmux) le_rfl ?_ (by omega)
  intro f hf
  rcases hf with ⟨j, rfl⟩ | rfl
  · refine Or.inr ⟨j, ?_⟩
    funext x
    by_cases h : T x ≤ F x
    · have ht := hTb x
      have he : F x + (2 ^ w - (T x + 1)) + 1 = 2 ^ w + (F x - T x) := by omega
      simp [mx, D, L, bitsOf, h, Nat.not_lt_of_ge h, he, Nat.testBit_two_pow_add_gt j.isLt]
    · simp [mx, D, L, bitsOf, h, Nat.lt_of_not_ge h]
  · exact Or.inl (Or.inr rfl)

end WireArithmetic

open Compiler.Build

/-- Compile the high bits selected by the rank recurrence; the base wires remain available. -/
theorem rankCircuitB {N m w K : ℕ} {A : Set (Sig N)}
    (r : (Fin N → Bool) → ℕ) (count : (Fin N → Bool) → Fin m → (Fin m → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hr : Available A (bitsOf w r)) (hrb : ∀ x, r x < 2 ^ w)
    (hcount : ∀ x j p, count x j p < 2 ^ w)
    (oracle : ∀ (A' : Set (Sig N)) (j : Fin m) (p : Fin m → Sig N),
      A ⊆ A' → Available A' p →
      Build A' (Set.range (bitsOf w (fun x => count x j (fun k => p k x)))) K) :
    Build A (Set.range (fun (k : Fin m) x => (rankStage (count x) (r x) m).pref k))
      (m * (K + (14 * w + 10) + 1)) := by
  let P (i : ℕ) (k : Fin m) : Sig N := fun x => (rankStage (count x) (r x) i).pref k
  let R (i : ℕ) (x : Fin N → Bool) := (rankStage (count x) (r x) i).residual
  let O (i : ℕ) := Set.range (P i) ∪ Set.range (bitsOf w (R i))
  have stages (i : ℕ) (hi : i ≤ m) : Build A (O i) (i * (K + (14 * w + 10) + 1)) := by
    induction i with
    | zero =>
      rw [Nat.zero_mul]
      apply idle
      rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
      · exact hfalse
      · exact hr k
    | succ i ih =>
      have him : i < m := by omega
      let j : Fin m := ⟨m - (i + 1), by omega⟩
      let B := A ∪ O i
      let T (x : Fin N → Bool) := count x j (fun k => P i k x)
      let C := Set.range (bitsOf w T)
      let D := B ∪ C
      let F : Sig N := fun x => decide (R i x < T x)
      let U (x : Fin N → Bool) := if T x ≤ R i x then R i x - T x else R i x
      let E := Set.range (bitsOf w U) ∪ {F}
      have hc : Build B C K := oracle B j (P i) Set.subset_union_left
        (fun k => Or.inr (Or.inl ⟨k, rfl⟩))
      have hs : Build D E (14 * w + 10) :=
        WireArithmetic.guardedSubB (R i) T (Or.inl (Or.inl hfalse)) (Or.inl (Or.inl htrue))
          (fun k => Or.inl (Or.inr (Or.inr ⟨k, rfl⟩))) (fun k => Or.inr ⟨k, rfl⟩)
          (fun x => (rankStage_residual_le (count x) (r x) i).trans_lt (hrb x))
          (fun x => hcount x j _)
      have hn : Build (B ∪ (C ∪ E)) {nt F} 1 := notG (Or.inr (Or.inr (Or.inr rfl)))
      have hp (k : Fin m) : P (i + 1) k = if k = j then nt F else P i k := by
        funext x
        change (rankStage (count x) (r x) (i + 1)).pref k = _
        rw [rankStage_succ _ _ _ him]
        by_cases hl : R i x < T x <;> by_cases hk : k = j <;>
          simp [rankAdvance, rankSetBit, j, P, R, T, nt, F, hl, hk] at *
      have hu : R (i + 1) = U := by
        funext x
        change (rankStage (count x) (r x) (i + 1)).residual = _
        rw [rankStage_succ _ _ _ him]
        by_cases hl : R i x < T x
        · simp [rankAdvance, j, P, R, T, U, hl, Nat.not_le_of_lt hl] at *
        · simp [rankAdvance, j, P, R, T, U, hl, Nat.le_of_not_gt hl] at *
      refine relax (seq (ih (by omega)) (seq (seq hc hs) hn)) le_rfl ?_ ?_
      · rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
        · rw [hp]
          split
          · exact Or.inr (Or.inr rfl)
          · exact Or.inl (Or.inl ⟨k, rfl⟩)
        · rw [hu]
          exact Or.inr (Or.inl (Or.inr (Or.inl ⟨k, rfl⟩)))
      · simp only [Nat.add_mul, Nat.one_mul, Nat.add_assoc, le_refl]
  exact relax (stages m le_rfl) le_rfl Set.subset_union_left le_rfl

namespace CellModel

open Finset CountDP CountCircuit

variable {n : ℕ}

abbrev V (n : ℕ) := Bool × Fin n
abbrev W (n : ℕ) := Fin (2^(2*n))

private def finPair : V n ≃ Fin n × Fin 2 where
  toFun p := (p.2, finTwoEquiv.symm p.1)
  invFun p := (finTwoEquiv p.2, p.1)
  left_inv := by intro p; simp
  right_inv := by intro p; simp

def pos : V n ≃ Fin (2*n) :=
  finPair.trans (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)))

theorem pos_val (p : V n) : (pos p).val = 2*p.2.val+p.1.toNat := by
  cases p with
  | mk b i => cases b <;> simp [pos, finPair, finProdFinEquiv, finTwoEquiv, Nat.add_comm]

def bit (w : W n) (p : V n) : Bool := w.val.testBit (2*p.2.val+p.1.toNat)

def spins (w : W n) : Finset (V n) := Finset.univ.filter (fun p => bit w p = true)

theorem spins_bit (w : W n) (p : V n) : decide (p ∈ spins w) = bit w p := by simp [spins]

theorem spins_bijective : Function.Bijective (spins (n := n)) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨?_, by simp [Fintype.card_finset]⟩
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 2*n
  · let p := (pos (n := n)).symm ⟨j, hj⟩
    have hpos : (pos p).val = j := congrArg Fin.val (pos.apply_symm_apply ⟨j, hj⟩)
    have ha := spins_bit a p
    rw [h, spins_bit, bit, bit, ← pos_val, hpos] at ha
    exact ha.symm
  · have hpow : 2^(2*n) ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (a.isLt.trans_le hpow), Nat.testBit_eq_false_of_lt (b.isLt.trans_le hpow)]

def turn (σ τ : Equiv.Perm (Fin n)) (k : Fin 3) : Equiv.Perm (Fin n) := ![1, σ, τ] k

def link (σ τ : Equiv.Perm (Fin n)) (k : Fin 3) : Fin n ↪ (V n × V n) :=
  ⟨fun i => ((false,i),(true, turn σ τ k i)), fun _ _ h => congrArg (fun e => e.1.2) h⟩

def features (σ τ : Equiv.Perm (Fin n)) : Features (V n) :=
  fun k => Finset.univ.map (link σ τ k)

def test : Test := fun k a b => if k.val = 2 then decide (a = b) else decide (a ≠ b)

theorem edge_features (σ τ : Equiv.Perm (Fin n)) (k : Fin 3) (e : V n × V n)
    (he : e ∈ features σ τ k) : Edge σ τ e.1 e.2 ∧ Edge σ τ e.2 e.1 := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp he
  have h : Edge σ τ (link σ τ k i).1 (link σ τ k i).2 := by
    fin_cases k <;> simp [Edge, link, turn]
  exact ⟨h, Edge_symm σ τ h⟩

def cell (σ τ : Equiv.Perm (Fin n)) (permits : V n → Bool → Bool) (t : BucketIndex n) : Finset (W n) :=
  (Finset.univ : Finset (W n)).filter (fun w =>
    (∀ p : V n, permits p (bit w p) = true) ∧
    (Finset.univ.filter (fun i : Fin n => bit w (false,i) ≠ bit w (true,i))).card = (t 0).val ∧
    (Finset.univ.filter (fun i : Fin n => bit w (false,i) ≠ bit w (true,σ i))).card = (t 1).val ∧
    (Finset.univ.filter (fun i : Fin n => bit w (false,i) = bit w (true,τ i))).card = (t 2).val)

private theorem weight_univ (σ τ : Equiv.Perm (Fin n)) (w : W n) (k : Fin 3) :
    weight (features σ τ) test univ (spins w) k =
      (Finset.univ.filter (fun i : Fin n => test k (bit w (false,i)) (bit w (true,turn σ τ k i)) = true)).card := by
  simp [weight, CountCircuit.inner, features, Finset.filter_map, active, link, spins_bit]
  rfl

theorem mem_cell (σ τ : Equiv.Perm (Fin n)) (permits : V n → Bool → Bool) (t : BucketIndex n) (w : W n) :
    w ∈ cell σ τ permits t ↔ (∀ p : V n, permits p (bit w p) = true) ∧
      weight (features σ τ) test univ (spins w) = coords t := by
  have h₀ : weight (features σ τ) test univ (spins w) 0 =
      (Finset.univ.filter (fun i : Fin n => bit w (false,i) ≠ bit w (true,i))).card := by
    rw [weight_univ]
    congr 1
  have h₁ : weight (features σ τ) test univ (spins w) 1 =
      (Finset.univ.filter (fun i : Fin n => bit w (false,i) ≠ bit w (true,σ i))).card := by
    rw [weight_univ]
    congr 1
  have h₂ : weight (features σ τ) test univ (spins w) 2 =
      (Finset.univ.filter (fun i : Fin n => bit w (false,i) = bit w (true,τ i))).card := by
    rw [weight_univ]
    congr 1
  have he (f g : Stats) : f = g ↔ f 0 = g 0 ∧ f 1 = g 1 ∧ f 2 = g 2 := by
    constructor
    · rintro rfl; exact ⟨rfl,rfl,rfl⟩
    · rintro ⟨h₀,h₁,h₂⟩
      funext k
      fin_cases k <;> assumption
  rw [he, h₀, h₁, h₂]
  simp [cell]

theorem cell_count (σ τ : Equiv.Perm (Fin n)) (permits : V n → Bool → Bool) (t : BucketIndex n) :
    (bucket univ ∅ permits (weight (features σ τ) test univ) ∅ (coords t)).card =
      (cell σ τ permits t).card := by
  let f : W n ↪ Finset (V n) := ⟨spins, spins_bijective.1⟩
  have he : (cell σ τ permits t).map f = bucket univ ∅ permits (weight (features σ τ) test univ) ∅ (coords t) := by
    ext s
    obtain ⟨w, rfl⟩ := spins_bijective.2 s
    change f w ∈ (cell σ τ permits t).map f ↔ _
    rw [Finset.mem_map', mem_cell, mem_bucket]
    simp [spins_bit]
  rw [← he, Finset.card_map]

theorem cell_bound (σ τ : Equiv.Perm (Fin n)) (permits : V n → Bool → Bool) (t : BucketIndex n) :
    (cell σ τ permits t).card < 2^(2*n+1) := by
  have h := Finset.card_le_card (Finset.subset_univ (cell σ τ permits t))
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [pow_succ]
  have hp := Nat.two_pow_pos (2*n)
  omega

def compat (j : Fin (2*n)) (pref : Fin (2*n) → Bool) (p : V n) (a : Bool) : Bool :=
  if j.val ≤ (pos p).val then decide (a = rankSetBit pref j false (pos p)) else true

def restrictPermit (permits : V n → Bool → Bool) (j : Fin (2*n)) (pref : Fin (2*n) → Bool) : V n → Bool → Bool :=
  fun p a => permits p a && compat j pref p a

theorem restricted_cell (σ τ : Equiv.Perm (Fin n)) (permits : V n → Bool → Bool) (t : BucketIndex n)
    (j : Fin (2*n)) (pref : Fin (2*n) → Bool) :
    (cell σ τ (restrictPermit permits j pref) t).card = rankCount (cell σ τ permits t) j pref := by
  unfold rankCount
  congr 1
  ext w
  simp only [rankCandidates, mem_cell, Finset.mem_filter, restrictPermit, Bool.and_eq_true]
  constructor
  · rintro ⟨hP, hW⟩
    refine ⟨⟨fun p => (hP p).1, hW⟩, ?_⟩
    intro k hk
    let p := (pos (n := n)).symm k
    have he : pos p = k := pos.apply_symm_apply k
    have hh := (hP p).2
    rw [compat, he, ite_eq_left hk, decide_eq_true_eq] at hh
    rwa [bit, ← pos_val, he] at hh
  · rintro ⟨⟨hP, hW⟩, hPref⟩
    refine ⟨fun p => ⟨hP p, ?_⟩, hW⟩
    unfold compat
    by_cases h : j.val ≤ (pos p).val
    · simp only [ite_eq_left h, decide_eq_true_eq]
      simpa only [bit, pos_val] using hPref (pos p) h
    · simp [h]

end CellModel

namespace SelectTable

open Finset Compiler.Build CountCircuit

variable {N n w : ℕ}

private def asBits (z : Fin (2^w)) (j : Fin w) : Bool := z.val.testBit j.val

private theorem asBits_bijective : Function.Bijective (asBits (w := w)) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by simp⟩
  intro a b he
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w
  · exact congrFun he ⟨j, hj⟩
  · have hp : 2^w ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (a.isLt.trans_le hp), Nat.testBit_eq_false_of_lt (b.isLt.trans_le hp)]

noncomputable def fromBits (f : Fin w → Bool) : ℕ :=
  ((Equiv.ofBijective asBits asBits_bijective).symm f).val

theorem fromBits_lt (f : Fin w → Bool) : fromBits f < 2^w := Fin.isLt _

theorem fromBits_bit (f : Fin w → Bool) (j : Fin w) : (fromBits f).testBit j.val = f j :=
  congrFun ((Equiv.ofBijective asBits asBits_bijective).apply_symm_apply f) j

theorem fromBits_id {z : ℕ} (hz : z < 2^w) : fromBits (fun j : Fin w => z.testBit j.val) = z :=
  congrArg Fin.val ((Equiv.ofBijective asBits asBits_bijective).symm_apply_apply ⟨z, hz⟩)

def sel (hot : Fin 3 → Fin (n+1) → Sig N) (t : BucketIndex n) : Sig N :=
  an (an (hot 0 (t 0)) (hot 1 (t 1))) (hot 2 (t 2))

private theorem sel_build {A : Set (Sig N)} (hot : Fin 3 → Fin (n+1) → Sig N)
    (hhot : ∀ k a, hot k a ∈ A) (t : BucketIndex n) : Build A {sel hot t} 2 := by
  have h := andG (hhot 0 (t 0)) (hhot 1 (t 1))
  have h' := andG (A := A ∪ {an (hot 0 (t 0)) (hot 1 (t 1))})
    (f := an (hot 0 (t 0)) (hot 1 (t 1))) (Or.inr rfl) (Or.inl (hhot 2 (t 2)))
  exact thenG h h'

noncomputable def pickBit (hot : Fin 3 → Fin (n+1) → Sig N)
    (data : BucketIndex n → (Fin N → Bool) → ℕ) (j : Fin w) : Sig N :=
  fun x => ((Finset.univ : Finset (BucketIndex n)).toList.map
    (fun t => an (sel hot t) (bitsOf w (data t) j))).any (fun f => f x)

noncomputable def pick (hot : Fin 3 → Fin (n+1) → Sig N)
    (data : BucketIndex n → (Fin N → Bool) → ℕ) (w : ℕ) (x : Fin N → Bool) : ℕ :=
  fromBits (fun j : Fin w => pickBit hot data j x)

theorem pick_lt (hot : Fin 3 → Fin (n+1) → Sig N)
    (data : BucketIndex n → (Fin N → Bool) → ℕ) (w : ℕ) (x : Fin N → Bool) :
    pick hot data w x < 2^w := fromBits_lt _

theorem pick_onehot (hot : Fin 3 → Fin (n+1) → Sig N)
    (data : BucketIndex n → (Fin N → Bool) → ℕ) (x : Fin N → Bool) (t₀ : BucketIndex n)
    (hh : ∀ k j, hot k j x = decide (j = t₀ k)) (hd : data t₀ x < 2^w) :
    pick hot data w x = data t₀ x := by
  have hs (t : BucketIndex n) : sel hot t x = decide (t = t₀) := by
    have he : t = t₀ ↔ t 0 = t₀ 0 ∧ t 1 = t₀ 1 ∧ t 2 = t₀ 2 := by
      constructor
      · rintro rfl; exact ⟨rfl,rfl,rfl⟩
      · rintro ⟨h₀,h₁,h₂⟩
        funext i
        fin_cases i <;> assumption
    simp [sel, an, hh, he, Bool.and_assoc, Bool.decide_and]
  have hb (j : Fin w) : pickBit hot data j x = (data t₀ x).testBit j.val := by
    have ht : pickBit hot data j x = true ↔ (data t₀ x).testBit j.val = true := by
      simp [pickBit, List.any_eq_true, an, hs, bitsOf]
    cases ha : pickBit hot data j x <;> cases hb : (data t₀ x).testBit j.val <;> simp_all
  unfold pick
  simp_rw [hb]
  exact fromBits_id hd

def pickCost (n w : ℕ) : ℕ := w * (4*(n+1)^3)

theorem buildPick {A : Set (Sig N)} (hot : Fin 3 → Fin (n+1) → Sig N)
    (data : BucketIndex n → (Fin N → Bool) → ℕ) (w : ℕ)
    (hh : ∀ k j, hot k j ∈ A) (hd : ∀ t, Available A (bitsOf w (data t)))
    (hf : (fun _ => false) ∈ A) :
    Build A (Set.range (bitsOf w (pick hot data w))) (pickCost n w) := by
  classical
  have he (j : Fin w) : bitsOf w (pick hot data w) j = pickBit hot data j := by
    funext x
    exact fromBits_bit _ j
  rw [funext he]
  unfold pickCost
  apply finG
  intro j
  let terms (t : BucketIndex n) := an (sel hot t) (bitsOf w (data t) j)
  have H : Build A (Set.range terms) ((n+1)^3*3) := by
    have hx (t : BucketIndex n) : Build A {terms t} 3 := by
      exact thenG (sel_build hot hh t) (andG (Or.inr rfl) (Or.inl (hd t j)))
    simpa [BucketIndex] using allG terms 3 hx
  have hJ : Build (A ∪ Set.range terms) {pickBit hot data j} ((n+1)^3) := by
    have hg := anyG (A := A ∪ Set.range terms)
      ((Finset.univ : Finset (BucketIndex n)).toList.map terms)
      (by simp) (Or.inl hf)
    change Build _ {fun x => ((Finset.univ : Finset (BucketIndex n)).toList.map terms).any (fun f => f x)} _
    simpa [BucketIndex] using hg
  exact relax (thenG H hJ) le_rfl le_rfl (by omega)

end SelectTable

namespace Core

open Finset Compiler.Build CountCircuit CellModel PathCount SelectTable WireArithmetic

variable {N n h : ℕ}

abbrev B (n : ℕ) := 2*n
abbrev D (n : ℕ) := 2*n+1

abbrev Permit (N n : ℕ) := V n → Bool → Sig N
abbrev Hot (N n : ℕ) := Fin 3 → Fin (n+1) → Sig N

abbrev Path (σ τ : Equiv.Perm (Fin n)) (h : ℕ) :=
  Relation.ReflTransGen (transition (Edge σ τ) (h+4)) (∅, Finset.univ) (Finset.univ, ∅)

def cells (σ τ : Equiv.Perm (Fin n)) (permits : Permit N n) (t : BucketIndex n) (x : Fin N → Bool) : ℕ :=
  (cell σ τ (fun v a => permits v a x) t).card

def cellOutputs (σ τ : Equiv.Perm (Fin n)) (permits : Permit N n) : Set (Sig N) :=
  familyOut Finset.univ (fun t : BucketIndex n => Set.range (bitsOf (D n) (cells σ τ permits t)))

theorem cellOutput_mem (σ τ : Equiv.Perm (Fin n)) (permit : Permit N n) (t : BucketIndex n) (i : Fin (D n)) :
    bitsOf (D n) (cells σ τ permit t) i ∈ cellOutputs σ τ permit :=
  ⟨t, Finset.mem_univ t, i, rfl⟩

def tableCost (n h : ℕ) := (2*(2*n))*stepCost n (D n) (h+4)

theorem buildCells {A : Set (Sig N)} {σ τ : Equiv.Perm (Fin n)} (path : Path σ τ h)
    (permits : Permit N n) (hp : ∀ v a, permits v a ∈ A)
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    Build A (cellOutputs σ τ permits) (tableCost n h) := by
  have H := rootTable (A := A) (m := D n) (b := n) (features σ τ) test (edge_features σ τ) permits hp hf ht path
  refine relax H le_rfl ?_ ?_
  · rintro f ⟨t, -, i, rfl⟩
    have he : fBucket (features σ τ) test permits Finset.univ ∅ ∅ (coords t) = cells σ τ permits t := by
      funext x
      exact cell_count σ τ _ t
    rw [← he]
    exact table_mem (Finset.Subset.rfl) t i
  · simp [tableCost, Fintype.card_prod]

def masked (permit : Permit N n) (j : Fin (B n)) (p : Fin (B n) → Sig N) : Permit N n :=
  fun v a x => restrictPermit (fun v' a' => permit v' a' x) j (fun k => p k x) v a

theorem buildMasked {A : Set (Sig N)} (permit : Permit N n) (j : Fin (B n)) (p : Fin (B n) → Sig N)
    (hp : ∀ v a, permit v a ∈ A) (hb : Available A p) (hf : (fun _ => false) ∈ A) :
    Build A (Set.range (fun i : V n × Bool => masked permit j p i.1 i.2)) (8*n) := by
  have H (i : V n × Bool) : Build A {masked permit j p i.1 i.2} 2 := by
    obtain ⟨v, a⟩ := i
    by_cases hk : j.val ≤ (pos v).val
    · by_cases he : pos v = j
      · cases a
        · have e : masked permit j p v false = permit v false := by
            funext x; simp [masked, restrictPermit, compat, rankSetBit, he]
          rw [e]
          exact relax (idle (Set.singleton_subset_iff.mpr (hp v false))) le_rfl le_rfl (by omega)
        · have e : masked permit j p v true = fun _ => false := by
            funext x; simp [masked, restrictPermit, compat, rankSetBit, he]
          rw [e]
          exact relax (idle (Set.singleton_subset_iff.mpr hf)) le_rfl le_rfl (by omega)
      · cases a
        · have e : masked permit j p v false = an (permit v false) (nt (p (pos v))) := by
            funext x; simp [masked, restrictPermit, compat, hk, rankSetBit, he, an, nt, Bool.false_eq]
          rw [e]
          exact thenG (notG (hb (pos v))) (andG (Or.inl (hp v false)) (Or.inr rfl))
        · have e : masked permit j p v true = an (permit v true) (p (pos v)) := by
            funext x; simp [masked, restrictPermit, compat, hk, rankSetBit, he, an, Bool.true_eq]
          rw [e]
          exact relax (andG (hp v true) (hb (pos v))) le_rfl le_rfl (by omega)
    · have e : masked permit j p v a = permit v a := by
        funext x; simp [masked, restrictPermit, compat, hk]
      rw [e]
      exact relax (idle (Set.singleton_subset_iff.mpr (hp v a))) le_rfl le_rfl (by omega)
  have hsize : Fintype.card (V n × Bool) * 2 = 8*n := by simp [Fintype.card_prod]; omega
  simpa only [hsize] using allG _ 2 H

noncomputable def total (σ τ : Equiv.Perm (Fin n)) (hot : Hot N n) (permit : Permit N n) : (Fin N → Bool) → ℕ :=
  pick hot (cells σ τ permit) (D n)

noncomputable def recount (σ τ : Equiv.Perm (Fin n)) (hot : Hot N n) (permit : Permit N n)
    (x : Fin N → Bool) (j : Fin (B n)) (p : Fin (B n) → Bool) : ℕ :=
  total σ τ hot (masked permit j (fun k _ => p k)) x

private theorem pick_local {hot : Hot N n} {F G : BucketIndex n → (Fin N → Bool) → ℕ} {x : Fin N → Bool}
    (he : ∀ t, F t x = G t x) : pick hot F w x = pick hot G w x := by
  unfold pick
  congr 1
  funext j
  simp [pickBit, List.any_map, Function.comp_def, an, bitsOf, he]

theorem recount_agree (σ τ : Equiv.Perm (Fin n)) (hot : Hot N n) (permit : Permit N n)
    (x : Fin N → Bool) (t : BucketIndex n) (hhot : ∀ k j, hot k j x = decide (j = t k))
    (j : Fin (B n)) (p : Fin (B n) → Bool) :
    recount σ τ hot permit x j p = rankCount (cell σ τ (fun v a => permit v a x) t) j p := by
  unfold recount total
  rw [pick_onehot _ _ _ t hhot (cell_bound σ τ _ t)]
  exact restricted_cell σ τ _ t j p

def recountCost (n h : ℕ) := 8*n + tableCost n h + pickCost n (D n)

theorem buildRecount {A : Set (Sig N)} {σ τ : Equiv.Perm (Fin n)} (path : Path σ τ h)
    (permit : Permit N n) (hot : Hot N n) (j : Fin (B n)) (p : Fin (B n) → Sig N)
    (hp : ∀ v a, permit v a ∈ A) (hh : ∀ k j, hot k j ∈ A) (hb : Available A p)
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    Build A (Set.range (bitsOf (D n) (fun x => recount σ τ hot permit x j (fun k => p k x)))) (recountCost n h) := by
  let mask := masked permit j p
  let M := Set.range (fun i : V n × Bool => mask i.1 i.2)
  have hm : Build A M (8*n) := buildMasked permit j p hp hb hf
  have hc := buildCells (A := A ∪ M) path mask (fun v a => Or.inr ⟨(v,a),rfl⟩) (Or.inl hf) (Or.inl ht)
  have ht' := buildPick (A := (A ∪ M) ∪ cellOutputs σ τ mask) hot (cells σ τ mask) (D n)
    (fun k j' => Or.inl (Or.inl (hh k j'))) (fun t l => Or.inr (cellOutput_mem σ τ mask t l)) (Or.inl (Or.inl hf))
  have he : (fun x => recount σ τ hot permit x j (fun k => p k x)) = total σ τ hot mask := by
    funext x
    exact pick_local (fun _ => rfl)
  rw [he]
  have H := thenG (seq hm hc) (relax ht' (fun _ hs => by simpa only [Set.union_assoc] using hs) le_rfl le_rfl)
  exact H

noncomputable def flagSig (σ τ : Equiv.Perm (Fin n)) (hot : Hot N n) (permit : Permit N n)
    (r : (Fin N → Bool) → ℕ) : Sig N := fun x => decide (r x < total σ τ hot permit x)

noncomputable def wordSig (σ τ : Equiv.Perm (Fin n)) (hot : Hot N n) (permit : Permit N n)
    (r : (Fin N → Bool) → ℕ) (j : Fin (B n)) : Sig N :=
  fun x => flagSig σ τ hot permit r x && (rankStage (recount σ τ hot permit x) (r x) (B n)).pref j

def coreCost (n h : ℕ) := tableCost n h + pickCost n (D n) + (10*D n+10) +
  (B n)*(recountCost n h + (14*D n+10) + 1) + B n

theorem buildOutputs {A : Set (Sig N)} {σ τ : Equiv.Perm (Fin n)} (path : Path σ τ h)
    (permit : Permit N n) (hot : Hot N n) (r : (Fin N → Bool) → ℕ)
    (hp : ∀ v a, permit v a ∈ A) (hh : ∀ k j, hot k j ∈ A)
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (hr : Available A (bitsOf (D n) r)) (hrb : ∀ x, r x < 2^(D n)) :
    Build A ((cellOutputs σ τ permit ∪ {flagSig σ τ hot permit r}) ∪ Set.range (wordSig σ τ hot permit r))
      (coreCost n h) := by
  let C := cellOutputs σ τ permit
  let T := Set.range (bitsOf (D n) (total σ τ hot permit))
  let F : Set (Sig N) := {flagSig σ τ hot permit r}
  let P := Set.range (fun j : Fin (B n) => fun x => (rankStage (recount σ τ hot permit x) (r x) (B n)).pref j)
  have hc : Build A C _ := buildCells path permit hp hf ht
  have ht' : Build (A ∪ C) T _ := buildPick hot (cells σ τ permit) (D n)
    (fun k j => Or.inl (hh k j)) (fun t i => Or.inr (cellOutput_mem σ τ permit t i)) (Or.inl hf)
  have htot : ∀ x, total σ τ hot permit x < 2^(D n) := fun x => pick_lt _ _ _ x
  have hflag : Build (A ∪ (C ∪ T)) F _ := wordLtB r (total σ τ hot permit)
    (Or.inl hf) (Or.inl ht) (fun i => Or.inl (hr i)) (fun i => Or.inr (Or.inr ⟨i,rfl⟩)) hrb htot
  have hprefix : Build A P _ := rankCircuitB r (recount σ τ hot permit) hf ht hr hrb
    (fun x j p => pick_lt _ _ _ x) (fun A' j p ha hb => buildRecount path permit hot j p
      (fun v a => ha (hp v a)) (fun k t => ha (hh k t)) hb (ha hf) (ha ht))
  have H := bothG (seq (seq hc ht') hflag) hprefix
  have hlast : Build (A ∪ (((C ∪ T) ∪ F) ∪ P)) (Set.range (wordSig σ τ hot permit r)) (B n) :=
    wordAndG (v := fun _ => flagSig σ τ hot permit r) (fun _ => Or.inr (Or.inl (Or.inr rfl)))
      (fun i => Or.inr (Or.inr ⟨i,rfl⟩))
  refine relax (seq H hlast) le_rfl ?_ le_rfl
  intro s hs
  rcases hs with (hs | hs) | hs
  · exact Or.inl (Or.inl (Or.inl (Or.inl hs)))
  · exact Or.inl (Or.inl (Or.inr hs))
  · exact Or.inr hs

end Core

open Compiler.Build

namespace InputEncoding

variable {n : ℕ}

def inputDim (n : ℕ) : ℕ := 2 + 4*n + 3*(n+1) + 2*n

private def mask (permits : Bool × Fin n → Bool → Bool) : List Bool :=
  (List.ofFn (fun i : Fin n =>
    [permits (false,i) false, permits (false,i) true,
     permits (true,i) false, permits (true,i) true])).flatten

private def hot (j : Fin (n+1)) : List Bool :=
  List.ofFn (fun k : Fin (n+1) => decide (k = j))

def encode (permits : Bool × Fin n → Bool → Bool) (a b c : Fin (n+1))
    (index : Fin (2^(2*n))) : List Bool :=
  [false,true] ++ mask permits ++ hot a ++ hot b ++ hot c ++
    List.ofFn (fun i : Fin (2*n) => index.val.testBit i.val)

private def maskAt (permits : Bool × Fin n → Bool → Bool) (j : Fin (4*n)) : Bool :=
  permits (decide (2 ≤ j.val % 4), ⟨j.val / 4, by omega⟩) (decide (j.val % 2 = 1))

private theorem mask_eq (permits : Bool × Fin n → Bool → Bool) :
    mask permits = List.ofFn (maskAt permits) := by
  rw [List.ofFn_mul']
  unfold mask
  congr 1
  apply congrArg List.ofFn
  funext i
  have hi := i.isLt
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp only [maskAt, Fin.val_zero, Fin.val_succ]
  have hm0 : 4 * i.val % 2 ≠ 1 := by omega
  have hm1 : (4 * i.val + 1) % 2 = 1 := by omega
  have hm3 : (4 * i.val + 3) % 2 = 1 := by omega
  have h1 : (4 * i.val + (0 + 1)) / 4 = i.val := by omega
  have h2 : (4 * i.val + (0 + 1 + 1)) / 4 = i.val := by omega
  have h3 : (4 * i.val + (0 + 1 + 1 + 1)) / 4 = i.val := by omega
  simp [h1, h2, h3, hm0, hm1, hm3]

@[local simp] private theorem mask_length (permits : Bool × Fin n → Bool → Bool) :
    (mask permits).length = 4*n := by rw [mask_eq, List.length_ofFn]

@[local simp] private theorem hot_length (j : Fin (n+1)) : (hot j).length = n+1 :=
  List.length_ofFn

theorem encode_length (permits : Bool × Fin n → Bool → Bool) (a b c : Fin (n+1))
    (index : Fin (2^(2*n))) : (encode permits a b c index).length = inputDim n := by
  simp [encode, inputDim]
  omega

private def permitPos (p : Bool × Fin n) (b : Bool) : Fin (inputDim n) :=
  ⟨2 + 4*p.2.val + 2*p.1.toNat + b.toNat, by
    have := p.2.isLt
    cases p.1 <;> cases b <;> simp [inputDim] <;> omega⟩

private def hotPos (k : Fin 3) (j : Fin (n+1)) : Fin (inputDim n) :=
  ⟨2 + 4*n + k.val*(n+1) + j.val, by
    have := j.isLt
    fin_cases k <;> simp [inputDim] <;> omega⟩

private def indexPos (j : Fin (2*n)) : Fin (inputDim n) :=
  ⟨2 + 4*n + 3*(n+1) + j.val, by have := j.isLt; unfold inputDim; omega⟩

def getPermit (p : Bool × Fin n) (b : Bool) : Sig (inputDim n) := fun v => v (permitPos p b)

def getHot (k : Fin 3) (j : Fin (n+1)) : Sig (inputDim n) := fun v => v (hotPos k j)

def getIndex (j : Fin (2*n)) : Sig (inputDim n) := fun v => v (indexPos j)

theorem getPermit_mem_base (p : Bool × Fin n) (b : Bool) :
    getPermit p b ∈ base (inputDim n) := Or.inl ⟨permitPos p b, rfl⟩

theorem getHot_mem_base (k : Fin 3) (j : Fin (n+1)) :
    getHot k j ∈ base (inputDim n) := Or.inl ⟨hotPos k j, rfl⟩

theorem getIndex_mem_base (j : Fin (2*n)) :
    getIndex j ∈ base (inputDim n) := Or.inl ⟨indexPos j, rfl⟩

variable (permits : Bool × Fin n → Bool → Bool) (a b c : Fin (n+1))
  (index : Fin (2^(2*n)))

theorem getPermit_encode (p : Bool × Fin n) (s : Bool) :
    getPermit p s (listInput (encode permits a b c index) (encode_length permits a b c index)) =
      permits p s := by
  obtain ⟨side, i⟩ := p
  have hi := i.isLt
  rw [getPermit, listInput_getD]
  simp only [encode, permitPos, List.append_assoc]
  rw [List.getD_eq_getElem _ _ (by
    simp; cases side <;> cases s <;> simp <;> omega)]
  rw [List.getElem_append_right (by simp; omega),
    List.getElem_append_left (by simp; cases side <;> cases s <;> simp <;> omega)]
  simp only [mask_eq, List.getElem_ofFn, maskAt]
  cases side <;> cases s <;> simp <;>
    congr 1 <;> first | (simp; apply Fin.ext; dsimp; omega) |
      (simp; constructor <;> first | (apply Fin.ext; dsimp; omega) | omega) |
      (simp; omega)

theorem getHot_encode (k : Fin 3) (j : Fin (n+1)) :
    getHot k j (listInput (encode permits a b c index) (encode_length permits a b c index)) =
      decide (j = (![a,b,c] : Fin 3 → Fin (n+1)) k) := by
  have hj := j.isLt
  rw [getHot, listInput_getD]
  simp only [encode, hotPos, List.append_assoc]
  rw [List.getD_eq_getElem _ _ (by simp; fin_cases k <;> simp <;> omega)]
  rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by simp; omega)]
  fin_cases k <;> simp only [zero_mul, one_mul] <;>
    repeat' first | rw [List.getElem_append_left (by simp; omega)] |
      rw [List.getElem_append_right (by simp; omega)]
  all_goals simp only [hot, List.getElem_ofFn]; congr 2; apply Fin.ext; simp; omega

theorem getIndex_encode (j : Fin (2*n)) :
    getIndex j (listInput (encode permits a b c index) (encode_length permits a b c index)) =
      index.val.testBit j.val := by
  have hj := j.isLt
  rw [getIndex, listInput_getD]
  simp only [encode, indexPos]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp; omega)]
  simp only [List.getElem_ofFn]
  congr 1
  simp
  omega

end InputEncoding

namespace Front

open Compiler.Build Compiler.GateBridge InputEncoding CellModel SelectTable
open PEqualNP.Outside.L_pcx_431_aux.Core
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

private theorem addConstants {N : ℕ} (hN : 0 < N) :
    Build (inputs N) ({fun _ => false, fun _ => true} : Set (Sig N)) 3 := by
  let p : Sig N := fun x => x ⟨0,hN⟩
  have hp : p ∈ inputs N := ⟨⟨0,hN⟩, rfl⟩
  have h₁ := notG hp
  have h₂ := andG (A := inputs N ∪ {nt p}) (f := p) (g := nt p) (Or.inl hp) (Or.inr rfl)
  have he : an p (nt p) = fun _ => false := by
    funext x
    cases h : p x <;> simp [an, nt, h]
  rw [he] at h₂
  have h₃ := notG (A := inputs N ∪ ({nt p} ∪ {fun _ => false})) (f := fun _ => false) (Or.inr (Or.inr rfl))
  have ht : nt (fun _ : Fin N → Bool => false) = fun _ => true := rfl
  rw [ht] at h₃
  refine relax (seq (seq h₁ h₂) h₃) le_rfl ?_ le_rfl
  rintro f (rfl | rfl)
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr rfl

theorem realize {N b : ℕ} {O : Set (Sig N)} (hN : 0 < N) (H : Build (base N) O b) :
    ∃ (g : Circuit) (whereAt : O → Fin (N+g.size)),
      ReadsBack N g ∧ g.size ≤ 3+b ∧ (∀ a ∈ g.gates, Legal a.op a.inputs.length) ∧
      ∀ (f : O) (x : Fin N → Bool), (g.wires (List.ofFn x)).getD (whereAt f).val false = f.val x := by
  classical
  have H' : Build (inputs N) O (3+b) := thenG (addConstants hN) H
  have hs : Scheduled N id 0 (inputs N) := start (F := id) (fun (i : Fin N) x => x i) (fun _ _ => rfl)
  obtain ⟨k, hk, hks⟩ := H'.run hs le_rfl
  rw [Nat.zero_add] at hks
  obtain ⟨gs, e, back, legal, hw⟩ := hks
  have hh (f : O) := hw f.val (Or.inr f.property)
  choose i hi hs using hh
  refine ⟨⟨gs, 0⟩, fun f => ⟨i f, ?_⟩, back, ?_, legal, ?_⟩
  · simpa only [Circuit.size, e] using hi f
  · simpa only [Circuit.size, e] using hk
  · intro f x
    exact hs f x

noncomputable def indexVal {n : ℕ} (x : Fin (inputDim n) → Bool) : ℕ :=
  fromBits (fun j : Fin (B n) => getIndex j x)

theorem indexVal_bound {n : ℕ} (x : Fin (inputDim n) → Bool) : indexVal x < 2^(D n) := by
  have hx := fromBits_lt (fun j : Fin (B n) => getIndex j x)
  exact hx.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ (B n)))

theorem indexVal_available (n : ℕ) : Available (base (inputDim n)) (bitsOf (D n) indexVal) := by
  intro j
  by_cases h : j.val < B n
  · have he : bitsOf (D n) indexVal j = getIndex ⟨j.val, h⟩ := by
      funext x
      exact fromBits_bit (fun i : Fin (B n) => getIndex i x) ⟨j.val,h⟩
    rw [he]
    exact getIndex_mem_base _
  · have hj : j.val = B n := by have := j.isLt; change j.val < B n+1 at this; omega
    have he : bitsOf (D n) (indexVal (n := n)) j = fun _ => false := by
      funext x
      change (indexVal x).testBit j.val = false
      rw [hj]
      exact Nat.testBit_eq_false_of_lt (fromBits_lt (fun i : Fin (B n) => getIndex i x))
    rw [he]
    exact Or.inr (Or.inl rfl)

theorem indexVal_encode {n : ℕ} (permit : V n → Bool → Bool) (a b c : Fin (n+1)) (idx : W n) :
    indexVal (listInput (encode permit a b c idx) (encode_length permit a b c idx)) = idx.val := by
  unfold indexVal
  simpa only [getIndex_encode] using (fromBits_id idx.isLt)

theorem budget (n h : ℕ) : 3 + coreCost n h ≤ (n+2)^20 * 2^h := by
  let x := n+2
  let Y := x^5 * 2^h
  have hx : 2 ≤ x := by dsimp [x]; omega
  have hn : n ≤ x := by dsimp [x]; omega
  have hn' : n+1 ≤ x := by dsimp [x]; omega
  have hd : D n ≤ 2*x := by dsimp [D, x]; omega
  have hpos : 1 ≤ 2^h := Nat.two_pow_pos h
  have hY : x^5 ≤ Y := by simpa only [Nat.mul_one] using (Nat.mul_le_mul_left (x^5) hpos)
  have h₁ : 1 ≤ x := by omega
  have hX : x ≤ Y := by
    apply le_trans _ hY
    simpa only [pow_one] using (Nat.pow_le_pow_right h₁ (by decide : 1 ≤ 5))
  have hX4 : x^4 ≤ Y := (Nat.pow_le_pow_right h₁ (by decide : 4 ≤ 5)).trans hY
  have hone : 1 ≤ Y := h₁.trans hX
  have htab : tableCost n h ≤ 1152*Y := by
    unfold tableCost CountCircuit.stepCost
    rw [pow_add]
    calc
      2*(2*n) * (2^h * 2^4 * (n+1)^3 * (9*D n)) ≤
          2*(2*x) * (2^h * 2^4 * x^3 * (9*(2*x))) := by gcongr
      _ = 1152*Y := by dsimp [Y]; ring
  have hpick : pickCost n (D n) ≤ 8*Y := by
    unfold pickCost
    calc
      D n * (4*(n+1)^3) ≤ (2*x) * (4*x^3) := by gcongr
      _ = 8*x^4 := by ring
      _ ≤ 8*Y := Nat.mul_le_mul_left _ hX4
  have hrec : recountCost n h + (14*D n+10) + 1 ≤ 1210*Y := by
    unfold recountCost
    omega
  have hprod : B n * (recountCost n h + (14*D n+10) + 1) ≤ 2420*(x*Y) := by
    calc
      B n * (recountCost n h + (14*D n+10) + 1) ≤ (2*x)*(1210*Y) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hrec
      _ = 2420*(x*Y) := by ring
  have hY' : Y ≤ x*Y := by simpa only [Nat.one_mul] using (Nat.mul_le_mul_right Y h₁)
  have hsmall : 3 + coreCost n h ≤ 4000*(x*Y) := by
    unfold coreCost B at *
    omega
  have he : x*Y = x^6 * 2^h := by dsimp [Y]; ring
  have hc : 4000 ≤ x^14 := (by decide : 4000 ≤ 2^14).trans (Nat.pow_le_pow_left hx 14)
  calc
    3 + coreCost n h ≤ 4000*(x*Y) := hsmall
    _ ≤ x^14*(x*Y) := Nat.mul_le_mul_right _ hc
    _ = (n+2)^20 * 2^h := by rw [he]; change x^14 * (x^6 * 2^h) = x^20 * 2^h; ring

end Front

end PEqualNP.Outside.L_pcx_431_aux

open PEqualNP.Outside PEqualNP.Outside.L_pcx_431_aux
open PEqualNP.Outside.L_pcx_431_aux.Compiler.Build
open PEqualNP.Outside.L_pcx_431_aux.CellModel
open PEqualNP.Outside.L_pcx_431_aux.InputEncoding
open PEqualNP.Outside.L_pcx_431_aux.Core
open PEqualNP.Outside.L_pcx_431_aux.Front
open PEqualNP.Outside.L_pcx_431_aux.SelectTable

set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.L_pcx_431 :
∃ C : ℕ, 0 < C ∧ ∀ (n h : ℕ) (σ τ : Equiv.Perm (Fin n)),
  (∀ (q : Fin (n+1)) (M : Finset (Fin n × Fin n)),
    (∀ e ∈ M, decide (e.1.val < q.val) ≠ decide (e.2.val < q.val) ∧
      (e.2 = σ e.1 ∨ e.2 = τ e.1)) →
    Set.InjOn Prod.fst (↑M : Set (Fin n × Fin n)) →
    Set.InjOn Prod.snd (↑M : Set (Fin n × Fin n)) → M.card ≤ h) →
  let I := Fin n
  let J := Fin (n+1)
  let V := Bool × I
  let W := Fin (2^(2*n))
  let D := Fin (2*n+1)
  let N := 2 + 4*n + 3*(n+1) + 2*n
  let bit := fun (w : W) (p : V) => w.val.testBit (2*p.2.val+p.1.toNat)
  ∃ (g : PEqualNP.CircuitLowerBounds.Circuit)
    (count : J → J → J → D → Fin (N+g.size))
    (flag : Fin (N+g.size)) (word : Fin (2*n) → Fin (N+g.size)),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N g ∧ g.size ≤ (n+2)^C*2^h ∧
    (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
      (gate.op = .not ∧ gate.inputs.length = 1)) ∧
    ∀ (permits : V → Bool → Bool) (a b c : J) (index : W),
      let mask := (List.ofFn (fun i : I =>
        [permits (false,i) false, permits (false,i) true,
         permits (true,i) false, permits (true,i) true])).flatten
      let hot := fun (j : J) => List.ofFn (fun k : J => decide (k = j))
      let ws := g.wires ([false,true] ++ mask ++ hot a ++ hot b ++ hot c ++
        List.ofFn (fun i : Fin (2*n) => index.val.testBit i.val))
      let cell := fun (l s t : J) => (Finset.univ : Finset W).filter (fun w =>
        (∀ p : V, permits p (bit w p) = true) ∧
        (Finset.univ.filter (fun i : I => bit w (false,i) ≠ bit w (true,i))).card = l.val ∧
        (Finset.univ.filter (fun i : I => bit w (false,i) ≠ bit w (true,σ i))).card = s.val ∧
        (Finset.univ.filter (fun i : I => bit w (false,i) = bit w (true,τ i))).card = t.val)
      (∀ l s t, (∑ j : D, (ws.getD (count l s t j).val false).toNat*2^j.val) =
        (cell l s t).card) ∧
      ws.getD flag.val false = decide (index.val < (cell a b c).card) ∧
      let picked := ∑ j : Fin (2*n), (ws.getD (word j).val false).toNat*2^j.val
      if index.val < (cell a b c).card then
        ∃ w ∈ cell a b c, w.val = picked ∧ ((cell a b c).filter (fun y => y.val < w.val)).card = index.val
      else picked = 0 := by
  classical
  refine ⟨20, by decide, ?_⟩
  intro n h σ τ bound
  have path : Path σ τ h := by
    apply pathSchedule (E := Edge σ τ) (h := h) (fun {_ _} he => Edge_symm σ τ he)
    · intro q
      obtain ⟨C, hC, hcover⟩ := crossing_cover h σ τ bound q
      exact ⟨C, hC, fun x y hx hy => hcover x (mem_Left.mpr hx) y (fun hy' => hy (mem_Left.mp hy'))⟩
    · intro T b hd
      have he : T.filter (fun a => Edge σ τ a b) = T.filter (Edge σ τ b) := by
        ext a
        simp only [Finset.mem_filter]
        exact and_congr_right (fun _ => ⟨Edge_symm σ τ, Edge_symm σ τ⟩)
      rw [he]
      exact edge_degree_of_ne σ τ b T (fun a ha hn => hd a ha hn.symm)
  let P := getPermit (n := n)
  let H := getHot (n := n)
  let R := indexVal (n := n)
  let O := (cellOutputs σ τ P ∪ {flagSig σ τ H P R}) ∪ Set.range (wordSig σ τ H P R)
  have bld : Build (base (inputDim n)) O (coreCost n h) :=
    buildOutputs path P H R getPermit_mem_base getHot_mem_base (Or.inr (Or.inl rfl))
      (Or.inr (Or.inr rfl)) (indexVal_available n) indexVal_bound
  have hn : 0 < inputDim n := by unfold inputDim; omega
  obtain ⟨g, loc, hback, hsize, hlegal, hwire⟩ := realize hn bld
  let cRef (t : CountCircuit.BucketIndex n) (j : Fin (D n)) : O :=
    ⟨bitsOf (D n) (cells σ τ P t) j, Or.inl (Or.inl (cellOutput_mem σ τ P t j))⟩
  let fRef : O := ⟨flagSig σ τ H P R, Or.inl (Or.inr rfl)⟩
  let wRef (j : Fin (B n)) : O := ⟨wordSig σ τ H P R j, Or.inr ⟨j,rfl⟩⟩
  refine ⟨g, (fun l s t j => loc (cRef ![l,s,t] j)), loc fRef, (fun j => loc (wRef j)),
    hback, hsize.trans (budget n h), hlegal, ?_⟩
  intro permits a b c index
  let x := listInput (encode permits a b c index) (encode_length permits a b c index)
  have hx : List.ofFn x = encode permits a b c index := ofFn_listInput _ _
  have hp : (fun v z => P v z x) = permits := by
    funext v z
    exact getPermit_encode permits a b c index v z
  have hh (k : Fin 3) (j : Fin (n+1)) : H k j x = decide (j = (![a,b,c] : CountCircuit.BucketIndex n) k) :=
    getHot_encode permits a b c index k j
  have hr : R x = index.val := indexVal_encode permits a b c index
  have hc (t : CountCircuit.BucketIndex n) : cells σ τ P t x = (cell σ τ permits t).card := by
    unfold cells
    rw [hp]
  have hwc (t : CountCircuit.BucketIndex n) (j : Fin (D n)) :
      (g.wires (encode permits a b c index)).getD (loc (cRef t j)).val false =
        (cells σ τ P t x).testBit j.val := by
    rw [← hx]
    exact hwire (cRef t j) x
  have hwf : (g.wires (encode permits a b c index)).getD (loc fRef).val false = flagSig σ τ H P R x := by
    rw [← hx]
    exact hwire fRef x
  have hww (j : Fin (B n)) :
      (g.wires (encode permits a b c index)).getD (loc (wRef j)).val false = wordSig σ τ H P R j x := by
    rw [← hx]
    exact hwire (wRef j) x
  have hTotal : total σ τ H P x = (cell σ τ permits ![a,b,c]).card := by
    unfold total
    rw [pick_onehot _ _ _ ![a,b,c] hh (by rw [hc]; exact cell_bound _ _ _ _), hc]
  have hOracle (j : Fin (B n)) (p : Fin (B n) → Bool) :
      recount σ τ H P x j p = rankCount (cell σ τ permits ![a,b,c]) j p := by
    rw [recount_agree σ τ H P x ![a,b,c] hh, hp]
  refine ⟨?_, ?_, ?_⟩
  · intro l s t
    change (∑ j : Fin (D n), ((g.wires (encode permits a b c index)).getD
      (loc (cRef ![l,s,t] j)).val false).toNat * 2^j.val) = (cell σ τ permits ![l,s,t]).card
    simp_rw [hwc, hc]
    exact rankValue_bits (cell_bound σ τ permits ![l,s,t])
  · change (g.wires (encode permits a b c index)).getD (loc fRef).val false =
      decide (index.val < (cell σ τ permits ![a,b,c]).card)
    rw [hwf, flagSig, hr, hTotal]
  · change (if index.val < (cell σ τ permits ![a,b,c]).card then
      ∃ w ∈ cell σ τ permits ![a,b,c], w.val = (∑ j : Fin (B n),
        ((g.wires (encode permits a b c index)).getD (loc (wRef j)).val false).toNat * 2^j.val) ∧
        ((cell σ τ permits ![a,b,c]).filter (fun y => y.val < w.val)).card = index.val
      else (∑ j : Fin (B n), ((g.wires (encode permits a b c index)).getD (loc (wRef j)).val false).toNat * 2^j.val) = 0)
    simp_rw [hww, wordSig, flagSig, hr, hTotal]
    exact rankStage_word (cell σ τ permits ![a,b,c]) (recount σ τ H P x) hOracle index.val
