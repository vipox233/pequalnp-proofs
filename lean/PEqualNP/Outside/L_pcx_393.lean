import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_393_aux

-- The compiler and word primitives below are adapted from
-- lean/PEqualNP/Outside/L_pcx_431.lean at 5edaa5b98fcb8850538e82d2b7aa2d998868830f.
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

-- Every label in `S` is already represented by a wire. The circuit's output is not yet fixed.
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

-- Append one gate, retaining every old label even if the new label was already available.
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

-- A bounded straight-line loop retains the ambient inputs and the current state.
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

namespace Compiler
namespace Build

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

-- The low `w` bits of the two's-complement sum, and its underflow flag.
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

-- An unsigned comparison on two available `w`-bit words.
theorem wordLtB {N w : ℕ} {A : Set (Sig N)} (F T : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hF : Available A (bitsOf w F)) (hT : Available A (bitsOf w T))
    (hFb : ∀ x, F x < 2 ^ w) (hTb : ∀ x, T x < 2 ^ w) :
    Build A {fun x => decide (F x < T x)} (10 * w + 10) :=
  relax (subSumB F T hfalse htrue hF hT hFb hTb) le_rfl Set.subset_union_right le_rfl

-- Subtract when there is no underflow; otherwise retain the first operand.
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

theorem sumFinsetB {N w : ℕ} {A : Set (Sig N)} {ι : Type*}
    (s : Finset ι) (F : ι → (Fin N → Bool) → ℕ)
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (hF : ∀ i ∈ s, Available A (bitsOf w (F i))) :
    Build A (Set.range (bitsOf w (fun x => ∑ i ∈ s, F i x))) (s.card * (9 * w)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (bitConst (m := w) 0 hf ht)
  | @insert i s hi ih =>
    have H := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    have H' := sumTwoB (A := A ∪ Set.range (bitsOf w (fun x => ∑ j ∈ s, F j x)))
      w (F i) (fun x => ∑ j ∈ s, F j x) (Or.inl hf)
      (fun j => Or.inl (hF i (Finset.mem_insert_self _ _) j))
      (fun j => Or.inr ⟨j, rfl⟩)
    simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul, Nat.one_mul]
      using thenG H H'

theorem sumGatedB {N w : ℕ} {A : Set (Sig N)} {ι : Type*} [Fintype ι]
    (on : ι → Sig N) (F : ι → (Fin N → Bool) → ℕ)
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (ho : ∀ i, on i ∈ A) (hF : ∀ i, Available A (bitsOf w (F i))) :
    Build A (Set.range (bitsOf w (fun x => ∑ i, if on i x then F i x else 0)))
      (Fintype.card ι * (10 * w)) := by
  classical
  let G (i : ι) (x : Fin N → Bool) := if on i x then F i x else 0
  have H := familyG (fun i => Set.range (bitsOf w (G i))) w
    (fun i => bitGate (ho i) (hF i))
  have H' := sumFinsetB (A := A ∪ familyOut Finset.univ (fun i => Set.range (bitsOf w (G i))))
    Finset.univ G (Or.inl hf) (Or.inl ht)
    (fun i _ j => Or.inr (family_mem (B := fun i => Set.range (bitsOf w (G i))) (i := i) ⟨j, rfl⟩))
  simpa only [Finset.card_univ, ← Nat.mul_add, show w + 9 * w = 10 * w by omega]
    using thenG H H'

noncomputable def pathCounts {N : ℕ} {S E : Type*} [Fintype S] [Fintype E] [DecidableEq S]
    (init : S) (step : ℕ → S → E → S) (permit : ℕ → E → Sig N) :
    ℕ → S → (Fin N → Bool) → ℕ
  | 0, s, _ => if s = init then 1 else 0
  | j+1, s, x => ∑ a : S × E, if step j a.1 a.2 = s ∧ permit j a.2 x = true
      then pathCounts init step permit j a.1 x else 0

def countOut {N : ℕ} {S : Type*} [Fintype S]
    (w : ℕ) (F : S → (Fin N → Bool) → ℕ) : Set (Sig N) :=
  familyOut Finset.univ (fun i => Set.range (bitsOf w (F i)))

theorem countOut_mem {N w : ℕ} {S : Type*} [Fintype S]
    {F : S → (Fin N → Bool) → ℕ} (s : S) (i : Fin w) :
    bitsOf w (F s) i ∈ countOut w F := family_mem (i := s) ⟨i, rfl⟩

theorem pathCountsB {N w L : ℕ} {A : Set (Sig N)} {S E : Type*}
    [Fintype S] [Fintype E] [DecidableEq S]
    (init : S) (step : ℕ → S → E → S) (permit : ℕ → E → Sig N)
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (hp : ∀ j < L, ∀ e, permit j e ∈ A) :
    Build A (countOut w (pathCounts init step permit L))
      (L * (Fintype.card S * (Fintype.card (S × E) * (10 * w)))) := by
  let O j := countOut w (pathCounts init step permit j)
  have hb : Build A (O 0) 0 := by
    exact relax (familyG _ 0 (fun s => bitConst (m := w) (if s = init then 1 else 0) hf ht))
      le_rfl le_rfl (by simp)
  suffices H : Build A (O L) (0 + L * (Fintype.card S * (Fintype.card (S × E) * (10 * w)))) by
    simpa only [Nat.zero_add] using H
  refine loopG O hb fun j hj => ?_
  apply familyG
  intro s
  let on : S × E → Sig N := fun a => if step j a.1 a.2 = s then permit j a.2 else fun _ => false
  have hon (a) : on a ∈ A ∪ O j := by
    by_cases h : step j a.1 a.2 = s
    · rw [show on a = permit j a.2 from if_pos h]
      exact Or.inl (hp j hj a.2)
    · rw [show on a = (fun _ => false) from if_neg h]
      exact Or.inl hf
  have H := sumGatedB (w := w) on (fun (a : S × E) => pathCounts init step permit j a.1)
    (Or.inl hf) (Or.inl ht) hon (fun a i => Or.inr (countOut_mem a.1 i))
  refine relax H le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  refine ⟨i, ?_⟩
  congr 1
  funext x
  rw [pathCounts]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : step j a.1 a.2 = s <;> simp [on, h]

def runPath {S E : Type*} (init : S) (step : ℕ → S → E → S) :
    (j : ℕ) → (Fin j → E) → S
  | 0, _ => init
  | j+1, y => step j (runPath init step j (Fin.init y)) (y (Fin.last j))

def livePath {N : ℕ} {E : Type*} (permit : ℕ → E → Sig N) :
    (j : ℕ) → (Fin j → E) → (Fin N → Bool) → Bool
  | 0, _, _ => true
  | j+1, y, x => livePath permit j (Fin.init y) x && permit j (y (Fin.last j)) x

theorem pathCounts_spec {N : ℕ} {S E : Type*} [Fintype S] [Fintype E] [DecidableEq S]
    (init : S) (step : ℕ → S → E → S) (permit : ℕ → E → Sig N)
    (j : ℕ) (s : S) (x : Fin N → Bool) :
    pathCounts init step permit j s x =
      ∑ y : Fin j → E, if livePath permit j y x = true ∧ runPath init step j y = s then 1 else 0 := by
  classical
  induction j generalizing s with
  | zero => simp [pathCounts, livePath, runPath, eq_comm]
  | succ j ih =>
    rw [pathCounts]
    simp_rw [Fintype.sum_prod_type, ih]
    rw [Finset.sum_comm]
    let equiv := Fin.snocEquiv (fun _ : Fin (j + 1) => E)
    rw [← Fintype.sum_equiv equiv _ _ (fun _ => rfl), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    have he (a : S) :
        (if step j a e = s ∧ permit j e x = true then
          ∑ y : Fin j → E, if livePath permit j y x = true ∧ runPath init step j y = a then 1 else 0 else 0) =
        ∑ y : Fin j → E, if runPath init step j y = a then
          (if (livePath permit j y x = true ∧ permit j e x = true) ∧ step j a e = s then 1 else 0) else 0 := by
      split_ifs with h
      · apply Finset.sum_congr rfl
        intro y _
        by_cases hy : runPath init step j y = a <;> simp [hy, h.1, h.2]
      · rw [Finset.sum_eq_zero]
        intro y _
        by_cases hy : runPath init step j y = a
        · simp only [hy, if_true]
          split_ifs with hh
          · exact (h ⟨hh.2, hh.1.2⟩).elim
          · rfl
        · simp [hy]
    simp_rw [he, Finset.sum_comm (s := (Finset.univ : Finset S))]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single (runPath init step j y)]
    · simp [equiv, Fin.snocEquiv_apply, livePath, runPath]
    · intro a _ ha
      simp [Ne.symm ha]
    · simp

theorem livePath_spec {N : ℕ} {E : Type*} (permit : ℕ → E → Sig N)
    (j : ℕ) (y : Fin j → E) (x : Fin N → Bool) :
    livePath permit j y x = true ↔ ∀ i : Fin j, permit i.val (y i) x = true := by
  induction j with
  | zero => simp [livePath]
  | succ j ih =>
    simp only [livePath, Bool.and_eq_true, ih, Fin.init, Fin.forall_fin_succ_pi]
    constructor
    · intro h i
      exact Fin.lastCases (motive := fun i => permit i.val (y i) x = true) h.2 h.1 i
    · intro H
      exact ⟨fun i => H i.castSucc, H (Fin.last j)⟩

theorem runPath_fold {S E : Type*} (init : S) (next : S → E → S)
    (j : ℕ) (y : Fin j → E) :
    runPath init (fun _ => next) j y = (List.ofFn y).foldl next init := by
  induction j with
  | zero => simp [runPath]
  | succ j ih =>
    rw [List.ofFn_succ_last, List.foldl_append, runPath, ih]
    rfl

noncomputable def acceptingCount {N : ℕ} {S E : Type*} [Fintype S] [Fintype E] [DecidableEq S]
    (init : S) (step : ℕ → S → E → S) (permit : ℕ → E → Sig N) (accept : S → Sig N)
    (L : ℕ) (x : Fin N → Bool) : ℕ :=
  ∑ s, if accept s x then pathCounts init step permit L s x else 0

theorem acceptingCount_spec {N : ℕ} {S E : Type*} [Fintype S] [Fintype E] [DecidableEq S]
    (init : S) (step : ℕ → S → E → S) (permit : ℕ → E → Sig N) (accept : S → Sig N)
    (L : ℕ) (x : Fin N → Bool) :
    acceptingCount init step permit accept L x =
      ∑ y : Fin L → E, if livePath permit L y x = true ∧ accept (runPath init step L y) x = true
        then 1 else 0 := by
  unfold acceptingCount
  simp_rw [pathCounts_spec]
  have h (s : S) :
      (if accept s x = true then
        ∑ y : Fin L → E, if livePath permit L y x = true ∧ runPath init step L y = s then 1 else 0
        else 0) =
      ∑ y : Fin L → E, if runPath init step L y = s then
        if livePath permit L y x = true ∧ accept s x = true then 1 else 0
        else 0 := by
    by_cases hs : accept s x = true
    · simp only [hs, ite_true, and_true]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : runPath init step L y = s <;> simp [hy]
    · have hfalse : accept s x = false := Bool.eq_false_of_not_eq_true hs
      simp [hfalse]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_eq_single (runPath init step L y)]
  · simp
  · intro s _ hs
    simp [Ne.symm hs]
  · simp

theorem acceptingCountB {N w L : ℕ} {A : Set (Sig N)} {S E : Type*}
    [Fintype S] [Fintype E] [DecidableEq S]
    (init : S) (step : ℕ → S → E → S) (permit : ℕ → E → Sig N) (accept : S → Sig N)
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (hp : ∀ j < L, ∀ e, permit j e ∈ A) (ha : ∀ s, accept s ∈ A) :
    Build A (Set.range (bitsOf w (acceptingCount init step permit accept L)))
      (L * (Fintype.card S * (Fintype.card (S × E) * (10 * w))) + Fintype.card S * (10 * w)) := by
  have H := pathCountsB (w := w) init step permit hf ht hp
  have H' := sumGatedB (A := A ∪ countOut w (pathCounts init step permit L))
    (w := w) accept (pathCounts init step permit L) (Or.inl hf) (Or.inl ht)
    (fun s => Or.inl (ha s)) (fun s i => Or.inr (countOut_mem s i))
  exact thenG H H'

end Build
end Compiler

namespace Front

open Compiler.Build Compiler.GateBridge
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

end Front

namespace Layout

open Function Equiv.Perm

variable {n : ℕ}

abbrev Label := Fin n

abbrev Root (τ : Equiv.Perm (Fin n)) := {r : Fin n // ∀ s, τ.SameCycle r s → r ≤ s}

abbrev Active (τ : Equiv.Perm (Fin n)) := Σ r : Root τ, Fin (minimalPeriod τ r.val)

-- Adapted from lean/PEqualNP/Outside/L_pcx_375.lean at
-- 5edaa5b98fcb8850538e82d2b7aa2d998868830f.
lemma periodic (τ : Equiv.Perm (Fin n)) (i : Fin n) : i ∈ periodicPts τ := by
  have hlt : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by simp
  obtain ⟨a, b, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun t : Fin (n + 1) => (τ^[t.val]) i) hlt
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · refine ⟨b.val - a.val, by omega, ?_⟩
    apply (τ.injective.iterate a.val)
    rw [← Function.iterate_add_apply, show a.val + (b.val - a.val) = b.val by omega, heq]
  · refine ⟨a.val - b.val, by omega, ?_⟩
    apply (τ.injective.iterate b.val)
    rw [← Function.iterate_add_apply, show b.val + (a.val - b.val) = a.val by omega, heq]

lemma periodPos (τ : Equiv.Perm (Fin n)) (i : Fin n) : 0 < minimalPeriod τ i :=
  minimalPeriod_pos_of_mem_periodicPts (periodic τ i)

lemma periodLe (τ : Equiv.Perm (Fin n)) (i : Fin n) : minimalPeriod τ i ≤ n := by
  simpa only [Fintype.card_fin] using minimalPeriod_le_card (f := τ) (x := i)

lemma cycleIff (τ : Equiv.Perm (Fin n)) (r s : Fin n) :
    τ.SameCycle r s ↔ ∃ j < minimalPeriod τ r, (τ^[j]) r = s := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    rw [Equiv.Perm.coe_pow] at hk
    exact ⟨k % minimalPeriod τ r, Nat.mod_lt _ (periodPos τ r), iterate_mod_minimalPeriod_eq.trans hk⟩
  · rintro ⟨j, -, rfl⟩
    rw [← Equiv.Perm.coe_pow]
    exact (SameCycle.refl τ r).pow_right

lemma existsRoot (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    ∃ r : Root τ, τ.SameCycle r.val i := by
  classical
  let O := Finset.univ.filter (fun r => τ.SameCycle r i)
  have hO : O.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, SameCycle.refl τ i⟩⟩
  let r := O.min' hO
  have hr : τ.SameCycle r i := (Finset.mem_filter.mp (O.min'_mem hO)).2
  refine ⟨⟨r, ?_⟩, hr⟩
  intro s hs
  exact O.min'_le s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.symm.trans hr⟩)

def atSlot (τ : Equiv.Perm (Fin n)) (a : Active τ) : Fin n :=
  (τ^[a.2.val]) a.1.val

lemma atSlot_bij (τ : Equiv.Perm (Fin n)) : Function.Bijective (atSlot τ) := by
  constructor
  · rintro ⟨r, j⟩ ⟨s, k⟩ h
    have h1 : τ.SameCycle r.val (atSlot τ ⟨r, j⟩) := (cycleIff τ _ _).2 ⟨_, j.isLt, rfl⟩
    have h2 : τ.SameCycle s.val (atSlot τ ⟨s, k⟩) := (cycleIff τ _ _).2 ⟨_, k.isLt, rfl⟩
    rw [h] at h1
    have hrs := h1.trans h2.symm
    have hroot : r = s := Subtype.ext ((r.property _ hrs).antisymm (s.property _ hrs.symm))
    subst s
    have hjk : j = k := Fin.ext
      ((iterate_eq_iterate_iff_of_lt_minimalPeriod j.isLt k.isLt).mp h)
    subst k
    rfl
  · intro i
    obtain ⟨r, hr⟩ := existsRoot τ i
    obtain ⟨j, hj, h⟩ := (cycleIff τ _ _).mp hr
    exact ⟨⟨r, ⟨j, hj⟩⟩, h⟩

noncomputable def slotsEquiv (τ : Equiv.Perm (Fin n)) : Active τ ≃ Fin n :=
  Equiv.ofBijective (atSlot τ) (atSlot_bij τ)

lemma activeIff (τ : Equiv.Perm (Fin n)) (r : Fin n) (j : ℕ) :
    j < minimalPeriod τ r ↔ ∀ k ≤ j, 0 < k → (τ^[k]) r ≠ r := by
  constructor
  · intro h k hk hk0 hfix
    exact (not_lt_of_ge ((show IsPeriodicPt τ k r from hfix).minimalPeriod_le hk0)) (hk.trans_lt h)
  · intro h
    by_contra! hj
    exact h _ hj (periodPos τ r) iterate_minimalPeriod

lemma rootIff (τ : Equiv.Perm (Fin n)) (r : Fin n) :
    (∀ s, τ.SameCycle r s → r ≤ s) ↔ ∀ j : Fin n, r ≤ (τ^[j.val]) r := by
  constructor
  · intro h j
    rw [← Equiv.Perm.coe_pow]
    exact h _ (SameCycle.refl τ r).pow_right
  · intro h s hs
    obtain ⟨j, hj, rfl⟩ := (cycleIff τ _ _).mp hs
    exact h ⟨j, hj.trans_le (periodLe τ r)⟩

lemma nextSlot (τ : Equiv.Perm (Fin n)) (r : Root τ) (j : Fin (minimalPeriod τ r.val)) :
    τ (atSlot τ ⟨r, j⟩) =
      atSlot τ ⟨r, ⟨(j.val + 1) % minimalPeriod τ r.val, Nat.mod_lt _ (periodPos τ r.val)⟩⟩ := by
  simp only [atSlot, iterate_mod_minimalPeriod_eq, Function.iterate_succ_apply']

end Layout

namespace LayoutCircuit

open Compiler.Build

variable {N n : ℕ}

def anyFin {m : ℕ} (f : Fin m → Sig N) : Sig N :=
  fun x => (List.ofFn f).any (fun g => g x)

def allFin {m : ℕ} (f : Fin m → Sig N) : Sig N :=
  fun x => (List.ofFn f).all (fun g => g x)

lemma anyFin_true {m : ℕ} (f : Fin m → Sig N) (x : Fin N → Bool) :
    anyFin f x = true ↔ ∃ j, f j x = true := by
  simp [anyFin, List.any_eq_true, List.mem_ofFn]

lemma allFin_true {m : ℕ} (f : Fin m → Sig N) (x : Fin N → Bool) :
    allFin f x = true ↔ ∀ j, f j x = true := by
  simp [allFin, List.all_eq_true, List.mem_ofFn]

theorem anyFinB {m : ℕ} {A : Set (Sig N)} (f : Fin m → Sig N)
    (hf : ∀ j, f j ∈ A) (hz : (fun _ => false) ∈ A) :
    Build A {anyFin f} m := by
  unfold anyFin
  simpa only [List.length_ofFn] using
    anyG (List.ofFn f) (fun g hg => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
      exact hf j) hz

theorem allFinB {m : ℕ} {A : Set (Sig N)} (f : Fin m → Sig N)
    (hf : ∀ j, f j ∈ A) (ho : (fun _ => true) ∈ A) :
    Build A {allFin f} m := by
  unfold allFin
  simpa only [List.length_ofFn] using
    everyG (List.ofFn f) (fun g hg => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
      exact hf j) ho

abbrev Mat (n N : ℕ) := Fin n → Fin n → Sig N

def matPow (edge : Mat n N) : ℕ → Mat n N
  | 0, r, t => fun _ => decide (r = t)
  | j+1, r, t => anyFin (fun k => an (matPow edge j r k) (edge k t))

lemma matPow_spec (edge : Mat n N) (τ : Equiv.Perm (Fin n)) (x : Fin N → Bool)
    (he : ∀ r t, edge r t x = decide (τ r = t)) (j : ℕ) (r t : Fin n) :
    matPow edge j r t x = decide ((τ^[j]) r = t) := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    apply Bool.eq_iff_iff.mpr
    simp only [matPow, anyFin_true, an, Bool.and_eq_true, ih, he, decide_eq_true_eq,
      Function.iterate_succ_apply']
    constructor
    · rintro ⟨k, rfl, h⟩
      exact h
    · intro h
      exact ⟨_, rfl, h⟩

def matOut (edge : Mat n N) (j : ℕ) : Set (Sig N) :=
  {f | ∃ k ≤ j, ∃ r t, f = matPow edge k r t}

theorem matPowB {A : Set (Sig N)} (edge : Mat n N) (L : ℕ)
    (he : ∀ r t, edge r t ∈ A) (hz : (fun _ => false) ∈ A) (ho : (fun _ => true) ∈ A) :
    Build A (matOut edge L) (L * (n * n * (2 * n))) := by
  have hb : Build A (matOut edge 0) 0 := by
    apply idle
    rintro _ ⟨j, hj, r, t, rfl⟩
    have hj0 : j = 0 := by omega
    subst j
    by_cases h : r = t
    · simpa [matPow, h] using ho
    · simpa [matPow, h] using hz
  suffices HB : Build A (matOut edge L) (0 + L * (n * n * (2 * n))) by
    simpa only [Nat.zero_add] using HB
  refine loopG (matOut edge) hb fun j _ => ?_
  let B := A ∪ matOut edge j
  have each (r t : Fin n) : Build B {matPow edge (j+1) r t} (2*n) := by
    let f := fun k : Fin n => an (matPow edge j r k) (edge k t)
    have H := finG (A := B) f 1
      (fun k => andG (Or.inr ⟨j, le_rfl, r, k, rfl⟩) (Or.inl (he k t)))
    have H' := anyFinB (A := B ∪ Set.range f) f (fun k => Or.inr ⟨k, rfl⟩) (Or.inl (Or.inl hz))
    exact relax (thenG H H') le_rfl le_rfl (by omega)
  have H := allG (A := B) (α := Fin n × Fin n) (fun a => matPow edge (j+1) a.1 a.2)
    (2*n) (fun a => each a.1 a.2)
  refine relaxKeep H le_rfl ?_ (by simp)
  rintro _ ⟨k, hk, r, t, rfl⟩
  by_cases h : k = j+1
  · subst k
    exact Or.inr ⟨(r,t), rfl⟩
  · exact Or.inl (Or.inr ⟨k, by omega, r, t, rfl⟩)

def literal (f : Sig N) (b : Bool) : Sig N := if b then f else nt f

lemma literal_true (f : Sig N) (b : Bool) (x : Fin N → Bool) :
    literal f b x = true ↔ f x = b := by
  cases b <;> cases h : f x <;> simp [literal, nt, h]

lemma literalB {A : Set (Sig N)} (f : Sig N) (b : Bool) (hf : f ∈ A) :
    Build A {literal f b} 1 := by
  cases b
  · exact notG hf
  · exact relax (idle (Set.singleton_subset_iff.mpr hf)) le_rfl le_rfl (by omega)

def rootSignal (edge : Mat n N) (r : Fin n) : Sig N :=
  allFin (fun j : Fin n => allFin (fun t : Fin n =>
    if t < r then nt (matPow edge j.val r t) else fun _ => true))

def liveSignal (edge : Mat n N) (r j : Fin n) : Sig N :=
  an (rootSignal edge r)
    (allFin fun k : Fin n => if k.val < j.val then nt (matPow edge (k.val+1) r r) else fun _ => true)

lemma rootSignal_spec (edge : Mat n N) (τ : Equiv.Perm (Fin n)) (x : Fin N → Bool)
    (he : ∀ r t, edge r t x = decide (τ r = t)) (r : Fin n) :
    rootSignal edge r x = true ↔ ∀ s, τ.SameCycle r s → r ≤ s := by
  rw [Layout.rootIff]
  simp only [rootSignal, allFin_true]
  constructor
  · intro H j
    by_contra! h
    have hbad := H j ((τ^[j.val]) r)
    simp [h, nt, matPow_spec edge τ x he] at hbad
  · intro H j t
    by_cases h : t < r
    · have hne : (τ^[j.val]) r ≠ t := fun e => (not_lt_of_ge (e ▸ H j)) h
      simp [h, nt, matPow_spec edge τ x he, hne]
    · simp [h]

lemma liveSignal_spec (edge : Mat n N) (τ : Equiv.Perm (Fin n)) (x : Fin N → Bool)
    (he : ∀ r t, edge r t x = decide (τ r = t)) (r j : Fin n) :
    liveSignal edge r j x = true ↔
      (∀ s, τ.SameCycle r s → r ≤ s) ∧ j.val < Function.minimalPeriod τ r := by
  simp only [liveSignal, an, Bool.and_eq_true, rootSignal_spec edge τ x he, allFin_true,
    Layout.activeIff]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · intro H k hkj hk
    let l : Fin n := ⟨k-1, by have := j.isLt; omega⟩
    have hl : l.val < j.val := by dsimp [l]; omega
    have heq : l.val + 1 = k := by dsimp [l]; omega
    simpa [hl, nt, matPow_spec edge τ x he, heq] using H l
  · intro H l
    by_cases hl : l.val < j.val
    · have hbad := H (l.val+1) (by omega) (by omega)
      rw [Function.iterate_succ_apply] at hbad
      simp [hl, nt, matPow_spec edge τ x he, hbad]
    · simp [hl]

theorem testAllB {m : ℕ} {A : Set (Sig N)} (f : Fin m → Sig N)
    (mask : Fin m → Prop) [DecidablePred mask] (hf : ∀ j, f j ∈ A)
    (ho : (fun _ => true) ∈ A) :
    Build A {allFin (fun j => if mask j then nt (f j) else fun _ => true)} (2*m) := by
  let F : Fin m → Sig N := fun j => if mask j then nt (f j) else fun _ => true
  have H := finG (A := A) F 1 (fun j => by
    by_cases h : mask j
    · rw [show F j = nt (f j) from if_pos h]
      exact notG (hf j)
    · rw [show F j = (fun _ => true) from if_neg h]
      exact relax (idle (Set.singleton_subset_iff.mpr ho)) le_rfl le_rfl (by omega))
  have H' := allFinB (A := A ∪ Set.range F) F (fun j => Or.inr ⟨j, rfl⟩) (Or.inl ho)
  exact relax (thenG H H') le_rfl le_rfl (by omega)

theorem rootSignalB {A : Set (Sig N)} (edge : Mat n N) (r : Fin n)
    (hM : matOut edge n ⊆ A) (ho : (fun _ => true) ∈ A) :
    Build A {rootSignal edge r} (n*(2*n)+n) := by
  let F (j : Fin n) := allFin (fun t : Fin n =>
    if t < r then nt (matPow edge j.val r t) else fun _ => true)
  have H := finG (A := A) F (2*n) (fun j => testAllB _ _
    (fun t => hM ⟨j.val,j.isLt.le,r,t,rfl⟩) ho)
  have H' := allFinB (A := A ∪ Set.range F) F (fun j => Or.inr ⟨j, rfl⟩) (Or.inl ho)
  exact thenG H H'

theorem liveSignalB {A : Set (Sig N)} (edge : Mat n N) (r j : Fin n)
    (hM : matOut edge n ⊆ A) (ho : (fun _ => true) ∈ A) :
    Build A {liveSignal edge r j} (n*(2*n)+n+2*n+1) := by
  let y := allFin fun k : Fin n => if k.val < j.val then nt (matPow edge (k.val+1) r r) else fun _ => true
  have H := bothG (rootSignalB edge r hM ho) (testAllB (A := A)
    (fun k : Fin n => matPow edge (k.val+1) r r) (fun k => k.val < j.val)
    (fun k => hM ⟨k.val+1,k.isLt,r,r,rfl⟩) ho)
  have H' := andG (A := A ∪ ({rootSignal edge r} ∪ {y}))
    (f := rootSignal edge r) (g := y) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  exact thenG H H'

abbrev Permit (n N : ℕ) := (Bool × Fin n) → Fin 3 → Sig N
abbrev Symbol := Option (Bool × Fin 3 × Fin 3)

def allowAt (edge : Mat n N) (permit : Permit n N) (r j : Fin n) (d0 d1 : Fin 3) : Sig N :=
  anyFin fun i : Fin n => an (matPow edge j.val r i) (an (permit (false,i) d0) (permit (true,i) d1))

lemma allowAt_spec (edge : Mat n N) (permit : Permit n N) (τ : Equiv.Perm (Fin n))
    (x : Fin N → Bool) (he : ∀ r t, edge r t x = decide (τ r = t))
    (r j : Fin n) (d0 d1 : Fin 3) :
    allowAt edge permit r j d0 d1 x =
      (permit (false,(τ^[j.val]) r) d0 x && permit (true,(τ^[j.val]) r) d1 x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [allowAt, anyFin_true, an, Bool.and_eq_true, matPow_spec edge τ x he, decide_eq_true_eq]
  constructor
  · rintro ⟨i, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, rfl, h⟩

theorem allowAtB {A : Set (Sig N)} (edge : Mat n N) (permit : Permit n N)
    (r j : Fin n) (d0 d1 : Fin 3)
    (hm : matOut edge n ⊆ A) (hp : ∀ v d, permit v d ∈ A) (hz : (fun _ => false) ∈ A) :
    Build A {allowAt edge permit r j d0 d1} (3*n) := by
  let f (i : Fin n) := an (matPow edge j.val r i) (an (permit (false,i) d0) (permit (true,i) d1))
  have H := finG (A := A) f 2 (fun i =>
    thenG (andG (hp (false,i) d0) (hp (true,i) d1))
      (andG (Or.inl (hm ⟨j.val,j.isLt.le,r,i,rfl⟩)) (Or.inr rfl)))
  have H' := anyFinB (A := A ∪ Set.range f) f (fun j => Or.inr ⟨j, rfl⟩) (Or.inl hz)
  exact relax (thenG H H') le_rfl le_rfl (by omega)

def symbolSignal (edge : Mat n N) (permit : Permit n N) (r j : Fin n) : Symbol → Sig N
  | none => nt (liveSignal edge r j)
  | some (b,d0,d1) => an (liveSignal edge r j)
      (an (literal (matPow edge (j.val+1) r r) b) (allowAt edge permit r j d0 d1))

theorem symbolSignalB {A : Set (Sig N)} (edge : Mat n N) (permit : Permit n N)
    (r j : Fin n) (e : Symbol) (hm : matOut edge n ⊆ A)
    (hp : ∀ v d, permit v d ∈ A)
    (hz : (fun _ => false) ∈ A) (ho : (fun _ => true) ∈ A) :
    Build A {symbolSignal edge permit r j e} (n*(2*n)+n+2*n+1+3*n+3) := by
  have hl := liveSignalB edge r j hm ho
  cases e with
  | none =>
    exact relax (thenG hl (notG (Or.inr rfl))) le_rfl le_rfl (by omega)
  | some e =>
    obtain ⟨b,d0,d1⟩ := e
    let lit := literal (matPow edge (j.val+1) r r) b
    let al := allowAt edge permit r j d0 d1
    have H := bothG hl (bothG (literalB (matPow edge (j.val+1) r r) b (hm ⟨_,j.isLt,r,r,rfl⟩))
      (allowAtB edge permit r j d0 d1 hm hp hz))
    have H' := andG (A := A ∪ ({liveSignal edge r j} ∪ ({lit} ∪ {al}))) (f := lit) (g := al)
      (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl)))
    have H'' := andG (A := A ∪ (({liveSignal edge r j} ∪ ({lit} ∪ {al})) ∪ {an lit al}))
      (f := liveSignal edge r j) (g := an lit al) (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
    exact relax (thenG (seq H H') H'') le_rfl le_rfl (by omega)

def eqBits {m : ℕ} (F : Fin m → Sig N) (bits : Fin m → Bool) : Sig N :=
  allFin (fun j => literal (F j) (bits j))

lemma eqBits_spec {m : ℕ} (F : Fin m → Sig N) (bits : Fin m → Bool) (x : Fin N → Bool) :
    eqBits F bits x = true ↔ ∀ j, F j x = bits j := by simp [eqBits, allFin_true, literal_true]

theorem eqBitsB {m : ℕ} {A : Set (Sig N)} (F : Fin m → Sig N) (bits : Fin m → Bool)
    (hF : ∀ j, F j ∈ A) (ht : (fun _ => true) ∈ A) :
    Build A {eqBits F bits} (2*m) := by
  let G (j : Fin m) := literal (F j) (bits j)
  have H := finG (A := A) G 1 (fun j => literalB _ _ (hF j))
  have H' := allFinB (A := A ∪ Set.range G) G (fun j => Or.inr ⟨j, rfl⟩) (Or.inl ht)
  exact relax (thenG H H') le_rfl le_rfl (by omega)

end LayoutCircuit


open scoped BigOperators

-- Part4 through part4_card_le are ported unchanged, apart from the namespace,
-- from lean/PEqualNP/Outside/L_pcx_375.lean at
-- 5edaa5b98fcb8850538e82d2b7aa2d998868830f. The subsequent lemmas adapt the
-- bound to the doubled length budget and the inventory state used here.
def Part4 (m : ℕ) : Finset (Fin 4 × Fin m → Fin (m + 1)) :=
  Finset.univ.filter (fun c => ∑ p : Fin 4 × Fin m, (p.2.val + 1) * (c p).val = m)

lemma exp_quad_le (y : ℝ) (hy : 0 ≤ y) : 1 + y + y ^ 2 / 2 ≤ Real.exp y := by
  have h := Real.sum_le_exp_of_nonneg hy 3
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma sum_inv_sqrt_le (B : ℕ) :
    (∑ l ∈ Finset.range B, (1 : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ)) ≤ 2 * Real.sqrt (B : ℝ) := by
  induction B with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hsq : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hk1
    have hle : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)
    have hdiff : (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) *
        (Real.sqrt ((k + 1 : ℕ) : ℝ) + Real.sqrt (k : ℝ)) = 1 := by
      have : (Real.sqrt ((k + 1 : ℕ) : ℝ)) ^ 2 - (Real.sqrt (k : ℝ)) ^ 2 = 1 := by
        rw [Real.sq_sqrt hk1.le, Real.sq_sqrt hk]; push_cast; ring
      linarith
    have hstep : 1 / Real.sqrt ((k + 1 : ℕ) : ℝ) ≤
        2 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) := by
      rw [div_le_iff₀ hsq]
      nlinarith
    linarith

lemma part4_card_le (m : ℕ) : (Part4 m).card ≤ 2 ^ (70 * (Nat.sqrt m + 1)) := by
  let B : ℕ := Nat.sqrt m + 1
  have hBpos : (0 : ℝ) < (B : ℝ) := by positivity
  have hmle : (m : ℝ) ≤ (B : ℝ) * (B : ℝ) := by
    have h : m < B * B := Nat.lt_succ_sqrt m
    exact_mod_cast h.le
  let x : ℝ := Real.exp (-1 / (B : ℝ))
  have hxpos : 0 < x := Real.exp_pos _
  have hxlt1 : x < 1 := by
    dsimp [x]
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by norm_num) hBpos
  have hsum_eq : ((Part4 m).card : ℝ) * x ^ m ≤
      ∏ p : Fin 4 × Fin m, ∑ r : Fin (m + 1), (x ^ (p.2.val + 1)) ^ r.val := by
    rw [Fintype.prod_sum]
    have hterm : ∀ c ∈ Part4 m, x ^ m = ∏ p : Fin 4 × Fin m, (x ^ (p.2.val + 1)) ^ (c p).val := by
      intro c hc
      have hsum : ∑ p : Fin 4 × Fin m, (p.2.val + 1) * (c p).val = m := (Finset.mem_filter.mp hc).2
      simp_rw [← pow_mul]
      rw [Finset.prod_pow_eq_pow_sum, hsum]
    calc ((Part4 m).card : ℝ) * x ^ m
        = ∑ c ∈ Part4 m, x ^ m := by simp
      _ = ∑ c ∈ Part4 m, ∏ p : Fin 4 × Fin m, (x ^ (p.2.val + 1)) ^ (c p).val :=
          Finset.sum_congr rfl hterm
      _ ≤ ∑ c ∈ (Finset.univ : Finset (Fin 4 × Fin m → Fin (m + 1))),
            ∏ p : Fin 4 × Fin m, (x ^ (p.2.val + 1)) ^ (c p).val :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Finset.prod_nonneg (fun _ _ => pow_nonneg (pow_nonneg hxpos.le _) _))
  have hgeom : ∀ (y : ℝ), 0 ≤ y → y < 1 →
      (∑ r : Fin (m + 1), y ^ r.val) ≤ (1 - y)⁻¹ := by
    intro y hy0 hy1
    rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hy1.ne]
    have h1my : 0 < 1 - y := sub_pos.mpr hy1
    rw [← neg_sub 1 (y ^ (m + 1)), ← neg_sub 1 y, neg_div_neg_eq, div_le_iff₀ h1my,
        inv_mul_cancel₀ h1my.ne']
    have : 0 ≤ y ^ (m + 1) := pow_nonneg hy0 _
    linarith
  have hprod_le : (∏ p : Fin 4 × Fin m, ∑ r : Fin (m + 1), (x ^ (p.2.val + 1)) ^ r.val) ≤
      (∏ l ∈ Finset.range m, (1 - x ^ (l + 1))⁻¹) ^ 4 := by
    calc (∏ p : Fin 4 × Fin m, ∑ r : Fin (m + 1), (x ^ (p.2.val + 1)) ^ r.val)
        ≤ ∏ p : Fin 4 × Fin m, (1 - x ^ (p.2.val + 1))⁻¹ := by
          gcongr with p _
          exact hgeom (x ^ (p.2.val + 1)) (pow_nonneg hxpos.le _)
            (pow_lt_one₀ hxpos.le hxlt1 (Nat.succ_ne_zero _))
      _ = ∏ _ : Fin 4, ∏ l : Fin m, (1 - x ^ (l.val + 1))⁻¹ := by
          rw [Fintype.prod_prod_type]
      _ = (∏ l ∈ Finset.range m, (1 - x ^ (l + 1))⁻¹) ^ 4 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              Fin.prod_univ_eq_prod_range (fun l => (1 - x ^ (l + 1))⁻¹)]
  have h1mx : ∀ l : ℕ, 0 < 1 - x ^ (l + 1) := fun l =>
    sub_pos.mpr (pow_lt_one₀ hxpos.le hxlt1 (Nat.succ_ne_zero _))
  have hx_pow : ∀ l : ℕ, x ^ l = Real.exp (-((l : ℝ) / (B : ℝ))) := by
    intro l
    dsimp [x]
    rw [← Real.exp_nat_mul]
    congr 1; ring
  have hsmall : ∀ l : ℕ, l < B →
      (1 - x ^ (l + 1))⁻¹ ≤ Real.exp (2 * Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ)) := by
    intro l hl
    let t : ℝ := ((l + 1 : ℕ) : ℝ) / (B : ℝ)
    have htpos : 0 < t := by positivity
    have htle : t ≤ 1 := by
      dsimp [t]
      rw [div_le_one hBpos]
      exact_mod_cast hl
    have hexp_t : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have h1mt : t / 2 ≤ 1 - x ^ (l + 1) := by
      rw [hx_pow]
      have hneg : Real.exp (-t) ≤ (1 + t)⁻¹ := by
        rw [Real.exp_neg]
        exact inv_anti₀ (by linarith) hexp_t
      have h1 : t / (1 + t) ≤ 1 - Real.exp (-t) := by
        have : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp [show 1 + t ≠ 0 by linarith]; ring
        linarith
      have h2 : t / 2 ≤ t / (1 + t) := by
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]
        nlinarith
      linarith
    have hinv : (1 - x ^ (l + 1))⁻¹ ≤ 2 / t := by
      have : (1 - x ^ (l + 1))⁻¹ ≤ (t / 2)⁻¹ := inv_anti₀ (by linarith) h1mt
      simpa [inv_div] using this
    let u : ℝ := Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ)
    have hupos : 0 ≤ u := by positivity
    have hu2 : u ^ 2 = 1 / t := by
      dsimp [u, t]
      rw [div_pow, Real.sq_sqrt hBpos.le, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((l + 1 : ℕ) : ℝ))]
      field_simp
    have h2u : 2 / t ≤ Real.exp (2 * u) := by
      have hq := exp_quad_le (2 * u) (by linarith)
      have : 2 / t = (2 * u) ^ 2 / 2 := by rw [mul_pow, hu2]; ring
      linarith
    exact hinv.trans (by simpa [u, mul_div_assoc] using h2u)
  have hlarge : ∀ l : ℕ, B ≤ l →
      (1 - x ^ (l + 1))⁻¹ ≤ Real.exp (2 * x ^ (l + 1)) := by
    intro l hl
    have hle1 : 1 ≤ ((l + 1 : ℕ) : ℝ) / (B : ℝ) := by
      rw [le_div_iff₀ hBpos, one_mul]
      exact_mod_cast (show B ≤ l + 1 by omega)
    have hylt : x ^ (l + 1) ≤ 1 / 2 := by
      rw [hx_pow]
      have h1 : Real.exp (-(((l + 1 : ℕ) : ℝ) / (B : ℝ))) ≤ Real.exp (-1) :=
        Real.exp_le_exp.mpr (by linarith)
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h3 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, one_div]
        exact inv_anti₀ (by norm_num) h2
      linarith
    have hinv : (1 - x ^ (l + 1))⁻¹ ≤ 1 + 2 * x ^ (l + 1) := by
      have hpos : 0 < 1 - x ^ (l + 1) := by linarith
      have hy0 : 0 ≤ x ^ (l + 1) := pow_nonneg hxpos.le _
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith
    exact hinv.trans (by linarith [Real.add_one_le_exp (2 * x ^ (l + 1))])
  have hprod_exp : (∏ l ∈ Finset.range m, (1 - x ^ (l + 1))⁻¹) ≤ Real.exp (8 * (B : ℝ)) := by
    let f_bound (l : ℕ) : ℝ :=
      if l < B then 2 * Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ) else 2 * x ^ (l + 1)
    have hstep : (∏ l ∈ Finset.range m, (1 - x ^ (l + 1))⁻¹) ≤
        ∏ l ∈ Finset.range m, Real.exp (f_bound l) := by
      gcongr with l _
      · exact fun l _ => (inv_pos.mpr (h1mx l)).le
      · show (1 - x ^ (l + 1))⁻¹ ≤ Real.exp (if l < B then 2 * Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ) else 2 * x ^ (l + 1))
        split_ifs with h
        · exact hsmall l h
        · exact hlarge l (by omega)
    rw [← Real.exp_sum] at hstep
    apply hstep.trans
    apply Real.exp_le_exp.mpr
    have hsplit : (∑ l ∈ Finset.range m, f_bound l) ≤
        (∑ l ∈ Finset.range B, 2 * Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ)) +
        (∑ l ∈ Finset.range m, 2 * x ^ (l + 1)) := by
      have h1 : (∑ l ∈ Finset.range m, f_bound l) =
          (∑ l ∈ (Finset.range m).filter (· < B), 2 * Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ)) +
          (∑ l ∈ (Finset.range m).filter (fun l => ¬ l < B), 2 * x ^ (l + 1)) := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.range m) (· < B) f_bound]
        congr 1
        · apply Finset.sum_congr rfl; intro l hl; simp [f_bound, (Finset.mem_filter.mp hl).2]
        · apply Finset.sum_congr rfl; intro l hl; simp [f_bound, (Finset.mem_filter.mp hl).2]
      rw [h1]
      apply add_le_add
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro l hl; exact Finset.mem_range.mpr (Finset.mem_filter.mp hl).2
        · intro l _ _; positivity
      · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        · intro l _ _; positivity
    have hsum1 : (∑ l ∈ Finset.range B, 2 * Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ)) ≤ 4 * (B : ℝ) := by
      have : (∑ l ∈ Finset.range B, 2 * Real.sqrt (B : ℝ) / Real.sqrt ((l + 1 : ℕ) : ℝ)) =
          2 * Real.sqrt (B : ℝ) * ∑ l ∈ Finset.range B, 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
      rw [this]
      have hsq := sum_inv_sqrt_le B
      have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (B : ℝ))
      have hsqB : Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) = (B : ℝ) := Real.mul_self_sqrt hBpos.le
      nlinarith
    have hsum2 : (∑ l ∈ Finset.range m, 2 * x ^ (l + 1)) ≤ 4 * (B : ℝ) := by
      have : (∑ l ∈ Finset.range m, 2 * x ^ (l + 1)) = 2 * x * ∑ l ∈ Finset.range m, x ^ l := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
      rw [this, geom_sum_eq hxlt1.ne]
      have h1mx_pos : 0 < 1 - x := sub_pos.mpr hxlt1
      have h1mx_ge : 1 / (2 * (B : ℝ)) ≤ 1 - x := by
        have ht : 1 / (B : ℝ) ≤ 1 := by rw [div_le_one hBpos]; exact_mod_cast (show 1 ≤ B by omega)
        have h1 : 1 + 1 / (B : ℝ) ≤ Real.exp (1 / (B : ℝ)) := by linarith [Real.add_one_le_exp (1 / (B : ℝ))]
        have h2 : x ≤ (1 + 1 / (B : ℝ))⁻¹ := by
          dsimp [x]; rw [show -1 / (B : ℝ) = -(1 / (B : ℝ)) by ring, Real.exp_neg]
          exact inv_anti₀ (by positivity) h1
        have h3 : 1 - (1 + 1 / (B : ℝ))⁻¹ = (1 / (B : ℝ)) / (1 + 1 / (B : ℝ)) := by
          field_simp [hBpos.ne', show (B : ℝ) + 1 ≠ 0 by positivity]; ring
        have h4 : 1 / (2 * (B : ℝ)) ≤ (1 / (B : ℝ)) / (1 + 1 / (B : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h2B : 1 / (B : ℝ) * (2 * (B : ℝ)) = 2 := by field_simp [hBpos.ne']
          linarith
        linarith
      have hfrac : (x ^ m - 1) / (x - 1) ≤ (1 - x)⁻¹ := by
        rw [← neg_sub 1 (x ^ m), ← neg_sub 1 x, neg_div_neg_eq, div_le_iff₀ h1mx_pos,
            inv_mul_cancel₀ h1mx_pos.ne']
        have : 0 ≤ x ^ m := pow_nonneg hxpos.le m
        linarith
      have hinv : (1 - x)⁻¹ ≤ 2 * (B : ℝ) := by
        have := inv_anti₀ (by positivity) h1mx_ge
        simpa using this
      nlinarith
    linarith
  have hcard_real : ((Part4 m).card : ℝ) ≤ Real.exp (33 * (B : ℝ)) := by
    have hxm_pos : 0 < x ^ m := pow_pos hxpos m
    have h1 := hsum_eq.trans (hprod_le.trans (pow_le_pow_left₀
      (Finset.prod_nonneg (fun l _ => (inv_pos.mpr (h1mx l)).le)) hprod_exp 4))
    have h2 : ((Part4 m).card : ℝ) ≤ Real.exp (8 * (B : ℝ)) ^ 4 * (x ^ m)⁻¹ := by
      exact (le_mul_inv_iff₀ hxm_pos).mpr h1
    have h3 : Real.exp (8 * (B : ℝ)) ^ 4 = Real.exp (32 * (B : ℝ)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h4 : (x ^ m)⁻¹ ≤ Real.exp (B : ℝ) := by
      rw [hx_pow, ← Real.exp_neg, neg_neg]
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ hBpos]
      exact hmle
    calc ((Part4 m).card : ℝ)
        ≤ Real.exp (32 * (B : ℝ)) * Real.exp (B : ℝ) := by
          rw [← h3]
          exact h2.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
      _ = Real.exp (33 * (B : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
  have h2pow : Real.exp (33 * (B : ℝ)) ≤ ((2 ^ (70 * B) : ℕ) : ℝ) := by
    have he4 : Real.exp 1 ≤ (4 : ℝ) := by linarith [Real.exp_one_lt_d9]
    have h1 : Real.exp (33 * (B : ℝ)) = Real.exp 1 ^ (33 * B) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h1]
    calc Real.exp 1 ^ (33 * B)
        ≤ (4 : ℝ) ^ (33 * B) := pow_le_pow_left₀ (Real.exp_pos 1).le he4 _
      _ = (2 : ℝ) ^ (66 * B) := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]; congr 1; ring
      _ ≤ (2 : ℝ) ^ (70 * B) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = ((2 ^ (70 * B) : ℕ) : ℝ) := by norm_cast
  exact_mod_cast hcard_real.trans h2pow

-- Replacing the length budget by twice the number of labels only doubles the
-- constant in the exponent.
lemma part4_double_card_le (n : ℕ) :
    (Part4 (2 * n)).card ≤ 2 ^ (140 * (Nat.sqrt n + 1)) := by
  have hn : n < (Nat.sqrt n + 1) ^ 2 := by
    simpa only [pow_two] using Nat.lt_succ_sqrt n
  have hs : Nat.sqrt (2 * n) < 2 * (Nat.sqrt n + 1) := by
    rw [Nat.sqrt_lt]
    nlinarith
  exact (part4_card_le (2 * n)).trans (Nat.pow_le_pow_right (by decide) (by omega))

lemma succ_le_two_pow_sqrt (n : ℕ) :
    n + 1 ≤ 2 ^ (2 * (Nat.sqrt n + 1)) := by
  let b := Nat.sqrt n + 1
  have hb : b ≤ 2 ^ b := Nat.lt_two_pow_self.le
  calc
    n + 1 ≤ b * b := Nat.succ_le_of_lt (Nat.lt_succ_sqrt n)
    _ ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul hb hb
    _ = 2 ^ (2 * b) := by rw [← pow_add, two_mul]

-- Uniformly absorb a fixed coefficient, a polynomial in the input length,
-- and a fixed number of inventories into a single square-root exponential.
lemma part4_polynomial_le (n A d k : ℕ) :
    A * (n + 1) ^ d * (Part4 (2 * n)).card ^ k ≤
      2 ^ ((A + 2 * d + 140 * k) * (Nat.sqrt n + 1)) := by
  let b := Nat.sqrt n + 1
  have hAb : A ≤ A * b := by
    calc
      A = A * 1 := (Nat.mul_one A).symm
      _ ≤ A * b := Nat.mul_le_mul_left A (by dsimp [b]; omega)
  have hA : A ≤ 2 ^ (A * b) :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) hAb)
  calc
    A * (n + 1) ^ d * (Part4 (2 * n)).card ^ k
        ≤ 2 ^ (A * b) * (2 ^ (2 * b)) ^ d * (2 ^ (140 * b)) ^ k :=
      Nat.mul_le_mul
        (Nat.mul_le_mul hA (Nat.pow_le_pow_left (succ_le_two_pow_sqrt n) d))
        (Nat.pow_le_pow_left (part4_double_card_le n) k)
    _ = 2 ^ ((A + 2 * d + 140 * k) * b) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring

lemma part4_polynomial_bound (A d k : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ,
      A * (n + 1) ^ d * (Part4 (2 * n)).card ^ k ≤
        2 ^ (C * (Nat.sqrt n + 1)) := by
  refine ⟨A + 2 * d + 140 * k + 1, by omega, fun n => ?_⟩
  exact (part4_polynomial_le n A d k).trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_succ _)))

lemma part4_pow_bound (d k : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ,
      n ^ d * (Part4 (2 * n)).card ^ k ≤ 2 ^ (C * (Nat.sqrt n + 1)) := by
  obtain ⟨C, hC, h⟩ := part4_polynomial_bound 1 d k
  refine ⟨C, hC, fun n => ?_⟩
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_succ n) d)).trans
    (by simpa only [one_mul] using h n)

abbrev ProfileBoundState (n : ℕ) :=
  {c // c ∈ Part4 (2 * n)} × ((Fin (2 * n + 1) × Option Bool) × (Fin (2 * n + 1) × Option Bool))

lemma part4_state_card_le (n : ℕ) :
    Fintype.card (ProfileBoundState n) ≤ 2 ^ (180 * (Nat.sqrt n + 1)) := by
  simp only [ProfileBoundState, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin,
    Fintype.card_option, Fintype.card_bool]
  have h : (2 * n + 1) * 3 ≤ 6 * (n + 1) := by omega
  calc
    _ ≤ (Part4 (2 * n)).card * ((6 * (n + 1)) * (6 * (n + 1))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul h h)
    _ = 36 * (n + 1) ^ 2 * (Part4 (2 * n)).card ^ 1 := by ring
    _ ≤ 2 ^ (180 * (Nat.sqrt n + 1)) := part4_polynomial_le n 36 2 1


open scoped BigOperators

abbrev TernaryWord (m : ℕ) := Fin m → Fin 3

variable {m : ℕ}

def ternaryKey (x : TernaryWord m) : ℕ :=
  ∑ j : Fin m, (x j).val * 3 ^ j.val

private def lowKey (x : TernaryWord m) (cut : ℕ) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < cut), (x j).val * 3 ^ j.val

private theorem lowKey_succ (x : TernaryWord m) (j : Fin m) :
    lowKey x (j.val + 1) = lowKey x j.val + (x j).val * 3 ^ j.val := by
  have h : (Finset.univ.filter fun i : Fin m => i.val < j.val + 1) =
      insert j (Finset.univ.filter fun i : Fin m => i.val < j.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  unfold lowKey
  rw [h, Finset.sum_insert]
  · exact Nat.add_comm _ _
  · simp

private theorem lowKey_lt (x : TernaryWord m) (cut : ℕ) (h : cut ≤ m) :
    lowKey x cut < 3 ^ cut := by
  induction cut with
  | zero => simp [lowKey]
  | succ k ih =>
    let j : Fin m := ⟨k, by omega⟩
    have he := lowKey_succ x j
    change lowKey x (k + 1) = lowKey x k + (x j).val * 3 ^ k at he
    have hd : (x j).val * 3 ^ k ≤ 2 * 3 ^ k :=
      Nat.mul_le_mul_right _ (by have := (x j).isLt; omega)
    have hlow := ih (by omega)
    rw [he, pow_succ]
    omega

private theorem sameHigh_key_lt {x y : TernaryWord m} (j : Fin m)
    (hh : ∀ i : Fin m, j.val < i.val → x i = y i) (hd : x j < y j) :
    ternaryKey x < ternaryKey y := by
  have hbound := lowKey_lt x j.val j.isLt.le
  have hmul : (x j).val * 3 ^ j.val + 3 ^ j.val ≤ (y j).val * 3 ^ j.val := by
    have hd' : (x j).val + 1 ≤ (y j).val := hd
    simpa only [Nat.add_mul, Nat.one_mul] using
      Nat.mul_le_mul_right (3 ^ j.val) hd'
  have hlow : lowKey x (j.val + 1) < lowKey y (j.val + 1) := by
    rw [lowKey_succ x j, lowKey_succ y j]
    omega
  let high (z : TernaryWord m) :=
    ∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.val < j.val + 1),
      (z i).val * 3 ^ i.val
  have hsplit (z : TernaryWord m) : lowKey z (j.val + 1) + high z = ternaryKey z :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i.val < j.val + 1) _
  have hsame : high x = high y := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    rw [hh i (by omega)]
  rw [← hsplit x, ← hsplit y, hsame]
  exact Nat.add_lt_add_right hlow _

theorem ternaryKey_injective (m : ℕ) : Function.Injective (@ternaryKey m) := by
  intro x y hk
  by_contra hne
  let D := (Finset.univ : Finset (Fin m)).filter (fun i => x i ≠ y i)
  have hn : D.Nonempty := by
    by_contra h
    apply hne
    funext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let j := D.max' hn
  have hj : x j ≠ y j := (Finset.mem_filter.mp (D.max'_mem hn)).2
  have hh (i : Fin m) (hi : j.val < i.val) : x i = y i := by
    by_contra h
    have him : i ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    exact (not_le_of_gt (show j < i from hi)) (D.le_max' i him)
  rcases lt_or_gt_of_ne hj with h | h
  · exact (ne_of_lt (sameHigh_key_lt j hh h)) hk
  · exact (ne_of_lt (sameHigh_key_lt j (fun i hi => (hh i hi).symm) h)) hk.symm

-- The mask fixes exactly the positions at or above `cut`.
def ternaryCandidates (S : Finset (TernaryWord m)) (cut : ℕ) (p : TernaryWord m) :
    Finset (TernaryWord m) :=
  S.filter (fun x => ∀ j : Fin m, cut ≤ j.val → x j = p j)

def ternaryCount (S : Finset (TernaryWord m)) (cut : ℕ) (p : TernaryWord m) : ℕ :=
  (ternaryCandidates S cut p).card

theorem ternaryCandidates_top (S : Finset (TernaryWord m)) (p : TernaryWord m) :
    ternaryCandidates S m p = S := by
  apply Finset.filter_true_of_mem
  intro x _ j hj
  exact (Nat.not_le_of_gt j.isLt hj).elim

theorem ternaryCount_top (S : Finset (TernaryWord m)) (p : TernaryWord m) :
    ternaryCount S m p = S.card := by
  simp only [ternaryCount, ternaryCandidates_top]

theorem ternaryCount_le (S : Finset (TernaryWord m)) (cut : ℕ) (p : TernaryWord m) :
    ternaryCount S cut p ≤ S.card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem ternaryCandidates_step (S : Finset (TernaryWord m)) (p : TernaryWord m)
    (j : Fin m) (d : Fin 3) :
    ternaryCandidates S j.val (Function.update p j d) =
      (ternaryCandidates S (j.val + 1) p).filter (fun x => x j = d) := by
  ext x
  simp only [ternaryCandidates, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hp⟩
    refine ⟨⟨hx, ?_⟩, ?_⟩
    · intro i hi
      have hne : i ≠ j := fun h => by subst i; omega
      simpa [Function.update_of_ne hne] using hp i (by omega)
    · simpa using hp j le_rfl
  · rintro ⟨⟨hx, hp⟩, hd⟩
    refine ⟨hx, ?_⟩
    intro i hi
    by_cases he : i = j
    · subst i
      simpa using hd
    · rw [Function.update_of_ne he]
      have hv : i.val ≠ j.val := fun h => he (Fin.ext h)
      exact hp i (by omega)

def ternaryOffset (d : Fin 3) (c₀ c₁ : ℕ) : ℕ :=
  if d = 0 then 0 else if d = 1 then c₀ else c₀ + c₁

def ternaryChoose (c₀ c₁ r : ℕ) : Fin 3 × ℕ :=
  if r < c₀ then (0, r)
  else if r < c₀ + c₁ then (1, r - c₀)
  else (2, r - (c₀ + c₁))

-- Count smaller completions with the higher digits fixed, one digit at a time.
def ternaryRankFrom (count : ℕ → TernaryWord m → ℕ) (x : TernaryWord m) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if h : k < m then
      let j : Fin m := ⟨k, h⟩
      ternaryOffset (x j) (count k (Function.update x j 0))
        (count k (Function.update x j 1)) + ternaryRankFrom count x k
    else ternaryRankFrom count x k

-- At each step replace the highest unfixed digit and reduce the residual rank.
def ternarySelectFrom (count : ℕ → TernaryWord m → ℕ) :
    ℕ → TernaryWord m → ℕ → TernaryWord m
  | 0, p, _ => p
  | k + 1, p, r =>
    if h : k < m then
      let j : Fin m := ⟨k, h⟩
      let s := ternaryChoose (count k (Function.update p j 0))
        (count k (Function.update p j 1)) r
      ternarySelectFrom count k (Function.update p j s.1) s.2
    else ternarySelectFrom count k p r

private theorem three_digits (d : Fin 3) : d = 0 ∨ d = 1 ∨ d = 2 := by
  have hh : d.val = 0 ∨ d.val = 1 ∨ d.val = 2 := by have := d.isLt; omega
  rcases hh with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

private theorem choose_offset (c : Fin 3 → ℕ) (d : Fin 3) (r : ℕ)
    (hr : r < c d) :
    ternaryChoose (c 0) (c 1) (ternaryOffset d (c 0) (c 1) + r) = (d, r) := by
  rcases three_digits d with h | h | h
  · subst d
    simp [ternaryChoose, ternaryOffset, hr]
  · subst d
    have hn : ¬ c 0 + r < c 0 := by omega
    have hy : c 0 + r < c 0 + c 1 := by omega
    have hd0 : (1 : Fin 3) ≠ 0 := by decide
    simp [ternaryChoose, ternaryOffset, hd0, hn, hy]
  · subst d
    have hn : ¬ c 0 + c 1 + r < c 0 := by omega
    have hm : ¬ c 0 + c 1 + r < c 0 + c 1 := by omega
    have hd0 : (2 : Fin 3) ≠ 0 := by decide
    have hd1 : (2 : Fin 3) ≠ 1 := by decide
    simp [ternaryChoose, ternaryOffset, hd0, hd1, hn, hm]

private def ternaryEarlier (S : Finset (TernaryWord m)) (cut : ℕ) (x : TernaryWord m) :=
  (ternaryCandidates S cut x).filter (fun y => ternaryKey y < ternaryKey x)

private theorem earlier_step (S : Finset (TernaryWord m)) (x : TernaryWord m) (j : Fin m) :
    ternaryEarlier S (j.val + 1) x =
      (ternaryCandidates S (j.val + 1) x).filter (fun y => y j < x j) ∪
        ternaryEarlier S j.val x := by
  ext y
  simp only [ternaryEarlier, ternaryCandidates, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨⟨hy, hp⟩, hk⟩
    rcases lt_trichotomy (y j) (x j) with hd | hd | hd
    · exact Or.inl ⟨⟨hy, hp⟩, hd⟩
    · refine Or.inr ⟨⟨hy, ?_⟩, hk⟩
      intro i hi
      by_cases he : i = j
      · simpa [he] using hd
      · have hv : i.val ≠ j.val := fun h => he (Fin.ext h)
        exact hp i (by omega)
    · exact (not_lt_of_ge (sameHigh_key_lt j (fun i hi => (hp i hi).symm) hd).le hk).elim
  · rintro (⟨⟨hy, hp⟩, hd⟩ | ⟨⟨hy, hp⟩, hk⟩)
    · exact ⟨⟨hy, hp⟩, sameHigh_key_lt j hp hd⟩
    · exact ⟨⟨hy, fun i hi => hp i (by omega)⟩, hk⟩

private theorem earlier_disjoint (S : Finset (TernaryWord m)) (x : TernaryWord m) (j : Fin m) :
    Disjoint ((ternaryCandidates S (j.val + 1) x).filter (fun y => y j < x j))
      (ternaryEarlier S j.val x) := by
  apply Finset.disjoint_left.mpr
  intro y hy hz
  exact (ne_of_lt (Finset.mem_filter.mp hy).2)
    ((Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2 j le_rfl)

private theorem card_smaller_digit (A : Finset (TernaryWord m)) (j : Fin m) (d : Fin 3) :
    (A.filter (fun y => y j < d)).card =
      ternaryOffset d (A.filter (fun y => y j = 0)).card (A.filter (fun y => y j = 1)).card := by
  rcases three_digits d with h | h | h
  · subst d
    have he : A.filter (fun y => y j < 0) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro y _ hy
      change (y j).val < 0 at hy
      omega
    simp [he, ternaryOffset]
  · subst d
    have he : A.filter (fun y => y j < 1) = A.filter (fun y => y j = 0) := by
      apply Finset.filter_congr
      intro y _
      change (y j).val < 1 ↔ y j = 0
      rw [Fin.ext_iff]
      change (y j).val < 1 ↔ (y j).val = 0
      omega
    simp [he, ternaryOffset]
  · subst d
    have he : A.filter (fun y => y j < 2) =
        A.filter (fun y => y j = 0) ∪ A.filter (fun y => y j = 1) := by
      rw [← Finset.filter_or]
      apply Finset.filter_congr
      intro y _
      change (y j).val < 2 ↔ y j = 0 ∨ y j = 1
      simp only [Fin.ext_iff]
      change (y j).val < 2 ↔ (y j).val = 0 ∨ (y j).val = 1
      omega
    have hd : Disjoint (A.filter (fun y => y j = 0)) (A.filter (fun y => y j = 1)) := by
      apply Finset.disjoint_left.mpr
      intro y hy hz
      exact (by decide : (0 : Fin 3) ≠ 1) ((Finset.mem_filter.mp hy).2.symm.trans
        (Finset.mem_filter.mp hz).2)
    have hd0 : (2 : Fin 3) ≠ 0 := by decide
    have hd1 : (2 : Fin 3) ≠ 1 := by decide
    simp [he, Finset.card_union_of_disjoint hd, ternaryOffset, hd0, hd1]

private theorem rankFrom_card (S : Finset (TernaryWord m)) (x : TernaryWord m)
    (cut : ℕ) (hc : cut ≤ m) :
    ternaryRankFrom (ternaryCount S) x cut = (ternaryEarlier S cut x).card := by
  induction cut with
  | zero =>
    have h : ternaryEarlier S 0 x = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro y hy hlt
      have he : y = x := funext fun j => (Finset.mem_filter.mp hy).2 j (Nat.zero_le _)
      subst y
      exact (lt_irrefl _) hlt
    simp [ternaryRankFrom, h]
  | succ k ih =>
    have hk : k < m := by omega
    let j : Fin m := ⟨k, hk⟩
    rw [ternaryRankFrom, dif_pos hk, ih hk.le]
    change ternaryOffset (x j) (ternaryCount S j.val (Function.update x j 0))
      (ternaryCount S j.val (Function.update x j 1)) + (ternaryEarlier S j.val x).card =
      (ternaryEarlier S (j.val + 1) x).card
    rw [earlier_step S x j, Finset.card_union_of_disjoint (earlier_disjoint S x j),
      card_smaller_digit]
    simp only [ternaryCount, ternaryCandidates_step]

theorem ternaryRank_eq_card (S : Finset (TernaryWord m)) (x : TernaryWord m) :
    ternaryRankFrom (ternaryCount S) x m = (S.filter (fun y => ternaryKey y < ternaryKey x)).card := by
  simpa only [ternaryEarlier, ternaryCandidates_top] using rankFrom_card S x m le_rfl

private theorem rankFrom_lt_count (S : Finset (TernaryWord m)) (x : TernaryWord m)
    (hx : x ∈ S) (cut : ℕ) (hc : cut ≤ m) :
    ternaryRankFrom (ternaryCount S) x cut < ternaryCount S cut x := by
  rw [rankFrom_card S x cut hc]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
  intro h
  have hmem : x ∈ ternaryEarlier S cut x := by
    rw [h]
    exact Finset.mem_filter.mpr ⟨hx, fun _ _ => rfl⟩
  exact (lt_irrefl _) (Finset.mem_filter.mp hmem).2

theorem ternaryRank_strict (S : Finset (TernaryWord m)) {x y : TernaryWord m}
    (hx : x ∈ S) (h : ternaryKey x < ternaryKey y) :
    ternaryRankFrom (ternaryCount S) x m < ternaryRankFrom (ternaryCount S) y m := by
  rw [ternaryRank_eq_card, ternaryRank_eq_card]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨hzS, hzlt⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hzS, hzlt.trans h⟩
  · intro he
    have hmem : x ∈ S.filter (fun z => ternaryKey z < ternaryKey x) := by
      rw [he]
      exact Finset.mem_filter.mpr ⟨hx, h⟩
    exact (lt_irrefl _) (Finset.mem_filter.mp hmem).2

private theorem selectFrom_rankFrom (S : Finset (TernaryWord m)) (cut : ℕ) (hc : cut ≤ m)
    (p x : TernaryWord m) (hx : x ∈ ternaryCandidates S cut p) :
    ternarySelectFrom (ternaryCount S) cut p (ternaryRankFrom (ternaryCount S) x cut) = x := by
  induction cut generalizing p with
  | zero =>
    funext j
    exact ((Finset.mem_filter.mp hx).2 j (Nat.zero_le _)).symm
  | succ k ih =>
    have hk : k < m := by omega
    let j : Fin m := ⟨k, hk⟩
    have hp := (Finset.mem_filter.mp hx).2
    have he : ternaryCandidates S (j.val + 1) p = ternaryCandidates S (j.val + 1) x := by
      apply Finset.filter_congr
      intro y _
      constructor <;> intro hy i hi
      · exact (hy i hi).trans (hp i hi).symm
      · exact (hy i hi).trans (hp i hi)
    let c (d : Fin 3) := ternaryCount S j.val (Function.update p j d)
    have he' (d : Fin 3) : ternaryCount S j.val (Function.update x j d) = c d := by
      simp only [c, ternaryCount, ternaryCandidates_step, he]
    have hnext : x ∈ ternaryCandidates S j.val (Function.update p j (x j)) := by
      rw [ternaryCandidates_step]
      exact Finset.mem_filter.mpr ⟨hx, rfl⟩
    have hcnt : ternaryCount S j.val x = c (x j) := by
      rw [← he' (x j), Function.update_eq_self]
    have hr' := rankFrom_lt_count S x (Finset.mem_filter.mp hx).1 j.val hk.le
    rw [hcnt] at hr'
    rw [ternaryRankFrom, dif_pos hk, ternarySelectFrom, dif_pos hk]
    change ternarySelectFrom (ternaryCount S) k
      (Function.update p j (ternaryChoose (c 0) (c 1)
        (ternaryOffset (x j) (ternaryCount S j.val (Function.update x j 0))
          (ternaryCount S j.val (Function.update x j 1)) + ternaryRankFrom (ternaryCount S) x k)).1)
      (ternaryChoose (c 0) (c 1)
        (ternaryOffset (x j) (ternaryCount S j.val (Function.update x j 0))
          (ternaryCount S j.val (Function.update x j 1)) + ternaryRankFrom (ternaryCount S) x k)).2 = x
    rw [he' 0, he' 1, choose_offset c (x j) _ hr']
    exact ih hk.le _ hnext

theorem ternarySelect_rank (S : Finset (TernaryWord m)) (p x : TernaryWord m) (hx : x ∈ S) :
    ternarySelectFrom (ternaryCount S) m p (ternaryRankFrom (ternaryCount S) x m) = x := by
  apply selectFrom_rankFrom S m le_rfl p x
  simpa only [ternaryCandidates_top] using hx

private def ternaryRankIndex (S : Finset (TernaryWord m)) (x : {x // x ∈ S}) : Fin S.card :=
  ⟨ternaryRankFrom (ternaryCount S) x.val m, by
    simpa only [ternaryCount, ternaryCandidates_top] using rankFrom_lt_count S x.val x.property m le_rfl⟩

noncomputable def ternaryEquiv (S : Finset (TernaryWord m)) : Fin S.card ≃ {x // x ∈ S} :=
  (Equiv.ofBijective (ternaryRankIndex S) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨?_, by simp⟩
    intro x y he
    have hv := congrArg Fin.val he
    change ternaryRankFrom (ternaryCount S) x.val m = ternaryRankFrom (ternaryCount S) y.val m at hv
    apply Subtype.ext
    calc
      x.val = ternarySelectFrom (ternaryCount S) m (fun _ => 0)
          (ternaryRankFrom (ternaryCount S) x.val m) := (ternarySelect_rank S _ _ x.property).symm
      _ = y.val := by rw [hv, ternarySelect_rank S _ _ y.property])).symm

theorem ternaryEquiv_rank (S : Finset (TernaryWord m)) (i : Fin S.card) :
    ternaryRankFrom (ternaryCount S) (ternaryEquiv S i).val m = i.val := by
  have h := congrArg Fin.val ((ternaryEquiv S).symm_apply_apply i)
  exact h

theorem ternaryEquiv_select (S : Finset (TernaryWord m)) (p : TernaryWord m) (i : Fin S.card) :
    ternarySelectFrom (ternaryCount S) m p i.val = (ternaryEquiv S i).val := by
  rw [← ternaryEquiv_rank S i]
  exact ternarySelect_rank S p _ (ternaryEquiv S i).property

theorem ternaryEquiv_strict (S : Finset (TernaryWord m)) {i j : Fin S.card} (h : i < j) :
    ternaryKey (ternaryEquiv S i).val < ternaryKey (ternaryEquiv S j).val := by
  rcases lt_trichotomy (ternaryKey (ternaryEquiv S i).val) (ternaryKey (ternaryEquiv S j).val) with
    hk | hk | hk
  · exact hk
  · have he := ternaryKey_injective m hk
    exact ((ne_of_lt h) ((ternaryEquiv S).injective (Subtype.ext he))).elim
  · have hr := ternaryRank_strict S (ternaryEquiv S j).property hk
    rw [ternaryEquiv_rank, ternaryEquiv_rank] at hr
    exact (not_lt_of_ge (show i.val ≤ j.val from h.le) hr).elim


-- The two flattening lemmas and the testBit sum proof are from
-- lean/PEqualNP/Outside/L_pcx_399.lean at 5edaa5b98fcb8850538e82d2b7aa2d998868830f.
private lemma flatten_ofFn_eq_len {α : Type*} :
    ∀ (A B : ℕ) (L : Fin A → List α), (∀ a, (L a).length = B) → (List.ofFn L).flatten.length = A * B
  | 0, _, _, _ => by simp
  | A + 1, B, L, hL => by
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hL 0,
      flatten_ofFn_eq_len A B (fun a => L a.succ) (fun a => hL a.succ)]
    ring

private lemma flatten_ofFn_eq_getD {α : Type*} (d : α) :
    ∀ (A B : ℕ) (L : Fin A → List α), (∀ a, (L a).length = B) →
      ∀ (a : Fin A) {b : ℕ}, b < B →
        (List.ofFn L).flatten.getD (a.val * B + b) d = (L a).getD b d
  | 0, _, _, _, a, _, _ => Fin.elim0 a
  | A + 1, B, L, hL, a, b, hb => by
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ ?_ a
    · simp only [Fin.val_zero, zero_mul, zero_add]
      have hlen : b < (L 0).length := by rw [hL 0]; exact hb
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
    · intro a'
      have hge : (L 0).length ≤ a'.succ.val * B + b := by
        rw [hL 0, Fin.val_succ, Nat.succ_mul]; omega
      have hsub : a'.succ.val * B + b - (L 0).length = a'.val * B + b := by
        rw [hL 0, Fin.val_succ, Nat.succ_mul]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, hsub]
      simpa only [List.getD_eq_getElem?_getD] using
        flatten_ofFn_eq_getD d A B (fun x => L x.succ) (fun x => hL x.succ) a' hb

variable {n : ℕ}

def pos (v : Bool × Fin n) : Fin (2*n) :=
  ⟨v.2.val + (if v.1 then n else 0), by
    have h := v.2.isLt
    cases v.1 <;> simp <;> omega⟩

@[simp] theorem pos_val (v : Bool × Fin n) :
    (pos v).val = v.2.val + (if v.1 then n else 0) := rfl

def posEquiv (n : ℕ) : Bool × Fin n ≃ Fin (2*n) where
  toFun := pos
  invFun j := if h : j.val < n then (false, ⟨j.val, h⟩)
    else (true, ⟨j.val - n, by have := j.isLt; omega⟩)
  left_inv := by
    rintro ⟨b, i⟩
    have hi := i.isLt
    cases b <;> simp [hi, show ¬ i.val + n < n by omega]
  right_inv := by
    intro j
    apply Fin.ext
    dsimp only
    split_ifs with h
    · simp
    · change j.val - n + n = j.val
      omega

@[simp] theorem posEquiv_apply (v : Bool × Fin n) : posEquiv n v = pos v := rfl

def raw (x : Bool × Fin n → Bool) : List Bool :=
  List.ofFn (fun i => x (false,i)) ++ List.ofFn (fun i => x (true,i))

def permBits (σ : Equiv.Perm (Fin n)) : List Bool :=
  (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n => decide (σ i = j)))).flatten

def allowBits (allow : (Bool × Fin n) → Fin 3 → Bool) : List Bool :=
  (List.ofFn (fun k : Fin 3 => raw (fun v => allow v k))).flatten

def countBits (H : Fin (n+1) → Fin (n+1) → Fin (2*n+1) → Bool) : List Bool :=
  (List.ofFn (fun r => (List.ofFn (fun b => List.ofFn (H r b))).flatten)).flatten

def inputDim (n : ℕ) : ℕ := 2+n*n+6*n+(n+1)*(n+1)*(2*n+1)+8*n

def permOff (_ : ℕ) : ℕ := 2

def allowOff (n : ℕ) : ℕ := permOff n + n*n

def countOff (n : ℕ) : ℕ := allowOff n + 6*n

def someOff (n : ℕ) : ℕ := countOff n + (n+1)*(n+1)*(2*n+1)

def valueOff (n : ℕ) : ℕ := someOff n + 2*n

def rankOff (n : ℕ) : ℕ := valueOff n + 2*n

@[simp] theorem raw_length (x : Bool × Fin n → Bool) : (raw x).length = 2*n := by
  simp [raw] <;> omega

@[simp] theorem permBits_length (σ : Equiv.Perm (Fin n)) : (permBits σ).length = n*n :=
  flatten_ofFn_eq_len n n _ (fun _ => by simp)

@[simp] theorem allowBits_length (allow : (Bool × Fin n) → Fin 3 → Bool) :
    (allowBits allow).length = 6*n := by
  unfold allowBits
  rw [flatten_ofFn_eq_len 3 (2*n) _ (fun _ => raw_length _)]
  ring

@[simp] theorem countBits_length (H : Fin (n+1) → Fin (n+1) → Fin (2*n+1) → Bool) :
    (countBits H).length = (n+1)*(n+1)*(2*n+1) := by
  unfold countBits
  rw [flatten_ofFn_eq_len (n+1) ((n+1)*(2*n+1)) _ (fun _ =>
    flatten_ofFn_eq_len (n+1) (2*n+1) _ (fun _ => by simp))]
  rw [Nat.mul_assoc]

private theorem ofFn_getD {α : Type*} {m : ℕ} (f : Fin m → α) (i : Fin m) (d : α) :
    (List.ofFn f).getD i.val d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]

@[simp] theorem raw_getD (x : Bool × Fin n → Bool) (v : Bool × Fin n) (d : Bool) :
    (raw x).getD (pos v).val d = x v := by
  rcases v with ⟨b,i⟩
  cases b
  · change (raw x).getD i.val d = x (false,i)
    unfold raw
    rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
    exact ofFn_getD _ i _
  · change (raw x).getD (i.val + n) d = x (true,i)
    unfold raw
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
    simp only [List.length_ofFn, Nat.add_sub_cancel]
    exact ofFn_getD _ i _

@[simp] theorem permBits_getD (σ : Equiv.Perm (Fin n)) (i j : Fin n) (d : Bool) :
    (permBits σ).getD (i.val*n+j.val) d = decide (σ i = j) := by
  unfold permBits
  rw [flatten_ofFn_eq_getD d n n _ (fun _ => by simp) i j.isLt]
  exact ofFn_getD _ j d

@[simp] theorem allowBits_getD (allow : (Bool × Fin n) → Fin 3 → Bool)
    (v : Bool × Fin n) (k : Fin 3) (d : Bool) :
    (allowBits allow).getD (k.val*(2*n)+(pos v).val) d = allow v k := by
  unfold allowBits
  rw [flatten_ofFn_eq_getD d 3 (2*n) _ (fun _ => raw_length _) k (pos v).isLt]
  exact raw_getD _ v d

private theorem block_lt {A B : ℕ} (i : Fin A) {j : ℕ} (hj : j < B) : i.val*B+j < A*B := by
  have h := Nat.mul_le_mul_right B (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at h
  omega

@[simp] theorem countBits_getD (H : Fin (n+1) → Fin (n+1) → Fin (2*n+1) → Bool)
    (r b : Fin (n+1)) (k : Fin (2*n+1)) (d : Bool) :
    (countBits H).getD (r.val*((n+1)*(2*n+1))+(b.val*(2*n+1)+k.val)) d = H r b k := by
  unfold countBits
  rw [flatten_ofFn_eq_getD d (n+1) ((n+1)*(2*n+1)) _ (fun _ =>
    flatten_ofFn_eq_len (n+1) (2*n+1) _ (fun _ => by simp)) r (block_lt b k.isLt)]
  rw [flatten_ofFn_eq_getD d (n+1) (2*n+1) _ (fun _ => by simp) b k.isLt]
  exact ofFn_getD _ k d

section ExactEncode

variable (σ : Equiv.Perm (Fin n)) (allow : (Bool × Fin n) → Fin 3 → Bool)
variable (H : Fin (n+1) → Fin (n+1) → Fin (2*n+1) → Bool)
variable (p : Bool × Fin n → Option Bool) (junk : Bool × Fin n → Bool) (z : Fin (4*n) → Bool)

def encode : List Bool :=
  [false,true] ++ permBits σ ++ allowBits allow ++ countBits H ++ raw (fun v => (p v).isSome) ++
    raw (fun v => (p v).getD (junk v)) ++ List.ofFn z

@[simp] theorem encode_length : (encode σ allow H p junk z).length = inputDim n := by
  simp only [encode, inputDim, List.length_append, List.length_cons, List.length_nil,
    permBits_length, allowBits_length, countBits_length, raw_length, List.length_ofFn]
  omega

private theorem getD_segment {α : Type*} {whole before field after : List α}
    {off i : ℕ} (d : α) (hs : whole = before ++ (field ++ after))
    (ho : before.length = off) (hi : i < field.length) :
    whole.getD (off+i) d = field.getD i d := by
  subst whole
  subst off
  rw [List.getD_append_right _ _ _ _ (by omega),
    show before.length + i - before.length = i by omega, List.getD_append _ _ _ _ hi]

@[simp] theorem encode_getD_false (d : Bool) : (encode σ allow H p junk z).getD 0 d = false := by
  change (false :: _).getD 0 d = false
  rfl

@[simp] theorem encode_getD_true (d : Bool) : (encode σ allow H p junk z).getD 1 d = true := by
  change (false :: true :: _).getD 1 d = true
  rfl

@[simp] theorem encode_getD_perm (i j : Fin n) (d : Bool) :
    (encode σ allow H p junk z).getD (permOff n + (i.val*n+j.val)) d = decide (σ i = j) := by
  trans (permBits σ).getD (i.val*n+j.val) d
  · refine getD_segment (before := [false,true])
      (after := allowBits allow ++ countBits H ++ raw (fun w => (p w).isSome) ++
        raw (fun w => (p w).getD (junk w)) ++ List.ofFn z) d ?_ rfl ?_
    · simp only [encode, List.append_assoc]
    · simpa using block_lt i j.isLt
  · exact permBits_getD σ i j d

@[simp] theorem encode_getD_allow (v : Bool × Fin n) (k : Fin 3) (d : Bool) :
    (encode σ allow H p junk z).getD (allowOff n + (k.val*(2*n)+(pos v).val)) d = allow v k := by
  trans (allowBits allow).getD (k.val*(2*n)+(pos v).val) d
  · refine getD_segment (before := [false,true] ++ permBits σ)
      (after := countBits H ++ raw (fun w => (p w).isSome) ++
        raw (fun w => (p w).getD (junk w)) ++ List.ofFn z) d ?_ ?_ ?_
    · simp only [encode, List.append_assoc]
    · simp [allowOff, permOff] <;> omega
    · simpa only [allowBits_length, show 3*(2*n) = 6*n by ring] using block_lt k (pos v).isLt
  · exact allowBits_getD allow v k d

@[simp] theorem encode_getD_count (r b : Fin (n+1)) (k : Fin (2*n+1)) (d : Bool) :
    (encode σ allow H p junk z).getD
      (countOff n + (r.val*((n+1)*(2*n+1))+(b.val*(2*n+1)+k.val))) d = H r b k := by
  trans (countBits H).getD (r.val*((n+1)*(2*n+1))+(b.val*(2*n+1)+k.val)) d
  · refine getD_segment (before := ([false,true] ++ permBits σ) ++ allowBits allow)
      (after := raw (fun w => (p w).isSome) ++ raw (fun w => (p w).getD (junk w)) ++ List.ofFn z)
      d ?_ ?_ ?_
    · simp only [encode, List.append_assoc]
    · simp [countOff, allowOff, permOff] <;> omega
    · simpa only [countBits_length, Nat.mul_assoc] using block_lt r (block_lt b k.isLt)
  · exact countBits_getD H r b k d

@[simp] theorem encode_getD_some (v : Bool × Fin n) (d : Bool) :
    (encode σ allow H p junk z).getD (someOff n + (pos v).val) d = (p v).isSome := by
  trans (raw fun w => (p w).isSome).getD (pos v).val d
  · refine getD_segment (before := (([false,true] ++ permBits σ) ++ allowBits allow) ++ countBits H)
      (after := raw (fun w => (p w).getD (junk w)) ++ List.ofFn z) d ?_ ?_ ?_
    · simp only [encode, List.append_assoc]
    · simp [someOff, countOff, allowOff, permOff] <;> omega
    · simpa only [raw_length] using (pos v).isLt
  · exact raw_getD _ v d

@[simp] theorem encode_getD_value (v : Bool × Fin n) (d : Bool) :
    (encode σ allow H p junk z).getD (valueOff n + (pos v).val) d = (p v).getD (junk v) := by
  trans (raw fun w => (p w).getD (junk w)).getD (pos v).val d
  · refine getD_segment (before := ((([false,true] ++ permBits σ) ++ allowBits allow) ++ countBits H) ++
        raw (fun w => (p w).isSome)) (after := List.ofFn z) d ?_ ?_ ?_
    · simp only [encode, List.append_assoc]
    · simp [valueOff, someOff, countOff, allowOff, permOff] <;> omega
    · simpa only [raw_length] using (pos v).isLt
  · exact raw_getD _ v d

@[simp] theorem encode_getD_rank (k : Fin (4*n)) (d : Bool) :
    (encode σ allow H p junk z).getD (rankOff n + k.val) d = z k := by
  trans (List.ofFn z).getD k.val d
  · refine getD_segment (before := (((([false,true] ++ permBits σ) ++ allowBits allow) ++ countBits H) ++
        raw (fun w => (p w).isSome)) ++ raw (fun w => (p w).getD (junk w))) (after := []) d ?_ ?_ ?_
    · simp only [encode, List.append_nil, List.append_assoc]
    · simp [rankOff, valueOff, someOff, countOff, allowOff, permOff] <;> omega
    · simpa using k.isLt
  · exact ofFn_getD z k d

-- View the same posted input list as a vector for a circuit compiler.
def encodeFn : Fin (inputDim n) → Bool := fun i => (encode σ allow H p junk z).getD i.val false

@[simp] theorem ofFn_encodeFn : List.ofFn (encodeFn σ allow H p junk z) = encode σ allow H p junk z := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  rw [List.getElem_ofFn]
  exact List.getD_eq_getElem _ _ hj

end ExactEncode

theorem sum_testBit_two_pow (B v : ℕ) :
    (∑ j : Fin B, (v.testBit j.val).toNat * 2 ^ j.val) = v % 2 ^ B := by
  apply Nat.eq_of_testBit_eq
  intro k
  have h1 : ∀ B' : ℕ, ∀ w : Fin B' → Bool,
      (∑ j : Fin B', (w j).toNat * 2 ^ j.val).testBit k = if h : k < B' then w ⟨k, h⟩ else false := by
    intro B' w
    induction B' generalizing k with
    | zero => simp
    | succ B' ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      have hmul : (∑ i : Fin B', (w i.succ).toNat * (2 ^ i.val * 2)) =
          2 * ∑ i : Fin B', (w i.succ).toNat * 2 ^ i.val := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      rw [hmul]
      cases k with
      | zero =>
        simp only [Nat.zero_lt_succ, ↓reduceDIte]
        change ((w 0).toNat + 2 * ∑ i : Fin B', (w i.succ).toNat * 2 ^ i.val).testBit 0 = w 0
        cases h0 : w 0 <;> simp [Nat.testBit_zero]
      | succ k =>
        have htb : ((w 0).toNat + 2 * ∑ i : Fin B', (w i.succ).toNat * 2 ^ i.val).testBit (k + 1) =
            (∑ i : Fin B', (w i.succ).toNat * 2 ^ i.val).testBit k := by
          rw [Nat.testBit_succ]; congr 1; cases w 0 <;> simp <;> omega
        rw [htb, ih k (fun i => w i.succ)]
        by_cases hk : k < B'
        · simp [hk, show k + 1 < B' + 1 by omega]
        · simp [hk, show ¬ (k + 1 < B' + 1) by omega]
  rw [h1 B (fun j => v.testBit j.val), Nat.testBit_mod_two_pow]
  by_cases hk : k < B <;> simp [hk]

theorem val_testBit_of_lt {B v : ℕ} (hv : v < 2 ^ B) :
    (∑ j : Fin B, (v.testBit j.val).toNat * 2 ^ j.val) = v :=
  (sum_testBit_two_pow B v).trans (Nat.mod_eq_of_lt hv)

-- Inline after ProfileBound.lean, which supplies the exact-weight Part4.
-- Inline after ProfileBound.lean, which supplies the exact-weight Part4.
namespace StateCompression

open scoped BigOperators

abbrev Arc := ℕ × Bool × Bool
abbrev Slot (m : ℕ) := Fin 4 × Fin m
abbrev Inventory (m : ℕ) := {c // c ∈ Part4 m}

def arcColor : Fin 4 ≃ Bool × Bool :=
  (finProdFinEquiv (m := 2) (n := 2)).symm.trans (Equiv.prodCongr finTwoEquiv finTwoEquiv)

def slotLength {m : ℕ} (p : Slot m) : ℕ := p.2.val + 1

def slotArc {m : ℕ} (p : Slot m) : Arc := (slotLength p, arcColor p.1)

def arcSlot {m : ℕ} (a : Arc) (hp : 0 < a.1) (hle : a.1 ≤ m) : Slot m :=
  (arcColor.symm a.2, ⟨a.1 - 1, by omega⟩)

@[simp] lemma slotArc_arcSlot {m : ℕ} (a : Arc) (hp : 0 < a.1) (hle : a.1 ≤ m) :
    slotArc (arcSlot a hp hle) = a := by
  apply Prod.ext
  · change a.1 - 1 + 1 = a.1
    omega
  · exact arcColor.apply_symm_apply a.2

@[simp] lemma slotLength_arcSlot {m : ℕ} (a : Arc) (hp : 0 < a.1) (hle : a.1 ≤ m) :
    slotLength (arcSlot a hp hle) = a.1 :=
  congrArg Prod.fst (slotArc_arcSlot a hp hle)

lemma slotArc_injective (m : ℕ) : Function.Injective (@slotArc m) := by
  intro p q h
  apply Prod.ext
  · exact arcColor.injective (congrArg Prod.snd h)
  · apply Fin.ext
    have hlen : p.2.val + 1 = q.2.val + 1 := congrArg Prod.fst h
    omega

-- Unused length occupies the length-one, equal-endpoint, false-color slot.
def pad : Arc := (1, false, false)

def padSlot {m : ℕ} (hm : 0 < m) : Slot m := arcSlot pad (by decide) hm

@[simp] lemma slotArc_padSlot {m : ℕ} (hm : 0 < m) : slotArc (padSlot hm) = pad :=
  slotArc_arcSlot pad (by decide) hm

@[simp] lemma slotLength_padSlot {m : ℕ} (hm : 0 < m) : slotLength (padSlot hm) = 1 :=
  congrArg Prod.fst (slotArc_padSlot hm)

def count {m : ℕ} (inv : Inventory m) (p : Slot m) : ℕ := (inv.val p).val

def weight (A : List Arc) : ℕ := (A.map Prod.fst).sum

@[simp] lemma weight_nil : weight [] = 0 := rfl

@[simp] lemma weight_cons (a : Arc) (A : List Arc) : weight (a :: A) = a.1 + weight A := rfl

def weightedSum {m : ℕ} (f : Slot m → ℕ) : ℕ := ∑ p, slotLength p * f p

lemma weightedSum_count {m : ℕ} (inv : Inventory m) : weightedSum (count inv) = m :=
  (Finset.mem_filter.mp inv.property).2

private lemma weightedSum_add {m : ℕ} (f g : Slot m → ℕ) :
    weightedSum (fun p => f p + g p) = weightedSum f + weightedSum g := by
  simp only [weightedSum, Nat.mul_add, Finset.sum_add_distrib]

private lemma count_le_budget {m : ℕ} (f : Slot m → ℕ) (hf : weightedSum f = m) (p : Slot m) :
    f p ≤ m := by
  have hterm : slotLength p * f p ≤ m := by
    calc
      _ ≤ weightedSum f :=
        Finset.single_le_sum (f := fun q : Slot m => slotLength q * f q)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
      _ = m := hf
  calc
    f p = 1 * f p := (Nat.one_mul _).symm
    _ ≤ slotLength p * f p := Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le _))
    _ ≤ m := hterm

private def pack (m : ℕ) (f : Slot m → ℕ) (hf : weightedSum f = m) : Inventory m :=
  ⟨fun p => ⟨f p, Nat.lt_succ_of_le (count_le_budget f hf p)⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩⟩

private lemma count_pack (m : ℕ) (f : Slot m → ℕ) (hf : weightedSum f = m) (p : Slot m) :
    count (pack m f hf) p = f p := rfl

lemma inventory_ext {m : ℕ} {inv inv' : Inventory m}
    (h : ∀ p, count inv p = count inv' p) : inv = inv' :=
  Subtype.ext (funext fun p => Fin.ext (h p))

def single {m : ℕ} (i : Slot m) (n : ℕ) (p : Slot m) : ℕ := if p = i then n else 0

def padding (m n : ℕ) (p : Slot m) : ℕ := if slotArc p = pad then n else 0

private lemma weightedSum_single {m : ℕ} (i : Slot m) (n : ℕ) :
    weightedSum (single i n) = slotLength i * n := by
  calc
    _ = ∑ p : Slot m, if p = i then slotLength p * n else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : p = i <;> simp [single, h]
    _ = _ := Fintype.sum_ite_eq' _ _

lemma padding_eq_single {m : ℕ} (hm : 0 < m) (n : ℕ) :
    padding m n = single (padSlot hm) n := by
  funext p
  by_cases h : p = padSlot hm
  · subst p
    simp [padding, single]
  · have h' : slotArc p ≠ pad := by
      intro e
      exact h (slotArc_injective m (e.trans (slotArc_padSlot hm).symm))
    simp [padding, single, h, h']

private lemma weightedSum_padding (m n : ℕ) (hn : m = 0 → n = 0) :
    weightedSum (padding m n) = n := by
  by_cases hm : 0 < m
  · rw [padding_eq_single hm, weightedSum_single, slotLength_padSlot, Nat.one_mul]
  · have hn' : n = 0 := hn (by omega)
    simp [hn', weightedSum, padding]

def listCount {m : ℕ} (A : List Arc) (p : Slot m) : ℕ := A.count (slotArc p)

lemma listCount_cons {m : ℕ} (a : Arc) (A : List Arc) (hp : 0 < a.1) (hle : a.1 ≤ m) :
    listCount (a :: A) = fun p => listCount A p + single (arcSlot a hp hle) 1 p := by
  funext p
  by_cases h : p = arcSlot a hp hle
  · subst p
    simp [listCount, single]
  · have h' : a ≠ slotArc p := by
      intro e
      exact h (slotArc_injective m (e.symm.trans (slotArc_arcSlot a hp hle).symm))
    unfold listCount single
    rw [List.count_cons_of_ne h', ite_eq_right h, Nat.add_zero]

lemma weightedSum_listCount (m : ℕ) (A : List Arc)
    (hp : ∀ a ∈ A, 0 < a.1) (hM : weight A ≤ m) : weightedSum (listCount (m := m) A) = weight A := by
  induction A with
  | nil => simp [weightedSum, listCount]
  | cons a A ih =>
    have ha := hp a List.mem_cons_self
    have hp' : ∀ b ∈ A, 0 < b.1 := fun b hb => hp b (List.mem_cons_of_mem _ hb)
    have hM' : weight A ≤ m := by rw [weight_cons] at hM; omega
    have hle : a.1 ≤ m := by rw [weight_cons] at hM; omega
    rw [listCount_cons a A ha hle, weightedSum_add, ih hp' hM', weightedSum_single,
      Nat.mul_one, slotLength_arcSlot, weight_cons]
    exact Nat.add_comm _ _

-- Exact-weight inventory, padded with neutral unit-length arcs.
def compress (m : ℕ) (A : List Arc) (hp : ∀ a ∈ A, 0 < a.1) (hM : weight A ≤ m) : Inventory m :=
  pack m (fun p => listCount A p + padding m (m - weight A) p) (by
    rw [weightedSum_add, weightedSum_listCount m A hp hM, weightedSum_padding]
    · omega
    · intro h; omega)

lemma count_compress (m : ℕ) (A : List Arc) (hp : ∀ a ∈ A, 0 < a.1) (hM : weight A ≤ m)
    (p : Slot m) : count (compress m A hp hM) p = listCount A p + padding m (m - weight A) p := rfl

def zero (m : ℕ) : Inventory m := compress m [] (by simp) (by simp)

@[simp] lemma count_zero (m : ℕ) (p : Slot m) : count (zero m) p = padding m m p := by
  have e := count_compress m [] (by simp) (by simp [weight]) p
  change count (zero m) p = _ at e
  simpa [listCount, weight] using e

private lemma weightedSum_insert {m : ℕ} (inv : Inventory m) (a : Arc)
    (hp : 0 < a.1) (hle : a.1 ≤ m)
    (hs : a.1 ≤ count inv (padSlot (lt_of_lt_of_le hp hle))) :
    weightedSum (fun p => count inv p - padding m a.1 p + single (arcSlot a hp hle) 1 p) = m := by
  have he : (fun p => (count inv p - padding m a.1 p) + padding m a.1 p) = count inv := by
    rw [padding_eq_single (lt_of_lt_of_le hp hle)]
    funext p
    by_cases h : p = padSlot (lt_of_lt_of_le hp hle)
    · subst p
      simpa [single] using Nat.sub_add_cancel hs
    · simp [single, h]
  have hsum := congrArg weightedSum he
  rw [weightedSum_add, weightedSum_count,
    weightedSum_padding m a.1 (fun h => by omega)] at hsum
  rw [weightedSum_add, weightedSum_single, Nat.mul_one, slotLength_arcSlot, hsum]

-- Spend padding to add a positive arc, or leave the inventory unchanged when it does not fit.
def insert {m : ℕ} (inv : Inventory m) (a : Arc) : Inventory m :=
  if hp : 0 < a.1 ∧ a.1 ≤ m then
    if hs : a.1 ≤ count inv (padSlot (lt_of_lt_of_le hp.1 hp.2)) then
      pack m (fun p => count inv p - padding m a.1 p + single (arcSlot a hp.1 hp.2) 1 p)
        (weightedSum_insert inv a hp.1 hp.2 hs)
    else inv
  else inv

lemma insert_of_invalid {m : ℕ} (inv : Inventory m) (a : Arc) (h : ¬ (0 < a.1 ∧ a.1 ≤ m)) :
    insert inv a = inv := by simp [insert, h]

lemma insert_of_insufficient {m : ℕ} (inv : Inventory m) (a : Arc)
    (hp : 0 < a.1) (hle : a.1 ≤ m)
    (hs : count inv (padSlot (lt_of_lt_of_le hp hle)) < a.1) : insert inv a = inv := by
  simp only [insert, dite_eq_left (show 0 < a.1 ∧ a.1 ≤ m from ⟨hp, hle⟩),
    dite_eq_right (Nat.not_le.mpr hs)]

lemma count_insert_of_fits {m : ℕ} (inv : Inventory m) (a : Arc) (hp : 0 < a.1) (hle : a.1 ≤ m)
    (hs : a.1 ≤ count inv (padSlot (lt_of_lt_of_le hp hle))) (p : Slot m) :
    count (insert inv a) p = count inv p - padding m a.1 p + single (arcSlot a hp hle) 1 p := by
  simp only [insert, dite_eq_left (show 0 < a.1 ∧ a.1 ≤ m from ⟨hp, hle⟩),
    dite_eq_left hs, count_pack]

lemma compress_cons (m : ℕ) (a : Arc) (A : List Arc)
    (hp : ∀ b ∈ a :: A, 0 < b.1) (hM : weight (a :: A) ≤ m)
    (hp' : ∀ b ∈ A, 0 < b.1) (hM' : weight A ≤ m) :
    compress m (a :: A) hp hM = insert (compress m A hp' hM') a := by
  have ha := hp a List.mem_cons_self
  have hle : a.1 ≤ m := by rw [weight_cons] at hM; omega
  have hs : a.1 ≤ count (compress m A hp' hM') (padSlot (lt_of_lt_of_le ha hle)) := by
    rw [count_compress]
    have hh : a.1 + weight A ≤ m := hM
    simp only [padding, slotArc_padSlot, ite_true]
    omega
  apply inventory_ext
  intro p
  rw [count_insert_of_fits _ a ha hle hs, count_compress, count_compress,
    listCount_cons a A ha hle, weight_cons]
  have hh : a.1 + weight A ≤ m := hM
  by_cases h : slotArc p = pad <;> simp only [padding, h, ite_true, ite_false] <;> omega

section Product

variable {M : Type*} [CommMonoid M]

private lemma prod_single {m : ℕ} (F : Arc → M) (i : Slot m) :
    (∏ p : Slot m, F (slotArc p) ^ single i 1 p) = F (slotArc i) := by
  calc
    _ = ∏ p : Slot m, if p = i then F (slotArc p) else 1 := by
      apply Finset.prod_congr rfl
      intro p _
      by_cases h : p = i <;> simp [single, h]
    _ = _ := Fintype.prod_ite_eq' _ _

lemma prod_listCount (m : ℕ) (F : Arc → M) (A : List Arc)
    (hp : ∀ a ∈ A, 0 < a.1) (hM : weight A ≤ m) :
    (∏ p : Slot m, F (slotArc p) ^ listCount A p) = (A.map F).prod := by
  induction A with
  | nil => simp [listCount]
  | cons a A ih =>
    have ha := hp a List.mem_cons_self
    have hp' : ∀ b ∈ A, 0 < b.1 := fun b hb => hp b (List.mem_cons_of_mem _ hb)
    have hM' : weight A ≤ m := by rw [weight_cons] at hM; omega
    have hle : a.1 ≤ m := by rw [weight_cons] at hM; omega
    simp only [listCount_cons a A ha hle, pow_add, Finset.prod_mul_distrib, List.map_cons, List.prod_cons]
    rw [ih hp' hM', prod_single, slotArc_arcSlot]
    exact mul_comm _ _

-- If the padding arc has factor one, no length counter is needed to evaluate the product.
lemma prod_compress (m : ℕ) (F : Arc → M) (hpad : F pad = 1) (A : List Arc)
    (hp : ∀ a ∈ A, 0 < a.1) (hM : weight A ≤ m) :
    (∏ p : Slot m, F (slotArc p) ^ count (compress m A hp hM) p) = (A.map F).prod := by
  rw [← prod_listCount m F A hp hM]
  apply Finset.prod_congr rfl
  intro p _
  rw [count_compress]
  by_cases h : slotArc p = pad <;> simp [padding, h, hpad]

-- Remove the fictitious padding counts when the true used length is known.
def multiplicity {m : ℕ} (used : ℕ) (inv : Inventory m) (p : Slot m) : ℕ :=
  count inv p - padding m (m - used) p

@[simp] lemma multiplicity_compress (m : ℕ) (A : List Arc)
    (hp : ∀ a ∈ A, 0 < a.1) (hM : weight A ≤ m) (p : Slot m) :
    multiplicity (weight A) (compress m A hp hM) p = listCount A p := by
  simp [multiplicity, count_compress]

-- Arbitrary monoid factors, including a nontrivial factor at the padding slot.
lemma prod_compress_unpadded (m : ℕ) (F : Arc → M) (A : List Arc)
    (hp : ∀ a ∈ A, 0 < a.1) (hM : weight A ≤ m) :
    (∏ p : Slot m, F (slotArc p) ^ multiplicity (weight A) (compress m A hp hM) p) =
      (A.map F).prod := by
  simpa only [multiplicity_compress] using prod_listCount m F A hp hM

end Product
end StateCompression

namespace OrderCircuit

open Compiler.Build

variable {N m w : ℕ}

abbrev Prefix (N m : ℕ) := (Fin N → Bool) → TernaryWord m
abbrev Query (N m : ℕ) := (Fin N → Bool) → ℕ → TernaryWord m → ℕ

def digit (p : Prefix N m) (j : Fin m) (d : Fin 3) : Sig N := fun x => decide (p x j = d)

def prefixOut (p : Prefix N m) : Set (Sig N) := {f | ∃ j d, f = digit p j d}

def upd (p : Prefix N m) (j : Fin m) (d : Fin 3) : Prefix N m := fun x => Function.update (p x) j d

lemma upd_available {A : Set (Sig N)} (p : Prefix N m) (j : Fin m) (d : Fin 3)
    (hp : prefixOut p ⊆ A) (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    prefixOut (upd p j d) ⊆ A := by
  rintro _ ⟨i, a, rfl⟩
  by_cases hi : i = j
  · subst i
    have e : digit (upd p j d) j a = fun _ => decide (d = a) := by
      funext x
      simp [digit, upd]
    rw [e]
    by_cases h : d = a
    · simpa only [h, decide_true] using ht
    · simpa only [h, decide_false] using hf
  · have e : digit (upd p j d) i a = digit p i a := by
      funext x
      simp [digit, upd, Function.update_of_ne hi]
    rw [e]
    exact hp ⟨_, _, rfl⟩

def QueryBuild (A₀ : Set (Sig N)) (w c : ℕ) (count : Query N m) : Prop :=
  ∀ (A : Set (Sig N)), A₀ ⊆ A → ∀ (k : ℕ), k ≤ m → ∀ p : Prefix N m,
    prefixOut p ⊆ A → Build A (Set.range (bitsOf w (fun x => count x k (p x)))) c

abbrev Consts (A : Set (Sig N)) := (fun _ => false) ∈ A ∧ (fun _ => true) ∈ A

lemma queryPairB {A₀ A : Set (Sig N)} {c : ℕ} {count : Query N m} (Q : QueryBuild A₀ w c count)
    (hA : A₀ ⊆ A) (hc : Consts A) (p : Prefix N m) (hp : prefixOut p ⊆ A) (j : Fin m) :
    Build A (Set.range (bitsOf w (fun x => count x j.val (upd p j 0 x))) ∪
      Set.range (bitsOf w (fun x => count x j.val (upd p j 1 x)))) (2*c) := by
  simpa only [two_mul] using bothG (Q A hA _ j.isLt.le _ (upd_available p j 0 hp hc.1 hc.2))
    (Q A hA _ j.isLt.le _ (upd_available p j 1 hp hc.1 hc.2))

lemma offsetB {A : Set (Sig N)} (p : Prefix N m) (j : Fin m)
    (F G : (Fin N → Bool) → ℕ) (hc : Consts A) (hp : prefixOut p ⊆ A)
    (hF : Available A (bitsOf w F)) (hG : Available A (bitsOf w G)) :
    Build A (Set.range (bitsOf w (fun x => ternaryOffset (p x j) (F x) (G x)))) (11*w+1) := by
  let b₀ := nt (digit p j 0)
  let b₁ := digit p j 2
  let F' := fun x => if b₀ x then F x else 0
  let G' := fun x => if b₁ x then G x else 0
  have H₀ := notG (hp ⟨j,0,rfl⟩)
  have H₁ := bothG
    (bitGate (A := A ∪ {b₀}) (m := w) (p := b₀) (F := F) (Or.inr rfl) (fun i => Or.inl (hF i)))
    (bitGate (A := A ∪ {b₀}) (m := w) (p := b₁) (F := G) (Or.inl (hp ⟨j,2,rfl⟩)) (fun i => Or.inl (hG i)))
  have H₂ := sumTwoB (A := A ∪ ({b₀} ∪ (Set.range (bitsOf w F') ∪ Set.range (bitsOf w G'))))
    w F' G' (Or.inl hc.1) (fun i => Or.inr (Or.inr (Or.inl ⟨i,rfl⟩)))
    (fun i => Or.inr (Or.inr (Or.inr ⟨i,rfl⟩)))
  have eqn : (fun x => F' x + G' x) = (fun x => ternaryOffset (p x j) (F x) (G x)) := by
    funext x
    rcases three_digits (p x j) with h | h | h <;> simp [F',G',b₀,b₁,nt,digit,ternaryOffset,h]
  rw [← eqn]
  exact relax (thenG (seq H₀ H₁) H₂) le_rfl le_rfl (by omega)

lemma rankBuild {A : Set (Sig N)} {c : ℕ} {count : Query N m}
    (Q : QueryBuild A w c count) (hc : Consts A) (p : Prefix N m) (hp : prefixOut p ⊆ A) :
    Build A (Set.range (bitsOf w (fun x => ternaryRankFrom (count x) (p x) m))) (m*(2*c+20*w+1)) := by
  let O (k : ℕ) := Set.range (bitsOf w (fun x => ternaryRankFrom (count x) (p x) k))
  have hb : Build A (O 0) 0 := bitConst 0 hc.1 hc.2
  suffices H : Build A (O m) (0+m*(2*c+20*w+1)) by simpa only [Nat.zero_add] using H
  refine loopG O hb fun k hk => ?_
  let j : Fin m := ⟨k,hk⟩
  let F (x : Fin N → Bool) := count x k (upd p j 0 x)
  let G (x : Fin N → Bool) := count x k (upd p j 1 x)
  let T := Set.range (bitsOf w F) ∪ Set.range (bitsOf w G)
  let R (x : Fin N → Bool) := ternaryOffset (p x j) (F x) (G x)
  let B := A ∪ O k
  have H₀ : Build B T (2*c) := queryPairB Q Set.subset_union_left ⟨Or.inl hc.1,Or.inl hc.2⟩ p
    (hp.trans Set.subset_union_left) j
  have H₁ := offsetB (A := B ∪ T) p j F G ⟨Or.inl (Or.inl hc.1),Or.inl (Or.inl hc.2)⟩
    (hp.trans (Set.subset_union_left.trans Set.subset_union_left))
    (fun i => Or.inr (Or.inl ⟨i,rfl⟩)) (fun i => Or.inr (Or.inr ⟨i,rfl⟩))
  have H₂ := sumTwoB (A := B ∪ (T ∪ Set.range (bitsOf w R))) w R
    (fun x => ternaryRankFrom (count x) (p x) k) (Or.inl (Or.inl hc.1))
    (fun i => Or.inr (Or.inr ⟨i,rfl⟩)) (fun i => Or.inl (Or.inr ⟨i,rfl⟩))
  have eqn : O (k+1) = Set.range (bitsOf w (fun x => R x + ternaryRankFrom (count x) (p x) k)) := by
    simp only [O, ternaryRankFrom, dif_pos hk, R, F, G, j, upd]
  rw [eqn]
  exact relax (thenG (seq H₀ H₁) H₂) le_rfl le_rfl (by omega)

def selectedDigit (b₀ b₁ : Bool) : Fin 3 := if b₀ then 0 else if b₁ then 1 else 2

def selectResidual (t r : ℕ) : ℕ := if t ≤ r then r-t else r

lemma selectResidual_le (t r : ℕ) : selectResidual t r ≤ r := by
  unfold selectResidual
  split <;> omega

lemma choose_via_sub (c₀ c₁ r : ℕ) :
    ternaryChoose c₀ c₁ r =
      (selectedDigit (decide (r < c₀)) (decide (selectResidual c₀ r < c₁)),
       if r < c₀ then r else selectResidual c₁ (selectResidual c₀ r)) := by
  by_cases h₀ : r < c₀
  · simp [ternaryChoose, selectedDigit, h₀]
  · have hg : c₀ ≤ r := Nat.le_of_not_gt h₀
    by_cases h₁ : r < c₀+c₁
    · have ht : r-c₀ < c₁ := by omega
      simp [ternaryChoose, selectedDigit, selectResidual, h₀, h₁, hg, ht, not_le_of_gt ht]
    · have ht : c₁ ≤ r-c₀ := by omega
      simp [ternaryChoose, selectedDigit, selectResidual, h₀, h₁, hg, ht, not_lt_of_ge ht, Nat.sub_sub]

def chosenPrefix (p : Prefix N m) (j : Fin m) (b₀ b₁ : Sig N) : Prefix N m :=
  fun x => Function.update (p x) j (selectedDigit (b₀ x) (b₁ x))

lemma chosenPrefixB {A : Set (Sig N)} (p : Prefix N m) (j : Fin m) (b₀ b₁ : Sig N)
    (hp : prefixOut p ⊆ A) (h₀ : b₀ ∈ A) (h₁ : b₁ ∈ A) :
    Build A (prefixOut (chosenPrefix p j b₀ b₁)) 4 := by
  have H₀ := bothG (notG h₀) (notG h₁)
  let B := A ∪ ({nt b₀} ∪ {nt b₁})
  have H₁ := bothG (andG (A := B) (f := nt b₀) (g := b₁)
    (Or.inr (Or.inl rfl)) (Or.inl h₁))
    (andG (A := B) (f := nt b₀) (g := nt b₁) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))
  refine relaxKeep (seq H₀ H₁) le_rfl ?_ le_rfl
  rintro _ ⟨i,d,rfl⟩
  by_cases hi : i = j
  · subst i
    have e (d : Fin 3) : digit (chosenPrefix p j b₀ b₁) j d =
        if d = 0 then b₀ else if d = 1 then an (nt b₀) b₁ else an (nt b₀) (nt b₁) := by
      funext x
      rcases three_digits d with rfl | rfl | rfl <;> cases h₀ : b₀ x <;> cases h₁ : b₁ x <;>
        simp [digit, chosenPrefix, selectedDigit, an, nt, h₀, h₁] <;> decide
    rw [e]
    rcases three_digits d with rfl | rfl | rfl
    · exact Or.inl h₀
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · have e : digit (chosenPrefix p j b₀ b₁) i d = digit p i d := by
      funext x
      simp [digit, chosenPrefix, Function.update_of_ne hi]
    rw [e]
    exact Or.inl (hp ⟨i,d,rfl⟩)

abbrev SelState (N m : ℕ) := Prefix N m × ((Fin N → Bool) → ℕ)

def selectAdvance (count : Query N m) (j : Fin m) (s : SelState N m) : SelState N m :=
  let c₀ := fun x => count x j.val (upd s.1 j 0 x)
  let c₁ := fun x => count x j.val (upd s.1 j 1 x)
  (fun x => Function.update (s.1 x) j (ternaryChoose (c₀ x) (c₁ x) (s.2 x)).1,
   fun x => (ternaryChoose (c₀ x) (c₁ x) (s.2 x)).2)

def selectStage (count : Query N m) (r : (Fin N → Bool) → ℕ) : ℕ → SelState N m
  | 0 => (fun _ _ => 0, r)
  | k+1 => if h : k < m then selectAdvance count ⟨m-1-k, by omega⟩ (selectStage count r k)
    else selectStage count r k

lemma selectStage_residual (count : Query N m) (r : (Fin N → Bool) → ℕ) (j : ℕ)
    (x : Fin N → Bool) : (selectStage count r j).2 x ≤ r x := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    by_cases hj : j < m
    · rw [selectStage, dif_pos hj]
      simp only [selectAdvance, choose_via_sub]
      split
      · exact ih
      · exact (selectResidual_le _ _).trans ((selectResidual_le _ _).trans ih)
    · rw [selectStage, dif_neg hj]
      exact ih

lemma selectStage_spec (count : Query N m) (r : (Fin N → Bool) → ℕ) (x : Fin N → Bool) :
    (selectStage count r m).1 x = ternarySelectFrom (count x) m (fun _ => 0) (r x) := by
  suffices H : ∀ k ≤ m, let s := selectStage count r k
      ternarySelectFrom (count x) (m-k) (s.1 x) (s.2 x) =
        ternarySelectFrom (count x) m (fun _ => 0) (r x) by
    simpa only [Nat.sub_self, ternarySelectFrom] using H m le_rfl
  intro k hk
  induction k with
  | zero => simp [selectStage]
  | succ k ih =>
    have hk' : k < m := by omega
    rw [show m-k = (m-(k+1))+1 by omega] at ih
    simp only [ternarySelectFrom, show m-(k+1) < m by omega, dif_pos] at ih
    have hdiff : m-(k+1) = m-1-k := by omega
    simpa only [selectStage, dif_pos hk', selectAdvance, hdiff, upd] using ih hk'.le

def selOut (w : ℕ) (s : SelState N m) : Set (Sig N) := prefixOut s.1 ∪ Set.range (bitsOf w s.2)

lemma selectAdvanceB {A₀ A : Set (Sig N)} {c : ℕ} {count : Query N m}
    (Q : QueryBuild A₀ w c count) (hA : A₀ ⊆ A) (hc : Consts A)
    (hcount : ∀ x k p, count x k p < 2^w) (s : SelState N m)
    (hs : selOut w s ⊆ A) (hr : ∀ x, s.2 x < 2^w) (j : Fin m) :
    Build A (selOut w (selectAdvance count j s)) (2*c+32*w+24) := by
  let F := s.2
  let T₀ := fun x => count x j.val (upd s.1 j 0 x)
  let T₁ := fun x => count x j.val (upd s.1 j 1 x)
  let F₁ := fun x => selectResidual (T₀ x) (F x)
  let F₂ := fun x => selectResidual (T₁ x) (F₁ x)
  let b₀ := fun x => decide (F x < T₀ x)
  let b₁ := fun x => decide (F₁ x < T₁ x)
  let O₀ := Set.range (bitsOf w T₀) ∪ Set.range (bitsOf w T₁)
  let O₁ := Set.range (bitsOf w F₁) ∪ {b₀}
  let O₂ := Set.range (bitsOf w F₂) ∪ {b₁}
  let B := A ∪ O₀
  let C := A ∪ (O₀ ∪ O₁)
  let D := A ∪ ((O₀ ∪ O₁) ∪ O₂)
  have H₀ : Build A O₀ (2*c) := queryPairB Q hA hc s.1 (fun _ h => hs (Or.inl h)) j
  have H₁ : Build B O₁ (14*w+10) :=
    guardedSubB F T₀ (Or.inl hc.1) (Or.inl hc.2) (fun i => Or.inl (hs (Or.inr ⟨i,rfl⟩)))
      (fun i => Or.inr (Or.inl ⟨i,rfl⟩)) hr (fun x => hcount x _ _)
  have H₂ : Build C O₂ (14*w+10) :=
    guardedSubB F₁ T₁ (Or.inl hc.1) (Or.inl hc.2)
      (fun i => Or.inr (Or.inr (Or.inl ⟨i,rfl⟩))) (fun i => Or.inr (Or.inl (Or.inr ⟨i,rfl⟩)))
      (fun x => (selectResidual_le _ _).trans_lt (hr x)) (fun x => hcount x _ _)
  have hb₀ : b₀ ∈ D := Or.inr (Or.inl (Or.inr (Or.inr rfl)))
  have hb₁ : b₁ ∈ D := Or.inr (Or.inr (Or.inr rfl))
  have H₃ := chosenPrefixB s.1 j b₀ b₁ (A := D) (fun _ h => Or.inl (hs (Or.inl h))) hb₀ hb₁
  have H₄ := wordMuxG (A := D) (s := b₀) (v := bitsOf w F₂) (u := bitsOf w F) hb₀
    (fun i => Or.inr (Or.inr (Or.inl ⟨i,rfl⟩))) (fun i => Or.inl (hs (Or.inr ⟨i,rfl⟩)))
  have ep : (selectAdvance count j s).1 = chosenPrefix s.1 j b₀ b₁ := by
    funext x
    simp only [selectAdvance, choose_via_sub, chosenPrefix, b₀, b₁, F₁, T₀, T₁, F]
  have ew : bitsOf w (selectAdvance count j s).2 = fun i => mx b₀ (bitsOf w F₂ i) (bitsOf w F i) := by
    funext i x
    by_cases h : F x < T₀ x <;>
      simp [bitsOf, selectAdvance, choose_via_sub, mx, b₀, F, T₀, T₁, F₁, F₂, h]
  have H₅ := thenG (seq (seq H₀ H₁) H₂) (bothG H₃ H₄)
  rw [selOut, ep, ew]
  exact relax H₅ le_rfl le_rfl (by omega)

lemma selectBuild {A : Set (Sig N)} {c : ℕ} {count : Query N m}
    (Q : QueryBuild A w c count) (hc : Consts A)
    (hcount : ∀ x k p, count x k p < 2^w)
    (r : (Fin N → Bool) → ℕ) (hr : Available A (bitsOf w r)) (hrb : ∀ x, r x < 2^w) :
    Build A (prefixOut (fun x => ternarySelectFrom (count x) m (fun _ => 0) (r x)))
      (m*(2*c+32*w+24)) := by
  let O (k : ℕ) := selOut w (selectStage count r k)
  have hb : Build A (O 0) 0 := by
    apply idle
    rintro _ (⟨j,d,rfl⟩ | ⟨i,rfl⟩)
    · by_cases h : (0 : Fin 3) = d
      · have e : digit (selectStage count r 0).1 j d = fun _ => true := by funext x; simp [digit, selectStage, h]
        exact e ▸ hc.2
      · have e : digit (selectStage count r 0).1 j d = fun _ => false := by funext x; simp [digit, selectStage, h]
        exact e ▸ hc.1
    · exact hr i
  have H := loopG (t := m) O hb (fun k hk => by
    rw [show O (k+1) = selOut w (selectAdvance count ⟨m-1-k, by omega⟩ (selectStage count r k)) from by
      simp only [O, selectStage, dif_pos hk]]
    exact selectAdvanceB Q Set.subset_union_left ⟨Or.inl hc.1,Or.inl hc.2⟩ hcount _
      Set.subset_union_right (fun x => (selectStage_residual count r k x).trans_lt (hrb x)) _)
  have e : (fun x => ternarySelectFrom (count x) m (fun _ => 0) (r x)) = (selectStage count r m).1 :=
    funext fun x => (selectStage_spec count r x).symm
  rw [e]
  exact relax H le_rfl Set.subset_union_left (by simp)

end OrderCircuit

namespace ProfileFactor

-- Compare the signed arc product at pin 5edaa5b98fcb8850538e82d2b7aa2d998868830f,
-- lean/PEqualNP/Outside/L_pcx_399.lean, and the segment convolution at the same pin,
-- lean/PEqualNP/Outside/L_pcx_375.lean. Here the port product works directly in
-- the nonnegative coefficient semiring and follows a left-to-right scan.

abbrev Arc := ℕ × Bool × Bool
abbrev Ports (R : Type*) := Bool → Bool → R

variable {R : Type*} [CommSemiring R]

open scoped BigOperators

def colorAt (c : Bool) (k : ℕ) : Bool := if k % 2 = 0 then c else !c

lemma colorAt_zero (c : Bool) : colorAt c 0 = c := by simp [colorAt]

lemma colorAt_succ (c : Bool) (k : ℕ) : colorAt c (k + 1) = !colorAt c k := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have h' : (k + 1) % 2 = 1 := by omega
    simp [colorAt, h, h']
  · have h' : (k + 1) % 2 = 0 := by omega
    simp [colorAt, h, h']

lemma colorAt_flip (c : Bool) (k : ℕ) : colorAt (!c) k = !colorAt c k := by
  by_cases h : k % 2 = 0 <;> simp [colorAt, h]

lemma colorAt_add (c : Bool) (m k : ℕ) :
    colorAt c (m + k) = colorAt (colorAt c m) k := by
  induction k with
  | zero => simp [colorAt_zero]
  | succ k ih => rw [← Nat.add_assoc, colorAt_succ, colorAt_succ, ih]

lemma colorAt_even (c : Bool) {k : ℕ} (he : k % 2 = 0) : colorAt c k = c := by
  simp [colorAt, he]

def portId : Ports R := fun a b => if a = b then 1 else 0

def portComp (A B : Ports R) : Ports R := fun a b => ∑ v : Bool, A a v * B v b

lemma portComp_left_id (A : Ports R) : portComp portId A = A := by
  funext a b
  simp [portComp, portId, ite_mul]

lemma portComp_right_id (A : Ports R) : portComp A portId = A := by
  funext a b
  simp [portComp, portId, mul_ite, eq_comm]

lemma portComp_assoc (A B C : Ports R) :
    portComp (portComp A B) C = portComp A (portComp B C) := by
  funext a b
  simp only [portComp, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

def portTrace (A : Ports R) : R := ∑ a : Bool, A a a

def edgePort (w : Bool → R) (c : Bool) : Ports R :=
  fun a b => if a = b then 1 else w c

def letter (w : Bool → R) (c : Bool) (p : Option Bool) : Ports R :=
  fun a b => if p = none ∨ p = some a then edgePort w c a b else 0

lemma letter_none (w : Bool → R) (c : Bool) : letter w c none = edgePort w c := by
  funext a b
  simp [letter]

lemma portComp_letter_some (A : Ports R) (w : Bool → R) (c p a b : Bool) :
    portComp A (letter w c (some p)) a b = A a p * edgePort w c p b := by
  cases p <;> simp [portComp, letter, Fintype.sum_bool]

lemma portComp_rank_one (u v : Bool → R) (A : Ports R) (a b : Bool) :
    portComp (fun i j => u i * v j) A a b = u a * portComp (fun _ j => v j) A a b := by
  simp only [portComp, Finset.mul_sum, mul_assoc]

def freePath (w : Bool → R) : Bool → ℕ → Ports R
  | _, 0 => portId
  | c, k + 1 => portComp (edgePort w c) (freePath w (!c) k)

lemma freePath_one (w : Bool → R) (c : Bool) : freePath w c 1 = edgePort w c := by
  simpa only [freePath] using portComp_right_id (edgePort w c)

lemma freePath_add (w : Bool → R) (c : Bool) (m k : ℕ) :
    freePath w c (m + k) = portComp (freePath w c m) (freePath w (colorAt c m) k) := by
  induction m generalizing c with
  | zero => simp [freePath, colorAt_zero, portComp_left_id]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [freePath, colorAt_succ, ← colorAt_flip, portComp_assoc]
    rw [ih]

lemma freePath_appendEdge (w : Bool → R) (c : Bool) (k : ℕ) :
    portComp (freePath w c k) (edgePort w (colorAt c k)) = freePath w c (k + 1) := by
  rw [freePath_add, freePath_one]

lemma freePath_flip (w : Bool → R) (c : Bool) (k : ℕ) (a b : Bool) :
    freePath w c k (!a) (!b) = freePath w c k a b := by
  induction k generalizing c a b with
  | zero => cases a <;> cases b <;> rfl
  | succ k ih =>
    have h₀ := ih (!c) false b
    have h₁ := ih (!c) true b
    cases a <;> cases b <;>
      simp [freePath, portComp, Fintype.sum_bool, edgePort] at h₀ h₁ ⊢ <;>
      rw [h₀, h₁] <;> ac_rfl

def arcFactor (w : Bool → R) (q : Arc) : R := freePath w q.2.1 q.1 false q.2.2

lemma freePath_eq_arcFactor (w : Bool → R) (c : Bool) (k : ℕ) (a b : Bool) :
    freePath w c k a b = arcFactor w (k, c, Bool.xor a b) := by
  cases a <;> cases b
  · rfl
  · rfl
  · exact freePath_flip w c k false true
  · exact freePath_flip w c k false false

lemma arcFactor_zero (w : Bool → R) (c p : Bool) :
    arcFactor w (0, c, p) = if p = false then 1 else 0 := by
  cases p <;> simp [arcFactor, freePath, portId]

lemma arcFactor_succ (w : Bool → R) (c p : Bool) (k : ℕ) :
    arcFactor w (k + 1, c, p) =
      arcFactor w (k, !c, p) + w c * arcFactor w (k, !c, !p) := by
  have h : freePath w (!c) k true p = arcFactor w (k, !c, !p) := by
    cases p <;> exact freePath_eq_arcFactor w (!c) k true _
  calc
    _ = w c * freePath w (!c) k true p + arcFactor w (k, !c, p) := by
      simp [arcFactor, freePath, portComp, Fintype.sum_bool, edgePort]
    _ = _ := by rw [h, add_comm]

def wordPorts (w : Bool → R) : Bool → List (Option Bool) → Ports R
  | _, [] => portId
  | c, p :: ps => portComp (letter w c p) (wordPorts w (!c) ps)

lemma wordPorts_append (w : Bool → R) (c : Bool) (L M : List (Option Bool)) :
    wordPorts w c (L ++ M) = portComp (wordPorts w c L) (wordPorts w (colorAt c L.length) M) := by
  induction L generalizing c with
  | nil => simp [wordPorts, colorAt_zero, portComp_left_id]
  | cons p L ih =>
    simp only [List.cons_append, List.length_cons, wordPorts, colorAt_succ, ← colorAt_flip,
      portComp_assoc]
    rw [ih]

-- Open data: leading span length, first pin, trailing span length, last pin,
-- and color of the first edge of the trailing span.
abbrev OpenData := ℕ × Bool × ℕ × Bool × Bool

-- State fields: position, open data, completed (non-wraparound) arcs.
abbrev Scan := ℕ × Option OpenData × List Arc

def scanStep (c : Bool) : Scan → Option Bool → Scan
  | (k, none, A), none => (k + 1, none, A)
  | (k, none, A), some a => (k + 1, some (k, a, 1, a, colorAt c k), A)
  | (k, some (f, a, l, b, d), A), none => (k + 1, some (f, a, l + 1, b, d), A)
  | (k, some (f, a, l, b, d), A), some p =>
    (k + 1, some (f, a, 1, p, colorAt c k), (l, d, Bool.xor b p) :: A)

def scanWord (c : Bool) (L : List (Option Bool)) : Scan :=
  L.foldl (scanStep c) (0, none, [])

def arcLength (A : List Arc) : ℕ := (A.map Prod.fst).sum

def arcProduct (w : Bool → R) (A : List Arc) : R := (A.map (arcFactor w)).prod

def scanGood (c : Bool) : Scan → Prop
  | (k, o, A) => (∀ q ∈ A, 0 < q.1) ∧
    match o with
    | none => A = []
    | some (f, _, l, _, d) => 0 < l ∧ f + l + arcLength A = k ∧ colorAt d l = colorAt c k

def scanPorts (w : Bool → R) (c : Bool) : Scan → Ports R
  | (k, none, _) => freePath w c k
  | (_, some (f, a, l, b, d), A) => fun u v =>
    (arcProduct w A * freePath w c f u a) * freePath w d l b v

lemma scanStep_pos (c : Bool) (s : Scan) (p : Option Bool) :
    (scanStep c s p).1 = s.1 + 1 := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩ <;> cases p <;> rfl

lemma scanStep_good (c : Bool) (s : Scan) (p : Option Bool) (h : scanGood c s) :
    scanGood c (scanStep c s p) := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · obtain ⟨hpos, he⟩ := h
    cases p with
    | none => exact ⟨hpos, he⟩
    | some a =>
      subst A
      exact ⟨hpos, by simp [scanGood, arcLength, colorAt_succ, colorAt_zero]⟩
  · obtain ⟨hpos, hl, hk, hd⟩ := h
    cases p with
    | none =>
      exact ⟨hpos, by
        refine ⟨by omega, by omega, ?_⟩
        rw [colorAt_succ, colorAt_succ, hd]⟩
    | some p =>
      refine ⟨?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with hq | hq
        · subst q; exact hl
        · exact hpos q hq
      · refine ⟨by decide, ?_, ?_⟩
        · simp [arcLength] at hk ⊢
          omega
        · simp [colorAt_succ, colorAt_zero]

lemma scanStep_ports (w : Bool → R) (c : Bool) (s : Scan) (p : Option Bool)
    (h : scanGood c s) :
    scanPorts w c (scanStep c s p) = portComp (scanPorts w c s) (letter w (colorAt c s.1) p) := by
  funext u v
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · cases p with
    | none =>
      change freePath w c (k + 1) u v = portComp (freePath w c k) (letter w (colorAt c k) none) u v
      rw [letter_none, freePath_appendEdge]
    | some a =>
      have he : A = [] := h.2
      subst A
      change ((1 : R) * freePath w c k u a) * freePath w (colorAt c k) 1 a v =
        portComp (freePath w c k) (letter w (colorAt c k) (some a)) u v
      rw [portComp_letter_some, freePath_one, one_mul]
  · obtain ⟨_, _, _, hd⟩ := h
    cases p with
    | none =>
      change (arcProduct w A * freePath w c f u a) * freePath w d (l + 1) b v =
        portComp (fun i j => (arcProduct w A * freePath w c f i a) * freePath w d l b j)
          (letter w (colorAt c k) none) u v
      rw [letter_none, portComp_rank_one, ← hd, ← freePath_appendEdge] <;> rfl
    | some p =>
      change ((arcFactor w (l, d, Bool.xor b p) * arcProduct w A) * freePath w c f u a) *
          freePath w (colorAt c k) 1 p v =
        portComp (fun i j => (arcProduct w A * freePath w c f i a) * freePath w d l b j)
          (letter w (colorAt c k) (some p)) u v
      rw [portComp_letter_some, freePath_one, freePath_eq_arcFactor w d l b p]
      ac_rfl

lemma scanWord_spec (w : Bool → R) (c : Bool) (L : List (Option Bool)) :
    (scanWord c L).1 = L.length ∧ scanGood c (scanWord c L) ∧
    scanPorts w c (scanWord c L) = wordPorts w c L := by
  induction L using List.reverseRecOn with
  | nil => simp [scanWord, scanGood, scanPorts, wordPorts, freePath]
  | append_singleton L p ih =>
    obtain ⟨hk, hg, hp⟩ := ih
    have hs : scanWord c (L ++ [p]) = scanStep c (scanWord c L) p := by
      simp [scanWord, List.foldl_append]
    refine ⟨by simp [hs, scanStep_pos, hk], ?_, ?_⟩
    · rw [hs]
      exact scanStep_good c _ p hg
    · rw [hs, scanStep_ports _ _ _ _ hg, hp, hk, wordPorts_append]
      simp [wordPorts, portComp_right_id]

-- The first coordinate is the number of completely free cycles, zero or one.
def closeScan (c : Bool) : Scan → ℕ × List Arc
  | (k, none, _) => (1, [(k, c, false)])
  | (_, some (f, a, l, b, d), A) => (0, (l + f, d, Bool.xor b a) :: A)

lemma closeScan_length (c : Bool) (s : Scan) (hg : scanGood c s) :
    arcLength (closeScan c s).2 = s.1 := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · simp [closeScan, arcLength]
  · obtain ⟨_, _, hk, _⟩ := hg
    simp [closeScan, arcLength] at hk ⊢
    omega

lemma closeScan_positive (c : Bool) (s : Scan) (hg : scanGood c s) (hk : 0 < s.1) :
    ∀ q ∈ (closeScan c s).2, 0 < q.1 := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · simpa [closeScan] using hk
  · obtain ⟨hA, hl, _, _⟩ := hg
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst q
      change 0 < l + f
      omega
    · exact hA q hq

lemma closeScan_factor (w : Bool → R) (c : Bool) (s : Scan)
    (hg : scanGood c s) (he : s.1 % 2 = 0) :
    portTrace (scanPorts w c s) = (2 : R) ^ (closeScan c s).1 * arcProduct w (closeScan c s).2 := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · change (∑ x : Bool, freePath w c k x x) = (2 : R) ^ 1 * (arcFactor w (k, c, false) * 1)
    have h : freePath w c k true true = freePath w c k false false :=
      freePath_flip w c k false false
    rw [Fintype.sum_bool, pow_one, mul_one, two_mul, h] <;> rfl
  · obtain ⟨_, _, _, hd⟩ := hg
    change k % 2 = 0 at he
    have hc : colorAt d l = c := hd.trans (colorAt_even c he)
    have H : (∑ x : Bool, (arcProduct w A * freePath w c f x a) * freePath w d l b x) =
        arcProduct w A * portComp (freePath w d l) (freePath w c f) b a := by
      simp only [portComp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ac_rfl
    change (∑ x : Bool, (arcProduct w A * freePath w c f x a) * freePath w d l b x) =
        (2 : R) ^ 0 * (arcFactor w (l + f, d, Bool.xor b a) * arcProduct w A)
    rw [H, ← hc, ← freePath_add, freePath_eq_arcFactor w d (l + f) b a, pow_zero, one_mul, mul_comm]

lemma cycle_factor (w : Bool → R) (c : Bool) (L : List (Option Bool)) (he : L.length % 2 = 0) :
    portTrace (wordPorts w c L) =
      (2 : R) ^ (closeScan c (scanWord c L)).1 * arcProduct w (closeScan c (scanWord c L)).2 := by
  obtain ⟨hk, hg, hp⟩ := scanWord_spec w c L
  rw [← hp]
  apply closeScan_factor w c _ hg
  rw [hk]
  exact he

lemma scanWord_valid (c : Bool) (L : List (Option Bool)) :
    (scanWord c L).1 = L.length ∧ scanGood c (scanWord c L) :=
  let h := scanWord_spec (fun _ => (0 : ℕ)) c L
  ⟨h.1, h.2.1⟩

lemma scanPartial_length (c : Bool) (s : Scan) (hg : scanGood c s) :
    arcLength s.2.2 ≤ s.1 := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · have h : A = [] := hg.2
    simp [h, arcLength]
  · obtain ⟨_, _, hk, _⟩ := hg
    change arcLength A ≤ k
    omega

lemma scanPartial_positive (c : Bool) (s : Scan) (hg : scanGood c s) :
    ∀ q ∈ s.2.2, 0 < q.1 := by
  rcases s with ⟨k, o, A⟩
  exact hg.1

lemma scanWord_partial (c : Bool) (L : List (Option Bool)) :
    arcLength (scanWord c L).2.2 ≤ L.length ∧ ∀ q ∈ (scanWord c L).2.2, 0 < q.1 := by
  obtain ⟨hk, hg⟩ := scanWord_valid c L
  exact ⟨(scanPartial_length c _ hg).trans_eq hk, scanPartial_positive c _ hg⟩

lemma cycle_inventory_bounds (c : Bool) (L : List (Option Bool)) (hn : 0 < L.length) :
    arcLength (closeScan c (scanWord c L)).2 = L.length ∧
      ∀ q ∈ (closeScan c (scanWord c L)).2, 0 < q.1 := by
  obtain ⟨hk, hg⟩ := scanWord_valid c L
  refine ⟨(closeScan_length c _ hg).trans hk, closeScan_positive c _ hg ?_⟩
  rwa [hk]

lemma tailColor_eq_lastOffset (c : Bool) (k : ℕ) (f : ℕ) (a : Bool)
    (l : ℕ) (b d : Bool) (A : List Arc)
    (hg : scanGood c (k, some (f, a, l, b, d), A)) :
    l ≤ k ∧ d = colorAt c (k - l) := by
  obtain ⟨_, _, hk, hd⟩ := hg
  have hle : l ≤ k := by omega
  refine ⟨hle, ?_⟩
  have h := calc
    colorAt d l = colorAt c k := hd
    _ = colorAt c (k - l + l) := by rw [Nat.sub_add_cancel hle]
    _ = colorAt (colorAt c (k - l)) l := colorAt_add _ _ _
  by_cases hl : l % 2 = 0
  · simpa [colorAt, hl] using h
  · exact Bool.not_injective (by simpa only [colorAt, if_neg hl] using h)

-- Equivalent open fields with two absolute offsets, rather than trailing length.
abbrev OffsetScan := ℕ × Option (ℕ × Bool × ℕ × Bool) × List Arc

def offsetView : Scan → OffsetScan
  | (k, none, A) => (k, none, A)
  | (k, some (f, a, l, b, _), A) => (k, some (f, a, k - l, b), A)

def offsetStep (c : Bool) : OffsetScan → Option Bool → OffsetScan
  | (k, o, A), none => (k + 1, o, A)
  | (k, none, A), some a => (k + 1, some (k, a, k, a), A)
  | (k, some (f, a, l, b), A), some p =>
    (k + 1, some (f, a, k, p), (k - l, colorAt c l, Bool.xor b p) :: A)

def offsetClose (c : Bool) : OffsetScan → ℕ × List Arc
  | (k, none, _) => (1, [(k, c, false)])
  | (k, some (f, a, l, b), A) => (0, (k - l + f, colorAt c l, Bool.xor b a) :: A)

lemma offsetView_step (c : Bool) (s : Scan) (p : Option Bool) (h : scanGood c s) :
    offsetView (scanStep c s p) = offsetStep c (offsetView s) p := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · cases p <;> simp [offsetView, scanStep, offsetStep]
  · obtain ⟨hle, hc⟩ := tailColor_eq_lastOffset c k f a l b d A h
    cases p with
    | none =>
      have hs : k + 1 - (l + 1) = k - l := by omega
      simp [offsetView, scanStep, offsetStep, hs]
    | some p =>
      have hs : k - (k - l) = l := by omega
      simp [offsetView, scanStep, offsetStep, hs, hc]

lemma offsetView_close (c : Bool) (s : Scan) (h : scanGood c s) :
    offsetClose c (offsetView s) = closeScan c s := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · rfl
  · obtain ⟨hle, hc⟩ := tailColor_eq_lastOffset c k f a l b d A h
    have hs : k - (k - l) = l := by omega
    simp [offsetClose, offsetView, closeScan, hs, hc]

def offsetWord (c : Bool) (L : List (Option Bool)) : OffsetScan :=
  L.foldl (offsetStep c) (0, none, [])

lemma offsetWord_eq (c : Bool) (L : List (Option Bool)) :
    offsetWord c L = offsetView (scanWord c L) := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L p ih =>
    unfold offsetWord scanWord
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change offsetStep c (offsetWord c L) p = offsetView (scanStep c (scanWord c L) p)
    rw [ih, offsetView_step c _ p (scanWord_valid c L).2]

lemma offsetWord_close (c : Bool) (L : List (Option Bool)) :
    offsetClose c (offsetWord c L) = closeScan c (scanWord c L) := by
  rw [offsetWord_eq, offsetView_close c _ (scanWord_valid c L).2]

lemma offsetView_fields (c : Bool) (s : Scan) (hg : scanGood c s) :
    (offsetView s).1 = s.1 ∧ (offsetView s).2.2 = s.2.2 ∧
      (match (offsetView s).2.1 with
       | none => s.2.2 = []
       | some (f, _, l, _) => f ≤ l ∧ l < s.1 ∧ f + (s.1 - l) + arcLength s.2.2 = s.1) := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · exact ⟨rfl, rfl, hg.2⟩
  · obtain ⟨_, hl, hk, _⟩ := hg
    refine ⟨rfl, rfl, ?_⟩
    change f ≤ k - l ∧ k - l < k ∧ f + (k - (k - l)) + arcLength A = k
    omega

lemma offsetWord_fields (c : Bool) (L : List (Option Bool)) :
    (offsetWord c L).1 = L.length ∧
      arcLength (offsetWord c L).2.2 ≤ L.length ∧
      (∀ q ∈ (offsetWord c L).2.2, 0 < q.1) ∧
      (match (offsetWord c L).2.1 with
       | none => (offsetWord c L).2.2 = []
       | some (f, _, l, _) =>
          f ≤ l ∧ l < L.length ∧ f + (L.length - l) + arcLength (offsetWord c L).2.2 = L.length) := by
  obtain ⟨hk, hg⟩ := scanWord_valid c L
  obtain ⟨hp, ha, hb⟩ := offsetView_fields c _ hg
  obtain ⟨hl, hpos⟩ := scanWord_partial c L
  rw [offsetWord_eq, ha]
  rw [hk] at hb
  exact ⟨hp.trans hk, hl, hpos, hb⟩

lemma offset_inventory_bounds (c : Bool) (L : List (Option Bool)) (hn : 0 < L.length) :
    arcLength (offsetClose c (offsetWord c L)).2 = L.length ∧
      ∀ q ∈ (offsetClose c (offsetWord c L)).2, 0 < q.1 := by
  rw [offsetWord_close]
  exact cycle_inventory_bounds c L hn

lemma offset_cycle_factor (w : Bool → R) (c : Bool) (L : List (Option Bool)) (he : L.length % 2 = 0) :
    portTrace (wordPorts w c L) =
      (2 : R) ^ (offsetClose c (offsetWord c L)).1 * arcProduct w (offsetClose c (offsetWord c L)).2 := by
  rw [offsetWord_close]
  exact cycle_factor w c L he

lemma offsetStep_no_pin (c : Bool) (s : OffsetScan) (p : Option Bool) :
    (offsetStep c s p).2.1 = none ↔ s.2.1 = none ∧ p = none := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b⟩ <;> cases p <;> simp [offsetStep]

lemma offsetWord_no_pin (c : Bool) (L : List (Option Bool)) :
    (offsetWord c L).2.1 = none ↔ ∀ p ∈ L, p = none := by
  induction L using List.reverseRecOn with
  | nil => simp [offsetWord]
  | append_singleton L p ih =>
    have h : offsetWord c (L ++ [p]) = offsetStep c (offsetWord c L) p := by
      simp [offsetWord, List.foldl_append]
    rw [h, offsetStep_no_pin, ih]
    constructor
    · rintro ⟨hL, rfl⟩ q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hL q hq
      · simpa using hq
    · intro hh
      exact ⟨fun q hq => hh q (List.mem_append_left _ hq), hh p (by simp)⟩

lemma offsetClose_one_iff (c : Bool) (s : OffsetScan) :
    (offsetClose c s).1 = 1 ↔ s.2.1 = none := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b⟩ <;> simp [offsetClose]

lemma offsetCycle_free (c : Bool) (L : List (Option Bool)) :
    (offsetClose c (offsetWord c L)).1 = 1 ↔ ∀ p ∈ L, p = none := by
  rw [offsetClose_one_iff, offsetWord_no_pin]

lemma arcProduct_append (w : Bool → R) (A B : List Arc) :
    arcProduct w (A ++ B) = arcProduct w A * arcProduct w B := by
  simp [arcProduct, List.prod_append]

lemma arcLength_append (A B : List Arc) :
    arcLength (A ++ B) = arcLength A + arcLength B := by
  simp [arcLength, List.sum_append]

lemma arcLength_ge (A : List Arc) (q : Arc) (hq : q ∈ A) : q.1 ≤ arcLength A := by
  induction A with
  | nil => simp at hq
  | cons a A ih =>
    simp only [arcLength, List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hq with hq | hq
    · subst a; omega
    · have hh := ih hq
      unfold arcLength at hh
      omega

def arcUniverse (M : ℕ) : Finset Arc :=
  (Finset.Icc 1 M).product (Finset.univ : Finset (Bool × Bool))

lemma arcProduct_inventory (w : Bool → R) (A : List Arc) (M : ℕ)
    (hp : ∀ q ∈ A, 0 < q.1) (hM : arcLength A ≤ M) :
    arcProduct w A = ∏ q ∈ arcUniverse M, arcFactor w q ^ A.count q := by
  rw [arcProduct, Finset.prod_list_map_count]
  refine Finset.prod_subset ?_ ?_
  · intro q hq
    have hq' := List.mem_toFinset.mp hq
    simp [arcUniverse, Nat.succ_le_of_lt (hp q hq'), le_trans (arcLength_ge A q hq') hM]
  · intro q _ hq
    rw [List.count_eq_zero_of_not_mem (fun h => hq (List.mem_toFinset.mpr h)), pow_zero]

abbrev CycleWord := Bool × List (Option Bool)

def layoutArcs (W : List CycleWord) : List Arc :=
  (W.map fun (c, L) => (offsetClose c (offsetWord c L)).2).flatten

def layoutFree (W : List CycleWord) : ℕ :=
  (W.map fun (c, L) => (offsetClose c (offsetWord c L)).1).sum

lemma layout_factor (w : Bool → R) (W : List CycleWord)
    (he : ∀ q ∈ W, q.2.length % 2 = 0) :
    (W.map fun (c, L) => portTrace (wordPorts w c L)).prod =
      (2 : R) ^ layoutFree W * arcProduct w (layoutArcs W) := by
  induction W with
  | nil => simp [layoutFree, layoutArcs, arcProduct]
  | cons q W ih =>
    obtain ⟨c, L⟩ := q
    have hq := offset_cycle_factor w c L (he (c, L) (List.mem_cons_self ..))
    have ht := ih (fun q hq => he q (List.mem_cons_of_mem _ hq))
    simp only [layoutFree, layoutArcs, List.map_cons, List.sum_cons, List.flatten_cons,
      List.prod_cons, pow_add, arcProduct_append]
    rw [hq, ht]
    unfold layoutArcs layoutFree
    ac_rfl

lemma layout_inventory_bounds (W : List CycleWord) (hn : ∀ q ∈ W, 0 < q.2.length) :
    arcLength (layoutArcs W) = (W.map fun q => q.2.length).sum ∧
      ∀ q ∈ layoutArcs W, 0 < q.1 := by
  induction W with
  | nil => simp [layoutArcs, arcLength]
  | cons q W ih =>
    obtain ⟨c, L⟩ := q
    obtain ⟨hl, hp⟩ := offset_inventory_bounds c L (hn (c, L) (List.mem_cons_self ..))
    obtain ⟨ht, htp⟩ := ih (fun q hq => hn q (List.mem_cons_of_mem _ hq))
    change arcLength ((offsetClose c (offsetWord c L)).2 ++ layoutArcs W) =
      L.length + (W.map fun q => q.2.length).sum ∧
      ∀ q ∈ (offsetClose c (offsetWord c L)).2 ++ layoutArcs W, 0 < q.1
    refine ⟨by rw [arcLength_append, hl, ht], ?_⟩
    intro q hq
    exact (List.mem_append.mp hq).elim (hp q) (htp q)

lemma layout_factor_inventory (w : Bool → R) (W : List CycleWord) (M : ℕ)
    (he : ∀ q ∈ W, q.2.length % 2 = 0) (hn : ∀ q ∈ W, 0 < q.2.length)
    (hM : (W.map fun q => q.2.length).sum ≤ M) :
    (W.map fun (c, L) => portTrace (wordPorts w c L)).prod =
      (2 : R) ^ layoutFree W * ∏ q ∈ arcUniverse M, arcFactor w q ^ (layoutArcs W).count q := by
  obtain ⟨hl, hp⟩ := layout_inventory_bounds W hn
  rw [layout_factor w W he, arcProduct_inventory w _ M hp (hl.le.trans hM)]

def headBit {m : ℕ} (x : Fin m → Bool) (b : Bool) : Bool :=
  if h : 0 < m then x ⟨0, h⟩ else b

def nextBit {m : ℕ} (x : Fin m → Bool) (b : Bool) (i : Fin m) : Bool :=
  if h : i.val + 1 < m then x ⟨i.val + 1, h⟩ else b

lemma headBit_cons {m : ℕ} (a : Bool) (x : Fin m → Bool) (b : Bool) :
    headBit (Fin.cons a x) b = a := by
  simp [headBit]

lemma nextBit_cons_zero {m : ℕ} (a : Bool) (x : Fin m → Bool) (b : Bool) :
    nextBit (Fin.cons a x) b 0 = headBit x b := by
  by_cases hm : 0 < m
  · have h : 1 < m + 1 := by omega
    rw [nextBit, dif_pos (show (0 : Fin (m + 1)).val + 1 < m + 1 from h), headBit, dif_pos hm]
    exact Fin.cons_succ (α := fun _ : Fin (m + 1) => Bool) a x ⟨0, hm⟩
  · have h : ¬1 < m + 1 := by omega
    simp [nextBit, headBit, h, hm]

lemma nextBit_cons_succ {m : ℕ} (a : Bool) (x : Fin m → Bool) (b : Bool) (i : Fin m) :
    nextBit (Fin.cons a x) b i.succ = nextBit x b i := by
  by_cases hm : i.val + 1 < m
  · have h : i.val + 1 + 1 < m + 1 := by omega
    rw [nextBit, dif_pos (show i.succ.val + 1 < m + 1 from h), nextBit, dif_pos hm]
    exact Fin.cons_succ (α := fun _ : Fin (m + 1) => Bool) a x ⟨i.val + 1, hm⟩
  · have h : ¬i.val + 1 + 1 < m + 1 := by omega
    simp [nextBit, h, hm]

lemma nextBit_cyclic {m : ℕ} (hm : 0 < m) (x : Fin m → Bool) (i : Fin m) :
    nextBit x (x ⟨0, hm⟩) i = x ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩ := by
  by_cases h : i.val + 1 < m
  · simp [nextBit, h, Nat.mod_eq_of_lt h]
  · have he : i.val + 1 = m := by have := i.isLt; omega
    simp [nextBit, h, he]

def wordWeight (w : Bool → R) (c : Bool) (L : List (Option Bool))
    (x : Fin L.length → Bool) (b : Bool) : R :=
  ∏ i : Fin L.length, letter w (colorAt c i.val) L[i.val] (x i) (nextBit x b i)

lemma wordWeight_cons (w : Bool → R) (c : Bool) (p : Option Bool) (L : List (Option Bool))
    (a : Bool) (x : Fin L.length → Bool) (b : Bool) :
    wordWeight w c (p :: L) (Fin.cons a x) b =
      letter w c p a (headBit x b) * wordWeight w (!c) L x b := by
  simp only [wordWeight, List.length_cons, Fin.prod_univ_succ, Fin.val_zero, List.getElem_cons_zero,
    Fin.cons_zero, nextBit_cons_zero, colorAt_zero, Fin.val_succ, List.getElem_cons_succ,
    Fin.cons_succ, nextBit_cons_succ, colorAt_succ, colorAt_flip]

lemma wordPorts_eq_sum (w : Bool → R) (c : Bool) (L : List (Option Bool)) (a b : Bool) :
    wordPorts w c L a b = ∑ x : Fin L.length → Bool,
      if headBit x b = a then wordWeight w c L x b else 0 := by
  induction L generalizing c a b with
  | nil => simp [wordPorts, portId, headBit, wordWeight, eq_comm]
  | cons p L ih =>
    let F (x : Fin (L.length + 1) → Bool) : R :=
      if headBit x b = a then wordWeight w c (p :: L) x b else 0
    change _ = ∑ x, F x
    have hr : (∑ q : Bool × (Fin L.length → Bool), F (Fin.cons q.1 q.2)) = ∑ x, F x :=
      Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (L.length + 1) => Bool)) F
    rw [← hr, Fintype.sum_prod_type]
    simp only [F, headBit_cons, wordWeight_cons, wordPorts, portComp]
    have H : (∑ u : Bool, ∑ x : Fin L.length → Bool,
        if u = a then letter w c p u (headBit x b) * wordWeight w (!c) L x b else 0) =
        ∑ x : Fin L.length → Bool, letter w c p a (headBit x b) * wordWeight w (!c) L x b := by
      cases a <;> simp [Fintype.sum_bool]
    rw [H]
    simp_rw [ih, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    cases h : headBit x b <;> simp [Fintype.sum_bool, h]

lemma trace_eq_sum (w : Bool → R) (c : Bool) (L : List (Option Bool)) (hn : 0 < L.length) :
    portTrace (wordPorts w c L) =
      ∑ x : Fin L.length → Bool, wordWeight w c L x (x ⟨0, hn⟩) := by
  unfold portTrace
  simp_rw [wordPorts_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  cases h : x ⟨0, hn⟩ <;> simp [headBit, hn, Fintype.sum_bool, h]

def colorCount (c : Bool) (L : List (Option Bool)) (x : Fin L.length → Bool)
    (b d : Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin L.length => colorAt c i.val = d ∧ x i ≠ nextBit x b i).card

def wordFits (L : List (Option Bool)) (x : Fin L.length → Bool) : Prop :=
  ∀ i : Fin L.length, L[i.val] = none ∨ L[i.val] = some (x i)

def wordFits_decidable (L : List (Option Bool)) (x : Fin L.length → Bool) : Decidable (wordFits L x) :=
  inferInstanceAs (Decidable (∀ i : Fin L.length, L[i.val] = none ∨ L[i.val] = some (x i)))

lemma wordWeight_eq_powers (w : Bool → R) (c : Bool) (L : List (Option Bool))
    (x : Fin L.length → Bool) (b : Bool) :
    wordWeight w c L x b = @ite R (wordFits L x) (wordFits_decidable L x)
      (w false ^ colorCount c L x b false * w true ^ colorCount c L x b true) 0 := by
  classical
  by_cases hp : wordFits L x
  · rw [if_pos hp]
    have h (i : Fin L.length) :
        letter w (colorAt c i.val) L[i.val] (x i) (nextBit x b i) =
          (if colorAt c i.val = false ∧ x i ≠ nextBit x b i then w false else 1) *
          (if colorAt c i.val = true ∧ x i ≠ nextBit x b i then w true else 1) := by
      rw [letter, if_pos (hp i)]
      cases hc : colorAt c i.val <;> by_cases hx : x i = nextBit x b i <;> simp [edgePort, hc, hx]
    simp_rw [wordWeight, h]
    rw [Finset.prod_mul_distrib]
    simp only [← Finset.prod_filter, Finset.prod_const, colorCount]
  · rw [if_neg hp]
    change ¬ (∀ i : Fin L.length, L[i.val] = none ∨ L[i.val] = some (x i)) at hp
    obtain ⟨i, hi⟩ := not_forall.mp hp
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [letter, hi])

open MvPolynomial

noncomputable def biDegree (r b : ℕ) : Bool →₀ ℕ := Finsupp.single false r + Finsupp.single true b

lemma biDegree_eq_iff (r b r' b' : ℕ) : biDegree r b = biDegree r' b' ↔ r = r' ∧ b = b' := by
  constructor
  · intro h
    exact ⟨by simpa [biDegree] using congrArg (fun d : Bool →₀ ℕ => d false) h,
      by simpa [biDegree] using congrArg (fun d : Bool →₀ ℕ => d true) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma X_pow_mul_X_pow (r b : ℕ) :
    (X false : MvPolynomial Bool ℕ) ^ r * X true ^ b = monomial (biDegree r b) 1 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial]
  simp [biDegree]

lemma coeff_weighted_hist {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p]
    (r b : A → ℕ) (rr bb : ℕ) :
    (∑ x : A, if p x then
      (X false : MvPolynomial Bool ℕ) ^ (r x) * X true ^ (b x) else 0).coeff (biDegree rr bb) =
        (Finset.univ.filter fun x => p x ∧ r x = rr ∧ b x = bb).card := by
  rw [MvPolynomial.coeff_sum, Finset.card_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hp : p x <;>
    simp [hp, X_pow_mul_X_pow, MvPolynomial.coeff_monomial, biDegree_eq_iff]

def wrapNext {m : ℕ} (hm : 0 < m) (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩

lemma trace_ofFn (w : Bool → R) (c : Bool) {m : ℕ}
    (p : Fin m → Option Bool) (hm : 0 < m) :
    portTrace (wordPorts w c (List.ofFn p)) =
      ∑ x : Fin m → Bool, ∏ i : Fin m, letter w (colorAt c i.val) (p i) (x i) (x (wrapNext hm i)) := by
  have hn : 0 < (List.ofFn p).length := by simpa using hm
  let e : Fin m ≃ Fin (List.ofFn p).length := finCongr List.length_ofFn.symm
  let f := Equiv.arrowCongr e (Equiv.refl Bool)
  have hv (i : Fin m) : (e i).val = i.val := rfl
  have he (i : Fin m) : e (wrapNext hm i) = wrapNext hn (e i) := by
    apply Fin.ext
    simp [wrapNext, hv]
  rw [trace_eq_sum w c _ hn, ← f.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold wordWeight
  rw [← e.prod_comp]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [nextBit_cyclic, List.getElem_ofFn]
  have hi : (⟨(e i).val, by simpa using (e i).isLt⟩ : Fin m) = i := Fin.ext (hv i)
  change letter w (colorAt c (e i).val) (p ⟨(e i).val, _⟩) ((f x) (e i))
    ((f x) (wrapNext hn (e i))) = _
  have hf (j : Fin m) : f x (e j) = x j := by
    change x (e.symm (e j)) = x j
    rw [Equiv.symm_apply_apply]
  rw [← he, hf, hf, hi, hv]

variable {n : ℕ}

open Function

-- False/true positions are interleaved at each active slot.
def pairPos (m : ℕ) : Bool × Fin m ≃ Fin (2 * m) where
  toFun q := ⟨2 * q.2.val + q.1.toNat, by
    obtain ⟨b, j⟩ := q
    have h := j.isLt
    cases b <;> simp [Bool.toNat] <;> omega⟩
  invFun i := (decide (i.val % 2 = 1), ⟨i.val / 2, by have := i.isLt; omega⟩)
  left_inv := by
    rintro ⟨b, j⟩
    apply Prod.ext
    · change decide ((2 * j.val + b.toNat) % 2 = 1) = b
      cases b
      · exact decide_eq_false (show ¬ (2 * j.val + 0) % 2 = 1 by omega)
      · exact decide_eq_true (show (2 * j.val + 1) % 2 = 1 by omega)
    · apply Fin.ext
      change (2 * j.val + b.toNat) / 2 = j.val
      cases b <;> simp [Bool.toNat] <;> omega
  right_inv := by
    intro i
    apply Fin.ext
    change 2 * (i.val / 2) + (decide (i.val % 2 = 1)).toNat = i.val
    rcases Nat.mod_two_eq_zero_or_one i.val with h | h <;> simp [h, Bool.toNat] <;> omega

lemma wrapNext_pair_false {m : ℕ} (hm : 0 < m) (j : Fin m) :
    wrapNext (by omega : 0 < 2 * m) (pairPos m (false, j)) = pairPos m (true, j) := by
  apply Fin.ext
  change (2 * j.val + 1) % (2 * m) = 2 * j.val + 1
  exact Nat.mod_eq_of_lt (by have := j.isLt; omega)

lemma wrapNext_pair_true {m : ℕ} (hm : 0 < m) (j : Fin m) :
    wrapNext (by omega : 0 < 2 * m) (pairPos m (true, j)) = pairPos m (false, wrapNext hm j) := by
  apply Fin.ext
  change (2 * j.val + 1 + 1) % (2 * m) = 2 * ((j.val + 1) % m)
  rw [show 2 * j.val + 1 + 1 = 2 * (j.val + 1) by omega, Nat.mul_mod_mul_left]

abbrev CyclePos (τ : Equiv.Perm (Fin n)) (r : Layout.Root τ) := Fin (2 * minimalPeriod τ r.val)

lemma cyclePos_positive (τ : Equiv.Perm (Fin n)) (r : Layout.Root τ) :
    0 < 2 * minimalPeriod τ r.val := by
  have := Layout.periodPos τ r.val
  omega

noncomputable def slotVertex (τ : Equiv.Perm (Fin n)) (r : Layout.Root τ) (i : CyclePos τ r) : Bool × Fin n :=
  let q := (pairPos (minimalPeriod τ r.val)).symm i
  (q.1, Layout.atSlot τ ⟨r, q.2⟩)

lemma slotVertex_pair (τ : Equiv.Perm (Fin n)) (r : Layout.Root τ)
    (q : Bool × Fin (minimalPeriod τ r.val)) :
    slotVertex τ r (pairPos _ q) = (q.1, Layout.atSlot τ ⟨r, q.2⟩) := by
  simp [slotVertex]

noncomputable def vertexEquiv (τ : Equiv.Perm (Fin n)) :
    (Σ r : Layout.Root τ, CyclePos τ r) ≃ Bool × Fin n :=
  (Equiv.sigmaCongrRight fun (r : Layout.Root τ) =>
    (pairPos (minimalPeriod τ r.val)).symm.trans (Equiv.prodComm _ _)).trans
    ((Equiv.sigmaProdDistrib (fun r : Layout.Root τ => Fin (minimalPeriod τ r.val)) Bool).symm.trans
      ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl Bool) (Layout.slotsEquiv τ))))

lemma vertexEquiv_apply (τ : Equiv.Perm (Fin n)) (r : Layout.Root τ) (i : CyclePos τ r) :
    vertexEquiv τ ⟨r, i⟩ = slotVertex τ r i := rfl

noncomputable def cycleWord (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Layout.Root τ) :
    List (Option Bool) := List.ofFn (fun i : CyclePos τ r => p (slotVertex τ r i))

lemma cycleWord_length (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Layout.Root τ) :
    (cycleWord τ p r).length = 2 * minimalPeriod τ r.val := by
  simp [cycleWord]

lemma slotVertex_color (τ : Equiv.Perm (Fin n)) (r : Layout.Root τ) (i : CyclePos τ r) :
    colorAt false i.val = (slotVertex τ r i).1 := by
  obtain ⟨⟨b, j⟩, rfl⟩ := (pairPos (minimalPeriod τ r.val)).surjective i
  rw [slotVertex_pair]
  change (if (2 * j.val + b.toNat) % 2 = 0 then false else !false) = b
  cases b <;> simp

def nextVertex (σ : Equiv.Perm (Fin n)) : Bool × Fin n → Bool × Fin n
  | (false, i) => (true, i)
  | (true, i) => (false, σ.symm i)

lemma slotVertex_next (σ : Equiv.Perm (Fin n)) (r : Layout.Root σ.symm) (i : CyclePos σ.symm r) :
    slotVertex σ.symm r (wrapNext (cyclePos_positive σ.symm r) i) =
      nextVertex σ (slotVertex σ.symm r i) := by
  obtain ⟨⟨b, j⟩, rfl⟩ := (pairPos (minimalPeriod σ.symm r.val)).surjective i
  have hm := Layout.periodPos σ.symm r.val
  cases b with
  | false => rw [wrapNext_pair_false hm, slotVertex_pair, slotVertex_pair] <;> rfl
  | true =>
    rw [wrapNext_pair_true hm, slotVertex_pair, slotVertex_pair]
    change (false, Layout.atSlot σ.symm ⟨r, wrapNext hm j⟩) =
      (false, σ.symm (Layout.atSlot σ.symm ⟨r, j⟩))
    rw [Layout.nextSlot σ.symm r j] <;> rfl

def compatible (p : Bool × Fin n → Option Bool) (x : Bool × Fin n → Bool) : Prop :=
  ∀ v, p v = none ∨ p v = some (x v)

def postedCount (σ : Equiv.Perm (Fin n)) (x : Bool × Fin n → Bool) (c : Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, if c then σ i else i))).card

def edgeCount (σ : Equiv.Perm (Fin n)) (x : Bool × Fin n → Bool) (c : Bool) : ℕ :=
  (Finset.univ.filter (fun v : Bool × Fin n => v.1 = c ∧ x v ≠ x (nextVertex σ v))).card

lemma edgeCount_eq_posted (σ : Equiv.Perm (Fin n)) (x : Bool × Fin n → Bool) (c : Bool) :
    edgeCount σ x c = postedCount σ x c := by
  classical
  unfold edgeCount postedCount
  rw [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_bool, Finset.card_filter]
  cases c with
  | false => simp [nextVertex]
  | true =>
    simpa [nextVertex, ne_comm] using
      (Equiv.sum_comp σ (fun i => if x (true, i) ≠ x (false, σ.symm i) then (1 : ℕ) else 0)).symm

noncomputable def assignmentWeight (w : Bool → R) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (x : Bool × Fin n → Bool) : R := by
  classical
  exact if compatible p x then w false ^ postedCount σ x false * w true ^ postedCount σ x true else 0

lemma assignment_weight_eq (w : Bool → R) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (x : Bool × Fin n → Bool) :
    (∏ v : Bool × Fin n, letter w v.1 (p v) (x v) (x (nextVertex σ v))) = assignmentWeight w σ p x := by
  classical
  unfold assignmentWeight
  by_cases hp : compatible p x
  · rw [if_pos hp, ← edgeCount_eq_posted σ x false, ← edgeCount_eq_posted σ x true]
    have h (v : Bool × Fin n) :
        letter w v.1 (p v) (x v) (x (nextVertex σ v)) =
          (if v.1 = false ∧ x v ≠ x (nextVertex σ v) then w false else 1) *
          (if v.1 = true ∧ x v ≠ x (nextVertex σ v) then w true else 1) := by
      rw [letter, if_pos (hp v)]
      cases hc : v.1 <;> by_cases hx : x v = x (nextVertex σ v) <;> simp [edgePort, hc, hx]
    simp_rw [h]
    rw [Finset.prod_mul_distrib]
    simp only [← Finset.prod_filter, Finset.prod_const, edgeCount]
  · rw [if_neg hp]
    obtain ⟨v, hv⟩ := not_forall.mp (show ¬∀ v, p v = none ∨ p v = some (x v) from hp)
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [letter, hv])

noncomputable def cycleTraceProduct (w : Bool → R) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) : R := by
  classical
  exact ∏ r : Layout.Root σ.symm, portTrace (wordPorts w false (cycleWord σ.symm p r))

lemma cycleTrace_eq_assignments (w : Bool → R) (τ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (r : Layout.Root τ) :
    portTrace (wordPorts w false (cycleWord τ p r)) =
      ∑ x : CyclePos τ r → Bool, ∏ i : CyclePos τ r,
        letter w (colorAt false i.val) (p (slotVertex τ r i)) (x i)
          (x (wrapNext (cyclePos_positive τ r) i)) :=
  trace_ofFn w false _ (cyclePos_positive τ r)

set_option maxHeartbeats 1600000 in
lemma cycleTraceProduct_eq_weighted (w : Bool → R) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) :
    cycleTraceProduct w σ p = ∑ x : Bool × Fin n → Bool, assignmentWeight w σ p x := by
  classical
  let e : (Bool × Fin n → Bool) ≃ ((r : Layout.Root σ.symm) → CyclePos σ.symm r → Bool) :=
    (Equiv.arrowCongr (vertexEquiv σ.symm).symm (Equiv.refl Bool)).trans
      (Equiv.piCurry (fun (_ : Layout.Root σ.symm) _ => Bool))
  have he (x : Bool × Fin n → Bool) (r : Layout.Root σ.symm) (i : CyclePos σ.symm r) :
      e x r i = x (slotVertex σ.symm r i) := by
    change x (vertexEquiv σ.symm ⟨r, i⟩) = x (slotVertex σ.symm r i)
    rw [vertexEquiv_apply]
  unfold cycleTraceProduct
  simp_rw [cycleTrace_eq_assignments w σ.symm p]
  rw [Fintype.prod_sum, ← e.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← assignment_weight_eq]
  calc
    _ = ∏ r : Layout.Root σ.symm, ∏ i : CyclePos σ.symm r,
        letter w (slotVertex σ.symm r i).1 (p (slotVertex σ.symm r i))
          (x (slotVertex σ.symm r i)) (x (nextVertex σ (slotVertex σ.symm r i))) := by
      refine Finset.prod_congr rfl fun r _ => Finset.prod_congr rfl fun i _ => ?_
      rw [he, he, slotVertex_color, slotVertex_next]
    _ = ∏ q : (Σ r : Layout.Root σ.symm, CyclePos σ.symm r),
        letter w (vertexEquiv σ.symm q).1 (p (vertexEquiv σ.symm q))
          (x (vertexEquiv σ.symm q)) (x (nextVertex σ (vertexEquiv σ.symm q))) :=
      (Fintype.prod_sigma (fun q : (Σ r : Layout.Root σ.symm, CyclePos σ.symm r) =>
        letter w (vertexEquiv σ.symm q).1 (p (vertexEquiv σ.symm q))
          (x (vertexEquiv σ.symm q)) (x (nextVertex σ (vertexEquiv σ.symm q))))).symm
    _ = _ := (vertexEquiv σ.symm).prod_comp
      (fun v : Bool × Fin n => letter w v.1 (p v) (x v) (x (nextVertex σ v)))

noncomputable def histogram (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r b : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun x => compatible p x ∧ postedCount σ x false = r ∧ postedCount σ x true = b).card

lemma coeff_cycleTraceProduct (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r b : ℕ) :
    (cycleTraceProduct (fun c => X c : Bool → MvPolynomial Bool ℕ) σ p).coeff (biDegree r b) =
      histogram σ p r b := by
  classical
  rw [cycleTraceProduct_eq_weighted]
  exact coeff_weighted_hist (compatible p) (fun x => postedCount σ x false)
    (fun x => postedCount σ x true) r b

noncomputable def cycleWords (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    List CycleWord := by
  classical
  exact (Finset.univ : Finset (Layout.Root σ.symm)).toList.map
    (fun r => (false, cycleWord σ.symm p r))

lemma cycleWords_length (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    ((cycleWords σ p).map fun q => q.2.length).sum = 2 * n := by
  classical
  have h := Fintype.card_congr (Layout.slotsEquiv σ.symm)
  simp only [Layout.Active, Fintype.card_sigma, Fintype.card_fin] at h
  simp only [cycleWords, List.map_map, Function.comp_apply, cycleWord_length, Finset.sum_map_toList,
    ← Finset.mul_sum, h]

lemma cycleWords_member (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (q : CycleWord) (hq : q ∈ cycleWords σ p) :
    ∃ r : Layout.Root σ.symm, q = (false, cycleWord σ.symm p r) := by
  unfold cycleWords at hq
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hq
  exact ⟨r, hr.symm⟩

lemma cycleTraceProduct_eq_inventory (w : Bool → R) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) :
    cycleTraceProduct w σ p =
      (2 : R) ^ layoutFree (cycleWords σ p) *
        ∏ q ∈ arcUniverse (2 * n), arcFactor w q ^ (layoutArcs (cycleWords σ p)).count q := by
  classical
  have he (q : CycleWord) (hq : q ∈ cycleWords σ p) : q.2.length % 2 = 0 := by
    obtain ⟨r, rfl⟩ := cycleWords_member σ p q hq
    change (cycleWord σ.symm p r).length % 2 = 0
    rw [cycleWord_length]
    omega
  have hp (q : CycleWord) (hq : q ∈ cycleWords σ p) : 0 < q.2.length := by
    obtain ⟨r, rfl⟩ := cycleWords_member σ p q hq
    change 0 < (cycleWord σ.symm p r).length
    rw [cycleWord_length]
    exact cyclePos_positive _ _
  have h := layout_factor_inventory w (cycleWords σ p) (2 * n) he hp (cycleWords_length σ p).le
  simpa [cycleWords, cycleTraceProduct, List.map_map, Function.comp_apply] using h

lemma coeff_cycle_inventory (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r b : ℕ) :
    ((2 : MvPolynomial Bool ℕ) ^ layoutFree (cycleWords σ p) *
      ∏ q ∈ arcUniverse (2 * n), arcFactor (fun c => X c) q ^ (layoutArcs (cycleWords σ p)).count q).coeff
      (biDegree r b) =
        histogram σ p r b := by
  rw [← cycleTraceProduct_eq_inventory]
  exact coeff_cycleTraceProduct σ p r b

lemma coeff_posted_hist (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (r b : Fin (n + 1)) :
    ((2 : MvPolynomial Bool ℕ) ^ layoutFree (cycleWords σ p) *
      ∏ q ∈ arcUniverse (2 * n), arcFactor (fun c => X c) q ^ (layoutArcs (cycleWords σ p)).count q).coeff
      (biDegree r.val b.val) =
      ((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
        (∀ v, p v = none ∨ p v = some (x v)) ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val)).card := by
  classical
  rw [coeff_cycle_inventory σ p r.val b.val]
  unfold histogram
  congr 1
  ext x
  simp [postedCount, compatible]

end ProfileFactor

namespace Automaton

open ProfileFactor hiding Arc
open StateCompression LayoutCircuit

abbrev Open (M : ℕ) := Fin (M+1) × Bool × Fin (M+1) × Bool
abbrev State (M : ℕ) := Inventory M × Fin (M+1) × Fin (M+1) × Option (Open M)

private def small {M : ℕ} (k : ℕ) : Fin (M+1) := ⟨k % (M+1), Nat.mod_lt _ (Nat.succ_pos _)⟩

private lemma small_val {M k : ℕ} (hk : k ≤ M) : (small (M := M) k).val = k :=
  Nat.mod_eq_of_lt (Nat.lt_succ_of_le hk)

private def packOpen {M : ℕ} (o : ℕ × Bool × ℕ × Bool) : Open M :=
  (small o.1, o.2.1, small o.2.2.1, o.2.2.2)

def initial (M : ℕ) : State M := (StateCompression.zero M, small 0, small 0, none)

def vertex {M : ℕ} : State M → Option Bool → State M
  | (A,c,k,o), none => (A,c,small (k.val+1),o)
  | (A,c,k,none), some a => (A,c,small (k.val+1),some (k,a,k,a))
  | (A,c,k,some (f,a,l,b)), some p =>
    (insert A (k.val-l.val,colorAt false l.val,Bool.xor b p),c,small (k.val+1),some (f,a,k,p))

def close {M : ℕ} : State M → State M
  | (A,c,k,none) => (insert A (k.val,false,false),small (c.val+1),small 0,none)
  | (A,c,k,some (f,a,l,b)) =>
    (insert A (k.val-l.val+f.val,colorAt false l.val,Bool.xor b a),c,small 0,none)

def optionOf (d : Fin 3) : Option Bool := if d = 0 then none else some (decide (d = 2))

def digitOf (p : Option Bool) : Fin 3 := if p.isSome then if p.getD false then 2 else 1 else 0

lemma digit_option (d : Fin 3) : digitOf (optionOf d) = d := by
  fin_cases d <;> rfl

lemma option_digit (p : Option Bool) : optionOf (digitOf p) = p := by
  rcases p with _ | (_|_) <;> rfl

def next {M : ℕ} (s : State M) : Symbol → State M
  | none => s
  | some (last,d₀,d₁) =>
    let s' := vertex (vertex s (optionOf d₀)) (optionOf d₁)
    if last then close s' else s'

private lemma positive_append (A B : List Arc) (hA : ∀ a ∈ A, 0 < a.1)
    (hB : ∀ a ∈ B, 0 < a.1) : ∀ a ∈ A++B, 0 < a.1 := by
  intro a h
  rcases List.mem_append.mp h with h | h
  · exact hA a h
  · exact hB a h

private lemma weight_append' (A B : List Arc) : weight (A++B) = weight A + weight B := by
  simp [weight, List.sum_append]

private def Packed (M : ℕ) (A : List Arc) (c : ℕ) (s : OffsetScan)
    (hp : ∀ a ∈ s.2.2 ++ A, 0 < a.1) (hM : weight (s.2.2 ++ A) ≤ M) : State M :=
  (compress M (s.2.2 ++ A) hp hM, small c, small s.1, s.2.1.map packOpen)

lemma packed_vertex (M : ℕ) (A : List Arc) (c : ℕ) (s : OffsetScan) (d : Option Bool)
    (hk : s.1 ≤ M)
    (ho : ∀ o ∈ s.2.1, o.1 ≤ M ∧ o.2.2.1 ≤ M)
    (p : ∀ a ∈ s.2.2 ++ A, 0 < a.1) (h : weight (s.2.2 ++ A) ≤ M)
    (p' : ∀ a ∈ (offsetStep false s d).2.2 ++ A, 0 < a.1)
    (h' : weight ((offsetStep false s d).2.2 ++ A) ≤ M) :
    vertex (Packed M A c s p h) d = Packed M A c (offsetStep false s d) p' h' := by
  rcases s with ⟨k, o, B⟩
  rcases o with _ | ⟨f,a,l,b⟩
  · cases d <;> simp [Packed, vertex, offsetStep, small_val hk, packOpen]
  · have hl : l ≤ M := (ho _ rfl).2
    cases d with
    | none => simp [Packed, vertex, offsetStep, small_val hk]
    | some d =>
      simp only [Packed, vertex, offsetStep, Option.map_some, packOpen, small_val hk, small_val hl,
        List.cons_append]
      rw [compress_cons M (k-l,colorAt false l,Bool.xor b d) (B ++ A) p' h' p h]

lemma packed_close (M : ℕ) (A : List Arc) (c : ℕ) (s : OffsetScan)
    (hc : c ≤ M) (hk : s.1 ≤ M)
    (ho : ∀ o ∈ s.2.1, o.1 ≤ M ∧ o.2.2.1 ≤ M)
    (he : s.2.1 = none → s.2.2 = [])
    (p : ∀ a ∈ s.2.2 ++ A, 0 < a.1) (h : weight (s.2.2 ++ A) ≤ M)
    (p' : ∀ a ∈ (offsetClose false s).2 ++ A, 0 < a.1)
    (h' : weight ((offsetClose false s).2 ++ A) ≤ M) :
    close (Packed M A c s p h) =
      Packed M ((offsetClose false s).2 ++ A) (c+(offsetClose false s).1) (0,none,[]) p' h' := by
  rcases s with ⟨k,o,B⟩
  rcases o with _ | ⟨f,a,l,b⟩
  · obtain rfl : B = [] := he rfl
    simp only [Packed, close, offsetClose, Option.map_none, List.nil_append, small_val hk, small_val hc,
      List.singleton_append]
    rw [compress_cons M (k,false,false) A p' h' p h]
  · obtain ⟨hf,hl⟩ := ho _ rfl
    simp only [Packed, close, offsetClose, Option.map_none, Option.map_some, List.nil_append, packOpen,
      small_val hk, small_val hf, small_val hl, List.cons_append, Nat.add_zero]
    rw [compress_cons M (k-l+f,colorAt false l,Bool.xor b a) (B++A) p' h' p h]

lemma pad_factor {R : Type*} [CommSemiring R] (w : Bool → R) : arcFactor w StateCompression.pad = 1 := by
  simp [StateCompression.pad, arcFactor, freePath_one, edgePort]

noncomputable def polynomial {M : ℕ} (s : State M) : MvPolynomial Bool ℕ :=
  2 ^ s.2.1.val * ∏ q : Slot M, arcFactor MvPolynomial.X (slotArc q) ^ count s.1 q

lemma polynomial_packed (M : ℕ) (A : List Arc) (c : ℕ) (hc : c ≤ M)
    (p : ∀ a ∈ A, 0 < a.1) (h : weight A ≤ M) :
    polynomial (Packed M A c (0,none,[]) p h) = 2 ^ c * arcProduct MvPolynomial.X A := by
  unfold polynomial Packed arcProduct
  simp only [small_val hc, List.nil_append]
  rw [prod_compress _ _ (pad_factor _) _ p h]

lemma state_card {M : ℕ} : Fintype.card (State M) =
    (Part4 M).card * ((M+1) * ((M+1) * (1 + (M+1) * (2 * ((M+1) * 2))))) := by
  simp [State, Open, Inventory, Nat.add_comm]

private lemma offset_snoc (L : List (Option Bool)) (d : Option Bool) :
    offsetWord false (L++[d]) = offsetStep false (offsetWord false L) d := by
  simp [offsetWord, List.foldl_append]

private def wordMass (A : List Arc) (L : List (Option Bool)) : ℕ := weight A + L.length
private def ok (A : List Arc) : Prop := ∀ a ∈ A, 0 < a.1

private lemma wordPos (A : List Arc) (L : List (Option Bool)) (hp : ok A) :
    ok ((offsetWord false L).2.2 ++ A) := positive_append _ _ (offsetWord_fields false L).2.2.1 hp

private lemma wordBound (M : ℕ) (A : List Arc) (L : List (Option Bool)) (h : wordMass A L ≤ M) :
    weight ((offsetWord false L).2.2 ++ A) ≤ M := by
  have hL : weight (offsetWord false L).2.2 ≤ L.length := (offsetWord_fields false L).2.1
  rw [weight_append']
  unfold wordMass at h
  omega

private def packedWord (M : ℕ) (A : List Arc) (c : ℕ) (L : List (Option Bool))
    (hp : ok A) (h : wordMass A L ≤ M) : State M :=
  Packed M A c (offsetWord false L) (wordPos A L hp) (wordBound M A L h)

private lemma wordOpenBound (L : List (Option Bool)) (M : ℕ) (h : L.length ≤ M) :
    ∀ o ∈ (offsetWord false L).2.1, o.1 ≤ M ∧ o.2.2.1 ≤ M := by
  intro ⟨f,a,l,b⟩ ho
  have eqn : (offsetWord false L).2.1 = some (f,a,l,b) := ho
  have H := (offsetWord_fields false L).2.2.2
  rw [eqn] at H
  exact ⟨H.1.trans (H.2.1.le.trans h), H.2.1.le.trans h⟩

private lemma packedWord_vertex (M : ℕ) (A : List Arc) (c : ℕ) (L : List (Option Bool))
    (d : Option Bool) (hp : ok A) (h : wordMass A L ≤ M) (h' : wordMass A (L++[d]) ≤ M) :
    vertex (packedWord M A c L hp h) d = packedWord M A c (L++[d]) hp h' := by
  have hL : L.length ≤ M := by unfold wordMass at h; omega
  unfold packedWord
  have e := offset_snoc L d
  have p' : ok ((offsetStep false (offsetWord false L) d).2.2 ++ A) := by rw [← e]; exact wordPos A _ hp
  have q' : weight ((offsetStep false (offsetWord false L) d).2.2 ++ A) ≤ M := by
    rw [← e]; exact wordBound M A _ h'
  refine (packed_vertex M A c (offsetWord false L) d ?_ (wordOpenBound L M hL) _ _ p' q').trans ?_
  · simpa only [(offsetWord_fields false L).1] using hL
  · congr 1
    exact e.symm

private def closedArcs (L : List (Option Bool)) : List Arc := (offsetClose false (offsetWord false L)).2
private def closedFree (L : List (Option Bool)) : ℕ := (offsetClose false (offsetWord false L)).1

private lemma closedFree_le (L : List (Option Bool)) : closedFree L ≤ 1 := by
  unfold closedFree
  generalize offsetWord false L = s
  rcases s with ⟨k,o,B⟩
  rcases o with _ | ⟨f,a,l,b⟩ <;> simp [offsetClose]

private lemma closedArcs_ok (L : List (Option Bool)) (hL : 0 < L.length) : ok (closedArcs L) :=
  (offset_inventory_bounds false L hL).2

private lemma closedArcs_mass (L : List (Option Bool)) (hL : 0 < L.length) :
    weight (closedArcs L) = L.length := (offset_inventory_bounds false L hL).1

private lemma mass_closed_append (A : List Arc) (L : List (Option Bool)) (hL : 0 < L.length) :
    wordMass (closedArcs L ++ A) [] = wordMass A L := by
  simp [wordMass, weight_append', closedArcs_mass _ hL, Nat.add_comm]

private lemma packedWord_close (M : ℕ) (A : List Arc) (c : ℕ) (L : List (Option Bool))
    (hL : 0 < L.length) (hc : c ≤ M) (hp : ok A) (h : wordMass A L ≤ M) :
    close (packedWord M A c L hp h) =
      packedWord M (closedArcs L++A) (c+closedFree L) []
        (positive_append _ _ (closedArcs_ok L hL) hp) (by rwa [mass_closed_append _ _ hL]) := by
  have hLM : L.length ≤ M := by unfold wordMass at h; omega
  have he : (offsetWord false L).2.1 = none → (offsetWord false L).2.2 = [] := by
    intro hn
    have H := (offsetWord_fields false L).2.2.2
    rw [hn] at H
    exact H
  exact packed_close M A c _ hc (by simpa only [(offsetWord_fields false L).1] using hLM)
    (wordOpenBound L M hLM) he _ _ (positive_append _ _ (closedArcs_ok L hL) hp)
    (by change weight (closedArcs L ++ A) ≤ M
        rw [weight_append', closedArcs_mass L hL]
        unfold wordMass at h
        omega)

abbrev Pair := Fin 3 × Fin 3
private def wordOf (L : List Pair) : List (Option Bool) :=
  L.flatMap (fun a => [optionOf a.1, optionOf a.2])

private def mark : List Pair → List Symbol
  | [] => []
  | a::as => some (as.isEmpty,a.1,a.2) :: mark as

private lemma mark_length (L : List Pair) : (mark L).length = L.length := by
  induction L <;> simp [mark, *]

private lemma mark_get (L : List Pair) (i : ℕ) (hi : i < L.length) :
    (mark L)[i]'(by simpa only [mark_length] using hi) =
      some (decide (i+1=L.length),L[i].1,L[i].2) := by
  induction L generalizing i with
  | nil => simp at hi
  | cons a L ih =>
    cases i with
    | zero => cases L <;> simp [mark]
    | succ i => simpa [mark] using ih i (by simp at hi; omega)

private lemma mark_snoc (L : List Pair) (a : Pair) :
    mark (L++[a]) = L.map (fun d => some (false,d.1,d.2)) ++ [some (true,a.1,a.2)] := by
  induction L with
  | nil => rfl
  | cons b L ih => simp [mark, List.isEmpty_append, ih]

private lemma wordOf_length (L : List Pair) : (wordOf L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [wordOf] at ih ⊢; omega

private lemma wordOf_snoc (L : List Pair) (a : Pair) :
    wordOf (L++[a]) = wordOf L ++ [optionOf a.1, optionOf a.2] := by
  simp [wordOf, List.flatMap_append]

private lemma fold_unclosed (M : ℕ) (A : List Arc) (c : ℕ) (L : List Pair)
    (hp : ok A) (h : wordMass A (wordOf L) ≤ M) :
    (L.map (fun d => some (false,d.1,d.2))).foldl next
      (packedWord M A c [] hp (by unfold wordMass at *; simp at *; omega)) =
      packedWord M A c (wordOf L) hp h := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L d ih =>
    have h' : wordMass A (wordOf L ++ [optionOf d.1]) ≤ M := by
      rw [wordOf_snoc] at h
      simp [wordMass] at h ⊢
      omega
    have h₀ : wordMass A (wordOf L) ≤ M := by simp [wordMass] at h' ⊢; omega
    rw [List.map_append, List.foldl_append, ih h₀]
    simp only [List.map_singleton, List.foldl_cons, List.foldl_nil, next, Bool.false_eq_true, ite_false]
    rw [packedWord_vertex _ _ _ _ _ _ _ h']
    have e : wordOf (L++[d]) = (wordOf L ++ [optionOf d.1]) ++ [optionOf d.2] := by
      rw [wordOf_snoc, List.append_assoc]; rfl
    have h₂ : wordMass A ((wordOf L ++ [optionOf d.1]) ++ [optionOf d.2]) ≤ M := by rwa [← e]
    refine (packedWord_vertex _ _ _ _ _ _ _ h₂).trans ?_
    congr 1
    exact e.symm

private lemma fold_mark (M : ℕ) (A : List Arc) (c : ℕ) (L : List Pair)
    (hL : 0 < (wordOf L).length) (hc : c ≤ M) (hp : ok A) (h : wordMass A (wordOf L) ≤ M) :
    (mark L).foldl next (packedWord M A c [] hp (by unfold wordMass at *; simp at *; omega)) =
      packedWord M (closedArcs (wordOf L)++A) (c+closedFree (wordOf L)) []
        (positive_append _ _ (closedArcs_ok _ hL) hp) (by rwa [mass_closed_append _ _ hL]) := by
  induction L using List.reverseRecOn with
  | nil => simp [wordOf] at hL
  | append_singleton L d _ =>
    have e : wordOf (L++[d]) = (wordOf L ++ [optionOf d.1]) ++ [optionOf d.2] := by
      rw [wordOf_snoc, List.append_assoc]; rfl
    have h₀ : wordMass A (wordOf L) ≤ M := by rw [e] at h; simp [wordMass] at h ⊢; omega
    have h₁ : wordMass A (wordOf L ++ [optionOf d.1]) ≤ M := by
      rw [e] at h; simp [wordMass] at h ⊢; omega
    have h₂ : wordMass A ((wordOf L ++ [optionOf d.1]) ++ [optionOf d.2]) ≤ M := by rwa [← e]
    rw [mark_snoc, List.foldl_append, fold_unclosed _ _ _ _ _ h₀]
    simp only [List.foldl_cons, List.foldl_nil, next, ite_true]
    rw [packedWord_vertex _ _ _ _ _ _ _ h₁, packedWord_vertex _ _ _ _ _ _ _ h₂]
    have E : packedWord M A c ((wordOf L ++ [optionOf d.1]) ++ [optionOf d.2]) hp h₂ =
        packedWord M A c (wordOf (L++[d])) hp h := by congr 1; exact e.symm
    rw [E]
    exact packedWord_close M A c _ hL hc hp h

private lemma fold_inactive (M : ℕ) (s : State M) (k : ℕ) :
    (List.replicate k (none : Symbol)).foldl next s = s := by
  induction k <;> simp [List.replicate_succ, next, *]


open Function
open ProfileFactor hiding Arc
open StateCompression LayoutCircuit

variable {n : ℕ}

private def pairData (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (r : Fin n) (j : Fin (minimalPeriod τ r)) : Pair :=
  (digitOf (p (false,(τ^[j.val]) r)), digitOf (p (true,(τ^[j.val]) r)))

private noncomputable def rowPairs (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (r : Fin n) : List Pair := List.ofFn (pairData τ p r)

private lemma rowPairs_length (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Fin n) :
    (rowPairs τ p r).length = minimalPeriod τ r := List.length_ofFn

private lemma wordOf_rows (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Layout.Root τ) :
    wordOf (rowPairs τ p r.val) = cycleWord τ p r := by
  unfold cycleWord
  rw [List.ofFn_mul']
  unfold rowPairs wordOf
  rw [List.flatMap_def, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  rw [List.ofFn_succ]
  simp only [List.ofFn_succ, List.ofFn_zero, pairData, option_digit, Fin.val_zero, Fin.val_succ]
  have he : (2 * j.val) / 2 = j.val := by omega
  have ho : (2 * j.val + 1) / 2 = j.val := by omega
  have he' : ¬ (2 * j.val) % 2 = 1 := by omega
  have ho' : (2 * j.val + 1) % 2 = 1 := by omega
  simp [slotVertex, pairPos, Layout.atSlot, he, ho, he', ho', pairData, option_digit]

private noncomputable def rowEvents (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (r : Fin n) : List Symbol := by
  classical
  exact if ∀ s, τ.SameCycle r s → r ≤ s then
    mark (rowPairs τ p r) ++ List.replicate (n-minimalPeriod τ r) none else List.replicate n none

private lemma rowEvents_length (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Fin n) :
    (rowEvents τ p r).length = n := by
  classical
  by_cases h : ∀ s, τ.SameCycle r s → r ≤ s
  · rw [rowEvents, if_pos h]
    simp only [List.length_append, mark_length, rowPairs_length, List.length_replicate]
    have := Layout.periodLe τ r
    omega
  · rw [rowEvents, if_neg h, List.length_replicate]

private noncomputable def rowEntry (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (r j : Fin n) : Symbol :=
  (rowEvents τ p r)[j.val]'(by rw [rowEvents_length]; exact j.isLt)

private lemma rowEntry_live (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (r j : Fin n) (hr : ∀ s, τ.SameCycle r s → r ≤ s) (hj : j.val < minimalPeriod τ r) :
    rowEntry τ p r j = some (decide (j.val+1=minimalPeriod τ r),
      digitOf (p (false,(τ^[j.val]) r)),digitOf (p (true,(τ^[j.val]) r))) := by
  classical
  unfold rowEntry
  simp only [rowEvents, if_pos hr]
  rw [List.getElem_append_left (by simpa only [mark_length,rowPairs_length] using hj)]
  rw [mark_get _ _ (by simpa only [rowPairs_length] using hj)]
  simp [rowPairs, pairData]

private lemma rowEntry_inactive (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (r j : Fin n) (h : ¬ ((∀ s, τ.SameCycle r s → r ≤ s) ∧ j.val < minimalPeriod τ r)) :
    rowEntry τ p r j = none := by
  classical
  unfold rowEntry
  by_cases hr : ∀ s, τ.SameCycle r s → r ≤ s
  · have hj : minimalPeriod τ r ≤ j.val := Nat.le_of_not_gt (fun hj => h ⟨hr,hj⟩)
    simp only [rowEvents, if_pos hr]
    rw [List.getElem_append_right (by simpa only [mark_length,rowPairs_length] using hj)]
    simp
  · simp [rowEvents, hr]

private noncomputable def rowArcs (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Fin n) : List Arc := by
  classical
  exact if ∀ s, τ.SameCycle r s → r ≤ s then closedArcs (wordOf (rowPairs τ p r)) else []

private noncomputable def rowFree (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Fin n) : ℕ := by
  classical
  exact if ∀ s, τ.SameCycle r s → r ≤ s then closedFree (wordOf (rowPairs τ p r)) else 0

private lemma rowWord_pos (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Fin n) :
    0 < (wordOf (rowPairs τ p r)).length := by
  rw [wordOf_length, rowPairs_length]
  have := Layout.periodPos τ r
  omega

private lemma rowArcs_ok (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Fin n) :
    ok (rowArcs τ p r) := by
  classical
  by_cases h : ∀ s, τ.SameCycle r s → r ≤ s
  · rw [rowArcs, if_pos h]
    exact closedArcs_ok _ (rowWord_pos τ p r)
  · rw [rowArcs, if_neg h]
    simp [ok]

private lemma rowFree_le (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Fin n) :
    rowFree τ p r ≤ weight (rowArcs τ p r) := by
  classical
  by_cases h : ∀ s, τ.SameCycle r s → r ≤ s
  · rw [rowFree, if_pos h, rowArcs, if_pos h, closedArcs_mass _ (rowWord_pos τ p r)]
    exact (closedFree_le _).trans (rowWord_pos τ p r)
  · simp [rowFree, h]

private lemma rowArcs_weight (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Fin n) :
    weight (rowArcs τ p r) = if ∀ s, τ.SameCycle r s → r ≤ s then 2*minimalPeriod τ r else 0 := by
  classical
  by_cases h : ∀ s, τ.SameCycle r s → r ≤ s
  · rw [rowArcs, if_pos h, if_pos h, closedArcs_mass _ (rowWord_pos τ p r), wordOf_length, rowPairs_length]
  · rw [rowArcs, if_neg h, if_neg h]
    rfl

private lemma rowFold (M : ℕ) (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Fin n)
    (A : List Arc) (c : ℕ) (hc : c ≤ M) (hp : ok A) (hb : weight (rowArcs τ p r) + weight A ≤ M) :
    (rowEvents τ p r).foldl next (packedWord M A c [] hp (by simp [wordMass]; omega)) =
      packedWord M (rowArcs τ p r ++ A) (c + rowFree τ p r) []
        (positive_append _ _ (rowArcs_ok _ _ _) hp) (by simpa [wordMass, weight_append'] using hb) := by
  classical
  by_cases h : ∀ s, τ.SameCycle r s → r ≤ s
  · have hL := rowWord_pos τ p r
    have hB : wordMass A (wordOf (rowPairs τ p r)) ≤ M := by
      rw [rowArcs, if_pos h, closedArcs_mass _ hL] at hb
      simpa [wordMass, Nat.add_comm] using hb
    simp only [rowEvents, rowArcs, rowFree, if_pos h, List.foldl_append, fold_inactive]
    exact fold_mark _ _ _ _ hL hc hp hB
  · simp only [rowEvents, rowArcs, rowFree, if_neg h, fold_inactive, List.nil_append, Nat.add_zero]

private noncomputable def arcsRows (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (rs : List (Fin n)) : List Arc := rs.reverse.flatMap (rowArcs τ p)

private noncomputable def freeRows (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (rs : List (Fin n)) : ℕ := (rs.map (rowFree τ p)).sum

private lemma arcsRows_snoc (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (rs : List (Fin n)) (r : Fin n) : arcsRows τ p (rs++[r]) = rowArcs τ p r ++ arcsRows τ p rs := by
  simp [arcsRows]

private lemma freeRows_snoc (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (rs : List (Fin n)) (r : Fin n) : freeRows τ p (rs++[r]) = freeRows τ p rs + rowFree τ p r := by
  simp [freeRows]

private lemma arcsRows_ok (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (rs : List (Fin n)) :
    ok (arcsRows τ p rs) := by
  intro a ha
  obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp ha
  exact rowArcs_ok τ p r a hr

private lemma freeRows_le (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (rs : List (Fin n)) :
    freeRows τ p rs ≤ weight (arcsRows τ p rs) := by
  induction rs using List.reverseRecOn with
  | nil => simp [freeRows, arcsRows, weight]
  | append_singleton rs r ih =>
    rw [freeRows_snoc, arcsRows_snoc, weight_append']
    have := rowFree_le τ p r
    omega

private lemma rowsFold (M : ℕ) (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (rs : List (Fin n)) (h : weight (arcsRows τ p rs) ≤ M) :
    (rs.flatMap (rowEvents τ p)).foldl next (initial M) =
      packedWord M (arcsRows τ p rs) (freeRows τ p rs) [] (arcsRows_ok _ _ _) (by simpa [wordMass] using h) := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    have hB : weight (rowArcs τ p r) + weight (arcsRows τ p rs) ≤ M := by
      rwa [arcsRows_snoc, weight_append'] at h
    have hA : weight (arcsRows τ p rs) ≤ M := by omega
    rw [List.flatMap_append, List.foldl_append, ih hA]
    simp only [List.flatMap_singleton, arcsRows_snoc, freeRows_snoc]
    exact rowFold _ _ _ _ _ _ ((freeRows_le _ _ _).trans hA) (arcsRows_ok _ _ _) hB

private lemma arcsRows_weight (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (rs : List (Fin n)) : weight (arcsRows τ p rs) = (rs.map (fun r => weight (rowArcs τ p r))).sum := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih => simp [arcsRows_snoc, weight_append', ih, Nat.add_comm]

private lemma allRowsWeight (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    weight (arcsRows τ p (List.ofFn (fun r : Fin n => r))) = 2*n := by
  classical
  have H := Fintype.card_congr (Layout.slotsEquiv τ)
  simp only [Layout.Active, Fintype.card_sigma, Fintype.card_fin] at H
  rw [arcsRows_weight, List.map_ofFn, List.sum_ofFn]
  simp_rw [Function.comp_apply, rowArcs_weight]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun r => ∀ s, τ.SameCycle r s → r ≤ s) _ (fun _ => by simp)]
  rw [← Finset.mul_sum, H]

private noncomputable def rowPoly (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Fin n) :
    MvPolynomial Bool ℕ := 2 ^ rowFree τ p r * arcProduct MvPolynomial.X (rowArcs τ p r)

private lemma rowPoly_eq (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Fin n) :
    rowPoly τ p r = if hr : ∀ s, τ.SameCycle r s → r ≤ s then
      portTrace (wordPorts MvPolynomial.X false (cycleWord τ p ⟨r,hr⟩)) else 1 := by
  classical
  by_cases h : ∀ s, τ.SameCycle r s → r ≤ s
  · rw [rowPoly, rowFree, rowArcs, if_pos h, if_pos h, dif_pos h,
      wordOf_rows τ p ⟨r,h⟩]
    symm
    apply offset_cycle_factor
    rw [cycleWord_length]
    omega
  · simp [rowPoly, rowFree, rowArcs, h, arcProduct]

private lemma rowsProduct (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (rs : List (Fin n)) :
    (2 : MvPolynomial Bool ℕ) ^ freeRows τ p rs * arcProduct MvPolynomial.X (arcsRows τ p rs) =
      (rs.map (rowPoly τ p)).prod := by
  induction rs using List.reverseRecOn with
  | nil => simp [freeRows, arcsRows, arcProduct]
  | append_singleton rs r ih =>
    rw [freeRows_snoc, arcsRows_snoc, pow_add, arcProduct_append, List.map_append, List.prod_append, ← ih]
    simp only [List.map_singleton, List.prod_singleton, rowPoly]
    ring

private lemma prodRows (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    ((List.ofFn (fun r : Fin n => r)).map (rowPoly σ.symm p)).prod = cycleTraceProduct MvPolynomial.X σ p := by
  classical
  rw [List.map_ofFn, List.prod_ofFn, cycleTraceProduct]
  apply Finset.prod_congr_set {r | ∀ s, Equiv.Perm.SameCycle σ.symm r s → r ≤ s}
  · intro r hr
    exact (rowPoly_eq _ _ _).trans (dif_pos hr)
  · intro r hr
    exact (rowPoly_eq _ _ _).trans (dif_neg hr)


open Function
open ProfileFactor hiding Arc
open StateCompression LayoutCircuit Compiler.Build

variable {n N : ℕ}

private def rowLabel (hn : 0 < n) (i : ℕ) : Fin n := ⟨(i / n) % n, Nat.mod_lt _ hn⟩
private def rowOffset (hn : 0 < n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩

private lemma rowSlot_lt (r j : Fin n) : r.val*n+j.val < n*n := by
  calc
    _ < (r.val+1)*n := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.isLt _
    _ ≤ _ := Nat.mul_le_mul_right _ r.isLt

private lemma rowLabel_slot (hn : 0 < n) (r j : Fin n) : rowLabel hn (r.val*n+j.val) = r := by
  apply Fin.ext
  change (r.val*n+j.val)/n%n = r.val
  rw [Nat.mul_comm r.val, Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero, Nat.mod_eq_of_lt r.isLt]

private lemma rowOffset_slot (hn : 0 < n) (r j : Fin n) : rowOffset hn (r.val*n+j.val) = j := by
  apply Fin.ext
  change (r.val*n+j.val)%n = j.val
  rw [Nat.mul_comm r.val, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]

private lemma slot_rowLabel (hn : 0 < n) (i : Fin (n*n)) :
    (rowLabel hn i.val).val*n+(rowOffset hn i.val).val = i.val := by
  change (i.val / n) % n * n + i.val % n = i.val
  have hi : i.val/n < n := (Nat.div_lt_iff_lt_mul hn).2 i.isLt
  rw [Nat.mod_eq_of_lt hi, Nat.mul_comm, Nat.div_add_mod]

private def symbols {N : ℕ} (hn : 0 < n) (edge : Mat n N) (permit : Permit n N)
    (i : ℕ) (e : Symbol) : Sig N := symbolSignal edge permit (rowLabel hn i) (rowOffset hn i) e

private noncomputable def code (hn : 0 < n) (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (i : Fin (n*n)) : Symbol := rowEntry τ p (rowLabel hn i.val) (rowOffset hn i.val)

private lemma code_rows (hn : 0 < n) (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    List.ofFn (code hn τ p) = (List.ofFn (fun r : Fin n => r)).flatMap (rowEvents τ p) := by
  rw [List.ofFn_mul, List.flatMap_def, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext r
  simp only [Function.comp_apply, code, rowLabel_slot, rowOffset_slot]
  have e (j : Fin n) : rowEntry τ p r j = (rowEvents τ p r).get (j.cast (rowEvents_length τ p r).symm) := rfl
  simp_rw [e]
  exact (List.ofFn_congr (rowEvents_length τ p r) (rowEvents τ p r).get).symm.trans (List.ofFn_get _)

private lemma poly_code (hn : 0 < n) (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    polynomial (runPath (initial (2*n)) (fun _ => next) (n*n) (code hn σ.symm p)) =
      cycleTraceProduct MvPolynomial.X σ p := by
  rw [runPath_fold, code_rows]
  let rs := List.ofFn (fun r : Fin n => r)
  have hb : weight (arcsRows σ.symm p rs) ≤ 2*n := (allRowsWeight σ.symm p).le
  rw [rowsFold _ _ _ _ hb]
  have hfree : freeRows σ.symm p rs ≤ 2*n := (freeRows_le _ _ _).trans hb
  unfold packedWord
  change polynomial (Packed (2*n) (arcsRows σ.symm p rs) (freeRows σ.symm p rs) (0,none,[]) _ _) = _
  exact (polynomial_packed _ _ _ hfree (arcsRows_ok _ _ _) hb).trans
    ((rowsProduct _ _ _).trans (prodRows σ p))

private lemma cycle_end (τ : Equiv.Perm (Fin n)) (r : Fin n) (j : ℕ) (hj : j < minimalPeriod τ r) :
    (τ^[j+1]) r = r ↔ j+1 = minimalPeriod τ r := by
  constructor
  · intro h
    have h' := (show IsPeriodicPt τ (j+1) r from h).minimalPeriod_le (Nat.succ_pos j)
    omega
  · intro h
    rw [h]
    exact iterate_minimalPeriod

private lemma symbol_none_iff (edge : Mat n N) (permit : Permit n N) (τ : Equiv.Perm (Fin n))
    (x : Fin N → Bool) (he : ∀ r t, edge r t x = decide (τ r = t)) (r j : Fin n) :
    symbolSignal edge permit r j none x = true ↔
      ¬ ((∀ s, τ.SameCycle r s → r ≤ s) ∧ j.val < minimalPeriod τ r) := by
  simp [symbolSignal, nt, ← liveSignal_spec edge τ x he]

private lemma symbol_some_iff (edge : Mat n N) (permit : Permit n N) (τ : Equiv.Perm (Fin n))
    (x : Fin N → Bool) (he : ∀ r t, edge r t x = decide (τ r = t)) (r j : Fin n)
    (b : Bool) (d₀ d₁ : Fin 3) :
    symbolSignal edge permit r j (some (b,d₀,d₁)) x = true ↔
      ((∀ s, τ.SameCycle r s → r ≤ s) ∧ j.val < minimalPeriod τ r) ∧
      b = decide (j.val+1 = minimalPeriod τ r) ∧
      permit (false,(τ^[j.val]) r) d₀ x = true ∧ permit (true,(τ^[j.val]) r) d₁ x = true := by
  simp only [symbolSignal, an, Bool.and_eq_true, liveSignal_spec edge τ x he, literal_true,
    allowAt_spec edge permit τ x he, matPow_spec edge τ x he]
  apply and_congr_right
  intro H
  simp only [cycle_end τ r j.val H.2, eq_comm]

private noncomputable def decode (hn : 0 < n) (τ : Equiv.Perm (Fin n)) (y : Fin (n*n) → Symbol)
    (v : Bool × Fin n) : Option Bool :=
  let a := (Layout.slotsEquiv τ).symm v.2
  let r := a.1.val
  let j : Fin n := ⟨a.2.val, a.2.isLt.trans_le (Layout.periodLe τ r)⟩
  match y ⟨r.val*n+j.val,rowSlot_lt r j⟩ with
  | none => none
  | some (_,d₀,d₁) => optionOf (if v.1 then d₁ else d₀)

private lemma decode_at (hn : 0 < n) (τ : Equiv.Perm (Fin n)) (y : Fin (n*n) → Symbol)
    (r j : Fin n) (hr : ∀ s, τ.SameCycle r s → r ≤ s) (hj : j.val < minimalPeriod τ r)
    (b : Bool) :
    decode hn τ y (b,(τ^[j.val]) r) =
      match y ⟨r.val*n+j.val,rowSlot_lt r j⟩ with
      | none => none
      | some (_,d₀,d₁) => optionOf (if b then d₁ else d₀) := by
  have E : (Layout.slotsEquiv τ).symm ((τ^[j.val]) r) = ⟨⟨r,hr⟩,⟨j.val,hj⟩⟩ :=
    (Layout.slotsEquiv τ).symm_apply_apply ⟨⟨r,hr⟩,⟨j.val,hj⟩⟩
  let f (a : Layout.Active τ) : Option Bool :=
    let t : Fin n := ⟨a.2.val,a.2.isLt.trans_le (Layout.periodLe τ a.1.val)⟩
    match y ⟨a.1.val.val*n+t.val,rowSlot_lt a.1.val t⟩ with
    | none => none
    | some (_,d₀,d₁) => optionOf (if b then d₁ else d₀)
  exact congrArg f E

private lemma code_injective (hn : 0 < n) (τ : Equiv.Perm (Fin n)) : Function.Injective (code hn τ) := by
  intro p q H
  funext v
  let u := (Layout.slotsEquiv τ).symm v.2
  let r := u.1
  let j : Fin n := ⟨u.2.val,u.2.isLt.trans_le (Layout.periodLe τ r.val)⟩
  have hv : (τ^[j.val]) r.val = v.2 := (Layout.slotsEquiv τ).apply_symm_apply v.2
  have hi := congrFun H ⟨r.val.val*n+j.val,rowSlot_lt r.val j⟩
  simp only [code, rowLabel_slot, rowOffset_slot, rowEntry_live τ p r.val j r.property u.2.isLt,
    rowEntry_live τ q r.val j r.property u.2.isLt, hv, Option.some.injEq, Prod.mk.injEq, true_and] at hi
  rcases v with ⟨b,i⟩
  cases b
  · exact (option_digit (p (false,i))).symm.trans ((congrArg optionOf hi.1).trans (option_digit (q (false,i))))
  · exact (option_digit (p (true,i))).symm.trans ((congrArg optionOf hi.2).trans (option_digit (q (true,i))))

private lemma code_live (hn : 0 < n) (edge : Mat n N) (permit : Permit n N) (τ : Equiv.Perm (Fin n))
    (x : Fin N → Bool) (he : ∀ r t, edge r t x = decide (τ r = t)) (p : Bool × Fin n → Option Bool) :
    livePath (symbols hn edge permit) (n*n) (code hn τ p) x = true ↔
      ∀ v, permit v (digitOf (p v)) x = true := by
  rw [livePath_spec]
  constructor
  · intro H v
    let u := (Layout.slotsEquiv τ).symm v.2
    let r := u.1
    let j : Fin n := ⟨u.2.val,u.2.isLt.trans_le (Layout.periodLe τ r.val)⟩
    have hv : (τ^[j.val]) r.val = v.2 := (Layout.slotsEquiv τ).apply_symm_apply v.2
    have hi := H ⟨r.val.val*n+j.val,rowSlot_lt r.val j⟩
    simp only [symbols, code, rowLabel_slot, rowOffset_slot, rowEntry_live τ p r.val j r.property u.2.isLt,
      symbol_some_iff edge permit τ x he, hv] at hi
    rcases v with ⟨b,i⟩
    cases b
    · exact hi.2.2.1
    · exact hi.2.2.2
  · intro H i
    simp only [symbols, code]
    let r := rowLabel hn i.val
    let j := rowOffset hn i.val
    by_cases ha : (∀ s, τ.SameCycle r s → r ≤ s) ∧ j.val < minimalPeriod τ r
    · rw [rowEntry_live τ p r j ha.1 ha.2, symbol_some_iff edge permit τ x he]
      exact ⟨ha,rfl,H _,H _⟩
    · rw [rowEntry_inactive τ p r j ha, symbol_none_iff edge permit τ x he]
      exact ha

private lemma code_decode_live (hn : 0 < n) (edge : Mat n N) (permit : Permit n N)
    (τ : Equiv.Perm (Fin n)) (x : Fin N → Bool) (he : ∀ r t, edge r t x = decide (τ r = t))
    (y : Fin (n*n) → Symbol) (hy : livePath (symbols hn edge permit) (n*n) y x = true) :
    code hn τ (decode hn τ y) = y := by
  funext i
  have h := (livePath_spec _ _ _ _).1 hy i
  let r := rowLabel hn i.val
  let j := rowOffset hn i.val
  have hi : (⟨r.val*n+j.val,rowSlot_lt r j⟩ : Fin (n*n)) = i := Fin.ext (slot_rowLabel hn i)
  change symbolSignal edge permit r j (y i) x = true at h
  change rowEntry τ (decode hn τ y) r j = y i
  cases hY : y i with
  | none =>
    exact rowEntry_inactive τ _ r j ((symbol_none_iff edge permit τ x he r j).1 (hY ▸ h))
  | some e =>
    obtain ⟨b,d₀,d₁⟩ := e
    obtain ⟨ha,hb,_,_⟩ := (symbol_some_iff edge permit τ x he r j b d₀ d₁).1 (hY ▸ h)
    rw [rowEntry_live τ _ r j ha.1 ha.2, decode_at hn τ y r j ha.1 ha.2 false,
      decode_at hn τ y r j ha.1 ha.2 true, hi, hY, hb]
    simp [digit_option]

end Automaton

-- Bit decoding adapted from lean/PEqualNP/Outside/L_pcx_431.lean at
-- 5edaa5b98fcb8850538e82d2b7aa2d998868830f.
private def asBits {w : ℕ} (z : Fin (2^w)) (j : Fin w) : Bool := z.val.testBit j.val

private theorem asBits_bijective {w : ℕ} : Function.Bijective (asBits (w := w)) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by simp⟩
  intro a b he
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w
  · exact congrFun he ⟨j, hj⟩
  · have hp : 2^w ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le hp), Nat.testBit_lt_two_pow (b.isLt.trans_le hp)]

noncomputable def fromBits {w : ℕ} (f : Fin w → Bool) : ℕ :=
  ((Equiv.ofBijective asBits asBits_bijective).symm f).val

theorem fromBits_lt {w : ℕ} (f : Fin w → Bool) : fromBits f < 2^w := Fin.isLt _

theorem fromBits_bit {w : ℕ} (f : Fin w → Bool) (j : Fin w) : (fromBits f).testBit j.val = f j :=
  congrFun ((Equiv.ofBijective asBits asBits_bijective).apply_symm_apply f) j

theorem fromBits_eq_sum {w : ℕ} (f : Fin w → Bool) :
    fromBits f = ∑ j : Fin w, (f j).toNat * 2^j.val := by
  rw [← val_testBit_of_lt (fromBits_lt f)]
  simp only [fromBits_bit]

namespace Automaton

open Compiler.Build LayoutCircuit
open ProfileFactor hiding Arc
open StateCompression

variable {n N : ℕ}

abbrev Pin (n : ℕ) := Bool × Fin n → Option Bool
abbrev Hist (n : ℕ) := Fin (n+1) → Fin (n+1) → ℕ
abbrev Fields (n : ℕ) := Fin (n+1) × Fin (n+1) × Fin (2*n+1)
abbrev Target (n N : ℕ) := Fields n → Sig N

noncomputable def hist (σ : Equiv.Perm (Fin n)) (p : Pin n) : Hist n :=
  fun r b => histogram σ p r.val b.val

lemma hist_lt (σ : Equiv.Perm (Fin n)) (p : Pin n) (r b : Fin (n+1)) : hist σ p r b < 2^(2*n+1) := by
  classical
  unfold hist histogram
  have h : (Finset.univ : Finset (Bool × Fin n → Bool)).card = 2^(2*n) := by simp
  exact (Finset.card_filter_le _ _).trans_lt (h ▸ Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

lemma hist_posted (σ : Equiv.Perm (Fin n)) (p : Pin n) (r b : Fin (n+1)) :
    hist σ p r b = ((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
        (∀ v, p v = none ∨ p v = some (x v)) ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val)).card := by
  classical
  unfold hist histogram
  congr 1
  ext x
  simp [postedCount, compatible]

noncomputable def fiber (σ : Equiv.Perm (Fin n)) (a : Bool × Fin n → Fin 3 → Bool) (H : Hist n) :
    Finset (Pin n) := by
  classical
  exact Finset.univ.filter (fun p => hist σ p = H ∧ ∀ v, a v (digitOf (p v)) = true)

lemma fiber_lt (hn : 0 < n) (σ : Equiv.Perm (Fin n)) (a : Bool × Fin n → Fin 3 → Bool) (H : Hist n) :
    (fiber σ a H).card < 2^(4*n) := by
  classical
  have hc : Fintype.card (Pin n) = 3^(2*n) := by simp [Pin]
  have hp : 3^(2*n) < 4^(2*n) := Nat.pow_lt_pow_left (by decide) (by omega)
  have he : 4^(2*n) = 2^(4*n) := by rw [show (4:ℕ)=2^2 by decide, ← pow_mul]; congr 1; omega
  calc
    _ ≤ (Finset.univ : Finset (Pin n)).card := Finset.card_filter_le _ _
    _ = 3^(2*n) := Finset.card_univ.trans hc
    _ < 4^(2*n) := hp
    _ = _ := he

noncomputable def allType {ι : Type*} [Fintype ι] (f : ι → Sig N) : Sig N :=
  fun x => Finset.univ.toList.all (fun i => f i x)

lemma allType_true {ι : Type*} [Fintype ι] (f : ι → Sig N) (x : Fin N → Bool) :
    allType f x = true ↔ ∀ j, f j x = true := by
  simp [allType, List.all_eq_true]

lemma allTypeB {ι : Type*} [Fintype ι] {A : Set (Sig N)} (f : ι → Sig N)
    (hf : ∀ i, f i ∈ A) (ht : (fun _ => true) ∈ A) :
    Build A {allType f} (Fintype.card ι) := by
  unfold allType
  simpa only [List.length_map, Finset.length_toList, Finset.card_univ, List.all_map, Function.comp_def]
    using everyG (Finset.univ.toList.map f) (fun g hg => by
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
      exact hf i) ht

noncomputable def matchTarget (H : Target n N) (s : State (2*n)) : Sig N :=
  allType (fun q : Fields n => literal (H q)
    (((polynomial s).coeff (biDegree q.1.val q.2.1.val)).testBit q.2.2.val))

noncomputable def decodeTarget (H : Target n N) (x : Fin N → Bool) : Hist n :=
  fun r b => fromBits (fun k => H (r,b,k) x)

private lemma matchTarget_code (hn : 0 < n) (σ : Equiv.Perm (Fin n)) (p : Pin n)
    (H : Target n N) (x : Fin N → Bool) :
    matchTarget H (runPath (initial (2*n)) (fun _ => next) (n*n) (code hn σ.symm p)) x = true ↔
      hist σ p = decodeTarget H x := by
  unfold matchTarget
  rw [allType_true, poly_code]
  simp only [literal_true, coeff_cycleTraceProduct]
  constructor
  · intro h
    funext r b
    unfold decodeTarget
    have he (j : Fin (2*n+1)) : (hist σ p r b).testBit j.val = H (r,b,j) x := (h (r,b,j)).symm
    rw [fromBits_eq_sum]
    simp_rw [← he]
    exact (val_testBit_of_lt (hist_lt σ p r b)).symm
  · intro h q
    have hq := congrFun (congrFun h q.1) q.2.1
    change H q x = (hist σ p q.1 q.2.1).testBit q.2.2.val
    rw [hq]
    exact (fromBits_bit (fun j : Fin (2*n+1) => H (q.1,q.2.1,j) x) q.2.2).symm

def targetCost (n : ℕ) := Fintype.card (State (2*n)) * (2 * Fintype.card (Fields n))

theorem matchTargetB {A : Set (Sig N)} (H : Target n N) (ha : ∀ q, H q ∈ A)
    (ht : (fun _ => true) ∈ A) : Build A (Set.range (matchTarget H)) (targetCost n) := by
  apply allG
  intro s
  let f (q : Fields n) := literal (H q) (((polynomial s).coeff (biDegree q.1.val q.2.1.val)).testBit q.2.2.val)
  have H₀ := allG (A := A) f 1 (fun q => literalB _ _ (ha q))
  have H₁ := allTypeB (A := A ∪ Set.range f) f (fun i => Or.inr ⟨i,rfl⟩) (Or.inl ht)
  exact relax (thenG H₀ H₁) le_rfl le_rfl (by omega)

noncomputable def countRaw (hn : 0 < n) (edge : Mat n N) (permit : Permit n N)
    (H : Target n N) (x : Fin N → Bool) : ℕ := by
  classical
  exact acceptingCount (initial (2*n)) (fun _ => next) (symbols hn edge permit) (matchTarget H) (n*n) x

private lemma countRaw_spec (hn : 0 < n) (edge : Mat n N) (permit : Permit n N) (H : Target n N)
    (σ : Equiv.Perm (Fin n)) (x : Fin N → Bool) (he : ∀ r t, edge r t x = decide (σ.symm r = t)) :
    countRaw hn edge permit H x = (fiber σ (fun v d => permit v d x) (decodeTarget H x)).card := by
  classical
  rw [countRaw, acceptingCount_spec, ← Finset.card_filter]
  symm
  have hm (p : Pin n) : p ∈ fiber σ (fun v d => permit v d x) (decodeTarget H x) ↔
      livePath (symbols hn edge permit) (n*n) (code hn σ.symm p) x = true ∧
      matchTarget H (runPath (initial (2*n)) (fun _ => next) (n*n) (code hn σ.symm p)) x = true := by
    rw [code_live hn edge permit σ.symm x he, matchTarget_code hn]
    simp [fiber, and_comm]
  apply Finset.card_bij (fun p _ => code hn σ.symm p)
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hm _).mp hp⟩
  · intro p _ q _ h
    exact code_injective hn σ.symm h
  · intro y hy
    obtain ⟨hl,ha⟩ := (Finset.mem_filter.mp hy).2
    let p := decode hn σ.symm y
    have e : code hn σ.symm p = y := code_decode_live hn edge permit σ.symm x he y hl
    refine ⟨p,(hm _).2 ?_,e⟩
    rw [e]
    exact ⟨hl,ha⟩

private def permitOut (P : Permit n N) : Set (Sig N) := {f | ∃ v d, f = P v d}

private def symbolOut (edge : Mat n N) (P : Permit n N) : Set (Sig N) :=
  {f | ∃ r j e, f = symbolSignal edge P r j e}

def symbolCost (n : ℕ) := n*n*Fintype.card Symbol * (n*(2*n)+n+2*n+1+3*n+3)

def acceptCost (n : ℕ) :=
  n*n * (Fintype.card (State (2*n)) * (Fintype.card (State (2*n) × Symbol) * (10 * (4*n)))) +
     Fintype.card (State (2*n)) * (10 * (4*n))

private theorem allSymbolsB {A : Set (Sig N)} (edge : Mat n N) (P : Permit n N)
    (hm : matOut edge n ⊆ A) (hp : permitOut P ⊆ A)
    (hc : OrderCircuit.Consts A) : Build A (symbolOut edge P) (symbolCost n) := by
  let f (a : (Fin n × Fin n) × Symbol) := symbolSignal edge P a.1.1 a.1.2 a.2
  have h := allG (A := A) f _ (fun a => symbolSignalB edge P a.1.1 a.1.2 a.2 hm
    (fun v d => hp ⟨v,d,rfl⟩) hc.1 hc.2)
  refine relax h le_rfl ?_ ?_
  · rintro _ ⟨r,j,e,rfl⟩
    exact ⟨((r,j),e),rfl⟩
  · simp [symbolCost]

set_option maxHeartbeats 800000 in
theorem countRawB {A : Set (Sig N)} (hn : 0 < n) (edge : Mat n N) (P : Permit n N) (H : Target n N)
    (hm : matOut edge n ⊆ A) (hp : permitOut P ⊆ A) (ha : Set.range (matchTarget H) ⊆ A)
    (hc : OrderCircuit.Consts A) :
    Build A (Set.range (bitsOf (4*n) (countRaw hn edge P H))) (symbolCost n + acceptCost n) := by
  classical
  have ht := allSymbolsB edge P hm hp hc
  have hb : Build (A ∪ symbolOut edge P) (Set.range (bitsOf (4*n) (countRaw hn edge P H))) (acceptCost n) :=
    acceptingCountB _ _ _ _ (Or.inl hc.1) (Or.inl hc.2)
      (fun i _ e => Or.inr ⟨rowLabel hn i,rowOffset hn i,e,rfl⟩) (fun s => Or.inl (ha ⟨s,rfl⟩))
  exact thenG ht hb

end Automaton
namespace Automaton

open Compiler.Build LayoutCircuit OrderCircuit

variable {n N : ℕ}

def pinDigits (n : ℕ) : Pin n ≃ TernaryWord (2*n) where
  toFun p j := digitOf (p ((posEquiv n).symm j))
  invFun w v := optionOf (w (pos v))
  left_inv p := by
    funext v
    change optionOf (digitOf (p ((posEquiv n).symm ((posEquiv n) v)))) = p v
    rw [Equiv.symm_apply_apply, option_digit]
  right_inv w := by
    funext j
    change digitOf (optionOf (w ((posEquiv n) ((posEquiv n).symm j)))) = w j
    rw [Equiv.apply_symm_apply, digit_option]

noncomputable def wordFiber (σ : Equiv.Perm (Fin n)) (a : (Bool × Fin n) → Fin 3 → Bool) (h : Hist n) :
    Finset (TernaryWord (2*n)) := (fiber σ a h).map (pinDigits n).toEmbedding

lemma mem_wordFiber (σ : Equiv.Perm (Fin n)) (a : (Bool × Fin n) → Fin 3 → Bool) (h : Hist n)
    (q : TernaryWord (2*n)) : q ∈ wordFiber σ a h ↔ (pinDigits n).symm q ∈ fiber σ a h := by
  unfold wordFiber
  rw [Finset.mem_map]
  constructor
  · rintro ⟨p,hp,rfl⟩
    simpa using hp
  · intro hp
    exact ⟨_,hp,(pinDigits n).apply_symm_apply q⟩

def masked (P : Permit n N) (k : ℕ) (p : Prefix N (2*n)) (v : Bool × Fin n) (d : Fin 3) : Sig N :=
  if k ≤ (pos v).val then an (P v d) (digit p (pos v) d) else P v d

private lemma masked_spec (σ : Equiv.Perm (Fin n)) (P : Permit n N) (h : Hist n)
    (k : ℕ) (p : Prefix N (2*n)) (x : Fin N → Bool) :
    wordFiber σ (fun v d => masked P k p v d x) h =
      ternaryCandidates (wordFiber σ (fun v d => P v d x) h) k (p x) := by
  classical
  ext w
  simp only [ternaryCandidates, Finset.mem_filter, mem_wordFiber]
  let q := (pinDigits n).symm w
  change q ∈ fiber σ (fun v d => masked P k p v d x) h ↔
    q ∈ fiber σ (fun v d => P v d x) h ∧ ∀ j : Fin (2*n), k ≤ j.val → w j = p x j
  have hd (v : Bool × Fin n) : digitOf (q v) = w (pos v) := digit_option _
  have F (a : (Bool × Fin n) → Fin 3 → Bool) : q ∈ fiber σ a h ↔
      hist σ q = h ∧ ∀ v, a v (digitOf (q v)) = true := by
    simp [fiber]
  rw [F, F]
  simp only [masked, an, digit, hd]
  constructor
  · rintro ⟨hh,ha⟩
    refine ⟨⟨hh,?_⟩,?_⟩
    · intro v
      have hv := ha v
      split at hv
      · simp only [an, Bool.and_eq_true] at hv
        exact hv.1
      · exact hv
    · intro j hj
      let v := (posEquiv n).symm j
      have hv : pos v = j := (posEquiv n).apply_symm_apply j
      have h := ha v
      rw [hv, if_pos hj] at h
      simp only [an, digit, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2.symm
  · rintro ⟨⟨hh,ha⟩,hp⟩
    refine ⟨hh,fun v => ?_⟩
    split
    · rename_i h
      simp [an, digit, ha v, hp _ h]
      simpa only [hp _ h] using ha v
    · exact ha v

def queryCost (n : ℕ) := 6*n + (symbolCost n + acceptCost n)

noncomputable def query (hn : 0 < n) (edge : Mat n N) (P : Permit n N) (H : Target n N) : Query N (2*n) :=
  fun x k p => countRaw hn edge (masked P k (fun _ => p)) H x % 2^(4*n)

lemma query_lt (hn : 0 < n) (edge : Mat n N) (P : Permit n N) (H : Target n N)
    (x : Fin N → Bool) (k : ℕ) (p : TernaryWord (2*n)) : query hn edge P H x k p < 2^(4*n) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

lemma query_spec (hn : 0 < n) (edge : Mat n N) (P : Permit n N) (H : Target n N)
    (σ : Equiv.Perm (Fin n)) (x : Fin N → Bool) (he : ∀ r t, edge r t x = decide (σ.symm r = t))
    (k : ℕ) (p : TernaryWord (2*n)) :
    query hn edge P H x k p =
      ternaryCount (wordFiber σ (fun v d => P v d x) (decodeTarget H x)) k p := by
  unfold query
  rw [countRaw_spec _ _ _ _ _ _ he, Nat.mod_eq_of_lt (fiber_lt hn _ _ _)]
  unfold ternaryCount
  rw [← masked_spec σ P (decodeTarget H x) k (fun _ => p) x, wordFiber, Finset.card_map]

private lemma maskedB {A : Set (Sig N)} (P : Permit n N) (k : ℕ) (p : Prefix N (2*n))
    (ha : ∀ v d, P v d ∈ A) (hp : prefixOut p ⊆ A) : Build A (permitOut (masked P k p)) (6*n) := by
  let f (a : (Bool × Fin n) × Fin 3) := masked P k p a.1 a.2
  have H := allG (A := A) f 1 (fun ⟨v,d⟩ => by
    by_cases h : k ≤ (pos v).val
    · rw [show f (v,d) = an (P v d) (digit p (pos v) d) from if_pos h]
      exact andG (ha v d) (hp ⟨_,_,rfl⟩)
    · rw [show f (v,d) = P v d from if_neg h]
      exact relax (idle (Set.singleton_subset_iff.mpr (ha v d))) le_rfl le_rfl (by decide))
  refine relax H le_rfl ?_ (by simp; omega)
  rintro _ ⟨v,d,rfl⟩
  exact ⟨(v,d),rfl⟩

theorem queryB {A₀ : Set (Sig N)} (hn : 0 < n) (edge : Mat n N) (P : Permit n N) (H : Target n N)
    (hm : matOut edge n ⊆ A₀) (hp : ∀ v d, P v d ∈ A₀) (ha : Set.range (matchTarget H) ⊆ A₀)
    (hc : Consts A₀) : QueryBuild A₀ (4*n) (queryCost n) (query hn edge P H) := by
  intro A hA k _ p hprefix
  let Q := masked P k p
  have hQ := maskedB P k p (fun v d => hA (hp v d)) hprefix
  have hCount := countRawB (A := A ∪ permitOut Q) hn edge Q H
    (hm.trans (hA.trans Set.subset_union_left)) Set.subset_union_right
    (ha.trans (hA.trans Set.subset_union_left)) ⟨Or.inl (hA hc.1),Or.inl (hA hc.2)⟩
  apply relax (thenG hQ hCount) le_rfl ?_ le_rfl
  rintro _ ⟨i,rfl⟩
  refine ⟨i,?_⟩
  funext x
  simp only [bitsOf, query, Nat.testBit_mod_two_pow, i.isLt, decide_true, Bool.true_and]
  have eqn (v : Bool × Fin n) (d : Fin 3) : Q v d x = masked P k (fun _ => p x) v d x := by
    unfold Q masked an digit
    split <;> rfl
  have hx (l : ℕ) (a : Symbol) : symbols hn edge Q l a x =
      symbols hn edge (masked P k (fun _ => p x)) l a x := by
    cases a with
    | none => rfl
    | some e =>
      obtain ⟨b,d₀,d₁⟩ := e
      apply Bool.eq_iff_iff.mpr
      simp only [symbols, symbolSignal, an, Bool.and_eq_true, allowAt, anyFin_true, eqn]
  unfold countRaw
  simp_rw [acceptingCount_spec, livePath_spec, hx]

end Automaton

namespace ExactFront

open Compiler.Build Compiler.GateBridge LayoutCircuit Automaton OrderCircuit

variable {n : ℕ}

abbrev S (n : ℕ) := Sig (inputDim n)

private def inp (i : ℕ) (h : i < inputDim n) : S n := fun x => x ⟨i,h⟩

private lemma inp_mem (i : ℕ) (h : i < inputDim n) : inp i h ∈ base (inputDim n) :=
  Or.inl ⟨⟨i,h⟩,rfl⟩

private def permSig (r t : Fin n) : S n := inp (permOff n + (t.val*n+r.val)) (by
  have := block_lt t r.isLt
  unfold inputDim permOff
  omega)

private def allowSig (v : Bool × Fin n) (d : Fin 3) : S n := inp (allowOff n + (d.val*(2*n)+(pos v).val)) (by
  have := block_lt d (pos v).isLt
  unfold allowOff permOff inputDim
  omega)

private def histSig (q : Fields n) : S n := inp
    (countOff n + (q.1.val*((n+1)*(2*n+1))+(q.2.1.val*(2*n+1)+q.2.2.val))) (by
  have h := block_lt q.1 (block_lt q.2.1 q.2.2.isLt)
  unfold countOff allowOff permOff inputDim
  simp only [Nat.mul_assoc]
  omega)

private def someSig (v : Bool × Fin n) : S n := inp (someOff n+(pos v).val) (by
  have := (pos v).isLt
  unfold someOff countOff allowOff permOff inputDim
  omega)

private def valueSig (v : Bool × Fin n) : S n := inp (valueOff n+(pos v).val) (by
  have := (pos v).isLt
  unfold valueOff someOff countOff allowOff permOff inputDim
  omega)

private def indexSig (i : Fin (4*n)) : S n := inp (rankOff n+i.val) (by
  have := i.isLt
  unfold rankOff valueOff someOff countOff allowOff permOff inputDim
  omega)

private def pinInput (x : Fin (inputDim n) → Bool) : Pin n :=
  fun v => if someSig v x then some (valueSig v x) else none

private def pfx (n : ℕ) : Prefix (inputDim n) (2*n) := fun x => pinDigits n (pinInput x)

private noncomputable def indexInput (n : ℕ) (x : Fin (inputDim n) → Bool) : ℕ :=
  fromBits (fun j : Fin (4*n) => indexSig j x)

private lemma base_false (n : ℕ) : (fun _ => false) ∈ base (inputDim n) := Or.inr (Or.inl rfl)
private lemma base_true (n : ℕ) : (fun _ => true) ∈ base (inputDim n) := Or.inr (Or.inr rfl)

private theorem prefixB (n : ℕ) : Build (base (inputDim n)) (prefixOut (pfx n)) (12*n) := by
  let A := base (inputDim n)
  let f (a : Fin (2*n) × Fin 3) := digit (pfx n) a.1 a.2
  have H := allG (A := A) f 2 (fun ⟨j,d⟩ => by
    let v := (posEquiv n).symm j
    let su := someSig v
    let va := valueSig v
    have hs : su ∈ A := inp_mem _ _
    have hv : va ∈ A := inp_mem _ _
    rcases three_digits d with rfl | rfl | rfl
    · have e : f (j,0) = nt su := by
        funext x
        change decide (digitOf (if su x then some (va x) else none) = 0) = !(su x)
        cases su x <;> cases va x <;> decide
      rw [e]
      exact relax (notG hs) le_rfl le_rfl (by decide)
    · have e : f (j,1) = an su (nt va) := by
        funext x
        change decide (digitOf (if su x then some (va x) else none) = 1) = (su x && !va x)
        cases su x <;> cases va x <;> decide
      rw [e]
      exact thenG (notG hv) (andG (Or.inl hs) (Or.inr rfl))
    · have e : f (j,2) = an su va := by
        funext x
        change decide (digitOf (if su x then some (va x) else none) = 2) = (su x && va x)
        cases su x <;> cases va x <;> decide
      rw [e]
      exact relax (andG hs hv) le_rfl le_rfl (by decide))
  refine relax H le_rfl ?_ (by simp; omega)
  rintro _ ⟨j,d,rfl⟩
  exact ⟨(j,d),rfl⟩

private abbrev BF (n : ℕ) := base (inputDim n)
private abbrev PO (n : ℕ) := prefixOut (pfx n)
private abbrev MO (n : ℕ) := matOut (permSig (n := n)) n
private noncomputable abbrev TO (n : ℕ) := Set.range (matchTarget (histSig (n := n)))
private noncomputable abbrev Env (n : ℕ) := BF n ∪ ((MO n ∪ TO n) ∪ PO n)

private def setupCost (n : ℕ) := n*(n*n*(2*n)) + targetCost n + 12*n

private lemma prepB (n : ℕ) : Build (BF n) ((MO n ∪ TO n) ∪ PO n) (setupCost n) := by
  have HM : Build (BF n) (MO n) (n*(n*n*(2*n))) :=
    matPowB permSig n (fun _ _ => inp_mem _ _) (base_false n) (base_true n)
  have HT : Build (BF n) (TO n) (targetCost n) := matchTargetB histSig (fun _ => inp_mem _ _) (base_true n)
  exact bothG (bothG HM HT) (prefixB n)

private lemma env_consts (n : ℕ) : Consts (Env n) := ⟨Or.inl (base_false n),Or.inl (base_true n)⟩

private noncomputable def Q (hn : 0 < n) := query hn permSig allowSig histSig

private theorem Qbuild (hn : 0 < n) : QueryBuild (Env n) (4*n) (queryCost n) (Q hn) :=
  queryB hn permSig allowSig histSig
    (fun _ hf => Or.inr (Or.inl (Or.inl hf))) (fun _ _ => Or.inl (inp_mem _ _))
    (fun _ hf => Or.inr (Or.inl (Or.inr hf))) (env_consts n)

private noncomputable def countOutput (hn : 0 < n) := bitsOf (4*n) (fun x => Q hn x (2*n) (fun _ => 0))
private noncomputable def rankOutput (hn : 0 < n) := bitsOf (4*n) (fun x => ternaryRankFrom (Q hn x) (pfx n x) (2*n))
private noncomputable def validOutput (hn : 0 < n) : S n := fun x => (Q hn x 0 (pfx n x)).testBit 0

private noncomputable def selectOutput (hn : 0 < n) : Prefix (inputDim n) (2*n) :=
  fun x => ternarySelectFrom (Q hn x) (2*n) (fun _ => 0) (indexInput n x)

private noncomputable def pinOutput (hn : 0 < n) (b : Bool) (v : Bool × Fin n) : S n :=
  if b then digit (selectOutput hn) (pos v) 2 else nt (digit (selectOutput hn) (pos v) 0)

private def gatedCost (n : ℕ) := 2*queryCost n +
  (2*n)*(2*queryCost n+20*(4*n)+1) + (2*n)*(2*queryCost n+32*(4*n)+24) + 4*n

private def fullCost (n : ℕ) := setupCost n + gatedCost n

private noncomputable def outputs (hn : 0 < n) : Set (S n) :=
  (((Set.range (countOutput hn) ∪ {validOutput hn}) ∪ Set.range (rankOutput hn)) ∪
    Set.range (fun a : Bool × (Bool × Fin n) => pinOutput hn a.1 a.2))

private theorem outputsBuild (hn : 0 < n) : Build (BF n) (outputs hn) (fullCost n) := by
  have hp : prefixOut (pfx n) ⊆ Env n := fun _ h => Or.inr (Or.inr h)
  have hzero : prefixOut (m := 2*n) (fun _ _ => (0 : Fin 3)) ⊆ Env n := by
    rintro _ ⟨i,d,rfl⟩
    by_cases h : (0 : Fin 3) = d
    · have E : digit (N := inputDim n) (fun _ _ => (0 : Fin 3)) i d = fun _ => true := by
        funext x; simp [digit,h]
      rw [E]
      exact (env_consts n).2
    · have E : digit (N := inputDim n) (fun _ _ => (0 : Fin 3)) i d = fun _ => false := by
        funext x; simp [digit,h]
      rw [E]
      exact (env_consts n).1
  have HB : Build (Env n) (Set.range (countOutput hn)) (queryCost n) :=
    Qbuild hn _ le_rfl _ le_rfl _ hzero
  have HV : Build (Env n) {validOutput hn} (queryCost n) :=
    relax (Qbuild hn _ le_rfl 0 (Nat.zero_le _) _ hp) le_rfl
      (Set.singleton_subset_iff.mpr ⟨⟨0,by omega⟩,rfl⟩) le_rfl
  have HR := rankBuild (Qbuild hn) (env_consts n) (pfx n) hp
  have HI : Available (Env n) (bitsOf (4*n) (indexInput n)) := by
    intro i
    have e : bitsOf (4*n) (indexInput n) i = indexSig i := funext fun x => fromBits_bit _ _
    rw [e]
    exact Or.inl (inp_mem _ _)
  have HS := selectBuild (Qbuild hn) (env_consts n) (query_lt hn _ _ _) (indexInput n) HI (fun _ => fromBits_lt _)
  let A := Env n ∪ prefixOut (selectOutput hn)
  let f (a : Bool × (Bool × Fin n)) := pinOutput hn a.1 a.2
  have HT : Build A (Set.range f) (4*n) := by
    apply relax (allG (A := A) f 1 ?_) le_rfl le_rfl (by simp; omega)
    rintro ⟨b,v⟩
    cases b
    · exact notG (Or.inr ⟨pos v,0,rfl⟩)
    · exact relax (idle (Set.singleton_subset_iff.mpr (Or.inr ⟨pos v,2,rfl⟩))) le_rfl le_rfl (by decide)
  have Hpins := thenG HS HT
  apply thenG (prepB n)
  exact relax (bothG (bothG (bothG HB HV) HR) Hpins) le_rfl le_rfl (by unfold gatedCost; omega)


open Compiler.Build Compiler.GateBridge LayoutCircuit Automaton OrderCircuit
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

variable {n : ℕ}

private def wordVal {w : ℕ} (f : Fin w → Bool) : ℕ := ∑ j : Fin w, (f j).toNat * 2^j.val

private def postedHist (σ : Equiv.Perm (Fin n)) (p : Pin n) (r b : Fin (n+1)) : ℕ :=
  ((Finset.univ : Finset ((Bool × Fin n) → Bool)).filter (fun x =>
    (∀ v, p v = none ∨ p v = some (x v)) ∧
    (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,i))).card = r.val ∧
    (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,σ i))).card = b.val)).card

private def postedKey (p : Pin n) : ℕ :=
  ∑ v : Bool × Fin n, (if (p v).isSome then 1+((p v).getD false).toNat else 0) *
    3^(v.2.val + (if v.1 then n else 0))

private noncomputable def shownFiber (σ : Equiv.Perm (Fin n)) (a : (Bool × Fin n) → Fin 3 → Bool)
    (H : Fin (n+1) → Fin (n+1) → Fin (2*n+1) → Bool) : Finset (Pin n) :=
  Finset.univ.filter (fun p => postedHist σ p = (fun r b => wordVal (H r b)) ∧
    ∀ v, a v (digitOf (p v)) = true)

private lemma shownFiber_eq (σ : Equiv.Perm (Fin n)) (a : (Bool × Fin n) → Fin 3 → Bool)
    (H : Fin (n+1) → Fin (n+1) → Fin (2*n+1) → Bool) : shownFiber σ a H = fiber σ a (fun r b => wordVal (H r b)) := by
  have he (p : Pin n) : postedHist σ p = hist σ p := funext fun r => funext fun b => (hist_posted σ p r b).symm
  ext p
  simp [shownFiber, fiber, he]

private lemma key_as_word (p : Pin n) : postedKey p = ternaryKey (pinDigits n p) := by
  symm
  unfold ternaryKey
  rw [← (posEquiv n).sum_comp (fun j : Fin (2*n) => (pinDigits n p j).val * 3^j.val)]
  apply Finset.sum_congr rfl
  intro v _
  have e : pinDigits n p (posEquiv n v) = digitOf (p v) := by
    change digitOf (p ((posEquiv n).symm (posEquiv n v))) = _
    rw [Equiv.symm_apply_apply]
  rw [e]
  rcases v with ⟨b,i⟩
  cases b <;> rcases h : p (_,i) with _ | (_|_) <;> simp [h, digitOf, posEquiv, pos, wordVal]

private lemma ternaryCount_zero {m : ℕ} (S : Finset (TernaryWord m)) (w : TernaryWord m) :
    ternaryCount S 0 w = if w ∈ S then 1 else 0 := by
  classical
  have eqs (q : TernaryWord m) : (∀ j, 0 ≤ (j : Fin m).val → q j = w j) ↔ q = w := by
    simp only [Nat.zero_le, true_implies]
    exact ⟨funext, fun h => congrFun h⟩
  unfold ternaryCount ternaryCandidates
  simp_rw [eqs]
  by_cases h : w ∈ S
  · have e : S.filter (fun q => q = w) = {w} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨And.right, fun he => ⟨he.symm ▸ h,he⟩⟩
    simp [e,h]
  · have e : S.filter (fun q => q = w) = ∅ := by
      ext q
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨hq,rfl⟩
      exact h hq
    simp [e,h]

private noncomputable def orders (σ : Equiv.Perm (Fin n)) (a : (Bool × Fin n) → Fin 3 → Bool) (h : Hist n) :
    Fin (fiber σ a h).card ≃ {p : Pin n // p ∈ fiber σ a h} :=
  (finCongr (show (fiber σ a h).card = (wordFiber σ a h).card by rw [wordFiber, Finset.card_map])).trans
    ((ternaryEquiv (wordFiber σ a h)).trans
      (Equiv.subtypeEquiv (pinDigits n).symm (mem_wordFiber σ a h)))

private lemma order_as_word (σ : Equiv.Perm (Fin n)) (a : (Bool × Fin n) → Fin 3 → Bool) (h : Hist n)
    (i : Fin (fiber σ a h).card) :
    pinDigits n (orders σ a h i).val =
      (ternaryEquiv (wordFiber σ a h) ⟨i.val, by rw [wordFiber, Finset.card_map]; exact i.isLt⟩).val := by
  unfold orders
  simp [Fin.cast]

private lemma order_strict (σ : Equiv.Perm (Fin n)) (a : (Bool × Fin n) → Fin 3 → Bool) (h : Hist n)
    (i j : Fin (fiber σ a h).card) (hij : i < j) :
    postedKey (orders σ a h i).val < postedKey (orders σ a h j).val := by
  rw [key_as_word, key_as_word, order_as_word, order_as_word]
  exact ternaryEquiv_strict _ hij

set_option maxHeartbeats 1000000 in
private theorem semantics (hn : 0 < n) (σ : Equiv.Perm (Fin n)) (a : (Bool × Fin n) → Fin 3 → Bool)
    (H : Fin (n+1) → Fin (n+1) → Fin (2*n+1) → Bool) :
    let F := shownFiber σ a H
    ∃ e : Fin F.card ≃ {p : Pin n // p ∈ F},
      (∀ i j : Fin F.card, i < j → postedKey (e i).val < postedKey (e j).val) ∧
      ∀ (p : Pin n) (junk : Bool × Fin n → Bool) (z : Fin (4*n) → Bool),
        let x := encodeFn σ a H p junk z
        let q : Pin n := fun v => if pinOutput hn false v x then some (pinOutput hn true v x) else none
        wordVal (fun j => countOutput hn j x) = F.card ∧ (validOutput hn x = true ↔ p ∈ F) ∧
          ∀ i : Fin F.card, (p = (e i).val → wordVal (fun j => rankOutput hn j x) = i.val) ∧
            (wordVal z = i.val → q = (e i).val) := by
  dsimp only
  rw [shownFiber_eq]
  let h : Hist n := fun r b => wordVal (H r b)
  let F := fiber σ a h
  let S := wordFiber σ a h
  let e := orders σ a h
  refine ⟨e, order_strict σ a h, ?_⟩
  intro p junk z
  let x := encodeFn σ a H p junk z
  have hperm (r t : Fin n) : permSig r t x = decide (σ.symm r = t) := by
    change (encode σ a H p junk z).getD (permOff n + (t.val*n+r.val)) false = _
    rw [encode_getD_perm]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro he; exact (σ.symm_apply_eq.mpr he.symm)
    · intro he; rw [← he, σ.apply_symm_apply]
  have hallow (v : Bool × Fin n) (d : Fin 3) : allowSig v d x = a v d := by
    exact encode_getD_allow σ a H p junk z v d false
  have hH (r b : Fin (n+1)) (k : Fin (2*n+1)) : histSig (r,b,k) x = H r b k := by
    exact encode_getD_count σ a H p junk z r b k false
  have htarget : decodeTarget histSig x = h := by
    funext r b
    unfold decodeTarget h wordVal
    simp only [hH, fromBits_eq_sum]
  have hpin : pinInput x = p := by
    funext v
    have hs : someSig v x = (p v).isSome := encode_getD_some σ a H p junk z v false
    have hv : valueSig v x = (p v).getD (junk v) := encode_getD_value σ a H p junk z v false
    cases hp : p v <;> simp [pinInput, hs, hv, hp]
  have hpfx : pfx n x = pinDigits n p := congrArg (pinDigits n) hpin
  have hindex : indexInput n x = wordVal z := by
    unfold indexInput wordVal
    rw [fromBits_eq_sum]
    have hi (j : Fin (4*n)) : indexSig j x = z j := encode_getD_rank σ a H p junk z j false
    simp only [hi]
  have hQ : Q hn x = ternaryCount S := by
    funext k w
    unfold Q
    rw [query_spec _ _ _ _ σ x hperm, htarget]
    simp only [hallow]
    rfl
  have hN : (Q hn x (2*n) (fun _ => 0)) = F.card := by
    rw [hQ, ternaryCount_top]
    exact Finset.card_map _
  have hvalid : validOutput hn x = true ↔ p ∈ F := by
    unfold validOutput
    rw [hQ, hpfx, ternaryCount_zero]
    have hm : pinDigits n p ∈ S ↔ p ∈ F := by
      simpa [S,F] using mem_wordFiber σ a h (pinDigits n p)
    by_cases hp : p ∈ F
    · have hw := hm.mpr hp
      simp [hw,hp]
    · have hw : pinDigits n p ∉ S := fun hw => hp (hm.mp hw)
      simp [hw,hp]
  have hCard : S.card = F.card := Finset.card_map _
  refine ⟨?_,hvalid,?_⟩
  · change wordVal (fun j : Fin (4*n) => (Q hn x (2*n) (fun _ => 0)).testBit j.val) = F.card
    rw [hN]
    exact val_testBit_of_lt (fiber_lt hn σ a h)
  · intro i
    refine ⟨?_,?_⟩
    · intro hi
      have hv : ternaryRankFrom (Q hn x) (pfx n x) (2*n) = i.val := by
        rw [hQ, hpfx, hi, order_as_word]
        exact ternaryEquiv_rank S ⟨i.val, i.isLt.trans_le hCard.ge⟩
      change wordVal (fun j : Fin (4*n) => (ternaryRankFrom (Q hn x) (pfx n x) (2*n)).testBit j.val) = _
      rw [hv]
      exact val_testBit_of_lt (i.isLt.trans (fiber_lt hn σ a h))
    · intro hi
      have hs : selectOutput hn x = pinDigits n (e i).val := by
        unfold selectOutput
        rw [hQ, hindex, hi, order_as_word]
        exact ternaryEquiv_select S _ ⟨i.val, i.isLt.trans_le hCard.ge⟩
      funext v
      have hv : selectOutput hn x (pos v) = digitOf ((e i).val v) := by
        rw [hs]
        change digitOf ((e i).val ((posEquiv n).symm (posEquiv n v))) = _
        rw [Equiv.symm_apply_apply]
      change (if pinOutput hn false v x then some (pinOutput hn true v x) else none) = _
      simp only [pinOutput, Bool.true_eq, ite_true, Bool.false_eq_true, ite_false, nt, digit, hv]
      rcases (e i).val v with _ | (_|_) <;> rfl

private def SqBound (f : ℕ → ℕ) : Prop := ∃ C : ℕ, ∀ n, f n ≤ 2^(C*(Nat.sqrt n+1))

private lemma sq_const (c : ℕ) : SqBound (fun _ => c) := by
  refine ⟨c, fun n => Nat.lt_two_pow_self.le.trans ?_⟩
  exact Nat.pow_le_pow_right (by decide) (by have h := Nat.mul_le_mul_left c (Nat.succ_pos (Nat.sqrt n)); simpa only [Nat.mul_one] using h)

private lemma sq_id : SqBound (fun n => n) :=
  ⟨2, fun n => (Nat.le_succ n).trans (succ_le_two_pow_sqrt n)⟩

private lemma sq_inv : SqBound (fun n => (Part4 (2*n)).card) := ⟨140, part4_double_card_le⟩

private lemma sq_add {f g : ℕ → ℕ} (hf : SqBound f) (hg : SqBound g) : SqBound (fun n => f n + g n) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  refine ⟨a+b+1, fun n => ?_⟩
  let k := Nat.sqrt n+1
  have Ha : f n ≤ 2^((a+b)*k) := (ha n).trans (Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_right _ (by omega)))
  have Hb : g n ≤ 2^((a+b)*k) := (hb n).trans (Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_right _ (by omega)))
  calc f n + g n ≤ 2^((a+b)*k) + 2^((a+b)*k) := Nat.add_le_add Ha Hb
    _ = 2^((a+b)*k+1) := by rw [Nat.pow_succ]; omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      change (a+b)*k+1 ≤ (a+b+1)*k
      rw [show (a+b+1)*k = (a+b)*k+k by ring]
      dsimp [k]
      omega)

private lemma sq_mul {f g : ℕ → ℕ} (hf : SqBound f) (hg : SqBound g) : SqBound (fun n => f n * g n) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  refine ⟨a+b, fun n => (Nat.mul_le_mul (ha n) (hb n)).trans_eq ?_⟩
  rw [← pow_add, Nat.add_mul]

private lemma sq_full : SqBound (fun n => 3 + fullCost n) := by
  have hN1 : SqBound (fun n => n+1) := sq_add sq_id (sq_const 1)
  have hM1 : SqBound (fun n => 2*n+1) := sq_add (sq_mul (sq_const 2) sq_id) (sq_const 1)
  have hs : SqBound (fun n => Fintype.card (State (2*n))) := by
    simp only [state_card]
    exact sq_mul sq_inv (sq_mul hM1 (sq_mul hM1 (sq_add (sq_const 1)
      (sq_mul hM1 (sq_mul (sq_const 2) (sq_mul hM1 (sq_const 2)))))))
  have hS : Fintype.card LayoutCircuit.Symbol = 19 := by simp [LayoutCircuit.Symbol]
  have hs' (n : ℕ) : Fintype.card (State (2*n) × LayoutCircuit.Symbol) = Fintype.card (State (2*n))*19 := by
    rw [Fintype.card_prod, hS]
  have hF (n : ℕ) : Fintype.card (Fields n) = (n+1)*((n+1)*(2*n+1)) := by simp [Fields]
  have hT : SqBound targetCost := by
    change SqBound (fun n => Fintype.card (State (2*n)) * (2 * Fintype.card (Fields n)))
    simp only [hF]
    exact sq_mul hs (sq_mul (sq_const 2) (sq_mul hN1 (sq_mul hN1 hM1)))
  have hNN := sq_mul sq_id sq_id
  have h2N := sq_mul (sq_const 2) sq_id
  have h4N := sq_mul (sq_const 4) sq_id
  have h40N := sq_mul (sq_const 10) h4N
  have hA : SqBound acceptCost := by
    change SqBound (fun n => n*n * (Fintype.card (State (2*n)) *
      (Fintype.card (State (2*n) × LayoutCircuit.Symbol) * (10*(4*n)))) +
      Fintype.card (State (2*n)) * (10*(4*n)))
    simp only [hs']
    exact sq_add (sq_mul hNN (sq_mul hs (sq_mul (sq_mul hs (sq_const 19)) h40N))) (sq_mul hs h40N)
  have hY : SqBound symbolCost := by
    change SqBound (fun n => n*n*Fintype.card LayoutCircuit.Symbol * (n*(2*n)+n+2*n+1+3*n+3))
    simp only [hS]
    exact sq_mul (sq_mul hNN (sq_const 19)) (sq_add
      (sq_add (sq_add (sq_add (sq_add (sq_mul sq_id h2N) sq_id) h2N) (sq_const 1))
        (sq_mul (sq_const 3) sq_id)) (sq_const 3))
  have hQ : SqBound queryCost :=
    sq_add (sq_mul (sq_const 6) sq_id) (sq_add hY hA)
  have hSetup : SqBound setupCost :=
    sq_add (sq_add (sq_mul sq_id (sq_mul hNN h2N)) hT) (sq_mul (sq_const 12) sq_id)
  have h2Q := sq_mul (sq_const 2) hQ
  have hG : SqBound gatedCost := sq_add
    (sq_add (sq_add h2Q (sq_mul h2N (sq_add (sq_add h2Q (sq_mul (sq_const 20) h4N)) (sq_const 1))))
      (sq_mul h2N (sq_add (sq_add h2Q (sq_mul (sq_const 32) h4N)) (sq_const 24)))) h4N
  exact sq_add (sq_const 3) (sq_add hSetup hG)

lemma sqrt_budget : ∃ C : ℕ, 0 < C ∧ ∀ n, 3 + fullCost n ≤ 2^(C*(Nat.sqrt n+1)) := by
  obtain ⟨C,h⟩ := sq_full
  exact ⟨C+1, by omega, fun n => (h n).trans (Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_right _ (Nat.le_succ _)))⟩

set_option maxHeartbeats 1200000 in
theorem construct (hn : 0 < n) :
    ∃ (g : Circuit) (num ord : Fin (4*n) → Fin (inputDim n + g.size))
      (valid : Fin (inputDim n + g.size)) (pinWire : Bool → Bool × Fin n → Fin (inputDim n + g.size)),
      ReadsBack (inputDim n) g ∧ g.size ≤ 3 + fullCost n ∧
      (∀ gate ∈ g.gates, Legal gate.op gate.inputs.length) ∧
      ∀ (σ : Equiv.Perm (Fin n)) (a : (Bool × Fin n) → Fin 3 → Bool)
        (H : Fin (n+1) → Fin (n+1) → Fin (2*n+1) → Bool),
        let F := shownFiber σ a H
        ∃ e : Fin F.card ≃ {p : Pin n // p ∈ F},
          (∀ i j : Fin F.card, i < j → postedKey (e i).val < postedKey (e j).val) ∧
          ∀ (p : Pin n) (junk : Bool × Fin n → Bool) (z : Fin (4*n) → Bool),
            let ws := g.wires (encode σ a H p junk z)
            let q : Pin n := fun v => if ws.getD (pinWire false v).val false
              then some (ws.getD (pinWire true v).val false) else none
            wordVal (fun j => ws.getD (num j).val false) = F.card ∧ (ws.getD valid.val false = true ↔ p ∈ F) ∧
              ∀ i : Fin F.card, (p = (e i).val → wordVal (fun j => ws.getD (ord j).val false) = i.val) ∧
                (wordVal z = i.val → q = (e i).val) := by
  have hinput : 0 < inputDim n := by unfold inputDim; omega
  obtain ⟨g,w,hback,hsize,hlegal,h⟩ := Front.realize hinput (outputsBuild hn)
  let N (j : Fin (4*n)) : outputs hn := ⟨countOutput hn j, Or.inl (Or.inl (Or.inl ⟨j,rfl⟩))⟩
  let R (j : Fin (4*n)) : outputs hn := ⟨rankOutput hn j, Or.inl (Or.inr ⟨j,rfl⟩)⟩
  let V : outputs hn := ⟨validOutput hn, Or.inl (Or.inl (Or.inr rfl))⟩
  let P (b : Bool) (v : Bool × Fin n) : outputs hn := ⟨pinOutput hn b v, Or.inr ⟨(b,v),rfl⟩⟩
  refine ⟨g,fun j => w (N j),fun j => w (R j),w V,fun b v => w (P b v),hback,hsize,hlegal,?_⟩
  intro σ a H
  obtain ⟨e,he,hs⟩ := semantics hn σ a H
  refine ⟨e,he,fun p junk z => ?_⟩
  have hw (f : outputs hn) : (g.wires (encode σ a H p junk z)).getD (w f).val false =
      f.val (encodeFn σ a H p junk z) := by
    rw [← ofFn_encodeFn]
    exact h f _
  dsimp only
  simp_rw [hw]
  exact hs p junk z

end ExactFront
end PEqualNP.Outside.L_pcx_393_aux

open PEqualNP.Outside.L_pcx_393_aux

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_pcx_393 :
∃ C : ℕ, 0 < C ∧ ∀ t : ℕ,
  let n := t+1
  let I := Fin n
  let J := Fin (n+1)
  let V := Bool × I
  let W := Fin (2*n+1)
  let K := Fin (4*n)
  let P := V → Option Bool
  let hist := fun (σ : Equiv.Perm I) (p : P) (r b : J) =>
    ((Finset.univ : Finset (V → Bool)).filter (fun x =>
      (∀ v, p v = none ∨ p v = some (x v)) ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = r.val ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,σ i))).card = b.val)).card
  let raw := fun (x : V → Bool) => List.ofFn (fun i : I => x (false,i)) ++ List.ofFn (fun i : I => x (true,i))
  let tag := fun (o : Option Bool) => if o.isSome then 1+(o.getD false).toNat else 0
  let val := fun (z : K → Bool) => ∑ k : K, (z k).toNat * 2^k.val
  let key := fun (p : P) => ∑ v : V, tag (p v) * 3^(v.2.val + (if v.1 then n else 0))
  let inputs := 2+n*n+6*n+(n+1)*(n+1)*(2*n+1)+8*n
  ∃ (g : PEqualNP.CircuitLowerBounds.Circuit) (num ord : K → Fin (inputs+g.size))
    (valid : Fin (inputs+g.size)) (pinWire : Bool → V → Fin (inputs+g.size)),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs g ∧ g.size ≤ 2^(C*(Nat.sqrt n+1)) ∧
    (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
      (gate.op = .not ∧ gate.inputs.length = 1)) ∧
    ∀ (σ : Equiv.Perm I) (allow : V → Fin 3 → Bool) (H : J → J → W → Bool),
      let table := fun (r b : J) => ∑ k : W, (H r b k).toNat * 2^k.val
      let fiber := (Finset.univ : Finset P).filter (fun p => hist σ p = table ∧ ∀ v, allow v (if (p v).isSome then (if (p v).getD false then 2 else 1) else 0) = true)
      let countBits := (List.ofFn (fun r : J => (List.ofFn (fun b : J => List.ofFn (H r b))).flatten)).flatten
      let permBits := (List.ofFn (fun i : I => List.ofFn (fun j : I => decide (σ i = j)))).flatten
      let allowBits := (List.ofFn (fun k : Fin 3 => raw (fun v => allow v k))).flatten
      ∃ e : Fin fiber.card ≃ {p : P // p ∈ fiber},
        (∀ i j : Fin fiber.card, i < j → key (e i).val < key (e j).val) ∧
        ∀ (p : P) (junk : V → Bool) (z : K → Bool),
        let ws := g.wires ([false,true] ++ permBits ++ allowBits ++ countBits ++ raw (fun v => (p v).isSome) ++
          raw (fun v => (p v).getD (junk v)) ++ List.ofFn z)
        let q : P := fun v => if ws.getD (pinWire false v).val false then some (ws.getD (pinWire true v).val false) else none
        val (fun k => ws.getD (num k).val false) = fiber.card ∧
          (ws.getD valid.val false = true ↔ p ∈ fiber) ∧
          ∀ i : Fin fiber.card,
            (p = (e i).val → val (fun k => ws.getD (ord k).val false) = i.val) ∧
            (val z = i.val → q = (e i).val) := by
  obtain ⟨C,hC,hCbound⟩ := ExactFront.sqrt_budget
  refine ⟨C,hC,fun t => ?_⟩
  dsimp only
  obtain ⟨g,num,ord,valid,pinWire,hback,hsize,hlegal,hcorrect⟩ := ExactFront.construct (Nat.succ_pos t)
  refine ⟨g,num,ord,valid,pinWire,hback,hsize.trans (hCbound _),hlegal,?_⟩
  intro σ allow H
  have hs := hcorrect σ allow H
  dsimp only [ExactFront.shownFiber, ExactFront.postedHist, ExactFront.wordVal, ExactFront.postedKey, encode,
    allowBits, countBits, permBits, raw, Automaton.digitOf] at hs
  exact hs
