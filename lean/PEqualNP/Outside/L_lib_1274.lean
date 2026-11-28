import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1274_aux

namespace GateBridge

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (Monotone2)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

variable {α : Type*}

def Scheduled (n : Nat) (F : α → (Fin n → Bool) → Bool) (k : Nat) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ Monotone2 ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
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

theorem start {n : Nat} {F : α → (Fin n → Bool) → Bool}
    (input : Fin n → α) (h : ∀ i x, F (input i) x = x i) :
    Scheduled n F 0 (Set.range input) := by
  refine ⟨[], rfl, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp [Monotone2]
  · intro a ha
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    refine ⟨i.val, by simp, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, h i x]

theorem restrict {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k S) (hsub : T ⊆ S) : Scheduled n F k T := by
  obtain ⟨gs, hs, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hr, hf, fun a ha => hw a (hsub ha)⟩

theorem realizeDeps {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x)
    (deps : List α) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List Nat, is.length = deps.length ∧ (∀ i ∈ is, i < n + k) ∧
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

theorem push {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    (h : Scheduled n F k S) (op : GateOp) (deps : List α) (out : α)
    (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
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

end GateBridge

namespace Build049

open PEqualNP.CircuitLowerBounds

variable {n : Nat}
abbrev Sig (n : Nat) := (Fin n → Bool) → Bool
def Build (A B : Set (Sig n)) (b : Nat) : Prop :=
  True ∧ (∀ {m S}, GateBridge.Scheduled n id m S → A ⊆ S →
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B))

theorem Build.run {A B : Set (Sig n)} {b m S} (H : Build A B b)
    (HS : GateBridge.Scheduled n id m S) (hA : A ⊆ S) :
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B) := H.2 HS hA

theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : Build A B 0 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

theorem relax {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c, hc, HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c, hc.trans h, GateBridge.restrict HS' (Set.union_subset_union le_rfl hB)⟩

theorem seq {A B C : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  obtain ⟨d, hd, K⟩ := H.run HS hA
  obtain ⟨e, he, K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d + e, Nat.add_le_add hd he, by simpa [Nat.add_assoc, Set.union_assoc] using K'⟩

theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨1, le_rfl, ?_⟩
  have h := GateBridge.push HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridge.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

def an (f g : Sig n) : Sig n := fun x => f x && g x
def or (f g : Sig n) : Sig n := fun x => f x || g x

theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {an f g} 1 :=
  one .and [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {or f g} 1 :=
  one .or [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, or])

theorem constG {A : Set (Sig n)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b
  · exact one .or [] (by simp) (by simp) (by simp) _ (by intro; rfl)
  · exact one .and [] (by simp) (by simp) (by simp) _ (by intro; rfl)

theorem listBuild {α : Type*} {A : Set (Sig n)} (xs : List α)
    (F : α → Sig n) (c : Nat) (H : ∀ a ∈ xs, Build A {F a} c) :
    Build A {f | ∃ a ∈ xs, f = F a} (xs.length * c) := by
  induction xs with
  | nil =>
    exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp)
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ {F a}) Set.subset_union_left le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ ?_
    · rintro f ⟨b, hb, rfl⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr ⟨b, hb, rfl⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]

theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c : Nat)
    (H : ∀ i, Build A {F i} c) : Build A (Set.range F) (k * c) := by
  have h := listBuild (List.finRange k) F c (fun i _ => H i)
  rw [List.length_finRange] at h
  refine relax h le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, List.mem_finRange i, rfl⟩

end Build049

namespace Bitonic

def bitonicMerge (off : Nat) : Nat → Bool → List (Nat × Nat × Bool)
  | 0, _ => []
  | k + 1, asc =>
    let h := 2 ^ k
    let stage := (List.range h).map (fun i => (off + i, off + h + i, asc))
    stage ++ bitonicMerge off k asc ++ bitonicMerge (off + h) k asc

def bitonicSort (off : Nat) : Nat → Bool → List (Nat × Nat × Bool)
  | 0, _ => []
  | k + 1, asc =>
    let h := 2 ^ k
    bitonicSort off k true ++ bitonicSort (off + h) k false ++ bitonicMerge off (k + 1) asc

theorem bitonicMerge_length (off : Nat) : ∀ k asc,
    2 * (bitonicMerge off k asc).length = k * 2 ^ k
  | 0, _ => by simp [bitonicMerge]
  | k + 1, asc => by
    simp only [bitonicMerge, List.length_append, List.length_map, List.length_range]
    have h1 := bitonicMerge_length off k asc
    have h2 := bitonicMerge_length (off + 2 ^ k) k asc
    have he : (k + 1) * 2 ^ (k + 1) = 2 * 2 ^ k + 2 * (k * 2 ^ k) := by
      rw [Nat.pow_succ, Nat.succ_mul]
      rw [← Nat.mul_assoc k (2 ^ k) 2, Nat.mul_comm (k * 2 ^ k) 2, Nat.mul_comm (2 ^ k) 2, Nat.add_comm]
    omega

theorem bitonicSort_length (off : Nat) : ∀ k asc,
    4 * (bitonicSort off k asc).length = k * (k + 1) * 2 ^ k
  | 0, _ => by simp [bitonicSort]
  | k + 1, asc => by
    simp only [bitonicSort, List.length_append]
    have h1 := bitonicSort_length off k true
    have h2 := bitonicSort_length (off + 2 ^ k) k false
    have hm := bitonicMerge_length off (k + 1) asc
    have he : (k + 1) * (k + 1 + 1) * 2 ^ (k + 1) =
        2 * (k * (k + 1) * 2 ^ k) + 2 * ((k + 1) * 2 ^ (k + 1)) := by
      rw [Nat.pow_succ]
      have e1 : k * (k + 1) * 2 ^ k = (k + 1) * k * 2 ^ k := by rw [Nat.mul_comm k (k + 1)]
      have e2 : (k + 1) * (k + 2) * (2 ^ k * 2) =
          (k + 1) * k * (2 ^ k * 2) + (k + 1) * 2 * (2 ^ k * 2) := by
        rw [Nat.mul_add (k + 1) k 2, Nat.add_mul]
      rw [e2]
      have e3 : 2 * (k * (k + 1) * 2 ^ k) = (k + 1) * k * (2 ^ k * 2) := by
        rw [e1, Nat.mul_comm 2, Nat.mul_assoc]
      have e4 : 2 * ((k + 1) * (2 ^ k * 2)) = (k + 1) * 2 * (2 ^ k * 2) := by
        rw [← Nat.mul_assoc 2 (k + 1), Nat.mul_comm 2 (k + 1)]
      omega
    omega

theorem bitonicMerge_mem (off : Nat) : ∀ k asc c,
    c ∈ bitonicMerge off k asc → off ≤ c.1 ∧ c.1 < c.2.1 ∧ c.2.1 < off + 2 ^ k
  | 0, _, c, hc => by simp [bitonicMerge] at hc
  | k + 1, asc, c, hc => by
    simp only [bitonicMerge, List.mem_append, List.mem_map, List.mem_range] at hc
    rcases hc with (⟨i, hi, rfl⟩ | hc) | hc
    · dsimp only
      rw [Nat.pow_succ]
      omega
    · have h := bitonicMerge_mem off k asc c hc
      rw [Nat.pow_succ]
      omega
    · have h := bitonicMerge_mem (off + 2 ^ k) k asc c hc
      rw [Nat.pow_succ]
      omega

theorem bitonicSort_mem (off : Nat) : ∀ k asc c,
    c ∈ bitonicSort off k asc → off ≤ c.1 ∧ c.1 < c.2.1 ∧ c.2.1 < off + 2 ^ k
  | 0, _, c, hc => by simp [bitonicSort] at hc
  | k + 1, asc, c, hc => by
    simp only [bitonicSort, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · have h := bitonicSort_mem off k true c hc
      rw [Nat.pow_succ]
      omega
    · have h := bitonicSort_mem (off + 2 ^ k) k false c hc
      rw [Nat.pow_succ]
      omega
    · exact bitonicMerge_mem off (k + 1) asc c hc

def swapBit (k1 k2 : Nat) (asc : Bool) : Bool :=
  if asc then decide (k2 < k1) else decide (k1 < k2)

def applySwap {α : Type*} (u v : Nat) (sw : Bool) (st : Nat → α) : Nat → α :=
  fun idx =>
    if sw then
      if idx = u then st v else if idx = v then st u else st idx
    else st idx

theorem applySwap_invol {α : Type*} (u v : Nat) (sw : Bool) (st : Nat → α) :
    applySwap u v sw (applySwap u v sw st) = st := by
  funext idx
  simp only [applySwap]
  cases sw with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    by_cases h1 : idx = u
    · subst h1
      by_cases huv : idx = v
      · subst huv; simp
      · simp [huv, Ne.symm huv]
    · by_cases h2 : idx = v
      · subst h2; simp [h1]
      · simp [h1, h2]

theorem applySwap_comp {α β : Type*} (u v : Nat) (sw : Bool) (f : α → β) (st : Nat → α) :
    applySwap u v sw (fun idx => f (st idx)) = fun idx => f (applySwap u v sw st idx) := by
  funext idx
  simp only [applySwap]
  cases sw <;> simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : idx = u
  · simp [h1]
  · by_cases h2 : idx = v
    · subst h2; simp [h1]
    · simp [h1, h2]

def runNet {α : Type*} (key : α → Nat) : List (Nat × Nat × Bool) → (Nat → α) → (Nat → α)
  | [], st => st
  | (u, v, asc) :: rest, st =>
    let sw := swapBit (key (st u)) (key (st v)) asc
    runNet key rest (applySwap u v sw st)

theorem runNet_append {α : Type*} (key : α → Nat) (n1 n2 : List (Nat × Nat × Bool)) (st : Nat → α) :
    runNet key (n1 ++ n2) st = runNet key n2 (runNet key n1 st) := by
  induction n1 generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [List.cons_append, runNet]
    exact ih _

def netSwaps {α : Type*} (key : α → Nat) : List (Nat × Nat × Bool) → (Nat → α) → List (Nat × Nat × Bool)
  | [], _ => []
  | (u, v, asc) :: rest, st =>
    let sw := swapBit (key (st u)) (key (st v)) asc
    (u, v, sw) :: netSwaps key rest (applySwap u v sw st)

def replaySwaps {β : Type*} : List (Nat × Nat × Bool) → (Nat → β) → (Nat → β)
  | [], st => st
  | (u, v, sw) :: rest, st => replaySwaps rest (applySwap u v sw st)

theorem replaySwaps_append {β : Type*} (s1 s2 : List (Nat × Nat × Bool)) (st : Nat → β) :
    replaySwaps (s1 ++ s2) st = replaySwaps s2 (replaySwaps s1 st) := by
  induction s1 generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [List.cons_append, replaySwaps]
    exact ih _

theorem replaySwaps_comp {α β : Type*} (sws : List (Nat × Nat × Bool)) (f : α → β) (st : Nat → α) :
    replaySwaps sws (fun idx => f (st idx)) = fun idx => f (replaySwaps sws st idx) := by
  induction sws generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [replaySwaps]
    rw [applySwap_comp]
    exact ih _

theorem replaySwaps_reverse_cancel {β : Type*} (sws : List (Nat × Nat × Bool)) (st : Nat → β) :
    replaySwaps sws.reverse (replaySwaps sws st) = st := by
  induction sws generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [List.reverse_cons, replaySwaps, replaySwaps_append]
    rw [ih, applySwap_invol]

theorem runNet_eq_replay {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    runNet key net st = replaySwaps (netSwaps key net st) st := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [runNet, netSwaps, replaySwaps]
    exact ih _

theorem runNet_unchanged {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool))
    (st : Nat → α) (idx : Nat) (h : ∀ c ∈ net, idx ≠ c.1 ∧ idx ≠ c.2.1) :
    runNet key net st idx = st idx := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    have hc := h (u, v, asc) List.mem_cons_self
    simp only [runNet]
    rw [ih _ (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    simp only [applySwap]
    cases swapBit (key (st u)) (key (st v)) asc
    · rfl
    · simp only [↓reduceIte, hc.1, hc.2]

theorem runNet_mono_map {α : Type*} (key : α → Nat) (f : Nat → Bool)
    (hf : ∀ x y, x ≤ y → f x = true → f y = true)
    (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    (fun idx => f (key (runNet key net st idx))) =
      runNet (fun b : Bool => b.toNat) net (fun idx => f (key (st idx))) := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [runNet]
    rw [ih]
    congr 1
    funext idx
    simp only [applySwap, swapBit]
    have hpair :
        (f (key (if (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v)))
          then st v else st u)) =
         if (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
             else decide ((f (key (st u))).toNat < (f (key (st v))).toNat))
          then f (key (st v)) else f (key (st u))) ∧
        (f (key (if (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v)))
          then st u else st v)) =
         if (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
             else decide ((f (key (st u))).toNat < (f (key (st v))).toNat))
          then f (key (st u)) else f (key (st v))) := by
      cases asc <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · by_cases hlt : key (st u) < key (st v)
        · have hle : key (st u) ≤ key (st v) := Nat.le_of_lt hlt
          simp only [hlt, decide_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · simp
          · exact absurd (hf _ _ hle hfu) (by rw [hfv]; decide)
          · simp
        · have hle : key (st v) ≤ key (st u) := Nat.le_of_not_lt hlt
          simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · exact absurd (hf _ _ hle hfv) (by rw [hfu]; decide)
          · simp
          · simp
      · by_cases hlt : key (st v) < key (st u)
        · have hle : key (st v) ≤ key (st u) := Nat.le_of_lt hlt
          simp only [hlt, decide_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · exact absurd (hf _ _ hle hfv) (by rw [hfu]; decide)
          · simp
          · simp
        · have hle : key (st u) ≤ key (st v) := Nat.le_of_not_lt hlt
          simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · simp
          · exact absurd (hf _ _ hle hfu) (by rw [hfv]; decide)
          · simp
    by_cases h1 : idx = u
    · subst h1
      have hl := hpair.1
      by_cases hs1 : (if asc then decide (key (st v) < key (st idx)) else decide (key (st idx) < key (st v))) = true <;>
        by_cases hs2 : (if asc then decide ((f (key (st v))).toNat < (f (key (st idx))).toNat)
          else decide ((f (key (st idx))).toNat < (f (key (st v))).toNat)) = true <;>
        simp only [hs1, hs2, ↓reduceIte] at hl ⊢ <;> exact hl
    · by_cases h2 : idx = v
      · subst h2
        have hr := hpair.2
        by_cases hs1 : (if asc then decide (key (st idx) < key (st u)) else decide (key (st u) < key (st idx))) = true <;>
          by_cases hs2 : (if asc then decide ((f (key (st idx))).toNat < (f (key (st u))).toNat)
            else decide ((f (key (st u))).toNat < (f (key (st idx))).toNat)) = true <;>
          simp only [hs1, hs2, h1, ↓reduceIte] at hr ⊢ <;> exact hr
      · by_cases hs1 : (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v))) = true <;>
          by_cases hs2 : (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
            else decide ((f (key (st u))).toNat < (f (key (st v))).toNat)) = true <;>
          simp only [hs1, hs2, h1, h2, Bool.false_eq_true, ↓reduceIte]

def IsBitonic (off len : Nat) (g : Nat → Bool) : Prop :=
  ∃ s e, s ≤ e ∧ e ≤ len ∧
    ((∀ i < len, g (off + i) = true ↔ s ≤ i ∧ i < e) ∨
     (∀ i < len, g (off + i) = false ↔ s ≤ i ∧ i < e))

def IsSortedBool (off len : Nat) (asc : Bool) (g : Nat → Bool) : Prop :=
  ∀ i j, i ≤ j → j < len →
    if asc then (g (off + i) = true → g (off + j) = true)
    else (g (off + j) = true → g (off + i) = true)

theorem runNet_bool_const (net : List (Nat × Nat × Bool)) (off len : Nat) (v : Bool)
    (g : Nat → Bool)
    (hnet : ∀ c ∈ net, off ≤ c.1 ∧ c.1 < off + len ∧ off ≤ c.2.1 ∧ c.2.1 < off + len)
    (hg : ∀ i < len, g (off + i) = v) :
    ∀ i < len, runNet (fun b : Bool => b.toNat) net g (off + i) = v := by
  induction net generalizing g with
  | nil => exact hg
  | cons c rest ih =>
    rcases c with ⟨x, y, asc⟩
    have hc := hnet (x, y, asc) List.mem_cons_self
    dsimp only at hc
    simp only [runNet]
    apply ih _ (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc'))
    intro i hi
    simp only [applySwap]
    have hx : g x = v := by
      have e : off + (x - off) = x := by omega
      rw [← e]; exact hg (x - off) (by omega)
    have hy : g y = v := by
      have e : off + (y - off) = y := by omega
      rw [← e]; exact hg (y - off) (by omega)
    cases swapBit (g x).toNat (g y).toNat asc
    · exact hg i hi
    · simp only [↓reduceIte]
      by_cases h1 : off + i = x
      · simp [h1, hy]
      · by_cases h2 : off + i = y
        · simp only [h1, ↓reduceIte]; simp only [h2, ↓reduceIte]; exact hx
        · simp [h1, h2, hg i hi]

theorem stage_eval (off h : Nat) (asc : Bool) (g : Nat → Bool) :
    ∀ m ≤ h, ∀ idx,
      let stage := (List.range m).map (fun i => (off + i, off + h + i, asc))
      runNet (fun b : Bool => b.toNat) stage g idx =
        if off ≤ idx ∧ idx < off + m then
          if asc then g idx && g (idx + h) else g idx || g (idx + h)
        else if off + h ≤ idx ∧ idx < off + h + m then
          if asc then g (idx - h) || g idx else g (idx - h) && g idx
        else g idx := by
  intro m
  induction m with
  | zero =>
    intro _ idx
    dsimp only
    simp only [List.range_zero, List.map_nil, runNet, Nat.add_zero]
    simp only [show ¬ (off ≤ idx ∧ idx < off) by omega,
      show ¬ (off + h ≤ idx ∧ idx < off + h) by omega, ↓reduceIte]
  | succ m ih =>
    intro hm idx
    dsimp only
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, runNet_append]
    simp only [runNet, applySwap, swapBit]
    have h1 := ih (by omega) (off + m)
    have h2 := ih (by omega) (off + h + m)
    have h3 := ih (by omega) idx
    have h1' : runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g (off + m) = g (off + m) := by
      rw [h1]; simp only [show ¬ (off ≤ off + m ∧ off + m < off + m) by omega,
        show ¬ (off + h ≤ off + m ∧ off + m < off + h + m) by omega, ↓reduceIte]
    have h2' : runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g (off + h + m) = g (off + h + m) := by
      rw [h2]; simp only [show ¬ (off ≤ off + h + m ∧ off + h + m < off + m) by omega,
        show ¬ (off + h ≤ off + h + m ∧ off + h + m < off + h + m) by omega, ↓reduceIte]
    rw [h1', h2']
    by_cases hidx1 : idx = off + m
    · subst hidx1
      rw [h1']
      have e1 : off + m + h = off + h + m := by omega
      have hc1 : off ≤ off + m ∧ off + m < off + (m + 1) := by omega
      simp only [hc1, ↓reduceIte, e1]
      cases asc <;> cases g (off + m) <;> cases g (off + h + m) <;> rfl
    · by_cases hidx2 : idx = off + h + m
      · subst hidx2
        rw [h2']
        have e1 : off + h + m - h = off + m := by omega
        have hc1 : ¬ (off ≤ off + h + m ∧ off + h + m < off + (m + 1)) := by omega
        have hc2 : off + h ≤ off + h + m ∧ off + h + m < off + h + (m + 1) := by omega
        have hne : off + h + m ≠ off + m := by omega
        simp only [hc1, hc2, hne, ↓reduceIte, e1]
        cases asc <;> cases g (off + m) <;> cases g (off + h + m) <;> rfl
      · have hne1 : ¬ (idx = off + m) := hidx1
        have hne2 : ¬ (idx = off + h + m) := hidx2
        have heq : (if (if asc then decide ((g (off + h + m)).toNat < (g (off + m)).toNat)
            else decide ((g (off + m)).toNat < (g (off + h + m)).toNat)) then
            if idx = off + m then g (off + h + m) else if idx = off + h + m then g (off + m)
            else runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx
          else runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx) =
          runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx := by
          cases (if asc then decide ((g (off + h + m)).toNat < (g (off + m)).toNat)
            else decide ((g (off + m)).toNat < (g (off + h + m)).toNat)) <;> simp [hne1, hne2]
        rw [heq, h3]
        by_cases c1 : off ≤ idx ∧ idx < off + m
        · have c1' : off ≤ idx ∧ idx < off + (m + 1) := by omega
          simp only [c1, c1', and_self, ↓reduceIte]
        · by_cases c2 : off + h ≤ idx ∧ idx < off + h + m
          · have c1' : ¬ (off ≤ idx ∧ idx < off + (m + 1)) := by omega
            have c2' : off + h ≤ idx ∧ idx < off + h + (m + 1) := by omega
            simp only [c1, c2, c1', c2', and_self, ↓reduceIte]
          · have c1' : ¬ (off ≤ idx ∧ idx < off + (m + 1)) := by omega
            have c2' : ¬ (off + h ≤ idx ∧ idx < off + h + (m + 1)) := by omega
            simp only [c1, c2, c1', c2', and_self, ↓reduceIte]

theorem bitonic_split_true (off h : Nat) (g : Nat → Bool) (hb : IsBitonic off (2 * h) g) :
    let lo : Nat → Bool := fun idx => g idx && g (idx + h)
    let hi : Nat → Bool := fun idx => g (idx - h) || g idx
    IsBitonic off h lo ∧ IsBitonic (off + h) h hi ∧
      ((∀ i < h, lo (off + i) = false) ∨ (∀ i < h, hi (off + h + i) = true)) := by
  intro lo hi
  rcases hb with ⟨s, e, hse, he2h, htr | hfa⟩
  · by_cases hlen : e - s ≤ h
    · have hlo_all : ∀ i < h, lo (off + i) = false := by
        intro i hi_lt
        dsimp only [lo]
        cases h1 : g (off + i) with
        | false => rfl
        | true =>
          have hi1 := (htr i (by omega)).mp h1
          cases h2 : g (off + i + h) with
          | false => rfl
          | true =>
            have e1 : off + i + h = off + (h + i) := by omega
            rw [e1] at h2
            have hi2 := (htr (h + i) (by omega)).mp h2
            omega
      refine ⟨⟨0, 0, Nat.le_refl 0, Nat.zero_le h, Or.inl (fun i hi_lt => by rw [hlo_all i hi_lt]; simp)⟩,
        ?_, Or.inl hlo_all⟩
      have hhi_iff : ∀ i < h, hi (off + h + i) = true ↔ (s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e) := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2, Bool.or_eq_true, htr i (by omega), htr (h + i) (by omega)]
      by_cases heh : e ≤ h
      · exact ⟨s, e, hse, heh, Or.inl (fun i hi_lt => by rw [hhi_iff i hi_lt]; omega)⟩
      · by_cases hhs : h ≤ s
        · exact ⟨s - h, e - h, by omega, by omega, Or.inl (fun i hi_lt => by rw [hhi_iff i hi_lt]; omega)⟩
        · refine ⟨e - h, s, by omega, by omega, Or.inr (fun i hi_lt => ?_)⟩
          have h1 := hhi_iff i hi_lt
          cases hval : hi (off + h + i) with
          | false =>
            have hnt : ¬ ((s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e)) := fun hp => by
              have := h1.mpr hp; rw [hval] at this; cases this
            constructor
            · intro _; omega
            · intro _; rfl
          | true =>
            have ht := h1.mp hval
            constructor
            · intro hc; cases hc
            · intro hr; omega
    · have hhi_all : ∀ i < h, hi (off + h + i) = true := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2, Bool.or_eq_true, htr i (by omega), htr (h + i) (by omega)]
        omega
      refine ⟨⟨s, e - h, by omega, by omega, Or.inl (fun i hi_lt => ?_)⟩,
        ⟨0, h, Nat.zero_le h, Nat.le_refl h, Or.inl (fun i hi_lt => by rw [hhi_all i hi_lt]; simp [hi_lt])⟩,
        Or.inr hhi_all⟩
      dsimp only [lo]
      have e1 : off + i + h = off + (h + i) := by omega
      rw [e1, Bool.and_eq_true, htr i (by omega), htr (h + i) (by omega)]
      omega
  · by_cases hlen : e - s ≤ h
    · have hhi_all : ∀ i < h, hi (off + h + i) = true := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2]
        cases h1 : g (off + i) with
        | true => rfl
        | false =>
          have hi1 := (hfa i (by omega)).mp h1
          cases h2 : g (off + (h + i)) with
          | true => rfl
          | false =>
            have hi2 := (hfa (h + i) (by omega)).mp h2
            omega
      refine ⟨?_, ⟨0, h, Nat.zero_le h, Nat.le_refl h, Or.inl (fun i hi_lt => by rw [hhi_all i hi_lt]; simp [hi_lt])⟩,
        Or.inr hhi_all⟩
      have hlo_iff : ∀ i < h, lo (off + i) = false ↔ (s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e) := by
        intro i hi_lt
        dsimp only [lo]
        have e1 : off + i + h = off + (h + i) := by omega
        rw [e1, Bool.and_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
      by_cases heh : e ≤ h
      · exact ⟨s, e, hse, heh, Or.inr (fun i hi_lt => by rw [hlo_iff i hi_lt]; omega)⟩
      · by_cases hhs : h ≤ s
        · exact ⟨s - h, e - h, by omega, by omega, Or.inr (fun i hi_lt => by rw [hlo_iff i hi_lt]; omega)⟩
        · refine ⟨e - h, s, by omega, by omega, Or.inl (fun i hi_lt => ?_)⟩
          have h1 := hlo_iff i hi_lt
          cases hval : lo (off + i) with
          | true =>
            have hnf : ¬ ((s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e)) := fun hp => by
              have := h1.mpr hp; rw [hval] at this; cases this
            constructor
            · intro _; omega
            · intro _; rfl
          | false =>
            have hf := h1.mp hval
            constructor
            · intro hc; cases hc
            · intro hr; omega
    · have hlo_all : ∀ i < h, lo (off + i) = false := by
        intro i hi_lt
        dsimp only [lo]
        have e1 : off + i + h = off + (h + i) := by omega
        rw [e1, Bool.and_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
        omega
      refine ⟨⟨0, 0, Nat.le_refl 0, Nat.zero_le h, Or.inl (fun i hi_lt => by rw [hlo_all i hi_lt]; simp)⟩,
        ⟨s, e - h, by omega, by omega, Or.inr (fun i hi_lt => ?_)⟩,
        Or.inl hlo_all⟩
      dsimp only [hi]
      have e1 : off + h + i - h = off + i := by omega
      have e2 : off + h + i = off + (h + i) := by omega
      rw [e1, e2, Bool.or_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
      omega

theorem bitonicMerge_sorted (off : Nat) : ∀ k asc (g : Nat → Bool),
    IsBitonic off (2 ^ k) g →
    IsSortedBool off (2 ^ k) asc (runNet (fun b : Bool => b.toNat) (bitonicMerge off k asc) g)
  | 0, asc, g, _ => by
    intro i j hij hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    cases asc <;> exact fun h => h
  | k + 1, asc, g, hb => by
    let h := 2 ^ k
    have h2 : 2 ^ (k + 1) = 2 * h := by dsimp [h]; rw [Nat.pow_succ, Nat.mul_comm]
    rw [h2] at hb ⊢
    simp only [bitonicMerge, runNet_append]
    let stage := (List.range h).map (fun i => (off + i, off + h + i, asc))
    let g1 := runNet (fun b : Bool => b.toNat) stage g
    let g2 := runNet (fun b : Bool => b.toNat) (bitonicMerge off k asc) g1
    let g3 := runNet (fun b : Bool => b.toNat) (bitonicMerge (off + h) k asc) g2
    change IsSortedBool off (2 * h) asc g3
    have hstage := stage_eval off h asc g h (Nat.le_refl h)
    have hg1_L : ∀ i < h, g1 (off + i) = if asc then g (off + i) && g (off + i + h) else g (off + i) || g (off + i + h) := by
      intro i hi_lt
      have hs := hstage (off + i)
      dsimp only at hs
      have hc1 : off ≤ off + i ∧ off + i < off + h := by omega
      simp only [hc1, and_self, ↓reduceIte] at hs
      exact hs
    have hg1_R : ∀ i < h, g1 (off + h + i) = if asc then g (off + h + i - h) || g (off + h + i) else g (off + h + i - h) && g (off + h + i) := by
      intro i hi_lt
      have hs := hstage (off + h + i)
      dsimp only at hs
      have hc1 : ¬ (off ≤ off + h + i ∧ off + h + i < off + h) := by omega
      have hc2 : off + h ≤ off + h + i ∧ off + h + i < off + h + h := by omega
      simp only [hc1, hc2, and_self, ↓reduceIte] at hs
      exact hs
    have hsp := bitonic_split_true off h g hb
    have hleft_bit : IsBitonic off h g1 := by
      cases asc with
      | true =>
        rcases hsp.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          rw [hg1_L i hi_lt]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          rw [hg1_L i hi_lt]
          exact h3 i hi_lt
      | false =>
        rcases hsp.2.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          have h3' := h3 i hi_lt
          dsimp only at h3'
          rw [e1, e2] at h3'
          rw [hg1_L i hi_lt]
          exact h3'
        · right
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          have h3' := h3 i hi_lt
          dsimp only at h3'
          rw [e1, e2] at h3'
          rw [hg1_L i hi_lt]
          exact h3'
    have hright_bit : IsBitonic (off + h) h g2 := by
      have hg2_eq : ∀ i < h, g2 (off + h + i) = g1 (off + h + i) := by
        intro i hi_lt
        apply runNet_unchanged
        intro c hc
        have hm := bitonicMerge_mem off k asc c hc
        dsimp only [h] at hi_lt ⊢
        omega
      cases asc with
      | true =>
        rcases hsp.2.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          exact h3 i hi_lt
      | false =>
        rcases hsp.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [e1, e2]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [e1, e2]
          exact h3 i hi_lt
    have hsL : IsSortedBool off h asc g2 := bitonicMerge_sorted off k asc g1 hleft_bit
    have hsR : IsSortedBool (off + h) h asc g3 := bitonicMerge_sorted (off + h) k asc g2 hright_bit
    have hg3_left : ∀ i < h, g3 (off + i) = g2 (off + i) := by
      intro i hi_lt
      apply runNet_unchanged
      intro c hc
      have hm := bitonicMerge_mem (off + h) k asc c hc
      dsimp only [h] at hi_lt ⊢
      omega
    have hnetL : ∀ c ∈ bitonicMerge off k asc, off ≤ c.1 ∧ c.1 < off + h ∧ off ≤ c.2.1 ∧ c.2.1 < off + h := by
      intro c hc; have hm := bitonicMerge_mem off k asc c hc; dsimp [h]; omega
    have hnetR : ∀ c ∈ bitonicMerge (off + h) k asc,
        off + h ≤ c.1 ∧ c.1 < off + h + h ∧ off + h ≤ c.2.1 ∧ c.2.1 < off + h + h := by
      intro c hc; have hm := bitonicMerge_mem (off + h) k asc c hc; dsimp [h]; omega
    intro i j hij hj
    by_cases hjh : j < h
    · rw [hg3_left i (by omega), hg3_left j hjh]
      exact hsL i j hij hjh
    · by_cases hih : h ≤ i
      · have ei : off + i = off + h + (i - h) := by omega
        have ej : off + j = off + h + (j - h) := by omega
        rw [ei, ej]
        exact hsR (i - h) (j - h) (by omega) (by omega)
      · have hi_lt : i < h := by omega
        have hj_lt : j - h < h := by omega
        have ej : off + j = off + h + (j - h) := by omega
        rw [hg3_left i hi_lt, ej]
        cases asc with
        | true =>
          simp only [↓reduceIte]
          rcases hsp.2.2 with hlo | hhi
          · have hg1L : ∀ x < h, g1 (off + x) = false := by
              intro x hx
              rw [hg1_L x hx]
              exact hlo x hx
            have hg2i : g2 (off + i) = false :=
              runNet_bool_const (bitonicMerge off k true) off h false g1 hnetL hg1L i hi_lt
            intro ht; rw [hg2i] at ht; cases ht
          · have hg2R : ∀ x < h, g2 (off + h + x) = true := by
              intro x hx
              have heq : g2 (off + h + x) = g1 (off + h + x) := by
                apply runNet_unchanged; intro c hc; have hm := bitonicMerge_mem off k true c hc; dsimp [h] at hx ⊢; omega
              rw [heq, hg1_R x hx]
              exact hhi x hx
            intro _
            exact runNet_bool_const (bitonicMerge (off + h) k true) (off + h) h true g2 hnetR hg2R (j - h) hj_lt
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rcases hsp.2.2 with hlo | hhi
          · have hg2R : ∀ x < h, g2 (off + h + x) = false := by
              intro x hx
              have heq : g2 (off + h + x) = g1 (off + h + x) := by
                apply runNet_unchanged; intro c hc; have hm := bitonicMerge_mem off k false c hc; dsimp [h] at hx ⊢; omega
              rw [heq, hg1_R x hx]
              simp only [Bool.false_eq_true, ↓reduceIte]
              have e1 : off + h + x - h = off + x := by omega
              have e2 : off + h + x = off + x + h := by omega
              rw [e1, e2]
              exact hlo x hx
            have hg3j : g3 (off + h + (j - h)) = false :=
              runNet_bool_const (bitonicMerge (off + h) k false) (off + h) h false g2 hnetR hg2R (j - h) hj_lt
            intro ht; rw [hg3j] at ht; cases ht
          · have hg1L : ∀ x < h, g1 (off + x) = true := by
              intro x hx
              rw [hg1_L x hx]
              simp only [Bool.false_eq_true, ↓reduceIte]
              have e1 : off + h + x - h = off + x := by omega
              have e2 : off + h + x = off + x + h := by omega
              have hhi' := hhi x hx
              dsimp only at hhi'
              rw [e1, e2] at hhi'
              exact hhi'
            intro _
            exact runNet_bool_const (bitonicMerge off k false) off h true g1 hnetL hg1L i hi_lt

theorem sorted_asc_desc_bitonic (off h : Nat) (g : Nat → Bool)
    (hL : IsSortedBool off h true g) (hR : IsSortedBool (off + h) h false g) :
    IsBitonic off (2 * h) g := by
  have hexL : ∃ s ≤ h, ∀ i < h, g (off + i) = true ↔ s ≤ i := by
    have hgenL : ∀ n, IsSortedBool off n true g → ∃ s ≤ n, ∀ i < n, g (off + i) = true ↔ s ≤ i := by
      intro n
      induction n with
      | zero => intro _; exact ⟨0, Nat.le_refl 0, fun i hi => by omega⟩
      | succ m ih =>
        intro hLm
        rcases ih (fun i j hij hj => hLm i j hij (by omega)) with ⟨s, hsm, hs⟩
        cases hgm : g (off + m) with
        | false =>
          refine ⟨m + 1, Nat.le_refl _, fun i hi => ?_⟩
          constructor
          · intro ht
            by_cases him : i = m
            · subst him; rw [hgm] at ht; cases ht
            · have hgt := hLm i m (by omega) (by omega)
              simp only [↓reduceIte] at hgt
              have := hgt ht; rw [hgm] at this; cases this
          · intro hc; omega
        | true =>
          refine ⟨s, by omega, fun i hi => ?_⟩
          by_cases him : i = m
          · subst i; rw [hgm]; simp [show s ≤ m from hsm]
          · exact hs i (by omega)
    exact hgenL h hL
  have hexR : ∃ e ≤ h, ∀ i < h, g (off + h + i) = true ↔ i < e := by
    have hgen : ∀ n (g' : Nat → Bool), IsSortedBool 0 n false g' →
        ∃ e ≤ n, ∀ i < n, g' i = true ↔ i < e := by
      intro n g'
      induction n with
      | zero => intro _; exact ⟨0, Nat.le_refl 0, fun i hi => by omega⟩
      | succ m ih =>
        intro hg'
        rcases ih (fun i j hij hj => hg' i j hij (by omega)) with ⟨e, hem, he⟩
        cases hgm : g' m with
        | false =>
          refine ⟨e, by omega, fun i hi => ?_⟩
          by_cases him : i = m
          · subst i; rw [hgm]; simp [show ¬ m < e by omega]
          · exact he i (by omega)
        | true =>
          refine ⟨m + 1, Nat.le_refl _, fun i hi => ?_⟩
          constructor
          · intro _; omega
          · intro _
            have := hg' i m (by omega) (by omega)
            simp only [Nat.zero_add, Bool.false_eq_true, ↓reduceIte] at this
            exact this hgm
    have hR' : IsSortedBool 0 h false (fun i => g (off + h + i)) := by
      intro i j hij hj
      simpa only [Nat.zero_add] using hR i j hij hj
    exact hgen h (fun i => g (off + h + i)) hR'
  rcases hexL with ⟨s, hsh, hs⟩
  rcases hexR with ⟨e, heh, he⟩
  refine ⟨s, h + e, by omega, by omega, Or.inl (fun i hi => ?_)⟩
  by_cases hih : i < h
  · rw [hs i hih]
    omega
  · have e1 : off + i = off + h + (i - h) := by omega
    rw [e1, he (i - h) (by omega)]
    omega

theorem bitonicSort_sorted_bool (off : Nat) : ∀ k asc (g : Nat → Bool),
    IsSortedBool off (2 ^ k) asc (runNet (fun b : Bool => b.toNat) (bitonicSort off k asc) g)
  | 0, asc, g => by
    intro i j hij hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    cases asc <;> exact fun h => h
  | k + 1, asc, g => by
    let h := 2 ^ k
    simp only [bitonicSort, runNet_append]
    let g1 := runNet (fun b : Bool => b.toNat) (bitonicSort off k true) g
    let g2 := runNet (fun b : Bool => b.toNat) (bitonicSort (off + h) k false) g1
    have hsL : IsSortedBool off h true g1 := bitonicSort_sorted_bool off k true g
    have hsR : IsSortedBool (off + h) h false g2 := bitonicSort_sorted_bool (off + h) k false g1
    have hg2L : IsSortedBool off h true g2 := by
      intro i j hij hj
      have e1 : g2 (off + i) = g1 (off + i) := by
        apply runNet_unchanged; intro c hc; have hm := bitonicSort_mem (off + h) k false c hc; dsimp [h] at hij hj ⊢; omega
      have e2 : g2 (off + j) = g1 (off + j) := by
        apply runNet_unchanged; intro c hc; have hm := bitonicSort_mem (off + h) k false c hc; dsimp [h] at hj ⊢; omega
      rw [e1, e2]
      exact hsL i j hij hj
    have hbit : IsBitonic off (2 ^ (k + 1)) g2 := by
      rw [Nat.pow_succ, Nat.mul_comm]
      exact sorted_asc_desc_bitonic off h g2 hg2L hsR
    exact bitonicMerge_sorted off (k + 1) asc g2 hbit

theorem bitonicSort_sorted {α : Type*} (key : α → Nat) (p : Nat) (st : Nat → α) :
    ∀ i j, i ≤ j → j < 2 ^ p →
      key (runNet key (bitonicSort 0 p true) st i) ≤ key (runNet key (bitonicSort 0 p true) st j) := by
  intro i j hij hj
  let T := key (runNet key (bitonicSort 0 p true) st i)
  let f : Nat → Bool := fun x => decide (T ≤ x)
  have hf : ∀ x y, x ≤ y → f x = true → f y = true := by
    intro x y hxy hx
    simp only [f, decide_eq_true_eq] at hx ⊢
    omega
  have hs := bitonicSort_sorted_bool 0 p true (fun idx => f (key (st idx))) i j hij hj
  simp only [Nat.zero_add, ↓reduceIte] at hs
  rw [← runNet_mono_map key f hf] at hs
  have hiT : f (key (runNet key (bitonicSort 0 p true) st i)) = true := by
    simp [f, T]
  have hjT := hs hiT
  simp only [f, decide_eq_true_eq] at hjT
  exact hjT

end Bitonic

namespace Net1274

open Bitonic

def runB (net : List (Nat × Nat × Bool)) (g : Nat → Bool) : Nat → Bool :=
  runNet (fun b : Bool => b.toNat) net g

def cmpB (c : Nat × Nat × Bool) (g : Nat → Bool) : Nat → Bool := fun l =>
  if l = c.1 then (if c.2.2 then (g c.1 && g c.2.1) else (g c.1 || g c.2.1))
  else if l = c.2.1 then (if c.2.2 then (g c.1 || g c.2.1) else (g c.1 && g c.2.1))
  else g l

theorem runB_nil (g : Nat → Bool) : runB [] g = g := rfl

theorem runB_cons (c : Nat × Nat × Bool) (rest : List (Nat × Nat × Bool)) (g : Nat → Bool)
    (h : c.1 ≠ c.2.1) : runB (c :: rest) g = runB rest (cmpB c g) := by
  obtain ⟨u, v, asc⟩ := c
  simp only at h
  simp only [runB, runNet]
  congr 1
  funext l
  simp only [applySwap, swapBit, cmpB]
  by_cases h1 : l = u
  · subst h1
    cases hu : g l <;> cases hv : g v <;> cases asc <;> simp [hu, hv]
  · by_cases h2 : l = v
    · subst h2
      cases hu : g u <;> cases hv : g l <;> cases asc <;> simp [hu, hv, h1]
    · cases hu : g u <;> cases hv : g v <;> cases asc <;> simp [hu, hv, h1, h2]

def Distinct (net : List (Nat × Nat × Bool)) : Prop := ∀ c ∈ net, c.1 ≠ c.2.1

theorem cmpB_mono (c : Nat × Nat × Bool) (g g' : Nat → Bool)
    (h : ∀ l, g l = true → g' l = true) : ∀ l, cmpB c g l = true → cmpB c g' l = true := by
  intro l hl
  obtain ⟨u, v, asc⟩ := c
  have hu := h u
  have hv := h v
  have hl' := h l
  simp only [cmpB] at hl ⊢
  split_ifs at hl ⊢ <;> simp_all <;> tauto

theorem runB_mono (net : List (Nat × Nat × Bool)) (hd : Distinct net) :
    ∀ g g' : Nat → Bool, (∀ l, g l = true → g' l = true) →
      ∀ l, runB net g l = true → runB net g' l = true := by
  induction net with
  | nil => intro g g' h; exact h
  | cons c rest ih =>
    intro g g' h
    have hc : c.1 ≠ c.2.1 := hd c List.mem_cons_self
    have hr : Distinct rest := fun c' hc' => hd c' (List.mem_cons_of_mem _ hc')
    rw [runB_cons c rest g hc, runB_cons c rest g' hc]
    exact ih hr _ _ (cmpB_mono c g g' h)

def cnt (L : Nat) (g : Nat → Bool) : Nat := ∑ i ∈ Finset.range L, (g i).toNat

theorem cnt_cmpB (c : Nat × Nat × Bool) (g : Nat → Bool) (L : Nat) (hu : c.1 < L) (hv : c.2.1 < L)
    (huv : c.1 ≠ c.2.1) : cnt L (cmpB c g) = cnt L g := by
  obtain ⟨u, v, asc⟩ := c
  simp only at hu hv huv
  unfold cnt
  have hu' : u ∈ Finset.range L := Finset.mem_range.2 hu
  have hv' : v ∈ (Finset.range L).erase u := by simp [Ne.symm huv, hv]
  rw [← Finset.add_sum_erase _ _ hu', ← Finset.add_sum_erase _ _ hv']
  rw [← Finset.add_sum_erase _ _ hu', ← Finset.add_sum_erase _ _ hv']
  have hrest : ∑ i ∈ ((Finset.range L).erase u).erase v, (cmpB (u, v, asc) g i).toNat =
      ∑ i ∈ ((Finset.range L).erase u).erase v, (g i).toNat := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_erase] at hi
    simp [cmpB, hi.1, hi.2.1]
  rw [hrest]
  simp only [cmpB, if_pos rfl, if_neg (Ne.symm huv)]
  cases g u <;> cases g v <;> cases asc <;> simp <;> omega

theorem cnt_runB (L : Nat) : ∀ (net : List (Nat × Nat × Bool)) (g : Nat → Bool),
    (∀ c ∈ net, c.1 < L ∧ c.2.1 < L ∧ c.1 ≠ c.2.1) → cnt L (runB net g) = cnt L g := by
  intro net
  induction net with
  | nil => intro g _; rfl
  | cons c rest ih =>
    intro g h
    have hc := h c List.mem_cons_self
    rw [runB_cons c rest g hc.2.2, ih _ (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    exact cnt_cmpB c g L hc.1 hc.2.1 hc.2.2

theorem sum_ones (h : Nat → Bool) : ∀ m, (∀ i < m, h i = true) → ∑ i ∈ Finset.range m, (h i).toNat = m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [Finset.sum_range_succ, ih (fun i hi => hm i (by omega)), hm m (by omega)]
    rfl

theorem sorted_desc_thr (L : Nat) (h : Nat → Bool) (hs : IsSortedBool 0 L false h) :
    ∀ i < L, h i = decide (i < cnt L h) := by
  intro i hi
  have hs' : ∀ a b, a ≤ b → b < L → h b = true → h a = true := by
    intro a b hab hb hh
    have := hs a b hab hb
    simp only [Nat.zero_add, Bool.false_eq_true, ↓reduceIte] at this
    exact this hh
  cases hhi : h i
  ·
    have hz : ∀ j, i ≤ j → j < L → h j = false := by
      intro j hij hj
      cases hj' : h j
      · rfl
      · have := hs' i j hij hj hj'; rw [hhi] at this; exact absurd this (by decide)
    have hsplit : cnt L h = ∑ k ∈ Finset.range i, (h k).toNat + ∑ k ∈ Finset.range (L - i), (h (i + k)).toNat := by
      unfold cnt
      have e : L = i + (L - i) := by omega
      conv_lhs => rw [e]
      rw [Finset.sum_range_add]
    have h2 : ∑ k ∈ Finset.range (L - i), (h (i + k)).toNat = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [hz (i + k) (by omega) (by omega)]
      rfl
    have h1 : ∑ k ∈ Finset.range i, (h k).toNat ≤ i := by
      calc ∑ k ∈ Finset.range i, (h k).toNat ≤ ∑ k ∈ Finset.range i, 1 :=
            Finset.sum_le_sum (fun k _ => Bool.toNat_le (h k))
        _ = i := by simp
    symm
    simp only [decide_eq_false_iff_not, not_lt]
    omega
  · have ho : ∀ j ≤ i, h j = true := fun j hj => hs' j i hj hi hhi
    have hsplit : cnt L h = ∑ k ∈ Finset.range (i + 1), (h k).toNat + ∑ k ∈ Finset.range (L - (i + 1)), (h (i + 1 + k)).toNat := by
      unfold cnt
      have e : L = (i + 1) + (L - (i + 1)) := by omega
      conv_lhs => rw [e]
      rw [Finset.sum_range_add]
    have h1 := sum_ones h (i + 1) (fun j hj => ho j (by omega))
    symm
    simp only [decide_eq_true_eq]
    omega

def sortNet (p : Nat) : List (Nat × Nat × Bool) := bitonicSort 0 p false

theorem sortNet_mem (p : Nat) : ∀ c ∈ sortNet p, c.1 < 2 ^ p ∧ c.2.1 < 2 ^ p ∧ c.1 ≠ c.2.1 := by
  intro c hc
  have := bitonicSort_mem 0 p false c hc
  omega

theorem sortNet_distinct (p : Nat) : Distinct (sortNet p) := fun c hc => (sortNet_mem p c hc).2.2

theorem sortNet_thr (p : Nat) (g : Nat → Bool) (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 2 ^ p) :
    runB (sortNet p) g (k - 1) = decide (k ≤ cnt (2 ^ p) g) := by
  have hs := bitonicSort_sorted_bool 0 p false g
  have h := sorted_desc_thr (2 ^ p) _ hs (k - 1) (by omega)
  have hc := cnt_runB (2 ^ p) (sortNet p) g (sortNet_mem p)
  unfold runB sortNet at hc
  unfold runB sortNet
  rw [h, hc]
  simp only [decide_eq_decide]
  omega

theorem sortNet_length (p : Nat) : 4 * (sortNet p).length = p * (p + 1) * 2 ^ p :=
  bitonicSort_length 0 p false

def cof (k : Nat) (net : List (Nat × Nat × Bool)) (g : Nat → Bool) (l : Nat) : Bool :=
  runB net (Function.update g l true) k

theorem cof_nil (k : Nat) (g : Nat → Bool) (l : Nat) :
    cof k [] g l = if l = k then true else g k := by
  simp only [cof, runB_nil, Function.update_apply]
  by_cases h : k = l
  · subst h; simp
  · simp [h, Ne.symm h]

theorem cof_ge (k : Nat) (net : List (Nat × Nat × Bool)) (hd : Distinct net) (g : Nat → Bool) (l : Nat) :
    runB net g k = true → cof k net g l = true := by
  apply runB_mono net hd
  intro m hm
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem cof_self (k : Nat) (net : List (Nat × Nat × Bool)) (g : Nat → Bool) (l : Nat) (h : g l = true) :
    cof k net g l = runB net g k := by
  simp only [cof]
  rw [← h, Function.update_eq_self]

theorem cof_cons_other (k : Nat) (c : Nat × Nat × Bool) (rest : List (Nat × Nat × Bool)) (g : Nat → Bool)
    (l : Nat) (hc : c.1 ≠ c.2.1) (h1 : l ≠ c.1) (h2 : l ≠ c.2.1) :
    cof k (c :: rest) g l = cof k rest (cmpB c g) l := by
  simp only [cof]
  rw [runB_cons c rest _ hc]
  congr 1
  funext m
  obtain ⟨u, v, asc⟩ := c
  simp only at h1 h2
  simp only [cmpB, Function.update_apply]
  by_cases hm : m = l
  · subst hm; simp [h1, h2]
  · by_cases hu : m = u
    · subst hu; simp [hm, Ne.symm h1, Ne.symm h2]
    · by_cases hv : m = v
      · subst hv; simp [hm, hu, Ne.symm h1, Ne.symm h2]
      · simp [hm, hu, hv]

def orL (c : Nat × Nat × Bool) : Nat := if c.2.2 then c.2.1 else c.1
def andL (c : Nat × Nat × Bool) : Nat := if c.2.2 then c.1 else c.2.1

theorem cof_cons_fst (k : Nat) (c : Nat × Nat × Bool) (rest : List (Nat × Nat × Bool)) (g : Nat → Bool)
    (hc : c.1 ≠ c.2.1) (hd : Distinct rest) :
    cof k (c :: rest) g c.1 =
      (cof k rest (cmpB c g) (orL c) || (g c.2.1 && cof k rest (cmpB c g) (andL c))) := by
  obtain ⟨u, v, asc⟩ := c
  simp only at hc
  have hc' : v ≠ u := Ne.symm hc
  simp only [orL, andL]
  have hT : cof k ((u, v, asc) :: rest) g u = runB rest (cmpB (u, v, asc) (Function.update g u true)) k := by
    simp only [cof]; rw [runB_cons _ rest _ hc]
  rw [hT]
  have hge := fun l => cof_ge k rest hd (cmpB (u, v, asc) g) l
  cases asc
  ·
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hgu : g u <;> cases hgv : g v
    · have e : cmpB (u, v, false) (Function.update g u true) = Function.update (cmpB (u, v, false) g) u true := by
        funext m; simp only [cmpB, Function.update_apply]
        by_cases hm : m = u
        · subst hm; simp
        · by_cases hm2 : m = v
          · subst hm2; simp [hc', hm, hc, hgu, hgv]
          · simp [hc', hm, hm2]
      rw [e]; simp [hc', cof]
    · have e : cmpB (u, v, false) (Function.update g u true) = Function.update (cmpB (u, v, false) g) v true := by
        funext m; simp only [cmpB, Function.update_apply]
        by_cases hm : m = u
        · subst hm; simp [hc', hc, hgv]
        · by_cases hm2 : m = v
          · subst hm2; simp [hc', hm, hc, hgu, hgv]
          · simp [hc', hm, hm2]
      rw [e]
      have hs : cof k rest (cmpB (u, v, false) g) u = runB rest (cmpB (u, v, false) g) k :=
        cof_self _ _ _ _ (by simp [hc', cmpB, hgv])
      rw [hs]
      have := hge v
      simp only [Bool.true_and]
      cases h' : runB rest (cmpB (u, v, false) g) k
      · simp [hc', cof]
      · rw [this h']; simp [hc', cof] at this ⊢; exact this h'
    · have e : cmpB (u, v, false) (Function.update g u true) = cmpB (u, v, false) g := by
        funext m; simp only [cmpB, Function.update_apply]
        by_cases hm : m = u
        · subst hm; simp [hc', hgu]
        · by_cases hm2 : m = v
          · subst hm2; simp [hc', hm, hc, hgu, hgv]
          · simp [hc', hm, hm2]
      rw [e]
      have hs : cof k rest (cmpB (u, v, false) g) u = runB rest (cmpB (u, v, false) g) k :=
        cof_self _ _ _ _ (by simp [hc', cmpB, hgu])
      rw [hs]; simp
    · have e : cmpB (u, v, false) (Function.update g u true) = cmpB (u, v, false) g := by
        funext m; simp only [cmpB, Function.update_apply]
        by_cases hm : m = u
        · subst hm; simp [hc', hgu]
        · by_cases hm2 : m = v
          · subst hm2; simp [hc', hm, hc, hgu, hgv]
          · simp [hc', hm, hm2]
      rw [e]
      have hs : cof k rest (cmpB (u, v, false) g) u = runB rest (cmpB (u, v, false) g) k :=
        cof_self _ _ _ _ (by simp [hc', cmpB, hgu])
      have hs2 : cof k rest (cmpB (u, v, false) g) v = runB rest (cmpB (u, v, false) g) k :=
        cof_self _ _ _ _ (by simp [hc', cmpB, hc, hgu, hgv])
      rw [hs, hs2]; simp
  ·
    simp only [↓reduceIte]
    cases hgu : g u <;> cases hgv : g v
    · have e : cmpB (u, v, true) (Function.update g u true) = Function.update (cmpB (u, v, true) g) v true := by
        funext m; simp only [cmpB, Function.update_apply]
        by_cases hm : m = u
        · subst hm; simp [hc', hc, hgv]
        · by_cases hm2 : m = v
          · subst hm2; simp [hc', hm, hc, hgu, hgv]
          · simp [hc', hm, hm2]
      rw [e]; simp [hc', cof]
    · have e : cmpB (u, v, true) (Function.update g u true) = Function.update (cmpB (u, v, true) g) u true := by
        funext m; simp only [cmpB, Function.update_apply]
        by_cases hm : m = u
        · subst hm; simp [hc', hc, hgv]
        · by_cases hm2 : m = v
          · subst hm2; simp [hc', hm, hc, hgu, hgv]
          · simp [hc', hm, hm2]
      rw [e]
      have hs : cof k rest (cmpB (u, v, true) g) v = runB rest (cmpB (u, v, true) g) k :=
        cof_self _ _ _ _ (by simp [hc', cmpB, hc, hgv])
      rw [hs]
      have := hge u
      simp only [Bool.true_and]
      cases h' : runB rest (cmpB (u, v, true) g) k
      · simp [hc', cof]
      · have h2 := this h'; simp only [cof] at h2 ⊢; simp [hc', h2]
    · have e : cmpB (u, v, true) (Function.update g u true) = cmpB (u, v, true) g := by
        funext m; simp only [cmpB, Function.update_apply]
        by_cases hm : m = u
        · subst hm; simp [hc', hgu]
        · by_cases hm2 : m = v
          · subst hm2; simp [hc', hm, hc, hgu, hgv]
          · simp [hc', hm, hm2]
      rw [e]
      have hs : cof k rest (cmpB (u, v, true) g) v = runB rest (cmpB (u, v, true) g) k :=
        cof_self _ _ _ _ (by simp [hc', cmpB, hc, hgu])
      rw [hs]; simp
    · have e : cmpB (u, v, true) (Function.update g u true) = cmpB (u, v, true) g := by
        funext m; simp only [cmpB, Function.update_apply]
        by_cases hm : m = u
        · subst hm; simp [hc', hgu, hgv]
        · by_cases hm2 : m = v
          · subst hm2; simp [hc', hm, hc, hgu, hgv]
          · simp [hc', hm, hm2]
      rw [e]
      have hs : cof k rest (cmpB (u, v, true) g) v = runB rest (cmpB (u, v, true) g) k :=
        cof_self _ _ _ _ (by simp [hc', cmpB, hc, hgu])
      have hs2 : cof k rest (cmpB (u, v, true) g) u = runB rest (cmpB (u, v, true) g) k :=
        cof_self _ _ _ _ (by simp [hc', cmpB, hgu, hgv])
      rw [hs, hs2]; simp

end Net1274

namespace Net1274

theorem cmpB_swap (u v : Nat) (asc : Bool) (h : u ≠ v) : cmpB (v, u, !asc) = cmpB (u, v, asc) := by
  funext g l
  simp only [cmpB]
  by_cases h1 : l = u
  · subst h1; cases asc <;> simp [h, Bool.and_comm, Bool.or_comm]
  · by_cases h2 : l = v
    · subst h2; cases asc <;> simp [h1, Bool.and_comm, Bool.or_comm]
    · simp [h1, h2]

theorem cof_cons_snd (k : Nat) (c : Nat × Nat × Bool) (rest : List (Nat × Nat × Bool)) (g : Nat → Bool)
    (hc : c.1 ≠ c.2.1) (hd : Distinct rest) :
    cof k (c :: rest) g c.2.1 =
      (cof k rest (cmpB c g) (orL c) || (g c.1 && cof k rest (cmpB c g) (andL c))) := by
  obtain ⟨u, v, asc⟩ := c
  simp only at hc ⊢
  have e1 : cof k ((u, v, asc) :: rest) g v = cof k ((v, u, !asc) :: rest) g v := by
    simp only [cof]
    rw [runB_cons _ rest _ hc, runB_cons _ rest _ (Ne.symm hc), cmpB_swap u v asc hc]
  rw [e1, cof_cons_fst k (v, u, !asc) rest g (Ne.symm hc) hd]
  simp only [cmpB_swap u v asc hc, orL, andL]
  cases asc <;> simp

end Net1274

namespace NetBuild1274

open Build049 Net1274

variable {N : Nat}

theorem par {A B C : Set (Sig N)} {b c : Nat} (H : Build A B b) (J : Build A C c) :
    Build A (B ∪ C) (b + c) :=
  seq H (relax J Set.subset_union_left le_rfl le_rfl)

theorem orAndG {A : Set (Sig N)} {a b c : Sig N} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
    Build A {fun X => a X || (b X && c X)} 2 := by
  have h1 := andG hb hc
  have h2 := orG (A := A ∪ {an b c}) (f := a) (g := an b c) (Or.inl ha) (Or.inr rfl)
  exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

def cmpS (c : Nat × Nat × Bool) (st : Nat → Sig N) : Nat → Sig N :=
  fun l X => cmpB c (fun m => st m X) l

def runS (net : List (Nat × Nat × Bool)) (st : Nat → Sig N) : Nat → Sig N :=
  fun l X => runB net (fun m => st m X) l

def cofS (k : Nat) (net : List (Nat × Nat × Bool)) (st : Nat → Sig N) : Nat → Sig N :=
  fun l X => cof k net (fun m => st m X) l

def netOut (L k1 k2 : Nat) (net : List (Nat × Nat × Bool)) (st : Nat → Sig N) : Set (Sig N) :=
  {f | ∃ l < L, f = cofS k1 net st l ∨ f = cofS k2 net st l} ∪ {runS net st k1, runS net st k2}

theorem cmpG {A : Set (Sig N)} (c : Nat × Nat × Bool) (st : Nat → Sig N) (hu : st c.1 ∈ A)
    (hv : st c.2.1 ∈ A) : Build A {cmpS c st c.1, cmpS c st c.2.1} 2 := by
  obtain ⟨u, v, asc⟩ := c
  simp only at hu hv ⊢
  by_cases huv : u = v
  · subst huv
    have e : cmpS (u, u, asc) st u = if asc then an (st u) (st u) else or (st u) (st u) := by
      cases asc <;> (funext X; simp [cmpS, cmpB, Build049.an, Build049.or])
    rw [Set.pair_eq_singleton]
    cases asc
    · rw [e]; exact relax (orG hu hu) le_rfl le_rfl (by omega)
    · rw [e]; exact relax (andG hu hu) le_rfl le_rfl (by omega)
  · have e1 : cmpS (u, v, asc) st u = if asc then an (st u) (st v) else or (st u) (st v) := by
      cases asc <;> (funext X; simp [cmpS, cmpB, Build049.an, Build049.or])
    have e2 : cmpS (u, v, asc) st v = if asc then or (st u) (st v) else an (st u) (st v) := by
      cases asc <;> (funext X; simp [cmpS, cmpB, Build049.an, Build049.or, Ne.symm huv])
    rw [e1, e2, Set.insert_eq]
    cases asc
    · exact par (orG hu hv) (andG hu hv)
    · exact par (andG hu hv) (orG hu hv)

theorem netBuild (L k1 k2 : Nat) (tru : Sig N) (htv : ∀ X, tru X = true) (hk1 : k1 < L) (hk2 : k2 < L) :
    ∀ (net : List (Nat × Nat × Bool)) (A : Set (Sig N)) (st : Nat → Sig N),
      (∀ c ∈ net, c.1 < L ∧ c.2.1 < L ∧ c.1 ≠ c.2.1) → tru ∈ A → (∀ l < L, st l ∈ A) →
      Build A (netOut L k1 k2 net st) (10 * net.length) := by
  intro net
  induction net with
  | nil =>
    intro A st _ htru hst
    apply idle
    have hb : ∀ k < L, ∀ l, cofS k [] st l ∈ A := by
      intro k hk l
      by_cases hl : l = k
      · have e : cofS k [] st l = tru := by
          funext X; simp [cofS, cof_nil, hl, htv]
        rw [e]; exact htru
      · have e : cofS k [] st l = st k := by
          funext X; simp [cofS, cof_nil, hl]
        rw [e]; exact hst k hk
    rintro f (⟨l, hl, rfl | rfl⟩ | hf)
    · exact hb k1 hk1 l
    · exact hb k2 hk2 l
    · rcases hf with rfl | hf
      · exact hst k1 hk1
      · rw [Set.mem_singleton_iff.mp hf]; exact hst k2 hk2
  | cons c rest ih =>
    intro A st hnet htru hst
    have hc := hnet c List.mem_cons_self
    have hrest : ∀ c' ∈ rest, c'.1 < L ∧ c'.2.1 < L ∧ c'.1 ≠ c'.2.1 :=
      fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc')
    have hd : Distinct rest := fun c' hc' => (hrest c' hc').2.2
    set st' := cmpS c st with hst'
    have H1 := cmpG c st (hst _ hc.1) (hst _ hc.2.1)
    set A1 := A ∪ {cmpS c st c.1, cmpS c st c.2.1} with hA1
    have hst1 : ∀ l < L, st' l ∈ A1 := by
      intro l hl
      by_cases h1 : l = c.1
      · subst h1; exact Or.inr (Or.inl rfl)
      · by_cases h2 : l = c.2.1
        · subst h2; exact Or.inr (Or.inr rfl)
        · left
          have e : st' l = st l := by
            funext X; simp [hst', cmpS, cmpB, h1, h2]
          rw [e]; exact hst l hl
    have H2 := ih A1 st' hrest (Or.inl htru) hst1
    set A2 := A1 ∪ netOut L k1 k2 rest st' with hA2
    have hin : ∀ k, (k = k1 ∨ k = k2) → ∀ l < L, cofS k rest st' l ∈ A2 := by
      intro k hk l hl
      right; left
      rcases hk with rfl | rfl
      · exact ⟨l, hl, Or.inl rfl⟩
      · exact ⟨l, hl, Or.inr rfl⟩
    have hor : orL c < L := by unfold orL; split_ifs <;> omega
    have hand : andL c < L := by unfold andL; split_ifs <;> omega
    have hstA2 : ∀ l < L, st l ∈ A2 := fun l hl => Or.inl (Or.inl (hst l hl))
    have G : ∀ k, (k = k1 ∨ k = k2) →
        Build A2 {cofS k (c :: rest) st c.1, cofS k (c :: rest) st c.2.1} 4 := by
      intro k hk
      have e1 : cofS k (c :: rest) st c.1 =
          fun X => cofS k rest st' (orL c) X || (st c.2.1 X && cofS k rest st' (andL c) X) := by
        funext X; simp only [cofS]; rw [cof_cons_fst k c rest _ hc.2.2 hd]; rfl
      have e2 : cofS k (c :: rest) st c.2.1 =
          fun X => cofS k rest st' (orL c) X || (st c.1 X && cofS k rest st' (andL c) X) := by
        funext X; simp only [cofS]; rw [cof_cons_snd k c rest _ hc.2.2 hd]; rfl
      rw [e1, e2, Set.insert_eq]
      exact par (orAndG (hin k hk _ hor) (hstA2 _ hc.2.1) (hin k hk _ hand))
        (orAndG (hin k hk _ hor) (hstA2 _ hc.1) (hin k hk _ hand))
    have H3 := par (G k1 (Or.inl rfl)) (G k2 (Or.inr rfl))
    have Hall := seq H1 (seq H2 H3)
    refine relax Hall le_rfl ?_ (by simp only [List.length_cons]; omega)
    have hother : ∀ k l, l ≠ c.1 → l ≠ c.2.1 → cofS k (c :: rest) st l = cofS k rest st' l := by
      intro k l h1 h2
      funext X; simp only [cofS]; rw [cof_cons_other k c rest _ l hc.2.2 h1 h2]; rfl
    have hrun : ∀ k, runS (c :: rest) st k = runS rest st' k := by
      intro k; funext X; simp only [runS]; rw [runB_cons c rest _ hc.2.2]; rfl
    rintro f (⟨l, hl, hf⟩ | hf)
    · by_cases h1 : l = c.1
      · subst h1
        rcases hf with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl (Or.inl rfl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · by_cases h2 : l = c.2.1
        · subst h2
          rcases hf with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl (Or.inr rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
        · rcases hf with rfl | rfl
          · rw [hother k1 l h1 h2]; exact Or.inr (Or.inl (Or.inl ⟨l, hl, Or.inl rfl⟩))
          · rw [hother k2 l h1 h2]; exact Or.inr (Or.inl (Or.inl ⟨l, hl, Or.inr rfl⟩))
    · rcases hf with rfl | hf
      · rw [hrun]; exact Or.inr (Or.inl (Or.inr (Or.inl rfl)))
      · rw [Set.mem_singleton_iff.mp hf, hrun]; exact Or.inr (Or.inl (Or.inr (Or.inr rfl)))

end NetBuild1274

namespace Sem1274

def dx (a c : Bool × Bool) : Bool × Bool := ((a.1 && c.2) || (a.2 && c.1), (a.1 && c.1) || (a.2 && c.2))

def ex (v : Bool) : Bool × Bool := (v, !v)

theorem dx_ex (u v : Bool) : dx (ex u) (ex v) = ex (xor u v) := by cases u <;> cases v <;> rfl
theorem dx_zero_l (c : Bool × Bool) : dx (false, false) c = (false, false) := by simp [dx]
theorem dx_zero_r (a : Bool × Bool) : dx a (false, false) = (false, false) := by simp [dx]

def pairR (b : Nat → Bool) (t : Nat) : Bool × Bool := (b (2 * t + 1), b (2 * t))

def Pf (b : Nat → Bool) : Nat → Bool × Bool
  | 0 => (false, true)
  | t + 1 => dx (Pf b t) (pairR b t)

def Sg (b : Nat → Bool) : Nat → Nat → Bool × Bool
  | 0, _ => (false, true)
  | m + 1, s => dx (pairR b s) (Sg b m (s + 1))

def par (b : Nat → Bool) : Nat → Bool
  | 0 => false
  | t + 1 => xor (par b t) (b (2 * t + 1))

def spar (b : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | m + 1, s => xor (b (2 * s + 1)) (spar b m (s + 1))

def Exact (b : Nat → Bool) (t : Nat) : Prop := b (2 * t) = !b (2 * t + 1)
def Empty (b : Nat → Bool) (t : Nat) : Prop := b (2 * t) = false ∧ b (2 * t + 1) = false

theorem pairR_exact (b : Nat → Bool) (t : Nat) (h : Exact b t) : pairR b t = ex (b (2 * t + 1)) := by
  simp only [pairR, ex, Exact] at h ⊢; rw [h]

theorem pairR_empty (b : Nat → Bool) (t : Nat) (h : Empty b t) : pairR b t = (false, false) := by
  simp [pairR, h.1, h.2]

theorem Pf_exact (b : Nat → Bool) : ∀ t, (∀ s < t, Exact b s) → Pf b t = ex (par b t)
  | 0, _ => rfl
  | t + 1, h => by
    rw [Pf, Pf_exact b t (fun s hs => h s (by omega)), pairR_exact b t (h t (by omega)), dx_ex]; rfl

theorem Pf_empty (b : Nat → Bool) : ∀ t s, s < t → Empty b s → Pf b t = (false, false)
  | 0, s, hs, _ => absurd hs (Nat.not_lt_zero _)
  | t + 1, s, hs, he => by
    rw [Pf]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with h | h
    · rw [Pf_empty b t s h he, dx_zero_l]
    · subst h; rw [pairR_empty b _ he, dx_zero_r]

theorem Sg_exact (b : Nat → Bool) : ∀ m s, (∀ s', s ≤ s' → s' < s + m → Exact b s') →
    Sg b m s = ex (spar b m s)
  | 0, s, _ => rfl
  | m + 1, s, h => by
    rw [Sg, Sg_exact b m (s + 1) (fun s' h1 h2 => h s' (by omega) (by omega)),
      pairR_exact b s (h s le_rfl (by omega)), dx_ex]; rfl

theorem Sg_empty (b : Nat → Bool) : ∀ m s s', s ≤ s' → s' < s + m → Empty b s' → Sg b m s = (false, false)
  | 0, s, s', h1, h2, _ => by omega
  | m + 1, s, s', h1, h2, he => by
    rw [Sg]
    by_cases h : s' = s
    · subst h; rw [pairR_empty b _ he, dx_zero_l]
    · rw [Sg_empty b m (s + 1) s' (by omega) (by omega) he, dx_zero_r]

theorem Pf_congr (b b' : Nat → Bool) : ∀ t, (∀ s < t, pairR b s = pairR b' s) → Pf b t = Pf b' t
  | 0, _ => rfl
  | t + 1, h => by rw [Pf, Pf, Pf_congr b b' t (fun s hs => h s (by omega)), h t (by omega)]

theorem Sg_congr (b b' : Nat → Bool) : ∀ m s, (∀ s', s ≤ s' → s' < s + m → pairR b s' = pairR b' s') →
    Sg b m s = Sg b' m s
  | 0, _, _ => rfl
  | m + 1, s, h => by
    rw [Sg, Sg, Sg_congr b b' m (s + 1) (fun s' h1 h2 => h s' (by omega) (by omega)), h s le_rfl (by omega)]

theorem par_split (b : Nat → Bool) : ∀ m s, par b (s + m) = xor (par b s) (spar b m s)
  | 0, s => by simp [spar]
  | m + 1, s => by
    rw [show s + (m + 1) = (s + 1) + m by omega, par_split b m (s + 1), par, spar]
    simp [Bool.xor_assoc]

def Qr (b : Nat → Bool) (q t : Nat) : Bool × Bool := dx (Pf b t) (Sg b (q - t) (t + 1))

def zR (b : Nat → Bool) (q t : Nat) : Bool × Bool :=
  (b (2 * t + 1) || (Qr b q t).1, b (2 * t) || (Qr b q t).2)

def oth (b : Nat → Bool) (q t : Nat) : Bool := xor (par b t) (spar b (q - t) (t + 1))

theorem par_oth (b : Nat → Bool) (q t : Nat) (ht : t ≤ q) :
    par b (q + 1) = xor (oth b q t) (b (2 * t + 1)) := by
  have e := par_split b (q - t) (t + 1)
  rw [show t + 1 + (q - t) = q + 1 by omega] at e
  rw [e, par, oth]
  cases par b t <;> cases b (2 * t + 1) <;> cases spar b (q - t) (t + 1) <;> rfl

theorem Qr_exact (b : Nat → Bool) (q t : Nat) (h : ∀ s ≤ q, s ≠ t → Exact b s) (ht : t ≤ q) :
    Qr b q t = ex (oth b q t) := by
  rw [Qr, Pf_exact b t (fun s hs => h s (by omega) (by omega)),
    Sg_exact b (q - t) (t + 1) (fun s' h1 h2 => h s' (by omega) (by omega)), dx_ex]; rfl

theorem Qr_poison (b : Nat → Bool) (q t s : Nat) (hs : s ≤ q) (hst : s ≠ t) (he : Empty b s) :
    Qr b q t = (false, false) := by
  rw [Qr]
  by_cases h : s < t
  · rw [Pf_empty b t s h he, dx_zero_l]
  · rw [Sg_empty b (q - t) (t + 1) s (by omega) (by omega) he, dx_zero_r]

theorem Qr_congr (b b' : Nat → Bool) (q t : Nat) (ht : t ≤ q)
    (h : ∀ s ≤ q, s ≠ t → pairR b s = pairR b' s) :
    Qr b q t = Qr b' q t := by
  rw [Qr, Qr, Pf_congr b b' t (fun s hs => h s (by omega) (by omega)),
    Sg_congr b b' (q - t) (t + 1) (fun s' h1 h2 => h s' (by omega) (by omega))]

end Sem1274

namespace Sem1274

variable (q : Nat)

def bx (x : Finset (Fin (2 * (q + 2)))) : Nat → Bool := fun i =>
  if h : i < 2 * (q + 2) then decide ((⟨i, h⟩ : Fin (2 * (q + 2))) ∈ x) else false

theorem mem_iff_bx (x : Finset (Fin (2 * (q + 2)))) (i : Fin (2 * (q + 2))) :
    i ∈ x ↔ bx q x i.val = true := by
  simp [bx, i.isLt]

theorem bx_ge (x : Finset (Fin (2 * (q + 2)))) (i : Nat) (h : 2 * (q + 2) ≤ i) : bx q x i = false := by
  simp [bx]; omega

theorem bx_insert (x : Finset (Fin (2 * (q + 2)))) (j : Fin (2 * (q + 2))) (i : Nat) :
    bx q (insert j x) i = (bx q x i || decide (i = j.val)) := by
  unfold bx
  by_cases h : i < 2 * (q + 2)
  · simp only [h, ↓reduceDIte, Finset.mem_insert]
    by_cases hij : i = j.val
    · subst hij; simp
    · have : (⟨i, h⟩ : Fin (2 * (q + 2))) ≠ j := fun e => hij (by rw [← e])
      simp [this, hij]
  · simp only [h, ↓reduceDIte, Bool.false_or]
    have : i ≠ j.val := by have := j.isLt; omega
    simp [this]

theorem sum_bx (x : Finset (Fin (2 * (q + 2)))) :
    ∑ i ∈ Finset.range (2 * (q + 2)), (bx q x i).toNat = x.card := by
  rw [Finset.sum_range (fun i => (bx q x i).toNat)]
  have e : ∀ i : Fin (2 * (q + 2)), (bx q x i.val).toNat = if i ∈ x then 1 else 0 := by
    intro i
    by_cases hi : i ∈ x
    · simp [bx, i.isLt, hi]
    · simp [bx, i.isLt, hi]
  simp only [e]
  rw [Finset.sum_boole]
  simp

theorem cnt_bx (x : Finset (Fin (2 * (q + 2)))) (L : Nat) (hL : 2 * (q + 2) ≤ L) :
    Net1274.cnt L (bx q x) = x.card := by
  unfold Net1274.cnt
  have e : L = 2 * (q + 2) + (L - 2 * (q + 2)) := by omega
  rw [e, Finset.sum_range_add, sum_bx]
  have hz : ∑ k ∈ Finset.range (L - 2 * (q + 2)), (bx q x (2 * (q + 2) + k)).toNat = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [bx_ge q x _ (by omega)]; rfl
  rw [hz, Nat.add_zero]

def pc (b : Nat → Bool) (t : Nat) : Nat := (b (2 * t)).toNat + (b (2 * t + 1)).toNat

theorem sum_pairs (f : Nat → Nat) : ∀ m, ∑ i ∈ Finset.range (2 * m), f i =
    ∑ t ∈ Finset.range m, (f (2 * t) + f (2 * t + 1))
  | 0 => by simp
  | m + 1 => by
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_pairs f m, Finset.sum_range_succ]
    ring

theorem card_pairs (x : Finset (Fin (2 * (q + 2)))) :
    x.card = ∑ t ∈ Finset.range (q + 2), pc (bx q x) t := by
  rw [← sum_bx, sum_pairs]; rfl

theorem all_one (a : Nat → Nat) (m : Nat) (h1 : ∀ t < m, a t ≤ 1)
    (hs : m ≤ ∑ t ∈ Finset.range m, a t) : ∀ t < m, a t = 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨t, ht, hne⟩ := hc
  have hlt : ∑ s ∈ Finset.range m, a s < ∑ s ∈ Finset.range m, 1 :=
    Finset.sum_lt_sum (fun s hs => h1 s (Finset.mem_range.1 hs))
      ⟨t, Finset.mem_range.2 ht, by have := h1 t ht; omega⟩
  simp at hlt
  omega

def WF (b : Nat → Bool) : Prop := (∀ t ≤ q, Exact b t) ∧ b (2 * q + 2) = true ∧ b (2 * q + 3) = false

theorem wf_of_pc (b : Nat → Bool) (h : ∀ t < q + 2, pc b t = 1) (hs : b (2 * q + 3) = false) : WF q b := by
  refine ⟨fun t ht => ?_, ?_, hs⟩
  · have := h t (by omega)
    unfold pc at this
    unfold Exact
    cases h1 : b (2 * t) <;> cases h2 : b (2 * t + 1) <;> simp_all
  · have := h (q + 1) (by omega)
    unfold pc at this
    rw [show 2 * (q + 1) = 2 * q + 2 by ring, show 2 * q + 2 + 1 = 2 * q + 3 by ring, hs] at this
    cases h1 : b (2 * q + 2) <;> simp_all

def CodeP (z : Finset (Fin q)) (i : Fin (2 * (q + 2))) : Prop :=
  i.val = 2 * q + 2 ∨ (i.val / 2 < q ∧ (i.val % 2 = 1 ↔ ∃ t ∈ z, t.val = i.val / 2)) ∨
    (i.val / 2 = q ∧ i.val % 2 = z.card % 2)

def zOf (b : Nat → Bool) : Finset (Fin q) := Finset.univ.filter (fun t => b (2 * t.val + 1) = true)

theorem par_card (b : Nat → Bool) : ∀ m,
    par b m = decide (((Finset.range m).filter (fun t => b (2 * t + 1) = true)).card % 2 = 1)
  | 0 => by simp [par]
  | m + 1 => by
    rw [par, par_card b m, Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
    generalize (∑ x ∈ Finset.range m, if b (2 * x + 1) = true then 1 else 0) = c
    cases h : b (2 * m + 1) <;> rcases Nat.mod_two_eq_zero_or_one c with h' | h' <;> simp [h', Nat.add_mod]

theorem zOf_card (b : Nat → Bool) :
    (zOf q b).card = ((Finset.range q).filter (fun t => b (2 * t + 1) = true)).card := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext t
  simp only [zOf, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.isLt, ha⟩
  · rintro ⟨ht, hb⟩; exact ⟨⟨t, ht⟩, hb, rfl⟩

theorem bad_iff (f : Finset (Fin q) → Bool) (code : Finset (Fin q) → Finset (Fin (2 * (q + 2))))
    (hcode : ∀ z i, i ∈ code z ↔ CodeP q z i) (y : Finset (Fin (2 * (q + 2)))) :
    (∃ z, f z = false ∧ y = code z) ↔
      (WF q (bx q y) ∧ par (bx q y) (q + 1) = false ∧ f (zOf q (bx q y)) = false) := by
  have hb : ∀ (i : Nat) (hi : i < 2 * (q + 2)), bx q y i = true ↔ (⟨i, hi⟩ : Fin (2 * (q + 2))) ∈ y := by
    intro i hi; rw [mem_iff_bx]
  constructor
  · rintro ⟨z, hf, rfl⟩
    have hv : ∀ (i : Nat) (hi : i < 2 * (q + 2)), bx q (code z) i = true ↔ CodeP q z ⟨i, hi⟩ := by
      intro i hi; rw [hb i hi, hcode]
    have hodd : ∀ t < q, bx q (code z) (2 * t + 1) = true ↔ ∃ s ∈ z, s.val = t := by
      intro t ht
      rw [hv _ (by omega)]
      unfold CodeP
      simp only
      have e1 : (2 * t + 1) / 2 = t := by omega
      have e2 : (2 * t + 1) % 2 = 1 := by omega
      rw [e1, e2]
      constructor
      · rintro (h | ⟨_, h⟩ | ⟨h, _⟩)
        · omega
        · exact h.1 rfl
        · omega
      · intro h; exact Or.inr (Or.inl ⟨ht, ⟨fun _ => h, fun _ => rfl⟩⟩)
    have hev : ∀ t < q, bx q (code z) (2 * t) = true ↔ ¬ ∃ s ∈ z, s.val = t := by
      intro t ht
      rw [hv _ (by omega)]
      unfold CodeP
      simp only
      have e1 : (2 * t) / 2 = t := by omega
      have e2 : (2 * t) % 2 = 0 := by omega
      rw [e1, e2]
      constructor
      · rintro (h | ⟨_, h⟩ | ⟨h, _⟩)
        · omega
        · intro hh; exact absurd (h.2 hh) (by omega)
        · omega
      · intro h; exact Or.inr (Or.inl ⟨ht, ⟨fun h' => absurd h' (by omega), fun h' => absurd h' h⟩⟩)
    have hq1 : bx q (code z) (2 * q + 1) = true ↔ z.card % 2 = 1 := by
      rw [hv _ (by omega)]
      unfold CodeP
      simp only
      constructor
      · rintro (h | ⟨h, _⟩ | ⟨_, h⟩)
        · omega
        · omega
        · omega
      · intro h; exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    have hq0 : bx q (code z) (2 * q) = true ↔ z.card % 2 = 0 := by
      rw [hv _ (by omega)]
      unfold CodeP
      simp only
      constructor
      · rintro (h | ⟨h, _⟩ | ⟨_, h⟩)
        · omega
        · omega
        · omega
      · intro h; exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    have hq2 : bx q (code z) (2 * q + 2) = true := by
      rw [hv _ (by omega)]; exact Or.inl rfl
    have hq3 : bx q (code z) (2 * q + 3) = false := by
      cases h : bx q (code z) (2 * q + 3)
      · rfl
      · rw [hv _ (by omega)] at h
        unfold CodeP at h
        simp only at h
        omega
    have hzof : zOf q (bx q (code z)) = z := by
      ext t
      simp only [zOf, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hodd t.val t.isLt]
      constructor
      · rintro ⟨s, hs, hst⟩; rwa [← Fin.ext hst]
      · intro ht; exact ⟨t, ht, rfl⟩
    have hwf : WF q (bx q (code z)) := by
      refine ⟨fun t ht => ?_, hq2, hq3⟩
      unfold Exact
      rcases Nat.lt_or_ge t q with h | h
      · have ho := hodd t h
        have he := hev t h
        by_cases E : ∃ s ∈ z, s.val = t
        · have v1 : bx q (code z) (2 * t + 1) = true := ho.2 E
          have v0 : bx q (code z) (2 * t) = false := by
            cases hh : bx q (code z) (2 * t)
            · rfl
            · exact absurd E (he.1 hh)
          rw [v0, v1]; rfl
        · have v1 : bx q (code z) (2 * t + 1) = false := by
            cases hh : bx q (code z) (2 * t + 1)
            · rfl
            · exact absurd (ho.1 hh) E
          have v0 : bx q (code z) (2 * t) = true := he.2 E
          rw [v0, v1]; rfl
      · rw [show t = q by omega]
        by_cases hc : z.card % 2 = 1
        · have v1 : bx q (code z) (2 * q + 1) = true := hq1.2 hc
          have v0 : bx q (code z) (2 * q) = false := by
            cases hh : bx q (code z) (2 * q)
            · rfl
            · have := hq0.1 hh; omega
          rw [v0, v1]; rfl
        · have v1 : bx q (code z) (2 * q + 1) = false := by
            cases hh : bx q (code z) (2 * q + 1)
            · rfl
            · exact absurd (hq1.1 hh) hc
          have v0 : bx q (code z) (2 * q) = true := hq0.2 (by omega)
          rw [v0, v1]; rfl
    refine ⟨hwf, ?_, by rw [hzof]; exact hf⟩
    rw [par, par_card, ← zOf_card, hzof]
    rcases Nat.mod_two_eq_zero_or_one z.card with h | h
    · have : bx q (code z) (2 * q + 1) = false := by
        cases h' : bx q (code z) (2 * q + 1)
        · rfl
        · have := hq1.1 h'; omega
      simp [h, this]
    · have : bx q (code z) (2 * q + 1) = true := hq1.2 h
      simp [h, this]
  · rintro ⟨hwf, hpar, hf⟩
    refine ⟨zOf q (bx q y), hf, ?_⟩
    ext i
    rw [hcode, mem_iff_bx]
    obtain ⟨hex, h2, h3⟩ := hwf
    have hpq : par (bx q y) q = bx q y (2 * q + 1) := by
      rw [par] at hpar
      cases h1 : par (bx q y) q <;> cases h2 : bx q y (2 * q + 1) <;> simp_all
    have hzc : (zOf q (bx q y)).card % 2 = 1 ↔ bx q y (2 * q + 1) = true := by
      rw [← hpq, par_card, zOf_card]; simp
    have hzm : ∀ t < q, (∃ s ∈ zOf q (bx q y), s.val = t) ↔ bx q y (2 * t + 1) = true := by
      intro t ht
      simp only [zOf, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨s, hs, rfl⟩; exact hs
      · intro h; exact ⟨⟨t, ht⟩, h, rfl⟩
    unfold CodeP
    obtain ⟨iv, hi⟩ := i
    simp only
    have hdecomp : iv = 2 * (iv / 2) + iv % 2 := by omega
    rcases Nat.lt_or_ge (iv / 2) q with ht | ht
    · have hm := hzm (iv / 2) ht
      rcases Nat.mod_two_eq_zero_or_one iv with hp | hp
      · have he := hex (iv / 2) (by omega)
        unfold Exact at he
        rw [show iv = 2 * (iv / 2) by omega] at ⊢
        rw [he]
        constructor
        · intro h; refine Or.inr (Or.inl ⟨by omega, ?_⟩)
          constructor
          · intro h'; omega
          · intro h'; rw [show 2 * (iv / 2) / 2 = iv / 2 by omega] at h'; rw [hm.1 h'] at h; simp at h
        · rintro (h | ⟨_, h⟩ | ⟨h, _⟩)
          · omega
          · rw [show 2 * (iv / 2) / 2 = iv / 2 by omega, show 2 * (iv / 2) % 2 = 0 by omega] at h
            cases hh : bx q y (2 * (iv / 2) + 1)
            · rfl
            · have := h.2 (hm.2 hh); omega
          · omega
      · rw [show iv = 2 * (iv / 2) + 1 by omega] at ⊢
        rw [show (2 * (iv / 2) + 1) / 2 = iv / 2 by omega, show (2 * (iv / 2) + 1) % 2 = 1 by omega]
        constructor
        · intro h; exact Or.inr (Or.inl ⟨ht, ⟨fun _ => hm.2 h, fun _ => rfl⟩⟩)
        · rintro (h | ⟨_, h⟩ | ⟨h, _⟩)
          · omega
          · exact hm.1 (h.1 rfl)
          · omega
    · rcases Nat.lt_or_ge (iv / 2) (q + 1) with ht2 | ht2
      · have htq : iv / 2 = q := by omega
        rcases Nat.mod_two_eq_zero_or_one iv with hp | hp
        · have hiv : iv = 2 * q := by omega
          subst hiv
          have he := hex q le_rfl
          unfold Exact at he
          rw [he]
          constructor
          · intro h
            refine Or.inr (Or.inr ⟨by omega, ?_⟩)
            have : bx q y (2 * q + 1) = false := by simpa using h
            have h' : ¬ (zOf q (bx q y)).card % 2 = 1 := fun hh => by rw [hzc.1 hh] at this; simp at this
            omega
          · rintro (h | ⟨h, _⟩ | ⟨_, h⟩)
            · omega
            · omega
            · have h' : (zOf q (bx q y)).card % 2 ≠ 1 := by omega
              cases hh : bx q y (2 * q + 1)
              · rfl
              · exact absurd (hzc.2 hh) h'
        · have hiv : iv = 2 * q + 1 := by omega
          subst hiv
          constructor
          · intro h
            refine Or.inr (Or.inr ⟨by omega, ?_⟩)
            have := hzc.2 h
            omega
          · rintro (h | ⟨h, _⟩ | ⟨_, h⟩)
            · omega
            · omega
            · exact hzc.1 (by omega)
      · have htq : iv / 2 = q + 1 := by omega
        rcases Nat.mod_two_eq_zero_or_one iv with hp | hp
        · have hiv : iv = 2 * q + 2 := by omega
          subst hiv
          simp [h2]
        · have hiv : iv = 2 * q + 3 := by omega
          subst hiv
          rw [h3]
          simp only [Bool.false_eq_true, false_iff]
          omega

end Sem1274

namespace Sem1274

open PEqualNP.CircuitLowerBounds

def dflt : Bool × Bool := (false, true)

def simStep (g : Gate) (w : List (Bool × Bool)) : Bool × Bool :=
  match g.op with
  | .and => ((g.inputs.map fun i => (w.getD i dflt).1).all id, (g.inputs.map fun i => (w.getD i dflt).2).any id)
  | .or => ((g.inputs.map fun i => (w.getD i dflt).1).any id, (g.inputs.map fun i => (w.getD i dflt).2).all id)
  | .not => match g.inputs with
    | [] => (true, false)
    | i :: _ => ((w.getD i dflt).2, (w.getD i dflt).1)
  | _ => dflt

def simW (gs : List Gate) (w : List (Bool × Bool)) : List (Bool × Bool) :=
  gs.foldl (fun w g => w ++ [simStep g w]) w

theorem getD_map_ex (w : List Bool) (i : Nat) : (w.map ex).getD i dflt = ex (w.getD i false) := by
  by_cases h : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]; rfl

theorem any_map_not (l : List Nat) (f : Nat → Bool) :
    (l.map fun i => !(f i)).any id = !((l.map f).all id) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.any_cons, List.all_cons, id, ih]; cases f a <;> simp

theorem all_map_not (l : List Nat) (f : Nat → Bool) :
    (l.map fun i => !(f i)).all id = !((l.map f).any id) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.any_cons, List.all_cons, id, ih]; cases f a <;> simp

theorem simStep_ok (g : Gate) (hg : g.op = .and ∨ g.op = .or ∨ g.op = .not) (w : List Bool) :
    simStep g (w.map ex) = ex (g.op.eval (g.inputs.map fun i => w.getD i false)) := by
  rcases g with ⟨op, ins⟩
  simp only at hg
  rcases hg with rfl | rfl | rfl
  · simp only [simStep, getD_map_ex, ex, GateOp.eval]
    rw [any_map_not]
  · simp only [simStep, getD_map_ex, ex, GateOp.eval]
    rw [all_map_not]
  · cases ins with
    | nil => rfl
    | cons i _ =>
      simp only [simStep, getD_map_ex]
      simp [ex, GateOp.eval]

theorem simW_ok (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    ∀ w : List Bool, simW gs (w.map ex) =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).map ex := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    simp only [simW, List.foldl_cons] at ih ⊢
    rw [simStep_ok g (hgs g List.mem_cons_self) w]
    have e : w.map ex ++ [ex (g.op.eval (g.inputs.map fun i => w.getD i false))] =
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).map ex := by simp
    rw [e]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _

def initR (b : Nat → Bool) (q i : Nat) : Bool × Bool :=
  if i < q then zR b q i else if i = q then (false, true) else (true, false)

def w0 (b : Nat → Bool) (q : Nat) : List (Bool × Bool) := (List.range (q + 2)).map (initR b q)

def FB (D : Circuit) (q : Nat) (b : Nat → Bool) : Bool := ((simW D.gates (w0 b q)).getD D.output dflt).1

theorem FB_ok (D : Circuit) (q : Nat) (f : Finset (Fin q) → Bool)
    (hD : ∀ g ∈ D.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hf : ∀ z : Finset (Fin q), D.eval (List.ofFn (fun i : Fin q => decide (i ∈ z)) ++ [false, true]) = f z)
    (b c : Nat → Bool) (hz : ∀ t < q, zR b q t = ex (c t)) :
    FB D q b = f (Finset.univ.filter (fun t : Fin q => c t.val = true)) := by
  set Z := Finset.univ.filter (fun t : Fin q => c t.val = true) with hZ
  have hw : w0 b q = (List.ofFn (fun i : Fin q => decide (i ∈ Z)) ++ [false, true]).map ex := by
    apply List.ext_getElem
    · simp [w0]
    · intro i h1 h2
      simp only [w0, List.length_map, List.length_range] at h1
      simp only [w0, List.getElem_map, List.getElem_range]
      simp only [initR]
      rcases Nat.lt_or_ge i q with hi | hi
      · rw [if_pos hi, hz i hi, List.getElem_append_left (by simpa using hi)]
        simp [hZ]
      · rw [List.getElem_append_right (by simpa using hi)]
        simp only [List.length_ofFn]
        rcases Nat.lt_or_ge i (q + 1) with hi2 | hi2
        · have : i = q := by omega
          subst this
          simp [ex]
        · have : i = q + 1 := by omega
          subst this
          simp [ex]
  rw [FB, hw, simW_ok D.gates hD, getD_map_ex]
  simp only [ex]
  rw [← hf Z]
  rfl

end Sem1274

namespace Sem1274

open PEqualNP.CircuitLowerBounds

def colB (q : Nat) (b : Nat → Bool) : Bool := (List.range (q + 1)).any (fun t => b (2 * t) && b (2 * t + 1))

theorem colB_true (q : Nat) (b : Nat → Bool) :
    colB q b = true ↔ ∃ t ≤ q, b (2 * t) = true ∧ b (2 * t + 1) = true := by
  simp only [colB, List.any_eq_true, List.mem_range, Bool.and_eq_true]
  constructor
  · rintro ⟨t, ht, h⟩; exact ⟨t, by omega, h⟩
  · rintro ⟨t, ht, h⟩; exact ⟨t, by omega, h⟩

def oddT (q : Nat) (b : Nat → Bool) : Bool := (Pf b (q + 1)).1
def G0 (D : Circuit) (q : Nat) (b : Nat → Bool) : Bool := colB q b || b (2 * q + 3) || FB D q b
def partner (j : Nat) : Nat := if j % 2 = 0 then j + 1 else j - 1
def oddY (q : Nat) (b : Nat → Bool) (j : Nat) : Bool :=
  if j / 2 ≤ q then (if j % 2 = 1 then (Qr b q (j / 2)).2 else (Qr b q (j / 2)).1)
  else (if j % 2 = 0 then oddT q b else true)
def Hj (D : Circuit) (q : Nat) (b : Nat → Bool) (j : Nat) : Bool := G0 D q b || b (partner j) || oddY q b j

def Bad (q : Nat) (f : Finset (Fin q) → Bool) (b : Nat → Bool) : Prop :=
  WF q b ∧ par b (q + 1) = false ∧ f (zOf q b) = false

theorem not_wf_col (q : Nat) (b : Nat → Bool) (t : Nat) (ht : t ≤ q) (h1 : b (2 * t) = true)
    (h2 : b (2 * t + 1) = true) : ¬ WF q b := by
  rintro ⟨hex, _, _⟩
  have := hex t ht
  unfold Exact at this
  rw [h1, h2] at this
  simp at this

theorem not_wf_spare (q : Nat) (b : Nat → Bool) (h : b (2 * q + 3) = true) : ¬ WF q b := by
  rintro ⟨_, _, h3⟩; rw [h] at h3; simp at h3

theorem pc_le_one (b : Nat → Bool) (t : Nat) (h : ¬ (b (2 * t) = true ∧ b (2 * t + 1) = true)) : pc b t ≤ 1 := by
  unfold pc
  cases h1 : b (2 * t) <;> cases h2 : b (2 * t + 1) <;> simp_all

theorem zR_exact_all (q : Nat) (b : Nat → Bool) (hex : ∀ s ≤ q, Exact b s) (hp : par b (q + 1) = false) :
    ∀ t < q, zR b q t = ex (b (2 * t + 1)) := by
  intro t ht
  have hQ := Qr_exact b q t (fun s hs _ => hex s hs) (by omega)
  have ho := par_oth b q t (by omega)
  rw [hp] at ho
  have hoth : oth b q t = b (2 * t + 1) := by
    revert ho
    generalize oth b q t = o
    generalize b (2 * t + 1) = c
    cases o <;> cases c <;> decide
  have he := hex t (by omega)
  unfold Exact at he
  simp only [zR, hQ, hoth, ex, he]
  cases b (2 * t + 1) <;> rfl

theorem bad_end (q : Nat) (f : Finset (Fin q) → Bool) (b : Nat → Bool) (hwf : WF q b)
    (hp : par b (q + 1) = false) : f (zOf q b) = true ↔ ¬ Bad q f b := by
  constructor
  · intro h1 h2; rw [h2.2.2] at h1; exact Bool.false_ne_true h1
  · intro h1
    cases h2 : f (zOf q b)
    · exact absurd ⟨hwf, hp, h2⟩ h1
    · rfl

theorem bad_odd (q : Nat) (f : Finset (Fin q) → Bool) (b : Nat → Bool) (hp : par b (q + 1) = true) :
    ¬ Bad q f b := by
  intro h; rw [h.2.1] at hp; exact Bool.false_ne_true hp

theorem main_ok (D : Circuit) (q : Nat) (f : Finset (Fin q) → Bool)
    (hD : ∀ g ∈ D.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hf : ∀ z : Finset (Fin q), D.eval (List.ofFn (fun i : Fin q => decide (i ∈ z)) ++ [false, true]) = f z)
    (x : Finset (Fin (2 * (q + 2)))) (hx : x.card = q + 2) :
    (G0 D q (bx q x) || oddT q (bx q x)) = true ↔ ¬ Bad q f (bx q x) := by
  have hsum := card_pairs q x
  set b := bx q x with hb
  by_cases hc : colB q b = true
  · obtain ⟨t, ht, h1, h2⟩ := (colB_true q b).1 hc
    simp only [G0, hc, Bool.true_or, true_iff]
    exact fun h => not_wf_col q b t ht h1 h2 h.1
  by_cases hs : b (2 * q + 3) = true
  · simp only [G0, hs, Bool.or_true, Bool.true_or, true_iff]
    exact fun h => not_wf_spare q b hs h.1
  have hc' : colB q b = false := by simpa using hc
  have hs' : b (2 * q + 3) = false := by simpa using hs
  have hpc : ∀ t < q + 2, pc b t ≤ 1 := by
    intro t ht
    rcases Nat.lt_or_ge t (q + 1) with h | h
    · apply pc_le_one; intro hh; exact hc ((colB_true q b).2 ⟨t, by omega, hh⟩)
    · have : t = q + 1 := by omega
      subst this
      apply pc_le_one
      intro hh
      rw [show 2 * (q + 1) + 1 = 2 * q + 3 by ring, hs'] at hh
      simp at hh
  have hall := all_one (pc b) (q + 2) hpc (by omega)
  have hwf := wf_of_pc q b hall hs'
  have hodd : oddT q b = par b (q + 1) := by
    unfold oddT; rw [Pf_exact b (q + 1) (fun s hs => hwf.1 s (by omega))]; rfl
  simp only [G0, hc', hs', Bool.false_or, hodd]
  cases hp : par b (q + 1)
  · have hz := zR_exact_all q b hwf.1 hp
    have hF := FB_ok D q f hD hf b (fun t => b (2 * t + 1)) hz
    rw [hF, Bool.or_false]
    exact bad_end q f b hwf hp
  · simp only [Bool.or_true, true_iff]
    exact bad_odd q f b hp

theorem tap_ok (D : Circuit) (q : Nat) (f : Finset (Fin q) → Bool)
    (hD : ∀ g ∈ D.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hf : ∀ z : Finset (Fin q), D.eval (List.ofFn (fun i : Fin q => decide (i ∈ z)) ++ [false, true]) = f z)
    (x : Finset (Fin (2 * (q + 2)))) (j : Fin (2 * (q + 2))) (hx : (insert j x).card = q + 2) :
    Hj D q (bx q x) j.val = true ↔ ¬ Bad q f (bx q (insert j x)) := by
  have hsum := card_pairs q (insert j x)
  have hbb := bx_insert q x j
  have hJn := j.isLt
  set b := bx q x with hb
  set b' := bx q (insert j x) with hb'
  set J := j.val with hJ
  have hbJ : b' J = true := by rw [hbb]; simp
  have hle : ∀ i, b i = true → b' i = true := by intro i h; rw [hbb, h]; rfl
  have hne : ∀ i, i ≠ J → b' i = b i := by intro i h; rw [hbb]; simp [h]
  have hpJ : partner J ≠ J := by unfold partner; split_ifs <;> omega
  by_cases hA : colB q b = true ∨ b (2 * q + 3) = true ∨ b (partner J) = true ∨ J = 2 * q + 3
  · have hH : Hj D q b J = true := by
      rcases hA with h | h | h | h
      · simp [Hj, G0, h]
      · simp [Hj, G0, h]
      · simp [Hj, h]
      · have : oddY q b J = true := by
          unfold oddY; rw [if_neg (by omega), if_neg (by omega)]
        simp [Hj, this]
    rw [iff_true_left hH]
    intro hbad
    have hw := hbad.1
    rcases hA with h | h | h | h
    · obtain ⟨t, ht, h1, h2⟩ := (colB_true q b).1 h
      exact not_wf_col q b' t ht (hle _ h1) (hle _ h2) hw
    · exact not_wf_spare q b' (hle _ h) hw
    · have hpt := hle _ h
      rcases Nat.lt_or_ge (J / 2) (q + 1) with ht | ht
      · rcases Nat.mod_two_eq_zero_or_one J with hm | hm
        · have e : partner J = 2 * (J / 2) + 1 := by unfold partner; rw [if_pos hm]; omega
          apply not_wf_col q b' (J / 2) (by omega) _ _ hw
          · rw [show 2 * (J / 2) = J by omega]; exact hbJ
          · rw [← e]; exact hpt
        · have e : partner J = 2 * (J / 2) := by unfold partner; rw [if_neg (by omega)]; omega
          apply not_wf_col q b' (J / 2) (by omega) _ _ hw
          · rw [← e]; exact hpt
          · rw [show 2 * (J / 2) + 1 = J by omega]; exact hbJ
      · apply not_wf_spare q b' _ hw
        rcases Nat.mod_two_eq_zero_or_one J with hm | hm
        · have e : partner J = 2 * q + 3 := by unfold partner; rw [if_pos hm]; omega
          rw [← e]; exact hpt
        · rw [show 2 * q + 3 = J by omega]; exact hbJ
    · exact not_wf_spare q b' (by rw [← h]; exact hbJ) hw
  rw [not_or, not_or, not_or] at hA
  obtain ⟨hc, hs, hpa, hJ3⟩ := hA
  have hc' : colB q b = false := by simpa using hc
  have hs' : b (2 * q + 3) = false := by simpa using hs
  have hpa' : b (partner J) = false := by simpa using hpa
  have hs'' : b' (2 * q + 3) = false := by rw [hne _ (by omega)]; exact hs'
  have hbp : b' (partner J) = false := by rw [hne _ hpJ]; exact hpa'
  have hpc : ∀ t < q + 2, pc b' t ≤ 1 := by
    intro t ht
    by_cases htJ : t = J / 2
    · apply pc_le_one
      rintro ⟨h1, h2⟩
      rw [htJ] at h1 h2
      rcases Nat.mod_two_eq_zero_or_one J with hm | hm
      · have e : partner J = 2 * (J / 2) + 1 := by unfold partner; rw [if_pos hm]; omega
        rw [← e, hbp] at h2; simp at h2
      · have e : partner J = 2 * (J / 2) := by unfold partner; rw [if_neg (by omega)]; omega
        rw [← e, hbp] at h1; simp at h1
    · have e1 : b' (2 * t) = b (2 * t) := hne _ (by omega)
      have e2 : b' (2 * t + 1) = b (2 * t + 1) := hne _ (by omega)
      have hpp : pc b' t = pc b t := by unfold pc; rw [e1, e2]
      rw [hpp]
      apply pc_le_one
      rintro ⟨h1, h2⟩
      rcases Nat.lt_or_ge t (q + 1) with h | h
      · exact hc ((colB_true q b).2 ⟨t, by omega, h1, h2⟩)
      · have : t = q + 1 := by omega
        rw [this, show 2 * (q + 1) + 1 = 2 * q + 3 by ring, hs'] at h2
        simp at h2
  have hall := all_one (pc b') (q + 2) hpc (by omega)
  have hwf := wf_of_pc q b' hall hs''
  have hH : Hj D q b J = (FB D q b || oddY q b J) := by simp [Hj, G0, hc', hs', hpa']
  rw [hH]
  have hpairs : ∀ s, s ≠ J / 2 → pairR b s = pairR b' s := by
    intro s hs
    simp only [pairR]
    rw [hne (2 * s + 1) (by omega), hne (2 * s) (by omega)]
  have hY : oddY q b J = par b' (q + 1) := by
    unfold oddY
    by_cases ht : J / 2 ≤ q
    · rw [if_pos ht]
      have hQ : Qr b q (J / 2) = ex (oth b' q (J / 2)) := by
        rw [Qr_congr b b' q (J / 2) ht (fun s _ hs => hpairs s hs)]
        exact Qr_exact b' q (J / 2) (fun s hs _ => hwf.1 s hs) ht
      rw [hQ, par_oth b' q (J / 2) ht]
      rcases Nat.mod_two_eq_zero_or_one J with hm | hm
      · rw [if_neg (by omega)]
        have hex := hwf.1 (J / 2) ht
        unfold Exact at hex
        have e2 : 2 * (J / 2) = J := by omega
        have h0 : b' (2 * (J / 2) + 1) = false := by
          rw [e2] at hex ⊢
          rw [hbJ] at hex
          cases h : b' (J + 1)
          · rfl
          · rw [h] at hex; simp at hex
        rw [h0]; simp [ex]
      · rw [if_pos hm, show 2 * (J / 2) + 1 = J by omega, hbJ]; simp [ex]
    · rw [if_neg ht]
      rw [if_pos (by omega)]
      unfold oddT
      rw [Pf_congr b b' (q + 1) (fun s hs => hpairs s (by omega)),
        Pf_exact b' (q + 1) (fun s hs => hwf.1 s (by omega))]
      rfl
  rw [hY]
  cases hp : par b' (q + 1)
  · have hz : ∀ t < q, zR b q t = ex (b' (2 * t + 1)) := by
      by_cases hbJ' : b J = true
      · have hbe : b = b' := by
          funext i
          by_cases hi : i = J
          · rw [hi, hbJ]; exact hbJ'
          · exact (hne i hi).symm
        rw [hbe]; exact zR_exact_all q b' hwf.1 hp
      · have hbJf : b J = false := by simpa using hbJ'
        by_cases ht : J / 2 ≤ q
        · have hemp : Empty b (J / 2) := by
            rcases Nat.mod_two_eq_zero_or_one J with hm | hm
            · have e : partner J = 2 * (J / 2) + 1 := by unfold partner; rw [if_pos hm]; omega
              exact ⟨by rw [show 2 * (J / 2) = J by omega]; exact hbJf, by rw [← e]; exact hpa'⟩
            · have e : partner J = 2 * (J / 2) := by unfold partner; rw [if_neg (by omega)]; omega
              exact ⟨by rw [← e]; exact hpa', by rw [show 2 * (J / 2) + 1 = J by omega]; exact hbJf⟩
          intro t htq
          by_cases htt : t = J / 2
          · rw [htt]
            have hQ : Qr b q (J / 2) = ex (oth b' q (J / 2)) := by
              rw [Qr_congr b b' q (J / 2) ht (fun s _ hs => hpairs s hs)]
              exact Qr_exact b' q (J / 2) (fun s hs _ => hwf.1 s hs) ht
            have ho := par_oth b' q (J / 2) ht
            rw [hp] at ho
            have hoth : oth b' q (J / 2) = b' (2 * (J / 2) + 1) := by
              revert ho
              generalize oth b' q (J / 2) = o
              generalize b' (2 * (J / 2) + 1) = c
              cases o <;> cases c <;> decide
            simp only [zR, hQ, hemp.1, hemp.2, Bool.false_or, hoth, ex]
          · have hQ : Qr b q t = (false, false) := Qr_poison b q t (J / 2) ht (Ne.symm htt) hemp
            have he := hwf.1 t (by omega)
            unfold Exact at he
            simp only [zR, hQ, Bool.or_false, ex]
            rw [← hne (2 * t + 1) (by omega), ← hne (2 * t) (by omega), he]
        · intro t htq
          have hzz : zR b q t = zR b' q t := by
            simp only [zR]
            rw [Qr_congr b b' q t (by omega) (fun s hs _ => hpairs s (by omega)),
              hne (2 * t + 1) (by omega), hne (2 * t) (by omega)]
          rw [hzz]; exact zR_exact_all q b' hwf.1 hp t htq
    have hF := FB_ok D q f hD hf b (fun t => b' (2 * t + 1)) hz
    rw [hF, Bool.or_false]
    exact bad_end q f b' hwf hp
  · simp only [Bool.or_true, true_iff]
    exact bad_odd q f b' hp

end Sem1274

namespace Asm1274

open Build049 NetBuild1274 Net1274 Sem1274
open PEqualNP.CircuitLowerBounds

variable {N : Nat}

theorem and2orG {A : Set (Sig N)} {a b c d : Sig N} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) :
    Build A {fun X => (a X && b X) || (c X && d X)} 3 := by
  have h1 := andG ha hb
  have h2 := andG (A := A ∪ {an a b}) (Or.inl hc) (Or.inl hd)
  have h3 := orG (A := A ∪ ({an a b} ∪ {an c d})) (f := an a b) (g := an c d)
    (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  exact relax (seq (seq h1 h2) h3) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

theorem xorG {A : Set (Sig N)} {a1 a2 c1 c2 : Sig N} (h1 : a1 ∈ A) (h2 : a2 ∈ A) (h3 : c1 ∈ A) (h4 : c2 ∈ A) :
    Build A {fun X => (dx (a1 X, a2 X) (c1 X, c2 X)).1, fun X => (dx (a1 X, a2 X) (c1 X, c2 X)).2} 6 := by
  rw [Set.insert_eq]
  exact par (and2orG h1 h4 h2 h3) (and2orG h1 h3 h2 h4)

theorem or3G {A : Set (Sig N)} {a b c : Sig N} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
    Build A {fun X => a X || b X || c X} 2 := by
  have h1 := orG ha hb
  have h2 := orG (A := A ∪ {Build049.or a b}) (f := Build049.or a b) (g := c) (Or.inr rfl) (Or.inl hc)
  exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

theorem simStepBuild {A : Set (Sig N)} (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : g.inputs.length ≤ 2)
    (W : (Fin N → Bool) → List (Bool × Bool))
    (hin : ∀ i ∈ g.inputs, (fun X => ((W X).getD i dflt).1) ∈ A ∧ (fun X => ((W X).getD i dflt).2) ∈ A) :
    Build A {fun X => (simStep g (W X)).1, fun X => (simStep g (W X)).2} 2 := by
  rw [Set.insert_eq]
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen hin
  have hd1 : ∀ x ∈ ins.map (fun i => fun X => ((W X).getD i dflt).1), x ∈ A := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx; exact (hin i hi).1
  have hd2 : ∀ x ∈ ins.map (fun i => fun X => ((W X).getD i dflt).2), x ∈ A := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx; exact (hin i hi).2
  rcases hop with rfl | rfl | rfl
  · exact par (one .and _ (by simp) (by simpa using hlen) hd1 _ (by intro X; simp [simStep, GateOp.eval, List.map_map]; rfl))
      (one .or _ (by simp) (by simpa using hlen) hd2 _ (by intro X; simp [simStep, GateOp.eval, List.map_map]; rfl))
  · exact par (one .or _ (by simp) (by simpa using hlen) hd1 _ (by intro X; simp [simStep, GateOp.eval, List.map_map]; rfl))
      (one .and _ (by simp) (by simpa using hlen) hd2 _ (by intro X; simp [simStep, GateOp.eval, List.map_map]; rfl))
  · cases ins with
    | nil =>
      have e1 : (fun X => (simStep ⟨GateOp.not, []⟩ (W X)).1) = fun _ => true := by funext X; rfl
      have e2 : (fun X => (simStep ⟨GateOp.not, []⟩ (W X)).2) = fun _ => false := by funext X; rfl
      rw [e1, e2]
      exact par (constG true) (constG false)
    | cons i rest =>
      have e1 : (fun X => (simStep ⟨GateOp.not, i :: rest⟩ (W X)).1) =
          fun X => GateOp.or.eval ([fun X => ((W X).getD i dflt).2].map fun g => g X) := by
        funext X; simp [simStep, GateOp.eval]
      have e2 : (fun X => (simStep ⟨GateOp.not, i :: rest⟩ (W X)).2) =
          fun X => GateOp.or.eval ([fun X => ((W X).getD i dflt).1].map fun g => g X) := by
        funext X; simp [simStep, GateOp.eval]
      rw [e1, e2]
      have hi := hin i List.mem_cons_self
      exact par (one .or _ (by simp) (by simp) (by simpa using hi.2) _ (fun _ => rfl))
        (one .or _ (by simp) (by simp) (by simpa using hi.1) _ (fun _ => rfl))

end Asm1274

namespace Asm1274

open Build049 NetBuild1274 Net1274 Sem1274
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

variable (q : Nat)

abbrev NN : Nat := 2 * (q + 2) + 2

def bv (X : Fin (NN q) → Bool) : Nat → Bool := fun i =>
  if h : i < 2 * (q + 2) then X ⟨i, by unfold NN; omega⟩ else false

def inS (i : Fin (NN q)) : Sig (NN q) := fun X => X i
def bitS (i : Nat) : Sig (NN q) := fun X => bv q X i
def tru : Sig (NN q) := fun _ => true
def fls : Sig (NN q) := fun _ => false

theorem bitS_mem (i : Nat) (hi : i < 2 * (q + 2)) : bitS q i ∈ Set.range (inS q) :=
  ⟨⟨i, by unfold NN; omega⟩, by funext X; simp [inS, bitS, bv, hi]⟩

def P1 (t : Nat) : Sig (NN q) := fun X => (Pf (bv q X) t).1
def P2 (t : Nat) : Sig (NN q) := fun X => (Pf (bv q X) t).2
def PfSet (m : Nat) : Set (Sig (NN q)) := {f | ∃ t ≤ m, f = P1 q t ∨ f = P2 q t}

theorem pfBuild (A : Set (Sig (NN q))) (htr : tru q ∈ A) (hfl : fls q ∈ A)
    (hbit : ∀ i < 2 * (q + 2), bitS q i ∈ A) : ∀ m, m ≤ q + 1 → Build A (PfSet q m) (6 * m)
  | 0, _ => by
    apply idle
    rintro f ⟨t, ht, hf⟩
    have : t = 0 := by omega
    subst this
    rcases hf with rfl | rfl
    · exact hfl
    · exact htr
  | m + 1, hm => by
    have ih := pfBuild A htr hfl hbit m (by omega)
    have hx := xorG (A := A ∪ PfSet q m) (a1 := P1 q m) (a2 := P2 q m) (c1 := bitS q (2 * m + 1))
      (c2 := bitS q (2 * m)) (Or.inr ⟨m, le_rfl, Or.inl rfl⟩) (Or.inr ⟨m, le_rfl, Or.inr rfl⟩)
      (Or.inl (hbit _ (by omega))) (Or.inl (hbit _ (by omega)))
    refine relax (seq ih hx) le_rfl ?_ (by omega)
    rintro f ⟨t, ht, hf⟩
    rcases Nat.lt_or_ge t (m + 1) with h | h
    · exact Or.inl ⟨t, by omega, hf⟩
    · have : t = m + 1 := by omega
      subst this
      right
      rcases hf with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl

def S1 (m : Nat) : Sig (NN q) := fun X => (Sg (bv q X) m (q + 1 - m)).1
def S2 (m : Nat) : Sig (NN q) := fun X => (Sg (bv q X) m (q + 1 - m)).2
def SgSet (m : Nat) : Set (Sig (NN q)) := {f | ∃ t ≤ m, f = S1 q t ∨ f = S2 q t}

theorem sgBuild (A : Set (Sig (NN q))) (htr : tru q ∈ A) (hfl : fls q ∈ A)
    (hbit : ∀ i < 2 * (q + 2), bitS q i ∈ A) : ∀ m, m ≤ q + 1 → Build A (SgSet q m) (6 * m)
  | 0, _ => by
    apply idle
    rintro f ⟨t, ht, hf⟩
    have : t = 0 := by omega
    subst this
    rcases hf with rfl | rfl
    · exact hfl
    · exact htr
  | m + 1, hm => by
    have ih := sgBuild A htr hfl hbit m (by omega)
    have hx := xorG (A := A ∪ SgSet q m) (a1 := bitS q (2 * (q - m) + 1)) (a2 := bitS q (2 * (q - m)))
      (c1 := S1 q m) (c2 := S2 q m)
      (Or.inl (hbit _ (by omega))) (Or.inl (hbit _ (by omega)))
      (Or.inr ⟨m, le_rfl, Or.inl rfl⟩) (Or.inr ⟨m, le_rfl, Or.inr rfl⟩)
    have e1 : S1 q (m + 1) = fun X => (dx (bitS q (2 * (q - m) + 1) X, bitS q (2 * (q - m)) X)
        (S1 q m X, S2 q m X)).1 := by
      funext X
      simp only [S1, S2, bitS]
      rw [show q + 1 - (m + 1) = q - m by omega, Sg, show q - m + 1 = q + 1 - m by omega]
      rfl
    have e2 : S2 q (m + 1) = fun X => (dx (bitS q (2 * (q - m) + 1) X, bitS q (2 * (q - m)) X)
        (S1 q m X, S2 q m X)).2 := by
      funext X
      simp only [S1, S2, bitS]
      rw [show q + 1 - (m + 1) = q - m by omega, Sg, show q - m + 1 = q + 1 - m by omega]
      rfl
    refine relax (seq ih hx) le_rfl ?_ (by omega)
    rintro f ⟨t, ht, hf⟩
    rcases Nat.lt_or_ge t (m + 1) with h | h
    · exact Or.inl ⟨t, by omega, hf⟩
    · have : t = m + 1 := by omega
      subst this
      right
      rcases hf with rfl | rfl
      · rw [e1]; exact Or.inl rfl
      · rw [e2]; exact Or.inr rfl

def Q1 (t : Nat) : Sig (NN q) := fun X => (Qr (bv q X) q t).1
def Q2 (t : Nat) : Sig (NN q) := fun X => (Qr (bv q X) q t).2

theorem qBuild (A : Set (Sig (NN q))) (hP : PfSet q (q + 1) ⊆ A) (hS : SgSet q (q + 1) ⊆ A) :
    Build A ({f | ∃ a ∈ List.range (q + 1), f = Q1 q a} ∪ {f | ∃ a ∈ List.range (q + 1), f = Q2 q a})
      ((q + 1) * 3 + (q + 1) * 3) := by
  have hp1 : ∀ t ≤ q + 1, P1 q t ∈ A := fun t ht => hP ⟨t, ht, Or.inl rfl⟩
  have hp2 : ∀ t ≤ q + 1, P2 q t ∈ A := fun t ht => hP ⟨t, ht, Or.inr rfl⟩
  have hs1 : ∀ t ≤ q + 1, S1 q t ∈ A := fun t ht => hS ⟨t, ht, Or.inl rfl⟩
  have hs2 : ∀ t ≤ q + 1, S2 q t ∈ A := fun t ht => hS ⟨t, ht, Or.inr rfl⟩
  refine par (relax (listBuild (List.range (q + 1)) (Q1 q) 3 (fun t ht => ?_)) le_rfl le_rfl (by simp))
    (relax (listBuild (List.range (q + 1)) (Q2 q) 3 (fun t ht => ?_)) le_rfl le_rfl (by simp))
  · have htq : t < q + 1 := List.mem_range.1 ht
    have e : Q1 q t = fun X => (P1 q t X && S2 q (q - t) X) || (P2 q t X && S1 q (q - t) X) := by
      funext X
      simp only [Q1, Qr, P1, P2, S1, S2]
      rw [show q + 1 - (q - t) = t + 1 by omega]
      rfl
    rw [e]
    exact and2orG (hp1 t (by omega)) (hs2 _ (by omega)) (hp2 t (by omega)) (hs1 _ (by omega))
  · have htq : t < q + 1 := List.mem_range.1 ht
    have e : Q2 q t = fun X => (P1 q t X && S1 q (q - t) X) || (P2 q t X && S2 q (q - t) X) := by
      funext X
      simp only [Q2, Qr, P1, P2, S1, S2]
      rw [show q + 1 - (q - t) = t + 1 by omega]
      rfl
    rw [e]
    exact and2orG (hp1 t (by omega)) (hs1 _ (by omega)) (hp2 t (by omega)) (hs2 _ (by omega))

def zP (t : Nat) : Sig (NN q) := fun X => (zR (bv q X) q t).1
def zN (t : Nat) : Sig (NN q) := fun X => (zR (bv q X) q t).2

theorem zBuild (A : Set (Sig (NN q))) (hbit : ∀ i < 2 * (q + 2), bitS q i ∈ A)
    (hQ : ∀ t ≤ q, Q1 q t ∈ A ∧ Q2 q t ∈ A) :
    Build A ({f | ∃ a ∈ List.range q, f = zP q a} ∪ {f | ∃ a ∈ List.range q, f = zN q a}) (q * 1 + q * 1) := by
  refine par (relax (listBuild (List.range q) (zP q) 1 (fun t ht => ?_)) le_rfl le_rfl (by simp))
    (relax (listBuild (List.range q) (zN q) 1 (fun t ht => ?_)) le_rfl le_rfl (by simp))
  · have htq : t < q := List.mem_range.1 ht
    have e : zP q t = Build049.or (bitS q (2 * t + 1)) (Q1 q t) := rfl
    rw [e]
    exact orG (hbit _ (by omega)) (hQ t (by omega)).1
  · have htq : t < q := List.mem_range.1 ht
    have e : zN q t = Build049.or (bitS q (2 * t)) (Q2 q t) := rfl
    rw [e]
    exact orG (hbit _ (by omega)) (hQ t (by omega)).2

theorem simW_length (gs : List Gate) : ∀ w : List (Bool × Bool), (simW gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [simW]
  | cons g gs ih =>
    intro w
    simp only [simW, List.foldl_cons] at ih ⊢
    rw [ih]; simp; omega

def SW (D : Circuit) (m : Nat) (X : Fin (NN q) → Bool) : List (Bool × Bool) :=
  simW (D.gates.take m) (w0 (bv q X) q)
def R1 (D : Circuit) (m i : Nat) : Sig (NN q) := fun X => ((SW q D m X).getD i dflt).1
def R2 (D : Circuit) (m i : Nat) : Sig (NN q) := fun X => ((SW q D m X).getD i dflt).2
def RSet (D : Circuit) (m : Nat) : Set (Sig (NN q)) := {f | ∃ i < q + 2 + m, f = R1 q D m i ∨ f = R2 q D m i}

theorem SW_length (D : Circuit) (m : Nat) (X : Fin (NN q) → Bool) (hm : m ≤ D.gates.length) :
    (SW q D m X).length = q + 2 + m := by
  simp only [SW]
  rw [simW_length]
  simp [w0, List.length_take]
  omega

theorem SW_succ (D : Circuit) (m : Nat) (X : Fin (NN q) → Bool) (hm : m < D.gates.length) :
    SW q D (m + 1) X = SW q D m X ++ [simStep (D.gates[m]) (SW q D m X)] := by
  simp only [SW, simW]
  rw [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some, List.foldl_append]
  rfl

theorem R_prefix (D : Circuit) (m i : Nat) (hm : m < D.gates.length) (hi : i < q + 2 + m) :
    R1 q D (m + 1) i = R1 q D m i ∧ R2 q D (m + 1) i = R2 q D m i := by
  constructor
  · funext X; simp only [R1]; rw [SW_succ q D m X hm, List.getD_append _ _ _ _ (by rw [SW_length q D m X (by omega)]; exact hi)]
  · funext X; simp only [R2]; rw [SW_succ q D m X hm, List.getD_append _ _ _ _ (by rw [SW_length q D m X (by omega)]; exact hi)]

theorem R_new (D : Circuit) (m : Nat) (hm : m < D.gates.length) :
    R1 q D (m + 1) (q + 2 + m) = (fun X => (simStep (D.gates[m]) (SW q D m X)).1) ∧
    R2 q D (m + 1) (q + 2 + m) = (fun X => (simStep (D.gates[m]) (SW q D m X)).2) := by
  constructor
  · funext X; simp only [R1]
    rw [SW_succ q D m X hm, List.getD_append_right _ _ _ _ (by rw [SW_length q D m X (by omega)])]
    rw [SW_length q D m X (by omega)]; simp
  · funext X; simp only [R2]
    rw [SW_succ q D m X hm, List.getD_append_right _ _ _ _ (by rw [SW_length q D m X (by omega)])]
    rw [SW_length q D m X (by omega)]; simp

theorem simBuild (D : Circuit) (hfan : FanInTwo D) (hrb : ReadsBack (q + 2) D) (A : Set (Sig (NN q)))
    (hinit : RSet q D 0 ⊆ A) : ∀ m, m ≤ D.gates.length → Build A (RSet q D m) (2 * m)
  | 0, _ => idle hinit
  | m + 1, hm => by
    have ih := simBuild D hfan hrb A hinit m (by omega)
    have hml : m < D.gates.length := by omega
    have hg := hfan (D.gates[m]) (List.getElem_mem hml)
    have hrd : ∀ i ∈ (D.gates[m]).inputs, i < q + 2 + m := by
      intro i hi
      have := hrb m hml i
      simp only [gateAt, List.getD_eq_getElem _ _ hml] at this
      exact this hi
    have hn := simStepBuild (A := A ∪ RSet q D m) (D.gates[m]) hg.1 hg.2 (SW q D m)
      (fun i hi => ⟨Or.inr ⟨i, hrd i hi, Or.inl rfl⟩, Or.inr ⟨i, hrd i hi, Or.inr rfl⟩⟩)
    refine relax (seq ih hn) le_rfl ?_ (by omega)
    rintro f ⟨i, hi, hf⟩
    rcases Nat.lt_or_ge i (q + 2 + m) with h | h
    · have hp := R_prefix q D m i hml h
      rcases hf with rfl | rfl
      · rw [hp.1]; exact Or.inl ⟨i, h, Or.inl rfl⟩
      · rw [hp.2]; exact Or.inl ⟨i, h, Or.inr rfl⟩
    · have : i = q + 2 + m := by omega
      subst this
      have hnw := R_new q D m hml
      rcases hf with rfl | rfl
      · rw [hnw.1]; exact Or.inr (Or.inl rfl)
      · rw [hnw.2]; exact Or.inr (Or.inr rfl)

theorem R0 (D : Circuit) (i : Nat) (hi : i < q + 2) :
    R1 q D 0 i = (if i < q then zP q i else if i = q then fls q else tru q) ∧
    R2 q D 0 i = (if i < q then zN q i else if i = q then tru q else fls q) := by
  have hw : ∀ X, (SW q D 0 X).getD i dflt = initR (bv q X) q i := by
    intro X
    simp only [SW, List.take_zero]
    rw [show simW [] (w0 (bv q X) q) = w0 (bv q X) q from rfl]
    rw [List.getD_eq_getElem _ _ (by simp [w0]; omega)]
    simp [w0]
  constructor
  · funext X; simp only [R1, hw, initR]
    split_ifs <;> rfl
  · funext X; simp only [R2, hw, initR]
    split_ifs <;> rfl

def colS (m : Nat) : Sig (NN q) := fun X => (List.range m).any (fun t => bv q X (2 * t) && bv q X (2 * t + 1))

theorem colBuild (A : Set (Sig (NN q))) (hfl : fls q ∈ A) (hbit : ∀ i < 2 * (q + 2), bitS q i ∈ A) :
    ∀ m, m ≤ q + 1 → Build A {colS q m} (2 * m)
  | 0, _ => by
    apply idle
    rintro f rfl
    have e : colS q 0 = fls q := by funext X; rfl
    rw [e]; exact hfl
  | m + 1, hm => by
    have ih := colBuild A hfl hbit m (by omega)
    have hn := orAndG (A := A ∪ {colS q m}) (a := colS q m) (b := bitS q (2 * m)) (c := bitS q (2 * m + 1))
      (Or.inr rfl) (Or.inl (hbit _ (by omega))) (Or.inl (hbit _ (by omega)))
    have e : colS q (m + 1) = fun X => colS q m X || (bitS q (2 * m) X && bitS q (2 * m + 1) X) := by
      funext X
      simp only [colS, bitS, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
    refine relax (seq ih hn) le_rfl ?_ (by omega)
    rintro f rfl
    rw [e]; exact Or.inr rfl

end Asm1274

namespace Asm1274

open Build049 NetBuild1274 Net1274 Sem1274
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

variable (q : Nat)

def pp : Nat := Nat.log2 (NN q) + 1
def net : List (Nat × Nat × Bool) := sortNet (pp q)
def LL : Nat := 2 ^ pp q
def st (l : Nat) : Sig (NN q) := if l < 2 * (q + 2) then bitS q l else fls q

theorem NN_lt_LL : NN q < LL q := Nat.lt_log2_self

def G0S (D : Circuit) : Sig (NN q) := fun X => colS q (q + 1) X || bitS q (2 * q + 3) X || R1 q D D.gates.length D.output X

def outS (D : Circuit) : Sig (NN q) := fun X =>
  runS (net q) (st q) (q + 2) X || (runS (net q) (st q) (q + 1) X && (G0S q D X || P1 q (q + 1) X))

def oddYS (j : Nat) : Sig (NN q) :=
  if j / 2 ≤ q then (if j % 2 = 1 then Q2 q (j / 2) else Q1 q (j / 2))
  else (if j % 2 = 0 then P1 q (q + 1) else tru q)

def HjS (D : Circuit) (j : Nat) : Sig (NN q) := fun X => G0S q D X || bitS q (partner j) X || oddYS q j X

def tapS (D : Circuit) (j : Nat) : Sig (NN q) := fun X =>
  cofS (q + 2) (net q) (st q) j X || (cofS (q + 1) (net q) (st q) j X && HjS q D j X)

def A1 : Set (Sig (NN q)) := Set.range (inS q) ∪ {tru q, fls q}
def A2 : Set (Sig (NN q)) := A1 q ∪ PfSet q (q + 1)
def A3 : Set (Sig (NN q)) := A2 q ∪ SgSet q (q + 1)
def QS : Set (Sig (NN q)) :=
  {f | ∃ a ∈ List.range (q + 1), f = Q1 q a} ∪ {f | ∃ a ∈ List.range (q + 1), f = Q2 q a}
def A4 : Set (Sig (NN q)) := A3 q ∪ QS q
def ZS : Set (Sig (NN q)) := {f | ∃ a ∈ List.range q, f = zP q a} ∪ {f | ∃ a ∈ List.range q, f = zN q a}
def A5 : Set (Sig (NN q)) := A4 q ∪ ZS q
def A6 (D : Circuit) : Set (Sig (NN q)) := A5 q ∪ RSet q D D.gates.length
def A7 (D : Circuit) : Set (Sig (NN q)) := A6 q D ∪ {colS q (q + 1)}
def A8 (D : Circuit) : Set (Sig (NN q)) := A7 q D ∪ {G0S q D}
def A9 (D : Circuit) : Set (Sig (NN q)) := A8 q D ∪ netOut (LL q) (q + 1) (q + 2) (net q) (st q)
def A10 (D : Circuit) : Set (Sig (NN q)) := A9 q D ∪ {outS q D}
def TS (D : Circuit) : Set (Sig (NN q)) := {f | ∃ a ∈ List.range (2 * (q + 2)), f = tapS q D a}

theorem bit1 : ∀ i < 2 * (q + 2), bitS q i ∈ A1 q := fun i hi => Or.inl (bitS_mem q i hi)
theorem tru1 : tru q ∈ A1 q := Or.inr (Or.inl rfl)
theorem fls1 : fls q ∈ A1 q := Or.inr (Or.inr rfl)

theorem s12 : A1 q ⊆ A2 q := Set.subset_union_left
theorem s23 : A2 q ⊆ A3 q := Set.subset_union_left
theorem s34 : A3 q ⊆ A4 q := Set.subset_union_left
theorem s45 : A4 q ⊆ A5 q := Set.subset_union_left
theorem s56 (D : Circuit) : A5 q ⊆ A6 q D := Set.subset_union_left
theorem s67 (D : Circuit) : A6 q D ⊆ A7 q D := Set.subset_union_left
theorem s78 (D : Circuit) : A7 q D ⊆ A8 q D := Set.subset_union_left
theorem s89 (D : Circuit) : A8 q D ⊆ A9 q D := Set.subset_union_left
theorem s910 (D : Circuit) : A9 q D ⊆ A10 q D := Set.subset_union_left

theorem s15 : A1 q ⊆ A5 q := (s45 q).trans' ((s34 q).trans' ((s23 q).trans' (s12 q)))
theorem s58 (D : Circuit) : A5 q ⊆ A8 q D := (s78 q D).trans' ((s67 q D).trans' (s56 q D))
theorem s18 (D : Circuit) : A1 q ⊆ A8 q D := (s58 q D).trans' (s15 q)
theorem s810 (D : Circuit) : A8 q D ⊆ A10 q D := (s910 q D).trans' (s89 q D)

theorem build_all (D : Circuit) (hfan : FanInTwo D) (hrb : ReadsBack (q + 2) D) (hout : D.output < q + 2 + D.size) :
    Build (Set.range (inS q)) ({tru q, fls q} ∪ (PfSet q (q + 1) ∪ (SgSet q (q + 1) ∪ (QS q ∪ (ZS q ∪
      (RSet q D D.gates.length ∪ ({colS q (q + 1)} ∪ ({G0S q D} ∪
      (netOut (LL q) (q + 1) (q + 2) (net q) (st q) ∪ ({outS q D} ∪ TS q D))))))))))
      (2 + (6 * (q + 1) + (6 * (q + 1) + (((q + 1) * 3 + (q + 1) * 3) + ((q * 1 + q * 1) +
        (2 * D.gates.length + (2 * (q + 1) + (2 + (10 * (net q).length + (3 + 2 * (q + 2) * 4)))))))))) := by
  have H1 : Build (Set.range (inS q)) {tru q, fls q} 2 := by
    rw [Set.insert_eq]; exact par (constG true) (constG false)
  have H2 : Build (A1 q) (PfSet q (q + 1)) (6 * (q + 1)) :=
    pfBuild q (A1 q) (tru1 q) (fls1 q) (bit1 q) (q + 1) le_rfl
  have H3 : Build (A2 q) (SgSet q (q + 1)) (6 * (q + 1)) :=
    sgBuild q (A2 q) (s12 q (tru1 q)) (s12 q (fls1 q)) (fun i hi => s12 q (bit1 q i hi)) (q + 1) le_rfl
  have H4 : Build (A3 q) (QS q) ((q + 1) * 3 + (q + 1) * 3) :=
    qBuild q (A3 q) ((s23 q).trans' Set.subset_union_right) Set.subset_union_right
  have hQ4 : ∀ t ≤ q, Q1 q t ∈ A4 q ∧ Q2 q t ∈ A4 q := fun t ht =>
    ⟨Or.inr (Or.inl ⟨t, List.mem_range.2 (by omega), rfl⟩), Or.inr (Or.inr ⟨t, List.mem_range.2 (by omega), rfl⟩)⟩
  have H5 : Build (A4 q) (ZS q) (q * 1 + q * 1) :=
    zBuild q (A4 q) (fun i hi => s34 q (s23 q (s12 q (bit1 q i hi)))) hQ4
  have hinit : RSet q D 0 ⊆ A5 q := by
    rintro f ⟨i, hi, hf⟩
    have h0 := R0 q D i (by omega)
    rcases hf with rfl | rfl
    · rw [h0.1]
      split_ifs with h1 h2
      · exact Or.inr (Or.inl ⟨i, List.mem_range.2 h1, rfl⟩)
      · exact s15 q (fls1 q)
      · exact s15 q (tru1 q)
    · rw [h0.2]
      split_ifs with h1 h2
      · exact Or.inr (Or.inr ⟨i, List.mem_range.2 h1, rfl⟩)
      · exact s15 q (tru1 q)
      · exact s15 q (fls1 q)
  have H6 : Build (A5 q) (RSet q D D.gates.length) (2 * D.gates.length) :=
    simBuild q D hfan hrb (A5 q) hinit D.gates.length le_rfl
  have H7 : Build (A6 q D) {colS q (q + 1)} (2 * (q + 1)) :=
    colBuild q (A6 q D) (s56 q D (s15 q (fls1 q))) (fun i hi => s56 q D (s15 q (bit1 q i hi))) (q + 1) le_rfl
  have hRout : R1 q D D.gates.length D.output ∈ A7 q D :=
    s67 q D (Or.inr ⟨D.output, by simpa [Circuit.size] using hout, Or.inl rfl⟩)
  have H8 : Build (A7 q D) {G0S q D} 2 :=
    or3G (Or.inr rfl) (s67 q D (s56 q D (s15 q (bit1 q _ (by omega))))) hRout
  have hst : ∀ l < LL q, st q l ∈ A8 q D := by
    intro l _
    unfold st
    split_ifs with h
    · exact s18 q D (bit1 q l h)
    · exact s18 q D (fls1 q)
  have hLL := NN_lt_LL q
  have H9 : Build (A8 q D) (netOut (LL q) (q + 1) (q + 2) (net q) (st q)) (10 * (net q).length) :=
    netBuild (LL q) (q + 1) (q + 2) (tru q) (fun _ => rfl) (by unfold NN at hLL; omega) (by unfold NN at hLL; omega)
      (net q) (A8 q D) (st q) (sortNet_mem (pp q)) (s18 q D (tru1 q)) hst
  have hP9 : P1 q (q + 1) ∈ A9 q D := s89 q D (s58 q D (s45 q (s34 q (s23 q (Or.inr ⟨q + 1, le_rfl, Or.inl rfl⟩)))))
  have H10 : Build (A9 q D) {outS q D} 3 := by
    have h1 := orG (A := A9 q D) (f := G0S q D) (g := P1 q (q + 1)) (s89 q D (Or.inr rfl)) hP9
    have h2 := orAndG (A := A9 q D ∪ {Build049.or (G0S q D) (P1 q (q + 1))})
      (a := runS (net q) (st q) (q + 2)) (b := runS (net q) (st q) (q + 1)) (c := Build049.or (G0S q D) (P1 q (q + 1)))
      (Or.inl (Or.inr (Or.inr (Or.inr rfl)))) (Or.inl (Or.inr (Or.inr (Or.inl rfl)))) (Or.inr rfl)
    exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl
  have H11 : Build (A10 q D) (TS q D) (2 * (q + 2) * 4) := by
    have h := listBuild (A := A10 q D) (List.range (2 * (q + 2))) (tapS q D) 4 (fun j hj => ?_)
    · exact relax h le_rfl le_rfl (by simp)
    have hj' : j < 2 * (q + 2) := List.mem_range.1 hj
    have hG : G0S q D ∈ A10 q D := s810 q D (Or.inr rfl)
    have hpb : bitS q (partner j) ∈ A10 q D := by
      apply s810 q D; apply s18 q D; apply bit1 q
      unfold partner; split_ifs <;> omega
    have hY : oddYS q j ∈ A10 q D := by
      unfold oddYS
      split_ifs with h1 h2 h3
      · exact s810 q D (s58 q D (s45 q (Or.inr (Or.inr ⟨j / 2, List.mem_range.2 (by omega), rfl⟩))))
      · exact s810 q D (s58 q D (s45 q (Or.inr (Or.inl ⟨j / 2, List.mem_range.2 (by omega), rfl⟩))))
      · exact s910 q D hP9
      · exact s810 q D (s18 q D (tru1 q))
    have h1 := or3G hG hpb hY
    have hc2 : cofS (q + 2) (net q) (st q) j ∈ A10 q D :=
      s910 q D (Or.inr (Or.inl ⟨j, by unfold NN at hLL; omega, Or.inr rfl⟩))
    have hc1 : cofS (q + 1) (net q) (st q) j ∈ A10 q D :=
      s910 q D (Or.inr (Or.inl ⟨j, by unfold NN at hLL; omega, Or.inl rfl⟩))
    have h2 := orAndG (A := A10 q D ∪ {fun X => G0S q D X || bitS q (partner j) X || oddYS q j X})
      (Or.inl hc2) (Or.inl hc1) (Or.inr rfl)
    exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl
  exact seq H1 (seq H2 (seq H3 (seq H4 (seq H5 (seq H6 (seq H7 (seq H8 (seq H9 (seq H10 H11)))))))))

end Asm1274

namespace Fin1274

open Build049 NetBuild1274 Net1274 Sem1274 Asm1274
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem extract (q : Nat) {B : Set (Sig (NN q))} {b : Nat} (H : Build (Set.range (inS q)) B b) :
    ∃ gs : List Gate, gs.length ≤ b ∧ ReadsBack (NN q) ⟨gs, 0⟩ ∧ Monotone2 ⟨gs, 0⟩ ∧
      ∀ a ∈ B, ∃ i < NN q + gs.length, ∀ X : Fin (NN q) → Bool,
        ((Circuit.mk gs 0).wires (List.ofFn X)).getD i false = a X := by
  have hs := GateBridge.start (F := (id : Sig (NN q) → Sig (NN q))) (inS q) (fun i x => rfl)
  obtain ⟨c, hc, gs, hlen, hr, hm, hw⟩ := H.run hs le_rfl
  refine ⟨gs, by omega, hr, hm, fun a ha => ?_⟩
  obtain ⟨i, hi, hv⟩ := hw a (Or.inr ha)
  exact ⟨i, by omega, hv⟩

theorem size_bound (q : Nat) (D : Circuit) :
    (2 + (6 * (q + 1) + (6 * (q + 1) + (((q + 1) * 3 + (q + 1) * 3) + ((q * 1 + q * 1) +
        (2 * D.gates.length + (2 * (q + 1) + (2 + (10 * (net q).length + (3 + 2 * (q + 2) * 4))))))))))
      ≤ 2 * D.size + 64 * (2 * (q + 2) + 2) * (Nat.log2 (2 * (q + 2) + 2) + 2) ^ 2 := by
  have hlen := sortNet_length (pp q)
  have h2L : 2 ^ Nat.log2 (2 * (q + 2) + 2) ≤ 2 * (q + 2) + 2 := Nat.log2_self_le (by omega)
  simp only [net, pp, NN] at hlen ⊢
  generalize Nat.log2 (2 * (q + 2) + 2) = L at hlen h2L ⊢
  generalize (sortNet (L + 1)).length = K at hlen ⊢
  have hA : (L + 1) * (L + 1 + 1) ≤ (L + 2) ^ 2 := by nlinarith
  have hB : 2 ^ (L + 1) ≤ 2 * (2 * (q + 2) + 2) := by rw [pow_succ]; omega
  have hAB := Nat.mul_le_mul hA hB
  have h4 : 4 ≤ (L + 2) ^ 2 := by nlinarith
  have hN4 : (2 * (q + 2) + 2) * 4 ≤ (2 * (q + 2) + 2) * (L + 2) ^ 2 := Nat.mul_le_mul_left _ h4
  have e1 : (L + 2) ^ 2 * (2 * (2 * (q + 2) + 2)) = 2 * ((2 * (q + 2) + 2) * (L + 2) ^ 2) := by ring
  have e2 : 64 * (2 * (q + 2) + 2) * (L + 2) ^ 2 = 64 * ((2 * (q + 2) + 2) * (L + 2) ^ 2) := by ring
  rw [e1] at hAB
  rw [e2]
  have hsz : D.size = D.gates.length := rfl
  rw [hsz]
  generalize (2 * (q + 2) + 2) * (L + 2) ^ 2 = Y at hAB hN4 ⊢
  generalize (L + 1) * (L + 1 + 1) * 2 ^ (L + 1) = Z at hlen hAB
  omega

def inpV (q : Nat) (x : Finset (Fin (2 * (q + 2)))) : Fin (NN q) → Bool := fun i =>
  if h : i.val < 2 * (q + 2) then decide ((⟨i.val, h⟩ : Fin (2 * (q + 2))) ∈ x)
  else decide (i.val = 2 * (q + 2) + 1)

theorem ofFn_inpV (q : Nat) (x : Finset (Fin (2 * (q + 2)))) (d : ∀ i : Fin (2 * (q + 2)), Decidable (i ∈ x)) :
    List.ofFn (inpV q x) = List.ofFn (fun i : Fin (2 * (q + 2)) => @decide (i ∈ x) (d i)) ++ [false, true] := by
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    simp only [inpV, Fin.coe_castLE]
    rw [dif_pos i.isLt]
    exact decide_eq_decide.2 Iff.rfl
  · simp [inpV, List.ofFn_succ]

theorem bv_inpV (q : Nat) (x : Finset (Fin (2 * (q + 2)))) : bv q (inpV q x) = bx q x := by
  funext i
  by_cases h : i < 2 * (q + 2) <;> simp [bv, bx, inpV, h]

theorem st_inpV (q : Nat) (x : Finset (Fin (2 * (q + 2)))) : (fun m => st q m (inpV q x)) = bx q x := by
  funext l
  unfold st
  split_ifs with h
  · simp [bitS, bv_inpV]
  · simp only [fls]; rw [bx_ge q x l (by omega)]

theorem LL_ge (q : Nat) : 2 * (q + 2) ≤ 2 ^ pp q := by
  have := NN_lt_LL q; unfold LL NN at this; omega

theorem run_thr (q : Nat) (x : Finset (Fin (2 * (q + 2)))) (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 2 * (q + 2)) :
    runS (net q) (st q) (k - 1) (inpV q x) = decide (k ≤ x.card) := by
  simp only [runS, st_inpV]
  unfold net
  rw [sortNet_thr (pp q) _ k hk1 (le_trans hk (LL_ge q)), cnt_bx q x _ (LL_ge q)]

theorem cof_thr (q : Nat) (x : Finset (Fin (2 * (q + 2)))) (j : Fin (2 * (q + 2))) (k : Nat) (hk1 : 1 ≤ k)
    (hk : k ≤ 2 * (q + 2)) :
    cofS (k - 1) (net q) (st q) j.val (inpV q x) = decide (k ≤ (insert j x).card) := by
  simp only [cofS, cof, st_inpV]
  have e : Function.update (bx q x) j.val true = bx q (insert j x) := by
    funext i
    rw [bx_insert]
    by_cases h : i = j.val
    · subst h; simp
    · simp [Function.update, h]
  rw [e]
  unfold net
  rw [sortNet_thr (pp q) _ k hk1 (le_trans hk (LL_ge q)), cnt_bx q _ _ (LL_ge q)]

theorem G0S_inpV (q : Nat) (D : Circuit) (x : Finset (Fin (2 * (q + 2)))) :
    G0S q D (inpV q x) = G0 D q (bx q x) := by
  simp only [G0S, G0, colS, colB, bitS, R1, SW, FB, bv_inpV, List.take_length]

theorem outS_inpV (q : Nat) (D : Circuit) (x : Finset (Fin (2 * (q + 2)))) :
    outS q D (inpV q x) = (decide (q + 3 ≤ x.card) || (decide (q + 2 ≤ x.card) &&
      (G0 D q (bx q x) || oddT q (bx q x)))) := by
  have h1 := run_thr q x (q + 3) (by omega) (by omega)
  have h2 := run_thr q x (q + 2) (by omega) (by omega)
  simp only [show q + 3 - 1 = q + 2 by omega, show q + 2 - 1 = q + 1 by omega] at h1 h2
  simp only [outS, h1, h2, G0S_inpV]
  simp [P1, oddT, bv_inpV]

theorem tapS_inpV (q : Nat) (D : Circuit) (x : Finset (Fin (2 * (q + 2)))) (j : Fin (2 * (q + 2))) :
    tapS q D j.val (inpV q x) = (decide (q + 3 ≤ (insert j x).card) || (decide (q + 2 ≤ (insert j x).card) &&
      Hj D q (bx q x) j.val)) := by
  have h1 := cof_thr q x j (q + 3) (by omega) (by omega)
  have h2 := cof_thr q x j (q + 2) (by omega) (by omega)
  simp only [show q + 3 - 1 = q + 2 by omega, show q + 2 - 1 = q + 1 by omega] at h1 h2
  have hY : oddYS q j.val (inpV q x) = oddY q (bx q x) j.val := by
    unfold oddYS oddY
    split_ifs <;> simp [Q1, Q2, P1, tru, oddT, bv_inpV]
  simp only [tapS, h1, h2, HjS, Hj, G0S_inpV, hY, bitS, bv_inpV]

theorem final (q : Nat) (D : Circuit) (hfan : FanInTwo D) (hrb : ReadsBack (q + 2) D)
    (hout : D.output < q + 2 + D.size) :
    ∃ C : Circuit, (FanInTwo C ∧ ReadsBack (2 * (q + 2) + 2) C ∧ C.output < 2 * (q + 2) + 2 + C.size) ∧
      Monotone2 C ∧ C.size ≤ 2 * D.size + 64 * (2 * (q + 2) + 2) * (Nat.log2 (2 * (q + 2) + 2) + 2) ^ 2 ∧
      (∀ x, C.eval (List.ofFn (inpV q x)) = outS q D (inpV q x)) ∧
      ∃ tap : Fin (2 * (q + 2)) → Fin (2 * (q + 2) + 2 + C.size), ∀ x j,
        (C.wires (List.ofFn (inpV q x))).getD (tap j).val false = tapS q D j.val (inpV q x) := by
  obtain ⟨gs, hlen, hr, hm, hw⟩ := extract q (build_all q D hfan hrb hout)
  obtain ⟨io, hio, hvo⟩ := hw (outS q D)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have ht : ∀ j : Fin (2 * (q + 2)), ∃ i < NN q + gs.length, ∀ X : Fin (NN q) → Bool,
      ((Circuit.mk gs 0).wires (List.ofFn X)).getD i false = tapS q D j.val X := fun j =>
    hw _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨j.val, List.mem_range.2 j.isLt, rfl⟩))))))))))
  choose ti hti htv using ht
  refine ⟨⟨gs, io⟩, ⟨?_, hr, hio⟩, hm, le_trans hlen (size_bound q D), fun x => hvo _,
    ⟨fun j => ⟨ti j, hti j⟩, fun x j => htv j _⟩⟩
  intro g hg
  have := hm g hg
  refine ⟨?_, this.2⟩
  have h1 := this.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
  tauto

theorem eq_decide_of (b : Bool) {P : Prop} {inst : Decidable P} (h : b = true ↔ P) : b = @decide P inst := by
  by_cases hp : P
  · rw [@decide_eq_true P inst hp]; exact h.2 hp
  · rw [@decide_eq_false P inst hp]; cases b
    · rfl
    · exact absurd (h.1 rfl) hp

theorem bad_card (q : Nat) (f : Finset (Fin q) → Bool) (y : Finset (Fin (2 * (q + 2))))
    (h : Bad q f (bx q y)) : y.card = q + 2 := by
  obtain ⟨⟨hex, h2, h3⟩, _, _⟩ := h
  rw [card_pairs]
  have hone : ∀ t ∈ Finset.range (q + 2), pc (bx q y) t = 1 := by
    intro t ht
    simp only [Finset.mem_range] at ht
    rcases Nat.lt_or_ge t (q + 1) with h | h
    · have he := hex t (by omega)
      unfold pc
      unfold Exact at he
      rw [he]
      cases bx q y (2 * t + 1) <;> rfl
    · have : t = q + 1 := by omega
      subst this
      unfold pc
      rw [show 2 * (q + 1) = 2 * q + 2 by ring, show 2 * q + 2 + 1 = 2 * q + 3 by ring, h2, h3]
      rfl
  rw [Finset.sum_congr rfl hone]
  simp

theorem val_iff (q : Nat) (f : Finset (Fin q) → Bool) (y : Finset (Fin (2 * (q + 2)))) (H : Bool)
    (hH : y.card = q + 2 → (H = true ↔ ¬ Bad q f (bx q y))) (P : Prop) {inst : Decidable P}
    (hP : P ↔ Bad q f (bx q y)) :
    ((decide (q + 3 ≤ y.card) || (decide (q + 2 ≤ y.card) && H)) = true) ↔
      (q + 2 ≤ @ite Nat P inst (q + 2 - 1) (min (q + 2) y.card)) := by
  by_cases hp : P
  · rw [@if_pos P inst hp]
    have hb := hP.1 hp
    have hc := bad_card q f y hb
    have hHf : H = false := by
      cases hh : H
      · rfl
      · exact absurd hb ((hH hc).1 hh)
    simp only [hc, hHf]
    simp
  · rw [@if_neg P inst hp]
    have hb : ¬ Bad q f (bx q y) := fun h => hp (hP.2 h)
    rcases Nat.lt_or_ge y.card (q + 2) with h | h
    · have h' : ¬ (q + 2 ≤ y.card) := by omega
      have h'' : ¬ (q + 3 ≤ y.card) := by omega
      simp [h', h'']
    · rcases Nat.lt_or_ge y.card (q + 3) with h2 | h2
      · have hc : y.card = q + 2 := by omega
        have hH' := (hH hc).2 hb
        simp [hc, hH']
      · have h3 : q + 3 ≤ y.card := h2
        simp [h3]
        try omega

theorem val_iff2 (q : Nat) (f : Finset (Fin q) → Bool) (y1 y2 : Finset (Fin (2 * (q + 2)))) (hy : y2 = y1)
    (H : Bool) (hH : y1.card = q + 2 → (H = true ↔ ¬ Bad q f (bx q y1))) (P : Prop) {inst : Decidable P}
    (hP : P ↔ Bad q f (bx q y2)) :
    ((decide (q + 3 ≤ y1.card) || (decide (q + 2 ≤ y1.card) && H)) = true) ↔
      (q + 2 ≤ @ite Nat P inst (q + 2 - 1) (min (q + 2) y2.card)) := by
  subst hy
  exact val_iff q f y2 H hH P hP

theorem bad_iff_gen (q : Nat) (f : Finset (Fin q) → Bool)
    {dE : ∀ (z : Finset (Fin q)) (i : Fin (2 * (q + 2))), Decidable (∃ t ∈ z, t.val = i.val / 2)}
    {dP : ∀ z : Finset (Fin q), DecidablePred (fun i : Fin (2 * (q + 2)) => i.val = 2 * q + 2 ∨
      (i.val / 2 < q ∧ i.val % 2 = @ite Nat (∃ t ∈ z, t.val = i.val / 2) (dE z i) 1 0) ∨
      (i.val / 2 = q ∧ i.val % 2 = z.card % 2))}
    (y : Finset (Fin (2 * (q + 2)))) :
    (∃ z, f z = false ∧ y = @Finset.filter (Fin (2 * (q + 2))) (fun i => i.val = 2 * q + 2 ∨
      (i.val / 2 < q ∧ i.val % 2 = @ite Nat (∃ t ∈ z, t.val = i.val / 2) (dE z i) 1 0) ∨
      (i.val / 2 = q ∧ i.val % 2 = z.card % 2)) (dP z) Finset.univ) ↔ Bad q f (bx q y) := by
  apply bad_iff q f _ _ y
  intro z i
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, CodeP]
  have key : (i.val % 2 = @ite Nat (∃ t ∈ z, t.val = i.val / 2) (dE z i) 1 0) ↔
      (i.val % 2 = 1 ↔ ∃ t ∈ z, t.val = i.val / 2) := by
    by_cases h : ∃ t ∈ z, t.val = i.val / 2
    · rw [@if_pos _ (dE z i) h]; simp [h]
    · rw [@if_neg _ (dE z i) h]; simp only [h, iff_false]; omega
  rw [key]

theorem insert_inst {m : Nat} (d : DecidableEq (Fin m)) (j : Fin m) (x : Finset (Fin m)) :
    @insert _ _ (@Finset.instInsert _ d) j x = @insert _ _ (@Finset.instInsert _ (instDecidableEqFin m)) j x := by
  have : d = instDecidableEqFin m := Subsingleton.elim _ _
  subst this
  rfl

end Fin1274

end PEqualNP.Outside.L_lib_1274_aux

theorem PEqualNP.Outside.L_lib_1274 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (q : Nat) (f : Finset (Fin q) → Bool),
  let r := q+2
  let n := 2*r
  let code := fun (z : Finset (Fin q)) => (Finset.univ : Finset (Fin n)).filter (fun i =>
    i.val = 2*q+2 ∨
    (i.val/2 < q ∧ i.val % 2 = (if ∃ t ∈ z, t.val = i.val/2 then 1 else 0)) ∨
    (i.val/2 = q ∧ i.val % 2 = z.card % 2))
  let R := fun (x : Finset (Fin n)) => if ∃ z, f z = false ∧ x = code z then r-1 else min r x.card
  let input := fun (m : Nat) (x : Finset (Fin m)) => List.ofFn (fun i : Fin m => decide (i ∈ x)) ++ [false,true]
  let valid := fun (m : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (m+2) C ∧ C.output < m+2+C.size
  let realizes := fun (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    valid q D ∧ ∀ z, D.eval (input q z) = f z
  ∀ D, realizes D → ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    valid n C ∧ PEqualNP.MetaComplexity.Monotone2 C ∧
    C.size ≤ 2*D.size + 64*(n+2)*(Nat.log2 (n+2)+2)^2 ∧
    (∀ x, C.eval (input n x) = decide (r ≤ R x)) ∧
    ∃ tap : Fin n → Fin (n+2+C.size), ∀ x j,
      (C.wires (input n x)).getD (tap j).val false = decide (r ≤ R (insert j x))) := by
  intro q f
  dsimp only
  intro D hD
  have hf : ∀ z : Finset (Fin q), D.eval (List.ofFn (fun i : Fin q => decide (i ∈ z)) ++ [false, true]) = f z := by
    intro z
    convert hD.2 z using 4
    funext i
    exact decide_eq_decide.2 Iff.rfl
  have hD' : ∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
    intro g hg
    have := (hD.1.1 g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  obtain ⟨C, hv, hm, hs, hmain, tap, htap⟩ := PEqualNP.Outside.L_lib_1274_aux.Fin1274.final q D hD.1.1 hD.1.2.1 hD.1.2.2
  refine ⟨C, hv, hm, hs, fun x => ?_, tap, fun x j => ?_⟩
  · refine ((congrArg C.eval (PEqualNP.Outside.L_lib_1274_aux.Fin1274.ofFn_inpV q x _).symm).trans (hmain x)).trans ?_
    rw [PEqualNP.Outside.L_lib_1274_aux.Fin1274.outS_inpV]
    apply PEqualNP.Outside.L_lib_1274_aux.Fin1274.eq_decide_of
    exact PEqualNP.Outside.L_lib_1274_aux.Fin1274.val_iff q f x _
      (fun hc => PEqualNP.Outside.L_lib_1274_aux.Sem1274.main_ok D q f hD' hf x hc) _ (PEqualNP.Outside.L_lib_1274_aux.Fin1274.bad_iff_gen q f x)
  · refine ((congrArg (fun L => (C.wires L).getD (tap j).val false) (PEqualNP.Outside.L_lib_1274_aux.Fin1274.ofFn_inpV q x _).symm).trans (htap x j)).trans ?_
    rw [PEqualNP.Outside.L_lib_1274_aux.Fin1274.tapS_inpV]
    have hyy := PEqualNP.Outside.L_lib_1274_aux.Fin1274.insert_inst (fun a b => Classical.propDecidable (a = b)) j x
    apply PEqualNP.Outside.L_lib_1274_aux.Fin1274.eq_decide_of
    exact PEqualNP.Outside.L_lib_1274_aux.Fin1274.val_iff2 q f (@insert _ _ (@Finset.instInsert _ (instDecidableEqFin _)) j x) _ hyy
      (PEqualNP.Outside.L_lib_1274_aux.Sem1274.Hj D q (PEqualNP.Outside.L_lib_1274_aux.Sem1274.bx q x) j.val) (PEqualNP.Outside.L_lib_1274_aux.Sem1274.tap_ok D q f hD' hf x j) _
      (PEqualNP.Outside.L_lib_1274_aux.Fin1274.bad_iff_gen q f _)
