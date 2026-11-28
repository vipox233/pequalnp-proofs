import PEqualNP.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Order
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

namespace PEqualNP.Outside.L_lib_1291_aux

open PEqualNP.CircuitLowerBounds

theorem getD_chain (m : ℕ) (f : Fin m → Bool) (i : ℕ) :
    (List.ofFn f ++ [false, true]).getD i false =
      if h : i < m then f ⟨i, h⟩ else decide (i = m + 1) := by
  by_cases h : i < m
  · simp only [h, dite_true]
    rw [List.getD_append _ _ _ _ (by simp; exact h)]
    simp [List.getD_eq_getElem?_getD, h]
  · simp only [h, dite_false]
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    rcases Nat.lt_trichotomy (i - m) 1 with h1 | h1 | h1
    · have : i = m := by omega
      subst this; simp
    · have : i = m + 1 := by omega
      subst this; simp
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp; omega


namespace GateBridgeN

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

variable {α : Type*}

def Scheduled (n : Nat) (F : α → (Fin n → Bool) → Bool) (k nc : Nat) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ notCount ⟨gs, 0⟩ = nc ∧ ReadsBack n ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
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
    Scheduled n F 0 0 (Set.range input) := by
  refine ⟨[], rfl, rfl, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp [FanInTwo]
  · intro a ha
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    refine ⟨i.val, by simp, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, h i x]

theorem restrict {n k nc : Nat} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k nc S) (hsub : T ⊆ S) : Scheduled n F k nc T := by
  obtain ⟨gs, hs, hnc, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hnc, hr, hf, fun a ha => hw a (hsub ha)⟩

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

def isNotGate : GateOp → Nat
  | .not => 1
  | _ => 0

theorem push {n k nc : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    (h : Scheduled n F k nc S) (op : GateOp) (deps : List α) (out : α)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, F out x = op.eval (deps.map fun a => F a x)) :
    Scheduled n F (k + 1) (nc + isNotGate op) (insert out S) := by
  obtain ⟨gs, hgs, hnc, hr, hf, hw⟩ := h
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
  have hnc_new : notCount ⟨gs ++ [g], 0⟩ = nc + isNotGate op := by
    dsimp only [notCount] at hnc ⊢
    rw [List.filter_append, List.length_append, hnc, List.filter_cons, List.filter_nil]
    cases op <;> rfl
  refine ⟨gs ++ [g], by simp [hgs], hnc_new, ?_, ?_, ?_⟩
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

end GateBridgeN

namespace Build068

open PEqualNP.CircuitLowerBounds

variable {n : Nat}
abbrev Sig (n : Nat) := (Fin n → Bool) → Bool

def BuildN (A B : Set (Sig n)) (b nb : Nat) : Prop :=
  True ∧ (∀ {m mn S}, GateBridgeN.Scheduled n id m mn S → A ⊆ S →
    ∃ c ≤ b, ∃ cn ≤ nb, GateBridgeN.Scheduled n id (m + c) (mn + cn) (S ∪ B))

theorem BuildN.run {A B : Set (Sig n)} {b nb m mn S} (H : BuildN A B b nb)
    (HS : GateBridgeN.Scheduled n id m mn S) (hA : A ⊆ S) :
    ∃ c ≤ b, ∃ cn ≤ nb, GateBridgeN.Scheduled n id (m + c) (mn + cn) (S ∪ B) := H.2 HS hA

theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : BuildN A B 0 0 := by
  refine ⟨trivial, ?_⟩
  intro m mn S HS hA
  refine ⟨0, Nat.le_refl _, 0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

theorem relax {A B C D : Set (Sig n)} {b d nb nd : Nat}
    (H : BuildN A B b nb) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) (hn : nb ≤ nd) : BuildN C D d nd := by
  refine ⟨trivial, ?_⟩
  intro m mn S HS hC
  obtain ⟨c, hc, cn, hcn, HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c, hc.trans h, cn, hcn.trans hn, GateBridgeN.restrict HS' (Set.union_subset_union le_rfl hB)⟩

theorem seq {A B C : Set (Sig n)} {b c nb nc : Nat}
    (H : BuildN A B b nb) (J : BuildN (A ∪ B) C c nc) : BuildN A (B ∪ C) (b + c) (nb + nc) := by
  refine ⟨trivial, ?_⟩
  intro m mn S HS hA
  obtain ⟨d, hd, dn, hdn, K⟩ := H.run HS hA
  obtain ⟨e, he, en, hen, K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d + e, Nat.add_le_add hd he, dn + en, Nat.add_le_add hdn hen,
    by simpa [Nat.add_assoc, Set.union_assoc] using K'⟩

theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) :
    BuildN A {f} 1 (GateBridgeN.isNotGate op) := by
  refine ⟨trivial, ?_⟩
  intro m mn S HS hA
  refine ⟨1, le_rfl, GateBridgeN.isNotGate op, le_rfl, ?_⟩
  have h := GateBridgeN.push HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridgeN.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

def ban (f g : Sig n) : Sig n := fun x => f x && g x
def bor (f g : Sig n) : Sig n := fun x => f x || g x
def bnt (f : Sig n) : Sig n := fun x => !f x

theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    BuildN A {ban f g} 1 0 :=
  one .and [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) (ban f g) (by simp [GateOp.eval, ban])

theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    BuildN A {bor f g} 1 0 :=
  one .or [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) (bor f g) (by simp [GateOp.eval, bor])

theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : BuildN A {bnt f} 1 1 :=
  one .not [f] (by simp) (by simp) (by simpa using hf) (bnt f) (by simp [GateOp.eval, bnt])

theorem constG {A : Set (Sig n)} (b : Bool) : BuildN A {fun _ => b} 1 0 := by
  cases b
  · exact one .or [] (by simp) (by simp) (by simp) (fun _ => false) (by intro; rfl)
  · exact one .and [] (by simp) (by simp) (by simp) (fun _ => true) (by intro; rfl)
theorem listBuild {α : Type*} {A : Set (Sig n)} (xs : List α)
    (F : α → Sig n) (c cn : Nat) (H : ∀ a ∈ xs, BuildN A {F a} c cn) :
    BuildN A {f | ∃ a ∈ xs, f = F a} (xs.length * c) (xs.length * cn) := by
  induction xs with
  | nil =>
    exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp) (by simp)
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ {F a}) Set.subset_union_left le_rfl le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ ?_ ?_
    · rintro f ⟨b, hb, rfl⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr ⟨b, hb, rfl⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]

theorem listBuildVar {α : Type*} {A : Set (Sig n)} (xs : List α)
    (F : α → Sig n) (cost : α → Nat) (H : ∀ a ∈ xs, BuildN A {F a} (cost a) 0) :
    BuildN A {f | ∃ a ∈ xs, f = F a} (xs.map cost).sum 0 := by
  induction xs with
  | nil =>
    exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp) (by simp)
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ {F a}) Set.subset_union_left le_rfl le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ (by simp) (by simp)
    rintro f ⟨b, hb, rfl⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Or.inl rfl
    · exact Or.inr ⟨b, hb, rfl⟩

theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c cn : Nat)
    (H : ∀ i, BuildN A {F i} c cn) : BuildN A (Set.range F) (k * c) (k * cn) := by
  have h := listBuild (List.finRange k) F c cn (fun i _ => H i)
  rw [List.length_finRange] at h
  refine relax h le_rfl ?_ le_rfl le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, List.mem_finRange i, rfl⟩

def foldAndList (base : Sig n) : List (Sig n) → Sig n
  | [] => base
  | f :: fs => ban f (foldAndList base fs)

theorem foldAndList_eval (base : Sig n) (l : List (Sig n)) (z : Fin n → Bool) :
    foldAndList base l z = (base z && l.all (fun f => f z)) := by
  induction l with
  | nil => simp [foldAndList]
  | cons f fs ih =>
    simp only [foldAndList, ban, ih, List.all_cons]
    cases base z <;> cases f z <;> simp

theorem build_foldAndList {A : Set (Sig n)} (base : Sig n) (l : List (Sig n))
    (hbase : base ∈ A) (hl : ∀ f ∈ l, f ∈ A) :
    BuildN A {foldAndList base l} l.length 0 := by
  induction l with
  | nil =>
    exact idle (by intro g hg; rcases Set.mem_singleton_iff.mp hg with rfl; exact hbase)
  | cons f fs ih =>
    have h1 := ih (fun g hg => hl g (List.mem_cons_of_mem f hg))
    have h2 : BuildN (A ∪ {foldAndList base fs}) {ban f (foldAndList base fs)} 1 0 :=
      andG (Or.inl (hl f List.mem_cons_self)) (Or.inr rfl)
    refine relax (seq h1 h2) le_rfl ?_ (by simp) (by simp)
    intro g hg
    exact Or.inr hg

def foldOrList (base : Sig n) : List (Sig n) → Sig n
  | [] => base
  | f :: fs => bor f (foldOrList base fs)

theorem foldOrList_eval (base : Sig n) (l : List (Sig n)) (z : Fin n → Bool) :
    foldOrList base l z = (base z || l.any (fun f => f z)) := by
  induction l with
  | nil => simp [foldOrList]
  | cons f fs ih =>
    simp only [foldOrList, bor, ih, List.any_cons]
    cases base z <;> cases f z <;> simp

theorem build_foldOrList {A : Set (Sig n)} (base : Sig n) (l : List (Sig n))
    (hbase : base ∈ A) (hl : ∀ f ∈ l, f ∈ A) :
    BuildN A {foldOrList base l} l.length 0 := by
  induction l with
  | nil =>
    exact idle (by intro g hg; rcases Set.mem_singleton_iff.mp hg with rfl; exact hbase)
  | cons f fs ih =>
    have h1 := ih (fun g hg => hl g (List.mem_cons_of_mem f hg))
    have h2 : BuildN (A ∪ {foldOrList base fs}) {bor f (foldOrList base fs)} 1 0 :=
      orG (Or.inl (hl f List.mem_cons_self)) (Or.inr rfl)
    refine relax (seq h1 h2) le_rfl ?_ (by simp) (by simp)
    intro g hg
    exact Or.inr hg

end Build068

namespace Construct

open Build068 PEqualNP.CircuitLowerBounds

variable {n : Nat}

theorem step2 {A : Set (Sig n)} {f g h : Sig n} (hf : f ∈ A) (hg : g ∈ A) (hh : h ∈ A) :
    BuildN A {bor h (ban f g)} 2 0 := by
  have h1 := andG hf hg
  have h2 := orG (A := A ∪ {ban f g}) (Or.inl hh) (Or.inr rfl)
  exact relax (seq h1 h2) le_rfl (by intro z hz; exact Or.inr hz) le_rfl le_rfl

theorem rangeBuild {A : Set (Sig n)} (k : Nat) (F : Nat → Sig n) (c cn : Nat)
    (H : ∀ i < k, BuildN A {F i} c cn) :
    BuildN A {f | ∃ i < k, f = F i} (k * c) (k * cn) := by
  have h := listBuild (List.range k) F c cn (fun i hi => H i (List.mem_range.mp hi))
  rw [List.length_range] at h
  refine relax h le_rfl ?_ le_rfl le_rfl
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, List.mem_range.mpr hi, rfl⟩

def T : Nat → Nat
  | 0 => 0
  | r + 1 => T r + 4 * 2 ^ r - 3

theorem T_add (r : Nat) : T r + 3 * r = 4 * (2 ^ r - 1) := by
  induction r with
  | zero => simp [T]
  | succ r ih =>
    simp only [T]
    have : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    rw [pow_succ]
    omega

def Srt (L : Nat) (u : Nat → Sig n) (x : Fin n → Bool) : Prop :=
  ∀ i j, i ≤ j → j < L → u i x = true → u j x = true

theorem inverter : ∀ (r : Nat) (A : Set (Sig n)) (u : Nat → Sig n),
    (∀ i < 2 ^ r - 1, u i ∈ A) →
    ∃ nu : Nat → Sig n, BuildN A {f | ∃ i < 2 ^ r - 1, f = nu i} (T r) r ∧
      ∀ x, Srt (2 ^ r - 1) u x → ∀ i < 2 ^ r - 1, nu i x = !(u i x) := by
  intro r
  induction r with
  | zero =>
    intro A u _
    refine ⟨u, relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by
      rintro f ⟨i, hi, _⟩; simp at hi) le_rfl le_rfl, ?_⟩
    intro x _ i hi; simp at hi
  | succ r ih =>
    intro A u hu
    set k := 2 ^ r - 1 with hk
    have hpow : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    have hlen : 2 ^ (r + 1) - 1 = 2 * k + 1 := by rw [pow_succ]; omega
    rw [hlen] at hu ⊢
    let nm : Sig n := bnt (u k)
    have H1 : BuildN A {nm} 1 1 := notG (hu k (by omega))
    let A1 := A ∪ {nm}
    let fd : Nat → Sig n := fun i => bor (u i) (ban (u (k + 1 + i)) nm)
    have H2 : BuildN A1 {f | ∃ i < k, f = fd i} (k * 2) (k * 0) :=
      rangeBuild k fd 2 0 (fun i hi => step2 (Or.inl (hu _ (by omega))) (Or.inr rfl)
        (Or.inl (hu _ (by omega))))
    let A2 := A1 ∪ {f | ∃ i < k, f = fd i}
    obtain ⟨nf, H3, hnf⟩ := ih A2 fd (fun i hi => Or.inr ⟨i, hi, rfl⟩)
    let A3 := A2 ∪ {f | ∃ i < k, f = nf i}
    let nu : Nat → Sig n := fun i =>
      if i < k then bor (nf i) nm else if i = k then nm else ban (nf (i - k - 1)) nm
    have H4 : BuildN A3 {f | ∃ i < k, f = bor (nf i) nm} (k * 1) (k * 0) :=
      rangeBuild k _ 1 0 (fun i hi => orG (Or.inr ⟨i, hi, rfl⟩) (Or.inl (Or.inl (Or.inr rfl))))
    have H5 : BuildN A3 {f | ∃ i < k, f = ban (nf i) nm} (k * 1) (k * 0) :=
      rangeBuild k _ 1 0 (fun i hi => andG (Or.inr ⟨i, hi, rfl⟩) (Or.inl (Or.inl (Or.inr rfl))))
    have H45 := seq H4 (relax H5 (C := A3 ∪ {f | ∃ i < k, f = bor (nf i) nm})
      Set.subset_union_left le_rfl le_rfl le_rfl)
    have Hall := seq (seq (seq H1 H2) (relax H3 (C := A ∪ ({nm} ∪ {f | ∃ i < k, f = fd i}))
      (fun z hz => by simp only [A1, A2, Set.mem_union] at hz ⊢; tauto) le_rfl le_rfl le_rfl))
      (relax H45 (C := A ∪ ({nm} ∪ {f | ∃ i < k, f = fd i} ∪ {f | ∃ i < k, f = nf i}))
      (fun z hz => by simp only [A1, A2, A3, Set.mem_union] at hz ⊢; tauto) le_rfl le_rfl le_rfl)
    refine ⟨nu, relax Hall le_rfl ?_ ?_ ?_, ?_⟩
    · rintro f ⟨i, hi, rfl⟩
      simp only [nu]
      split_ifs with h1 h2
      · exact Or.inr (Or.inl ⟨i, h1, rfl⟩)
      · exact Or.inl (Or.inl (Or.inl rfl))
      · exact Or.inr (Or.inr ⟨i - k - 1, by omega, rfl⟩)
    · simp only [T]; omega
    · omega
    · intro x hs i hi
      have hsk : ∀ j, j < 2 * k + 1 → k ≤ j → u k x = true → u j x = true :=
        fun j hj hkj h => hs k j hkj hj h
      cases hmid : u k x
      ·
        have hlow : ∀ j < k, u j x = false := by
          intro j hj
          cases hj' : u j x
          · rfl
          · have := hs j k (by omega) (by omega) hj'; rw [hmid] at this; exact this.symm
        have hnmx : nm x = true := by simp [nm, bnt, hmid]
        have hfd : ∀ j < k, fd j x = u (k + 1 + j) x := by
          intro j hj; simp [fd, bor, ban, hnmx, hlow j hj]
        have hsrt : Srt k fd x := by
          intro a b hab hb ha
          rw [hfd a (by omega)] at ha; rw [hfd b hb]
          exact hs _ _ (by omega) (by omega) ha
        have hnf' := hnf x hsrt
        simp only [nu]
        split_ifs with h1 h2
        · simp [bor, hnmx, hlow i h1]
        · subst h2; simp [nm, bnt]
        · simp only [ban, hnmx, Bool.and_true]
          rw [hnf' _ (by omega), hfd _ (by omega)]
          congr 3; omega
      · have hnmx : nm x = false := by simp [nm, bnt, hmid]
        have hfd : ∀ j < k, fd j x = u j x := by
          intro j hj; simp [fd, bor, ban, hnmx]
        have hsrt : Srt k fd x := by
          intro a b hab hb ha
          rw [hfd a (by omega)] at ha; rw [hfd b hb]
          exact hs _ _ hab (by omega) ha
        have hnf' := hnf x hsrt
        simp only [nu]
        split_ifs with h1 h2
        · simp only [bor, hnmx, Bool.or_false]; rw [hnf' i h1, hfd i h1]
        · subst h2; simp [nm, bnt]
        · simp only [ban, hnmx, Bool.and_false]
          rw [hsk i hi (by omega) hmid]; rfl

end Construct

namespace InversionRank

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (w : List Bool) := gs.foldl
  (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

def tick (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def code : List Gate → List Bool → List Bool
  | [], _ => []
  | g::gs, w =>
    let a := tick w g
    match g.op with
    | .not => (g.op.eval (g.inputs.map fun i => w.getD i false)) :: code gs a
    | _ => code gs a

def mark (g : Gate) : Bool := match g.op with | .not => true | _ => false

theorem code_len (gs : List Gate) (w : List Bool) :
    (code gs w).length = (gs.filter mark).length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    cases h : g.op <;> simp [code,h,mark,ih]

def ordered (x y : List Bool) :=
  x.length=y.length ∧ ∀ i, x.getD i false=true → y.getD i false=true

theorem extend_order {x y : List Bool} (w : ordered x y) {a b : Bool}
    (ab : a=true → b=true) : ordered (x++[a]) (y++[b]) := by
  refine ⟨by simp [w.1],?_⟩
  intro i
  by_cases before : i < x.length
  · rw [List.getD_append _ _ _ _ before,List.getD_append _ _ _ _ (w.1 ▸ before)]
    exact w.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by rw [←w.1]; omega),←w.1]
    cases i-x.length with
    | zero => simpa using ab
    | succ _ => simp

theorem output_order {gs : List Gate}
    (ops : ∀ g∈gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    {x y : List Bool} (w : ordered x y) (same : code gs x=code gs y) :
    ordered (run gs x) (run gs y) := by
  induction gs generalizing x y with
  | nil => exact w
  | cons g gs ih =>
    have rest (a) (ha : a∈gs) := ops a (List.mem_cons_of_mem _ ha)
    change ordered (run gs (tick x g)) (run gs (tick y g))
    have casesG := ops g (List.mem_cons_self ..)
    rcases casesG with h|h|h
    · apply ih rest (extend_order w ?_) (by simpa only [code,tick,h] using same)
      simp only [h,GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,and_imp]
      intro all z i hi ei
      subst z
      exact w.2 i (all _ _ hi rfl)
    · apply ih rest (extend_order w ?_) (by simpa only [code,tick,h] using same)
      simp only [h,GateOp.eval,List.any_eq_true,List.mem_map]
      rintro ⟨z,⟨i,hi,rfl⟩,yes⟩
      exact ⟨_,⟨i,hi,rfl⟩,w.2 i yes⟩
    · simp only [code,h,List.cons.injEq] at same
      apply ih rest (extend_order w ?_) same.2
      rw [h]
      exact fun e => same.1.symm.trans e

theorem input_order {n : Nat} {x y : Fin n → Bool} (xy : ∀ i, x i=true → y i=true) :
    ordered (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases h : i<n
  · rw [List.getD_append _ _ _ _ (by simpa),List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h] using xy ⟨i,h⟩
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h)]
    simp
def driverNumber : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 0 else 2^bs.length) + driverNumber bs

theorem driver_bound (l : List Bool) : driverNumber l < 2^l.length := by
  induction l with
  | nil => decide
  | cons b bs ih => cases b <;> simp [driverNumber,pow_succ] <;> omega

theorem driver_injective {a b : List Bool} (len : a.length=b.length)
    (num : driverNumber a=driverNumber b) : a=b := by
  induction a generalizing b with
  | nil => simpa using len.symm
  | cons x xs ih =>
    cases b with
    | nil => simp at len
    | cons y ys =>
      have sz : xs.length=ys.length := by simpa using len
      have h₁ := driver_bound xs
      have h₂ := driver_bound ys
      rw [sz] at h₁
      cases x <;> cases y <;> simp [driverNumber,sz] at num ⊢ <;> first | exact ih sz num | omega

theorem driver_mono (gs : List Gate) (ops : ∀ g∈gs, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    {a b : List Bool} (ab : ordered a b) :
    driverNumber (code gs a) ≤ driverNumber (code gs b) := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    have tailops := fun h (hh : h∈gs) => ops h (by simp [hh])
    have oneops : ∀ u ∈ [g], u.op=.and ∨ u.op=.or ∨ u.op=.not := by
      simpa using ops g (by simp)
    have growth (same : code [g] a=code [g] b) : ordered (tick a g) (tick b g) :=
      output_order oneops ab same
    rcases ops g (by simp) with eq|eq|eq
    · simp only [code,eq]
      exact ih tailops (growth (by simp [code,eq]))
    · simp only [code,eq]
      exact ih tailops (growth (by simp [code,eq]))
    · let out (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
      have anti : out b=true → out a=true := by
        cases inp : g.inputs with
        | nil => simp [out,eq,inp,GateOp.eval]
        | cons i more =>
          simp only [out,eq,inp,GateOp.eval,List.map_cons,List.headD_cons,Bool.not_eq_true']
          intro bz
          cases az : a.getD i false
          · rfl
          · have := ab.2 i az
            simp_all
      have len : (code gs (tick a g)).length=(code gs (tick b g)).length := by simp [code_len]
      change driverNumber (code (g::gs) a) ≤ driverNumber (code (g::gs) b)
      simp only [code,eq]
      rw [←eq]
      change driverNumber (out a :: code gs (tick a g)) ≤ driverNumber (out b :: code gs (tick b g))
      by_cases same : out a=out b
      · have next : ordered (tick a g) (tick b g) := extend_order ab (by change out a=true → out b=true; rw [same]; exact id)
        simpa only [driverNumber,same,len,Nat.add_le_add_iff_left] using
          Nat.add_le_add_left (ih tailops next) (if out b then 0 else 2^(code gs (tick b g)).length)
      · have zero : out b=false := by cases hb : out b <;> simp_all
        have one : out a=true := by cases ha : out a <;> simp_all
        have bound := driver_bound (code gs (tick a g))
        rw [len] at bound
        simp only [driverNumber,one,zero,Bool.false_eq_true,ite_false,ite_true,Nat.zero_add]
        omega

end InversionRank

theorem filter_mark_eq_notCount (C : Circuit) :
    (C.gates.filter InversionRank.mark).length = PEqualNP.NotBracket.notCount C := by
  dsimp only [PEqualNP.NotBracket.notCount]
  congr 1
  apply List.filter_congr
  intro g _
  rcases g with ⟨op, inp⟩
  cases op <;> simp [InversionRank.mark]

theorem lower_dir (n m r : Nat) (x : Fin m → Finset (Fin n)) (pin : Fin m → Option Bool) (c : Bool)
    (C : Circuit) (p : Nat)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hnc : PEqualNP.NotBracket.notCount C ≤ r)
    (hemp_out : (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ (∅ : Finset (Fin n)))) ++ [false, true])).getD C.output false = c)
    (hemp_p : (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ (∅ : Finset (Fin n)))) ++ [false, true])).getD p false = !c)
    (hpin : ∀ i,
      (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ x i)) ++ [false, true])).getD p false =
        !((C.wires (List.ofFn (fun k : Fin n => decide (k ∈ x i)) ++ [false, true])).getD C.output false) ∧
      ∀ v, pin i = some v →
        (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ x i)) ++ [false, true])).getD C.output false = v) :
    (∀ i, x i = ∅ → pin i ≠ some (!c)) ∧
    ¬ (∃ u : Fin (2 ^ r) → Fin m,
      (∀ j, pin (u j) = some (if j.val % 2 = 0 then !c else c)) ∧
      ∀ i j, i.val + 1 = j.val → x (u i) ⊆ x (u j)) := by
  constructor
  · intro i hxi hp
    have h1 := (hpin i).2 (!c) hp
    rw [hxi, hemp_out] at h1
    cases c <;> simp at h1
  · rintro ⟨u, hupin, husub⟩
    let y : Nat → Finset (Fin n) := fun t =>
      if h0 : t = 0 then ∅ else if ht : t - 1 < 2 ^ r then x (u ⟨t - 1, ht⟩) else ∅
    let w : Nat → List Bool := fun t =>
      List.ofFn (fun k : Fin n => decide (k ∈ y t)) ++ [false, true]
    have hsub : ∀ t < 2 ^ r, y t ⊆ y (t + 1) := by
      intro t ht
      by_cases h0 : t = 0
      · subst h0
        simp only [y, dite_true, Finset.empty_subset]
      · have ht1 : t - 1 < 2 ^ r := by omega
        have ht2 : t + 1 ≠ 0 := by omega
        have ht3 : t + 1 - 1 < 2 ^ r := by omega
        simp only [y, h0, ht1, ht2, ht3, dite_false, dite_true]
        exact husub ⟨t - 1, ht1⟩ ⟨t + 1 - 1, ht3⟩ (by dsimp; omega)
    have hval : ∀ t ≤ 2 ^ r,
        (C.wires (w t)).getD C.output false = (if t % 2 = 0 then c else !c) ∧
        (C.wires (w t)).getD p false = (if t % 2 = 0 then !c else c) := by
      intro t ht
      by_cases h0 : t = 0
      · subst h0
        simp only [w, y, dite_true, Nat.zero_mod, ite_true]
        exact ⟨hemp_out, hemp_p⟩
      · have ht1 : t - 1 < 2 ^ r := by omega
        have hyt : y t = x (u ⟨t - 1, ht1⟩) := by simp [y, h0, ht1]
        have hwt : w t = List.ofFn (fun k : Fin n => decide (k ∈ x (u ⟨t - 1, ht1⟩))) ++ [false, true] := by
          simp only [w, hyt]
        rw [hwt]
        have hp1 := (hpin (u ⟨t - 1, ht1⟩)).2 _ (hupin ⟨t - 1, ht1⟩)
        have hp2 := (hpin (u ⟨t - 1, ht1⟩)).1
        by_cases hev : t % 2 = 0
        · have hodd : ¬ ((t - 1) % 2 = 0) := by omega
          simp only [hodd, ite_false] at hp1
          rw [hp1] at hp2
          simp only [hev, ite_true]
          exact ⟨hp1, hp2⟩
        · have hev1 : (t - 1) % 2 = 0 := by omega
          simp only [hev1, ite_true] at hp1
          rw [hp1, Bool.not_not] at hp2
          simp only [hev, ite_false]
          exact ⟨hp1, hp2⟩
    have hops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      intro g hg
      have hmem := (hfan g hg).1
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
    have hstep : ∀ t < 2 ^ r,
        InversionRank.driverNumber (InversionRank.code C.gates (w t)) <
        InversionRank.driverNumber (InversionRank.code C.gates (w (t + 1))) := by
      intro t ht
      have hord : InversionRank.ordered (w t) (w (t + 1)) := by
        apply InversionRank.input_order
        intro k hk
        simp only [decide_eq_true_eq] at hk ⊢
        exact hsub t ht hk
      have hle := InversionRank.driver_mono C.gates hops hord
      refine Nat.lt_of_le_of_ne hle ?_
      intro heq
      have hlen : (InversionRank.code C.gates (w t)).length =
          (InversionRank.code C.gates (w (t + 1))).length := by
        simp [InversionRank.code_len]
      have hcode := InversionRank.driver_injective hlen heq
      have hout := InversionRank.output_order hops hord hcode
      have hv1 := hval t (by omega)
      have hv2 := hval (t + 1) (by omega)
      have h1 := hout.2 C.output
      have h2 := hout.2 p
      change (C.wires (w t)).getD C.output false = true →
        (C.wires (w (t + 1))).getD C.output false = true at h1
      change (C.wires (w t)).getD p false = true →
        (C.wires (w (t + 1))).getD p false = true at h2
      rw [hv1.1, hv2.1] at h1
      rw [hv1.2, hv2.2] at h2
      by_cases hev : t % 2 = 0
      · have hodd : ¬ ((t + 1) % 2 = 0) := by omega
        simp only [hev, hodd, ite_true, ite_false] at h1 h2
        cases c <;> simp at h1 h2
      · have hev2 : (t + 1) % 2 = 0 := by omega
        simp only [hev, hev2, ite_true, ite_false] at h1 h2
        cases c <;> simp at h1 h2
    have hlb : ∀ t ≤ 2 ^ r, t ≤ InversionRank.driverNumber (InversionRank.code C.gates (w t)) := by
      intro t ht
      induction t with
      | zero => exact Nat.zero_le _
      | succ t ih =>
        have h1 := ih (by omega)
        have h2 := hstep t (by omega)
        omega
    have hge := hlb (2 ^ r) le_rfl
    have hlt := InversionRank.driver_bound (InversionRank.code C.gates (w (2 ^ r)))
    rw [InversionRank.code_len, filter_mark_eq_notCount] at hlt
    have hpow : 2 ^ PEqualNP.NotBracket.notCount C ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hnc
    omega

namespace RankData

open Classical

def ChainAt {n m : Nat} (x : Fin m → Finset (Fin n)) (pin : Fin m → Option Bool) (c : Bool)
    (k : Nat) (i : Fin m) : Prop :=
  ∃ u : Fin (k + 1) → Fin m,
    u ⟨k, Nat.lt_succ_self k⟩ = i ∧
    (∀ j, pin (u j) = some (if j.val % 2 = 0 then !c else c)) ∧
    ∀ a b, a.val + 1 = b.val → x (u a) ⊆ x (u b)

theorem chainAt_strict {n m : Nat} {x : Fin m → Finset (Fin n)} {pin : Fin m → Option Bool}
    {c : Bool} (hx : Function.Injective x) {k : Nat}
    (u : Fin (k + 1) → Fin m)
    (hp : ∀ j, pin (u j) = some (if j.val % 2 = 0 then !c else c))
    (hs : ∀ a b, a.val + 1 = b.val → x (u a) ⊆ x (u b)) :
    ∀ a b : Fin (k + 1), a < b → x (u a) ⊂ x (u b) := by
  have hstep : ∀ (a b : Fin (k + 1)), a.val + 1 = b.val → x (u a) ⊂ x (u b) := by
    intro a b hab
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hs a b hab, ?_⟩
    intro heq
    have hu : u a = u b := hx heq
    have hpa := hp a
    have hpb := hp b
    rw [hu] at hpa
    rw [hpa] at hpb
    by_cases ha : a.val % 2 = 0
    · have hb : ¬ (b.val % 2 = 0) := by omega
      simp only [ha, hb, ite_true, ite_false, Option.some.injEq] at hpb
      cases c <;> simp at hpb
    · have hb : b.val % 2 = 0 := by omega
      simp only [ha, hb, ite_true, ite_false, Option.some.injEq] at hpb
      cases c <;> simp at hpb
  intro a b hab
  have hd : ∃ d, b.val = a.val + (d + 1) := ⟨b.val - a.val - 1, by omega⟩
  obtain ⟨d, hd⟩ := hd
  induction d generalizing b with
  | zero => exact hstep a b (by omega)
  | succ d ih =>
    let mid : Fin (k + 1) := ⟨a.val + (d + 1), by omega⟩
    exact (ih mid (by show a.val < a.val + (d + 1); omega) rfl).trans (hstep mid b (by dsimp [mid]; omega))

theorem chainAt_lt_m {n m : Nat} {x : Fin m → Finset (Fin n)} {pin : Fin m → Option Bool}
    {c : Bool} (hx : Function.Injective x) {k : Nat} {i : Fin m}
    (hc : ChainAt x pin c k i) : k < m := by
  obtain ⟨u, _, hp, hs⟩ := hc
  have hu_inj : Function.Injective u := by
    intro a b hab
    rcases lt_trichotomy a b with h | h | h
    · exact False.elim ((chainAt_strict hx u hp hs a b h).ne (congrArg x hab))
    · exact h
    · exact False.elim ((chainAt_strict hx u hp hs b a h).ne (congrArg x hab.symm))
  have hcard := Fintype.card_le_of_injective u hu_inj
  simp only [Fintype.card_fin] at hcard
  omega

noncomputable def chainLen {n m : Nat} (x : Fin m → Finset (Fin n)) (pin : Fin m → Option Bool)
    (c : Bool) (i : Fin m) : Nat :=
  ((Finset.range m).filter (fun k => ChainAt x pin c k i)).sup (fun k => k + 1)

theorem chainLen_le_m {n m : Nat} (x : Fin m → Finset (Fin n)) (pin : Fin m → Option Bool)
    (c : Bool) (i : Fin m) : chainLen x pin c i ≤ m := by
  unfold chainLen
  apply Finset.sup_le
  intro k hk
  have hk' : k < m := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  omega

theorem chainLen_witness {n m : Nat} {x : Fin m → Finset (Fin n)} {pin : Fin m → Option Bool}
    {c : Bool} {i : Fin m} (h : 1 ≤ chainLen x pin c i) :
    ChainAt x pin c (chainLen x pin c i - 1) i := by
  unfold chainLen at h ⊢
  set S := (Finset.range m).filter (fun k => ChainAt x pin c k i)
  have hne : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp] at h
    simp at h
  obtain ⟨k, hk, hsup⟩ := Finset.exists_mem_eq_sup S hne (fun k => k + 1)
  have hkc : ChainAt x pin c k i := (Finset.mem_filter.mp hk).2
  have heq : S.sup (fun k => k + 1) - 1 = k := by rw [hsup]; omega
  rw [heq]
  exact hkc

theorem chainLen_lt_pow {n m r : Nat} {x : Fin m → Finset (Fin n)} {pin : Fin m → Option Bool}
    {c : Bool}
    (hgood2 : ¬ (∃ u : Fin (2 ^ r) → Fin m,
      (∀ j, pin (u j) = some (if j.val % 2 = 0 then !c else c)) ∧
      ∀ a b, a.val + 1 = b.val → x (u a) ⊆ x (u b)))
    (i : Fin m) : chainLen x pin c i < 2 ^ r := by
  by_contra hlt
  have hge : 2 ^ r ≤ chainLen x pin c i := Nat.le_of_not_lt hlt
  have hpow : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hpos : 1 ≤ chainLen x pin c i := by omega
  obtain ⟨u, _, hp, hs⟩ := chainLen_witness hpos
  apply hgood2
  refine ⟨fun j => u ⟨j.val, by omega⟩, ?_, ?_⟩
  · intro j
    exact hp ⟨j.val, by omega⟩
  · intro a b hab
    exact hs ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ hab

theorem chainLen_extend {n m : Nat} {x : Fin m → Finset (Fin n)} {pin : Fin m → Option Bool}
    {c : Bool} (hx : Function.Injective x) {k : Nat} {i j : Fin m}
    (hc : ChainAt x pin c k j) (hsub : x j ⊆ x i)
    (hpi : pin i = some (if (k + 1) % 2 = 0 then !c else c)) :
    k + 2 ≤ chainLen x pin c i := by
  obtain ⟨u, hlast, hp, hs⟩ := hc
  have hc' : ChainAt x pin c (k + 1) i := by
    let u' : Fin (k + 2) → Fin m := fun t => if h : t.val < k + 1 then u ⟨t.val, h⟩ else i
    refine ⟨u', ?_, ?_, ?_⟩
    · simp [u']
    · intro t
      by_cases ht : t.val < k + 1
      · simp only [u', ht, dite_true]
        exact hp ⟨t.val, ht⟩
      · have hteq : t.val = k + 1 := by omega
        have hut : u' t = i := by
          dsimp only [u']
          split_ifs
          · omega
          · rfl
        rw [hut, hteq]
        exact hpi
    · intro a b hab
      have ha : a.val < k + 1 := by omega
      by_cases hb : b.val < k + 1
      · simp only [u', ha, hb, dite_true]
        exact hs ⟨a.val, ha⟩ ⟨b.val, hb⟩ hab
      · have haeq : a.val = k := by omega
        simp only [u', ha, hb, dite_true, dite_false]
        have heq : (⟨a.val, ha⟩ : Fin (k + 1)) = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext haeq
        rw [heq, hlast]
        exact hsub
  have hlt : k + 1 < m := chainAt_lt_m hx hc'
  unfold chainLen
  have hmem : k + 1 ∈ (Finset.range m).filter (fun t => ChainAt x pin c t i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hc'⟩
  have hle := Finset.le_sup (f := fun t => t + 1) hmem
  simpa using hle

noncomputable def maskRank {n m : Nat} (x : Fin m → Finset (Fin n)) (pin : Fin m → Option Bool)
    (c : Bool) (y : Finset (Fin n)) : Nat :=
  (Finset.univ.filter (fun i : Fin m => x i ⊆ y)).sup (chainLen x pin c)

noncomputable def maxRank {n m : Nat} (x : Fin m → Finset (Fin n)) (pin : Fin m → Option Bool)
    (c : Bool) : Nat :=
  (Finset.univ : Finset (Fin m)).sup (chainLen x pin c)

theorem maskRank_le_maxRank {n m : Nat} (x : Fin m → Finset (Fin n)) (pin : Fin m → Option Bool)
    (c : Bool) (y : Finset (Fin n)) :
    maskRank x pin c y ≤ maxRank x pin c := by
  unfold maskRank maxRank
  apply Finset.sup_le
  intro i _
  exact Finset.le_sup (f := chainLen x pin c) (Finset.mem_univ i)

theorem maxRank_le_m {n m : Nat} (x : Fin m → Finset (Fin n)) (pin : Fin m → Option Bool)
    (c : Bool) : maxRank x pin c ≤ m := by
  unfold maxRank
  apply Finset.sup_le
  intro i _
  exact chainLen_le_m x pin c i

theorem maxRank_lt_pow {n m r : Nat} {x : Fin m → Finset (Fin n)} {pin : Fin m → Option Bool}
    {c : Bool}
    (hgood2 : ¬ (∃ u : Fin (2 ^ r) → Fin m,
      (∀ j, pin (u j) = some (if j.val % 2 = 0 then !c else c)) ∧
      ∀ a b, a.val + 1 = b.val → x (u a) ⊆ x (u b))) :
    maxRank x pin c < 2 ^ r := by
  unfold maxRank
  by_cases hne : (Finset.univ : Finset (Fin m)).Nonempty
  · obtain ⟨i, _, hsup⟩ := Finset.exists_mem_eq_sup Finset.univ hne (chainLen x pin c)
    rw [hsup]
    exact chainLen_lt_pow hgood2 i
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.sup_empty, bot_eq_zero]
    exact Nat.pos_of_ne_zero (by positivity)

theorem maskRank_witness {n m : Nat} {x : Fin m → Finset (Fin n)} {pin : Fin m → Option Bool}
    {c : Bool} {y : Finset (Fin n)} (h : 1 ≤ maskRank x pin c y) :
    ∃ i : Fin m, x i ⊆ y ∧ chainLen x pin c i = maskRank x pin c y := by
  unfold maskRank at h ⊢
  set S := Finset.univ.filter (fun i : Fin m => x i ⊆ y)
  have hne : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp] at h
    simp at h
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup S hne (chainLen x pin c)
  exact ⟨i, (Finset.mem_filter.mp hi).2, hsup.symm⟩

theorem maskRank_empty {n m : Nat} {x : Fin m → Finset (Fin n)} {pin : Fin m → Option Bool}
    {c : Bool} (hx : Function.Injective x)
    (hgood1 : ∀ i, x i = ∅ → pin i ≠ some (!c)) :
    maskRank x pin c ∅ = 0 := by
  by_contra hne
  have hpos : 1 ≤ maskRank x pin c ∅ := by omega
  obtain ⟨i, hxi, hli⟩ := maskRank_witness hpos
  have hc := chainLen_witness (by omega : 1 ≤ chainLen x pin c i)
  generalize hk_eq : chainLen x pin c i - 1 = k at hc
  obtain ⟨u, hlast, hp, hs⟩ := hc
  have h0sub : x (u ⟨0, Nat.zero_lt_succ k⟩) ⊆ x (u ⟨k, Nat.lt_succ_self k⟩) := by
    by_cases hk : k = 0
    · subst hk; exact Finset.Subset.rfl
    · exact (chainAt_strict hx u hp hs ⟨0, Nat.zero_lt_succ k⟩ ⟨k, Nat.lt_succ_self k⟩
        (by show 0 < k; omega)).subset
  rw [hlast] at h0sub
  have h0emp : x (u ⟨0, Nat.zero_lt_succ k⟩) = ∅ :=
    Finset.subset_empty.mp (h0sub.trans hxi)
  have h0pin := hp ⟨0, Nat.zero_lt_succ k⟩
  simp only [Nat.zero_mod, ite_true] at h0pin
  exact hgood1 (u ⟨0, Nat.zero_lt_succ k⟩) h0emp h0pin

theorem maskRank_pin {n m : Nat} {x : Fin m → Finset (Fin n)} {pin : Fin m → Option Bool}
    {c : Bool} (hx : Function.Injective x) (i : Fin m) (v : Bool) (hp : pin i = some v) :
    (if maskRank x pin c (x i) % 2 = 1 then !c else c) = v := by
  have hle_k : chainLen x pin c i ≤ maskRank x pin c (x i) := by
    unfold maskRank
    have hmem : i ∈ Finset.univ.filter (fun j : Fin m => x j ⊆ x i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, Finset.Subset.rfl⟩
    exact Finset.le_sup (f := chainLen x pin c) hmem
  set k := maskRank x pin c (x i)
  by_cases hk0 : k = 0
  · simp only [hk0, Nat.zero_mod, zero_ne_one, ite_false]
    by_contra hne
    have hv : v = !c := by cases c <;> cases v <;> simp_all
    subst hv
    have hc0 : ChainAt x pin c 0 i := by
      refine ⟨fun _ => i, rfl, ?_, ?_⟩
      · intro j
        have hj : j.val = 0 := by omega
        simp [hp]
      · intro a b hab
        omega
    have hm_pos : 0 < m := Fin.pos i
    have h1 : 1 ≤ chainLen x pin c i := by
      unfold chainLen
      have hmem : 0 ∈ (Finset.range m).filter (fun t => ChainAt x pin c t i) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm_pos, hc0⟩
      exact Finset.le_sup (f := fun t => t + 1) hmem
    omega
  · have hpos : 1 ≤ k := by omega
    obtain ⟨j, hxj, hlj⟩ := maskRank_witness hpos
    have hcj : ChainAt x pin c (k - 1) j := by
      have h := chainLen_witness (by omega : 1 ≤ chainLen x pin c j)
      simpa [hlj] using h
    by_contra hne
    have hpi : pin i = some (if (k - 1 + 1) % 2 = 0 then !c else c) := by
      have hsub1 : k - 1 + 1 = k := by omega
      rw [hsub1, hp]
      by_cases hodd : k % 2 = 1
      · have hev : ¬ (k % 2 = 0) := by omega
        simp only [hodd, ite_true] at hne
        simp only [hev, ite_false, Option.some.injEq]
        cases c <;> cases v <;> simp_all
      · have hev : k % 2 = 0 := by omega
        simp only [hodd, ite_false] at hne
        simp only [hev, ite_true, Option.some.injEq]
        cases c <;> cases v <;> simp_all
    have hext := chainLen_extend hx hcj hxj hpi
    omega

end RankData

def vecOf {n : Nat} (y : Finset (Fin n)) (q : Fin (n + 2)) : Bool :=
  if h : q.val < n then decide (⟨q.val, h⟩ ∈ y) else decide (q.val = n + 1)

theorem ofFn_vecOf {n : Nat} (y : Finset (Fin n)) :
    List.ofFn (vecOf y) = List.ofFn (fun k : Fin n => decide (k ∈ y)) ++ [false, true] := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    rw [List.getElem_ofFn]
    have hget := getD_chain n (fun k : Fin n => decide (k ∈ y)) i
    rw [List.getD_eq_getElem _ _ h2] at hget
    rw [hget]
    rfl

theorem exists_r0 (B r : Nat) (h1 : 1 ≤ B) (h2 : B < 2 ^ r) :
    ∃ r0 ≤ r, B < 2 ^ r0 ∧ 2 ^ r0 - 1 ≤ 2 * B := by
  induction r with
  | zero => simp at h2; omega
  | succ r ih =>
    by_cases h : B < 2 ^ r
    · obtain ⟨r0, hr0, hlt, hle⟩ := ih h
      exact ⟨r0, by omega, hlt, hle⟩
    · refine ⟨r + 1, le_rfl, h2, ?_⟩
      rw [pow_succ]
      omega

theorem sum_indicator_range_le_one (v B : Nat) :
    ((List.range B).map (fun k => if v = k + 1 then 1 else 0)).sum ≤ 1 := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    by_cases hv : v = B + 1
    · have hzero : ((List.range B).map (fun k => if v = k + 1 then 1 else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro a ha
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
        have hk' := List.mem_range.mp hk
        have hne : v ≠ k + 1 := by omega
        simp [hne]
      rw [hzero]
      simp [hv]
    · simp [hv, ih]

theorem sum_filter_buckets_le_length {α : Type*} (f : α → Nat) (l : List α) (B : Nat) :
    ((List.range B).map (fun k => (l.filter (fun a => decide (f a = k + 1))).length)).sum ≤ l.length := by
  induction l with
  | nil =>
    have h0 : ((List.range B).map (fun k => (([] : List α).filter (fun a => decide (f a = k + 1))).length)).sum = 0 := by
      apply List.sum_eq_zero
      intro a ha
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
      rfl
    rw [h0]
    exact Nat.zero_le _
  | cons a as ih =>
    have hsplit : ∀ k, ((a :: as).filter (fun b => decide (f b = k + 1))).length =
        (if f a = k + 1 then 1 else 0) + (as.filter (fun b => decide (f b = k + 1))).length := by
      intro k
      simp only [List.filter_cons]
      by_cases h : f a = k + 1
      · simp [h, Nat.add_comm]
      · simp [h]
    have hsum : ∀ xs : List Nat,
        (xs.map (fun k => (if f a = k + 1 then 1 else 0) +
          (as.filter (fun b => decide (f b = k + 1))).length)).sum =
        (xs.map (fun k => if f a = k + 1 then 1 else 0)).sum +
        (xs.map (fun k => (as.filter (fun b => decide (f b = k + 1))).length)).sum := by
      intro xs
      induction xs with
      | nil => simp
      | cons k ks ihs =>
        simp only [List.map_cons, List.sum_cons, ihs]
        omega
    have hmap : (List.range B).map (fun k => ((a :: as).filter (fun b => decide (f b = k + 1))).length) =
        (List.range B).map (fun k => (if f a = k + 1 then 1 else 0) +
          (as.filter (fun b => decide (f b = k + 1))).length) := by
      apply List.map_congr_left
      intro k _
      exact hsplit k
    rw [hmap, hsum]
    have h1 := sum_indicator_range_le_one (f a) B
    simp only [List.length_cons]
    omega

theorem filter_parity_lengths (l : List Nat) :
    (l.filter (fun k => decide (k % 2 = 1))).length +
    (l.filter (fun k => decide (k % 2 = 0))).length = l.length := by
  induction l with
  | nil => simp
  | cons k ks ih =>
    simp only [List.filter_cons, List.length_cons]
    by_cases h : k % 2 = 1
    · have h0 : ¬ (k % 2 = 0) := by omega
      simp [h]
      omega
    · have h0 : k % 2 = 0 := by omega
      simp [h0]
      omega

def suffixOr {N : Nat} (B : Nat) (Buc : Nat → Build068.Sig N) : Nat → Build068.Sig N
  | 0 => Buc (B - 1)
  | d + 1 => Build068.bor (Buc (B - 1 - (d + 1))) (suffixOr B Buc d)

theorem decide_inst_eq (P : Prop) (d1 d2 : Decidable P) : @decide P d1 = @decide P d2 := by
  by_cases h : P <;> simp [h]

theorem ite_inst_eq {α : Type*} (P : Prop) (d1 d2 : Decidable P) (a b : α) :
    @ite α P d1 a b = @ite α P d2 a b := by
  by_cases h : P <;> simp [h]

theorem upper_dir (n m r : Nat) (x : Fin m → Finset (Fin n)) (pin : Fin m → Option Bool) (c : Bool)
    (hx : Function.Injective x)
    (hgood1 : ∀ i, x i = ∅ → pin i ≠ some (!c))
    (hgood2 : ¬ (∃ u : Fin (2 ^ r) → Fin m,
      (∀ j, pin (u j) = some (if j.val % 2 = 0 then !c else c)) ∧
      ∀ a b, a.val + 1 = b.val → x (u a) ⊆ x (u b))) :
    ∃ (C : Circuit) (p : Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
      C.output < n + 2 + C.size ∧ p < n + 2 + C.size ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ (∅ : Finset (Fin n)))) ++ [false, true])).getD C.output false = c ∧
      (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ (∅ : Finset (Fin n)))) ++ [false, true])).getD p false = !c ∧
      (∀ i,
        (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ x i)) ++ [false, true])).getD p false =
          !((C.wires (List.ofFn (fun k : Fin n => decide (k ∈ x i)) ++ [false, true])).getD C.output false) ∧
        ∀ v, pin i = some v →
          (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ x i)) ++ [false, true])).getD C.output false = v) ∧
      C.size ≤ (n + 12) * (m + 1) ∧
      ∀ y : Finset (Fin n),
        (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ y)) ++ [false, true])).getD p false =
          !((C.wires (List.ofFn (fun k : Fin n => decide (k ∈ y)) ++ [false, true])).getD C.output false) := by
  let len : Fin m → Nat := RankData.chainLen x pin c
  let L : Finset (Fin n) → Nat := RankData.maskRank x pin c
  let B : Nat := RankData.maxRank x pin c
  have hBm : B ≤ m := RankData.maxRank_le_m x pin c
  have hBpow : B < 2 ^ r := RankData.maxRank_lt_pow hgood2
  have hLB : ∀ y, L y ≤ B := RankData.maskRank_le_maxRank x pin c
  have hLemp : L ∅ = 0 := RankData.maskRank_empty hx hgood1
  have hLpin : ∀ i v, pin i = some v → (if L (x i) % 2 = 1 then !c else c) = v :=
    RankData.maskRank_pin hx
  by_cases hB0 : B = 0
  · let outW : Nat := if c then n + 1 else n
    let pW : Nat := if c then n else n + 1
    refine ⟨Circuit.mk [] outW, pW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · simp [PEqualNP.MetaComplexity.NestedCover.ReadsBack]
    · simp only [Circuit.size, List.length_nil, outW]
      cases c <;> simp
    · simp only [Circuit.size, List.length_nil, pW]
      cases c <;> simp
    · simp [PEqualNP.NotBracket.notCount]
    · change (List.ofFn (fun k : Fin n => decide (k ∈ (∅ : Finset (Fin n)))) ++ [false, true]).getD outW false = c
      rw [getD_chain]
      cases c <;> simp [outW]
    · change (List.ofFn (fun k : Fin n => decide (k ∈ (∅ : Finset (Fin n)))) ++ [false, true]).getD pW false = !c
      rw [getD_chain]
      cases c <;> simp [pW]
    · intro i
      constructor
      · change (List.ofFn (fun k : Fin n => decide (k ∈ x i)) ++ [false, true]).getD pW false =
          !((List.ofFn (fun k : Fin n => decide (k ∈ x i)) ++ [false, true]).getD outW false)
        rw [getD_chain, getD_chain]
        cases c <;> simp [outW, pW]
      · intro v hv
        have hLx : L (x i) = 0 := by have := hLB (x i); omega
        have hcv := hLpin i v hv
        rw [hLx] at hcv
        simp only [Nat.zero_mod, zero_ne_one, ite_false] at hcv
        change (List.ofFn (fun k : Fin n => decide (k ∈ x i)) ++ [false, true]).getD outW false = v
        rw [getD_chain, ← hcv]
        cases c <;> simp [outW]
    · simp [Circuit.size]
    · intro y
      change (List.ofFn (fun k : Fin n => decide (k ∈ y)) ++ [false, true]).getD pW false =
        !((List.ofFn (fun k : Fin n => decide (k ∈ y)) ++ [false, true]).getD outW false)
      rw [getD_chain, getD_chain]
      cases c <;> simp [outW, pW]
  · have hB1 : 1 ≤ B := by omega
    obtain ⟨r0, hr0_le, hB_lt_r0, hr0_bound⟩ := exists_r0 B r hB1 hBpow
    let inputSig : Fin (n + 2) → Build068.Sig (n + 2) := fun q z => z q
    let A0 : Set (Build068.Sig (n + 2)) := Set.range inputSig
    have hS0 : GateBridgeN.Scheduled (n + 2) id 0 0 A0 :=
      GateBridgeN.start inputSig (fun _ _ => rfl)
    let fFalse : Build068.Sig (n + 2) := inputSig ⟨n, by omega⟩
    let fTrue : Build068.Sig (n + 2) := inputSig ⟨n + 1, by omega⟩
    let fBit : Fin n → Build068.Sig (n + 2) := fun k => inputSig ⟨k.val, by omega⟩
    have hfFalse_A0 : fFalse ∈ A0 := ⟨⟨n, by omega⟩, rfl⟩
    have hfTrue_A0 : fTrue ∈ A0 := ⟨⟨n + 1, by omega⟩, rfl⟩
    have hfBit_A0 : ∀ k : Fin n, fBit k ∈ A0 := fun k => ⟨⟨k.val, by omega⟩, rfl⟩
    have hfFalse_val : ∀ y, fFalse (vecOf y) = false := by
      intro y; simp [fFalse, inputSig, vecOf]
    have hfTrue_val : ∀ y, fTrue (vecOf y) = true := by
      intro y; simp [fTrue, inputSig, vecOf]
    have hfBit_val : ∀ y k, fBit k (vecOf y) = decide (k ∈ y) := by
      intro y k; simp [fBit, inputSig, vecOf, k.isLt]
    let T_sig : Fin m → Build068.Sig (n + 2) := fun i =>
      Build068.foldAndList fTrue (((List.finRange n).filter (fun k => decide (k ∈ x i))).map fBit)
    have hT_val : ∀ i y, T_sig i (vecOf y) = decide (x i ⊆ y) := by
      intro i y
      dsimp only [T_sig]
      rw [Build068.foldAndList_eval, hfTrue_val, Bool.true_and]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
        forall_exists_index, and_imp, decide_eq_true_eq, Finset.subset_iff]
      constructor
      · intro h k hk
        have h1 := h (fBit k) k hk rfl
        rw [hfBit_val, decide_eq_true_eq] at h1
        exact h1
      · intro h f k hk rfl
        rw [hfBit_val, decide_eq_true_eq]
        exact h hk
    have hBuildA : Build068.BuildN A0 (Set.range T_sig) (m * n) 0 := by
      have h := Build068.finG (A := A0) T_sig n 0 (fun i => by
        have hb := Build068.build_foldAndList fTrue
          (((List.finRange n).filter (fun k => decide (k ∈ x i))).map fBit)
          hfTrue_A0 (by
            intro f hf
            obtain ⟨k, _, rfl⟩ := List.mem_map.mp hf
            exact hfBit_A0 k)
        refine Build068.relax hb le_rfl le_rfl ?_ le_rfl
        rw [List.length_map]
        exact (List.length_filter_le _ _).trans (by simp))
      simpa using h
    let A1 : Set (Build068.Sig (n + 2)) := A0 ∪ Set.range T_sig
    let pins : Nat → List (Fin m) := fun k =>
      (List.finRange m).filter (fun i => decide (len i = k + 1))
    let Buc : Nat → Build068.Sig (n + 2) := fun k =>
      Build068.foldOrList fFalse ((pins k).map T_sig)
    have hBuc_val : ∀ k y, Buc k (vecOf y) = true ↔ ∃ i : Fin m, x i ⊆ y ∧ len i = k + 1 := by
      intro k y
      dsimp only [Buc, pins]
      rw [Build068.foldOrList_eval, hfFalse_val, Bool.false_or]
      simp only [List.any_eq_true, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq]
      constructor
      · rintro ⟨f, ⟨i, hi, rfl⟩, hti⟩
        rw [hT_val, decide_eq_true_eq] at hti
        exact ⟨i, hti, hi⟩
      · rintro ⟨i, hsub, hi⟩
        exact ⟨T_sig i, ⟨i, hi, rfl⟩, by rw [hT_val, decide_eq_true_eq]; exact hsub⟩
    have hBuildB1 : Build068.BuildN A1 {f | ∃ k < B, f = Buc k} m 0 := by
      have h := Build068.listBuildVar (A := A1) (List.range B) Buc (fun k => (pins k).length)
        (fun k _ => by
          have hb := Build068.build_foldOrList (A := A1) fFalse ((pins k).map T_sig)
            (Or.inl hfFalse_A0) (by
              intro f hf
              obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
              exact Or.inr ⟨i, rfl⟩)
          simpa [List.length_map] using hb)
      refine Build068.relax h le_rfl ?_ ?_ le_rfl
      · rintro f ⟨k, hk, rfl⟩
        exact ⟨k, List.mem_range.mpr hk, rfl⟩
      · have hle := sum_filter_buckets_le_length len (List.finRange m) B
        simpa [pins] using hle
    let A2 : Set (Build068.Sig (n + 2)) := A1 ∪ {f | ∃ k < B, f = Buc k}
    let R_rev : Nat → Build068.Sig (n + 2) := suffixOr B Buc
    have hR_mono : ∀ d1 d2 z, d1 ≤ d2 → R_rev d1 z = true → R_rev d2 z = true := by
      intro d1 d2 z hle h1
      have hd : ∃ e, d2 = d1 + e := ⟨d2 - d1, by omega⟩
      obtain ⟨e, rfl⟩ := hd
      induction e with
      | zero => simpa using h1
      | succ e ih =>
        have hprev : suffixOr B Buc (d1 + e) z = true := ih (by omega)
        dsimp only [R_rev, suffixOr]
        simp [Build068.bor, hprev]
    have hR_val : ∀ d < B, ∀ y, R_rev d (vecOf y) = decide (B - d ≤ L y) := by
      intro d hd y
      induction d with
      | zero =>
        dsimp only [R_rev, suffixOr]
        apply Bool.eq_iff_iff.mpr
        rw [hBuc_val, decide_eq_true_eq]
        constructor
        · rintro ⟨i, hsub, hlen⟩
          have hle : len i ≤ L y := by
            classical
            exact Finset.le_sup (f := len) (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsub⟩)
          omega
        · intro hge
          have hpos : 1 ≤ L y := by omega
          obtain ⟨i, hsub, hlen⟩ := RankData.maskRank_witness hpos
          have hlen' : len i = L y := hlen
          have hleB := hLB y
          exact ⟨i, hsub, by omega⟩
      | succ d ih =>
        have hih : suffixOr B Buc d (vecOf y) = decide (B - d ≤ L y) := ih (by omega)
        dsimp only [R_rev, suffixOr]
        simp only [Build068.bor, hih]
        apply Bool.eq_iff_iff.mpr
        rw [Bool.or_eq_true, hBuc_val, decide_eq_true_eq, decide_eq_true_eq]
        constructor
        · rintro (⟨i, hsub, hlen⟩ | hge)
          · have hle : len i ≤ L y := by
              classical
              exact Finset.le_sup (f := len) (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsub⟩)
            omega
          · omega
        · intro hge
          by_cases hhi : B - d ≤ L y
          · exact Or.inr hhi
          · left
            have hpos : 1 ≤ L y := by omega
            obtain ⟨i, hsub, hlen⟩ := RankData.maskRank_witness hpos
            have hlen' : len i = L y := hlen
            exact ⟨i, hsub, by omega⟩
    have hBuildB2_aux : ∀ D, 1 ≤ D → D ≤ B →
        Build068.BuildN A2 {f | ∃ d < D, f = R_rev d} (D - 1) 0 := by
      intro D hD1 hDB
      induction D with
      | zero => omega
      | succ D ih =>
        by_cases hD0 : D = 0
        · subst hD0
          refine Build068.idle ?_
          rintro f ⟨d, hd, rfl⟩
          have hd0 : d = 0 := by omega
          subst hd0
          exact Or.inr ⟨B - 1, by omega, rfl⟩
        · have hprev := ih (by omega) (by omega)
          have hstep : Build068.BuildN (A2 ∪ {f | ∃ d < D, f = R_rev d}) {R_rev D} 1 0 := by
            have hDeq : D = (D - 1) + 1 := by omega
            have hRdef : R_rev D = Build068.bor (Buc (B - 1 - D)) (R_rev (D - 1)) := by
              conv_lhs => rw [hDeq]
              dsimp only [R_rev, suffixOr]
              rw [← hDeq]
            rw [hRdef]
            exact Build068.orG (Or.inl (Or.inr ⟨B - 1 - D, by omega, rfl⟩))
              (Or.inr ⟨D - 1, by omega, rfl⟩)
          refine Build068.relax (Build068.seq hprev hstep) le_rfl ?_ (by omega) (by simp)
          rintro f ⟨d, hd, rfl⟩
          by_cases hlt : d < D
          · exact Or.inl ⟨d, hlt, rfl⟩
          · have heq : d = D := by omega
            subst heq
            exact Or.inr rfl
    have hBuildB2 : Build068.BuildN A2 {f | ∃ d < B, f = R_rev d} m 0 :=
      Build068.relax (hBuildB2_aux B hB1 le_rfl) le_rfl le_rfl (by omega) le_rfl
    let A3 : Set (Build068.Sig (n + 2)) := A2 ∪ {f | ∃ d < B, f = R_rev d}
    let u_sig : Nat → Build068.Sig (n + 2) := fun j => if j < B then R_rev j else fTrue
    have hu_mem : ∀ j < 2 ^ r0 - 1, u_sig j ∈ A3 := by
      intro j _
      dsimp only [u_sig]
      split_ifs with h
      · exact Or.inr ⟨j, h, rfl⟩
      · exact Or.inl (Or.inl (Or.inl hfTrue_A0))
    obtain ⟨nu, hBuildC_raw, hnu_eval⟩ := Construct.inverter r0 A3 u_sig hu_mem
    have hT_le : Construct.T r0 ≤ 8 * m := by
      have hadd := Construct.T_add r0
      omega
    have hBuildC : Build068.BuildN A3 {f | ∃ j < 2 ^ r0 - 1, f = nu j} (8 * m) r0 :=
      Build068.relax hBuildC_raw le_rfl le_rfl hT_le le_rfl
    have hSrt_u : ∀ y, Construct.Srt (2 ^ r0 - 1) u_sig (vecOf y) := by
      intro y i j hij _ hi
      dsimp only [u_sig] at hi ⊢
      by_cases hj : j < B
      · have hi' : i < B := by omega
        simp only [hi', hj, ite_true] at hi ⊢
        exact hR_mono i j (vecOf y) hij hi
      · simp only [hj, ite_false]
        exact hfTrue_val y
    have hnu_val : ∀ d < B, ∀ y, nu d (vecOf y) = decide (L y < B - d) := by
      intro d hd y
      have hd' : d < 2 ^ r0 - 1 := by omega
      rw [hnu_eval (vecOf y) (hSrt_u y) d hd']
      dsimp only [u_sig]
      simp only [hd, ite_true]
      rw [hR_val d hd y]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      omega
    let A4 : Set (Build068.Sig (n + 2)) := A3 ∪ {f | ∃ j < 2 ^ r0 - 1, f = nu j}
    let E_sig : Nat → Build068.Sig (n + 2) := fun k =>
      Build068.ban (if k = 0 then fTrue else R_rev (B - k))
        (if k < B then nu (B - 1 - k) else fTrue)
    have hE_val : ∀ k ≤ B, ∀ y, E_sig k (vecOf y) = decide (L y = k) := by
      intro k hk y
      dsimp only [E_sig, Build068.ban]
      have hleft : (if k = 0 then fTrue else R_rev (B - k)) (vecOf y) = decide (k ≤ L y) := by
        split_ifs with h0
        · subst h0; simp [hfTrue_val]
        · rw [hR_val (B - k) (by omega) y]
          have : B - (B - k) = k := by omega
          rw [this]
      have hright : (if k < B then nu (B - 1 - k) else fTrue) (vecOf y) = decide (L y ≤ k) := by
        split_ifs with hlt
        · rw [hnu_val (B - 1 - k) (by omega) y]
          have : B - (B - 1 - k) = k + 1 := by omega
          rw [this]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          omega
        · rw [hfTrue_val]
          have hle := hLB y
          have : L y ≤ k := by omega
          simp [this]
      rw [hleft, hright]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    have hBuildD1 : Build068.BuildN A4 {f | ∃ k < B + 1, f = E_sig k} (m + 1) 0 := by
      have h := Construct.rangeBuild (A := A4) (B + 1) E_sig 1 0 (fun k hk => by
        dsimp only [E_sig]
        apply Build068.andG
        · split_ifs with h0
          · exact Or.inl (Or.inl (Or.inl (Or.inl hfTrue_A0)))
          · exact Or.inl (Or.inr ⟨B - k, by omega, rfl⟩)
        · split_ifs with hlt
          · exact Or.inr ⟨B - 1 - k, by omega, rfl⟩
          · exact Or.inl (Or.inl (Or.inl (Or.inl hfTrue_A0))))
      refine Build068.relax h le_rfl le_rfl ?_ (by simp)
      omega
    let A5 : Set (Build068.Sig (n + 2)) := A4 ∪ {f | ∃ k < B + 1, f = E_sig k}
    let oddKs : List Nat := (List.range (B + 1)).filter (fun k => decide (k % 2 = 1))
    let evenKs : List Nat := (List.range (B + 1)).filter (fun k => decide (k % 2 = 0))
    let oddSig : Build068.Sig (n + 2) := Build068.foldOrList fFalse (oddKs.map E_sig)
    let evenSig : Build068.Sig (n + 2) := Build068.foldOrList fFalse (evenKs.map E_sig)
    have hodd_val : ∀ y, oddSig (vecOf y) = decide (L y % 2 = 1) := by
      intro y
      dsimp only [oddSig, oddKs]
      rw [Build068.foldOrList_eval, hfFalse_val, Bool.false_or]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨f, ⟨k, ⟨hk, hpar⟩, rfl⟩, he⟩
        rw [hE_val k (by omega) y, decide_eq_true_eq] at he
        rw [he]; exact hpar
      · intro hpar
        have hle := hLB y
        refine ⟨E_sig (L y), ⟨L y, ⟨by omega, hpar⟩, rfl⟩, ?_⟩
        rw [hE_val (L y) hle y]
        simp
    have heven_val : ∀ y, evenSig (vecOf y) = decide (L y % 2 = 0) := by
      intro y
      dsimp only [evenSig, evenKs]
      rw [Build068.foldOrList_eval, hfFalse_val, Bool.false_or]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨f, ⟨k, ⟨hk, hpar⟩, rfl⟩, he⟩
        rw [hE_val k (by omega) y, decide_eq_true_eq] at he
        rw [he]; exact hpar
      · intro hpar
        have hle := hLB y
        refine ⟨E_sig (L y), ⟨L y, ⟨by omega, hpar⟩, rfl⟩, ?_⟩
        rw [hE_val (L y) hle y]
        simp
    have hBuildD2 : Build068.BuildN A5 {oddSig, evenSig} (m + 1) 0 := by
      have ho : Build068.BuildN A5 {oddSig} oddKs.length 0 := by
        have hb := Build068.build_foldOrList (A := A5) fFalse (oddKs.map E_sig)
          (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hfFalse_A0))))) (by
            intro f hf
            obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hf
            exact Or.inr ⟨k, List.mem_range.mp (List.mem_filter.mp hk).1, rfl⟩)
        simpa [List.length_map] using hb
      have he : Build068.BuildN (A5 ∪ {oddSig}) {evenSig} evenKs.length 0 := by
        have hb := Build068.build_foldOrList (A := A5 ∪ {oddSig}) fFalse (evenKs.map E_sig)
          (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hfFalse_A0)))))) (by
            intro f hf
            obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hf
            exact Or.inl (Or.inr ⟨k, List.mem_range.mp (List.mem_filter.mp hk).1, rfl⟩))
        simpa [List.length_map] using hb
      have hlen_oe : oddKs.length + evenKs.length = B + 1 := by
        have h := filter_parity_lengths (List.range (B + 1))
        simpa [oddKs, evenKs] using h
      refine Build068.relax (Build068.seq ho he) le_rfl ?_ (by omega) (by simp)
      intro f hf
      rcases Set.mem_insert_iff.mp hf with rfl | hf
      · exact Or.inl rfl
      · exact Or.inr hf
    have hS1 := Build068.BuildN.run hBuildA hS0 le_rfl
    obtain ⟨c1, hc1, cn1, hcn1, hSch1⟩ := hS1
    have hS2 := Build068.BuildN.run hBuildB1 hSch1 le_rfl
    obtain ⟨c2, hc2, cn2, hcn2, hSch2⟩ := hS2
    have hS3 := Build068.BuildN.run hBuildB2 hSch2 le_rfl
    obtain ⟨c3, hc3, cn3, hcn3, hSch3⟩ := hS3
    have hS4 := Build068.BuildN.run hBuildC hSch3 le_rfl
    obtain ⟨c4, hc4, cn4, hcn4, hSch4⟩ := hS4
    have hS5 := Build068.BuildN.run hBuildD1 hSch4 le_rfl
    obtain ⟨c5, hc5, cn5, hcn5, hSch5⟩ := hS5
    have hS6 := Build068.BuildN.run hBuildD2 hSch5 le_rfl
    obtain ⟨c6, hc6, cn6, hcn6, hSch6⟩ := hS6
    obtain ⟨gs, hgs, hnc, hrb, hfan, hw⟩ := hSch6
    let outSig : Build068.Sig (n + 2) := if c then evenSig else oddSig
    let pSig : Build068.Sig (n + 2) := if c then oddSig else evenSig
    have hout_mem : outSig ∈ A5 ∪ {oddSig, evenSig} := by
      dsimp only [outSig]
      cases c
      · exact Or.inr (Set.mem_insert oddSig {evenSig})
      · exact Or.inr (Set.mem_insert_of_mem oddSig (Set.mem_singleton evenSig))
    have hp_mem : pSig ∈ A5 ∪ {oddSig, evenSig} := by
      dsimp only [pSig]
      cases c
      · exact Or.inr (Set.mem_insert_of_mem oddSig (Set.mem_singleton evenSig))
      · exact Or.inr (Set.mem_insert oddSig {evenSig})
    obtain ⟨w_out, hw_out_lt, hw_out_eq⟩ := hw outSig hout_mem
    obtain ⟨w_p, hw_p_lt, hw_p_eq⟩ := hw pSig hp_mem
    let C : Circuit := Circuit.mk gs w_out
    have hC_out : ∀ y,
        (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ y)) ++ [false, true])).getD C.output false =
        (if L y % 2 = 1 then !c else c) := by
      intro y
      rw [← ofFn_vecOf y]
      have h := hw_out_eq (vecOf y)
      change (C.wires (List.ofFn (vecOf y))).getD C.output false = outSig (vecOf y) at h
      rw [h]
      dsimp only [outSig]
      cases c
      · simp only [Bool.false_eq_true, ite_false, hodd_val, Bool.not_false]
        by_cases hp1 : L y % 2 = 1 <;> simp [hp1]
      · simp only [ite_true, heven_val, Bool.not_true]
        by_cases hp1 : L y % 2 = 1
        · have hp0 : ¬ (L y % 2 = 0) := by omega
          simp [hp1]
        · have hp0 : L y % 2 = 0 := by omega
          simp [hp0]
    have hC_p : ∀ y : Finset (Fin n),
        (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ y)) ++ [false, true])).getD w_p false =
        !((C.wires (List.ofFn (fun k : Fin n => decide (k ∈ y)) ++ [false, true])).getD C.output false) := by
      intro y
      rw [hC_out y, ← ofFn_vecOf y]
      have h := hw_p_eq (vecOf y)
      change (C.wires (List.ofFn (vecOf y))).getD w_p false = pSig (vecOf y) at h
      rw [h]
      dsimp only [pSig]
      cases c
      · simp only [Bool.false_eq_true, ite_false, heven_val, Bool.not_false]
        by_cases hp1 : L y % 2 = 1
        · have hp0 : ¬ (L y % 2 = 0) := by omega
          simp [hp1]
        · have hp0 : L y % 2 = 0 := by omega
          simp [hp0]
      · simp only [ite_true, hodd_val, Bool.not_true]
        by_cases hp1 : L y % 2 = 1 <;> simp [hp1]
    have hsz_bound : C.size ≤ (n + 12) * (m + 1) := by
      change gs.length ≤ (n + 12) * (m + 1)
      have hmul : (n + 12) * (m + 1) = m * n + 12 * m + n + 12 := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one, Nat.mul_comm n m]
        omega
      omega
    refine ⟨C, w_p, hfan, hrb, ?_, ?_, ?_, ?_, ?_, ?_, hsz_bound, hC_p⟩
    · change w_out < n + 2 + gs.length; omega
    · change w_p < n + 2 + gs.length; omega
    · change PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ r; omega
    · rw [hC_out ∅, hLemp]; simp
    · rw [hC_p ∅, hC_out ∅, hLemp]; simp
    · intro i
      refine ⟨hC_p (x i), fun v hv => ?_⟩
      rw [hC_out (x i)]
      exact hLpin i v hv

end PEqualNP.Outside.L_lib_1291_aux

theorem PEqualNP.Outside.L_lib_1291 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m r : Nat) (x : Fin m → Finset (Fin n)) (pin : Fin m → Option Bool) (c : Bool),
  Function.Injective x →
  let chain := fun (k : Nat) => ∃ u : Fin k → Fin m,
    (∀ j, pin (u j) = some (if j.val % 2 = 0 then !c else c)) ∧
    ∀ i j, i.val+1=j.val → x (u i) ⊆ x (u j)
  let good := (∀ i, x i = ∅ → pin i ≠ some (!c)) ∧ ¬ chain (2^r)
  let wire := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (y : Finset (Fin n)) (p : Nat) =>
    (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ y)) ++ [false,true])).getD p false
  let fit := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Nat) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ p < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
    wire C ∅ C.output = c ∧ wire C ∅ p = !c ∧
    ∀ i, wire C (x i) p = !(wire C (x i) C.output) ∧
      ∀ v, pin i = some v → wire C (x i) C.output = v
  ((∃ C p, fit C p) ↔ good) ∧ (good → ∃ C p, fit C p ∧
    C.size ≤ (n+12)*(m+1) ∧ ∀ y, wire C y p = !(wire C y C.output))) := by
  intro n m r x pin c hx
  dsimp only
  have hdec : ∀ (y : Finset (Fin n)),
      (fun k : Fin n => @decide (k ∈ y) (Classical.propDecidable (k ∈ y))) =
      (fun k : Fin n => decide (k ∈ y)) :=
    fun y => funext fun k => PEqualNP.Outside.L_lib_1291_aux.decide_inst_eq _ _ _
  have hite : ∀ (j : Fin (2 ^ r)),
      @ite Bool (j.val % 2 = 0) (Classical.propDecidable (j.val % 2 = 0)) (!c) c =
      (if j.val % 2 = 0 then !c else c) :=
    fun j => PEqualNP.Outside.L_lib_1291_aux.ite_inst_eq _ _ _ _ _
  simp only [hdec, hite]
  have hupper : ((∀ i, x i = ∅ → pin i ≠ some (!c)) ∧
      ¬ (∃ u : Fin (2 ^ r) → Fin m,
        (∀ j, pin (u j) = some (if j.val % 2 = 0 then !c else c)) ∧
        ∀ i j, i.val + 1 = j.val → x (u i) ⊆ x (u j))) →
      ∃ C p,
        (PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
          C.output < n + 2 + C.size ∧ p < n + 2 + C.size ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
          (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ (∅ : Finset (Fin n)))) ++ [false, true])).getD C.output false = c ∧
          (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ (∅ : Finset (Fin n)))) ++ [false, true])).getD p false = !c ∧
          ∀ i, (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ x i)) ++ [false, true])).getD p false =
              !((C.wires (List.ofFn (fun k : Fin n => decide (k ∈ x i)) ++ [false, true])).getD C.output false) ∧
            ∀ v, pin i = some v →
              (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ x i)) ++ [false, true])).getD C.output false = v) ∧
        C.size ≤ (n + 12) * (m + 1) ∧
        ∀ y : Finset (Fin n), (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ y)) ++ [false, true])).getD p false =
          !((C.wires (List.ofFn (fun k : Fin n => decide (k ∈ y)) ++ [false, true])).getD C.output false) := by
    rintro ⟨hg1, hg2⟩
    obtain ⟨C, p, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      PEqualNP.Outside.L_lib_1291_aux.upper_dir n m r x pin c hx hg1 hg2
    exact ⟨C, p, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, h9, h10⟩
  refine ⟨⟨?_, fun hg => ?_⟩, hupper⟩
  · rintro ⟨C, p, hfan, _, _, _, hnc, hemp_out, hemp_p, hpin⟩
    exact PEqualNP.Outside.L_lib_1291_aux.lower_dir n m r x pin c C p hfan hnc hemp_out hemp_p hpin
  · obtain ⟨C, p, hf, _, _⟩ := hupper hg
    exact ⟨C, p, hf⟩
