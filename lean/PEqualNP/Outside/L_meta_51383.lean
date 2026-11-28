import PEqualNP.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Order
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

namespace PEqualNP.Outside.L_meta_51383_aux

open PEqualNP.CircuitLowerBounds

theorem getD_chain (m : ℕ) (f : Fin m → Bool) (i : ℕ) :
    (List.ofFn f ++ [false, true]).getD i false =
      if h : i < m then f ⟨i, h⟩ else decide (i = m + 1) := by
  by_cases h : i < m
  · rw [dite_eq_left_of_eq_true (eq_true h), List.getD_append _ _ _ _ (by simp; exact h)]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [dite_eq_right_of_eq_false (eq_false h), List.getD_append_right _ _ _ _ (by simp; omega)]
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

theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c cn : Nat)
    (H : ∀ i, BuildN A {F i} c cn) : BuildN A (Set.range F) (k * c) (k * cn) := by
  have h := listBuild (List.finRange k) F c cn (fun i _ => H i)
  rw [List.length_finRange] at h
  refine relax h le_rfl ?_ le_rfl le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, List.mem_finRange i, rfl⟩

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

namespace Part1

open Build068 Construct PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def enc {n : Nat} (x : Finset (Fin n)) : Fin (n + 2) → Bool :=
  fun i => if h : i.val < n then decide (⟨i.val, h⟩ ∈ x) else decide (i.val = n + 1)

theorem ofFn_enc {n : Nat} (x : Finset (Fin n)) :
    List.ofFn (enc x) = List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true] := by
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  simp only [List.getElem_ofFn, enc]
  by_cases h : i < n
  · rw [dite_eq_left_of_eq_true (eq_true h), List.getElem_append_left (by simp [h])]
    simp
  · rw [dite_eq_right_of_eq_false (eq_false h), List.getElem_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    have hlt : i < n + 2 := by rw [List.length_ofFn] at hi1; exact hi1
    rcases Nat.lt_or_eq_of_le (show n ≤ i by omega) with hgt | rfl
    · have hi : i = n + 1 := by omega
      subst hi; simp
    · simp

def coord {n : Nat} (j : Fin n) : Sig (n + 2) :=
  fun v => v ⟨j.val, by omega⟩

theorem coord_enc {n : Nat} (x : Finset (Fin n)) (j : Fin n) :
    coord j (enc x) = decide (j ∈ x) := by
  simp [coord, enc, j.isLt]

def countSig {m : Nat} (xs : List (Sig m)) (c : Nat) : Sig m :=
  fun v => decide (c ≤ (xs.filter (fun f => f v)).length)

theorem countSig_zero {m : Nat} (xs : List (Sig m)) :
    countSig xs 0 = fun _ => true := by
  funext v; simp [countSig]

theorem countSig_nil_succ {m : Nat} (c : Nat) :
    countSig ([] : List (Sig m)) (c + 1) = fun _ => false := by
  funext v; simp [countSig]

theorem countSig_cons_succ {m : Nat} (a : Sig m) (xs : List (Sig m)) (i : Nat) :
    countSig (a :: xs) (i + 1) = bor (countSig xs (i + 1)) (ban (countSig xs i) a) := by
  funext v
  simp only [countSig, bor, ban, List.filter_cons]
  cases ha : a v
  · simp
  · simp only [Bool.and_true, ite_true, List.length_cons]
    by_cases h1 : i + 1 ≤ (xs.filter (fun f => f v)).length
    · have h2 : i ≤ (xs.filter (fun f => f v)).length := by omega
      simp [h1, h2]
    · by_cases h2 : i ≤ (xs.filter (fun f => f v)).length
      · have h3 : i + 1 ≤ (xs.filter (fun f => f v)).length + 1 := by omega
        simp [h1, h2, h3]
      · have h3 : ¬ (i + 1 ≤ (xs.filter (fun f => f v)).length + 1) := by omega
        simp [h1, h2, h3]

theorem buildCount {m : Nat} {A : Set (Sig m)} (K : Nat) (xs : List (Sig m))
    (hT : (fun _ => true) ∈ A) (hF : (fun _ => false) ∈ A)
    (hxs : ∀ f ∈ xs, f ∈ A) :
    BuildN A {f | ∃ c ≤ K, f = countSig xs c} (xs.length * (K * 2)) 0 := by
  induction xs with
  | nil =>
    refine relax (idle (A := A) (B := {f | ∃ c ≤ K, f = countSig [] c}) ?_) le_rfl le_rfl (by simp) le_rfl
    rintro f ⟨c, _, rfl⟩
    cases c
    · simpa [countSig_zero] using hT
    · simpa [countSig_nil_succ] using hF
  | cons a xs ih =>
    have H1 := ih (fun f hf => hxs f (List.mem_cons_of_mem a hf))
    let B1 : Set (Sig m) := {f | ∃ c ≤ K, f = countSig xs c}
    have H2 : BuildN (A ∪ B1) {f | ∃ i < K, f = countSig (a :: xs) (i + 1)} (K * 2) (K * 0) :=
      rangeBuild K (fun i => countSig (a :: xs) (i + 1)) 2 0 (fun i hi => by
        rw [countSig_cons_succ]
        exact step2 (Or.inr ⟨i, by omega, rfl⟩) (Or.inl (hxs a List.mem_cons_self))
          (Or.inr ⟨i + 1, by omega, rfl⟩))
    refine relax (seq H1 H2) le_rfl ?_ ?_ ?_
    · rintro f ⟨c, hc, rfl⟩
      cases c with
      | zero =>
        exact Or.inl ⟨0, Nat.zero_le K, by simp [countSig_zero]⟩
      | succ i =>
        exact Or.inr ⟨i, by omega, rfl⟩
    · simp only [List.length_cons, Nat.succ_mul]
      exact le_rfl
    · simp

def orFold {m : Nat} : List (Sig m) → Sig m
  | [] => fun _ => false
  | f :: fs => bor f (orFold fs)

theorem orFold_eq_true {m : Nat} (fs : List (Sig m)) (v : Fin m → Bool) :
    orFold fs v = true ↔ ∃ f ∈ fs, f v = true := by
  induction fs with
  | nil => simp [orFold]
  | cons f fs ih =>
    simp [orFold, bor, Bool.or_eq_true, ih]

theorem buildOrFold {m : Nat} {A : Set (Sig m)} (fs : List (Sig m))
    (hF : (fun _ => false) ∈ A) (hfs : ∀ f ∈ fs, f ∈ A) :
    BuildN A {orFold fs} fs.length 0 := by
  induction fs with
  | nil =>
    exact relax (idle (by intro g hg; simpa [orFold] using hg ▸ hF)) le_rfl le_rfl (by simp) le_rfl
  | cons f fs ih =>
    have h1 := ih (fun g hg => hfs g (List.mem_cons_of_mem f hg))
    have h2 : BuildN (A ∪ {orFold fs}) {bor f (orFold fs)} 1 0 :=
      orG (Or.inl (hfs f List.mem_cons_self)) (Or.inr rfl)
    refine relax (seq h1 h2) le_rfl ?_ (by simp) (by simp)
    intro g hg; exact Or.inr hg

theorem list_filter_finRange_length {n : Nat} (p : Fin n → Bool) :
    ((List.finRange n).filter p).length = (Finset.univ.filter (fun i : Fin n => p i = true)).card := by
  have hnd : ((List.finRange n).filter p).Nodup := (List.nodup_finRange n).filter p
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext i
  simp

theorem filter_map_length {α β : Type*} (l : List α) (f : α → β) (p : β → Bool) :
    ((l.map f).filter p).length = (l.filter (fun a => p (f a))).length := by
  rw [List.filter_map, List.length_map]; rfl

def allCoords (n : Nat) : List (Sig (n + 2)) :=
  (List.finRange n).map coord

def omitCoords {n : Nat} (j : Fin n) : List (Sig (n + 2)) :=
  ((List.finRange n).filter (fun i => decide (i ≠ j))).map coord

theorem countSig_allCoords_enc {n : Nat} (x : Finset (Fin n)) (c : Nat) :
    countSig (allCoords n) c (enc x) = decide (c ≤ x.card) := by
  simp only [countSig, allCoords, filter_map_length]
  have hlen : ((List.finRange n).filter (fun i : Fin n => coord i (enc x))).length = x.card := by
    rw [list_filter_finRange_length]
    congr 1
    ext i
    simp [coord_enc]
  rw [hlen]

theorem countSig_omitCoords_enc {n : Nat} (x : Finset (Fin n)) (j : Fin n) (c : Nat) :
    countSig (omitCoords j) c (enc x) = decide (c ≤ (x.erase j).card) := by
  simp only [countSig, omitCoords, filter_map_length, List.filter_filter]
  have hlen : ((List.finRange n).filter (fun i : Fin n => coord i (enc x) && decide (i ≠ j))).length =
      (x.erase j).card := by
    rw [list_filter_finRange_length]
    congr 1
    ext i
    simp [coord_enc, Bool.and_eq_true, Finset.mem_erase, and_comm]
  rw [hlen]

theorem erase_card_lt {n : Nat} (x : Finset (Fin n)) (j : Fin n) :
    (x.erase j).card < n := by
  have hsub : x.erase j ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have : j ∈ x.erase j := by rw [heq]; exact Finset.mem_univ j
    exact (Finset.notMem_erase j x) this
  have hlt := Finset.card_lt_card hsub
  simpa using hlt

def F_S (n p : Nat) (S : Finset (Fin n)) (x : Finset (Fin n)) (j : Fin n) : Bool :=
  let k := (x.erase j).card
  if h : k < n then (if ⟨k, h⟩ ∈ S then decide (j ∉ x) else decide (p ≤ k)) else true

theorem F_S_eq_eval {n p : Nat} (S : Finset (Fin n)) (x : Finset (Fin n)) (j : Fin n) :
    F_S n p S x j =
      if ⟨(x.erase j).card, erase_card_lt x j⟩ ∈ S then decide (j ∉ x)
      else decide (p ≤ (x.erase j).card) := by
  simp [F_S, erase_card_lt x j]

theorem F_S_notMem {n p : Nat} (S : Finset (Fin n)) (y : Finset (Fin n)) (j : Fin n)
    (hj : j ∉ y) (hy : y.card < n) :
    F_S n p S y j = if ⟨y.card, hy⟩ ∈ S then true else decide (p ≤ y.card) := by
  have he : y.erase j = y := Finset.erase_eq_of_notMem hj
  have hfin : (⟨(y.erase j).card, erase_card_lt y j⟩ : Fin n) = ⟨y.card, hy⟩ := by
    ext; simp [he]
  rw [F_S_eq_eval, hfin, he, decide_eq_true hj]

theorem F_S_insert {n p : Nat} (S : Finset (Fin n)) (y : Finset (Fin n)) (j : Fin n)
    (hj : j ∉ y) (hy : y.card < n) :
    F_S n p S (insert j y) j = if ⟨y.card, hy⟩ ∈ S then false else decide (p ≤ y.card) := by
  have he : (insert j y).erase j = y := Finset.erase_insert hj
  have hfin : (⟨((insert j y).erase j).card, erase_card_lt (insert j y) j⟩ : Fin n) = ⟨y.card, hy⟩ := by
    ext; simp [he]
  rw [F_S_eq_eval, hfin, he]
  simp

theorem pairwise_lt_sort_fin {n : Nat} (S : Finset (Fin n)) :
    (S.sort (· ≤ ·)).Pairwise (· < ·) := by
  have hle : (S.sort (· ≤ ·)).Pairwise (· ≤ ·) := Finset.pairwise_sort S (· ≤ ·)
  have hnd : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup S (· ≤ ·)
  exact (hle.and hnd).imp (fun h => lt_of_le_of_ne h.1 h.2)

theorem sort_fin_strictMono {n : Nat} (S : Finset (Fin n)) {i j : Nat}
    (hi : i < (S.sort (· ≤ ·)).length) (hj : j < (S.sort (· ≤ ·)).length) (hij : i < j) :
    ((S.sort (· ≤ ·))[i]'hi).val < ((S.sort (· ≤ ·))[j]'hj).val := by
  have hp := List.pairwise_iff_getElem.mp (pairwise_lt_sort_fin S)
  exact hp i j hi hj hij

theorem sort_fin_mono {n : Nat} (S : Finset (Fin n)) {i j : Nat}
    (hi : i < (S.sort (· ≤ ·)).length) (hj : j < (S.sort (· ≤ ·)).length) (hij : i ≤ j) :
    ((S.sort (· ≤ ·))[i]'hi).val ≤ ((S.sort (· ≤ ·))[j]'hj).val := by
  rcases Nat.lt_or_eq_of_le hij with h | rfl
  · exact Nat.le_of_lt (sort_fin_strictMono S hi hj h)
  · exact le_rfl

def L_s {n : Nat} (S : Finset (Fin n)) (s : Nat) : Nat :=
  let rs := S.sort (· ≤ ·)
  if h : 0 < s ∧ s - 1 < rs.length then (rs[s - 1]'(h.2)).val + 1 else 0

def R_s {n : Nat} (S : Finset (Fin n)) (s : Nat) : Nat :=
  let rs := S.sort (· ≤ ·)
  if h : s < rs.length then (rs[s]'h).val else n

def stg {n : Nat} (S : Finset (Fin n)) (x : Finset (Fin n)) : Nat :=
  (S.filter (fun r => r.val + 1 ≤ x.card)).card

theorem stg_le_card {n : Nat} (S : Finset (Fin n)) (x : Finset (Fin n)) :
    stg S x ≤ S.card :=
  Finset.card_le_card (Finset.filter_subset _ S)

theorem L_s_le_R_s {n : Nat} (S : Finset (Fin n)) (s : Nat) (_hs : s ≤ S.card) :
    L_s S s ≤ R_s S s := by
  have hlen : (S.sort (· ≤ ·)).length = S.card := Finset.length_sort (· ≤ ·)
  simp only [L_s, R_s]
  split_ifs with h1 h2 h2
  · have := sort_fin_strictMono S h1.2 h2 (by omega)
    omega
  · have := ((S.sort (· ≤ ·))[s - 1]'(h1.2)).isLt
    omega
  · omega
  · omega

theorem R_s_le_n {n : Nat} (S : Finset (Fin n)) (s : Nat) :
    R_s S s ≤ n := by
  simp only [R_s]
  split_ifs with h
  · exact Nat.le_of_lt ((S.sort (· ≤ ·))[s]'h).isLt
  · exact le_rfl

theorem no_S_in_stage {n : Nat} (S : Finset (Fin n)) (s : Nat) (hs : s ≤ S.card)
    (r : Fin n) (hr : r ∈ S) :
    ¬ (L_s S s ≤ r.val ∧ r.val < R_s S s) := by
  have hlen : (S.sort (· ≤ ·)).length = S.card := Finset.length_sort (· ≤ ·)
  have hmem : r ∈ S.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hr
  obtain ⟨idx, hidx, hr_eq⟩ := List.mem_iff_getElem.mp hmem
  intro ⟨hL, hR⟩
  by_cases hlt : idx < s
  · have h1 : 0 < s ∧ s - 1 < (S.sort (· ≤ ·)).length := ⟨by omega, by omega⟩
    have hLs : L_s S s = ((S.sort (· ≤ ·))[s - 1]'(h1.2)).val + 1 := by
      simp only [L_s, h1, and_self, dite_true]
    have hmo := sort_fin_mono S hidx h1.2 (by omega)
    rw [hr_eq] at hmo
    omega
  · have h2 : s < (S.sort (· ≤ ·)).length := by omega
    have hRs : R_s S s = ((S.sort (· ≤ ·))[s]'h2).val := by
      simp only [R_s, h2, dite_true]
    have hmo := sort_fin_mono S h2 hidx (by omega)
    rw [hr_eq] at hmo
    omega

theorem L_s_le_iff_le_stg {n : Nat} (S : Finset (Fin n)) (x : Finset (Fin n))
    (s : Nat) (hs : s ≤ S.card) :
    L_s S s ≤ x.card ↔ s ≤ stg S x := by
  have hlen : (S.sort (· ≤ ·)).length = S.card := Finset.length_sort (· ≤ ·)
  constructor
  · intro hL
    by_cases hs0 : s = 0
    · subst hs0; exact Nat.zero_le _
    · have h1 : 0 < s ∧ s - 1 < (S.sort (· ≤ ·)).length := ⟨by omega, by omega⟩
      have hLs : L_s S s = ((S.sort (· ≤ ·))[s - 1]'(h1.2)).val + 1 := by
        simp only [L_s, h1, and_self, dite_true]
      rw [hLs] at hL
      let f : Fin s → Fin n := fun i => (S.sort (· ≤ ·))[i.val]'(by omega)
      have hinj : Function.Injective f := by
        intro a b hab
        ext
        by_contra hne
        have hval : ((S.sort (· ≤ ·))[a.val]'(by omega)).val = ((S.sort (· ≤ ·))[b.val]'(by omega)).val :=
          congrArg Fin.val hab
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · have := sort_fin_strictMono S (by omega : a.val < (S.sort (· ≤ ·)).length)
            (by omega : b.val < (S.sort (· ≤ ·)).length) h
          omega
        · have := sort_fin_strictMono S (by omega : b.val < (S.sort (· ≤ ·)).length)
            (by omega : a.val < (S.sort (· ≤ ·)).length) h
          omega
      have hsub : (Finset.univ.image f) ⊆ S.filter (fun r => r.val + 1 ≤ x.card) := by
        intro r hr
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
        rw [Finset.mem_filter]
        refine ⟨(Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem _), ?_⟩
        have hmo := sort_fin_mono S (by omega : i.val < (S.sort (· ≤ ·)).length) h1.2 (by omega)
        dsimp only [f]
        omega
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
      exact hcard
  · intro hst
    by_cases hs0 : s = 0
    · subst hs0; simp [L_s]
    · have h1 : 0 < s ∧ s - 1 < (S.sort (· ≤ ·)).length := ⟨by omega, by omega⟩
      have hLs : L_s S s = ((S.sort (· ≤ ·))[s - 1]'(h1.2)).val + 1 := by
        simp only [L_s, h1, and_self, dite_true]
      rw [hLs]
      by_contra hlt
      have hlt' : x.card < ((S.sort (· ≤ ·))[s - 1]'(h1.2)).val + 1 := by omega
      let f : Fin (s - 1) → Fin n := fun i => (S.sort (· ≤ ·))[i.val]'(by omega)
      have hsub : S.filter (fun r => r.val + 1 ≤ x.card) ⊆ Finset.univ.image f := by
        intro r hr
        rw [Finset.mem_filter] at hr
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp ((Finset.mem_sort (· ≤ ·)).mpr hr.1)
        have hidx_lt : idx < s - 1 := by
          by_contra hge
          have hmo := sort_fin_mono S h1.2 hidx (by omega)
          omega
        exact Finset.mem_image.mpr ⟨⟨idx, hidx_lt⟩, Finset.mem_univ _, rfl⟩
      have hcard := Finset.card_le_card hsub
      have hle2 : (Finset.univ.image f).card ≤ s - 1 := by
        calc (Finset.univ.image f).card ≤ (Finset.univ : Finset (Fin (s - 1))).card := Finset.card_image_le
          _ = s - 1 := by simp
      have : stg S x ≤ s - 1 := le_trans hcard hle2
      omega

theorem stg_le_iff_le_R_s {n : Nat} (S : Finset (Fin n)) (x : Finset (Fin n))
    (s : Nat) (hs : s ≤ S.card) :
    stg S x ≤ s ↔ x.card ≤ R_s S s := by
  have hlen : (S.sort (· ≤ ·)).length = S.card := Finset.length_sort (· ≤ ·)
  by_cases hlt : s < S.card
  · have h1 : s + 1 ≤ S.card := by omega
    have heq : L_s S (s + 1) = R_s S s + 1 := by
      have ha : 0 < s + 1 ∧ s + 1 - 1 < (S.sort (· ≤ ·)).length := ⟨by omega, by omega⟩
      have hb : s < (S.sort (· ≤ ·)).length := by omega
      simp only [L_s, R_s, ha, hb, and_self, dite_true, Nat.add_sub_cancel]
    have hiff := L_s_le_iff_le_stg S x (s + 1) h1
    rw [heq] at hiff
    omega
  · have heq : s = S.card := by omega
    subst heq
    have hR : R_s S S.card = n := by simp [R_s, hlen]
    rw [hR]
    have h1 : stg S x ≤ S.card := stg_le_card S x
    have h2 : x.card ≤ n := by simpa using Finset.card_le_univ x
    simp [h1, h2]

theorem stg_eq_iff {n : Nat} (S : Finset (Fin n)) (x : Finset (Fin n))
    (s : Nat) (hs : s ≤ S.card) :
    stg S x = s ↔ L_s S s ≤ x.card ∧ x.card ≤ R_s S s := by
  have h1 := L_s_le_iff_le_stg S x s hs
  have h2 := stg_le_iff_le_R_s S x s hs
  omega

def valFalse (n p : Nat) (S : Finset (Fin n)) (c : Nat) : Bool :=
  if h : c < n then decide (⟨c, h⟩ ∈ S ∨ p ≤ c) else false

def valTrue (n p : Nat) (S : Finset (Fin n)) (c : Nat) : Bool :=
  decide (1 ≤ c) && (if h : c - 1 < n then decide (⟨c - 1, h⟩ ∉ S ∧ p ≤ c - 1) else false)

def termSig (n p : Nat) (S : Finset (Fin n)) (j : Fin n) (c : Nat) : Sig (n + 2) :=
  bor (if valFalse n p S c then countSig (omitCoords j) c else fun _ => false)
      (if valTrue n p S c then ban (coord j) (countSig (allCoords n) c) else fun _ => false)

def sliceSig (n p : Nat) (S : Finset (Fin n)) (s : Nat) (j : Fin n) : Sig (n + 2) :=
  orFold ((List.range (R_s S s + 1 - L_s S s)).map (fun d => termSig n p S j (L_s S s + d)))

theorem sliceSig_stg_enc {n p : Nat} (S : Finset (Fin n)) (x : Finset (Fin n)) (j : Fin n) :
    sliceSig n p S (stg S x) j (enc x) = F_S n p S x j := by
  set s := stg S x with hs_def
  have hs_le : s ≤ S.card := stg_le_card S x
  have hbounds := (stg_eq_iff S x s hs_le).mp rfl
  have hLR : L_s S s ≤ R_s S s := L_s_le_R_s S s hs_le
  have hk_lt : (x.erase j).card < n := erase_card_lt x j
  have hlen : (S.sort (· ≤ ·)).length = S.card := Finset.length_sort (· ≤ ·)
  apply Bool.eq_iff_iff.mpr
  rw [sliceSig, orFold_eq_true]
  constructor
  · rintro ⟨f, hf, hfv⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hf
    have hd' : d < R_s S s + 1 - L_s S s := List.mem_range.mp hd
    set c := L_s S s + d with hc_def
    have hc_lo : L_s S s ≤ c := by omega
    have hc_hi : c ≤ R_s S s := by omega
    rw [F_S_eq_eval]
    simp only [termSig, bor, Bool.or_eq_true] at hfv
    rcases hfv with hA | hB
    · have hvf : valFalse n p S c = true := by
        cases h : valFalse n p S c <;> simp [h] at hA ⊢
      simp only [hvf, ite_true, countSig_omitCoords_enc, decide_eq_true_eq] at hA
      simp only [valFalse] at hvf
      have hc_lt : c < n := by
        by_contra hge
        simp only [hge, dite_false] at hvf
        simp at hvf
      simp only [hc_lt, dite_true, decide_eq_true_eq] at hvf
      by_cases hcR : c = R_s S s
      · have hsq : s < (S.sort (· ≤ ·)).length := by
          by_contra hge
          have : R_s S s = n := by simp only [R_s, hge, dite_false]
          omega
        have hRs_eq : R_s S s = ((S.sort (· ≤ ·))[s]'hsq).val := by simp only [R_s, hsq, dite_true]
        have hRs_mem : (⟨R_s S s, by omega⟩ : Fin n) ∈ S := by
          have : (⟨R_s S s, by omega⟩ : Fin n) = (S.sort (· ≤ ·))[s]'hsq := by
            ext; exact hRs_eq
          rw [this]
          exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hsq)
        have hcard_le : (x.erase j).card ≤ x.card := Finset.card_erase_le
        have hcard_eq : (x.erase j).card = x.card := by omega
        have hj_not : j ∉ x := by
          intro hjx
          have := Finset.card_erase_lt_of_mem hjx
          omega
        have hk_eq : (x.erase j).card = R_s S s := by omega
        have hk_mem : (⟨(x.erase j).card, hk_lt⟩ : Fin n) ∈ S := by
          have hfin : (⟨(x.erase j).card, hk_lt⟩ : Fin n) = ⟨R_s S s, by omega⟩ := by
            ext; exact hk_eq
          rw [hfin]
          exact hRs_mem
        simp only [hk_mem, ite_true, hj_not, not_false_eq_true, decide_true]
      · have hc_ltR : c < R_s S s := by omega
        have hc_notS : (⟨c, hc_lt⟩ : Fin n) ∉ S := fun hmem =>
          no_S_in_stage S s hs_le ⟨c, hc_lt⟩ hmem ⟨hc_lo, hc_ltR⟩
        have hpc : p ≤ c := hvf.resolve_left hc_notS
        have hpk : p ≤ (x.erase j).card := le_trans hpc hA
        by_cases hjx : j ∈ x
        · have hk_eq : (x.erase j).card = x.card - 1 := Finset.card_erase_of_mem hjx
          have hxpos : 1 ≤ x.card := Finset.card_pos.mpr ⟨j, hjx⟩
          have hk_ltR : (x.erase j).card < R_s S s := by omega
          have hk_notS : (⟨(x.erase j).card, hk_lt⟩ : Fin n) ∉ S := fun hmem =>
            no_S_in_stage S s hs_le ⟨(x.erase j).card, hk_lt⟩ hmem ⟨le_trans hc_lo hA, hk_ltR⟩
          simp [hk_notS, hpk]
        · split_ifs
          · simp [hjx]
          · simp [hpk]
    · have hvt : valTrue n p S c = true := by
        cases h : valTrue n p S c <;> simp [h] at hB ⊢
      simp only [hvt, ite_true] at hB
      simp only [ban, Bool.and_eq_true, coord_enc, countSig_allCoords_enc, decide_eq_true_eq] at hB
      rcases hB with ⟨hjx, hcx⟩
      simp only [valTrue, Bool.and_eq_true, decide_eq_true_eq] at hvt
      rcases hvt with ⟨hc1, hvt2⟩
      have hcm1_lt : c - 1 < n := by
        by_contra hge
        simp only [hge, dite_false] at hvt2
        simp at hvt2
      simp only [hcm1_lt, dite_true, decide_eq_true_eq] at hvt2
      rcases hvt2 with ⟨hcm1_notS, hpcm1⟩
      have hc_gtL : L_s S s < c := by
        by_contra hle
        have heqL : c = L_s S s := by omega
        by_cases hs0 : s = 0
        · have : L_s S s = 0 := by simp [L_s, hs0]
          omega
        · have h1 : 0 < s ∧ s - 1 < (S.sort (· ≤ ·)).length := ⟨by omega, by omega⟩
          have hLs : L_s S s = ((S.sort (· ≤ ·))[s - 1]'(h1.2)).val + 1 := by
            simp only [L_s, h1, and_self, dite_true]
          have hmem : (⟨c - 1, hcm1_lt⟩ : Fin n) ∈ S := by
            have : (⟨c - 1, hcm1_lt⟩ : Fin n) = (S.sort (· ≤ ·))[s - 1]'(h1.2) := by
              ext; dsimp only; omega
            rw [this]
            exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem h1.2)
          exact hcm1_notS hmem
      have hk_eq : (x.erase j).card = x.card - 1 := Finset.card_erase_of_mem hjx
      have hxpos : 1 ≤ x.card := Finset.card_pos.mpr ⟨j, hjx⟩
      have hk_lo : L_s S s ≤ (x.erase j).card := by omega
      have hk_hi : (x.erase j).card < R_s S s := by omega
      have hk_notS : (⟨(x.erase j).card, hk_lt⟩ : Fin n) ∉ S := fun hmem =>
        no_S_in_stage S s hs_le ⟨(x.erase j).card, hk_lt⟩ hmem ⟨hk_lo, hk_hi⟩
      have hpk : p ≤ (x.erase j).card := by omega
      simp [hk_notS, hpk]
  · intro hF
    rw [F_S_eq_eval] at hF
    refine ⟨termSig n p S j x.card, ?_, ?_⟩
    · refine List.mem_map.mpr ⟨x.card - L_s S s, List.mem_range.mpr (by omega), ?_⟩
      congr 1; omega
    · simp only [termSig, bor, Bool.or_eq_true]
      by_cases hjx : j ∈ x
      · right
        have hk_eq : (x.erase j).card = x.card - 1 := Finset.card_erase_of_mem hjx
        have hxpos : 1 ≤ x.card := Finset.card_pos.mpr ⟨j, hjx⟩
        have hk_notS : (⟨(x.erase j).card, hk_lt⟩ : Fin n) ∉ S := by
          intro hmem
          simp only [hmem, ite_true] at hF
          simp [hjx] at hF
        simp only [hk_notS, ite_false, decide_eq_true_eq] at hF
        have hcm1_lt : x.card - 1 < n := by omega
        have hcm1_notS : (⟨x.card - 1, hcm1_lt⟩ : Fin n) ∉ S := by
          have hfin : (⟨x.card - 1, hcm1_lt⟩ : Fin n) = ⟨(x.erase j).card, hk_lt⟩ := by
            ext; exact hk_eq.symm
          rw [hfin]
          exact hk_notS
        have hvt : valTrue n p S x.card = true := by
          simp [valTrue, hxpos, hcm1_lt, hcm1_notS, hk_eq ▸ hF]
        simp [hvt, ban, coord_enc, countSig_allCoords_enc, hjx]
      · left
        have heq_er : x.erase j = x := Finset.erase_eq_of_notMem hjx
        have hx_lt : x.card < n := by simpa [heq_er] using hk_lt
        have hdisj : (⟨x.card, hx_lt⟩ : Fin n) ∈ S ∨ p ≤ x.card := by
          by_cases hmem : (⟨(x.erase j).card, hk_lt⟩ : Fin n) ∈ S
          · left
            have hfin : (⟨x.card, hx_lt⟩ : Fin n) = ⟨(x.erase j).card, hk_lt⟩ := by
              ext; simp [heq_er]
            rw [hfin]
            exact hmem
          · right
            simp only [hmem, ite_false, decide_eq_true_eq] at hF
            simpa [heq_er] using hF
        have hvf : valFalse n p S x.card = true := by
          simp [valFalse, hx_lt, hdisj]
        simp [hvf, countSig_omitCoords_enc, heq_er]

theorem bound_gates (n q t : Nat) (hq : q ≤ n) (ht : t ≤ 8 * n) :
    2 + n * (n * 2) + n * (n * (n * 2)) + t + (q + 1) * 1 +
      n * ((n + 1) * 2) + n * ((q + 1) * (n + 1)) + n * ((q + 1) * 2) ≤ 32 * (n + 1) ^ 3 := by
  have hq1 : (q + 1) * 1 ≤ (n + 1) * 1 := by omega
  have hq2 : n * ((q + 1) * (n + 1)) ≤ n * ((n + 1) * (n + 1)) :=
    Nat.mul_le_mul_left n (Nat.mul_le_mul_right (n + 1) (by omega))
  have hq3 : n * ((q + 1) * 2) ≤ n * ((n + 1) * 2) :=
    Nat.mul_le_mul_left n (Nat.mul_le_mul_right 2 (by omega))
  have hid : 32 * (n + 1) ^ 3 =
      (2 + n * (n * 2) + n * (n * (n * 2)) + 8 * n + (n + 1) * 1 +
        n * ((n + 1) * 2) + n * ((n + 1) * (n + 1)) + n * ((n + 1) * 2)) +
      (29 * n ^ 3 + 88 * n ^ 2 + 82 * n + 29) := by ring
  omega

theorem circuit_of_set {n b p : Nat} (S : Finset (Fin n)) (hScard : S.card ≤ 2 ^ b - 1) :
    ∃ (C : Circuit) (a : Fin n → Fin (n + 2 + C.size)),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
      notCount C ≤ b ∧ C.size ≤ 32 * (n + 1) ^ 3 ∧
      ∀ (x : Finset (Fin n)) (j : Fin n),
        (C.wires (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true])).getD (a j).val false =
          F_S n p S x j := by
  let rs := S.sort (· ≤ ·)
  have hq_eq : rs.length = S.card := Finset.length_sort (· ≤ ·)
  set q := S.card with hq_def
  have hq_le_n : q ≤ n := by simpa using Finset.card_le_univ S
  let A0 : Set (Sig (n + 2)) := Set.range (fun i : Fin (n + 2) => (fun v : Fin (n + 2) → Bool => v i))
  have HS0 : GateBridgeN.Scheduled (n + 2) id 0 0 A0 :=
    GateBridgeN.start (fun i : Fin (n + 2) => (fun v : Fin (n + 2) → Bool => v i)) (fun _ _ => rfl)
  have hcoord_in_A0 : ∀ j : Fin n, coord j ∈ A0 := fun j => ⟨⟨j.val, by omega⟩, rfl⟩
  have HcF : BuildN A0 {fun _ => false} 1 0 := constG false
  have HcT : BuildN (A0 ∪ {fun _ => false}) {fun _ => true} 1 0 := constG true
  have Hconst : BuildN A0 ({fun _ => false} ∪ {fun _ => true}) 2 0 := seq HcF HcT
  let A1 : Set (Sig (n + 2)) := A0 ∪ ({fun _ => false} ∪ {fun _ => true})
  have hF1 : (fun _ => false) ∈ A1 := Or.inr (Or.inl rfl)
  have hT1 : (fun _ => true) ∈ A1 := Or.inr (Or.inr rfl)
  have hcoord1 : ∀ j : Fin n, coord j ∈ A1 := fun j => Or.inl (hcoord_in_A0 j)
  have HallC : BuildN A1 {f | ∃ c ≤ n, f = countSig (allCoords n) c} ((allCoords n).length * (n * 2)) 0 :=
    buildCount n (allCoords n) hT1 hF1 (fun f hf => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf
      exact hcoord1 j)
  have HallC_len : (allCoords n).length = n := by simp [allCoords]
  rw [HallC_len] at HallC
  let B_all : Set (Sig (n + 2)) := {f | ∃ c ≤ n, f = countSig (allCoords n) c}
  let A2 : Set (Sig (n + 2)) := A1 ∪ B_all
  have Homit_each : ∀ j : Fin n,
      BuildN A2 {f | ∃ c ≤ n, f = countSig (omitCoords j) c} (n * (n * 2)) 0 := by
    intro j
    have h := buildCount (A := A2) n (omitCoords j) (Or.inl hT1) (Or.inl hF1) (fun f hf => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
      exact Or.inl (hcoord1 i))
    have hlen_le : (omitCoords j).length ≤ n := by
      calc (omitCoords j).length = ((List.finRange n).filter (fun i => decide (i ≠ j))).length := by simp [omitCoords]
        _ ≤ (List.finRange n).length := List.length_filter_le _ _
        _ = n := List.length_finRange
    exact relax h le_rfl le_rfl (Nat.mul_le_mul_right _ hlen_le) le_rfl
  have Homit_all : BuildN A2 {f | ∃ j : Fin n, ∃ c ≤ n, f = countSig (omitCoords j) c}
      (n * (n * (n * 2))) 0 := by
    have haux : ∀ l : List (Fin n),
        BuildN A2 {f | ∃ j ∈ l, ∃ c ≤ n, f = countSig (omitCoords j) c} (l.length * (n * (n * 2))) 0 := by
      intro l
      induction l with
      | nil =>
        exact relax (idle (A := A2) (B := ∅) (by simp)) le_rfl (by simp) (by simp) le_rfl
      | cons j ls ih =>
        have h1 := Homit_each j
        have h2 := relax ih (C := A2 ∪ {f | ∃ c ≤ n, f = countSig (omitCoords j) c})
          Set.subset_union_left le_rfl le_rfl le_rfl
        refine relax (seq h1 h2) le_rfl ?_ ?_ (by simp)
        · rintro f ⟨i, hi, c, hc, rfl⟩
          rcases List.mem_cons.mp hi with rfl | hi
          · exact Or.inl ⟨c, hc, rfl⟩
          · exact Or.inr ⟨i, hi, c, hc, rfl⟩
        · simp only [List.length_cons, Nat.succ_mul]
          omega
    have hfin := haux (List.finRange n)
    rw [List.length_finRange] at hfin
    refine relax hfin le_rfl ?_ le_rfl le_rfl
    rintro f ⟨j, c, hc, rfl⟩
    exact ⟨j, List.mem_finRange j, c, hc, rfl⟩
  let B_omit : Set (Sig (n + 2)) := {f | ∃ j : Fin n, ∃ c ≤ n, f = countSig (omitCoords j) c}
  let A3 : Set (Sig (n + 2)) := A2 ∪ B_omit
  let r0 : Nat := if q = 0 then 0 else Nat.log 2 q + 1
  have hr0_le_b : r0 ≤ b := by
    by_cases hq0 : q = 0
    · simp [r0, hq0]
    · simp only [r0, hq0, ite_false]
      have hq_lt : q < 2 ^ b := by
        have h1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
        omega
      have hlog : Nat.log 2 q < b := Nat.log_lt_of_lt_pow hq0 hq_lt
      omega
  have hq_le_pow : q ≤ 2 ^ r0 - 1 := by
    by_cases hq0 : q = 0
    · simp [r0, hq0]
    · simp only [r0, hq0, ite_false]
      have := Nat.lt_pow_succ_log_self (by omega : 1 < 2) q
      omega
  have hTr0_le : T r0 ≤ 8 * n := by
    have hadd := T_add r0
    by_cases hq0 : q = 0
    · simp [r0, hq0, T]
    · simp only [r0, hq0, ite_false] at hadd ⊢
      have hpow : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 hq0
      have h2 : 2 ^ (Nat.log 2 q + 1) = 2 * 2 ^ Nat.log 2 q := by rw [pow_succ]; omega
      omega
  let uSig : Nat → Sig (n + 2) := fun t =>
    if h : t < q then countSig (allCoords n) ((rs[q - 1 - t]'(by omega)).val + 1)
    else fun _ => true
  have hu_in_A3 : ∀ t < 2 ^ r0 - 1, uSig t ∈ A3 := by
    intro t _
    simp only [uSig]
    split_ifs with h
    · exact Or.inl (Or.inr ⟨(rs[q - 1 - t]'(by omega)).val + 1,
        Nat.succ_le_of_lt (rs[q - 1 - t]'(by omega)).isLt, rfl⟩)
    · exact Or.inl (Or.inl hT1)
  obtain ⟨nu, Hinv, hnu⟩ := inverter r0 A3 uSig hu_in_A3
  have hsrt_u : ∀ v : Fin (n + 2) → Bool, Srt (2 ^ r0 - 1) uSig v := by
    intro v i j hij _ hi
    have hlen_rs : (S.sort (· ≤ ·)).length = q := hq_eq
    simp only [uSig] at hi ⊢
    by_cases hjq : j < q
    · have hiq : i < q := by omega
      simp only [hiq, hjq, dite_true, countSig, decide_eq_true_eq] at hi ⊢
      have hmo := sort_fin_mono S (by omega : q - 1 - j < (S.sort (· ≤ ·)).length)
        (by omega : q - 1 - i < (S.sort (· ≤ ·)).length) (by omega)
      dsimp only [rs] at hi ⊢
      omega
    · simp only [hjq, dite_false]
  let B_inv : Set (Sig (n + 2)) := {f | ∃ t < 2 ^ r0 - 1, f = nu t}
  let A4 : Set (Sig (n + 2)) := A3 ∪ B_inv
  let loSig : Nat → Sig (n + 2) := fun s =>
    if h : 0 < s ∧ s - 1 < q then countSig (allCoords n) ((rs[s - 1]'(by omega)).val + 1)
    else fun _ => true
  let hiSig : Nat → Sig (n + 2) := fun s =>
    if h : s < q then nu (q - 1 - s) else fun _ => true
  let isStgSig : Nat → Sig (n + 2) := fun s => ban (loSig s) (hiSig s)
  have HisStg : BuildN A4 {f | ∃ s < q + 1, f = isStgSig s} ((q + 1) * 1) ((q + 1) * 0) :=
    rangeBuild (q + 1) isStgSig 1 0 (fun s _ => by
      refine andG ?_ ?_
      · simp only [loSig]
        split_ifs with h
        · exact Or.inl (Or.inl (Or.inr ⟨(rs[s - 1]'(by omega)).val + 1,
            Nat.succ_le_of_lt (rs[s - 1]'(by omega)).isLt, rfl⟩))
        · exact Or.inl (Or.inl (Or.inl hT1))
      · simp only [hiSig]
        split_ifs with h
        · exact Or.inr ⟨q - 1 - s, by omega, rfl⟩
        · exact Or.inl (Or.inl (Or.inl hT1)))
  have hisStg_enc : ∀ s ≤ q, ∀ x : Finset (Fin n),
      isStgSig s (enc x) = decide (stg S x = s) := by
    intro s hs x
    have hlen_rs : (S.sort (· ≤ ·)).length = q := hq_eq
    have hlo : loSig s (enc x) = decide (L_s S s ≤ x.card) := by
      simp only [loSig, L_s]
      split_ifs with h1 h2 h2
      · rw [countSig_allCoords_enc]
      · omega
      · omega
      · simp
    have hhi : hiSig s (enc x) = decide (x.card ≤ R_s S s) := by
      simp only [hiSig, R_s]
      split_ifs with h1 h2 h2
      · rw [hnu (enc x) (hsrt_u (enc x)) (q - 1 - s) (by omega)]
        have hlt : q - 1 - s < q := by omega
        simp only [uSig, hlt, dite_true]
        have hidx : q - 1 - (q - 1 - s) = s := by omega
        have hcast : (rs[q - 1 - (q - 1 - s)]'(by omega)).val = ((S.sort (· ≤ ·))[s]'h2).val := by
          dsimp only [rs]; congr 2
        rw [hcast, countSig_allCoords_enc]
        by_cases hle : x.card ≤ ((S.sort (· ≤ ·))[s]'h2).val
        · have hnot : ¬ (((S.sort (· ≤ ·))[s]'h2).val + 1 ≤ x.card) := by omega
          simp [hle, hnot]
        · have hge : ((S.sort (· ≤ ·))[s]'h2).val + 1 ≤ x.card := by omega
          simp [hle, hge]
      · omega
      · omega
      · have hxn : x.card ≤ n := by simpa using Finset.card_le_univ x
        simp [hxn]
    simp only [isStgSig, ban, hlo, hhi]
    rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq]
    exact (stg_eq_iff S x s hs).symm
  let B_stg : Set (Sig (n + 2)) := {f | ∃ s < q + 1, f = isStgSig s}
  let A5 : Set (Sig (n + 2)) := A4 ∪ B_stg
  have Hterm_one : ∀ j : Fin n, ∀ c < n + 1, BuildN A5 {termSig n p S j c} 2 0 := by
    intro j c hc
    have hc_le : c ≤ n := by omega
    have h1 : BuildN A5 {ban (coord j) (countSig (allCoords n) c)} 1 0 :=
      andG (Or.inl (Or.inl (Or.inl (Or.inl (hcoord1 j)))))
           (Or.inl (Or.inl (Or.inl (Or.inr ⟨c, hc_le, rfl⟩))))
    have h2 : BuildN (A5 ∪ {ban (coord j) (countSig (allCoords n) c)}) {termSig n p S j c} 1 0 := by
      refine orG ?_ ?_
      · split_ifs
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j, c, hc_le, rfl⟩)))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hF1))))
      · split_ifs
        · exact Or.inr rfl
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hF1))))
    exact relax (seq h1 h2) le_rfl (fun _ hz => Or.inr hz) le_rfl le_rfl
  have Hterm_j : ∀ j : Fin n,
      BuildN A5 {f | ∃ c < n + 1, f = termSig n p S j c} ((n + 1) * 2) 0 := by
    intro j
    simpa using rangeBuild (n + 1) (termSig n p S j) 2 0 (Hterm_one j)
  have Hterm_all : BuildN A5 {f | ∃ j : Fin n, ∃ c < n + 1, f = termSig n p S j c}
      (n * ((n + 1) * 2)) 0 := by
    have haux : ∀ l : List (Fin n),
        BuildN A5 {f | ∃ j ∈ l, ∃ c < n + 1, f = termSig n p S j c} (l.length * ((n + 1) * 2)) 0 := by
      intro l
      induction l with
      | nil => exact relax (idle (A := A5) (B := ∅) (by simp)) le_rfl (by simp) (by simp) le_rfl
      | cons j ls ih =>
        have h1 := Hterm_j j
        have h2 := relax ih (C := A5 ∪ {f | ∃ c < n + 1, f = termSig n p S j c})
          Set.subset_union_left le_rfl le_rfl le_rfl
        refine relax (seq h1 h2) le_rfl ?_ ?_ (by simp)
        · rintro f ⟨i, hi, c, hc, rfl⟩
          rcases List.mem_cons.mp hi with rfl | hi
          · exact Or.inl ⟨c, hc, rfl⟩
          · exact Or.inr ⟨i, hi, c, hc, rfl⟩
        · simp only [List.length_cons, Nat.succ_mul]; omega
    have hfin := haux (List.finRange n)
    rw [List.length_finRange] at hfin
    refine relax hfin le_rfl ?_ le_rfl le_rfl
    rintro f ⟨j, c, hc, rfl⟩
    exact ⟨j, List.mem_finRange j, c, hc, rfl⟩
  let B_term : Set (Sig (n + 2)) := {f | ∃ j : Fin n, ∃ c < n + 1, f = termSig n p S j c}
  let A6 : Set (Sig (n + 2)) := A5 ∪ B_term
  have Hslice_one : ∀ j : Fin n, ∀ s < q + 1, BuildN A6 {sliceSig n p S s j} (n + 1) 0 := by
    intro j s hs
    have hlen_le : ((List.range (R_s S s + 1 - L_s S s)).map
        (fun d => termSig n p S j (L_s S s + d))).length ≤ n + 1 := by
      simp only [List.length_map, List.length_range]
      have := R_s_le_n S s
      omega
    have hmem : ∀ f ∈ (List.range (R_s S s + 1 - L_s S s)).map
        (fun d => termSig n p S j (L_s S s + d)), f ∈ A6 := by
      intro f hf
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hf
      have hd' : d < R_s S s + 1 - L_s S s := List.mem_range.mp hd
      have hRn := R_s_le_n S s
      have hLR := L_s_le_R_s S s (by omega)
      exact Or.inr ⟨j, L_s S s + d, by omega, rfl⟩
    exact relax (buildOrFold _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hF1))))) hmem)
      le_rfl le_rfl hlen_le le_rfl
  have Hslice_all : BuildN A6 {f | ∃ j : Fin n, ∃ s < q + 1, f = sliceSig n p S s j}
      (n * ((q + 1) * (n + 1))) 0 := by
    have haux : ∀ l : List (Fin n),
        BuildN A6 {f | ∃ j ∈ l, ∃ s < q + 1, f = sliceSig n p S s j}
          (l.length * ((q + 1) * (n + 1))) 0 := by
      intro l
      induction l with
      | nil => exact relax (idle (A := A6) (B := ∅) (by simp)) le_rfl (by simp) (by simp) le_rfl
      | cons j ls ih =>
        have h1 : BuildN A6 {f | ∃ s < q + 1, f = sliceSig n p S s j} ((q + 1) * (n + 1)) 0 := by
          simpa using rangeBuild (q + 1) (fun s => sliceSig n p S s j) (n + 1) 0 (Hslice_one j)
        have h2 := relax ih (C := A6 ∪ {f | ∃ s < q + 1, f = sliceSig n p S s j})
          Set.subset_union_left le_rfl le_rfl le_rfl
        refine relax (seq h1 h2) le_rfl ?_ ?_ (by simp)
        · rintro f ⟨i, hi, s, hs, rfl⟩
          rcases List.mem_cons.mp hi with rfl | hi
          · exact Or.inl ⟨s, hs, rfl⟩
          · exact Or.inr ⟨i, hi, s, hs, rfl⟩
        · simp only [List.length_cons, Nat.succ_mul]; omega
    have hfin := haux (List.finRange n)
    rw [List.length_finRange] at hfin
    refine relax hfin le_rfl ?_ le_rfl le_rfl
    rintro f ⟨j, s, hs, rfl⟩
    exact ⟨j, List.mem_finRange j, s, hs, rfl⟩
  let B_slice : Set (Sig (n + 2)) := {f | ∃ j : Fin n, ∃ s < q + 1, f = sliceSig n p S s j}
  let A7 : Set (Sig (n + 2)) := A6 ∪ B_slice
  let outSig : Fin n → Sig (n + 2) := fun j =>
    orFold ((List.range (q + 1)).map (fun s => ban (isStgSig s) (sliceSig n p S s j)))
  have Hout_j : ∀ j : Fin n, BuildN A7 {outSig j} ((q + 1) * 2) 0 := by
    intro j
    have h1 : BuildN A7 {f | ∃ s < q + 1, f = ban (isStgSig s) (sliceSig n p S s j)}
        ((q + 1) * 1) 0 := by
      simpa using rangeBuild (q + 1) (fun s => ban (isStgSig s) (sliceSig n p S s j)) 1 0
        (fun s hs => andG (Or.inl (Or.inl (Or.inr ⟨s, hs, rfl⟩))) (Or.inr ⟨j, s, hs, rfl⟩))
    have h2 : BuildN (A7 ∪ {f | ∃ s < q + 1, f = ban (isStgSig s) (sliceSig n p S s j)})
        {outSig j} (q + 1) 0 := by
      have hfold := buildOrFold (A := A7 ∪ {f | ∃ s < q + 1, f = ban (isStgSig s) (sliceSig n p S s j)})
        ((List.range (q + 1)).map (fun s => ban (isStgSig s) (sliceSig n p S s j)))
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hF1)))))))
        (fun f hf => by
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hf
          exact Or.inr ⟨s, List.mem_range.mp hs, rfl⟩)
      simpa [outSig] using hfold
    exact relax (seq h1 h2) le_rfl (fun _ hz => Or.inr hz) (by omega) (by simp)
  have Hout_all : BuildN A7 (Set.range outSig) (n * ((q + 1) * 2)) 0 :=
    by simpa using finG outSig ((q + 1) * 2) 0 Hout_j
  have Htot1 := seq Hconst HallC
  have Htot2 := seq Htot1 (relax Homit_all (C := A0 ∪ (({fun _ => false} ∪ {fun _ => true}) ∪ B_all))
    (fun z hz => by simp only [A1, A2, Set.mem_union] at hz ⊢; tauto) le_rfl le_rfl le_rfl)
  have Htot3 := seq Htot2 (relax Hinv (C := A0 ∪ ((({fun _ => false} ∪ {fun _ => true}) ∪ B_all) ∪ B_omit))
    (fun z hz => by simp only [A1, A2, A3, Set.mem_union] at hz ⊢; tauto) le_rfl le_rfl le_rfl)
  have Htot4 := seq Htot3 (relax HisStg (C := A0 ∪ (((({fun _ => false} ∪ {fun _ => true}) ∪ B_all) ∪ B_omit) ∪ B_inv))
    (fun z hz => by simp only [A1, A2, A3, A4, Set.mem_union] at hz ⊢; tauto) le_rfl le_rfl le_rfl)
  have Htot5 := seq Htot4 (relax Hterm_all (C := A0 ∪ ((((({fun _ => false} ∪ {fun _ => true}) ∪ B_all) ∪ B_omit) ∪ B_inv) ∪ B_stg))
    (fun z hz => by simp only [A1, A2, A3, A4, A5, Set.mem_union] at hz ⊢; tauto) le_rfl le_rfl le_rfl)
  have Htot6 := seq Htot5 (relax Hslice_all (C := A0 ∪ (((((({fun _ => false} ∪ {fun _ => true}) ∪ B_all) ∪ B_omit) ∪ B_inv) ∪ B_stg) ∪ B_term))
    (fun z hz => by simp only [A1, A2, A3, A4, A5, A6, Set.mem_union] at hz ⊢; tauto) le_rfl le_rfl le_rfl)
  have Htot7 := seq Htot6 (relax Hout_all (C := A0 ∪ ((((((({fun _ => false} ∪ {fun _ => true}) ∪ B_all) ∪ B_omit) ∪ B_inv) ∪ B_stg) ∪ B_term) ∪ B_slice))
    (fun z hz => by simp only [A1, A2, A3, A4, A5, A6, A7, Set.mem_union] at hz ⊢; tauto) le_rfl le_rfl le_rfl)
  obtain ⟨c, hc, cn, hcn, Hsched⟩ := Htot7.run HS0 le_rfl
  obtain ⟨gs, hgs, hnc, hrb, hfit, hw⟩ := Hsched
  have hbound_c : c ≤ 32 * (n + 1) ^ 3 :=
    le_trans hc (bound_gates n q (T r0) hq_le_n hTr0_le)
  have hnc_le : cn ≤ b := by omega
  have htap_ex : ∀ j : Fin n, ∃ idx : Fin (n + 2 + gs.length),
      ∀ v : Fin (n + 2) → Bool, ((Circuit.mk gs 0).wires (List.ofFn v)).getD idx.val false = outSig j v := by
    intro j
    have hmem : outSig j ∈ A0 ∪ (((((((({fun _ => false} ∪ {fun _ => true}) ∪ B_all) ∪ B_omit) ∪ B_inv) ∪ B_stg) ∪ B_term) ∪ B_slice) ∪ Set.range outSig) :=
      Or.inr (Or.inr ⟨j, rfl⟩)
    obtain ⟨idx, hidx, hval⟩ := hw (outSig j) hmem
    exact ⟨⟨idx, by omega⟩, hval⟩
  choose a ha using htap_ex
  refine ⟨⟨gs, 0⟩, a, hfit, hrb, by simp, ?_, ?_, ?_⟩
  · omega
  · change gs.length ≤ 32 * (n + 1) ^ 3; omega
  · intro x j
    rw [← ofFn_enc x, ha j (enc x)]
    have hout : outSig j (enc x) = sliceSig n p S (stg S x) j (enc x) := by
      apply Bool.eq_iff_iff.mpr
      dsimp only [outSig]
      rw [orFold_eq_true]
      constructor
      · rintro ⟨f, hf, hfv⟩
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hf
        have hs' : s ≤ q := by have := List.mem_range.mp hs; omega
        simp only [ban, Bool.and_eq_true, hisStg_enc s hs' x, decide_eq_true_eq] at hfv
        rw [hfv.1]; exact hfv.2
      · intro hval
        refine ⟨ban (isStgSig (stg S x)) (sliceSig n p S (stg S x) j), ?_, ?_⟩
        · exact List.mem_map.mpr ⟨stg S x, List.mem_range.mpr (by have := stg_le_card S x; omega), rfl⟩
        · simp [ban, hisStg_enc (stg S x) (stg_le_card S x) x, hval]
    rw [hout, sliceSig_stg_enc]

end Part1

namespace Part2

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.NotBracket (notCount)

def pref {n : Nat} (σ : Equiv.Perm (Fin n)) (k : Nat) : Finset (Fin n) :=
  (Finset.univ.filter (fun r : Fin n => r.val < k)).image σ

theorem pref_card {n : Nat} (σ : Equiv.Perm (Fin n)) {k : Nat} (hk : k ≤ n) :
    (pref σ k).card = k := by
  rw [pref, Finset.card_image_of_injective _ σ.injective]
  have heq : (Finset.univ.filter (fun r : Fin n => r.val < k)) =
      Finset.univ.image (fun i : Fin k => (⟨i.val, by omega⟩ : Fin n)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hr; exact ⟨⟨r.val, hr⟩, rfl⟩
    · rintro ⟨i, rfl⟩; exact i.isLt
  have hinj : Function.Injective (fun i : Fin k => (⟨i.val, by omega⟩ : Fin n)) := by
    intro a b hab
    exact Fin.ext (Fin.mk.inj hab)
  rw [heq, Finset.card_image_of_injective _ hinj]
  simp

theorem apply_not_mem_pref {n : Nat} (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    σ k ∉ pref σ k.val := by
  intro h
  obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp h
  have hr' : r.val < k.val := (Finset.mem_filter.mp hr).2
  have : r = k := σ.injective heq
  subst this
  omega

theorem insert_pref {n : Nat} (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    insert (σ k) (pref σ k.val) = pref σ (k.val + 1) := by
  ext x
  simp only [Finset.mem_insert, pref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨r, hr, rfl⟩)
    · exact ⟨k, by omega, rfl⟩
    · exact ⟨r, by omega, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with h | h
    · exact Or.inr ⟨r, h, rfl⟩
    · left; congr 1; exact Fin.ext h

theorem perm_fiber_card {n : Nat} (k : Fin n) (y : Finset (Fin n)) (hy : y.card = k.val)
    (j : Fin n) (hj : j ∉ y) :
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => pref σ k.val = y ∧ σ k = j)).card =
      k.val.factorial * (n - 1 - k.val).factorial := by
  let A : Finset (Fin n) := Finset.univ.filter (fun r : Fin n => r.val < k.val)
  let B : Finset (Fin n) := Finset.univ.filter (fun r : Fin n => k.val < r.val)
  let Z : Finset (Fin n) := Finset.univ \ insert j y
  have hAcard : A.card = k.val := by
    have := pref_card (Equiv.refl (Fin n)) (Nat.le_of_lt k.isLt)
    simpa [pref, A] using this
  have hBcard : B.card = n - 1 - k.val := by
    have hpart : A ∪ (insert k B) = Finset.univ := by
      ext r
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
        true_and, iff_true, A, B]
      have : r.val < k.val ∨ r.val = k.val ∨ k.val < r.val := by omega
      rcases this with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr h)
    have hd1 : Disjoint A (insert k B) := by
      rw [Finset.disjoint_left]
      intro r hrA hrB
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, A] at hrA
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, B] at hrB
      rcases hrB with rfl | hrB <;> omega
    have hkB : k ∉ B := by simp [B]
    have hsum : A.card + (B.card + 1) = n := by
      have h1 := Finset.card_union_of_disjoint hd1
      rw [hpart, Finset.card_univ, Fintype.card_fin, Finset.card_insert_of_notMem hkB] at h1
      omega
    omega
  have hZcard : Z.card = n - 1 - k.val := by
    have h1 : (insert j y).card = k.val + 1 := by
      rw [Finset.card_insert_of_notMem hj, hy]
    have h2 : Z.card = (Finset.univ : Finset (Fin n)).card - (insert j y).card :=
      Finset.card_sdiff_of_subset (Finset.subset_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    omega
  let S_perm := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => pref σ k.val = y ∧ σ k = j)
  let fwd : {σ // σ ∈ S_perm} → ({a // a ∈ A} ≃ {u // u ∈ y}) × ({b // b ∈ B} ≃ {z // z ∈ Z}) :=
    fun ⟨σ, hσ⟩ =>
      have hσ' : pref σ k.val = y ∧ σ k = j := (Finset.mem_filter.mp hσ).2
      have hAmap : ∀ a ∈ A, σ a ∈ y := fun a ha => by
        rw [← hσ'.1, pref]; exact Finset.mem_image_of_mem σ ha
      have hAinv : ∀ u ∈ y, σ.symm u ∈ A := fun u hu => by
        rw [← hσ'.1, pref] at hu
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
        simpa [A] using ha
      have hBmap : ∀ b ∈ B, σ b ∈ Z := fun b hb => by
        simp only [Z, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert]
        intro hmem
        have hb' : k.val < b.val := (Finset.mem_filter.mp hb).2
        rcases hmem with heq | hmem
        · have : b = k := σ.injective (heq.trans hσ'.2.symm)
          subst this; omega
        · have := hAinv (σ b) hmem
          simp only [Equiv.symm_apply_apply, A, Finset.mem_filter, Finset.mem_univ, true_and] at this
          omega
      have hBinv : ∀ z ∈ Z, σ.symm z ∈ B := fun z hz => by
        simp only [Z, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, not_or] at hz
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        by_contra hle
        rcases Nat.lt_or_eq_of_le (show (σ.symm z).val ≤ k.val by omega) with hlt | heq
        · have := hAmap (σ.symm z) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
          simp only [Equiv.apply_symm_apply] at this
          exact hz.2 this
        · have hsk : σ.symm z = k := Fin.ext heq
          have : z = j := by rw [← σ.apply_symm_apply z, hsk, hσ'.2]
          exact hz.1 this
      (⟨fun a => ⟨σ a.1, hAmap a.1 a.2⟩, fun u => ⟨σ.symm u.1, hAinv u.1 u.2⟩,
        fun a => Subtype.ext (σ.symm_apply_apply a.1), fun u => Subtype.ext (σ.apply_symm_apply u.1)⟩,
       ⟨fun b => ⟨σ b.1, hBmap b.1 b.2⟩, fun z => ⟨σ.symm z.1, hBinv z.1 z.2⟩,
        fun b => Subtype.ext (σ.symm_apply_apply b.1), fun z => Subtype.ext (σ.apply_symm_apply z.1)⟩)
  let bwd : ({a // a ∈ A} ≃ {u // u ∈ y}) × ({b // b ∈ B} ≃ {z // z ∈ Z}) → {σ // σ ∈ S_perm} :=
    fun ⟨e1, e2⟩ =>
      let toF : Fin n → Fin n := fun r =>
        if h1 : r.val < k.val then (e1 ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩).1
        else if h2 : r.val = k.val then j
        else (e2 ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩).1
      let invF : Fin n → Fin n := fun x =>
        if h1 : x ∈ y then (e1.symm ⟨x, h1⟩).1
        else if h2 : x = j then k
        else (e2.symm ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [h1, h2]⟩⟩).1
      have hleft : Function.LeftInverse invF toF := by
        intro r
        dsimp only [toF]
        split_ifs with h1 h2
        · dsimp only [invF]
          have hm := (e1 ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩).2
          rw [dite_eq_left_of_eq_true (eq_true hm)]
          exact congrArg Subtype.val (e1.symm_apply_apply _)
        · dsimp only [invF]
          rw [dite_eq_right_of_eq_false (eq_false hj), dite_eq_left_of_eq_true (eq_true rfl)]
          exact Fin.ext h2.symm
        · dsimp only [invF]
          have hm := (e2 ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩).2
          simp only [Z, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, not_or] at hm
          rw [dite_eq_right_of_eq_false (eq_false hm.2), dite_eq_right_of_eq_false (eq_false hm.1)]
          exact congrArg Subtype.val (e2.symm_apply_apply _)
      have hright : Function.RightInverse invF toF := by
        intro x
        dsimp only [invF]
        split_ifs with h1 h2
        · dsimp only [toF]
          have hm := (e1.symm ⟨x, h1⟩).2
          have hlt : (e1.symm ⟨x, h1⟩).1.val < k.val := (Finset.mem_filter.mp hm).2
          rw [dite_eq_left_of_eq_true (eq_true hlt)]
          exact congrArg Subtype.val (e1.apply_symm_apply _)
        · dsimp only [toF]
          rw [dite_eq_right_of_eq_false (eq_false (by omega)), dite_eq_left_of_eq_true (eq_true rfl)]
          exact h2.symm
        · dsimp only [toF]
          have hm := (e2.symm ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [h1, h2]⟩⟩).2
          have hgt : k.val < (e2.symm ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [h1, h2]⟩⟩).1.val :=
            (Finset.mem_filter.mp hm).2
          rw [dite_eq_right_of_eq_false (eq_false (by omega)), dite_eq_right_of_eq_false (eq_false (by omega))]
          exact congrArg Subtype.val (e2.apply_symm_apply _)
      let σ : Equiv.Perm (Fin n) := ⟨toF, invF, hleft, hright⟩
      have hσ_mem : σ ∈ S_perm := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · ext u
          simp only [pref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨r, hr, rfl⟩
            change toF r ∈ y
            simp only [toF, dite_eq_left_of_eq_true (eq_true hr)]
            exact (e1 _).2
          · intro hu
            refine ⟨(e1.symm ⟨u, hu⟩).1, (Finset.mem_filter.mp (e1.symm ⟨u, hu⟩).2).2, ?_⟩
            change toF (e1.symm ⟨u, hu⟩).1 = u
            simp only [toF, dite_eq_left_of_eq_true (eq_true (Finset.mem_filter.mp (e1.symm ⟨u, hu⟩).2).2)]
            exact congrArg Subtype.val (e1.apply_symm_apply ⟨u, hu⟩)
        · change toF k = j
          simp [toF]
      ⟨σ, hσ_mem⟩
  have heq_equiv : {σ // σ ∈ S_perm} ≃
      ({a // a ∈ A} ≃ {u // u ∈ y}) × ({b // b ∈ B} ≃ {z // z ∈ Z}) :=
    ⟨fwd, bwd, by
      intro ⟨σ, hσ⟩
      apply Subtype.ext
      ext r
      have hσ' : pref σ k.val = y ∧ σ k = j := (Finset.mem_filter.mp hσ).2
      simp only [fwd, bwd, Equiv.coe_fn_mk]
      split_ifs with h1 h2
      · rfl
      · rw [Fin.ext h2, hσ'.2]
      · rfl, by
      rintro ⟨e1, e2⟩
      apply Prod.ext
      · ext ⟨a, ha⟩
        have hlt : a.val < k.val := (Finset.mem_filter.mp ha).2
        simp only [fwd, bwd, Equiv.coe_fn_mk, hlt, dite_true]
      · ext ⟨b, hb⟩
        have hgt : k.val < b.val := (Finset.mem_filter.mp hb).2
        have hn1 : ¬ (b.val < k.val) := by omega
        have hn2 : ¬ (b.val = k.val) := by omega
        simp only [fwd, bwd, Equiv.coe_fn_mk, hn1, hn2, dite_false]⟩
  have hcard_eq : S_perm.card =
      Fintype.card ({a // a ∈ A} ≃ {u // u ∈ y}) * Fintype.card ({b // b ∈ B} ≃ {z // z ∈ Z}) := by
    rw [← Fintype.card_coe S_perm, Fintype.card_congr heq_equiv, Fintype.card_prod]
  have h1 : Fintype.card ({a // a ∈ A} ≃ {u // u ∈ y}) = k.val.factorial := by
    have hc : Fintype.card {a // a ∈ A} = Fintype.card {u // u ∈ y} := by
      simp [Fintype.card_coe, hAcard, hy]
    let e0 : {a // a ∈ A} ≃ {u // u ∈ y} := Fintype.equivOfCardEq hc
    have he : ({a // a ∈ A} ≃ {u // u ∈ y}) ≃ Equiv.Perm {a // a ∈ A} :=
      ⟨fun e => e.trans e0.symm, fun p => p.trans e0,
        fun e => by ext x; simp, fun p => by ext x; simp⟩
    rw [Fintype.card_congr he, Fintype.card_perm, Fintype.card_coe, hAcard]
  have h2 : Fintype.card ({b // b ∈ B} ≃ {z // z ∈ Z}) = (n - 1 - k.val).factorial := by
    have hc : Fintype.card {b // b ∈ B} = Fintype.card {z // z ∈ Z} := by
      simp [Fintype.card_coe, hBcard, hZcard]
    let e0 : {b // b ∈ B} ≃ {z // z ∈ Z} := Fintype.equivOfCardEq hc
    have he : ({b // b ∈ B} ≃ {z // z ∈ Z}) ≃ Equiv.Perm {b // b ∈ B} :=
      ⟨fun e => e.trans e0.symm, fun p => p.trans e0,
        fun e => by ext x; simp, fun p => by ext x; simp⟩
    rw [Fintype.card_congr he, Fintype.card_perm, Fintype.card_coe, hBcard]
  rw [hcard_eq, h1, h2]

theorem perm_sum_good_eq {n : Nat} (g : Finset (Fin n) → Fin n → Nat) (k : Fin n) :
    (Finset.univ : Finset (Equiv.Perm (Fin n))).sum (fun σ => g (pref σ k.val) (σ k)) =
      k.val.factorial * (n - 1 - k.val).factorial *
        ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k.val)).sum (fun y =>
          ((Finset.univ : Finset (Fin n)) \ y).sum (fun j => g y j)) := by
  have hpart1 : (Finset.univ : Finset (Equiv.Perm (Fin n))).sum (fun σ => g (pref σ k.val) (σ k)) =
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k.val)).sum (fun y =>
        ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => pref σ k.val = y)).sum
          (fun σ => g (pref σ k.val) (σ k))) := by
    have hdisj : Set.PairwiseDisjoint
        (((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k.val)) : Set (Finset (Fin n)))
        (fun y => (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => pref σ k.val = y)) := by
      intro y1 _ y2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro σ h1 h2
      have h1' := (Finset.mem_filter.mp h1).2
      have h2' := (Finset.mem_filter.mp h2).2
      exact hne (h1'.symm.trans h2')
    rw [← Finset.sum_biUnion hdisj]
    congr 1
    ext σ
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, true_iff]
    exact ⟨pref σ k.val, pref_card σ (Nat.le_of_lt k.isLt), rfl⟩
  have hpart2 : ∀ y ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k.val),
      ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => pref σ k.val = y)).sum
        (fun σ => g (pref σ k.val) (σ k)) =
      ((Finset.univ : Finset (Fin n)) \ y).sum (fun j =>
        ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => pref σ k.val = y ∧ σ k = j)).sum
          (fun σ => g (pref σ k.val) (σ k))) := by
    intro y _
    have hdisj : Set.PairwiseDisjoint ((((Finset.univ : Finset (Fin n)) \ y) : Finset (Fin n)) : Set (Fin n))
        (fun j => (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => pref σ k.val = y ∧ σ k = j)) := by
      intro j1 _ j2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro σ h1 h2
      have h1' := (Finset.mem_filter.mp h1).2.2
      have h2' := (Finset.mem_filter.mp h2).2.2
      exact hne (h1'.symm.trans h2')
    rw [← Finset.sum_biUnion hdisj]
    congr 1
    ext σ
    simp only [Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and]
    constructor
    · intro hp
      exact ⟨σ k, by rw [← hp]; exact apply_not_mem_pref σ k, hp, rfl⟩
    · rintro ⟨_, _, hp, _⟩
      exact hp
  rw [hpart1, Finset.sum_congr rfl hpart2, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hy' : y.card = k.val := (Finset.mem_filter.mp hy).2
  have hj' : j ∉ y := (Finset.mem_sdiff.mp hj).2
  have hcongr : ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => pref σ k.val = y ∧ σ k = j)).sum
      (fun σ => g (pref σ k.val) (σ k)) =
      ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => pref σ k.val = y ∧ σ k = j)).sum
        (fun _ => g y j) := by
    refine Finset.sum_congr rfl (fun σ hσ => ?_)
    have hσ' := (Finset.mem_filter.mp hσ).2
    rw [hσ'.1, hσ'.2]
  rw [hcongr, Finset.sum_const, smul_eq_mul, perm_fiber_card k y hy' j hj']

theorem mark_eq_notCount (C : Circuit) :
    (C.gates.filter InversionRank.mark).length = notCount C := by
  dsimp only [notCount]
  congr 1
  induction C.gates with
  | nil => rfl
  | cons g gs ih =>
    cases h : g.op <;> simp [InversionRank.mark, h, ih]

theorem chain_good_le {n b : Nat} (C : Circuit) (a : Fin n → Fin (n + 2 + C.size))
    (hfit : FanInTwo C) (hnc : notCount C ≤ b) (σ : Equiv.Perm (Fin n)) :
    (Finset.univ : Finset (Fin n)).sum (fun k =>
      if (C.wires (List.ofFn (fun i : Fin n => decide (i ∈ pref σ k.val)) ++ [false, true])).getD (a (σ k)).val false = true ∧
         (C.wires (List.ofFn (fun i : Fin n => decide (i ∈ insert (σ k) (pref σ k.val))) ++ [false, true])).getD (a (σ k)).val false = false
      then (1 : Nat) else 0) ≤ 2 ^ b - 1 := by
  have hops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    intro g hg
    have h := (hfit g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    exact h
  let inp (k : Nat) : List Bool :=
    List.ofFn (fun i : Fin n => decide (i ∈ pref σ k)) ++ [false, true]
  let d (k : Nat) : Nat :=
    InversionRank.driverNumber (InversionRank.code C.gates (inp k))
  have hord : ∀ k : Fin n, InversionRank.ordered (inp k.val) (inp (k.val + 1)) := by
    intro k
    refine InversionRank.input_order (fun i hi => ?_)
    rw [decide_eq_true_eq] at hi ⊢
    rw [← insert_pref σ k]
    exact Finset.mem_insert_of_mem hi
  have hstep : ∀ k : Fin n,
      d k.val + (if (C.wires (inp k.val)).getD (a (σ k)).val false = true ∧
                    (C.wires (inp (k.val + 1))).getD (a (σ k)).val false = false
                 then (1 : Nat) else 0) ≤ d (k.val + 1) := by
    intro k
    have hmono : d k.val ≤ d (k.val + 1) :=
      InversionRank.driver_mono C.gates hops (hord k)
    split_ifs with hgood
    · have hne : d k.val ≠ d (k.val + 1) := by
        intro heq
        have hlen : (InversionRank.code C.gates (inp k.val)).length =
            (InversionRank.code C.gates (inp (k.val + 1))).length := by
          simp [InversionRank.code_len]
        have hcode := InversionRank.driver_injective hlen heq
        have hout := InversionRank.output_order hops (hord k) hcode
        have htrue : (C.wires (inp (k.val + 1))).getD (a (σ k)).val false = true :=
          hout.2 (a (σ k)).val hgood.1
        rw [hgood.2] at htrue
        simp at htrue
      omega
    · omega
  have htele : ∀ m ≤ n,
      d 0 + (Finset.range m).sum (fun k =>
        if h : k < n then
          if (C.wires (inp k)).getD (a (σ ⟨k, h⟩)).val false = true ∧
             (C.wires (inp (k + 1))).getD (a (σ ⟨k, h⟩)).val false = false
          then (1 : Nat) else 0
        else 0) ≤ d m := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, dite_eq_left_of_eq_true (eq_true (by omega : m < n))]
      have h1 := ih (by omega)
      have h2 := hstep ⟨m, by omega⟩
      dsimp only at h2
      omega
  have hsum_eq : (Finset.univ : Finset (Fin n)).sum (fun k =>
      if (C.wires (List.ofFn (fun i : Fin n => decide (i ∈ pref σ k.val)) ++ [false, true])).getD (a (σ k)).val false = true ∧
         (C.wires (List.ofFn (fun i : Fin n => decide (i ∈ insert (σ k) (pref σ k.val))) ++ [false, true])).getD (a (σ k)).val false = false
      then (1 : Nat) else 0) =
      (Finset.range n).sum (fun k =>
        if h : k < n then
          if (C.wires (inp k)).getD (a (σ ⟨k, h⟩)).val false = true ∧
             (C.wires (inp (k + 1))).getD (a (σ ⟨k, h⟩)).val false = false
          then (1 : Nat) else 0
        else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k =>
      if h : k < n then
        if (C.wires (inp k)).getD (a (σ ⟨k, h⟩)).val false = true ∧
           (C.wires (inp (k + 1))).getD (a (σ ⟨k, h⟩)).val false = false
        then (1 : Nat) else 0
      else 0) n]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Fin.eta, k.isLt, dite_true, inp, insert_pref]
  have hbd : d n < 2 ^ b := by
    have h1 : d n < 2 ^ (InversionRank.code C.gates (inp n)).length := InversionRank.driver_bound _
    rw [InversionRank.code_len, mark_eq_notCount] at h1
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) hnc)
  have htn := htele n le_rfl
  rw [hsum_eq]
  omega

theorem choose_fact_identity {n k : Nat} (hk : k < n) :
    (n - k) * Nat.choose n k * (k.factorial * (n - 1 - k).factorial) = n.factorial := by
  have hsub : n - k = (n - 1 - k) + 1 := by omega
  have hfac : (n - k) * (n - 1 - k).factorial = (n - k).factorial := by
    rw [hsub, Nat.factorial_succ]
  calc (n - k) * Nat.choose n k * (k.factorial * (n - 1 - k).factorial)
      = Nat.choose n k * k.factorial * ((n - k) * (n - 1 - k).factorial) := by ring
    _ = Nat.choose n k * k.factorial * (n - k).factorial := by rw [hfac]
    _ = n.factorial := Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt hk)

end Part2

namespace Part3

theorem deal_intervals {n b M : Nat} (hM : 1 ≤ M) (Q : Nat → Nat)
    (hQle : ∀ k < n, Q k ≤ M)
    (hQsum : (Finset.range n).sum Q ≤ M * (2 ^ b - 1)) :
    ∃ (m : Fin (n + 1) → Nat) (S : Fin (n + 1) → Finset (Fin n)),
      (∀ i, (S i).card ≤ 2 ^ b - 1) ∧
      (Finset.univ : Finset (Fin (n + 1))).sum m = M ∧
      (∀ k : Fin n, (Finset.univ : Finset (Fin (n + 1))).sum (fun i => m i * (if k ∈ S i then 1 else 0)) = Q k.val) ∧
      (∀ k : Fin n, (Finset.univ : Finset (Fin (n + 1))).sum (fun i => m i * (if k ∈ S i then 0 else 1)) = M - Q k.val) := by
  have hMpos : 0 < M := by omega
  let P : Nat → Nat := fun k => (Finset.range k).sum Q
  have hP0 : P 0 = 0 := by simp [P]
  have hPsucc : ∀ k, P (k + 1) = P k + Q k := fun k => Finset.sum_range_succ Q k
  have hPmono : ∀ a c, a ≤ c → P a ≤ P c := fun a c hac =>
    Finset.sum_le_sum_of_subset (Finset.range_mono hac)
  let assign : Fin M → Finset (Fin n) := fun z =>
    @Finset.filter (Fin n) (fun k : Fin n => ∃ q : Nat, P k.val ≤ z.val + q * M ∧ z.val + q * M < P (k.val + 1))
      (fun _ => Classical.propDecidable _) Finset.univ
  have hassign_card : ∀ z : Fin M, (assign z).card ≤ 2 ^ b - 1 := by
    intro z
    let qOf : Fin n → Nat := fun k =>
      @dite Nat (∃ q : Nat, P k.val ≤ z.val + q * M ∧ z.val + q * M < P (k.val + 1))
        (Classical.propDecidable _) (fun h => Classical.choose h) (fun _ => 0)
    have hmaps : Set.MapsTo qOf (assign z : Set (Fin n)) (Finset.range (2 ^ b - 1) : Set Nat) := by
      intro k hk
      have hk' : ∃ q : Nat, P k.val ≤ z.val + q * M ∧ z.val + q * M < P (k.val + 1) :=
        (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _ |>.mp hk).2
      have hspec := Classical.choose_spec hk'
      have hqeq : qOf k = Classical.choose hk' := by
        dsimp only [qOf]; exact dite_eq_left_of_eq_true (eq_true hk')
      rw [Finset.mem_coe, Finset.mem_range, hqeq]
      have hPn : P (k.val + 1) ≤ M * (2 ^ b - 1) :=
        le_trans (hPmono _ _ k.isLt) hQsum
      have hlt : Classical.choose hk' * M < (2 ^ b - 1) * M := by nlinarith
      exact Nat.lt_of_mul_lt_mul_right hlt
    have hinj : Set.InjOn qOf (assign z : Set (Fin n)) := by
      intro k1 hk1 k2 hk2 heq
      have h1 : ∃ q, P k1.val ≤ z.val + q * M ∧ z.val + q * M < P (k1.val + 1) :=
        (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _ |>.mp hk1).2
      have h2 : ∃ q, P k2.val ≤ z.val + q * M ∧ z.val + q * M < P (k2.val + 1) :=
        (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _ |>.mp hk2).2
      have hs1 := Classical.choose_spec h1
      have hs2 := Classical.choose_spec h2
      dsimp only [qOf] at heq
      rw [dite_eq_left_of_eq_true (eq_true h1), dite_eq_left_of_eq_true (eq_true h2)] at heq
      rw [heq] at hs1
      ext
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have := hPmono (k1.val + 1) k2.val hlt
        omega
      · have := hPmono (k2.val + 1) k1.val hgt
        omega
    have := Finset.card_le_card_of_injOn qOf hmaps hinj
    simpa using this
  have hquota_fin : ∀ k : Fin n,
      ((Finset.univ : Finset (Fin M)).filter (fun z => k ∈ assign z)).card = Q k.val := by
    intro k
    let f : Nat → Fin M := fun x => ⟨x % M, Nat.mod_lt x hMpos⟩
    have himg : (Finset.Ico (P k.val) (P (k.val + 1))).image f =
        (Finset.univ : Finset (Fin M)).filter (fun z => k ∈ assign z) := by
      ext z
      simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_filter, Finset.mem_univ, true_and, assign]
      constructor
      · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
        refine ⟨x / M, ?_, ?_⟩
        · have hdiv := Nat.mod_add_div x M
          have hcomm : x % M + x / M * M = x := by rw [Nat.mul_comm]; exact hdiv
          change P k.val ≤ x % M + x / M * M
          omega
        · have hdiv := Nat.mod_add_div x M
          have hcomm : x % M + x / M * M = x := by rw [Nat.mul_comm]; exact hdiv
          change x % M + x / M * M < P (k.val + 1)
          omega
      · rintro ⟨q, h1, h2⟩
        refine ⟨z.val + q * M, ⟨h1, h2⟩, ?_⟩
        ext
        simp only [f, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt z.isLt]
    have hinj : Set.InjOn f (Finset.Ico (P k.val) (P (k.val + 1)) : Set Nat) := by
      intro x1 hx1 x2 hx2 heq
      rw [Finset.mem_coe, Finset.mem_Ico] at hx1 hx2
      have hmod : x1 % M = x2 % M := congrArg Fin.val heq
      have hQ := hQle k.val k.isLt
      have hdiff1 : x1 < x2 + M := by rw [hPsucc] at hx1; omega
      have hdiff2 : x2 < x1 + M := by rw [hPsucc] at hx2; omega
      have h1 := Nat.mod_add_div x1 M
      have h2 := Nat.mod_add_div x2 M
      have hq1 : x1 / M = x2 / M := by nlinarith
      nlinarith
    rw [← himg, Finset.card_image_of_injOn hinj, Nat.card_Ico, hPsucc]
    omega
  let cutsFin : Finset Nat := (Finset.range (n + 1)).image (fun k => P k % M)
  have h0_mem : 0 ∈ cutsFin := by
    refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    simp [hP0]
  have hcuts_card : cutsFin.card ≤ n + 1 := by
    calc cutsFin.card ≤ (Finset.range (n + 1)).card := Finset.card_image_le
      _ = n + 1 := Finset.card_range (n + 1)
  have hcuts_lt : ∀ x ∈ cutsFin, x < M := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.mod_lt _ hMpos
  let cs_list : List Nat := cutsFin.sort (· ≤ ·)
  have hcs_len : cs_list.length = cutsFin.card := Finset.length_sort (· ≤ ·)
  have hcs_pos : 1 ≤ cs_list.length := by
    rw [hcs_len]
    exact Finset.card_pos.mpr ⟨0, h0_mem⟩
  have hcs_pw : cs_list.Pairwise (· < ·) := by
    have hle := Finset.pairwise_sort cutsFin (· ≤ ·)
    have hnd := Finset.sort_nodup cutsFin (· ≤ ·)
    exact (hle.and hnd).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hcs_strict : ∀ i j (hi : i < cs_list.length) (hj : j < cs_list.length), i < j →
      cs_list[i]'hi < cs_list[j]'hj := fun i j hi hj hij =>
    (List.pairwise_iff_getElem.mp hcs_pw) i j hi hj hij
  have hcs_mono : ∀ i j (hi : i < cs_list.length) (hj : j < cs_list.length), i ≤ j →
      cs_list[i]'hi ≤ cs_list[j]'hj := by
    intro i j hi hj hij
    rcases Nat.lt_or_eq_of_le hij with h | rfl
    · exact Nat.le_of_lt (hcs_strict i j hi hj h)
    · exact le_rfl
  have hcs0 : cs_list[0]'(by omega) = 0 := by
    have hmem : 0 ∈ cs_list := (Finset.mem_sort (· ≤ ·)).mpr h0_mem
    obtain ⟨j, hj, hj0⟩ := List.mem_iff_getElem.mp hmem
    by_cases hjz : j = 0
    · subst hjz; exact hj0
    · have := hcs_strict 0 j (by omega) hj (by omega)
      omega
  let endpt : Nat → Nat := fun i => if h : i < cs_list.length then cs_list[i]'h else M
  have hendpt0 : endpt 0 = 0 := by simp [endpt, show 0 < cs_list.length by omega, hcs0]
  have hendpt_top : endpt (n + 1) = M := by
    have : ¬ (n + 1 < cs_list.length) := by omega
    simp [endpt, this]
  have hendpt_le_M : ∀ i, endpt i ≤ M := by
    intro i
    simp only [endpt]
    split_ifs with h
    · exact Nat.le_of_lt (hcuts_lt _ ((Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem h)))
    · exact le_rfl
  have hendpt_mono : ∀ i, endpt i ≤ endpt (i + 1) := by
    intro i
    simp only [endpt]
    split_ifs with h1 h2 h2
    · exact Nat.le_of_lt (hcs_strict i (i + 1) h1 h2 (by omega))
    · exact Nat.le_of_lt (hcuts_lt _ ((Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem h1)))
    · omega
    · exact le_rfl
  have hno_cut : ∀ i u, endpt i < u → u < endpt (i + 1) → u ∉ cutsFin := by
    intro i u h1 h2 hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((Finset.mem_sort (· ≤ ·)).mpr hmem)
    change j < cs_list.length at hj
    have hi_lt : i < cs_list.length := by
      by_contra hge
      have ha : endpt i = M := by simp [endpt, hge]
      have hb : endpt (i + 1) = M := by simp [endpt, show ¬ (i + 1 < cs_list.length) by omega]
      omega
    have hei : endpt i = cs_list[i]'hi_lt := by simp [endpt, hi_lt]
    by_cases hji : j ≤ i
    · have hm := hcs_mono j i hj hi_lt hji
      dsimp only [cs_list] at hm hei
      rw [hei] at h1
      omega
    · have hi1 : i + 1 < cs_list.length := by omega
      have hei1 : endpt (i + 1) = cs_list[i + 1]'hi1 := by simp [endpt, hi1]
      have hm := hcs_mono (i + 1) j hi1 hj (by omega)
      dsimp only [cs_list] at hm hei1
      rw [hei1] at h2
      omega
  have hstep_const : ∀ u (hu : u + 1 < M), u + 1 ∉ cutsFin →
      assign ⟨u, by omega⟩ = assign ⟨u + 1, hu⟩ := by
    intro u hu hnot
    ext k
    simp only [assign, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, h1, h2⟩
      refine ⟨q, by omega, ?_⟩
      by_contra hge
      have heq : (u + 1) + q * M = P (k.val + 1) := by omega
      have hmod : P (k.val + 1) % M = u + 1 := by
        rw [← heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
      exact hnot (Finset.mem_image.mpr ⟨k.val + 1, Finset.mem_range.mpr (by omega), hmod⟩)
    · rintro ⟨q, h1, h2⟩
      refine ⟨q, ?_, by omega⟩
      by_contra hgt
      have heq : P k.val = (u + 1) + q * M := by omega
      have hmod : P k.val % M = u + 1 := by
        rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
      exact hnot (Finset.mem_image.mpr ⟨k.val, Finset.mem_range.mpr (by omega), hmod⟩)
  have hinterval_const : ∀ i u (hu1 : endpt i ≤ u) (hu2 : u < endpt (i + 1)),
      assign ⟨u, lt_of_lt_of_le hu2 (hendpt_le_M (i + 1))⟩ =
        assign ⟨endpt i, lt_of_le_of_lt hu1 (lt_of_lt_of_le hu2 (hendpt_le_M (i + 1)))⟩ := by
    intro i
    have haux : ∀ d (hd : endpt i + d < endpt (i + 1)),
        assign ⟨endpt i + d, lt_of_lt_of_le hd (hendpt_le_M (i + 1))⟩ =
          assign ⟨endpt i, lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_lt_of_le hd (hendpt_le_M (i + 1)))⟩ := by
      intro d
      induction d with
      | zero =>
        intro hd
        rfl
      | succ d ih =>
        intro hd
        have hprev := ih (by omega)
        have hu_ltM : (endpt i + d) + 1 < M := by
          have := hendpt_le_M (i + 1); omega
        have hnot := hno_cut i ((endpt i + d) + 1) (by omega) (by omega)
        have hst := hstep_const (endpt i + d) hu_ltM hnot
        have heq : (⟨endpt i + (d + 1), lt_of_lt_of_le hd (hendpt_le_M (i + 1))⟩ : Fin M) =
            ⟨(endpt i + d) + 1, hu_ltM⟩ := Fin.ext (by dsimp only; omega)
        rw [heq, ← hst]
        exact hprev
    intro u hu1 hu2
    have hd : endpt i + (u - endpt i) < endpt (i + 1) := by omega
    have hres := haux (u - endpt i) hd
    have heq : (⟨u, lt_of_lt_of_le hu2 (hendpt_le_M (i + 1))⟩ : Fin M) =
        ⟨endpt i + (u - endpt i), lt_of_lt_of_le hd (hendpt_le_M (i + 1))⟩ := Fin.ext (by dsimp only; omega)
    rw [heq]
    exact hres
  let m : Fin (n + 1) → Nat := fun i => endpt (i.val + 1) - endpt i.val
  let S : Fin (n + 1) → Finset (Fin n) := fun i =>
    if h : endpt i.val < M then assign ⟨endpt i.val, h⟩ else ∅
  have hsum_collapse : ∀ (g : Finset (Fin n) → Nat),
      (Finset.univ : Finset (Fin (n + 1))).sum (fun i => m i * g (S i)) =
        (Finset.univ : Finset (Fin M)).sum (fun z => g (assign z)) := by
    intro g
    let G : Nat → Nat := fun i => if h : endpt i < M then g (assign ⟨endpt i, h⟩) else g ∅
    let fz : Nat → Nat := fun z => if h : z < M then g (assign ⟨z, h⟩) else 0
    have htele : ∀ r ≤ n + 1,
        (Finset.range r).sum (fun i => (endpt (i + 1) - endpt i) * G i) =
          (Finset.Ico 0 (endpt r)).sum fz := by
      intro r hr
      induction r with
      | zero => simp [hendpt0]
      | succ r ih =>
        rw [Finset.sum_range_succ, ih (by omega)]
        have hsplit : Finset.Ico 0 (endpt (r + 1)) =
            Finset.Ico 0 (endpt r) ∪ Finset.Ico (endpt r) (endpt (r + 1)) := by
          ext z
          simp only [Finset.mem_Ico, Finset.mem_union]
          have := hendpt_mono r
          omega
        have hdisj : Disjoint (Finset.Ico 0 (endpt r)) (Finset.Ico (endpt r) (endpt (r + 1))) := by
          rw [Finset.disjoint_left]
          intro z hz1 hz2
          simp only [Finset.mem_Ico] at hz1 hz2
          omega
        rw [hsplit, Finset.sum_union hdisj]
        congr 1
        have hconst : (Finset.Ico (endpt r) (endpt (r + 1))).sum fz =
            (Finset.Ico (endpt r) (endpt (r + 1))).sum (fun _ => G r) := by
          refine Finset.sum_congr rfl (fun z hz => ?_)
          rw [Finset.mem_Ico] at hz
          have hzM : z < M := lt_of_lt_of_le hz.2 (hendpt_le_M (r + 1))
          have herM : endpt r < M := lt_of_le_of_lt hz.1 hzM
          simp only [fz, G, hzM, herM, dite_true]
          rw [hinterval_const r z hz.1 hz.2]
        rw [hconst, Finset.sum_const, smul_eq_mul, Nat.card_Ico]
    have hL : (Finset.univ : Finset (Fin (n + 1))).sum (fun i => m i * g (S i)) =
        (Finset.range (n + 1)).sum (fun i => (endpt (i + 1) - endpt i) * G i) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => (endpt (i + 1) - endpt i) * G i) (n + 1)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [m, S, G]
      split_ifs <;> rfl
    have hR : (Finset.Ico 0 (endpt (n + 1))).sum fz =
        (Finset.univ : Finset (Fin M)).sum (fun z => g (assign z)) := by
      rw [hendpt_top, Nat.Ico_zero_eq_range, ← Fin.sum_univ_eq_sum_range fz M]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      simp [fz, z.isLt]
    rw [hL, htele (n + 1) le_rfl, hR]
  refine ⟨m, S, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [S]
    split_ifs with h
    · exact hassign_card ⟨endpt i.val, h⟩
    · simp
  · have h1 := hsum_collapse (fun _ => 1)
    simpa using h1
  · intro k
    have h1 := hsum_collapse (fun T => if k ∈ T then 1 else 0)
    rw [h1, Finset.sum_boole, Nat.cast_id]
    exact hquota_fin k
  · intro k
    have h1 := hsum_collapse (fun T => if k ∈ T then 0 else 1)
    have h2 := hsum_collapse (fun T => if k ∈ T then 1 else 0)
    have h3 := hsum_collapse (fun _ => 1)
    have hadd : (Finset.univ : Finset (Fin (n + 1))).sum (fun i => m i * (if k ∈ S i then 0 else 1)) +
        (Finset.univ : Finset (Fin (n + 1))).sum (fun i => m i * (if k ∈ S i then 1 else 0)) = M := by
      rw [← Finset.sum_add_distrib]
      have heq : (Finset.univ : Finset (Fin (n + 1))).sum (fun i =>
          m i * (if k ∈ S i then 0 else 1) + m i * (if k ∈ S i then 1 else 0)) =
          (Finset.univ : Finset (Fin (n + 1))).sum (fun i => m i * 1) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        split_ifs <;> omega
      rw [heq, h3]
      simp
    have hq : (Finset.univ : Finset (Fin (n + 1))).sum (fun i => m i * (if k ∈ S i then 1 else 0)) = Q k.val := by
      rw [h2, Finset.sum_boole, Nat.cast_id]
      exact hquota_fin k
    omega

end Part3

namespace Part4

theorem card_subsets_card {n : Nat} (k : Nat) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k)).card = Nat.choose n k := by
  have heq : (Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k) =
      Finset.powersetCard k (Finset.univ : Finset (Fin n)) := by
    ext y
    simp [Finset.mem_powersetCard]
  rw [heq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem sum_edges_one {n : Nat} (k : Nat) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k)).sum (fun y =>
      ((Finset.univ : Finset (Fin n)) \ y).sum (fun _ => (1 : Nat))) =
      (n - k) * Nat.choose n k := by
  have h1 : ∀ y ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k),
      ((Finset.univ : Finset (Fin n)) \ y).sum (fun _ => (1 : Nat)) = n - k := by
    intro y hy
    have hy' : y.card = k := (Finset.mem_filter.mp hy).2
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_sdiff_of_subset (Finset.subset_univ y),
      Finset.card_univ, Fintype.card_fin, hy']
  rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, card_subsets_card, Nat.mul_comm]

theorem loss_edge_decomp {n : Nat} (w : Nat → Nat) (f : Finset (Fin n) → Fin n → Bool) :
    (Finset.univ : Finset (Finset (Fin n))).sum (fun x => w x.card *
      ((Finset.univ : Finset (Fin n)).filter (fun j => f x j ≠ decide (j ∉ x))).card) =
    (Finset.range n).sum (fun k =>
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k)).sum (fun y =>
        ((Finset.univ : Finset (Fin n)) \ y).sum (fun j =>
          (if f y j = false then w y.card else 0) +
          (if f (insert j y) j = true then w (y.card + 1) else 0)))) := by
  have h1 : (Finset.univ : Finset (Finset (Fin n))).sum (fun x => w x.card *
      ((Finset.univ : Finset (Fin n)).filter (fun j => f x j ≠ decide (j ∉ x))).card) =
      (Finset.univ : Finset (Fin n)).sum (fun j =>
        (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
          if f x j ≠ decide (j ∉ x) then w x.card else 0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> simp
  rw [h1]
  have h2 : ∀ j : Fin n,
      (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
        if f x j ≠ decide (j ∉ x) then w x.card else 0) =
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => j ∉ y)).sum (fun y =>
        (if f y j = false then w y.card else 0) +
        (if f (insert j y) j = true then w (y.card + 1) else 0)) := by
    intro j
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Finset (Fin n) => j ∉ x)]
    have hA : ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => j ∉ y)).sum (fun y =>
        if f y j ≠ decide (j ∉ y) then w y.card else 0) =
        ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => j ∉ y)).sum (fun y =>
          if f y j = false then w y.card else 0) := by
      refine Finset.sum_congr rfl (fun y hy => ?_)
      have hjy : j ∉ y := (Finset.mem_filter.mp hy).2
      have hdec : decide (j ∉ y) = true := decide_eq_true hjy
      rw [hdec]
      cases f y j <;> simp
    have hB : ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => ¬ j ∉ x)).sum (fun x =>
        if f x j ≠ decide (j ∉ x) then w x.card else 0) =
        ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => j ∉ y)).sum (fun y =>
          if f (insert j y) j = true then w (y.card + 1) else 0) := by
      refine Finset.sum_bij (fun x _ => x.erase j) ?_ ?_ ?_ ?_
      · intro x _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.notMem_erase j x⟩
      · intro x1 hx1 x2 hx2 heq
        have hj1 : j ∈ x1 := not_not.mp (Finset.mem_filter.mp hx1).2
        have hj2 : j ∈ x2 := not_not.mp (Finset.mem_filter.mp hx2).2
        rw [← Finset.insert_erase hj1, ← Finset.insert_erase hj2, heq]
      · intro y hy
        have hjy : j ∉ y := (Finset.mem_filter.mp hy).2
        refine ⟨insert j y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_not.mpr (Finset.mem_insert_self j y)⟩, ?_⟩
        exact Finset.erase_insert hjy
      · intro x hx
        have hjx : j ∈ x := not_not.mp (Finset.mem_filter.mp hx).2
        have hins : insert j (x.erase j) = x := Finset.insert_erase hjx
        have hcard : (x.erase j).card + 1 = x.card := by
          have := Finset.card_erase_add_one hjx
          exact this
        have hdec : decide (j ∉ x) = false := decide_eq_false (not_not.mpr hjx)
        rw [hins, hcard, hdec]
        cases f x j <;> simp
    rw [hA, hB, ← Finset.sum_add_distrib]
  have h3 : (Finset.univ : Finset (Fin n)).sum (fun j =>
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => j ∉ y)).sum (fun y =>
        (if f y j = false then w y.card else 0) +
        (if f (insert j y) j = true then w (y.card + 1) else 0))) =
      (Finset.univ : Finset (Finset (Fin n))).sum (fun y =>
        ((Finset.univ : Finset (Fin n)) \ y).sum (fun j =>
          (if f y j = false then w y.card else 0) +
          (if f (insert j y) j = true then w (y.card + 1) else 0))) := by
    have hrewrite1 : ∀ j : Fin n,
        ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => j ∉ y)).sum (fun y =>
          (if f y j = false then w y.card else 0) +
          (if f (insert j y) j = true then w (y.card + 1) else 0)) =
        (Finset.univ : Finset (Finset (Fin n))).sum (fun y =>
          if j ∉ y then
            (if f y j = false then w y.card else 0) +
            (if f (insert j y) j = true then w (y.card + 1) else 0)
          else 0) := fun j => Finset.sum_filter _ _
    simp_rw [hrewrite1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  rw [Finset.sum_congr rfl (fun j _ => h2 j), h3]
  have hsplit_card : (Finset.univ : Finset (Finset (Fin n))).sum (fun y =>
      ((Finset.univ : Finset (Fin n)) \ y).sum (fun j =>
        (if f y j = false then w y.card else 0) +
        (if f (insert j y) j = true then w (y.card + 1) else 0))) =
      (Finset.range (n + 1)).sum (fun k =>
        ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k)).sum (fun y =>
          ((Finset.univ : Finset (Fin n)) \ y).sum (fun j =>
            (if f y j = false then w y.card else 0) +
            (if f (insert j y) j = true then w (y.card + 1) else 0)))) := by
    have hdisj : Set.PairwiseDisjoint (Finset.range (n + 1) : Set Nat)
        (fun k => (Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k)) := by
      intro a _ b _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro y h1 h2
      have := (Finset.mem_filter.mp h1).2
      have := (Finset.mem_filter.mp h2).2
      omega
    rw [← Finset.sum_biUnion hdisj]
    congr 1
    ext y
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, true_and, true_iff]
    exact ⟨y.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ y), rfl⟩
  rw [hsplit_card, Finset.sum_range_succ]
  have htop_zero : ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = n)).sum (fun y =>
      ((Finset.univ : Finset (Fin n)) \ y).sum (fun j =>
        (if f y j = false then w y.card else 0) +
        (if f (insert j y) j = true then w (y.card + 1) else 0))) = 0 := by
    refine Finset.sum_eq_zero (fun y hy => ?_)
    have hy' : y.card = n := (Finset.mem_filter.mp hy).2
    have hyu : y = Finset.univ := Finset.eq_univ_of_card y (by simpa using hy')
    simp [hyu]
  rw [htop_zero, Nat.add_zero]

theorem layer_le_edges {n : Nat} (f : Finset (Fin n) → Fin n → Bool) (k : Nat) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k)).sum (fun y =>
      ((Finset.univ : Finset (Fin n)) \ y).sum (fun j =>
        if f y j = true ∧ f (insert j y) j = false then (1 : Nat) else 0)) ≤
      (n - k) * Nat.choose n k := by
  rw [← sum_edges_one k]
  refine Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun j _ => ?_))
  split_ifs <;> omega

theorem loss_lower_bound {n : Nat} (w : Nat → Nat) (f : Finset (Fin n) → Fin n → Bool) :
    (Finset.range n).sum (fun k =>
      ((n - k) * Nat.choose n k -
        ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k)).sum (fun y =>
          ((Finset.univ : Finset (Fin n)) \ y).sum (fun j =>
            if f y j = true ∧ f (insert j y) j = false then (1 : Nat) else 0))) *
      min (w k) (w (k + 1))) ≤
    (Finset.univ : Finset (Finset (Fin n))).sum (fun x => w x.card *
      ((Finset.univ : Finset (Fin n)).filter (fun j => f x j ≠ decide (j ∉ x))).card) := by
  rw [loss_edge_decomp w f]
  refine Finset.sum_le_sum (fun k _ => ?_)
  have hsub : (n - k) * Nat.choose n k -
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k)).sum (fun y =>
        ((Finset.univ : Finset (Fin n)) \ y).sum (fun j =>
          if f y j = true ∧ f (insert j y) j = false then (1 : Nat) else 0)) =
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k)).sum (fun y =>
        ((Finset.univ : Finset (Fin n)) \ y).sum (fun j =>
          1 - (if f y j = true ∧ f (insert j y) j = false then (1 : Nat) else 0))) := by
    have hadd : ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k)).sum (fun y =>
          ((Finset.univ : Finset (Fin n)) \ y).sum (fun j =>
            1 - (if f y j = true ∧ f (insert j y) j = false then (1 : Nat) else 0))) +
        ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k)).sum (fun y =>
          ((Finset.univ : Finset (Fin n)) \ y).sum (fun j =>
            if f y j = true ∧ f (insert j y) j = false then (1 : Nat) else 0)) =
        (n - k) * Nat.choose n k := by
      rw [← Finset.sum_add_distrib, ← sum_edges_one k]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs <;> omega
    omega
  rw [hsub, Finset.sum_mul]
  refine Finset.sum_le_sum (fun y hy => ?_)
  have hyk : y.card = k := (Finset.mem_filter.mp hy).2
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [hyk]
  cases f y j <;> cases f (insert j y) j <;> simp

theorem loss_F_S_eq {n p : Nat} (S : Finset (Fin n)) (w : Nat → Nat)
    (hw1 : ∀ k, k < p → w k ≤ w (k + 1))
    (hw2 : ∀ k, p ≤ k → k < n → w (k + 1) ≤ w k) :
    (Finset.univ : Finset (Finset (Fin n))).sum (fun x => w x.card *
      ((Finset.univ : Finset (Fin n)).filter (fun j => Part1.F_S n p S x j ≠ decide (j ∉ x))).card) =
    (Finset.range n).sum (fun k =>
      (n - k) * Nat.choose n k *
        (if h : k < n then (if ⟨k, h⟩ ∈ S then 0 else 1) else 0) * min (w k) (w (k + 1))) := by
  rw [loss_edge_decomp w (Part1.F_S n p S)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkn : k < n := Finset.mem_range.mp hk
  rw [dite_eq_left_of_eq_true (eq_true hkn)]
  have hmin : (if k < p then w k else w (k + 1)) = min (w k) (w (k + 1)) := by
    split_ifs with hkp
    · exact (min_eq_left (hw1 k hkp)).symm
    · exact (min_eq_right (hw2 k (by omega) hkn)).symm
  have hinner : ∀ y ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k),
      ∀ j ∈ (Finset.univ : Finset (Fin n)) \ y,
        (if Part1.F_S n p S y j = false then w y.card else 0) +
        (if Part1.F_S n p S (insert j y) j = true then w (y.card + 1) else 0) =
        (if ⟨k, hkn⟩ ∈ S then 0 else 1) * min (w k) (w (k + 1)) := by
    intro y hy j hj
    have hyk : y.card = k := (Finset.mem_filter.mp hy).2
    have hjy : j ∉ y := (Finset.mem_sdiff.mp hj).2
    have hyn : y.card < n := by omega
    rw [Part1.F_S_notMem S y j hjy hyn, Part1.F_S_insert S y j hjy hyn]
    have hfin : (⟨y.card, hyn⟩ : Fin n) = ⟨k, hkn⟩ := Fin.ext hyk
    rw [hfin, hyk]
    by_cases hmem : (⟨k, hkn⟩ : Fin n) ∈ S
    · simp [hmem]
    · simp only [hmem, ite_false, one_mul, ← hmin]
      by_cases hkp : k < p
      · have hnot : ¬ (p ≤ k) := by omega
        simp [hkp, hnot]
      · have hpk : p ≤ k := by omega
        simp [hkp, hpk]
  have hsum : ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k)).sum (fun y =>
      ((Finset.univ : Finset (Fin n)) \ y).sum (fun j =>
        (if Part1.F_S n p S y j = false then w y.card else 0) +
        (if Part1.F_S n p S (insert j y) j = true then w (y.card + 1) else 0))) =
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k)).sum (fun y =>
        ((Finset.univ : Finset (Fin n)) \ y).sum (fun _ =>
          (1 : Nat) * ((if ⟨k, hkn⟩ ∈ S then 0 else 1) * min (w k) (w (k + 1))))) := by
    refine Finset.sum_congr rfl (fun y hy => Finset.sum_congr rfl (fun j hj => ?_))
    rw [one_mul, hinner y hy j hj]
  rw [hsum]
  simp_rw [← Finset.sum_mul]
  rw [sum_edges_one k]
  ring

end Part4

def bitStd {n : Nat} (C : PEqualNP.CircuitLowerBounds.Circuit) (a : Fin n → Fin (n + 2 + C.size))
    (x : Finset (Fin n)) (j : Fin n) : Bool :=
  (C.wires (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true])).getD (a j).val false

def goodStd {n : Nat} (C : PEqualNP.CircuitLowerBounds.Circuit) (a : Fin n → Fin (n + 2 + C.size))
    (x : Finset (Fin n)) (j : Fin n) : Nat :=
  if bitStd C a x j = true ∧ bitStd C a (insert j x) j = false then 1 else 0

def layerStd {n : Nat} (C : PEqualNP.CircuitLowerBounds.Circuit) (a : Fin n → Fin (n + 2 + C.size))
    (k : Nat) : Nat :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => y.card = k)).sum (fun y =>
    ((Finset.univ : Finset (Fin n)) \ y).sum (fun j => goodStd C a y j))

def lossStd {n : Nat} (w : Nat → Nat) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (a : Fin n → Fin (n + 2 + C.size)) : Nat :=
  (Finset.univ : Finset (Finset (Fin n))).sum (fun x => w x.card *
    ((Finset.univ : Finset (Fin n)).filter (fun j => bitStd C a x j ≠ decide (j ∉ x))).card)

theorem decide_irrel (q : Prop) (d1 d2 : Decidable q) : @decide q d1 = @decide q d2 := by
  cases d1 <;> cases d2 <;> simp_all

theorem ite_irrel {α : Type*} (q : Prop) (d1 d2 : Decidable q) (a b : α) :
    @ite α q d1 a b = @ite α q d2 a b := by
  cases d1 <;> cases d2 <;> simp_all

theorem main_theorem (n T b p : Nat) (hp : p ≤ n)
    (old : Fin T → PEqualNP.CircuitLowerBounds.Circuit)
    (u : ∀ t, Fin n → Fin (n + 2 + (old t).size))
    (hvalid : ∀ t, PEqualNP.MetaComplexity.FanInTwo (old t) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) (old t) ∧
      (old t).output < n + 2 + (old t).size ∧
      PEqualNP.NotBracket.notCount (old t) ≤ b) :
    ∃ (cs : Fin (n + 1) → PEqualNP.CircuitLowerBounds.Circuit)
      (v : ∀ i, Fin n → Fin (n + 2 + (cs i).size)) (m : Fin (n + 1) → Nat),
      (∀ i, (PEqualNP.MetaComplexity.FanInTwo (cs i) ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) (cs i) ∧
        (cs i).output < n + 2 + (cs i).size ∧
        PEqualNP.NotBracket.notCount (cs i) ≤ b) ∧ (cs i).size ≤ 32 * (n + 1) ^ 3) ∧
      Finset.univ.sum m = T * n.factorial ∧
      (∀ (x : Finset (Fin n)) (j : Fin n), j ∉ x →
        (n - x.card) * Nat.choose n x.card *
          Finset.univ.sum (fun i => m i * goodStd (cs i) (v i) x j) =
        n.factorial * Finset.univ.sum (fun t => layerStd (old t) (u t) x.card)) ∧
      ∀ w : Nat → Nat, (∀ k, k < p → w k ≤ w (k + 1)) →
        (∀ k, p ≤ k → k < n → w (k + 1) ≤ w k) →
        Finset.univ.sum (fun i => m i * lossStd w (cs i) (v i)) ≤
          n.factorial * Finset.univ.sum (fun t => lossStd w (old t) (u t)) := by
  let X := Finset (Fin n)
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let valid := fun (C : Circ) => PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
    PEqualNP.NotBracket.notCount C ≤ b
  let taps := fun (C : Circ) => Fin n → Fin (n + 2 + C.size)
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨fun _ => ⟨[], 0⟩, fun _ j => Fin.elim0 j, fun _ => T, ?_, ?_, ?_, ?_⟩
    · intro i
      refine ⟨⟨by simp [PEqualNP.MetaComplexity.FanInTwo],
        by simp [PEqualNP.MetaComplexity.NestedCover.ReadsBack],
        by simp [PEqualNP.CircuitLowerBounds.Circuit.size],
        by simp [PEqualNP.NotBracket.notCount]⟩,
        by simp [PEqualNP.CircuitLowerBounds.Circuit.size]⟩
    · simp
    · intro x j; exact Fin.elim0 j
    · intro w _ _
      have hloss0 : ∀ (C : Circ) (a : taps C), lossStd w C a = 0 := by
        intro C a
        refine Finset.sum_eq_zero (fun x _ => ?_)
        have : ((Finset.univ : Finset (Fin 0)).filter (fun j => bitStd C a x j ≠ decide (j ∉ x))).card = 0 := by
          simp
        rw [this, Nat.mul_zero]
      simp [hloss0]
  by_cases hT0 : T = 0
  · subst hT0
    refine ⟨fun _ => ⟨[], 0⟩, fun _ _ => ⟨0, by simp [PEqualNP.CircuitLowerBounds.Circuit.size]⟩,
      fun _ => 0, ?_, ?_, ?_, ?_⟩
    · intro i
      refine ⟨⟨by simp [PEqualNP.MetaComplexity.FanInTwo],
        by simp [PEqualNP.MetaComplexity.NestedCover.ReadsBack],
        by simp [PEqualNP.CircuitLowerBounds.Circuit.size],
        by simp [PEqualNP.NotBracket.notCount]⟩,
        by simp [PEqualNP.CircuitLowerBounds.Circuit.size]⟩
    · simp
    · intro x j _; simp
    · intro w _ _; simp
  have hn_pos : 1 ≤ n := by omega
  have hT_pos : 1 ≤ T := by omega
  set M := T * n.factorial with hM_def
  have hM_pos : 1 ≤ M := Nat.mul_pos hT_pos (Nat.factorial_pos n)
  let Q : Nat → Nat := fun k =>
    if k < n then k.factorial * (n - 1 - k).factorial *
      (Finset.univ : Finset (Fin T)).sum (fun t => layerStd (old t) (u t) k)
    else 0
  have hperm_sum : ∀ (t : Fin T) (k : Fin n),
      (Finset.univ : Finset (Equiv.Perm (Fin n))).sum (fun σ =>
        goodStd (old t) (u t) (Part2.pref σ k.val) (σ k)) =
      k.val.factorial * (n - 1 - k.val).factorial * layerStd (old t) (u t) k.val :=
    fun t k => Part2.perm_sum_good_eq (goodStd (old t) (u t)) k
  have hQ_eq_perm : ∀ k : Fin n,
      Q k.val = (Finset.univ : Finset (Fin T)).sum (fun t =>
        (Finset.univ : Finset (Equiv.Perm (Fin n))).sum (fun σ =>
          goodStd (old t) (u t) (Part2.pref σ k.val) (σ k))) := by
    intro k
    simp only [Q, k.isLt, ite_true, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => (hperm_sum t k).symm)
  have hQle : ∀ k < n, Q k ≤ M := by
    intro k hk
    rw [hQ_eq_perm ⟨k, hk⟩]
    have hle : (Finset.univ : Finset (Fin T)).sum (fun t =>
        (Finset.univ : Finset (Equiv.Perm (Fin n))).sum (fun σ =>
          goodStd (old t) (u t) (Part2.pref σ k) (σ ⟨k, hk⟩))) ≤
        (Finset.univ : Finset (Fin T)).sum (fun _ =>
          (Finset.univ : Finset (Equiv.Perm (Fin n))).sum (fun _ => (1 : Nat))) := by
      refine Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun σ _ => ?_))
      dsimp only [goodStd]; split_ifs <;> omega
    have hrhs : (Finset.univ : Finset (Fin T)).sum (fun _ =>
        (Finset.univ : Finset (Equiv.Perm (Fin n))).sum (fun _ => (1 : Nat))) = M := by
      simp [M, Fintype.card_perm]
    exact le_trans hle (le_of_eq hrhs)
  have hQsum : (Finset.range n).sum Q ≤ M * (2 ^ b - 1) := by
    have h1 : (Finset.range n).sum Q = (Finset.univ : Finset (Fin n)).sum (fun k => Q k.val) :=
      (Fin.sum_univ_eq_sum_range Q n).symm
    rw [h1]
    simp_rw [hQ_eq_perm]
    rw [Finset.sum_comm]
    have h2 : (Finset.univ : Finset (Fin T)).sum (fun t =>
        (Finset.univ : Finset (Fin n)).sum (fun k =>
          (Finset.univ : Finset (Equiv.Perm (Fin n))).sum (fun σ =>
            goodStd (old t) (u t) (Part2.pref σ k.val) (σ k)))) ≤
        (Finset.univ : Finset (Fin T)).sum (fun _ =>
          (Finset.univ : Finset (Equiv.Perm (Fin n))).sum (fun _ => 2 ^ b - 1)) := by
      refine Finset.sum_le_sum (fun t _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum (fun σ _ => ?_)
      exact Part2.chain_good_le (old t) (u t) (hvalid t).1 (hvalid t).2.2.2 σ
    have hrhs : (Finset.univ : Finset (Fin T)).sum (fun _ =>
        (Finset.univ : Finset (Equiv.Perm (Fin n))).sum (fun _ => 2 ^ b - 1)) = M * (2 ^ b - 1) := by
      simp [M, Fintype.card_perm, Nat.mul_assoc]
    omega
  obtain ⟨m, S, hScard, hm_sum, hS_in, hS_out⟩ :=
    Part3.deal_intervals hM_pos Q hQle hQsum
  have hcirc_ex : ∀ i : Fin (n + 1),
      ∃ (C : Circ) (a : taps C),
        valid C ∧ C.size ≤ 32 * (n + 1) ^ 3 ∧
        ∀ (x : X) (j : Fin n), bitStd C a x j = Part1.F_S n p (S i) x j := by
    intro i
    obtain ⟨C, a, hfit, hrb, hout, hnc, hsz, hval⟩ :=
      Part1.circuit_of_set (p := p) (S i) (hScard i)
    exact ⟨C, a, ⟨hfit, hrb, hout, hnc⟩, hsz, hval⟩
  choose cs v hcs_valid hcs_size hcs_bit using hcirc_ex
  refine ⟨cs, v, m, fun i => ⟨hcs_valid i, hcs_size i⟩, hm_sum, ?_, ?_⟩
  · intro x j hjx
    have hkx_lt : x.card < n := by
      have h1 := Part1.erase_card_lt x j
      have h2 : x.erase j = x := Finset.erase_eq_of_notMem hjx
      rwa [h2] at h1
    have hgood_eq : ∀ i : Fin (n + 1),
        goodStd (cs i) (v i) x j = if ⟨x.card, hkx_lt⟩ ∈ S i then 1 else 0 := by
      intro i
      dsimp only [goodStd]
      rw [hcs_bit i x j, hcs_bit i (insert j x) j,
        Part1.F_S_notMem (S i) x j hjx hkx_lt,
        Part1.F_S_insert (S i) x j hjx hkx_lt]
      by_cases hmem : (⟨x.card, hkx_lt⟩ : Fin n) ∈ S i
      · simp [hmem]
      · simp only [hmem, ite_false]
        cases decide (p ≤ x.card) <;> simp
    have hsum_good : Finset.univ.sum (fun i => m i * goodStd (cs i) (v i) x j) = Q x.card := by
      simp_rw [hgood_eq]
      exact hS_in ⟨x.card, hkx_lt⟩
    rw [hsum_good]
    simp only [Q, hkx_lt, ite_true]
    rw [← Nat.mul_assoc, Part2.choose_fact_identity hkx_lt]
  · intro w hw1 hw2
    have hloss_cs : ∀ i : Fin (n + 1),
        lossStd w (cs i) (v i) =
        (Finset.range n).sum (fun k =>
          (n - k) * Nat.choose n k *
            (if h : k < n then (if ⟨k, h⟩ ∈ S i then 0 else 1) else 0) * min (w k) (w (k + 1))) := by
      intro i
      have h1 := Part4.loss_F_S_eq (S i) w hw1 hw2
      rw [← h1]
      dsimp only [lossStd]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      congr 2
      refine Finset.filter_congr (fun j _ => ?_)
      rw [hcs_bit i x j]
    have hLHS : Finset.univ.sum (fun i => m i * lossStd w (cs i) (v i)) =
        (Finset.range n).sum (fun k =>
          (n - k) * Nat.choose n k * (M - Q k) * min (w k) (w (k + 1))) := by
      simp_rw [hloss_cs, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hkn : k < n := Finset.mem_range.mp hk
      have hfactor : ∀ i : Fin (n + 1),
          m i * ((n - k) * Nat.choose n k *
            (if h : k < n then (if ⟨k, h⟩ ∈ S i then 0 else 1) else 0) * min (w k) (w (k + 1))) =
          (m i * (if ⟨k, hkn⟩ ∈ S i then 0 else 1)) * ((n - k) * Nat.choose n k * min (w k) (w (k + 1))) := by
        intro i
        rw [dite_eq_left_of_eq_true (eq_true hkn)]
        ring
      simp_rw [hfactor]
      rw [← Finset.sum_mul, hS_out ⟨k, hkn⟩]
      ring
    have hterm_eq : ∀ k ∈ Finset.range n,
        (n - k) * Nat.choose n k * (M - Q k) =
        n.factorial * (Finset.univ : Finset (Fin T)).sum (fun t =>
          (n - k) * Nat.choose n k - layerStd (old t) (u t) k) := by
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      have hQ_id : (n - k) * Nat.choose n k * Q k =
          n.factorial * (Finset.univ : Finset (Fin T)).sum (fun t => layerStd (old t) (u t) k) := by
        simp only [Q, hkn, ite_true]
        rw [← Nat.mul_assoc, Part2.choose_fact_identity hkn]
      have hlayer_le : ∀ t : Fin T, layerStd (old t) (u t) k ≤ (n - k) * Nat.choose n k :=
        fun t => Part4.layer_le_edges (bitStd (old t) (u t)) k
      have hsum_sub : (Finset.univ : Finset (Fin T)).sum (fun t =>
            (n - k) * Nat.choose n k - layerStd (old t) (u t) k) +
          (Finset.univ : Finset (Fin T)).sum (fun t => layerStd (old t) (u t) k) =
          T * ((n - k) * Nat.choose n k) := by
        rw [← Finset.sum_add_distrib]
        have hcongr : (Finset.univ : Finset (Fin T)).sum (fun t =>
            ((n - k) * Nat.choose n k - layerStd (old t) (u t) k) + layerStd (old t) (u t) k) =
            (Finset.univ : Finset (Fin T)).sum (fun _ => (n - k) * Nat.choose n k) :=
          Finset.sum_congr rfl (fun t _ => Nat.sub_add_cancel (hlayer_le t))
        rw [hcongr, Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
      have hMsub : (n - k) * Nat.choose n k * (M - Q k) + (n - k) * Nat.choose n k * Q k =
          (n - k) * Nat.choose n k * M := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (hQle k hkn)]
      have hMfac : (n - k) * Nat.choose n k * M = n.factorial * (T * ((n - k) * Nat.choose n k)) := by
        rw [hM_def]; ring
      have hmul_sub : n.factorial * (Finset.univ : Finset (Fin T)).sum (fun t =>
            (n - k) * Nat.choose n k - layerStd (old t) (u t) k) +
          n.factorial * (Finset.univ : Finset (Fin T)).sum (fun t => layerStd (old t) (u t) k) =
          n.factorial * (T * ((n - k) * Nat.choose n k)) := by
        rw [← Nat.mul_add, hsum_sub]
      omega
    rw [hLHS]
    have hRHS_step : (Finset.range n).sum (fun k =>
        (n - k) * Nat.choose n k * (M - Q k) * min (w k) (w (k + 1))) =
        n.factorial * (Finset.univ : Finset (Fin T)).sum (fun t =>
          (Finset.range n).sum (fun k =>
            ((n - k) * Nat.choose n k - layerStd (old t) (u t) k) * min (w k) (w (k + 1)))) := by
      have h1 : (Finset.range n).sum (fun k =>
          (n - k) * Nat.choose n k * (M - Q k) * min (w k) (w (k + 1))) =
          (Finset.range n).sum (fun k =>
            n.factorial * (Finset.univ : Finset (Fin T)).sum (fun t =>
              ((n - k) * Nat.choose n k - layerStd (old t) (u t) k) * min (w k) (w (k + 1)))) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [hterm_eq k hk, Nat.mul_assoc, Finset.sum_mul]
      rw [h1, ← Finset.mul_sum, Finset.sum_comm]
    rw [hRHS_step]
    refine Nat.mul_le_mul_left n.factorial (Finset.sum_le_sum (fun t _ => ?_))
    exact Part4.loss_lower_bound w (bitStd (old t) (u t))

end PEqualNP.Outside.L_meta_51383_aux

theorem PEqualNP.Outside.L_meta_51383 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n T b p : Nat), p ≤ n →
  let X := Finset (Fin n)
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let valid := fun (C : Circ) => PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
    PEqualNP.NotBracket.notCount C ≤ b
  let taps := fun (C : Circ) => Fin n → Fin (n+2+C.size)
  let bit := fun (C : Circ) (a : taps C) (x : X) (j : Fin n) =>
    (C.wires (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true])).getD (a j).val false
  let good := fun (C : Circ) (a : taps C) (x : X) (j : Fin n) =>
    if bit C a x j = true ∧ bit C a (insert j x) j = false then (1 : Nat) else 0
  let layer := fun (C : Circ) (a : taps C) (k : Nat) =>
    ((Finset.univ : Finset X).filter (fun y => y.card = k)).sum (fun y =>
      ((Finset.univ : Finset (Fin n)) \ y).sum (fun j => good C a y j))
  let loss := fun (w : Nat → Nat) (C : Circ) (a : taps C) =>
    (Finset.univ : Finset X).sum (fun x => w x.card *
      ((Finset.univ : Finset (Fin n)).filter (fun j => bit C a x j ≠ decide (j ∉ x))).card)
  ∀ (old : Fin T → Circ) (u : ∀ t, taps (old t)), (∀ t, valid (old t)) →
    ∃ (cs : Fin (n+1) → Circ) (v : ∀ i, taps (cs i)) (m : Fin (n+1) → Nat),
      (∀ i, valid (cs i) ∧ (cs i).size ≤ 32*(n+1)^3) ∧
      Finset.univ.sum m = T*n.factorial ∧
      (∀ (x : X) (j : Fin n), j ∉ x →
        (n-x.card)*Nat.choose n x.card *
          Finset.univ.sum (fun i => m i * good (cs i) (v i) x j) =
        n.factorial * Finset.univ.sum (fun t => layer (old t) (u t) x.card)) ∧
      ∀ w : Nat → Nat, (∀ k, k < p → w k ≤ w (k+1)) →
        (∀ k, p ≤ k → k < n → w (k+1) ≤ w k) →
        Finset.univ.sum (fun i => m i * loss w (cs i) (v i)) ≤
          n.factorial * Finset.univ.sum (fun t => loss w (old t) (u t))) := by
  intro n T b p hp X Circ valid taps bit good layer loss old u hvalid
  obtain ⟨cs, v, m, h1, h2, h3, h4⟩ :=
    PEqualNP.Outside.L_meta_51383_aux.main_theorem n T b p hp old u hvalid
  have hbit : ∀ (C : Circ) (a : taps C) (x : X) (j : Fin n),
      bit C a x j = PEqualNP.Outside.L_meta_51383_aux.bitStd C a x j := fun C a x j =>
    congrArg (fun f => (C.wires (List.ofFn f ++ [false, true])).getD (a j).val false)
      (funext fun i => PEqualNP.Outside.L_meta_51383_aux.decide_irrel (i ∈ x) _ _)
  have hgood : ∀ (C : Circ) (a : taps C) (x : X) (j : Fin n),
      good C a x j = PEqualNP.Outside.L_meta_51383_aux.goodStd C a x j := fun C a x j => by
    dsimp only [good, PEqualNP.Outside.L_meta_51383_aux.goodStd]
    rw [hbit, hbit]
    have hins : ∀ (d1 d2 : DecidableEq (Fin n)),
        @insert (Fin n) (Finset (Fin n)) (@Finset.instInsert (Fin n) d1) j x =
        @insert (Fin n) (Finset (Fin n)) (@Finset.instInsert (Fin n) d2) j x := fun d1 d2 => by
      ext z; rw [@Finset.mem_insert _ d1, @Finset.mem_insert _ d2]
    rw [hins _ (instDecidableEqFin n)]
    exact PEqualNP.Outside.L_meta_51383_aux.ite_irrel _ _ _ 1 0
  have hlayer : ∀ (C : Circ) (a : taps C) (k : Nat),
      layer C a k = PEqualNP.Outside.L_meta_51383_aux.layerStd C a k := fun C a k => by
    dsimp only [layer, PEqualNP.Outside.L_meta_51383_aux.layerStd]
    refine Finset.sum_congr (by ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (fun y _ =>
      Finset.sum_congr (by ext j; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]) (fun j _ => hgood C a y j))
  have hloss : ∀ (w : Nat → Nat) (C : Circ) (a : taps C),
      loss w C a = PEqualNP.Outside.L_meta_51383_aux.lossStd w C a := fun w C a => by
    dsimp only [loss, PEqualNP.Outside.L_meta_51383_aux.lossStd]
    refine Finset.sum_congr rfl (fun x _ => congrArg (w x.card * ·) (congrArg Finset.card (by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hbit C a x j]
      exact Iff.of_eq (congrArg (fun b => PEqualNP.Outside.L_meta_51383_aux.bitStd C a x j ≠ b)
        (PEqualNP.Outside.L_meta_51383_aux.decide_irrel (j ∉ x) _ _)))))
  refine ⟨cs, v, m, h1, h2, ?_, ?_⟩
  · intro x j hjx
    simpa only [hgood, hlayer] using h3 x j hjx
  · intro w hw1 hw2
    simpa only [hloss] using h4 w hw1 hw2
