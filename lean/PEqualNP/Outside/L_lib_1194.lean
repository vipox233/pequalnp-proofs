import PEqualNP.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Order
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

namespace PEqualNP.Outside.L_lib_1194_aux

open PEqualNP.CircuitLowerBounds

theorem getD_chain (m : ℕ) (f : Fin m → Bool) (i : ℕ) :
    (List.ofFn f ++ [false, true]).getD i false =
      if h : i < m then f ⟨i, h⟩ else decide (i = m + 1) := by
  by_cases h : i < m
  · rw [dite_eq_left h, List.getD_append _ _ _ _ (by simp; exact h)]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [dite_eq_right h, List.getD_append_right _ _ _ _ (by simp; omega)]
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

namespace Construct2

open Build068 Construct PEqualNP.CircuitLowerBounds

variable {n : Nat}

def ins : List (Sig n) → Sig n → List (Sig n) × Sig n
  | [], c => ([], c)
  | l0 :: ls, c => ((ban l0 c) :: (ins ls (bor l0 c)).1, (ins ls (bor l0 c)).2)

def carriesL : List (Sig n) → Sig n → List (Sig n)
  | [], c => [c]
  | l0 :: ls, c => c :: carriesL ls (bor l0 c)

def rev : List (Sig n) → Sig n → List (Sig n) → Sig n → List (Sig n) × Sig n
  | l0 :: ls, c, nn0 :: nns, ncf =>
    (bor (rev ls (bor l0 c) nns ncf).2 (ban nn0 c) :: (rev ls (bor l0 c) nns ncf).1,
      bor (rev ls (bor l0 c) nns ncf).2 (ban nn0 l0))
  | _, _, _, ncf => ([], ncf)

theorem ins_len (l : List (Sig n)) (c : Sig n) : (ins l c).1.length = l.length := by
  induction l generalizing c with
  | nil => rfl
  | cons a l ih => simp [ins, ih]

theorem rev_len (l : List (Sig n)) (c : Sig n) (nns : List (Sig n)) (ncf : Sig n)
    (h : nns.length = l.length) : (rev l c nns ncf).1.length = l.length := by
  induction l generalizing c nns with
  | nil => cases nns <;> rfl
  | cons a l ih =>
    cases nns with
    | nil => simp at h
    | cons b nns => simp only [rev, List.length_cons]; rw [ih _ _ (by simpa using h)]

theorem ins_last_mem (l : List (Sig n)) (c : Sig n) : (ins l c).2 ∈ carriesL l c := by
  induction l generalizing c with
  | nil => simp [ins, carriesL]
  | cons a l ih => simp only [ins, carriesL]; exact List.mem_cons_of_mem _ (ih _)

theorem ins_build {A : Set (Sig n)} (l : List (Sig n)) (c : Sig n)
    (hl : ∀ f ∈ l, f ∈ A) (hc : c ∈ A) :
    BuildN A {f | f ∈ carriesL l c ∨ f ∈ (ins l c).1} (2 * l.length) 0 := by
  induction l generalizing A c with
  | nil =>
    refine relax (idle (A := A) (B := {c}) (by simpa using hc)) le_rfl ?_ le_rfl le_rfl
    intro f hf; simp [carriesL, ins] at hf; simp [hf]
  | cons a l ih =>
    have ha : a ∈ A := hl a (by simp)
    have h1 := andG ha hc
    have h2 := orG (A := A ∪ {ban a c}) (Or.inl ha) (Or.inl hc)
    have h12 := seq h1 h2
    have h3 := ih (A := A ∪ ({ban a c} ∪ {bor a c})) (c := bor a c)
      (fun f hf => Or.inl (hl f (by simp [hf]))) (Or.inr (Or.inr rfl))
    have h0 := idle (A := A) (B := {c}) (by simpa using hc)
    have hall := seq h0 (relax (seq h12 h3) (C := A ∪ {c}) Set.subset_union_left le_rfl le_rfl le_rfl)
    refine relax hall le_rfl ?_ ?_ le_rfl
    · intro f hf
      simp only [carriesL, ins, List.mem_cons, Set.mem_ofPred_eq] at hf
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      rcases hf with (rfl | hf) | (rfl | hf)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl hf))
      · exact Or.inr (Or.inl (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr hf))
    · simp only [List.length_cons]; omega

end Construct2

namespace Construct2

open Build068 Construct PEqualNP.CircuitLowerBounds

variable {n : Nat}

theorem rev_build {A : Set (Sig n)} (l : List (Sig n)) (c : Sig n) (nns : List (Sig n))
    (ncf : Sig n) (hl : ∀ f ∈ l, f ∈ A) (hcar : ∀ f ∈ carriesL l c, f ∈ A)
    (hnns : ∀ f ∈ nns, f ∈ A) (hncf : ncf ∈ A) (hlen : nns.length = l.length) :
    BuildN A {f | f ∈ (rev l c nns ncf).1 ∨ f = (rev l c nns ncf).2} (4 * l.length) 0 := by
  induction l generalizing c nns with
  | nil =>
    refine relax (idle (A := A) (B := {ncf}) (by simpa using hncf)) le_rfl ?_ le_rfl le_rfl
    intro f hf
    cases nns <;> simp [rev] at hf <;> simp [hf]
  | cons a l ih =>
    cases nns with
    | nil => simp at hlen
    | cons b nns =>
      have hc : c ∈ A := hcar c (by simp [carriesL])
      have ha : a ∈ A := hl a (by simp)
      have hb : b ∈ A := hnns b (by simp)
      have H1 := ih (bor a c) nns (fun f hf => hl f (by simp [hf]))
        (fun f hf => hcar f (by simp [carriesL, hf])) (fun f hf => hnns f (by simp [hf]))
        (by simpa using hlen)
      set R := rev l (bor a c) nns ncf with hR
      let RS := {f | f ∈ R.1 ∨ f = R.2}
      have H2 := step2 (A := A ∪ RS) (f := b) (g := c) (h := R.2) (Or.inl hb) (Or.inl hc)
        (Or.inr (Or.inr rfl))
      have H3 := step2 (A := A ∪ RS ∪ {bor R.2 (ban b c)}) (f := b) (g := a) (h := R.2)
        (Or.inl (Or.inl hb)) (Or.inl (Or.inl ha)) (Or.inl (Or.inr (Or.inr rfl)))
      have H := seq H1 (relax (seq H2 H3) (C := A ∪ RS) le_rfl le_rfl le_rfl le_rfl)
      refine relax H le_rfl ?_ ?_ le_rfl
      · intro f hf
        simp only [rev, ← hR, List.mem_cons, Set.mem_ofPred_eq] at hf
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
        rcases hf with (rfl | hf) | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl (Or.inl hf)
        · exact Or.inr (Or.inr rfl)
      · simp only [List.length_cons]; omega

theorem ins_last (l : List (Sig n)) (c : Sig n) (x : Fin n → Bool) :
    (ins l c).2 x = (c x || l.any (fun f => f x)) := by
  induction l generalizing c with
  | nil => simp [ins]
  | cons a l ih =>
    simp only [ins, ih, bor, List.any_cons]
    cases a x <;> cases c x <;> simp

theorem ins_count (l : List (Sig n)) (c : Sig n) (x : Fin n → Bool) :
    (((ins l c).1 ++ [(ins l c).2]).map (fun f => f x)).count false =
      (l.map (fun f => f x)).count false + (if c x then 0 else 1) := by
  induction l generalizing c with
  | nil => cases h : c x <;> simp [ins, h]
  | cons a l ih =>
    have := ih (bor a c)
    simp only [ins, List.cons_append, List.map_cons, List.count_cons] at this ⊢
    rw [this]
    cases ha : a x <;> cases hc : c x <;> simp [ban, bor, ha, hc]

theorem ins_allTrue (l : List (Sig n)) (c : Sig n) (x : Fin n → Bool)
    (hl : ∀ f ∈ l, f x = true) (hc : c x = true) :
    ∀ y ∈ ((ins l c).1 ++ [(ins l c).2]).map (fun f => f x), y = true := by
  induction l generalizing c with
  | nil => simp [ins, hc]
  | cons a l ih =>
    have ha : a x = true := hl a (by simp)
    intro y hy
    simp only [ins, List.cons_append, List.map_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · simp [ban, ha, hc]
    · exact ih (bor a c) (fun f hf => hl f (by simp [hf])) (by simp [bor, ha]) y hy

theorem ins_sorted (l : List (Sig n)) (c : Sig n) (x : Fin n → Bool)
    (hl : (l.map (fun f => f x)).Pairwise (· ≤ ·)) :
    (((ins l c).1 ++ [(ins l c).2]).map (fun f => f x)).Pairwise (· ≤ ·) := by
  induction l generalizing c with
  | nil => simp [ins]
  | cons a l ih =>
    simp only [List.map_cons, List.pairwise_cons] at hl
    simp only [ins, List.cons_append, List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih (bor a c) hl.2⟩
    intro y hy
    cases hac : ban a c x
    · exact Bool.false_le _
    · simp only [ban, Bool.and_eq_true] at hac
      have hlt : ∀ f ∈ l, f x = true := by
        intro f hf
        have := hl.1 (f x) (List.mem_map_of_mem hf)
        rw [hac.1] at this
        revert this; cases f x <;> simp
      rw [ins_allTrue l (bor a c) x hlt (by simp [bor, hac.1]) y hy]

theorem rev_eval (l : List (Sig n)) (c : Sig n) (nns : List (Sig n)) (ncf : Sig n)
    (x : Fin n → Bool)
    (hn : nns.map (fun f => f x) = ((ins l c).1.map (fun f => f x)).map not)
    (hf : ncf x = !((ins l c).2 x)) :
    (rev l c nns ncf).1.map (fun f => f x) = (l.map (fun f => f x)).map not ∧
      (rev l c nns ncf).2 x = !(c x) := by
  induction l generalizing c nns with
  | nil =>
    cases nns with
    | nil => simp [rev]; simpa [ins] using hf
    | cons b nns => simp [ins] at hn
  | cons a l ih =>
    cases nns with
    | nil => simp [ins] at hn
    | cons b nns =>
      simp only [ins, List.map_cons, List.cons.injEq] at hn
      obtain ⟨hb, hn'⟩ := hn
      obtain ⟨h1, h2⟩ := ih (bor a c) nns hn' (by simpa [ins] using hf)
      simp only [rev, List.map_cons, h1, List.cons.injEq, and_true]
      simp only [bor, ban, h2, hb]
      cases a x <;> cases c x <;> simp

end Construct2

namespace Construct3

open Build068 Construct Construct2 PEqualNP.CircuitLowerBounds

def inp (m : Nat) (i : Nat) : Sig (m + 2) := fun x => if h : i < m + 2 then x ⟨i, h⟩ else false

def restC (m : Nat) (j : Nat) (x : Fin (m + 2) → Bool) : Nat :=
  ((Finset.Ico j m).filter (fun i => inp m i x = false)).card

def costC (m b r j : Nat) : Nat := 6 * ∑ i ∈ Finset.Ico j m, min i b + T r

theorem restC_succ (m j : Nat) (x : Fin (m + 2) → Bool) (hj : j < m) :
    restC m j x = restC m (j + 1) x + (if inp m j x = false then 1 else 0) := by
  unfold restC
  rw [← Finset.insert_Ico_add_one_left_eq_Ico hj, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem bool_le_true {a b : Bool} (h : a ≤ b) (ha : a = true) : b = true := by
  subst ha; revert h; cases b <;> simp

theorem rest_build (m b r : Nat) (hb : b < 2 ^ r) (hbm : b ≤ m) :
    ∀ d j, j + d = m → ∀ (A : Set (Sig (m + 2))) (L : List (Sig (m + 2))), L.length = min j b →
      (∀ f ∈ L, f ∈ A) → (∀ i < m + 2, inp m i ∈ A) →
      ∃ (NL : List (Sig (m + 2))) (NX : Nat → Sig (m + 2)), NL.length = L.length ∧
        BuildN A {f | f ∈ NL ∨ ∃ i, j ≤ i ∧ i < m ∧ f = NX i} (costC m b r j) r ∧
        ∀ x, inp m (m + 1) x = true → inp m m x = false →
          (L.map (fun f => f x)).Pairwise (· ≤ ·) →
          (L.map (fun f => f x)).count false + restC m j x ≤ b →
          NL.map (fun f => f x) = (L.map (fun f => f x)).map not ∧
          ∀ i, j ≤ i → i < m → NX i x = !(inp m i x) := by
  intro d
  induction d with
  | zero =>
    intro j hj A L hL hLA hinp
    have hjm : j = m := by omega
    subst hjm
    have hLb : L.length = b := by rw [hL]; omega
    let u : Nat → Sig (j + 2) := fun i => L.getD i (inp j (j + 1))
    have hu : ∀ i < 2 ^ r - 1, u i ∈ A := by
      intro i _
      by_cases hi : i < L.length
      · simp only [u, List.getD_eq_getElem _ _ hi]; exact hLA _ (List.getElem_mem hi)
      · simp only [u]; rw [List.getD_eq_default _ _ (show L.length ≤ i by omega)]; exact hinp _ (by omega)
    obtain ⟨nu, H, hnu⟩ := inverter r A u hu
    refine ⟨(List.range L.length).map nu, fun _ => inp j 0, by simp, ?_, ?_⟩
    · refine relax H le_rfl ?_ ?_ le_rfl
      · rintro f (hf | ⟨i, hi1, hi2, _⟩)
        · simp only [List.mem_map, List.mem_range] at hf
          obtain ⟨i, hi, rfl⟩ := hf
          exact ⟨i, by omega, rfl⟩
        · omega
      · simp [costC]
    · intro x hT _ hsort _
      have hsrt : Srt (2 ^ r - 1) u x := by
        intro i k hik hk hui
        by_cases hkl : k < L.length
        · have hil : i < L.length := by omega
          simp only [u, List.getD_eq_getElem _ _ hkl]
          simp only [u, List.getD_eq_getElem _ _ hil] at hui
          rcases Nat.lt_or_eq_of_le hik with hlt | heq
          · have := List.pairwise_iff_getElem.mp hsort i k (by simpa using hil)
              (by simpa using hkl) hlt
            simp only [List.getElem_map] at this
            exact bool_le_true this hui
          · subst heq; exact hui
        · simp only [u]; rw [List.getD_eq_default _ _ (show L.length ≤ k by omega)]; exact hT
      refine ⟨?_, fun i hi1 hi2 => by omega⟩
      apply List.ext_getElem (by simp)
      intro k hk1 hk2
      simp only [List.getElem_map, List.getElem_range]
      simp only [List.length_map, List.length_range] at hk1
      rw [hnu x hsrt k (by omega)]
      simp only [u, List.getD_eq_getElem _ _ hk1]
  | succ d ih =>
    intro j hj A L hL hLA hinp
    have hjm : j < m := by omega
    set c := inp m j with hc
    set P := ins L c with hP
    set L' := if L.length < b then P.1 ++ [P.2] else P.1 with hL'def
    have hP1len : P.1.length = L.length := ins_len L c
    have hL' : L'.length = min (j + 1) b := by
      rw [hL'def]; split_ifs with h
      · simp [hP1len]; omega
      · rw [hP1len]; omega
    have H1 := ins_build L c hLA (hinp j (by omega))
    set I1 := {f | f ∈ carriesL L c ∨ f ∈ P.1} with hI1
    have hL'A : ∀ f ∈ L', f ∈ A ∪ I1 := by
      intro f hf
      rw [hL'def] at hf
      split_ifs at hf
      · rcases List.mem_append.mp hf with hf | hf
        · exact Or.inr (Or.inr hf)
        · rw [List.mem_singleton] at hf; subst hf; exact Or.inr (Or.inl (ins_last_mem L c))
      · exact Or.inr (Or.inr hf)
    obtain ⟨NL', NX', hlen', H2, hcor'⟩ :=
      ih (j + 1) (by omega) (A ∪ I1) L' hL' hL'A (fun i hi => Or.inl (hinp i hi))
    set B2 := {f | f ∈ NL' ∨ ∃ i, j + 1 ≤ i ∧ i < m ∧ f = NX' i} with hB2
    set nns := NL'.take L.length with hnns
    set ncf := if L.length < b then NL'.getD L.length (inp m m) else inp m m with hncf
    have hnnslen : nns.length = L.length := by
      rw [hnns, List.length_take, hlen', hL']; omega
    have H3 := rev_build (A := A ∪ (I1 ∪ B2)) L c nns ncf
      (fun f hf => Or.inl (hLA f hf)) (fun f hf => Or.inr (Or.inl (Or.inl hf)))
      (fun f hf => Or.inr (Or.inr (Or.inl (List.mem_of_mem_take hf))))
      (by
        rw [hncf]; split_ifs with h
        · by_cases hl : L.length < NL'.length
          · rw [List.getD_eq_getElem _ _ hl]
            exact Or.inr (Or.inr (Or.inl (List.getElem_mem hl)))
          · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (hinp m (by omega))
        · exact Or.inl (hinp m (by omega)))
      hnnslen
    set R := rev L c nns ncf with hR
    have Hall := seq (seq H1 H2) H3
    refine ⟨R.1, fun i => if i = j then R.2 else NX' i, rev_len L c nns ncf hnnslen,
      relax Hall le_rfl ?_ ?_ (by omega), ?_⟩
    · rintro f (hf | ⟨i, hi1, hi2, rfl⟩)
      · exact Or.inr (Or.inl hf)
      · by_cases hij : i = j
        · simp only [hij, ite_true]; exact Or.inr (Or.inr rfl)
        · simp only [hij, ite_false]
          exact Or.inl (Or.inr (Or.inr ⟨i, by omega, hi2, rfl⟩))
    · unfold costC
      rw [Finset.sum_eq_sum_Ico_succ_bot hjm]
      rw [hL]; omega
    · intro x hT hF hsort hcount
      have hrs := restC_succ m j x hjm
      rw [← hc] at hrs
      have hcnt := ins_count L c x
      have hsrt := ins_sorted L c x hsort
      have hlast := ins_last L c x
      rw [← hP] at hcnt hsrt hlast
      have hmapP : ((P.1 ++ [P.2]).map (fun f => f x)) =
          P.1.map (fun f => f x) ++ [P.2 x] := by simp

      have hdisc : ¬ L.length < b → P.2 x = true := by
        intro hnb
        rw [hlast]
        by_contra hcon
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff, List.any_eq_false] at hcon
        have hall : (L.map (fun f => f x)).count false = L.length := by
          have : (L.map (fun f => f x)).count false = (L.map (fun f => f x)).length :=
            List.count_eq_length.mpr (by
            intro y hy
            simp only [List.mem_map] at hy
            obtain ⟨f, hf, rfl⟩ := hy
            simpa using (hcon.2 f hf).symm)
          simpa using this
        rw [hall, hrs, hcon.1] at hcount
        simp only [ite_true] at hcount
        omega
      have hsort' : (L'.map (fun f => f x)).Pairwise (· ≤ ·) := by
        rw [hL'def]; split_ifs
        · exact hsrt
        · rw [hmapP] at hsrt; exact (List.pairwise_append.mp hsrt).1
      have hcount' : (L'.map (fun f => f x)).count false + restC m (j + 1) x ≤ b := by
        rw [hL'def]; split_ifs with h
        · rw [hcnt]; rw [hrs] at hcount
          cases hcx : c x <;> simp only [hcx, Bool.false_eq_true, ite_true, ite_false] at hcount ⊢ <;>
            omega
        · rw [hmapP, List.count_append] at hcnt
          have h2 := hdisc h
          rw [h2] at hcnt
          simp only [List.count_singleton, Bool.true_beq, Bool.false_eq_true,
            ite_false, add_zero] at hcnt
          rw [hcnt]; rw [hrs] at hcount
          cases hcx : c x <;> simp only [hcx, Bool.false_eq_true, ite_true, ite_false] at hcount ⊢ <;>
            omega
      obtain ⟨hNL', hNX'⟩ := hcor' x hT hF hsort' hcount'
      have hnnsv : nns.map (fun f => f x) = (P.1.map (fun f => f x)).map not := by
        rw [hnns, List.map_take, hNL', hL'def]
        split_ifs
        · simp only [List.map_append]
          rw [List.take_append_of_le_length (by simp [hP1len])]
          rw [List.take_of_length_le (by simp [hP1len])]
        · rw [List.take_of_length_le (by simp [hP1len])]
      have hncfv : ncf x = !(P.2 x) := by
        rw [hncf]; split_ifs with h
        · have hl : L.length < NL'.length := by rw [hlen', hL']; omega
          rw [List.getD_eq_getElem _ _ hl]
          have e := congrArg (fun l => l[L.length]?) hNL'
          simp only [List.getElem?_map, List.getElem?_eq_getElem hl] at e
          have hl2 : L.length < L'.length := by rw [hL']; omega
          rw [List.getElem?_eq_getElem hl2] at e
          simp only [Option.map_some, Option.some.injEq] at e
          rw [e]
          congr 1
          have e2 : L'[L.length]? = some P.2 := by
            rw [hL'def, ite_eq_left h, List.getElem?_append_right (by simp [hP1len])]
            simp [hP1len]
          rw [List.getElem?_eq_getElem hl2] at e2
          rw [Option.some.injEq] at e2
          rw [e2]
        · rw [hdisc h]; exact hF
      obtain ⟨hR1, hR2⟩ := rev_eval L c nns ncf x hnnsv hncfv
      refine ⟨hR1, ?_⟩
      intro i hi1 hi2
      by_cases hij : i = j
      · subst hij; simp only [ite_true]; exact hR2
      · simp only [hij, ite_false]; exact hNX' i (by omega) hi2

end Construct3

namespace Final

open Build068 Construct Construct2 Construct3 PEqualNP.CircuitLowerBounds

theorem ofFn_chain (m : Nat) (x : Fin m → Bool) :
    List.ofFn x ++ [false, true] =
      List.ofFn (fun k : Fin (m + 2) => if h : k.val < m then x ⟨k.val, h⟩ else decide (k.val = m + 1)) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  have e1 := getD_chain m x k
  rw [List.getD_eq_getElem _ _ h1] at e1
  rw [e1, List.getElem_ofFn]

theorem upper (m a r : Nat) (hb : min a m < 2 ^ r) :
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (m + 2 + C.size)),
      (PEqualNP.MetaComplexity.FanInTwo C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (m + 2) C ∧ C.output < m + 2 + C.size) ∧
      C.size + 3 * r ≤ 6 * (Finset.range m).sum (fun j => min j (min a m)) + 4 * (2 ^ r - 1) ∧
      PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ x : Fin m → Bool, ((Finset.univ : Finset (Fin m)).filter (fun i => x i = false)).card ≤ a →
        ∀ i, (C.wires (List.ofFn x ++ [false,true])).getD (tap i).val false = !x i := by
  set b := min a m with hbdef
  have hbm : b ≤ m := min_le_right _ _
  let S0 : Set (Sig (m + 2)) := Set.range (fun i : Fin (m + 2) => (fun x => x i : Sig (m + 2)))
  have Hstart : GateBridgeN.Scheduled (m + 2) id 0 0 S0 :=
    GateBridgeN.start (fun i : Fin (m + 2) => (fun x => x i : Sig (m + 2))) (fun _ _ => rfl)
  obtain ⟨NL, NX, _, H, hcor⟩ := rest_build m b r hb hbm m 0 (by omega) S0 [] (by simp) (by simp)
    (fun i hi => ⟨⟨i, hi⟩, by funext x; simp [inp, hi]⟩)
  obtain ⟨c, hc, cn, hcn, HS⟩ := H.run Hstart le_rfl
  obtain ⟨gs, hgs, hnc, hrb, hfan, hw⟩ := HS
  have hex : ∀ i : Fin m, ∃ w : Nat, w < m + 2 + (0 + c) ∧ ∀ x : Fin (m + 2) → Bool,
      ((Circuit.mk gs 0).wires (List.ofFn x)).getD w false = NX i.val x := by
    intro i
    exact hw _ (Or.inr (Or.inr ⟨i.val, by omega, i.isLt, rfl⟩))
  choose w hw1 hw2 using hex
  refine ⟨⟨gs, 0⟩, fun i => ⟨w i, by simp only [Circuit.size, hgs]; exact hw1 i⟩, ⟨hfan, hrb, ?_⟩,
    ?_, ?_, ?_⟩
  · simp [Circuit.size]
  · simp only [Circuit.size, hgs]
    have h1 := T_add r
    unfold costC at hc
    rw [← Finset.range_eq_Ico] at hc
    omega
  · rw [hnc]; omega
  · intro x hprom i
    let x' : Fin (m + 2) → Bool := fun k =>
      if h : k.val < m then x ⟨k.val, h⟩ else decide (k.val = m + 1)
    rw [ofFn_chain m x]
    change ((Circuit.mk gs 0).wires (List.ofFn x')).getD (w i) false = !x i
    rw [hw2 i x']
    have hT : inp m (m + 1) x' = true := by simp [inp, x']
    have hF : inp m m x' = false := by simp [inp, x']
    have hrest : restC m 0 x' ≤ b := by
      unfold restC
      have e : (Finset.Ico 0 m).filter (fun k => inp m k x' = false) =
          ((Finset.univ : Finset (Fin m)).filter (fun i => x i = false)).map Fin.valEmbedding := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_map, Finset.mem_univ, true_and,
          Fin.valEmbedding_apply]
        constructor
        · rintro ⟨⟨_, hk⟩, hx⟩
          refine ⟨⟨k, hk⟩, ?_, rfl⟩
          simpa [inp, x', hk, show k < m + 2 by omega] using hx
        · rintro ⟨j, hj, rfl⟩
          refine ⟨⟨Nat.zero_le _, j.isLt⟩, ?_⟩
          simpa [inp, x', j.isLt, show j.val < m + 2 by omega] using hj
      rw [e, Finset.card_map]
      refine le_min hprom ?_
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    have := (hcor x' hT hF (by simp) (by simpa using hrest)).2 i.val (Nat.zero_le _) i.isLt
    rw [this]
    simp [inp, x', i.isLt, show i.val < m + 2 by omega]

end Final

namespace Dual068

open Build068 Construct PEqualNP.CircuitLowerBounds

variable {n : Nat}

abbrev DSig (n : Nat) := Sig n × Sig n

def dMem (p : DSig n) (A : Set (Sig n)) : Prop := p.1 ∈ A ∧ p.2 ∈ A

def dSet (S : Set (DSig n)) : Set (Sig n) := {f | ∃ p ∈ S, f = p.1 ∨ f = p.2}

def dValidAt (p : DSig n) (x : Fin n → Bool) : Prop := p.2 x = !(p.1 x)

def dNot (p : DSig n) : DSig n := (p.2, p.1)

def dAnd (p q : DSig n) : DSig n := (ban p.1 q.1, bor p.2 q.2)

def dOr (p q : DSig n) : DSig n := (bor p.1 q.1, ban p.2 q.2)

theorem dValid_not {p : DSig n} {x : Fin n → Bool} (hp : dValidAt p x) :
    dValidAt (dNot p) x := by
  dsimp [dValidAt, dNot] at hp ⊢
  rw [hp, Bool.not_not]

theorem dValid_and {p q : DSig n} {x : Fin n → Bool} (hp : dValidAt p x) (hq : dValidAt q x) :
    dValidAt (dAnd p q) x := by
  dsimp [dValidAt, dAnd, ban, bor] at hp hq ⊢
  rw [hp, hq]
  cases p.1 x <;> cases q.1 x <;> rfl

theorem dValid_or {p q : DSig n} {x : Fin n → Bool} (hp : dValidAt p x) (hq : dValidAt q x) :
    dValidAt (dOr p q) x := by
  dsimp [dValidAt, dOr, ban, bor] at hp hq ⊢
  rw [hp, hq]
  cases p.1 x <;> cases q.1 x <;> rfl

theorem dIdle {A : Set (Sig n)} {p : DSig n} (hp : dMem p A) :
    BuildN A (dSet {p}) 0 0 := by
  refine relax (idle (A := A) (B := dSet {p}) ?_) le_rfl le_rfl le_rfl le_rfl
  rintro f ⟨q, hq, hfq⟩
  rw [Set.mem_singleton_iff] at hq
  subst hq
  rcases hfq with rfl | rfl
  · exact hp.1
  · exact hp.2

theorem dAndG {A : Set (Sig n)} {p q : DSig n} (hp : dMem p A) (hq : dMem q A) :
    BuildN A (dSet {dAnd p q}) 2 0 := by
  have h1 := andG hp.1 hq.1
  have h2 := orG (A := A ∪ {ban p.1 q.1}) (Or.inl hp.2) (Or.inl hq.2)
  refine relax (seq h1 h2) le_rfl ?_ le_rfl le_rfl
  rintro f ⟨r, hr, hfr⟩
  rw [Set.mem_singleton_iff] at hr
  subst hr
  rcases hfr with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem dOrG {A : Set (Sig n)} {p q : DSig n} (hp : dMem p A) (hq : dMem q A) :
    BuildN A (dSet {dOr p q}) 2 0 := by
  have h1 := orG hp.1 hq.1
  have h2 := andG (A := A ∪ {bor p.1 q.1}) (Or.inl hp.2) (Or.inl hq.2)
  refine relax (seq h1 h2) le_rfl ?_ le_rfl le_rfl
  rintro f ⟨r, hr, hfr⟩
  rw [Set.mem_singleton_iff] at hr
  subst hr
  rcases hfr with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem dMem_of_mem {S : Set (DSig n)} {A : Set (Sig n)} {p : DSig n}
    (hp : p ∈ S) (hsub : dSet S ⊆ A) : dMem p A :=
  ⟨hsub ⟨p, hp, Or.inl rfl⟩, hsub ⟨p, hp, Or.inr rfl⟩⟩

theorem dListBuild {α : Type*} {A : Set (Sig n)} (xs : List α)
    (F : α → DSig n) (c : Nat) (H : ∀ a ∈ xs, BuildN A (dSet {F a}) c 0) :
    BuildN A (dSet {p | ∃ a ∈ xs, p = F a}) (xs.length * c) 0 := by
  induction xs with
  | nil =>
    refine relax (idle (A := A) (B := ∅) (by simp)) le_rfl ?_ (by simp) (by simp)
    rintro f ⟨p, ⟨a, ha, _⟩, _⟩
    simp at ha
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ dSet {F a}) Set.subset_union_left le_rfl le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ ?_ (by simp)
    · rintro f ⟨p, ⟨b, hb, rfl⟩, hfp⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl ⟨F b, rfl, hfp⟩
      · exact Or.inr ⟨F b, ⟨b, hb, rfl⟩, hfp⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]

theorem dFinG {k : Nat} {A : Set (Sig n)} (F : Fin k → DSig n) (c : Nat)
    (H : ∀ i, BuildN A (dSet {F i}) c 0) :
    BuildN A (dSet (Set.range F)) (k * c) 0 := by
  have h := dListBuild (List.finRange k) F c (fun i _ => H i)
  rw [List.length_finRange] at h
  refine relax h le_rfl ?_ le_rfl le_rfl
  rintro f ⟨p, ⟨i, rfl⟩, hfp⟩
  exact ⟨F i, ⟨i, List.mem_finRange i, rfl⟩, hfp⟩

end Dual068

namespace TwoSAT

def lit {m : Nat} (i : Fin m) (c : Bool) : Fin (2 * m) :=
  ⟨2 * i.val + c.toNat, by
    cases c
    · simp only [Bool.toNat_false]; omega
    · simp only [Bool.toNat_true]; omega⟩

def varOf {m : Nat} (u : Fin (2 * m)) : Fin m :=
  ⟨u.val / 2, by omega⟩

def polOf {m : Nat} (u : Fin (2 * m)) : Bool :=
  decide (u.val % 2 = 1)

def opp {m : Nat} (u : Fin (2 * m)) : Fin (2 * m) :=
  lit (varOf u) (!(polOf u))

theorem varOf_lit {m : Nat} (i : Fin m) (c : Bool) : varOf (lit i c) = i := by
  apply Fin.ext
  cases c
  · simp only [varOf, lit, Bool.toNat_false, add_zero]; omega
  · simp only [varOf, lit, Bool.toNat_true]; omega

theorem polOf_lit {m : Nat} (i : Fin m) (c : Bool) : polOf (lit i c) = c := by
  cases c
  · simp only [polOf, lit, Bool.toNat_false, add_zero, decide_eq_false_iff_not]
    omega
  · simp only [polOf, lit, Bool.toNat_true]
    exact decide_eq_true (by omega)

theorem lit_var_pol {m : Nat} (u : Fin (2 * m)) : lit (varOf u) (polOf u) = u := by
  apply Fin.ext
  simp only [lit, varOf, polOf]
  by_cases h : u.val % 2 = 1
  · simp only [h, decide_true, Bool.toNat_true]
    omega
  · simp only [h, decide_false, Bool.toNat_false]
    omega

theorem opp_lit {m : Nat} (i : Fin m) (c : Bool) : opp (lit i c) = lit i (!c) := by
  simp only [opp, varOf_lit, polOf_lit]

theorem varOf_opp {m : Nat} (u : Fin (2 * m)) : varOf (opp u) = varOf u := by
  simp only [opp, varOf_lit]

theorem polOf_opp {m : Nat} (u : Fin (2 * m)) : polOf (opp u) = !(polOf u) := by
  simp only [opp, polOf_lit]

theorem opp_opp {m : Nat} (u : Fin (2 * m)) : opp (opp u) = u := by
  simp only [opp, varOf_lit, polOf_lit, Bool.not_not, lit_var_pol]

theorem opp_inj {m : Nat} {u v : Fin (2 * m)} (h : opp u = opp v) : u = v := by
  rw [← opp_opp u, ← opp_opp v, h]

def Legal {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool))) (z b : Fin m → Bool) : Prop :=
  ∀ e ∈ E, ¬ (z e.1.1 = true ∧ z e.2.1 = true ∧ b e.1.1 = e.1.2 ∧ b e.2.1 = e.2.2)

def hasEdge {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (u v : Fin (2 * m)) : Bool :=
  decide (((varOf u, polOf u), (varOf v, !(polOf v))) ∈ E ∨
    ((varOf v, !(polOf v)), (varOf u, polOf u)) ∈ E)

theorem hasEdge_opp {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (u v : Fin (2 * m)) : hasEdge E (opp v) (opp u) = hasEdge E u v := by
  simp only [hasEdge, varOf_opp, polOf_opp, Bool.not_not]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  exact or_comm

def mat0 {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) (u v : Fin (2 * m)) : Bool :=
  if u = v then true else if hasEdge E u v then (z (varOf u) && z (varOf v)) else false

theorem mat0_refl {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) (u : Fin (2 * m)) : mat0 E z u u = true := by
  simp [mat0]

theorem mat0_opp {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) (u v : Fin (2 * m)) : mat0 E z (opp v) (opp u) = mat0 E z u v := by
  simp only [mat0, hasEdge_opp, varOf_opp]
  by_cases huv : u = v
  · subst huv
    simp
  · have hne : opp v ≠ opp u := fun h => huv (opp_inj h).symm
    rw [ite_eq_right hne, ite_eq_right huv]
    split_ifs
    · exact Bool.and_comm _ _
    · rfl

theorem mat0_sound {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z f : Fin m → Bool) (hf : Legal E z f) {u v : Fin (2 * m)}
    (hm : mat0 E z u v = true) (hu : f (varOf u) = polOf u) :
    f (varOf v) = polOf v := by
  by_cases huv : u = v
  · subst huv; exact hu
  · simp only [mat0, ite_eq_right huv] at hm
    split_ifs at hm with he
    simp only [Bool.and_eq_true] at hm
    simp only [hasEdge, decide_eq_true_eq] at he
    by_contra hne
    have hfv : f (varOf v) = !(polOf v) := by
      cases h1 : f (varOf v) <;> cases h2 : polOf v <;> simp_all
    rcases he with he | he
    · exact hf _ he ⟨hm.1, hm.2, hu, hfv⟩
    · exact hf _ he ⟨hm.2, hm.1, hfv, hu⟩

def fw {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) : Nat → Fin (2 * m) → Fin (2 * m) → Bool
  | 0, u, v => mat0 E z u v
  | k + 1, u, v =>
    if hk : k < 2 * m then
      fw E z k u v || (fw E z k u ⟨k, hk⟩ && fw E z k ⟨k, hk⟩ v)
    else
      fw E z k u v

inductive PathK {L : Nat} (M0 : Fin L → Fin L → Bool) : Nat → Fin L → Fin L → Prop
  | base {k u v} : M0 u v = true → PathK M0 k u v
  | step {k u w v} : w.val < k → PathK M0 k u w → PathK M0 k w v → PathK M0 k u v

theorem PathK.mono {L : Nat} {M0 : Fin L → Fin L → Bool} {k1 k2 : Nat} {u v : Fin L}
    (hk : k1 ≤ k2) (h : PathK M0 k1 u v) : PathK M0 k2 u v := by
  induction h with
  | base h0 => exact PathK.base h0
  | step hw _ _ ih1 ih2 => exact PathK.step (Nat.lt_of_lt_of_le hw hk) ih1 ih2

theorem PathK_succ_elim {L : Nat} {M0 : Fin L → Fin L → Bool} {k : Nat} (hk : k < L)
    {u v : Fin L} (h : PathK M0 (k + 1) u v) :
    PathK M0 k u v ∨ (PathK M0 k u ⟨k, hk⟩ ∧ PathK M0 k ⟨k, hk⟩ v) := by
  induction h with
  | base h0 => exact Or.inl (PathK.base h0)
  | @step u w v hw _ _ ih1 ih2 =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hw) with hwlt | hweq
    · rcases ih1 with h1 | ⟨h1a, h1b⟩ <;> rcases ih2 with h2 | ⟨h2a, h2b⟩
      · exact Or.inl (PathK.step hwlt h1 h2)
      · exact Or.inr ⟨PathK.step hwlt h1 h2a, h2b⟩
      · exact Or.inr ⟨h1a, PathK.step hwlt h1b h2⟩
      · exact Or.inr ⟨h1a, h2b⟩
    · have hwk : w = ⟨k, hk⟩ := Fin.ext hweq
      subst hwk
      rcases ih1 with h1 | ⟨h1a, _⟩ <;> rcases ih2 with h2 | ⟨_, h2b⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2b⟩
      · exact Or.inr ⟨h1a, h2⟩
      · exact Or.inr ⟨h1a, h2b⟩

theorem fw_eq_true_iff {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) :
    ∀ k ≤ 2 * m, ∀ u v, fw E z k u v = true ↔ PathK (mat0 E z) k u v := by
  intro k
  induction k with
  | zero =>
    intro _ u v
    constructor
    · intro h; exact PathK.base h
    · intro h
      induction h with
      | base h0 => exact h0
      | step hw _ _ => omega
  | succ k ih =>
    intro hk u v
    have hklt : k < 2 * m := by omega
    have ihk := ih (by omega)
    simp only [fw, dite_eq_left hklt, Bool.or_eq_true, Bool.and_eq_true, ihk]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact PathK.mono (Nat.le_succ k) h
      · exact PathK.step (show (⟨k, hklt⟩ : Fin (2 * m)).val < k + 1 by simp)
          (PathK.mono (Nat.le_succ k) h1) (PathK.mono (Nat.le_succ k) h2)
    · exact PathK_succ_elim hklt

def R {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) (u v : Fin (2 * m)) : Bool :=
  fw E z (2 * m) u v

theorem R_iff {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) (u v : Fin (2 * m)) :
    R E z u v = true ↔ PathK (mat0 E z) (2 * m) u v :=
  fw_eq_true_iff E z (2 * m) le_rfl u v

theorem R_refl {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) (u : Fin (2 * m)) : R E z u u = true :=
  (R_iff E z u u).mpr (PathK.base (mat0_refl E z u))

theorem R_trans {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) {u w v : Fin (2 * m)}
    (h1 : R E z u w = true) (h2 : R E z w v = true) : R E z u v = true :=
  (R_iff E z u v).mpr (PathK.step w.isLt ((R_iff E z u w).mp h1) ((R_iff E z w v).mp h2))

theorem PathK_opp {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) {u v : Fin (2 * m)} (h : PathK (mat0 E z) (2 * m) u v) :
    PathK (mat0 E z) (2 * m) (opp v) (opp u) := by
  induction h with
  | base h0 =>
    apply PathK.base
    rwa [mat0_opp]
  | @step _ w _ _ _ _ ih1 ih2 =>
    exact PathK.step (opp w).isLt ih2 ih1

theorem R_opp {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) (u v : Fin (2 * m)) :
    R E z (opp v) (opp u) = R E z u v := by
  rw [Bool.eq_iff_iff, R_iff, R_iff]
  constructor
  · intro h
    have h' := PathK_opp E z h
    rwa [opp_opp, opp_opp] at h'
  · exact PathK_opp E z

theorem R_sound {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z f : Fin m → Bool) (hf : Legal E z f) {u v : Fin (2 * m)}
    (h : R E z u v = true) (hu : f (varOf u) = polOf u) :
    f (varOf v) = polOf v := by
  have hp := (R_iff E z u v).mp h
  clear h
  induction hp with
  | base h0 => exact mat0_sound E z f hf h0 hu
  | step _ _ _ ih1 ih2 => exact ih2 (ih1 hu)

theorem foldr_or_eq_true_iff {α : Type*} (xs : List α) (f : α → Bool) :
    xs.foldr (fun a acc => f a || acc) false = true ↔ ∃ a ∈ xs, f a = true := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldr_cons, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨b, hb, hfb⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨b, Or.inr hb, hfb⟩
    · rintro ⟨b, rfl | hb, hfb⟩
      · exact Or.inl hfb
      · exact Or.inr ⟨b, hb, hfb⟩

def unfeas {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool))) (z : Fin m → Bool) : Bool :=
  (List.finRange m).foldr
    (fun i acc => (R E z (lit i false) (lit i true) && R E z (lit i true) (lit i false)) || acc)
    false

theorem unfeas_eq_true_iff {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) :
    unfeas E z = true ↔
      ∃ i : Fin m, R E z (lit i false) (lit i true) = true ∧
        R E z (lit i true) (lit i false) = true := by
  rw [unfeas, foldr_or_eq_true_iff]
  simp only [List.mem_finRange, true_and, Bool.and_eq_true]

def T_step {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) : Nat → Fin (2 * m) → Bool
  | 0, _ => false
  | t + 1, u =>
    if ht : t < m then
      let it : Fin m := ⟨t, ht⟩
      let bt := T_step E z t (lit it true) || R E z (lit it false) (lit it true)
      T_step E z t u || (((!bt) && R E z (lit it false) u) || (bt && R E z (lit it true) u))
    else
      T_step E z t u

def bChoice {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) (i : Fin m) : Bool :=
  T_step E z i.val (lit i true) || R E z (lit i false) (lit i true)

theorem T_step_succ_eq {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z : Fin m → Bool) (t : Nat) (ht : t < m) (u : Fin (2 * m)) :
    T_step E z (t + 1) u = (T_step E z t u || R E z (lit ⟨t, ht⟩ (bChoice E z ⟨t, ht⟩)) u) := by
  simp only [T_step, dite_eq_left ht, bChoice]
  cases h : (T_step E z t (lit ⟨t, ht⟩ true) || R E z (lit ⟨t, ht⟩ false) (lit ⟨t, ht⟩ true)) <;>
    simp

def Inv {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool))) (z : Fin m → Bool) (t : Nat) : Prop :=
  (∀ u v, T_step E z t u = true → R E z u v = true → T_step E z t v = true) ∧
  (∀ u, ¬ (T_step E z t u = true ∧ T_step E z t (opp u) = true)) ∧
  (∀ j : Fin m, j.val < t → T_step E z t (lit j (bChoice E z j)) = true)

theorem Inv_zero {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool))) (z : Fin m → Bool) :
    Inv E z 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v h _; simp [T_step] at h
  · intro u h; simp [T_step] at h
  · intro j hj; omega

theorem Inv_step {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool))) (z : Fin m → Bool)
    (hu : unfeas E z = false) {t : Nat} (ht : t < m) (hinv : Inv E z t) :
    Inv E z (t + 1) := by
  let it : Fin m := ⟨t, ht⟩
  let bt : Bool := bChoice E z it
  let l : Fin (2 * m) := lit it bt
  have hstep : ∀ u, T_step E z (t + 1) u = (T_step E z t u || R E z l u) :=
    fun u => T_step_succ_eq E z t ht u
  have hgood : T_step E z t (opp l) = false ∧ R E z l (opp l) = false := by
    cases hbt : bt
    · have hl : l = lit it false := by simp [l, hbt]
      have ho : opp l = lit it true := by rw [hl, opp_lit]; rfl
      have hbt0 : T_step E z t (lit it true) = false ∧ R E z (lit it false) (lit it true) = false :=
        Bool.or_eq_false_iff.mp hbt
      rw [ho, hl]
      exact hbt0
    · have hl : l = lit it true := by simp [l, hbt]
      have ho : opp l = lit it false := by rw [hl, opp_lit]; rfl
      have hbt1 : T_step E z t (lit it true) = true ∨ R E z (lit it false) (lit it true) = true :=
        Bool.or_eq_true _ _ |>.mp hbt
      rw [ho, hl]
      constructor
      · cases hf : T_step E z t (lit it false)
        · rfl
        · exfalso
          rcases hbt1 with ht1 | hr1
          · exact hinv.2.1 (lit it false) ⟨hf, by simpa [opp_lit] using ht1⟩
          · exact hinv.2.1 (lit it false) ⟨hf, by simpa [opp_lit] using hinv.1 _ _ hf hr1⟩
      · cases hr : R E z (lit it true) (lit it false)
        · rfl
        · exfalso
          rcases hbt1 with ht1 | hr1
          · exact hinv.2.1 (lit it true) ⟨ht1, by simpa [opp_lit] using hinv.1 _ _ ht1 hr⟩
          · have huf : unfeas E z = true := (unfeas_eq_true_iff E z).mpr ⟨it, hr1, hr⟩
            rw [hu] at huf
            simp at huf
  refine ⟨?_, ?_, ?_⟩
  · intro u v htu hruv
    rw [hstep u, Bool.or_eq_true] at htu
    rw [hstep v, Bool.or_eq_true]
    rcases htu with htu | hrlu
    · exact Or.inl (hinv.1 u v htu hruv)
    · exact Or.inr (R_trans E z hrlu hruv)
  · intro u ⟨h1, h2⟩
    rw [hstep u, Bool.or_eq_true] at h1
    rw [hstep (opp u), Bool.or_eq_true] at h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact hinv.2.1 u ⟨h1, h2⟩
    · have h2' : R E z u (opp l) = true := by
        have := R_opp E z l (opp u)
        rw [opp_opp] at this
        rw [this]
        exact h2
      have hbad := hinv.1 u (opp l) h1 h2'
      rw [hgood.1] at hbad; simp at hbad
    · have h1' : R E z (opp u) (opp l) = true := by
        rwa [R_opp]
      have hbad := hinv.1 (opp u) (opp l) h2 h1'
      rw [hgood.1] at hbad; simp at hbad
    · have h2' : R E z u (opp l) = true := by
        have := R_opp E z l (opp u)
        rw [opp_opp] at this
        rw [this]
        exact h2
      have hbad := R_trans E z h1 h2'
      rw [hgood.2] at hbad; simp at hbad
  · intro j hj
    rw [hstep]
    rw [Bool.or_eq_true]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjlt | hjeq
    · exact Or.inl (hinv.2.2 j hjlt)
    · have hji : j = it := Fin.ext hjeq
      subst hji
      exact Or.inr (R_refl E z l)

theorem Inv_le {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool))) (z : Fin m → Bool)
    (hu : unfeas E z = false) : ∀ t ≤ m, Inv E z t := by
  intro t
  induction t with
  | zero => intro _; exact Inv_zero E z
  | succ t ih =>
    intro ht
    exact Inv_step E z hu (by omega) (ih (by omega))

theorem bChoice_legal {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (hE : ∀ e ∈ E, e.1.1 ≠ e.2.1) (z : Fin m → Bool) (hu : unfeas E z = false) :
    Legal E z (bChoice E z) := by
  have hinv := Inv_le E z hu m le_rfl
  intro e he ⟨hz1, hz2, hb1, hb2⟩
  let u := lit e.1.1 e.1.2
  let v := lit e.2.1 (!e.2.2)
  have huv : u ≠ v := by
    intro h
    have hv := congrArg varOf h
    simp only [u, v, varOf_lit] at hv
    exact hE e he hv
  have hedge : hasEdge E u v = true := by
    simp only [hasEdge, decide_eq_true_eq, u, v, varOf_lit, polOf_lit, Bool.not_not]
    exact Or.inl he
  have hmat : mat0 E z u v = true := by
    simp only [mat0, ite_eq_right huv, hedge, ite_true, u, v, varOf_lit, hz1, hz2, Bool.and_self]
  have hRuv : R E z u v = true := (R_iff E z u v).mpr (PathK.base hmat)
  have hTu : T_step E z m u = true := by
    have := hinv.2.2 e.1.1 e.1.1.isLt
    rwa [hb1] at this
  have hTov : T_step E z m (opp v) = true := by
    have := hinv.2.2 e.2.1 e.2.1.isLt
    rw [hb2] at this
    simpa [v, opp_lit] using this
  have hTv : T_step E z m v = true := hinv.1 u v hTu hRuv
  exact hinv.2.1 v ⟨hTv, hTov⟩

theorem unfeas_eq_false_of_legal {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z f : Fin m → Bool) (hf : Legal E z f) : unfeas E z = false := by
  cases hu : unfeas E z
  · rfl
  · exfalso
    obtain ⟨i, h1, h2⟩ := (unfeas_eq_true_iff E z).mp hu
    cases hfi : f i
    · have h' := R_sound E z f hf h1 (by simp [varOf_lit, polOf_lit, hfi])
      simp only [varOf_lit, polOf_lit, hfi] at h'
      simp at h'
    · have h' := R_sound E z f hf h2 (by simp [varOf_lit, polOf_lit, hfi])
      simp only [varOf_lit, polOf_lit, hfi] at h'
      simp at h'

theorem unfeas_iff_not_feasible {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (hE : ∀ e ∈ E, e.1.1 ≠ e.2.1) (z : Fin m → Bool) :
    unfeas E z = true ↔ ¬ ∃ b, Legal E z b := by
  constructor
  · rintro hu ⟨b, hb⟩
    have := unfeas_eq_false_of_legal E z b hb
    rw [hu] at this
    simp at this
  · intro hnf
    cases hu : unfeas E z
    · exfalso
      exact hnf ⟨bChoice E z, bChoice_legal E hE z hu⟩
    · rfl

theorem bChoice_lex_least {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (z f : Fin m → Bool) (hf : Legal E z f) (i : Fin m)
    (hpre : ∀ j : Fin m, j < i → bChoice E z j = f j)
    (hbi : bChoice E z i = true) : f i = true := by
  have hT : ∀ t ≤ i.val, ∀ u, T_step E z t u = true → f (varOf u) = polOf u := by
    intro t
    induction t with
    | zero =>
      intro _ u h
      simp [T_step] at h
    | succ t ih =>
      intro ht u htu
      have htm : t < m := by omega
      rw [T_step_succ_eq E z t htm u, Bool.or_eq_true] at htu
      rcases htu with h1 | h2
      · exact ih (by omega) u h1
      · have hlt : (⟨t, htm⟩ : Fin m) < i :=
          Fin.lt_def.mpr (show t < i.val by omega)
        have heq := hpre ⟨t, htm⟩ hlt
        exact R_sound E z f hf h2 (by simp [varOf_lit, polOf_lit, heq])
  simp only [bChoice, Bool.or_eq_true] at hbi
  rcases hbi with h1 | h2
  · have := hT i.val le_rfl (lit i true) h1
    simpa [varOf_lit, polOf_lit] using this
  · cases hfi : f i
    · have h' := R_sound E z f hf h2 (by simp [varOf_lit, polOf_lit, hfi])
      simp only [varOf_lit, polOf_lit, hfi] at h'
      simp at h'
    · rfl

end TwoSAT

namespace Circuit1194

open PEqualNP.CircuitLowerBounds Build068 Construct Construct2 Construct3 Final Dual068 TwoSAT

theorem dMem_mono {n : Nat} {A B : Set (Sig n)} {p : DSig n}
    (hp : dMem p A) (hsub : A ⊆ B) : dMem p B :=
  ⟨hsub hp.1, hsub hp.2⟩

theorem dMem_not {n : Nat} {A : Set (Sig n)} {p : DSig n}
    (hp : dMem p A) : dMem (dNot p) A :=
  ⟨hp.2, hp.1⟩

theorem dOrAndG {n : Nat} {A : Set (Sig n)} {p q r : DSig n}
    (hp : dMem p A) (hq : dMem q A) (hr : dMem r A) :
    BuildN A (dSet {dOr p (dAnd q r)}) 4 0 := by
  have h1 := dAndG hq hr
  have h2 := dOrG (A := A ∪ dSet {dAnd q r}) (dMem_mono hp Set.subset_union_left)
    (dMem_of_mem rfl Set.subset_union_right)
  exact relax (seq h1 h2) le_rfl Set.subset_union_right le_rfl le_rfl

theorem dStepUpdateG {n : Nat} {A : Set (Sig n)} {t bt r0 r1 : DSig n}
    (ht : dMem t A) (hbt : dMem bt A) (hr0 : dMem r0 A) (hr1 : dMem r1 A) :
    BuildN A (dSet {dOr t (dOr (dAnd (dNot bt) r0) (dAnd bt r1))}) 8 0 := by
  let p1 := dAnd (dNot bt) r0
  let p2 := dAnd bt r1
  let p3 := dOr p1 p2
  have h1 : BuildN A (dSet {p1}) 2 0 := dAndG (dMem_not hbt) hr0
  have h2 : BuildN (A ∪ dSet {p1}) (dSet {p2}) 2 0 :=
    dAndG (dMem_mono hbt Set.subset_union_left) (dMem_mono hr1 Set.subset_union_left)
  have h12 := seq h1 h2
  have h3 : BuildN (A ∪ (dSet {p1} ∪ dSet {p2})) (dSet {p3}) 2 0 :=
    dOrG (dMem_of_mem rfl (Set.subset_union_left.trans Set.subset_union_right))
      (dMem_of_mem rfl (Set.subset_union_right.trans Set.subset_union_right))
  have h123 := seq h12 h3
  have h4 : BuildN (A ∪ (dSet {p1} ∪ dSet {p2} ∪ dSet {p3})) (dSet {dOr t p3}) 2 0 :=
    dOrG (dMem_mono ht Set.subset_union_left)
      (dMem_of_mem rfl (Set.subset_union_right.trans Set.subset_union_right))
  exact relax (seq h123 h4) le_rfl Set.subset_union_right le_rfl le_rfl

theorem dBuildListUnion {n : Nat} {α : Type*} {A : Set (Sig n)} (xs : List α)
    (S : α → Set (DSig n)) (c : Nat)
    (H : ∀ a ∈ xs, BuildN A (dSet (S a)) c 0) :
    BuildN A (dSet {p | ∃ a ∈ xs, p ∈ S a}) (xs.length * c) 0 := by
  induction xs with
  | nil =>
    refine relax (idle (A := A) (B := ∅) (by simp)) le_rfl ?_ (by simp) (by simp)
    rintro f ⟨p, ⟨a, ha, _⟩, _⟩
    simp at ha
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ dSet (S a)) Set.subset_union_left le_rfl le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ ?_ (by simp)
    · rintro f ⟨p, ⟨b, hb, hpb⟩, hfp⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl ⟨p, hpb, hfp⟩
      · exact Or.inr ⟨p, ⟨b, hb, hpb⟩, hfp⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]

theorem dFin2G {n k l : Nat} {A : Set (Sig n)} (F : Fin k → Fin l → DSig n) (c : Nat)
    (H : ∀ i j, BuildN A (dSet {F i j}) c 0) :
    BuildN A (dSet {p | ∃ i j, p = F i j}) (k * (l * c)) 0 := by
  have h := dBuildListUnion (List.finRange k) (fun i => Set.range (F i)) (l * c)
    (fun i _ => dFinG (F i) c (H i))
  rw [List.length_finRange] at h
  refine relax h le_rfl ?_ le_rfl le_rfl
  rintro f ⟨p, ⟨i, j, rfl⟩, hfp⟩
  exact ⟨F i j, ⟨i, List.mem_finRange i, ⟨j, rfl⟩⟩, hfp⟩

def dFoldOr {n : Nat} {α : Type*} (xs : List α) (F : α → DSig n) (dZero : DSig n) : DSig n :=
  xs.foldr (fun a acc => dOr (F a) acc) dZero

theorem dFoldOr_valid {n : Nat} {α : Type*} (xs : List α) (F : α → DSig n) (dZero : DSig n)
    (x : Fin n → Bool) (hF : ∀ a ∈ xs, dValidAt (F a) x) (hZ : dValidAt dZero x) :
    dValidAt (dFoldOr xs F dZero) x := by
  induction xs with
  | nil => exact hZ
  | cons a xs ih =>
    exact dValid_or (hF a List.mem_cons_self) (ih (fun b hb => hF b (List.mem_cons_of_mem a hb)))

theorem dFoldOr_eval {n : Nat} {α : Type*} (xs : List α) (F : α → DSig n) (dZero : DSig n)
    (x : Fin n → Bool) (hZ : dZero.1 x = false) :
    (dFoldOr xs F dZero).1 x = xs.foldr (fun a acc => (F a).1 x || acc) false := by
  induction xs with
  | nil => exact hZ
  | cons a xs ih =>
    change ((F a).1 x || (dFoldOr xs F dZero).1 x) =
      ((F a).1 x || xs.foldr (fun a acc => (F a).1 x || acc) false)
    rw [ih]

theorem dFoldOr_build {n : Nat} {α : Type*} {A : Set (Sig n)} (xs : List α)
    (F : α → DSig n) (dZero : DSig n)
    (hF : ∀ a ∈ xs, dMem (F a) A) (hZ : dMem dZero A) :
    ∃ B : Set (Sig n), BuildN A B (xs.length * 2) 0 ∧ dMem (dFoldOr xs F dZero) (A ∪ B) := by
  induction xs with
  | nil =>
    refine ⟨∅, relax (idle (A := A) (B := ∅) (by simp)) le_rfl le_rfl (by simp) le_rfl, ?_⟩
    exact dMem_mono hZ Set.subset_union_left
  | cons a xs ih =>
    obtain ⟨B1, H1, hmem1⟩ := ih (fun b hb => hF b (List.mem_cons_of_mem a hb))
    have H2 := dOrG (A := A ∪ B1) (dMem_mono (hF a List.mem_cons_self) Set.subset_union_left) hmem1
    refine ⟨B1 ∪ dSet {dOr (F a) (dFoldOr xs F dZero)},
      relax (seq H1 H2) le_rfl le_rfl ?_ (by simp), ?_⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul]
    · exact dMem_of_mem rfl (Set.subset_union_right.trans Set.subset_union_right)

def extInput {m : Nat} (z : Fin m → Bool) : Fin (m + 2) → Bool :=
  fun k => if h : k.val < m then z ⟨k.val, h⟩ else decide (k.val = m + 1)

theorem inp_extInput_lt {m : Nat} (z : Fin m → Bool) (i : Fin m) :
    inp m i.val (extInput z) = z i := by
  simp [inp, extInput, i.isLt, show i.val < m + 2 by omega]

theorem inp_extInput_m {m : Nat} (z : Fin m → Bool) :
    inp m m (extInput z) = false := by
  simp [inp, extInput]

theorem inp_extInput_m1 {m : Nat} (z : Fin m → Bool) :
    inp m (m + 1) (extInput z) = true := by
  simp [inp, extInput]

def dFalse (m : Nat) : DSig (m + 2) := (inp m m, inp m (m + 1))

def dTrue (m : Nat) : DSig (m + 2) := (inp m (m + 1), inp m m)

def dVar (m : Nat) (NX : Nat → Sig (m + 2)) (i : Fin m) : DSig (m + 2) :=
  (inp m i.val, NX i.val)

def dMat0 (m : Nat) (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (u v : Fin (2 * m)) : DSig (m + 2) :=
  if u = v then dTrue m
  else if hasEdge E u v then dAnd (dVar m NX (varOf u)) (dVar m NX (varOf v))
  else dFalse m

def dFW (m : Nat) (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) : Nat → Fin (2 * m) → Fin (2 * m) → DSig (m + 2)
  | 0, u, v => dMat0 m E NX u v
  | k + 1, u, v =>
    if hk : k < 2 * m then
      dOr (dFW m E NX k u v) (dAnd (dFW m E NX k u ⟨k, hk⟩) (dFW m E NX k ⟨k, hk⟩ v))
    else
      dFW m E NX k u v

def dR (m : Nat) (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (u v : Fin (2 * m)) : DSig (m + 2) :=
  dFW m E NX (2 * m) u v

def dUnfeasPair (m : Nat) (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (i : Fin m) : DSig (m + 2) :=
  dAnd (dR m E NX (lit i false) (lit i true)) (dR m E NX (lit i true) (lit i false))

def dUnfeas (m : Nat) (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) : DSig (m + 2) :=
  dFoldOr (List.finRange m) (dUnfeasPair m E NX) (dFalse m)

def dT (m : Nat) (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) : Nat → Fin (2 * m) → DSig (m + 2)
  | 0, _ => dFalse m
  | t + 1, u =>
    if ht : t < m then
      let it : Fin m := ⟨t, ht⟩
      let dBt := dOr (dT m E NX t (lit it true)) (dR m E NX (lit it false) (lit it true))
      dOr (dT m E NX t u)
        (dOr (dAnd (dNot dBt) (dR m E NX (lit it false) u))
             (dAnd dBt (dR m E NX (lit it true) u)))
    else
      dT m E NX t u

def dB (m : Nat) (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (i : Fin m) : DSig (m + 2) :=
  dOr (dT m E NX i.val (lit i true)) (dR m E NX (lit i false) (lit i true))

def tapSig (m : Nat) (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (i : Fin m) (c : Bool) : Sig (m + 2) :=
  if c then ban (inp m i.val) (dB m E NX i).1 else ban (inp m i.val) (dB m E NX i).2

theorem dMat0_sem {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (z : Fin m → Bool)
    (hNX : ∀ i : Fin m, NX i.val (extInput z) = !(z i)) (u v : Fin (2 * m)) :
    dValidAt (dMat0 m E NX u v) (extInput z) ∧
      (dMat0 m E NX u v).1 (extInput z) = mat0 E z u v := by
  have hvVar : ∀ i : Fin m, dValidAt (dVar m NX i) (extInput z) := by
    intro i
    dsimp [dValidAt, dVar]
    rw [hNX i, inp_extInput_lt]
  have hvFalse : dValidAt (dFalse m) (extInput z) := by
    simp [dValidAt, dFalse, inp_extInput_m, inp_extInput_m1]
  have hvTrue : dValidAt (dTrue m) (extInput z) := by
    simp [dValidAt, dTrue, inp_extInput_m, inp_extInput_m1]
  simp only [dMat0, mat0]
  split_ifs
  · exact ⟨hvTrue, inp_extInput_m1 z⟩
  · refine ⟨dValid_and (hvVar (varOf u)) (hvVar (varOf v)), ?_⟩
    simp [dAnd, ban, dVar, inp_extInput_lt]
  · exact ⟨hvFalse, inp_extInput_m z⟩

theorem dFW_sem {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (z : Fin m → Bool)
    (hNX : ∀ i : Fin m, NX i.val (extInput z) = !(z i)) :
    ∀ k u v, dValidAt (dFW m E NX k u v) (extInput z) ∧
      (dFW m E NX k u v).1 (extInput z) = fw E z k u v := by
  intro k
  induction k with
  | zero => exact dMat0_sem E NX z hNX
  | succ k ih =>
    intro u v
    simp only [dFW, fw]
    split_ifs with hk
    · have h1 := ih u v
      have h2 := ih u ⟨k, hk⟩
      have h3 := ih ⟨k, hk⟩ v
      refine ⟨dValid_or h1.1 (dValid_and h2.1 h3.1), ?_⟩
      simp only [dOr, dAnd, bor, ban, h1.2, h2.2, h3.2]
    · exact ih u v

theorem dR_sem {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (z : Fin m → Bool)
    (hNX : ∀ i : Fin m, NX i.val (extInput z) = !(z i)) (u v : Fin (2 * m)) :
    dValidAt (dR m E NX u v) (extInput z) ∧
      (dR m E NX u v).1 (extInput z) = R E z u v :=
  dFW_sem E NX z hNX (2 * m) u v

theorem dUnfeas_sem {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (z : Fin m → Bool)
    (hNX : ∀ i : Fin m, NX i.val (extInput z) = !(z i)) :
    (dUnfeas m E NX).1 (extInput z) = unfeas E z := by
  rw [dUnfeas, dFoldOr_eval _ _ _ _ (inp_extInput_m z), unfeas]
  congr 1
  funext i acc
  simp only [dUnfeasPair, dAnd, ban, (dR_sem E NX z hNX _ _).2]

theorem dT_sem {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (z : Fin m → Bool)
    (hNX : ∀ i : Fin m, NX i.val (extInput z) = !(z i)) :
    ∀ t u, dValidAt (dT m E NX t u) (extInput z) ∧
      (dT m E NX t u).1 (extInput z) = T_step E z t u := by
  intro t
  induction t with
  | zero =>
    intro u
    exact ⟨by simp [dValidAt, dT, dFalse, inp_extInput_m, inp_extInput_m1],
      by simp [dT, dFalse, T_step, inp_extInput_m]⟩
  | succ t ih =>
    intro u
    simp only [dT, T_step]
    split_ifs with ht
    · let it : Fin m := ⟨t, ht⟩
      have hTu := ih u
      have hT1 := ih (lit it true)
      have hR01 := dR_sem E NX z hNX (lit it false) (lit it true)
      have hR0u := dR_sem E NX z hNX (lit it false) u
      have hR1u := dR_sem E NX z hNX (lit it true) u
      let dBt := dOr (dT m E NX t (lit it true)) (dR m E NX (lit it false) (lit it true))
      have hvBt : dValidAt dBt (extInput z) := dValid_or hT1.1 hR01.1
      have heBt : dBt.1 (extInput z) = (T_step E z t (lit it true) || R E z (lit it false) (lit it true)) := by
        simp only [dBt, dOr, bor, hT1.2, hR01.2]
      have heNBt : (dNot dBt).1 (extInput z) = !(dBt.1 (extInput z)) := hvBt
      refine ⟨dValid_or hTu.1 (dValid_or (dValid_and (dValid_not hvBt) hR0u.1) (dValid_and hvBt hR1u.1)), ?_⟩
      change (dOr (dT m E NX t u)
        (dOr (dAnd (dNot dBt) (dR m E NX (lit it false) u))
             (dAnd dBt (dR m E NX (lit it true) u)))).1 (extInput z) = _
      simp only [dOr, dAnd, bor, ban, hTu.2, heNBt, heBt, hR0u.2, hR1u.2]
      rfl
    · exact ih u

theorem dB_sem {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (z : Fin m → Bool)
    (hNX : ∀ i : Fin m, NX i.val (extInput z) = !(z i)) (i : Fin m) :
    dValidAt (dB m E NX i) (extInput z) ∧
      (dB m E NX i).1 (extInput z) = bChoice E z i := by
  have h1 := dT_sem E NX z hNX i.val (lit i true)
  have h2 := dR_sem E NX z hNX (lit i false) (lit i true)
  exact ⟨dValid_or h1.1 h2.1, by simp only [dB, bChoice, dOr, bor, h1.2, h2.2]⟩

theorem tapSig_eval {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (z : Fin m → Bool)
    (hNX : ∀ i : Fin m, NX i.val (extInput z) = !(z i)) (i : Fin m) (c : Bool) :
    tapSig m E NX i c (extInput z) = (z i && decide (bChoice E z i = c)) := by
  have hB := dB_sem E NX z hNX i
  cases c
  · simp only [tapSig, Bool.false_eq_true, ite_false, ban, inp_extInput_lt]
    rw [hB.1, hB.2]
    cases bChoice E z i <;> rfl
  · simp only [tapSig, ite_true, ban, inp_extInput_lt]
    rw [hB.2]
    cases bChoice E z i <;> rfl

theorem dMat0_build {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (A : Set (Sig (m + 2)))
    (hF : dMem (dFalse m) A) (hT : dMem (dTrue m) A)
    (hV : ∀ i : Fin m, dMem (dVar m NX i) A) :
    ∃ B : Set (Sig (m + 2)),
      BuildN A B (8 * (m * m)) 0 ∧
      ∀ u v, dMem (dMat0 m E NX u v) (A ∪ B) := by
  have H := dFin2G (A := A) (dMat0 m E NX) 2 (fun u v => by
    simp only [dMat0]
    split_ifs
    · exact relax (dIdle hT) le_rfl le_rfl (by omega) le_rfl
    · exact dAndG (hV (varOf u)) (hV (varOf v))
    · exact relax (dIdle hF) le_rfl le_rfl (by omega) le_rfl)
  have hcost : (2 * m) * ((2 * m) * 2) = 8 * (m * m) := by
    calc (2 * m) * ((2 * m) * 2) = (2 * 2 * 2) * (m * m) := by
          simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = 8 * (m * m) := rfl
  refine ⟨dSet {p | ∃ u v, p = dMat0 m E NX u v},
    relax H le_rfl le_rfl (le_of_eq hcost) le_rfl, ?_⟩
  intro u v
  exact dMem_of_mem (S := {p | ∃ i j, p = dMat0 m E NX i j}) ⟨u, v, rfl⟩ Set.subset_union_right

theorem dFW_build {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) :
    ∀ (k : Nat) (A : Set (Sig (m + 2))),
      (∀ u v, dMem (dMat0 m E NX u v) A) →
      ∃ B : Set (Sig (m + 2)),
        BuildN A B (k * (16 * (m * m))) 0 ∧
        ∀ u v, dMem (dFW m E NX k u v) (A ∪ B) := by
  intro k
  induction k with
  | zero =>
    intro A h0
    refine ⟨∅, relax (idle (A := A) (B := ∅) (by simp)) le_rfl le_rfl (by simp) le_rfl, ?_⟩
    intro u v
    exact dMem_mono (h0 u v) Set.subset_union_left
  | succ k ih =>
    intro A h0
    obtain ⟨B1, H1, hmem1⟩ := ih A h0
    have H2 := dFin2G (A := A ∪ B1) (dFW m E NX (k + 1)) 4 (fun u v => by
      simp only [dFW]
      split_ifs with hk
      · exact dOrAndG (hmem1 u v) (hmem1 u ⟨k, hk⟩) (hmem1 ⟨k, hk⟩ v)
      · exact relax (dIdle (hmem1 u v)) le_rfl le_rfl (by omega) le_rfl)
    have hcost2 : (2 * m) * ((2 * m) * 4) = 16 * (m * m) := by
      calc (2 * m) * ((2 * m) * 4) = (2 * 2 * 4) * (m * m) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ = 16 * (m * m) := rfl
    refine ⟨B1 ∪ dSet {p | ∃ u v, p = dFW m E NX (k + 1) u v},
      relax (seq H1 H2) le_rfl le_rfl (by rw [hcost2, Nat.succ_mul k]) (by simp), ?_⟩
    intro u v
    exact dMem_of_mem (S := {p | ∃ i j, p = dFW m E NX (k + 1) i j}) ⟨u, v, rfl⟩
      (Set.subset_union_right.trans Set.subset_union_right)

theorem dUnfeas_build {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (A : Set (Sig (m + 2)))
    (hF : dMem (dFalse m) A) (hR : ∀ u v, dMem (dR m E NX u v) A) :
    ∃ B : Set (Sig (m + 2)),
      BuildN A B (4 * m) 0 ∧ dMem (dUnfeas m E NX) (A ∪ B) := by
  have H1 := dFinG (A := A) (dUnfeasPair m E NX) 2 (fun i =>
    dAndG (hR (lit i false) (lit i true)) (hR (lit i true) (lit i false)))
  let B1 := dSet (Set.range (dUnfeasPair m E NX))
  obtain ⟨B2, H2, hmem2⟩ := dFoldOr_build (A := A ∪ B1) (List.finRange m)
    (dUnfeasPair m E NX) (dFalse m)
    (fun i _ => dMem_of_mem (S := Set.range (dUnfeasPair m E NX)) ⟨i, rfl⟩ Set.subset_union_right)
    (dMem_mono hF Set.subset_union_left)
  rw [List.length_finRange] at H2
  refine ⟨B1 ∪ B2, relax (seq H1 H2) le_rfl le_rfl (by omega) (by simp), ?_⟩
  exact dMem_mono hmem2 (by intro f hf; simp only [Set.mem_union] at hf ⊢; tauto)

theorem dT_build {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) :
    ∀ t ≤ m, ∀ (A : Set (Sig (m + 2))),
      dMem (dFalse m) A → (∀ u v, dMem (dR m E NX u v) A) →
      ∃ B : Set (Sig (m + 2)),
        BuildN A B (t * (2 + 16 * m)) 0 ∧
        (∀ u, dMem (dT m E NX t u) (A ∪ B)) ∧
        (∀ i : Fin m, i.val < t → dMem (dB m E NX i) (A ∪ B)) := by
  intro t
  induction t with
  | zero =>
    intro _ A hF _
    refine ⟨∅, relax (idle (A := A) (B := ∅) (by simp)) le_rfl le_rfl (by simp) le_rfl,
      fun _ => dMem_mono hF Set.subset_union_left, fun i hi => by omega⟩
  | succ t ih =>
    intro ht A hF hR
    have htm : t < m := by omega
    obtain ⟨B1, H1, hT1, hB1⟩ := ih (by omega) A hF hR
    let it : Fin m := ⟨t, htm⟩
    have hR1 : ∀ u v, dMem (dR m E NX u v) (A ∪ B1) :=
      fun u v => dMem_mono (hR u v) Set.subset_union_left
    have H2 : BuildN (A ∪ B1) (dSet {dB m E NX it}) 2 0 :=
      dOrG (hT1 (lit it true)) (hR1 (lit it false) (lit it true))
    let A2 := (A ∪ B1) ∪ dSet {dB m E NX it}
    have hBt2 : dMem (dB m E NX it) A2 := dMem_of_mem rfl Set.subset_union_right
    have H3 : BuildN A2 (dSet (Set.range (dT m E NX (t + 1)))) ((2 * m) * 8) 0 :=
      dFinG (A := A2) (dT m E NX (t + 1)) 8 (fun u => by
        simp only [dT, dite_eq_left htm]
        exact dStepUpdateG (dMem_mono (hT1 u) Set.subset_union_left) hBt2
          (dMem_mono (hR1 (lit it false) u) Set.subset_union_left)
          (dMem_mono (hR1 (lit it true) u) Set.subset_union_left))
    have H23 := seq H2 (relax H3 (C := (A ∪ B1) ∪ dSet {dB m E NX it}) le_rfl le_rfl le_rfl le_rfl)
    have Hall := seq H1 H23
    have hcost : t * (2 + 16 * m) + (2 + (2 * m) * 8) = (t + 1) * (2 + 16 * m) := by
      have h16 : (2 * m) * 8 = 16 * m := by omega
      rw [h16, Nat.succ_mul t]
    refine ⟨B1 ∪ (dSet {dB m E NX it} ∪ dSet (Set.range (dT m E NX (t + 1)))),
      relax Hall le_rfl le_rfl (le_of_eq hcost) (by simp), ?_, ?_⟩
    · intro u
      exact dMem_of_mem (S := Set.range (dT m E NX (t + 1))) ⟨u, rfl⟩
        (Set.subset_union_right.trans (Set.subset_union_right.trans Set.subset_union_right))
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hilt | hieq
      · exact dMem_mono (hB1 i hilt) (by intro f hf; simp only [Set.mem_union] at hf ⊢; tauto)
      · have heq : i = it := Fin.ext hieq
        subst heq
        exact dMem_of_mem rfl
          (Set.subset_union_left.trans (Set.subset_union_right.trans Set.subset_union_right))

theorem tapSig_build {m : Nat} (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (NX : Nat → Sig (m + 2)) (A : Set (Sig (m + 2)))
    (hinp : ∀ i : Fin m, inp m i.val ∈ A) (hB : ∀ i : Fin m, dMem (dB m E NX i) A) :
    ∃ B : Set (Sig (m + 2)),
      BuildN A B (2 * m) 0 ∧ ∀ i c, tapSig m E NX i c ∈ A ∪ B := by
  have Htrue := finG (A := A) (fun i : Fin m => tapSig m E NX i true) 1 0 (fun i => by
    simp only [tapSig, ite_true]
    exact andG (hinp i) (hB i).1)
  have Hfalse := finG (A := A ∪ Set.range (fun i : Fin m => tapSig m E NX i true))
    (fun i : Fin m => tapSig m E NX i false) 1 0 (fun i => by
      simp only [tapSig, Bool.false_eq_true, ite_false]
      exact andG (Or.inl (hinp i)) (Or.inl (hB i).2))
  refine ⟨Set.range (fun i : Fin m => tapSig m E NX i true) ∪
      Set.range (fun i : Fin m => tapSig m E NX i false),
    relax (seq Htrue Hfalse) le_rfl le_rfl (by omega) (by simp), ?_⟩
  intro i c
  cases c
  · exact Or.inr (Or.inr ⟨i, rfl⟩)
  · exact Or.inr (Or.inl ⟨i, rfl⟩)

theorem solve_zero (r : Nat) (E : Finset ((Fin 0 × Bool) × (Fin 0 × Bool))) :
    let legal := fun (z b : Fin 0 → Bool) => ∀ e ∈ E,
      ¬ (z e.1.1 = true ∧ z e.2.1 = true ∧ b e.1.1 = e.1.2 ∧ b e.2.1 = e.2.2)
    let feasible := fun z => ∃ b, legal z b
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin 0 → Bool → Fin (0 + 2 + C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (0 + 2) C ∧ C.output < 0 + 2 + C.size ∧
      PEqualNP.NotBracket.notCount C ≤ r ∧ C.size ≤ 64 * (0 + 1) ^ 3 ∧
      ∀ z, let wires := List.ofFn z ++ [false, true]
           (C.eval wires = true ↔ ¬ feasible z) ∧
           (feasible z → ∃ b, legal z b ∧
             (∀ f, legal z f → ∀ i, (∀ j, j < i → b j = f j) → b i = true → f i = true) ∧
             ∀ i c, (C.wires wires).getD (tap i c).val false = (z i && decide (b i = c))) := by
  refine ⟨⟨[], 0⟩, fun i => Fin.elim0 i, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · simp [PEqualNP.MetaComplexity.NestedCover.ReadsBack]
  · simp [Circuit.size]
  · simp [PEqualNP.NotBracket.notCount]
  · simp [Circuit.size]
  · intro z
    let b0 : Fin 0 → Bool := fun i => Fin.elim0 i
    have hleg0 : ∀ e ∈ E, ¬ (z e.1.1 = true ∧ z e.2.1 = true ∧ b0 e.1.1 = e.1.2 ∧ b0 e.2.1 = e.2.2) :=
      fun e _ => Fin.elim0 e.1.1
    have hfeas : ∃ b : Fin 0 → Bool, ∀ e ∈ E, ¬ (z e.1.1 = true ∧ z e.2.1 = true ∧ b e.1.1 = e.1.2 ∧ b e.2.1 = e.2.2) :=
      ⟨b0, hleg0⟩
    refine ⟨?_, ?_⟩
    · simp only [Circuit.eval, Circuit.wires, List.foldl_nil, List.ofFn_zero, List.nil_append,
        List.getD_cons_zero, Bool.false_eq_true, false_iff, not_not]
      exact hfeas
    · intro _
      exact ⟨b0, hleg0, fun _ _ i => Fin.elim0 i, fun i => Fin.elim0 i⟩

theorem solve_pos (m r : Nat) (hm : 0 < m) (E : Finset ((Fin m × Bool) × (Fin m × Bool)))
    (hE : ∀ e ∈ E, e.1.1 ≠ e.2.1) (hmr : m < 2 ^ r) :
    let legal := fun (z b : Fin m → Bool) => ∀ e ∈ E,
      ¬ (z e.1.1 = true ∧ z e.2.1 = true ∧ b e.1.1 = e.1.2 ∧ b e.2.1 = e.2.2)
    let feasible := fun z => ∃ b, legal z b
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Bool → Fin (m + 2 + C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (m + 2) C ∧ C.output < m + 2 + C.size ∧
      PEqualNP.NotBracket.notCount C ≤ r ∧ C.size ≤ 64 * (m + 1) ^ 3 ∧
      ∀ z, let wires := List.ofFn z ++ [false, true]
           (C.eval wires = true ↔ ¬ feasible z) ∧
           (feasible z → ∃ b, legal z b ∧
             (∀ f, legal z f → ∀ i, (∀ j, j < i → b j = f j) → b i = true → f i = true) ∧
             ∀ i c, (C.wires wires).getD (tap i c).val false = (z i && decide (b i = c))) := by
  let d : Nat := Nat.log 2 m + 1
  have hm0 : m ≠ 0 := by omega
  have hlog_le : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm0
  have hd_lt : m < 2 ^ d := Nat.lt_pow_succ_log_self (by omega) m
  have hd_le_r : d ≤ r := by
    by_contra h
    have h1 : r ≤ Nat.log 2 m := by omega
    have h2 : 2 ^ r ≤ 2 ^ Nat.log 2 m := Nat.pow_le_pow_right (by omega) h1
    omega
  have hpowd : 2 ^ d ≤ 2 * m := by
    change 2 ^ (Nat.log 2 m + 1) ≤ 2 * m
    rw [pow_succ]
    omega
  let S0 : Set (Sig (m + 2)) := Set.range (fun i : Fin (m + 2) => (fun x => x i : Sig (m + 2)))
  have Hstart : GateBridgeN.Scheduled (m + 2) id 0 0 S0 :=
    GateBridgeN.start (fun i : Fin (m + 2) => (fun x => x i : Sig (m + 2))) (fun _ _ => rfl)
  have hinpS0 : ∀ i < m + 2, inp m i ∈ S0 :=
    fun i hi => ⟨⟨i, hi⟩, by funext x; simp [inp, hi]⟩
  obtain ⟨NL, NX, _, H_inv, hcor_inv⟩ :=
    rest_build m m d hd_lt le_rfl m 0 (by omega) S0 [] (by simp) (by simp) hinpS0
  have hNX_sem : ∀ z : Fin m → Bool, ∀ i : Fin m, NX i.val (extInput z) = !(z i) := by
    intro z i
    have hrest : restC m 0 (extInput z) ≤ m := by
      unfold restC
      calc ((Finset.Ico 0 m).filter (fun k => inp m k (extInput z) = false)).card
          ≤ (Finset.Ico 0 m).card := Finset.card_filter_le _ _
        _ = m := by simp
    have h := (hcor_inv (extInput z) (inp_extInput_m1 z) (inp_extInput_m z) (by simp)
      (by simpa using hrest)).2 i.val (Nat.zero_le _) i.isLt
    rw [h, inp_extInput_lt]
  let B_inv := {f | f ∈ NL ∨ ∃ i, 0 ≤ i ∧ i < m ∧ f = NX i}
  let A1 := S0 ∪ B_inv
  have hF1 : dMem (dFalse m) A1 :=
    ⟨Or.inl (hinpS0 m (by omega)), Or.inl (hinpS0 (m + 1) (by omega))⟩
  have hT1 : dMem (dTrue m) A1 :=
    ⟨Or.inl (hinpS0 (m + 1) (by omega)), Or.inl (hinpS0 m (by omega))⟩
  have hV1 : ∀ i : Fin m, dMem (dVar m NX i) A1 := fun i =>
    ⟨Or.inl (hinpS0 i.val (by omega)), Or.inr (Or.inr ⟨i.val, Nat.zero_le _, i.isLt, rfl⟩)⟩
  obtain ⟨B2, H2, hMat0⟩ := dMat0_build E NX A1 hF1 hT1 hV1
  let A2 := A1 ∪ B2
  obtain ⟨B3, H3, hR3⟩ := dFW_build E NX (2 * m) A2 hMat0
  let A3 := A2 ∪ B3
  have hF3 : dMem (dFalse m) A3 := dMem_mono hF1 (Set.subset_union_left.trans Set.subset_union_left)
  obtain ⟨B4, H4, hUnf4⟩ := dUnfeas_build E NX A3 hF3 hR3
  let A4 := A3 ∪ B4
  have hF4 : dMem (dFalse m) A4 := dMem_mono hF3 Set.subset_union_left
  have hR4 : ∀ u v, dMem (dR m E NX u v) A4 := fun u v => dMem_mono (hR3 u v) Set.subset_union_left
  obtain ⟨B5, H5, _, hB5⟩ := dT_build E NX m le_rfl A4 hF4 hR4
  let A5 := A4 ∪ B5
  have hinp5 : ∀ i : Fin m, inp m i.val ∈ A5 := fun i =>
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hinpS0 i.val (by omega))))))
  have hB5' : ∀ i : Fin m, dMem (dB m E NX i) A5 := fun i => hB5 i i.isLt
  obtain ⟨B6, H6, hTap6⟩ := tapSig_build E NX A5 hinp5 hB5'
  have H12 := seq H_inv H2
  have H123 := seq H12 (relax H3 (C := S0 ∪ (B_inv ∪ B2))
    (by intro f hf; simp only [A2, A1, Set.mem_union] at hf ⊢; tauto) le_rfl le_rfl le_rfl)
  have H1234 := seq H123 (relax H4 (C := S0 ∪ (B_inv ∪ B2 ∪ B3))
    (by intro f hf; simp only [A3, A2, A1, Set.mem_union] at hf ⊢; tauto) le_rfl le_rfl le_rfl)
  have H12345 := seq H1234 (relax H5 (C := S0 ∪ (B_inv ∪ B2 ∪ B3 ∪ B4))
    (by intro f hf; simp only [A4, A3, A2, A1, Set.mem_union] at hf ⊢; tauto) le_rfl le_rfl le_rfl)
  have Hall := seq H12345 (relax H6 (C := S0 ∪ (B_inv ∪ B2 ∪ B3 ∪ B4 ∪ B5))
    (by intro f hf; simp only [A5, A4, A3, A2, A1, Set.mem_union] at hf ⊢; tauto) le_rfl le_rfl le_rfl)
  obtain ⟨c, hc, cn, hcn, HS⟩ := Hall.run Hstart le_rfl
  obtain ⟨gs, hgs, hnc, hrb, hfan, hw⟩ := HS
  have hUnf_mem : (dUnfeas m E NX).1 ∈ S0 ∪ (B_inv ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6) := by
    have := hUnf4.1
    simp only [A3, A2, A1, Set.mem_union] at this ⊢
    tauto
  have hTap_mem : ∀ i c_b, tapSig m E NX i c_b ∈ S0 ∪ (B_inv ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6) := by
    intro i c_b
    have := hTap6 i c_b
    simp only [A5, A4, A3, A2, A1, Set.mem_union] at this ⊢
    tauto
  obtain ⟨out_idx, hout_lt, hout_val⟩ := hw _ hUnf_mem
  have htap_ex : ∀ i : Fin m, ∀ c_b : Bool,
      ∃ w : Nat, w < m + 2 + (0 + c) ∧
        ∀ x : Fin (m + 2) → Bool,
          ((Circuit.mk gs 0).wires (List.ofFn x)).getD w false = tapSig m E NX i c_b x :=
    fun i c_b => hw _ (hTap_mem i c_b)
  choose w hw_lt hw_val using htap_ex
  have hcost_bound : c ≤ 64 * (m + 1) ^ 3 := by
    have hsum : (∑ i ∈ Finset.Ico 0 m, min i m) ≤ m * m := by
      calc (∑ i ∈ Finset.Ico 0 m, min i m)
          ≤ ∑ _i ∈ Finset.Ico 0 m, m := Finset.sum_le_sum (fun i _ => Nat.min_le_right i m)
        _ = m * m := by simp
    have hTd : T d ≤ 8 * m := by
      have h1 := T_add d
      omega
    have hcostC : costC m m d 0 ≤ 6 * (m * m) + 8 * m := by
      unfold costC
      omega
    have hfwc : (2 * m) * (16 * (m * m)) = 32 * (m * m * m) := by
      have h1 : (2 * m) * (16 * (m * m)) = 2 * (16 * (m * m * m)) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm]
      omega
    have htc : m * (2 + 16 * m) = 16 * (m * m) + 2 * m := by
      rw [Nat.mul_add]
      have : m * (16 * m) = 16 * (m * m) := by
        simp only [Nat.mul_assoc, Nat.mul_comm]
      omega
    have hcube : (m + 1) ^ 3 = m * m * m + 3 * (m * m) + 3 * m + 1 := by
      simp only [pow_succ, pow_zero, one_mul, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]
      omega
    rw [hfwc, htc] at hc
    omega
  let C : Circuit := ⟨gs, out_idx⟩
  refine ⟨C, fun i c_b => ⟨w i c_b, by simp only [C, Circuit.size, hgs]; exact hw_lt i c_b⟩,
    hfan, hrb, ?_, ?_, ?_, ?_⟩
  · simp only [C, Circuit.size, hgs]
    exact hout_lt
  · change PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ r
    rw [hnc]
    omega
  · simp only [C, Circuit.size, hgs]
    omega
  · intro z
    have hchain : List.ofFn z ++ [false, true] = List.ofFn (extInput z) := ofFn_chain m z
    have heval : C.eval (List.ofFn z ++ [false, true]) = unfeas E z := by
      rw [hchain]
      change ((Circuit.mk gs 0).wires (List.ofFn (extInput z))).getD out_idx false = unfeas E z
      rw [hout_val (extInput z)]
      exact dUnfeas_sem E NX z (hNX_sem z)
    refine ⟨?_, ?_⟩
    · rw [heval]
      exact unfeas_iff_not_feasible E hE z
    · intro hfeas
      have huf : unfeas E z = false := by
        obtain ⟨b, hb⟩ := hfeas
        exact unfeas_eq_false_of_legal E z b hb
      refine ⟨bChoice E z, bChoice_legal E hE z huf, ?_, ?_⟩
      · intro f hf i hpre hbi
        exact bChoice_lex_least E z f hf i hpre hbi
      · intro i c_b
        rw [hchain]
        change ((Circuit.mk gs 0).wires (List.ofFn (extInput z))).getD (w i c_b) false =
          (z i && decide (bChoice E z i = c_b))
        rw [hw_val i c_b (extInput z), tapSig_eval E NX z (hNX_sem z) i c_b]

end Circuit1194

end PEqualNP.Outside.L_lib_1194_aux

theorem PEqualNP.Outside.L_lib_1194 : (∀ (m r : Nat) (E : Finset ((Fin m × Bool) × (Fin m × Bool))),
  (∀ e ∈ E, e.1.1 ≠ e.2.1) → m < 2^r →
  let legal := fun (z b : Fin m → Bool) => ∀ e ∈ E,
    ¬ (z e.1.1 = true ∧ z e.2.1 = true ∧ b e.1.1 = e.1.2 ∧ b e.2.1 = e.2.2)
  let feasible := fun z => ∃ b, legal z b
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Bool → Fin (m+2+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (m+2) C ∧ C.output < m+2+C.size ∧
    PEqualNP.NotBracket.notCount C ≤ r ∧ C.size ≤ 64*(m+1)^3 ∧
    ∀ z, let wires := List.ofFn z ++ [false,true]
         (C.eval wires = true ↔ ¬ feasible z) ∧
         (feasible z → ∃ b, legal z b ∧
           (∀ f, legal z f → ∀ i, (∀ j, j < i → b j = f j) → b i = true → f i = true) ∧
           ∀ i c, (C.wires wires).getD (tap i c).val false = (z i && decide (b i = c)))) := by
  intro m r E hE hmr
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact PEqualNP.Outside.L_lib_1194_aux.Circuit1194.solve_zero r E
  · exact PEqualNP.Outside.L_lib_1194_aux.Circuit1194.solve_pos m r hm E hE hmr
