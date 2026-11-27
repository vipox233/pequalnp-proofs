import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25507_aux

namespace GateBridge

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

variable {α : Type*}

private def Scheduled (n : ℕ) (F : α → (Fin n → Bool) → Bool) (k : ℕ) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : ℕ, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x

private theorem wireLength (C : Circuit) (w : List Bool) :
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

private theorem start {n : ℕ} {F : α → (Fin n → Bool) → Bool}
    (input : Fin n → α) (h : ∀ i x, F (input i) x = x i) :
    Scheduled n F 0 (Set.range input) := by
  refine ⟨[], rfl, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp [FanInTwo]
  · intro a ha
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    refine ⟨i.val, by simp, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, h i x]

private theorem restrict {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k S) (hsub : T ⊆ S) : Scheduled n F k T := by
  obtain ⟨gs, hs, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hr, hf, fun a ha => hw a (hsub ha)⟩

private theorem realizeDeps {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α}
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

private theorem push {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α}
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

private theorem finish {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α} {out : α}
    (h : Scheduled n F k S) (hout : out ∈ S) :
    ∃ C : Circuit, C.size = k ∧ ReadsBack n C ∧ FanInTwo C ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F out x := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨i, _, hi⟩ := hw out hout
  exact ⟨⟨gs, i⟩, hgs, hr, hf, hi⟩

end GateBridge

namespace BitBridge

private def stepBit (k word i : Nat) : Bool :=
  word.testBit i ^^ (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))

private def wordStep (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc i => if stepBit k word i then acc ||| 2 ^ i else acc) 0

private theorem testBit_foldl_set (p : Nat → Bool) (xs : List Nat) (acc i : Nat) :
    (xs.foldl (fun a j => if p j then a ||| 2 ^ j else a) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih]
    by_cases hji : j = i
    · subst j
      cases p i <;> simp
    · cases p j <;> simp [hji, Ne.symm hji]

private theorem testBit_wordStep_all (k word i : Nat) :
    (wordStep k word).testBit i = (decide (i < k) && stepBit k word i) := by
  simp only [wordStep, testBit_foldl_set, Nat.zero_testBit, Bool.false_or, List.mem_range]

private theorem testBit_wordStep {k word i : Nat} (hi : i < k) :
    (wordStep k word).testBit i =
      (word.testBit i ^^ (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))) := by
  simp [testBit_wordStep_all, stepBit, hi]

private theorem wordStep_lt (k word : Nat) : wordStep k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  simp [testBit_wordStep_all, Nat.not_lt_of_ge hi]

private theorem lt_two_pow_iff_testBit {n k a : Nat} (hn : n < 2 ^ k) :
    n < 2 ^ a ↔ ∀ i, a ≤ i → i < k → n.testBit i = false := by
  constructor
  · intro ha i hai _
    exact Nat.testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hai))
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hai
    by_cases hi : i < k
    · exact h i hai hi
    · exact Nat.testBit_lt_two_pow
        (hn.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_gt hi)))

private def rot (k s w : Nat) : Nat :=
  ((w <<< (s % k)) ||| (w >>> (k - s % k))) % 2 ^ k

private theorem rot_lt {k s w : Nat} : rot k s w < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem bit_rot {k s w i : Nat} (wlt : w < 2 ^ k) (ilt : i < k) :
    (rot k s w).testBit i = w.testBit ((i + k - s % k) % k) := by
  have hs : s % k < k := Nat.mod_lt _ (by omega)
  simp only [rot, Nat.testBit_mod_two_pow, ilt, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ i
  · have hz : w.testBit (k - s % k + i) = false :=
      Nat.testBit_lt_two_pow (wlt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (i + k - s % k) % k = i - s % k := by
      rw [Nat.mod_eq_sub_mod (by omega : k ≤ i + k - s % k), Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, hz, he]
  · have he : (i + k - s % k) % k = k - s % k + i := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, he]

private theorem lt_xor {a b k : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hm := Nat.pow_le_pow_right Nat.zero_lt_two hi
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hm),
    Nat.testBit_lt_two_pow (hb.trans_le hm)]

private theorem wordStep_eq (k word : Nat) :
    wordStep k word = (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0 := by
  unfold wordStep
  congr 1
  funext a j
  change (if stepBit k word j then a ||| 2 ^ j else a) =
    a ||| ((stepBit k word j).toNat <<< j)
  cases stepBit k word j <;> simp [Nat.shiftLeft_eq]

private theorem rbit {k w i : Nat} (h : i < k) {m : Nat} (hm : m < k)
    (hw : w < 2 ^ k) : (rot k m w).testBit i = w.testBit ((i + k - m) % k) := by
  rw [bit_rot hw h, Nat.mod_eq_of_lt hm]

end BitBridge

namespace Build25507

open PEqualNP.CircuitLowerBounds

variable {n : Nat}
private abbrev Sig (n : Nat) := (Fin n → Bool) → Bool
private def Build (A B : Set (Sig n)) (b : Nat) : Prop :=
  True ∧ (∀ {m S}, GateBridge.Scheduled n id m S → A ⊆ S →
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B))

private theorem Build.run {A B : Set (Sig n)} {b m S} (H : Build A B b)
    (HS : GateBridge.Scheduled n id m S) (hA : A ⊆ S) :
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B) := H.2 HS hA

private theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : Build A B 0 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

private theorem relax {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c, hc, HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c, hc.trans h, GateBridge.restrict HS' (Set.union_subset_union le_rfl hB)⟩

private theorem seq {A B C : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  obtain ⟨d, hd, K⟩ := H.run HS hA
  obtain ⟨e, he, K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d + e, Nat.add_le_add hd he, by simpa [Nat.add_assoc, Set.union_assoc] using K'⟩

private theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨1, le_rfl, ?_⟩
  have h := GateBridge.push HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridge.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

private def an (f g : Sig n) : Sig n := fun x => f x && g x
private def or (f g : Sig n) : Sig n := fun x => f x || g x
private def nt (f : Sig n) : Sig n := fun x => !f x
private def xo (f g : Sig n) : Sig n := fun x => xor (f x) (g x)

private theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {an f g} 1 :=
  one .and [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

private theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {or f g} 1 :=
  one .or [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, or])

private theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : Build A {nt f} 1 :=
  one .not [f] (by simp) (by simp) (by simpa using hf) _ (by simp [GateOp.eval, nt])

private theorem xorG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
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

private theorem constG {A : Set (Sig n)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b
  · exact one .or [] (by simp) (by simp) (by simp) _ (by intro; rfl)
  · exact one .and [] (by simp) (by simp) (by simp) _ (by intro; rfl)

private theorem mixG {A : Set (Sig n)} {f g h : Sig n}
    (hf : f ∈ A) (hg : g ∈ A) (hh : h ∈ A) : Build A {xo (xo f g) h} 8 := by
  exact relax (seq (xorG hf hg)
    (xorG (A := A ∪ {xo f g}) (f := xo f g) (by simp) (Or.inl hh))) le_rfl (by simp) le_rfl

private theorem nonlinG {A : Set (Sig n)} {f g h : Sig n}
    (hf : f ∈ A) (hg : g ∈ A) (hh : h ∈ A) :
    Build A {xo f (an (nt g) h)} 6 := by
  have h₁ := notG hg
  have h₂ := andG (A := A ∪ {nt g}) (f := nt g) (by simp) (Or.inl hh)
  have h₃ := xorG (A := A ∪ ({nt g} ∪ {an (nt g) h})) (Or.inl hf)
    (g := an (nt g) h) (by simp)
  exact relax (seq (seq h₁ h₂) h₃) le_rfl (by simp) le_rfl

private theorem flipG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) (b : Bool) :
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

private theorem pivotG {A : Set (Sig n)} {a b c u : Sig n}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hu : u ∈ A) (d : Bool) :
    Build A {fun w => xor (xor (xor (a w) (!(b w) && c w)) (u w)) d} 11 := by
  let f := xo a (an (nt b) c)
  have H₁ : Build A {f} 6 := nonlinG ha hb hc
  let g := xo f u
  have H₂ : Build (A ∪ {f}) {g} 4 := xorG (Or.inr rfl) (Or.inl hu)
  have H₃ := flipG (A := A ∪ ({f} ∪ {g})) (f := g) (by simp) d
  exact relax (seq (seq H₁ H₂) H₃) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

private theorem topological {α : Type*} [DecidableEq α] {A : Set (Sig n)}
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
        refine Finset.mem_erase.mpr ⟨?_, hl⟩
        intro heq
        subst l
        exact (Nat.not_lt_of_ge (himax j (Finset.mem_of_mem_erase hj))) hlt
      have Hs := IH (s.erase i) Hsub fun j hj =>
        relax (H j (Finset.mem_of_mem_erase hj))
          (by rintro f (hf | ⟨l, hl, hlt, rfl⟩)
              · exact Or.inl hf
              · exact Or.inr ⟨l, hstep j hj l hl hlt, hlt, rfl⟩) le_rfl le_rfl
      have Hi := relax (H i hi) (C := A ∪ {f | ∃ j ∈ s.erase i, f = F j})
        (by rintro f (hf | ⟨j, hj, hlt, rfl⟩)
            · exact Or.inl hf
            · exact Or.inr ⟨j, Finset.mem_erase.mpr ⟨by aesop, hj⟩, rfl⟩) le_rfl le_rfl
      refine relax (seq Hs Hi) le_rfl ?_ ?_
      · rintro f ⟨j, hj, rfl⟩
        by_cases he : j = i
        · exact Or.inr (by simp [he])
        · exact Or.inl ⟨j, Finset.mem_erase.mpr ⟨he, hj⟩, rfl⟩
      · rw [Finset.sum_erase_add _ _ hi]
    · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp)

private theorem anyG {A : Set (Sig n)} (xs : List (Sig n))
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

private theorem allG {α : Type*} [Fintype α] {A : Set (Sig n)}
    (F : α → Sig n) (c : Nat) (H : ∀ i, Build A {F i} c) :
    Build A (Set.range F) (Fintype.card α * c) := by
  classical
  have K := topological F (fun _ => 0) (fun _ => c) Finset.univ
    (fun i _ => relax (H i) Set.subset_union_left le_rfl le_rfl)
  refine relax (by simpa only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] using K) le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, Finset.mem_univ _, rfl⟩

private theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c : Nat)
    (H : ∀ i, Build A {F i} c) : Build A (Set.range F) (k * c) := by
  simpa only [Fintype.card_fin] using allG F c H

private theorem notAnyG {A : Set (Sig n)} (xs : List (Sig n))
    (hs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => !(xs.any (fun f => f x))} (xs.length + 1) :=
  relax (seq (anyG xs hs hfalse) (notG (f := fun x => xs.any (fun f => f x))
    (Or.inr rfl))) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

end Build25507

namespace Joint25507

open BitBridge Build25507
open PEqualNP.MetaComplexity (tableIndex)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem pack_succ {n : Nat} (x : Fin (n + 1) → Bool) :
    tableIndex x = tableIndex (fun i : Fin n => x i.castSucc)
        + (if x (Fin.last n) = true then 2 ^ n else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  rfl

private theorem pack_lt : ∀ {n : Nat} (x : Fin n → Bool), tableIndex x < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [tableIndex]
  | succ n IH =>
    intro x
    rw [pack_succ, pow_succ]
    have := IH (fun i : Fin n => x i.castSucc)
    split <;> omega

private theorem bit_pack : ∀ {n : Nat} (x : Fin n → Bool) (i : Fin n),
    (tableIndex x).testBit i = x i := by
  intro n
  induction n with
  | zero => intro x i; exact i.elim0
  | succ n IH =>
    intro x i
    have hlt := pack_lt (fun i : Fin n => x i.castSucc)
    rw [pack_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.val_last]
      cases x (Fin.last n) <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [Nat.add_zero, Nat.testBit_lt_two_pow hlt]
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
    · change (tableIndex (fun i : Fin n => x i.castSucc) +
        (if x (Fin.last n) = true then 2 ^ n else 0)).testBit j.val = x j.castSucc
      cases x (Fin.last n) <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [Nat.add_zero]; exact IH _ j
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt j.isLt]; exact IH _ j

private def constant (k t : Nat) : Nat := 3 ^ (k + t) % 2 ^ k
private def updateRound (k d e t w state : Nat) : Nat :=
  wordStep k (state ^^^ rot k d state ^^^ rot k (k - d) state) ^^^ rot k e w ^^^ constant k t

private def rowWord (k w u : Nat) : Nat → Nat
  | 0 => rot k 1 w ^^^ u
  | t + 1 => updateRound k 1 (2 * t) (t + 1) w (rowWord k w u t)

private def colWord (k r w v : Nat) : Nat → Nat
  | 0 => rot k 3 w ^^^ v
  | t + 1 => updateRound k 2 (3 * (t + 1) + 1) (r + (t + 1)) w (colWord k r w v t)

private theorem upd_lt (k d e t w state : Nat) : updateRound k d e t w state < 2 ^ k :=
  lt_xor (lt_xor (wordStep_lt _ _) rot_lt) (Nat.mod_lt _ (Nat.two_pow_pos _))

private theorem rowWord_lt {k w u : Nat} (hu : u < 2 ^ k) (t : Nat) : rowWord k w u t < 2 ^ k := by
  cases t
  · exact lt_xor rot_lt hu
  · exact upd_lt ..

private theorem colWord_lt {k r w v : Nat} (hv : v < 2 ^ k) (t : Nat) : colWord k r w v t < 2 ^ k := by
  cases t
  · exact lt_xor rot_lt hv
  · exact upd_lt ..

private theorem round_fold {α : Type*} (f : Nat → α) (op : α → Nat → α)
    (hf : ∀ j, f (j + 1) = op (f j) j) (t : Nat) :
    (List.range t).foldl op (f 0) = f t := by
  induction t with
  | zero => rfl
  | succ t IH => rw [List.range_succ, List.foldl_append, IH, List.foldl_cons, List.foldl_nil, hf]

private def ix {k : Nat} (hk : 0 < k) (i : Nat) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩
private def bits {k n : Nat} (w : (Fin n → Bool) → Nat) (i : Fin k) : Sig n :=
  fun v => (w v).testBit i
private def prev {k : Nat} (hk : 0 < k) (i : Fin k) (d : Nat) : Fin k := ix hk (i.val + k - d % k)

private theorem rotG {k n : Nat} (hk : 0 < k) {A : Set (Sig n)}
    {w : (Fin n → Bool) → Nat} (hw : ∀ v, w v < 2 ^ k) (hs : ∀ i : Fin k, bits w i ∈ A)
    (d : Nat) (i : Fin k) : bits (fun v => rot k d (w v)) i ∈ A := by
  convert hs (prev hk i d) using 1
  funext v
  exact bit_rot (s := d) (hw v) i.isLt

private theorem xorBits {k n : Nat} {A : Set (Sig n)} {w u : (Fin n → Bool) → Nat} (i : Fin k)
    (hw : bits w i ∈ A) (hu : bits u i ∈ A) :
    Build A {bits (fun v => w v ^^^ u v) i} 4 := by
  have he : bits (fun v => w v ^^^ u v) i = xo (bits w i) (bits u i) := by
    funext v; exact Nat.testBit_xor ..
  rw [he]; exact xorG hw hu

private theorem roundG {k n : Nat} (hk : 0 < k) {A : Set (Sig n)} (d : Nat)
    (w s : (Fin n → Bool) → Nat) (hw : ∀ v, w v < 2 ^ k) (hs : ∀ v, s v < 2 ^ k)
    (hW : ∀ i : Fin k, bits w i ∈ A) (hS : ∀ i : Fin k, bits s i ∈ A) (e t : Nat) :
    Build A (Set.range (fun i : Fin k => bits (fun v => updateRound k d e t (w v) (s v)) i)) (19 * k) := by
  let w₁ := fun v => s v ^^^ rot k d (s v) ^^^ rot k (k - d) (s v)
  let F := fun i : Fin k => bits w₁ i
  have H : Build A (Set.range F) (k * 8) := finG F 8 fun i => by
    have E : F i = xo (xo (bits s i) (bits (fun v => rot k d (s v)) i))
        (bits (fun v => rot k (k - d) (s v)) i) := by
      funext v; simp only [F, bits, w₁, Nat.testBit_xor, xo]
    rw [E]
    exact mixG (hS i) (rotG hk hs hS d i) (rotG hk hs hS (k - d) i)
  let G := fun i : Fin k => bits (fun v => updateRound k d e t (w v) (s v)) i
  have J : Build (A ∪ Set.range F) (Set.range G) (k * 11) := finG G 11 fun i => by
    have E : G i = (fun v => xor (xor (xor (F i v) (!(F (ix hk (i.val + 1)) v) && F (ix hk (i.val + 2)) v))
      (bits (fun v => rot k e (w v)) i v)) ((constant k t).testBit i)) := by
      funext v
      simp only [G, bits, updateRound, Nat.testBit_xor, testBit_wordStep i.isLt]
      simp only [F, bits, w₁, ix, Nat.testBit_xor]
    rw [E]
    exact pivotG (Or.inr ⟨_, rfl⟩) (Or.inr ⟨_, rfl⟩) (Or.inr ⟨_, rfl⟩)
      (Or.inl (rotG hk hw hW e i)) _
  exact relax (seq H J) le_rfl Set.subset_union_right (by omega)

private theorem rowSchedule {k n : Nat} (hk : 0 < k) {A : Set (Sig n)}
    (w u : (Fin n → Bool) → Nat) (hw : ∀ x, w x < 2 ^ k) (hu : ∀ x, u x < 2 ^ k)
    (hW : ∀ i : Fin k, bits w i ∈ A) (hU : ∀ i : Fin k, bits u i ∈ A) (t : Nat) :
    Build A (Set.range (fun i : Fin k => bits (fun x => rowWord k (w x) (u x) t) i)) (4 * k + 19 * k * t) := by
  induction t with
  | zero =>
    simpa [Nat.mul_comm] using (finG (fun i : Fin k => bits (fun x => rowWord k (w x) (u x) 0) i) 4
      (fun i => xorBits i (rotG hk hw hW 1 i) (hU i)))
  | succ t IH =>
    have H := roundG hk 1 (A := A ∪ Set.range (fun i : Fin k => bits (fun x => rowWord k (w x) (u x) t) i)) w (fun x => rowWord k (w x) (u x) t) hw
      (fun x => rowWord_lt (hu x) t) (fun i => Or.inl (hW i)) (fun i => Or.inr ⟨i, rfl⟩)
        (2 * t) (t + 1)
    exact relax (seq IH H) le_rfl Set.subset_union_right (by ring_nf; omega)

private theorem colSchedule {k n : Nat} (hk : 0 < k) {A : Set (Sig n)}
    (r : Nat) (w v : (Fin n → Bool) → Nat) (hw : ∀ x, w x < 2 ^ k) (hv : ∀ x, v x < 2 ^ k)
    (hW : ∀ i : Fin k, bits w i ∈ A) (hV : ∀ i : Fin k, bits v i ∈ A) (t : Nat) :
    Build A (Set.range (fun i : Fin k => bits (fun x => colWord k r (w x) (v x) t) i)) (4 * k + 19 * k * t) := by
  induction t with
  | zero =>
    simpa [Nat.mul_comm] using (finG (fun i : Fin k => bits (fun x => colWord k r (w x) (v x) 0) i) 4
      (fun i => xorBits i (rotG hk hw hW 3 i) (hV i)))
  | succ t IH =>
    have H := roundG hk 2 (A := A ∪ Set.range (fun i : Fin k => bits (fun x => colWord k r (w x) (v x) t) i)) w (fun x => colWord k r (w x) (v x) t) hw
      (fun x => colWord_lt (hv x) t) (fun i => Or.inl (hW i)) (fun i => Or.inr ⟨i, rfl⟩)
        (3 * (t + 1) + 1) (r + (t + 1))
    exact relax (seq IH H) le_rfl Set.subset_union_right (by ring_nf; omega)

private theorem thresholds {k n : Nat} {A : Set (Sig n)} (h : Nat) (w : (Fin n → Bool) → Nat)
    (hw : ∀ v, w v < 2 ^ k) (hs : ∀ i : Fin k, h ≤ i.val → bits w i ∈ A)
    (hfalse : (fun _ => false) ∈ A) : Build A {fun v => decide (w v < 2 ^ h)} (k + 1) := by
  let xs : List (Fin k) := (List.finRange k).filter (fun i => decide (h ≤ i.val))
  have hs' : ∀ f ∈ xs.map (bits w), f ∈ A := by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    exact hs i (by simpa [xs] using hi)
  have he : (fun v => !((xs.map (bits w)).any (fun f => f v))) = (fun v => decide (w v < 2 ^ h)) := by
    funext v
    apply Bool.eq_iff_iff.mpr
    rw [Bool.not_eq_true', decide_eq_true_eq, lt_two_pow_iff_testBit (hw v)]
    simp only [List.any_eq_false, List.mem_map, forall_exists_index, and_imp]
    constructor
    · intro H i hi hik
      exact Bool.eq_false_iff.mpr (H _ ⟨i, hik⟩ (by simp [xs, hi]) rfl)
    · intro H f i hi he
      subst f
      exact Bool.eq_false_iff.mp (H _ (by simpa [xs] using hi) i.isLt)
  rw [← he]
  refine relax (notAnyG _ hs' hfalse) le_rfl le_rfl (Nat.succ_le_succ ?_)
  simpa [xs] using (List.length_filter_le (p := fun i : Fin k => decide (h ≤ i.val)) (List.finRange k))

private def AgreeCyc (k p L R : Nat) (w₁ w₂ : Nat) : Prop :=
  ∀ d : Nat, d ≤ L + R → w₁.testBit ((p + k - L + d) % k) = w₂.testBit ((p + k - L + d) % k)

private theorem agreeCyc_mono {k p L₁ R₁ L₂ R₂ w₁ w₂ : Nat}
    (hL : L₁ ≤ L₂) (hR : R₁ ≤ R₂) (hL2 : L₂ ≤ k)
    (H : AgreeCyc k p L₂ R₂ w₁ w₂) : AgreeCyc k p L₁ R₁ w₁ w₂ := by
  intro d hd
  have h1 := H (L₂ - L₁ + d) (by omega)
  have he : p + k - L₂ + (L₂ - L₁ + d) = p + k - L₁ + d := by omega
  rw [← he]
  exact h1

private theorem agreeCyc_shift1 {k p L R δ w₁ w₂ : Nat}
    (hL : L + 1 ≤ k) (hδ : δ ≤ 4)
    (H : AgreeCyc k p (L + 1) (R + 3) w₁ w₂) :
    AgreeCyc k ((p + k - 1 + δ) % k) L R w₁ w₂ := by
  intro d hd
  have h1 := H (δ + d) (by omega)
  have he : ((p + k - 1 + δ) % k + k - L + d) % k = (p + k - (L + 1) + (δ + d)) % k := by
    apply Nat.ModEq.add_right_cancel' (L + 1)
    change (((p + k - 1 + δ) % k + k - L + d) + (L + 1)) % k =
      ((p + k - (L + 1) + (δ + d)) + (L + 1)) % k
    have ea : (p + k - 1 + δ) % k + k - L + d + (L + 1) =
        (p + k - 1 + δ) % k + (d + 1) + k := by omega
    have eb : p + k - (L + 1) + (δ + d) + (L + 1) =
        (p + k - 1 + δ) + (d + 1) := by omega
    rw [ea, eb, Nat.add_mod_right, Nat.mod_add_mod]
  rw [he]
  exact h1

private theorem agreeCyc_shift2 {k p L R δ w₁ w₂ : Nat}
    (hL : L + 2 ≤ k) (hδ : δ ≤ 6)
    (H : AgreeCyc k p (L + 2) (R + 4) w₁ w₂) :
    AgreeCyc k ((p + k - 2 + δ) % k) L R w₁ w₂ := by
  intro d hd
  have h1 := H (δ + d) (by omega)
  have he : ((p + k - 2 + δ) % k + k - L + d) % k = (p + k - (L + 2) + (δ + d)) % k := by
    apply Nat.ModEq.add_right_cancel' (L + 2)
    change (((p + k - 2 + δ) % k + k - L + d) + (L + 2)) % k =
      ((p + k - (L + 2) + (δ + d)) + (L + 2)) % k
    have ea : (p + k - 2 + δ) % k + k - L + d + (L + 2) =
        (p + k - 2 + δ) % k + (d + 2) + k := by omega
    have eb : p + k - (L + 2) + (δ + d) + (L + 2) =
        (p + k - 2 + δ) + (d + 2) := by omega
    rw [ea, eb, Nat.add_mod_right, Nat.mod_add_mod]
  rw [he]
  exact h1

private theorem step_mix1_congr {k s₁ s₂ p : Nat} (hk : 2 ≤ k)
    (hs1 : s₁ < 2 ^ k) (hs2 : s₂ < 2 ^ k) (hp : p < k)
    (H : ∀ δ ≤ 4, s₁.testBit ((p + k - 1 + δ) % k) = s₂.testBit ((p + k - 1 + δ) % k)) :
    (wordStep k (s₁ ^^^ rot k 1 s₁ ^^^ rot k (k - 1) s₁)).testBit p =
    (wordStep k (s₂ ^^^ rot k 1 s₂ ^^^ rot k (k - 1) s₂)).testBit p := by
  have hkpos : 0 < k := by omega
  have hlin (j : Nat) (hj : j ≤ 2) :
      (s₁ ^^^ rot k 1 s₁ ^^^ rot k (k - 1) s₁).testBit ((p + j) % k) =
      (s₂ ^^^ rot k 1 s₂ ^^^ rot k (k - 1) s₂).testBit ((p + j) % k) := by
    have hm := Nat.mod_lt (p + j) hkpos
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
      rbit hm (by omega) hs1, rbit hm (by omega) hs1,
      rbit hm (by omega) hs2, rbit hm (by omega) hs2]
    have e0 : (p + j) % k = (p + k - 1 + (j + 1)) % k := by
      rw [show p + k - 1 + (j + 1) = (p + j) + k by omega, Nat.add_mod_right]
    have e1 : ((p + j) % k + k - 1) % k = (p + k - 1 + j) % k := by
      apply Nat.ModEq.add_right_cancel' 1
      change ((p + j) % k + k - 1 + 1) % k = (p + k - 1 + j + 1) % k
      rw [show (p + j) % k + k - 1 + 1 = (p + j) % k + k by omega,
        show p + k - 1 + j + 1 = (p + j) + k by omega,
        Nat.add_mod_right, Nat.add_mod_right, Nat.mod_mod]
    have e2 : ((p + j) % k + k - (k - 1)) % k = (p + k - 1 + (j + 2)) % k := by
      rw [show (p + j) % k + k - (k - 1) = (p + j) % k + 1 by omega, Nat.mod_add_mod,
        show p + k - 1 + (j + 2) = (p + j + 1) + k by omega, Nat.add_mod_right]
    rw [e1, e2, e0, H (j + 1) (by omega), H j (by omega), H (j + 2) (by omega)]
  rw [testBit_wordStep hp, testBit_wordStep hp]
  have hp0 : p = (p + 0) % k := (Nat.mod_eq_of_lt hp).symm
  conv_lhs => rw [hp0]
  conv_rhs => rw [hp0]
  rw [show ((p + 0) % k + 1) % k = (p + 1) % k by rw [Nat.mod_add_mod],
    show ((p + 0) % k + 2) % k = (p + 2) % k by rw [Nat.mod_add_mod]]
  rw [hlin 0 (by omega), hlin 1 (by omega), hlin 2 (by omega)]

private theorem step_mix2_congr {k s₁ s₂ p : Nat} (hk : 3 ≤ k)
    (hs1 : s₁ < 2 ^ k) (hs2 : s₂ < 2 ^ k) (hp : p < k)
    (H : ∀ δ ≤ 6, s₁.testBit ((p + k - 2 + δ) % k) = s₂.testBit ((p + k - 2 + δ) % k)) :
    (wordStep k (s₁ ^^^ rot k 2 s₁ ^^^ rot k (k - 2) s₁)).testBit p =
    (wordStep k (s₂ ^^^ rot k 2 s₂ ^^^ rot k (k - 2) s₂)).testBit p := by
  have hkpos : 0 < k := by omega
  have hlin (j : Nat) (hj : j ≤ 2) :
      (s₁ ^^^ rot k 2 s₁ ^^^ rot k (k - 2) s₁).testBit ((p + j) % k) =
      (s₂ ^^^ rot k 2 s₂ ^^^ rot k (k - 2) s₂).testBit ((p + j) % k) := by
    have hm := Nat.mod_lt (p + j) hkpos
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
      rbit hm (by omega) hs1, rbit hm (by omega) hs1,
      rbit hm (by omega) hs2, rbit hm (by omega) hs2]
    have e0 : (p + j) % k = (p + k - 2 + (j + 2)) % k := by
      rw [show p + k - 2 + (j + 2) = (p + j) + k by omega, Nat.add_mod_right]
    have e1 : ((p + j) % k + k - 2) % k = (p + k - 2 + j) % k := by
      apply Nat.ModEq.add_right_cancel' 2
      change ((p + j) % k + k - 2 + 2) % k = (p + k - 2 + j + 2) % k
      rw [show (p + j) % k + k - 2 + 2 = (p + j) % k + k by omega,
        show p + k - 2 + j + 2 = (p + j) + k by omega,
        Nat.add_mod_right, Nat.add_mod_right, Nat.mod_mod]
    have e2 : ((p + j) % k + k - (k - 2)) % k = (p + k - 2 + (j + 4)) % k := by
      rw [show (p + j) % k + k - (k - 2) = (p + j) % k + 2 by omega, Nat.mod_add_mod,
        show p + k - 2 + (j + 4) = (p + j + 2) + k by omega, Nat.add_mod_right]
    rw [e1, e2, e0, H (j + 2) (by omega), H j (by omega), H (j + 4) (by omega)]
  rw [testBit_wordStep hp, testBit_wordStep hp]
  have hp0 : p = (p + 0) % k := (Nat.mod_eq_of_lt hp).symm
  conv_lhs => rw [hp0]
  conv_rhs => rw [hp0]
  rw [show ((p + 0) % k + 1) % k = (p + 1) % k by rw [Nat.mod_add_mod],
    show ((p + 0) % k + 2) % k = (p + 2) % k by rw [Nat.mod_add_mod]]
  rw [hlin 0 (by omega), hlin 1 (by omega), hlin 2 (by omega)]

private theorem rowWord_dep {k u w₁ w₂ : Nat} (hu : u < 2 ^ k) (hw1 : w₁ < 2 ^ k) (hw2 : w₂ < 2 ^ k)
    (t : Nat) (ht : max (t + 1) (2 * t) < k) (p : Nat) (hp : p < k)
    (H : AgreeCyc k p (max (t + 1) (2 * t - 2)) (3 * t) w₁ w₂) :
    (rowWord k w₁ u t).testBit p = (rowWord k w₂ u t).testBit p := by
  induction t generalizing p with
  | zero =>
    simp only [rowWord, Nat.testBit_xor]
    rw [rbit hp (by omega) hw1, rbit hp (by omega) hw2]
    have h0 := H 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [show max (0 + 1) (2 * 0 - 2) = 1 by decide] at h0
    rw [h0]
  | succ t IH =>
    simp only [rowWord, updateRound, Nat.testBit_xor]
    have hstep : (wordStep k (rowWord k w₁ u t ^^^ rot k 1 (rowWord k w₁ u t) ^^^ rot k (k - 1) (rowWord k w₁ u t))).testBit p =
        (wordStep k (rowWord k w₂ u t ^^^ rot k 1 (rowWord k w₂ u t) ^^^ rot k (k - 1) (rowWord k w₂ u t))).testBit p := by
      apply step_mix1_congr (by omega) (rowWord_lt hu t) (rowWord_lt hu t) hp
      intro δ hδ
      apply IH (by omega) _ (Nat.mod_lt _ (by omega))
      apply agreeCyc_shift1 (by omega) hδ
      exact agreeCyc_mono (by omega) (by omega) (by omega) H
    have hkey : (rot k (2 * t) w₁).testBit p = (rot k (2 * t) w₂).testBit p := by
      rw [rbit hp (by omega) hw1, rbit hp (by omega) hw2]
      have hk1 := H (max (t + 1 + 1) (2 * (t + 1) - 2) - 2 * t) (by omega)
      have he : p + k - max (t + 1 + 1) (2 * (t + 1) - 2) + (max (t + 1 + 1) (2 * (t + 1) - 2) - 2 * t) =
          p + k - 2 * t := by omega
      rw [he] at hk1
      exact hk1
    rw [hstep, hkey]

private theorem colWord_dep {k r v w₁ w₂ : Nat} (hv : v < 2 ^ k) (hw1 : w₁ < 2 ^ k) (hw2 : w₂ < 2 ^ k)
    (t : Nat) (ht : max (2 * t + 3) (3 * t + 4) < k) (p : Nat) (hp : p < k)
    (H : AgreeCyc k p (max (2 * t + 3) (3 * t + 1)) (4 * t - 3) w₁ w₂) :
    (colWord k r w₁ v t).testBit p = (colWord k r w₂ v t).testBit p := by
  induction t generalizing p with
  | zero =>
    simp only [colWord, Nat.testBit_xor]
    rw [rbit hp (by omega) hw1, rbit hp (by omega) hw2]
    have h0 := H 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [show max (2 * 0 + 3) (3 * 0 + 1) = 3 by decide] at h0
    rw [h0]
  | succ t IH =>
    simp only [colWord, updateRound, Nat.testBit_xor]
    have hstep : (wordStep k (colWord k r w₁ v t ^^^ rot k 2 (colWord k r w₁ v t) ^^^ rot k (k - 2) (colWord k r w₁ v t))).testBit p =
        (wordStep k (colWord k r w₂ v t ^^^ rot k 2 (colWord k r w₂ v t) ^^^ rot k (k - 2) (colWord k r w₂ v t))).testBit p := by
      apply step_mix2_congr (by omega) (colWord_lt hv t) (colWord_lt hv t) hp
      intro δ hδ
      cases t with
      | zero =>
        simp only [colWord, Nat.testBit_xor]
        have hq : (p + k - 2 + δ) % k < k := Nat.mod_lt _ (by omega)
        rw [rbit hq (by omega) hw1, rbit hq (by omega) hw2]
        have h1 := H δ (by omega)
        have he : ((p + k - 2 + δ) % k + k - 3) % k =
            (p + k - max (2 * (0 + 1) + 3) (3 * (0 + 1) + 1) + δ) % k := by
          rw [show max (2 * (0 + 1) + 3) (3 * (0 + 1) + 1) = 5 by decide]
          apply Nat.ModEq.add_right_cancel' 5
          change (((p + k - 2 + δ) % k + k - 3) + 5) % k = ((p + k - 5 + δ) + 5) % k
          have ea : (p + k - 2 + δ) % k + k - 3 + 5 = (p + k - 2 + δ) % k + 2 + k := by omega
          have eb : p + k - 5 + δ + 5 = (p + k - 2 + δ) + 2 := by omega
          rw [ea, eb, Nat.add_mod_right, Nat.mod_add_mod]
        rw [he, h1]
      | succ t' =>
        apply IH (by omega) _ (Nat.mod_lt _ (by omega))
        apply agreeCyc_shift2 (by omega) hδ
        exact agreeCyc_mono (by omega) (by omega) (by omega) H
    have hkey : (rot k (3 * (t + 1) + 1) w₁).testBit p = (rot k (3 * (t + 1) + 1) w₂).testBit p := by
      rw [rbit hp (by omega) hw1, rbit hp (by omega) hw2]
      have hk1 := H (max (2 * (t + 1) + 3) (3 * (t + 1) + 1) - (3 * (t + 1) + 1)) (by omega)
      have he : p + k - max (2 * (t + 1) + 3) (3 * (t + 1) + 1) +
          (max (2 * (t + 1) + 3) (3 * (t + 1) + 1) - (3 * (t + 1) + 1)) =
          p + k - (3 * (t + 1) + 1) := by omega
      rw [he] at hk1
      exact hk1
    rw [hstep, hkey]

private def rowCoreBit (k r w u i : Nat) : Bool :=
  let S := rowWord k w u (r - 1)
  (wordStep k (S ^^^ rot k 1 S ^^^ rot k (k - 1) S) ^^^ constant k r).testBit i

private def colCoreBit (k r w v i : Nat) : Bool :=
  let S := colWord k r w v (r - 1)
  (wordStep k (S ^^^ rot k 2 S ^^^ rot k (k - 2) S) ^^^ constant k (r + r)).testBit i

private theorem rowWord_final_xor {k r w u i : Nat} (hr : 4 ≤ r) (hk : 2 * r < k)
    (hw : w < 2 ^ k) (hi : i < k) :
    (rowWord k w u r).testBit i = xor (rowCoreBit k r w u i) (w.testBit ((i + k - (2 * r - 2)) % k)) := by
  have he : r - 1 + 1 = r := by omega
  conv_lhs => rw [← he]; unfold rowWord updateRound
  simp only [rowCoreBit, Nat.testBit_xor, he]
  rw [show 2 * (r - 1) = 2 * r - 2 by omega, rbit hi (by omega) hw]
  cases (wordStep k (rowWord k w u (r - 1) ^^^ rot k 1 (rowWord k w u (r - 1)) ^^^
    rot k (k - 1) (rowWord k w u (r - 1)))).testBit i <;>
    cases w.testBit ((i + k - (2 * r - 2)) % k) <;>
    cases (constant k r).testBit i <;> rfl

private theorem colWord_final_xor {k r w v i : Nat} (hr : 4 ≤ r) (hk : 3 * r + 2 < k)
    (hw : w < 2 ^ k) (hi : i < k) :
    (colWord k r w v r).testBit i = xor (colCoreBit k r w v i) (w.testBit ((i + k - (3 * r + 1)) % k)) := by
  have he : r - 1 + 1 = r := by omega
  conv_lhs => rw [← he]; unfold colWord updateRound
  simp only [colCoreBit, Nat.testBit_xor, he]
  rw [rbit hi (by omega) hw]
  cases (wordStep k (colWord k r w v (r - 1) ^^^ rot k 2 (colWord k r w v (r - 1)) ^^^
    rot k (k - 2) (colWord k r w v (r - 1)))).testBit i <;>
    cases w.testBit ((i + k - (3 * r + 1)) % k) <;>
    cases (constant k (r + r)).testBit i <;> rfl

private theorem rowCoreBit_dep {k r u w₁ w₂ i : Nat} (hr : 4 ≤ r) (hk : 6 * r - 5 < k)
    (hu : u < 2 ^ k) (hw1 : w₁ < 2 ^ k) (hw2 : w₂ < 2 ^ k) (hi : i < k)
    (H : AgreeCyc k i (2 * r - 3) (3 * r) w₁ w₂) :
    rowCoreBit k r w₁ u i = rowCoreBit k r w₂ u i := by
  simp only [rowCoreBit, Nat.testBit_xor]
  congr 1
  apply step_mix1_congr (by omega) (rowWord_lt hu (r - 1)) (rowWord_lt hu (r - 1)) hi
  intro δ hδ
  apply rowWord_dep hu hw1 hw2 (r - 1) (by omega) _ (Nat.mod_lt _ (by omega))
  apply agreeCyc_shift1 (by omega) hδ
  exact agreeCyc_mono (by omega) (by omega) (by omega) H

private theorem colCoreBit_dep {k r v w₁ w₂ i : Nat} (hr : 4 ≤ r) (hk : 6 * r - 5 < k)
    (hv : v < 2 ^ k) (hw1 : w₁ < 2 ^ k) (hw2 : w₂ < 2 ^ k) (hi : i < k)
    (H : AgreeCyc k i (3 * r) (4 * r - 3) w₁ w₂) :
    colCoreBit k r w₁ v i = colCoreBit k r w₂ v i := by
  simp only [colCoreBit, Nat.testBit_xor]
  congr 1
  apply step_mix2_congr (by omega) (colWord_lt hv (r - 1)) (colWord_lt hv (r - 1)) hi
  intro δ hδ
  apply colWord_dep hv hw1 hw2 (r - 1) (by omega) _ (Nat.mod_lt _ (by omega))
  apply agreeCyc_shift2 (by omega) hδ
  exact agreeCyc_mono (by omega) (by omega) (by omega) H

private def setBit (k w p : Nat) (b : Bool) : Nat :=
  tableIndex (fun i : Fin k => if i.val = p then b else w.testBit i.val)

private theorem setBit_lt {k w p : Nat} {b : Bool} : setBit k w p b < 2 ^ k := pack_lt _

private theorem testBit_setBit {k w p i : Nat} {b : Bool} (hi : i < k) :
    (setBit k w p b).testBit i = if i = p then b else w.testBit i :=
  bit_pack (fun j : Fin k => if j.val = p then b else w.testBit j.val) ⟨i, hi⟩

private def inputs (n : Nat) : Set (Sig n) := Set.range (fun i : Fin n => fun v => v i)
private def base (n : Nat) : Set (Sig n) := inputs n ∪ {fun _ => false, fun _ => true}

private theorem inputG (n : Nat) : Build (inputs n) {fun _ => false, fun _ => true} 2 := by
  simpa only [Set.singleton_union] using
    (seq (constG (A := inputs n) false) (constG (A := inputs n ∪ {fun _ => false}) true))

private def U (k : Nat) (v : Fin (k + k) → Bool) : Nat := tableIndex fun i : Fin k => v (Fin.castAdd k i)
private def V (k : Nat) (v : Fin (k + k) → Bool) : Nat := tableIndex fun i : Fin k => v (Fin.natAdd k i)
private theorem U_lt (k : Nat) (v) : U k v < 2 ^ k := pack_lt _
private theorem V_lt (k : Nat) (v) : V k v < 2 ^ k := pack_lt _
private theorem bitU (k : Nat) (i : Fin k) : bits (U k) i ∈ base (k + k) :=
  Or.inl ⟨Fin.castAdd k i, funext fun v => (bit_pack (fun j : Fin k => v (Fin.castAdd k j)) i).symm⟩
private theorem bitV (k : Nat) (i : Fin k) : bits (V k) i ∈ base (k + k) :=
  Or.inl ⟨Fin.natAdd k i, funext fun v => (bit_pack (fun j : Fin k => v (Fin.natAdd k j)) i).symm⟩

private theorem constBit_mem {n : Nat} (b : Bool) : (fun _ : Fin n → Bool => b) ∈ base n := by
  cases b <;> exact Or.inr (by simp)

private theorem testSlotCircuit {k r : Nat} (hk : 0 < k) {A : Set (Sig (k + k))}
    (W : (Fin (k + k) → Bool) → Nat) (hWlt : ∀ v, W v < 2 ^ k)
    (hW : ∀ i : Fin k, bits W i ∈ A) (hU : ∀ i : Fin k, bits (U k) i ∈ A)
    (hV : ∀ i : Fin k, bits (V k) i ∈ A) (hf : (fun _ => false) ∈ A) :
    Build A {(fun v =>
      decide (rowWord k (W v) (U k v) r < 2 ^ (k - (k + 1) / 2)) &&
      decide (colWord k r (W v) (V k v) r < 2 ^ (k - (k + 1) / 2)))}
      (2 * (4 * k + 19 * k * r) + 2 * k + 3) := by
  let h := k - (k + 1) / 2
  let R := Set.range (fun i : Fin k => bits (fun v => rowWord k (W v) (U k v) r) i)
  have HR : Build A R (4 * k + 19 * k * r) := rowSchedule hk W (U k) hWlt (U_lt k) hW hU r
  let C := Set.range (fun i : Fin k => bits (fun v => colWord k r (W v) (V k v) r) i)
  have HC : Build (A ∪ R) C (4 * k + 19 * k * r) :=
    colSchedule hk r W (V k) hWlt (V_lt k) (fun i => Or.inl (hW i)) (fun i => Or.inl (hV i)) r
  let rl : Sig (k + k) := fun v => decide (rowWord k (W v) (U k v) r < 2 ^ h)
  let cl : Sig (k + k) := fun v => decide (colWord k r (W v) (V k v) r < 2 ^ h)
  have Hrl : Build (A ∪ (R ∪ C)) {rl} (k + 1) :=
    thresholds h _ (fun v => rowWord_lt (U_lt k v) r) (fun i _ => Or.inr (Or.inl ⟨i, rfl⟩)) (Or.inl hf)
  have Hcl : Build (A ∪ ((R ∪ C) ∪ {rl})) {cl} (k + 1) :=
    thresholds h _ (fun v => colWord_lt (V_lt k v) r) (fun i _ => Or.inr (Or.inl (Or.inr ⟨i, rfl⟩))) (Or.inl hf)
  have HA : Build (A ∪ (((R ∪ C) ∪ {rl}) ∪ {cl})) {an rl cl} 1 :=
    andG (f := rl) (g := cl) (by simp) (by simp)
  refine relax (seq (seq (seq (seq HR HC) Hrl) Hcl) HA) le_rfl Set.subset_union_right ?_
  ring_nf; omega

private def initWord (k r seed : Nat) : Nat :=
  tableIndex (fun i : Fin k =>
    if k - (2 * r - 2) ≤ i.val then
      seed.testBit (i.val - (k - (2 * r - 2)))
    else if i.val < 4 * r - 3 then
      seed.testBit (2 * r - 2 + i.val)
    else false)

private def sweepRowTop (k r u : Nat) : Nat → Nat → Nat
  | 0, w => w
  | s + 1, w =>
    let w' := sweepRowTop k r u s w
    let p := k - (2 * r - 2) - 1 - s
    let i := k - 1 - s
    setBit k w' p ((rowWord k w' u r).testBit i)

private def sweepColMid (k r v : Nat) : Nat → Nat → Nat
  | 0, w => w
  | s + 1, w =>
    let w' := sweepColMid k r v s w
    let h := (k + 1) / 2
    let p := k - h - (2 * r - 2) - 1 - s
    let i := k - h + (r + 2) - s
    setBit k w' p ((colWord k r w' v r).testBit i)

private theorem sweepRowTop_lt {k r u s w : Nat} (hw : w < 2 ^ k) :
    sweepRowTop k r u s w < 2 ^ k := by
  induction s with
  | zero => exact hw
  | succ s _ => exact setBit_lt

private theorem sweepColMid_lt {k r v s w : Nat} (hw : w < 2 ^ k) :
    sweepColMid k r v s w < 2 ^ k := by
  induction s with
  | zero => exact hw
  | succ s _ => exact setBit_lt

private theorem sweepRowTop_unchanged {k r u s w m : Nat} (hm : m < k) (hkr : 2 * r - 2 < k)
    (hout : m < k - (2 * r - 2) - s ∨ k - (2 * r - 2) ≤ m) :
    (sweepRowTop k r u s w).testBit m = w.testBit m := by
  induction s with
  | zero => rfl
  | succ s IH =>
    simp only [sweepRowTop]
    rw [testBit_setBit hm]
    simp only [show ¬ m = k - (2 * r - 2) - 1 - s by omega, ↓reduceIte]
    exact IH (by omega)

private theorem sweepColMid_unchanged {k r v s w m : Nat} (hm : m < k)
    (hkr : (k + 1) / 2 + (2 * r - 2) < k)
    (hout : m < k - (k + 1) / 2 - (2 * r - 2) - s ∨ k - (k + 1) / 2 - (2 * r - 2) ≤ m) :
    (sweepColMid k r v s w).testBit m = w.testBit m := by
  induction s with
  | zero => rfl
  | succ s IH =>
    simp only [sweepColMid]
    rw [testBit_setBit hm]
    simp only [show ¬ m = k - (k + 1) / 2 - (2 * r - 2) - 1 - s by omega, ↓reduceIte]
    exact IH (by omega)

private theorem agree_above_row_any {k r p w₁ w₂ : Nat} (hr : 4 ≤ r) (hk : 6 * r - 5 < k)
    (hp1 : 4 * r - 3 ≤ p) (hp2 : p < k - (2 * r - 2))
    (H : ∀ m < k, (m < 4 * r - 3 ∨ p < m) → w₁.testBit m = w₂.testBit m) :
    AgreeCyc k (p + (2 * r - 2)) (2 * r - 3) (3 * r) w₁ w₂ := by
  intro d hd
  have hm : (p + (2 * r - 2) + k - (2 * r - 3) + d) % k < k := Nat.mod_lt _ (by omega)
  apply H _ hm
  have e : p + (2 * r - 2) + k - (2 * r - 3) + d = k + (p + 1 + d) := by omega
  rw [e]
  by_cases hlt : p + 1 + d < k
  · right
    rw [Nat.add_comm k, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    omega
  · left
    have hlt2 : p + 1 + d - k < k := by omega
    rw [show k + (p + 1 + d) = (p + 1 + d - k) + 2 * k by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt2]
    omega

private theorem agree_above_col_any {k r p w₁ w₂ : Nat} (hr : 4 ≤ r) (hk : 6 * r - 5 < k)
    (hp1 : 4 * r - 3 ≤ p) (hp2 : p < k - (3 * r + 1))
    (H : ∀ m < k, (m < 4 * r - 3 ∨ p < m) → w₁.testBit m = w₂.testBit m) :
    AgreeCyc k (p + (3 * r + 1)) (3 * r) (4 * r - 3) w₁ w₂ := by
  intro d hd
  have hm : (p + (3 * r + 1) + k - 3 * r + d) % k < k := Nat.mod_lt _ (by omega)
  apply H _ hm
  have e : p + (3 * r + 1) + k - 3 * r + d = k + (p + 1 + d) := by omega
  rw [e]
  by_cases hlt : p + 1 + d < k
  · right
    rw [Nat.add_comm k, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    omega
  · left
    have hlt2 : p + 1 + d - k < k := by omega
    rw [show k + (p + 1 + d) = (p + 1 + d - k) + 2 * k by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt2]
    omega

private theorem xor_false_eq_self {a b : Bool} (h : xor a b = false) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem sweepRowTop_match {k r u raw seed s : Nat} (hr : 4 ≤ r) (hk : 6 * r - 5 < k)
    (hu : u < 2 ^ k) (hraw : raw < 2 ^ k)
    (hpass : rowWord k raw u r < 2 ^ (k - (k + 1) / 2))
    (hs1 : s ≤ (k + 1) / 2) (hs2 : s ≤ k - (6 * r - 5))
    (hseed : ∀ j < 6 * r - 5, seed.testBit j = raw.testBit ((k - (2 * r - 2) + j) % k)) :
    ∀ m < k, (m < 4 * r - 3 ∨ k - (2 * r - 2) - s ≤ m) →
      (sweepRowTop k r u s (initWord k r seed)).testBit m = raw.testBit m := by
  induction s with
  | zero =>
    intro m hm hm'
    simp only [sweepRowTop, initWord, bit_pack _ ⟨m, hm⟩]
    by_cases h1 : k - (2 * r - 2) ≤ m
    · simp only [h1, ↓reduceIte]
      have h0 := hseed (m - (k - (2 * r - 2))) (by omega)
      have e : (k - (2 * r - 2) + (m - (k - (2 * r - 2)))) % k = m := by
        rw [show k - (2 * r - 2) + (m - (k - (2 * r - 2))) = m by omega, Nat.mod_eq_of_lt hm]
      rw [h0, e]
    · simp only [h1, ↓reduceIte]
      have h2 : m < 4 * r - 3 := by omega
      simp only [h2, ↓reduceIte]
      have h0 := hseed (2 * r - 2 + m) (by omega)
      have e : (k - (2 * r - 2) + (2 * r - 2 + m)) % k = m := by
        rw [show k - (2 * r - 2) + (2 * r - 2 + m) = m + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hm]
      rw [h0, e]
  | succ s IH =>
    have hprev := IH (by omega) (by omega)
    let w' := sweepRowTop k r u s (initWord k r seed)
    have hw' : w' < 2 ^ k := sweepRowTop_lt (pack_lt _)
    let p := k - (2 * r - 2) - 1 - s
    let i := k - 1 - s
    have hp_lt : p < k := by dsimp [p]; omega
    have hi_lt : i < k := by dsimp [i]; omega
    have hp_zero : w'.testBit p = false := by
      dsimp [w']
      rw [sweepRowTop_unchanged hp_lt (by omega) (Or.inl (by dsimp [p]; omega))]
      simp only [initWord, bit_pack _ ⟨p, hp_lt⟩]
      simp only [show ¬ k - (2 * r - 2) ≤ p by dsimp [p]; omega, ↓reduceIte,
        show ¬ p < 4 * r - 3 by dsimp [p]; omega]
    have hidx : (i + k - (2 * r - 2)) % k = p := by
      rw [show i + k - (2 * r - 2) = p + k by dsimp [i, p]; omega, Nat.add_mod_right, Nat.mod_eq_of_lt hp_lt]
    have hbit : (rowWord k w' u r).testBit i = raw.testBit p := by
      rw [rowWord_final_xor hr (by omega) hw' hi_lt, hidx, hp_zero, Bool.xor_false]
      have hcore : rowCoreBit k r w' u i = rowCoreBit k r raw u i := by
        apply rowCoreBit_dep hr hk hu hw' hraw hi_lt
        have ei : i = p + (2 * r - 2) := by dsimp [i, p]; omega
        rw [ei]
        apply agree_above_row_any hr hk (by dsimp [p]; omega) (by dsimp [p]; omega)
        intro q hq hq'
        exact hprev q hq (by dsimp [p] at hq'; omega)
      rw [hcore]
      have hraw0 : (rowWord k raw u r).testBit i = false :=
        (lt_two_pow_iff_testBit (rowWord_lt hu r)).mp hpass i (by dsimp [i]; omega) hi_lt
      rw [rowWord_final_xor hr (by omega) hraw hi_lt, hidx] at hraw0
      exact xor_false_eq_self hraw0
    intro m hm hm'
    simp only [sweepRowTop]
    rw [testBit_setBit hm]
    by_cases hmp : m = p
    · subst hmp
      simp only [p, ↓reduceIte]
      exact hbit
    · simp only [show ¬ m = k - (2 * r - 2) - 1 - s from hmp, ↓reduceIte]
      exact hprev m hm (by dsimp [p] at hmp; omega)

private theorem sweepColMid_match {k r v raw w1 s : Nat} (hr : 4 ≤ r) (hk : 6 * r - 5 < k)
    (hv : v < 2 ^ k) (hraw : raw < 2 ^ k) (hw1 : w1 < 2 ^ k)
    (hpass : colWord k r raw v r < 2 ^ (k - (k + 1) / 2))
    (hh_lt : (k + 1) / 2 < k - (6 * r - 5))
    (hs1 : s ≤ r + 3) (hs2 : s ≤ k - (6 * r - 5) - (k + 1) / 2)
    (hw1_match : ∀ m < k, (m < 4 * r - 3 ∨ k - (k + 1) / 2 - (2 * r - 2) ≤ m) → w1.testBit m = raw.testBit m)
    (hw1_zero : ∀ m < k, 4 * r - 3 ≤ m → m < k - (k + 1) / 2 - (2 * r - 2) → w1.testBit m = false) :
    ∀ m < k, (m < 4 * r - 3 ∨ k - (k + 1) / 2 - (2 * r - 2) - s ≤ m) →
      (sweepColMid k r v s w1).testBit m = raw.testBit m := by
  induction s with
  | zero =>
    intro m hm hm'
    simp only [sweepColMid, Nat.sub_zero] at hm' ⊢
    exact hw1_match m hm hm'
  | succ s IH =>
    have hprev := IH (by omega) (by omega)
    let w' := sweepColMid k r v s w1
    have hw' : w' < 2 ^ k := sweepColMid_lt hw1
    let h := (k + 1) / 2
    let p := k - h - (2 * r - 2) - 1 - s
    let i := k - h + (r + 2) - s
    have hp_lt : p < k := by dsimp [p, h]; omega
    have hi_lt : i < k := by dsimp [i, h]; omega
    have hp_zero : w'.testBit p = false := by
      dsimp [w']
      rw [sweepColMid_unchanged hp_lt (by omega) (Or.inl (by dsimp [p, h]; omega))]
      exact hw1_zero p hp_lt (by dsimp [p, h]; omega) (by dsimp [p, h]; omega)
    have hidx : (i + k - (3 * r + 1)) % k = p := by
      rw [show i + k - (3 * r + 1) = p + k by dsimp [i, p, h]; omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hp_lt]
    have hbit : (colWord k r w' v r).testBit i = raw.testBit p := by
      rw [colWord_final_xor hr (by omega) hw' hi_lt, hidx, hp_zero, Bool.xor_false]
      have hcore : colCoreBit k r w' v i = colCoreBit k r raw v i := by
        apply colCoreBit_dep hr hk hv hw' hraw hi_lt
        have ei : i = p + (3 * r + 1) := by dsimp [i, p, h]; omega
        rw [ei]
        apply agree_above_col_any hr hk (by dsimp [p, h]; omega) (by dsimp [p, h]; omega)
        intro q hq hq'
        exact hprev q hq (by dsimp [p, h] at hq'; omega)
      rw [hcore]
      have hraw0 : (colWord k r raw v r).testBit i = false :=
        (lt_two_pow_iff_testBit (colWord_lt hv r)).mp hpass i (by dsimp [i, h]; omega) hi_lt
      rw [colWord_final_xor hr (by omega) hraw hi_lt, hidx] at hraw0
      exact xor_false_eq_self hraw0
    intro m hm hm'
    simp only [sweepColMid]
    rw [testBit_setBit hm]
    by_cases hmp : m = p
    · subst hmp
      simp only [p, h, ↓reduceIte]
      exact hbit
    · simp only [show ¬ m = k - (k + 1) / 2 - (2 * r - 2) - 1 - s from hmp, ↓reduceIte]
      exact hprev m hm (by dsimp [p, h] at hmp; omega)

private theorem sweepRowTop_circuit {k r : Nat} (hk : 0 < k) {A : Set (Sig (k + k))}
    (W0 : (Fin (k + k) → Bool) → Nat) (hW0lt : ∀ v, W0 v < 2 ^ k)
    (hW0 : ∀ i : Fin k, bits W0 i ∈ A) (hU : ∀ i : Fin k, bits (U k) i ∈ A) (s : Nat)
    (hs : s ≤ k) :
    Build A (Set.range (fun i : Fin k => bits (fun v => sweepRowTop k r (U k v) s (W0 v)) i))
      (s * (4 * k + 19 * k * r)) := by
  induction s with
  | zero =>
    refine relax (idle ?_) le_rfl le_rfl (by omega)
    rintro _ ⟨i, rfl⟩
    exact hW0 i
  | succ s IH =>
    let W' := fun v => sweepRowTop k r (U k v) s (W0 v)
    let R' := Set.range (fun i : Fin k => bits W' i)
    have hW'lt : ∀ v, W' v < 2 ^ k := fun v => sweepRowTop_lt (hW0lt v)
    let RW := Set.range (fun i : Fin k => bits (fun v => rowWord k (W' v) (U k v) r) i)
    have HR : Build (A ∪ R') RW (4 * k + 19 * k * r) :=
      rowSchedule hk W' (U k) hW'lt (U_lt k) (fun i => Or.inr ⟨i, rfl⟩) (fun i => Or.inl (hU i)) r
    refine relax (seq (IH (by omega)) HR) le_rfl ?_ (by ring_nf; omega)
    rintro _ ⟨m, rfl⟩
    let p := k - (2 * r - 2) - 1 - s
    let idx := k - 1 - s
    by_cases hmp : m.val = p
    · right
      refine ⟨⟨idx, by dsimp [idx]; omega⟩, ?_⟩
      funext v
      simp only [bits, sweepRowTop]
      rw [testBit_setBit m.isLt]
      simp only [show m.val = k - (2 * r - 2) - 1 - s from hmp, ↓reduceIte]
      rfl
    · left
      refine ⟨m, ?_⟩
      funext v
      simp only [bits, sweepRowTop]
      rw [testBit_setBit m.isLt]
      simp only [show ¬ m.val = k - (2 * r - 2) - 1 - s from hmp, ↓reduceIte]

private theorem sweepColMid_circuit {k r : Nat} (hk : 0 < k) {A : Set (Sig (k + k))}
    (W1 : (Fin (k + k) → Bool) → Nat) (hW1lt : ∀ v, W1 v < 2 ^ k)
    (hW1 : ∀ i : Fin k, bits W1 i ∈ A) (hV : ∀ i : Fin k, bits (V k) i ∈ A) (s : Nat)
    (hidx_lt : ∀ s' < s, k - (k + 1) / 2 + (r + 2) - s' < k) :
    Build A (Set.range (fun i : Fin k => bits (fun v => sweepColMid k r (V k v) s (W1 v)) i))
      (s * (4 * k + 19 * k * r)) := by
  induction s with
  | zero =>
    refine relax (idle ?_) le_rfl le_rfl (by omega)
    rintro _ ⟨i, rfl⟩
    exact hW1 i
  | succ s IH =>
    let W' := fun v => sweepColMid k r (V k v) s (W1 v)
    let R' := Set.range (fun i : Fin k => bits W' i)
    have hW'lt : ∀ v, W' v < 2 ^ k := fun v => sweepColMid_lt (hW1lt v)
    let CW := Set.range (fun i : Fin k => bits (fun v => colWord k r (W' v) (V k v) r) i)
    have HC : Build (A ∪ R') CW (4 * k + 19 * k * r) :=
      colSchedule hk r W' (V k) hW'lt (V_lt k) (fun i => Or.inr ⟨i, rfl⟩) (fun i => Or.inl (hV i)) r
    refine relax (seq (IH (fun s' hs' => hidx_lt s' (by omega))) HC) le_rfl ?_ (by ring_nf; omega)
    rintro _ ⟨m, rfl⟩
    let h := (k + 1) / 2
    let p := k - h - (2 * r - 2) - 1 - s
    let idx := k - h + (r + 2) - s
    have hidx : idx < k := hidx_lt s (by omega)
    by_cases hmp : m.val = p
    · right
      refine ⟨⟨idx, hidx⟩, ?_⟩
      funext v
      simp only [bits, sweepColMid]
      rw [testBit_setBit m.isLt]
      simp only [show m.val = k - (k + 1) / 2 - (2 * r - 2) - 1 - s from hmp, ↓reduceIte]
      rfl
    · left
      refine ⟨m, ?_⟩
      funext v
      simp only [bits, sweepColMid]
      rw [testBit_setBit m.isLt]
      simp only [show ¬ m.val = k - (k + 1) / 2 - (2 * r - 2) - 1 - s from hmp, ↓reduceIte]

private theorem solve_zero (r : Nat) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (0 + 0) C ∧
    C.size ≤ 2 ^ min 0 (6 * r - 5) * (24 * (0 + 1) ^ 2 * (r + 1)) ∧
    ∀ v : Fin (0 + 0) → Bool, C.eval (List.ofFn v) =
      (List.range (2 ^ 0)).any (fun w =>
        decide (rowWord 0 w (U 0 v) r < 2 ^ (0 - (0 + 1) / 2)) &&
        decide (colWord 0 r w (V 0 v) r < 2 ^ (0 - (0 + 1) / 2))) := by
  refine ⟨⟨[⟨.and, []⟩], 0⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have : g = ⟨.and, []⟩ := List.mem_singleton.mp hg
    subst g
    simp
  · intro j hj i hi
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    simp [gateAt] at hi
  · change 1 ≤ 2 ^ min 0 (6 * r - 5) * (24 * (0 + 1) ^ 2 * (r + 1))
    have h1 : 1 ≤ 2 ^ min 0 (6 * r - 5) := Nat.two_pow_pos _
    nlinarith
  · intro v
    have hr0 : rowWord 0 0 (U 0 v) r < 1 := rowWord_lt (U_lt 0 v) r
    have hc0 : colWord 0 r 0 (V 0 v) r < 1 := colWord_lt (V_lt 0 v) r
    have hr0' : rowWord 0 0 (U 0 v) r = 0 := by omega
    have hc0' : colWord 0 r 0 (V 0 v) r = 0 := by omega
    simp [Circuit.eval, Circuit.wires, GateOp.eval, hr0', hc0']

private theorem solve_small (k r : Nat) (hk1 : 1 ≤ k) (hks : k ≤ 6 * r - 5) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (k + k) C ∧
    C.size ≤ 2 ^ min k (6 * r - 5) * (24 * (k + 1) ^ 2 * (r + 1)) ∧
    ∀ v : Fin (k + k) → Bool, C.eval (List.ofFn v) =
      (List.range (2 ^ k)).any (fun w =>
        decide (rowWord k w (U k v) r < 2 ^ (k - (k + 1) / 2)) &&
        decide (colWord k r w (V k v) r < 2 ^ (k - (k + 1) / 2))) := by
  have hk : 0 < k := by omega
  let N := 2 ^ k
  let s := 2 * (4 * k + 19 * k * r) + 2 * k + 3
  let F : Fin N → Sig (k + k) := fun w v =>
    decide (rowWord k w.val (U k v) r < 2 ^ (k - (k + 1) / 2)) &&
    decide (colWord k r w.val (V k v) r < 2 ^ (k - (k + 1) / 2))
  have Hs : Build (base (k + k)) (Set.range F) (N * s) := finG F s fun w => by
    exact testSlotCircuit hk (fun _ => w.val) (fun _ => w.isLt)
      (fun i => constBit_mem (w.val.testBit i.val))
      (bitU k) (bitV k) (constBit_mem false)
  let xs := (List.finRange N).map F
  let O : Sig (k + k) := fun v => xs.any (fun f => f v)
  have Ho : Build (base (k + k) ∪ Set.range F) {O} N := by
    simpa only [xs, List.length_map, List.length_finRange] using
      (anyG (A := base (k + k) ∪ Set.range F) xs
        (by intro f hf; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf; exact Or.inr ⟨i, rfl⟩)
        (Or.inl (constBit_mem false)))
  have H : Build (inputs (k + k)) {O} (2 + (N * s + N)) :=
    relax (seq (inputG (k + k)) (seq Hs Ho)) le_rfl
      (Set.singleton_subset_iff.mpr (Or.inr (Or.inr rfl))) le_rfl
  obtain ⟨c, hc, HS⟩ := H.run (GateBridge.start (F := id) (fun i : Fin (k + k) => fun v => v i) (by intros; rfl)) le_rfl
  clear H
  obtain ⟨C, hsize, hread, hfan, hout⟩ := GateBridge.finish HS (Or.inr (Set.mem_singleton O))
  refine ⟨C, hfan, hread, ?_, fun v => ?_⟩
  · rw [hsize, Nat.zero_add, min_eq_left hks]
    have hn : 1 ≤ N := Nat.two_pow_pos _
    have hslot : s + 3 ≤ 24 * (k + 1) ^ 2 * (r + 1) := by
      have hexp1 : s + 3 = 38 * (k * r) + 10 * k + 6 := by dsimp [s]; ring
      have hexp2 : 24 * (k + 1) ^ 2 * (r + 1) =
          24 * (k * k * r) + 48 * (k * r) + 24 * r + 24 * (k * k) + 48 * k + 24 := by ring
      omega
    have hm := Nat.mul_le_mul_left N hslot
    change c ≤ N * (24 * (k + 1) ^ 2 * (r + 1))
    calc
      c ≤ 2 + (N * s + N) := hc
      _ ≤ N * (s + 3) := by
        rw [Nat.mul_add N s 3, show N * 3 = N + N + N by omega]
        omega
      _ ≤ N * (24 * (k + 1) ^ 2 * (r + 1)) := hm
  · rw [hout]
    change O v = _
    apply Bool.eq_iff_iff.mpr
    simp only [O, xs, List.any_eq_true, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨_, ⟨i, _, rfl⟩, hh⟩
      exact ⟨i.val, i.isLt, hh⟩
    · rintro ⟨i, hi, hh⟩
      exact ⟨F ⟨i, hi⟩, ⟨⟨i, hi⟩, List.mem_finRange _, rfl⟩, hh⟩

private theorem solve_large (k r : Nat) (hr : 4 ≤ r) (hkl : 6 * r - 5 < k) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (k + k) C ∧
    C.size ≤ 2 ^ min k (6 * r - 5) * (24 * (k + 1) ^ 2 * (r + 1)) ∧
    ∀ v : Fin (k + k) → Bool, C.eval (List.ofFn v) =
      (List.range (2 ^ k)).any (fun w =>
        decide (rowWord k w (U k v) r < 2 ^ (k - (k + 1) / 2)) &&
        decide (colWord k r w (V k v) r < 2 ^ (k - (k + 1) / 2))) := by
  have hk : 0 < k := by omega
  let h := (k + 1) / 2
  let rem := k - (6 * r - 5)
  let nrow := min h rem
  let ncol := min (r + 3) (rem - nrow)
  let N := 2 ^ (6 * r - 5)
  let Wfin (seed : Nat) (v : Fin (k + k) → Bool) : Nat :=
    sweepColMid k r (V k v) ncol (sweepRowTop k r (U k v) nrow (initWord k r seed))
  have hWfin_lt (seed : Nat) (v : Fin (k + k) → Bool) : Wfin seed v < 2 ^ k :=
    sweepColMid_lt (sweepRowTop_lt (pack_lt _))
  let F : Fin N → Sig (k + k) := fun seed v =>
    decide (rowWord k (Wfin seed.val v) (U k v) r < 2 ^ (k - h)) &&
    decide (colWord k r (Wfin seed.val v) (V k v) r < 2 ^ (k - h))
  let s := (k + 2) * (4 * k + 19 * k * r) + 2 * k + 3
  have hslot_build (seed : Fin N) : Build (base (k + k)) {F seed} s := by
    let A := base (k + k)
    let W0 : (Fin (k + k) → Bool) → Nat := fun _ => initWord k r seed.val
    let W1 : (Fin (k + k) → Bool) → Nat := fun v => sweepRowTop k r (U k v) nrow (W0 v)
    let W2 : (Fin (k + k) → Bool) → Nat := Wfin seed.val
    have hW0 : ∀ i : Fin k, bits W0 i ∈ A := fun i => constBit_mem ((initWord k r seed.val).testBit i.val)
    have hW0lt : ∀ v, W0 v < 2 ^ k := fun _ => pack_lt _
    have hW1lt : ∀ v, W1 v < 2 ^ k := fun v => sweepRowTop_lt (hW0lt v)
    let S1 := Set.range (fun i : Fin k => bits W1 i)
    have H1 : Build A S1 (nrow * (4 * k + 19 * k * r)) :=
      sweepRowTop_circuit hk W0 hW0lt hW0 (bitU k) nrow (by dsimp [nrow, rem]; omega)
    let S2 := Set.range (fun i : Fin k => bits W2 i)
    have H2 : Build (A ∪ S1) S2 (ncol * (4 * k + 19 * k * r)) :=
      sweepColMid_circuit hk W1 hW1lt (fun i => Or.inr ⟨i, rfl⟩) (fun i => Or.inl (bitV k i)) ncol
        (fun s' hs' => by
          have hnc : 0 < ncol := by omega
          have hnr : nrow = h := by dsimp [ncol, nrow] at hnc ⊢; omega
          have hhl : h < rem := by dsimp [ncol, nrow] at hnc ⊢; omega
          dsimp [h, rem] at hhl ⊢
          omega)
    have H3 : Build (A ∪ (S1 ∪ S2)) {F seed} (2 * (4 * k + 19 * k * r) + 2 * k + 3) :=
      testSlotCircuit hk W2 (hWfin_lt seed.val) (fun i => Or.inr (Or.inr ⟨i, rfl⟩))
        (fun i => Or.inl (bitU k i)) (fun i => Or.inl (bitV k i)) (Or.inl (constBit_mem false))
    refine relax (seq (seq H1 H2) H3) le_rfl Set.subset_union_right ?_
    have hnc_le : nrow + ncol ≤ k := by dsimp [nrow, ncol, rem]; omega
    have hmul : (nrow + ncol + 2) * (4 * k + 19 * k * r) ≤ (k + 2) * (4 * k + 19 * k * r) :=
      Nat.mul_le_mul_right _ (by omega)
    dsimp [s]
    linarith
  have Hs : Build (base (k + k)) (Set.range F) (N * s) := finG F s hslot_build
  let xs := (List.finRange N).map F
  let O : Sig (k + k) := fun v => xs.any (fun f => f v)
  have Ho : Build (base (k + k) ∪ Set.range F) {O} N := by
    simpa only [xs, List.length_map, List.length_finRange] using
      (anyG (A := base (k + k) ∪ Set.range F) xs
        (by intro f hf; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf; exact Or.inr ⟨i, rfl⟩)
        (Or.inl (constBit_mem false)))
  have H : Build (inputs (k + k)) {O} (2 + (N * s + N)) :=
    relax (seq (inputG (k + k)) (seq Hs Ho)) le_rfl
      (Set.singleton_subset_iff.mpr (Or.inr (Or.inr rfl))) le_rfl
  obtain ⟨c, hc, HS⟩ := H.run (GateBridge.start (F := id) (fun i : Fin (k + k) => fun v => v i) (by intros; rfl)) le_rfl
  clear H
  obtain ⟨C, hsize, hread, hfan, hout⟩ := GateBridge.finish HS (Or.inr (Set.mem_singleton O))
  refine ⟨C, hfan, hread, ?_, fun v => ?_⟩
  · rw [hsize, Nat.zero_add, min_eq_right (by omega : 6 * r - 5 ≤ k)]
    have hn : 1 ≤ N := Nat.two_pow_pos _
    have hslot : s + 3 ≤ 24 * (k + 1) ^ 2 * (r + 1) := by
      have hexp1 : s + 3 = 19 * (k * k * r) + 38 * (k * r) + 4 * (k * k) + 10 * k + 6 := by dsimp [s]; ring
      have hexp2 : 24 * (k + 1) ^ 2 * (r + 1) =
          24 * (k * k * r) + 48 * (k * r) + 24 * r + 24 * (k * k) + 48 * k + 24 := by ring
      omega
    have hm := Nat.mul_le_mul_left N hslot
    change c ≤ N * (24 * (k + 1) ^ 2 * (r + 1))
    calc
      c ≤ 2 + (N * s + N) := hc
      _ ≤ N * (s + 3) := by
        rw [Nat.mul_add N s 3, show N * 3 = N + N + N by omega]
        omega
      _ ≤ N * (24 * (k + 1) ^ 2 * (r + 1)) := hm
  · rw [hout]
    change O v = _
    apply Bool.eq_iff_iff.mpr
    simp only [O, xs, List.any_eq_true, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨_, ⟨seed, _, rfl⟩, hh⟩
      exact ⟨Wfin seed.val v, hWfin_lt seed.val v, hh⟩
    · rintro ⟨raw, hraw, hraw'⟩
      have hraw1 : rowWord k raw (U k v) r < 2 ^ (k - h) :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hraw').1
      have hraw2 : colWord k r raw (V k v) r < 2 ^ (k - h) :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hraw').2
      let seedVal : Nat := tableIndex (fun j : Fin (6 * r - 5) =>
        raw.testBit ((k - (2 * r - 2) + j.val) % k))
      let seed : Fin N := ⟨seedVal, pack_lt _⟩
      have hseed (j : Nat) (hj : j < 6 * r - 5) :
          seed.val.testBit j = raw.testBit ((k - (2 * r - 2) + j) % k) :=
        bit_pack _ ⟨j, hj⟩
      refine ⟨F seed, ⟨seed, List.mem_finRange _, rfl⟩, ?_⟩
      let w1 := sweepRowTop k r (U k v) nrow (initWord k r seed.val)
      have hw1 : w1 < 2 ^ k := sweepRowTop_lt (pack_lt _)
      have hw1_match := sweepRowTop_match hr hkl (U_lt k v) hraw hraw1
        (min_le_left ..) (min_le_right ..) hseed
      by_cases hrem : rem ≤ h
      · have hnr : nrow = rem := min_eq_right hrem
        have hnc : ncol = 0 := by dsimp [ncol]; omega
        have heq : Wfin seed.val v = raw := by
          dsimp [Wfin]
          rw [hnc]
          simp only [sweepColMid]
          apply Nat.eq_of_testBit_eq
          intro m
          by_cases hm : m < k
          · exact hw1_match m hm (by dsimp [nrow, rem] at hnr ⊢; omega)
          · have hp := Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k ≤ m)
            rw [Nat.testBit_lt_two_pow (hw1.trans_le hp), Nat.testBit_lt_two_pow (hraw.trans_le hp)]
        simpa only [F, heq] using hraw'
      · have hhl : h < rem := by omega
        have hnr : nrow = h := min_eq_left (by omega)
        have hw1_zero (m : Nat) (hm : m < k) (h1 : 4 * r - 3 ≤ m) (h2 : m < k - h - (2 * r - 2)) :
            w1.testBit m = false := by
          dsimp [w1]
          rw [sweepRowTop_unchanged hm (by omega) (Or.inl (by rw [hnr]; omega))]
          simp only [initWord, bit_pack _ ⟨m, hm⟩]
          simp only [show ¬ k - (2 * r - 2) ≤ m by omega, ↓reduceIte, show ¬ m < 4 * r - 3 by omega]
        have hw2_match := sweepColMid_match (s := ncol) hr hkl (V_lt k v) hraw hw1 hraw2 hhl
          (min_le_left ..) (by dsimp [ncol, rem, h]; rw [hnr]; exact min_le_right ..)
          (fun m hm hm' => by
            have h1 := hw1_match m hm (by dsimp [nrow, rem, h] at hnr ⊢; omega)
            exact h1) hw1_zero
        by_cases hrem2 : rem - h ≤ r + 3
        · have hnc : ncol = rem - h := by dsimp [ncol]; rw [hnr]; exact min_eq_right hrem2
          have heq : Wfin seed.val v = raw := by
            apply Nat.eq_of_testBit_eq
            intro m
            by_cases hm : m < k
            · exact hw2_match m hm (by dsimp [rem] at hnc ⊢; omega)
            · have hp := Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k ≤ m)
              rw [Nat.testBit_lt_two_pow ((hWfin_lt seed.val v).trans_le hp),
                Nat.testBit_lt_two_pow (hraw.trans_le hp)]
          simpa only [F, heq] using hraw'
        · have hnc : ncol = r + 3 := by dsimp [ncol]; rw [hnr]; exact min_eq_left (by omega)
          have hwf1 : rowWord k (Wfin seed.val v) (U k v) r < 2 ^ (k - h) := by
            rw [lt_two_pow_iff_testBit (rowWord_lt (U_lt k v) r)]
            intro i hi1 hi2
            have heq_bit : (rowWord k (Wfin seed.val v) (U k v) r).testBit i =
                (rowWord k raw (U k v) r).testBit i := by
              rw [rowWord_final_xor hr (by omega) (hWfin_lt seed.val v) hi2,
                rowWord_final_xor hr (by omega) hraw hi2]
              have hidx : (i + k - (2 * r - 2)) % k = i - (2 * r - 2) := by
                rw [show i + k - (2 * r - 2) = (i - (2 * r - 2)) + k by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              rw [hidx, hw2_match (i - (2 * r - 2)) (by omega) (Or.inr (by omega))]
              congr 1
              apply rowCoreBit_dep hr hkl (U_lt k v) (hWfin_lt seed.val v) hraw hi2
              have ei : i = (i - (2 * r - 2)) + (2 * r - 2) := by omega
              rw [ei]
              apply agree_above_row_any hr hkl (by omega) (by omega)
              intro m hm hm'
              exact hw2_match m hm (by omega)
            rw [heq_bit]
            exact (lt_two_pow_iff_testBit (rowWord_lt (U_lt k v) r)).mp hraw1 i hi1 hi2
          have hwf2 : colWord k r (Wfin seed.val v) (V k v) r < 2 ^ (k - h) := by
            rw [lt_two_pow_iff_testBit (colWord_lt (V_lt k v) r)]
            intro i hi1 hi2
            have heq_bit : (colWord k r (Wfin seed.val v) (V k v) r).testBit i =
                (colWord k r raw (V k v) r).testBit i := by
              rw [colWord_final_xor hr (by omega) (hWfin_lt seed.val v) hi2,
                colWord_final_xor hr (by omega) hraw hi2]
              have hidx : (i + k - (3 * r + 1)) % k = i - (3 * r + 1) := by
                rw [show i + k - (3 * r + 1) = (i - (3 * r + 1)) + k by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              rw [hidx, hw2_match (i - (3 * r + 1)) (by omega) (Or.inr (by omega))]
              congr 1
              apply colCoreBit_dep hr hkl (V_lt k v) (hWfin_lt seed.val v) hraw hi2
              have ei : i = (i - (3 * r + 1)) + (3 * r + 1) := by omega
              rw [ei]
              apply agree_above_col_any hr hkl (by omega) (by omega)
              intro m hm hm'
              exact hw2_match m hm (by omega)
            rw [heq_bit]
            exact (lt_two_pow_iff_testBit (colWord_lt (V_lt k v) r)).mp hraw2 i hi1 hi2
          simp only [F, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hwf1, hwf2⟩

private theorem solve (k r : Nat) (hr : 4 ≤ r) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (k + k) C ∧
    C.size ≤ 2 ^ min k (6 * r - 5) * (24 * (k + 1) ^ 2 * (r + 1)) ∧
    ∀ v : Fin (k + k) → Bool, C.eval (List.ofFn v) =
      (List.range (2 ^ k)).any (fun w =>
        decide (rowWord k w (U k v) r < 2 ^ (k - (k + 1) / 2)) &&
        decide (colWord k r w (V k v) r < 2 ^ (k - (k + 1) / 2))) := by
  by_cases hk0 : k = 0
  · subst hk0
    exact solve_zero r
  · by_cases hks : k ≤ 6 * r - 5
    · exact solve_small k r (by omega) hks
    · exact solve_large k r hr (by omega)

end Joint25507

end PEqualNP.Outside.L_meta_25507_aux

open PEqualNP.Outside.L_meta_25507_aux.BitBridge PEqualNP.Outside.L_meta_25507_aux.Joint25507

theorem PEqualNP.Outside.L_meta_25507 : ∀ (k r : Nat), 4 ≤ r →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (rowKey rowName : Nat) =>
    (List.range r).foldl (fun rowState rowIndex =>
      step (rowState ^^^ rot 1 rowState ^^^ rot (k - 1) rowState) ^^^
        rot (2 * rowIndex) rowKey ^^^ constant (rowIndex + 1)) (rot 1 rowKey ^^^ rowName)
  let second := fun (colKey colName : Nat) =>
    (List.range r).foldl (fun colState colIndex =>
      step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
        rot (3 * (colIndex + 1) + 1) colKey ^^^ constant (r + (colIndex + 1)))
      (rot 3 colKey ^^^ colName)
  let h := (k + 1) / 2
  let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
    (List.range (2 ^ k)).any (fun w =>
      decide (first w row.val < 2 ^ (k - h)) && decide (second w col.val < 2 ^ (k - h)))
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + k) C ∧
    C.size ≤ 2 ^ (min k (6 * r - 5)) * (24 * (k + 1) ^ 2 * (r + 1)) ∧
    ∀ bits : Fin (k + k) → Bool,
      C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits := by
  intro k r hr
  have rowEq (w u : Nat) :
      (List.range r).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit i)
            (!((s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit ((i + 1) % k)) &&
             (s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ rot k (2 * t) w ^^^ constant k (t + 1)) (rot k 1 w ^^^ u) = rowWord k w u r := by
    simp only [← wordStep_eq]
    exact round_fold (rowWord k w u) (fun s t => updateRound k 1 (2 * t) (t + 1) w s) (by intros; rfl) r
  have colEq (w v : Nat) :
      (List.range r).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit i)
            (!((s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit ((i + 1) % k)) &&
             (s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ rot k (3 * (t + 1) + 1) w ^^^ constant k (r + (t + 1))) (rot k 3 w ^^^ v) = colWord k r w v r := by
    simp only [← wordStep_eq]
    exact round_fold (colWord k r w v)
      (fun s t => updateRound k 2 (3 * (t + 1) + 1) (r + (t + 1)) w s) (by intros; rfl) r
  dsimp only
  obtain ⟨C, hFan, hRead, hSize, hEval⟩ := solve k r hr
  refine ⟨C, hFan, hRead, hSize, fun b => ?_⟩
  rw [hEval]
  unfold PEqualNP.Represents.adjFun
  dsimp only
  simp only [← wordStep_eq] at rowEq colEq ⊢
  change _ = (List.range (2 ^ k)).any (fun w =>
    decide ((List.range r).foldl (fun s t => wordStep k (s ^^^ rot k 1 s ^^^ rot k (k - 1) s)
      ^^^ rot k (2 * t) w ^^^ constant k (t + 1)) (rot k 1 w ^^^ ((U k b) % 2 ^ k)) < 2 ^ (k - (k + 1) / 2)) &&
    decide ((List.range r).foldl (fun s t => wordStep k (s ^^^ rot k 2 s ^^^ rot k (k - 2) s)
      ^^^ rot k (3 * (t + 1) + 1) w ^^^ constant k (r + (t + 1))) (rot k 3 w ^^^ ((V k b) % 2 ^ k)) < 2 ^ (k - (k + 1) / 2)))
  simp only [Nat.mod_eq_of_lt (U_lt k b), Nat.mod_eq_of_lt (V_lt k b), rowEq, colEq]
