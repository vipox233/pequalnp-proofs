import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29778

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

section GateBridge

variable {α : Type*}

def Scheduled (n : ℕ) (F : α → (Fin n → Bool) → Bool) (k : ℕ) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : ℕ, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x

lemma wireLength (C : Circuit) (w : List Bool) :
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

lemma schedStart {n : ℕ} {F : α → (Fin n → Bool) → Bool}
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

lemma schedRestrict {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k S) (hsub : T ⊆ S) : Scheduled n F k T := by
  obtain ⟨gs, hs, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hr, hf, fun a ha => hw a (hsub ha)⟩

lemma realizeDeps {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α}
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

lemma schedPush {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α}
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

end GateBridge

section BuildComb

variable {n : ℕ}
abbrev Sig (n : ℕ) := (Fin n → Bool) → Bool
abbrev NatSig (n : ℕ) := (Fin n → Bool) → ℕ

def Build (A B : Set (Sig n)) (b : ℕ) : Prop :=
  True ∧ (∀ {m S}, Scheduled n id m S → A ⊆ S →
    ∃ c ≤ b, Scheduled n id (m + c) (S ∪ B))

lemma Build.run {A B : Set (Sig n)} {b m S} (H : Build A B b)
    (HS : Scheduled n id m S) (hA : A ⊆ S) :
    ∃ c ≤ b, Scheduled n id (m + c) (S ∪ B) := H.2 HS hA

lemma idle {A B : Set (Sig n)} (h : B ⊆ A) : Build A B 0 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

lemma relax {A B C D : Set (Sig n)} {b d : ℕ}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c, hc, HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c, hc.trans h, schedRestrict HS' (Set.union_subset_union le_rfl hB)⟩

lemma seq {A B C : Set (Sig n)} {b c : ℕ}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  obtain ⟨d, hd, K⟩ := H.run HS hA
  obtain ⟨e, he, K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d + e, Nat.add_le_add hd he, by simpa [Nat.add_assoc, Set.union_assoc] using K'⟩

lemma seqRight {A B C : Set (Sig n)} {b c : ℕ}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A C (b + c) :=
  relax (seq H J) le_rfl Set.subset_union_right le_rfl

lemma oneG {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨1, le_rfl, ?_⟩
  have h := schedPush HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact schedRestrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

def an (f g : Sig n) : Sig n := fun x => f x && g x
def orS (f g : Sig n) : Sig n := fun x => f x || g x
def nt (f : Sig n) : Sig n := fun x => !f x
def xr (f g : Sig n) : Sig n := fun x => xor (f x) (g x)

lemma andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {an f g} 1 :=
  oneG .and [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

lemma orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {orS f g} 1 :=
  oneG .or [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, orS])

lemma notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : Build A {nt f} 1 :=
  oneG .not [f] (by simp) (by simp) (by simpa using hf) _ (by simp [GateOp.eval, nt])

lemma constG {A : Set (Sig n)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b
  · exact oneG .or [] (by simp) (by simp) (by simp) _ (by intro; rfl)
  · exact oneG .and [] (by simp) (by simp) (by simp) _ (by intro; rfl)

lemma xorG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {xr f g} 4 := by
  have he : xr f g = an (orS f g) (nt (an f g)) := by
    funext x; simp only [xr, an, orS, nt]; cases f x <;> cases g x <;> rfl
  rw [he]
  have h1 := orG hf hg
  have h2 := andG (A := A ∪ {orS f g}) (Or.inl hf) (Or.inl hg)
  have h3 := notG (A := A ∪ ({orS f g} ∪ {an f g})) (Or.inr (Or.inr rfl))
  have h4 := andG (A := A ∪ (({orS f g} ∪ {an f g}) ∪ {nt (an f g)}))
    (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  exact relax (seq (seq (seq h1 h2) h3) h4) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

lemma xnorG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => decide (f x = g x)} 5 := by
  have he : (fun x => decide (f x = g x)) = nt (xr f g) := by
    funext x; simp only [nt, xr]; cases f x <;> cases g x <;> rfl
  rw [he]
  exact seqRight (xorG hf hg) (notG (Or.inr rfl))

lemma chiGateG {A : Set (Sig n)} {a b c : Sig n}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
    Build A {fun x => xor (a x) (!(b x) && c x)} 6 := by
  have h1 : Build A {nt b} 1 := notG hb
  have h2 : Build (A ∪ {nt b}) {an (nt b) c} 1 := andG (Or.inr rfl) (Or.inl hc)
  have h3 : Build (A ∪ ({nt b} ∪ {an (nt b) c})) {xr a (an (nt b) c)} 4 :=
    xorG (Or.inl ha) (Or.inr (Or.inr rfl))
  have he : xr a (an (nt b) c) = (fun x => xor (a x) (!(b x) && c x)) := rfl
  rw [he] at h3
  exact seqRight (seq h1 h2) h3

lemma listBuildSetsVar {α : Type*} {A : Set (Sig n)} (xs : List α)
    (B : α → Set (Sig n)) (c : α → ℕ) (H : ∀ a ∈ xs, Build A (B a) (c a)) :
    Build A {f | ∃ a ∈ xs, f ∈ B a} ((xs.map c).sum) := by
  induction xs with
  | nil =>
    exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp)
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ B a) Set.subset_union_left le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ (by simp)
    rintro f ⟨b, hb, hfb⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Or.inl hfb
    · exact Or.inr ⟨b, hb, hfb⟩

lemma listBuildSets {α : Type*} {A : Set (Sig n)} (xs : List α)
    (B : α → Set (Sig n)) (c : ℕ) (H : ∀ a ∈ xs, Build A (B a) c) :
    Build A {f | ∃ a ∈ xs, f ∈ B a} (xs.length * c) := by
  have h := listBuildSetsVar xs B (fun _ => c) H
  refine relax h le_rfl le_rfl ?_
  simp

lemma listBuild {α : Type*} {A : Set (Sig n)} (xs : List α)
    (F : α → Sig n) (c : ℕ) (H : ∀ a ∈ xs, Build A {F a} c) :
    Build A {f | ∃ a ∈ xs, f = F a} (xs.length * c) :=
  listBuildSets xs (fun a => {F a}) c H

lemma andListG {α : Type*} {A : Set (Sig n)} (xs : List α) (F : α → Sig n)
    (htrue : (fun _ => true) ∈ A) (hF : ∀ a ∈ xs, F a ∈ A) :
    Build A {fun x => xs.all (fun a => F a x)} xs.length := by
  induction xs with
  | nil =>
    exact relax (idle (Set.singleton_subset_iff.mpr htrue)) le_rfl le_rfl (by simp)
  | cons a xs ih =>
    have h1 := ih (fun b hb => hF b (List.mem_cons_of_mem a hb))
    have h2 : Build (A ∪ {fun x => xs.all (fun b => F b x)})
        {an (F a) (fun x => xs.all (fun b => F b x))} 1 :=
      andG (Or.inl (hF a List.mem_cons_self)) (Or.inr rfl)
    have he : an (F a) (fun x => xs.all (fun b => F b x)) =
        (fun x => (a :: xs).all (fun b => F b x)) := by
      funext x; simp [an]
    rw [he] at h2
    exact relax (seqRight h1 h2) le_rfl le_rfl (by simp)

def bitsVal (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 => bitsVal f m + if f m then 2 ^ m else 0

lemma bitsVal_lt (f : ℕ → Bool) : ∀ m, bitsVal f m < 2 ^ m
  | 0 => by simp [bitsVal]
  | m + 1 => by
    have ih := bitsVal_lt f m
    simp only [bitsVal, Nat.pow_succ]
    cases f m <;> simp <;> omega

lemma bitsVal_testBit (f : ℕ → Bool) : ∀ m i, i < m → (bitsVal f m).testBit i = f i
  | 0, _, hi => by omega
  | m + 1, i, hi => by
    simp only [bitsVal]
    have hlt := bitsVal_lt f m
    by_cases him : i = m
    · subst him
      cases hfm : f i
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact Nat.testBit_lt_two_pow hlt
      · simp only [↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
    · have him' : i < m := by omega
      cases hfm : f m
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact bitsVal_testBit f m i him'
      · simp only [↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt him']
        exact bitsVal_testBit f m i him'

lemma bitsVal_congr (f g : ℕ → Bool) : ∀ m, (∀ i < m, f i = g i) → bitsVal f m = bitsVal g m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [bitsVal]
    rw [bitsVal_congr f g m (fun i hi => h i (by omega)), h m (by omega)]

lemma bitsVal_of_testBit (x m : ℕ) (hx : x < 2 ^ m) :
    bitsVal (fun i => x.testBit i) m = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · exact bitsVal_testBit (fun j => x.testBit j) m i hi
  · have h1 := Nat.testBit_lt_two_pow
      ((bitsVal_lt (fun j => x.testBit j) m).trans_le
        (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.not_lt.mp hi)))
    have h2 := Nat.testBit_lt_two_pow
      (hx.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.not_lt.mp hi)))
    rw [h1, h2]

def carryRec (f g : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | m + 1 => (f m && g m) || (carryRec f g m && xor (f m) (g m))

def sumBitRec (f g : ℕ → Bool) (m i : ℕ) : Bool :=
  if i < m then xor (xor (f i) (g i)) (carryRec f g i)
  else if i = m then carryRec f g m
  else false

lemma bitsVal_addWord (f g : ℕ → Bool) : ∀ m,
    bitsVal (sumBitRec f g m) (m + 1) = bitsVal f m + bitsVal g m := by
  have haux : ∀ m, bitsVal (fun i => xor (xor (f i) (g i)) (carryRec f g i)) m +
      (if carryRec f g m then 2 ^ m else 0) = bitsVal f m + bitsVal g m := by
    intro m
    induction m with
    | zero => simp [bitsVal, carryRec]
    | succ m ih =>
      simp only [bitsVal, carryRec]
      have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
      rcases Bool.eq_false_or_eq_true (f m) with hf' | hf' <;>
        rcases Bool.eq_false_or_eq_true (g m) with hg' | hg' <;>
        rcases Bool.eq_false_or_eq_true (carryRec f g m) with hc' | hc' <;>
        simp [hf', hg', hc'] at ih ⊢ <;> omega
  intro m
  simp only [bitsVal]
  have hcon : bitsVal (sumBitRec f g m) m =
      bitsVal (fun i => xor (xor (f i) (g i)) (carryRec f g i)) m :=
    bitsVal_congr _ _ m (fun i hi => by simp [sumBitRec, hi])
  have htop : sumBitRec f g m m = carryRec f g m := by simp [sumBitRec]
  rw [hcon, htop]
  exact haux m

lemma addWordG {A : Set (Sig n)} (f g : ℕ → Sig n) (m : ℕ)
    (hf : ∀ i < m, f i ∈ A) (hg : ∀ i < m, g i ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {h | ∃ i < m + 1, h = fun v => sumBitRec (fun j => f j v) (fun j => g j v) m i}
      (12 * m) := by
  have hstep : ∀ t ≤ m, Build A
      ({fun v => carryRec (fun j => f j v) (fun j => g j v) t} ∪
       {h | ∃ i < t, h = fun v => xor (xor (f i v) (g i v)) (carryRec (fun j => f j v) (fun j => g j v) i)})
      (12 * t) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine relax (idle (A := A) ?_) le_rfl le_rfl (by omega)
      rintro h (rfl | ⟨i, hi, _⟩)
      · exact hfalse
      · omega
    | succ t ih =>
      intro ht
      have Hprev := ih (by omega)
      let Bprev :=
        {fun v => carryRec (fun j => f j v) (fun j => g j v) t} ∪
        {h | ∃ i < t, h = fun v => xor (xor (f i v) (g i v)) (carryRec (fun j => f j v) (fun j => g j v) i)}
      let A0 := A ∪ Bprev
      let cSig : Sig n := fun v => carryRec (fun j => f j v) (fun j => g j v) t
      have hc : cSig ∈ A0 := Or.inr (Or.inl rfl)
      have hft : f t ∈ A0 := Or.inl (hf t (by omega))
      have hgt : g t ∈ A0 := Or.inl (hg t (by omega))
      have Hx1 : Build A0 {xr (f t) (g t)} 4 := xorG hft hgt
      have Hsum : Build (A0 ∪ {xr (f t) (g t)}) {xr (xr (f t) (g t)) cSig} 4 :=
        xorG (Or.inr rfl) (Or.inl hc)
      have Hab : Build (A0 ∪ ({xr (f t) (g t)} ∪ {xr (xr (f t) (g t)) cSig})) {an (f t) (g t)} 1 :=
        andG (Or.inl hft) (Or.inl hgt)
      have Hcx : Build (A0 ∪ (({xr (f t) (g t)} ∪ {xr (xr (f t) (g t)) cSig}) ∪ {an (f t) (g t)}))
          {an cSig (xr (f t) (g t))} 1 :=
        andG (Or.inl hc) (Or.inr (Or.inl (Or.inl rfl)))
      have Hcnext : Build (A0 ∪ ((({xr (f t) (g t)} ∪ {xr (xr (f t) (g t)) cSig}) ∪ {an (f t) (g t)}) ∪
          {an cSig (xr (f t) (g t))})) {orS (an (f t) (g t)) (an cSig (xr (f t) (g t)))} 1 :=
        orG (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
      have Htot := seq Hprev (seq (seq (seq (seq Hx1 Hsum) Hab) Hcx) Hcnext)
      refine relax Htot le_rfl ?_ (by omega)
      rintro h (rfl | ⟨i, hi, rfl⟩)
      · exact Or.inr (Or.inr rfl)
      · by_cases hit : i = t
        · subst hit
          exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr rfl))))
        · exact Or.inl (Or.inr ⟨i, by omega, rfl⟩)
  have hmain := hstep m (Nat.le_refl m)
  refine relax hmain le_rfl ?_ le_rfl
  rintro h ⟨i, hi, rfl⟩
  by_cases him : i < m
  · right
    refine ⟨i, him, ?_⟩
    funext v; simp [sumBitRec, him]
  · have heq : i = m := by omega
    subst heq
    left
    funext v; simp [sumBitRec]

def wordBits (W : ℕ) (f : NatSig n) : Set (Sig n) :=
  {g | ∃ i < W, g = fun x => (f x).testBit i}

lemma constWordG {A : Set (Sig n)} (W c : ℕ)
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) :
    Build A (wordBits W (fun _ => c)) 0 := by
  refine idle ?_
  rintro g ⟨i, _, rfl⟩
  cases hc : c.testBit i
  · simpa only [hc] using h0
  · simpa only [hc] using h1

lemma boolToNatWordG {A : Set (Sig n)} (W : ℕ) (f : Sig n)
    (hf : f ∈ A) (h0 : (fun _ => false) ∈ A) :
    Build A (wordBits W (fun x => (f x).toNat)) 0 := by
  refine idle ?_
  rintro g ⟨i, _, rfl⟩
  cases i with
  | zero =>
    have he : (fun x => (f x).toNat.testBit 0) = f := by
      funext x; cases f x <;> rfl
    rw [he]; exact hf
  | succ i =>
    have he : (fun x => (f x).toNat.testBit (i + 1)) = (fun _ => false) := by
      funext x
      cases f x
      · simp
      · exact Nat.testBit_lt_two_pow (by
          have : 2 ≤ 2 ^ (i + 1) := by
            calc 2 = 2 ^ 1 := rfl
              _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          simp only [Bool.toNat_true]; omega)
    rw [he]; exact h0

lemma addNatG {A : Set (Sig n)} (W : ℕ) (f g : NatSig n)
    (hfl : ∀ x, f x < 2 ^ W) (hgl : ∀ x, g x < 2 ^ W)
    (hf : wordBits W f ⊆ A) (hg : wordBits W g ⊆ A)
    (h0 : (fun _ => false) ∈ A) :
    Build A (wordBits W (fun x => f x + g x)) (12 * W) := by
  have h := addWordG (fun i x => (f x).testBit i) (fun i x => (g x).testBit i) W
    (fun i hi => hf ⟨i, hi, rfl⟩) (fun i hi => hg ⟨i, hi, rfl⟩) h0
  refine relax h le_rfl ?_ le_rfl
  rintro s ⟨i, hi, rfl⟩
  refine ⟨i, by omega, ?_⟩
  funext x
  have hsum := bitsVal_addWord (fun j => (f x).testBit j) (fun j => (g x).testBit j) W
  rw [bitsVal_of_testBit (f x) W (hfl x), bitsVal_of_testBit (g x) W (hgl x)] at hsum
  have htb := bitsVal_testBit (sumBitRec (fun j => (f x).testBit j) (fun j => (g x).testBit j) W)
    (W + 1) i (by omega)
  rw [hsum] at htb
  exact htb

lemma sumListNatG {α : Type*} {A : Set (Sig n)} (W : ℕ) (xs : List α) (F : α → NatSig n)
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (hF : ∀ a ∈ xs, wordBits W (F a) ⊆ A)
    (hlt : ∀ x, (xs.map (fun a => F a x)).sum < 2 ^ W) :
    Build A (wordBits W (fun x => (xs.map (fun a => F a x)).sum)) (xs.length * (12 * W)) := by
  induction xs with
  | nil =>
    exact relax (constWordG W 0 h0 h1) le_rfl le_rfl (by simp)
  | cons a xs ih =>
    have hlt_tail : ∀ x, (xs.map (fun b => F b x)).sum < 2 ^ W := by
      intro x
      have hx := hlt x
      simp only [List.map_cons, List.sum_cons] at hx
      omega
    have hlt_head : ∀ x, F a x < 2 ^ W := by
      intro x
      have hx := hlt x
      simp only [List.map_cons, List.sum_cons] at hx
      omega
    have h1' := ih (fun b hb => hF b (List.mem_cons_of_mem a hb)) hlt_tail
    have h2' := addNatG (A := A ∪ wordBits W (fun x => (xs.map (fun b => F b x)).sum)) W
      (F a) (fun x => (xs.map (fun b => F b x)).sum)
      hlt_head hlt_tail
      ((hF a List.mem_cons_self).trans Set.subset_union_left)
      Set.subset_union_right
      (Or.inl h0)
    refine relax (seqRight h1' h2') le_rfl ?_ ?_
    · rintro g ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · simp only [List.length_cons, Nat.succ_mul]
      exact le_rfl

lemma maskNatG {A : Set (Sig n)} (W : ℕ) (cond : Sig n) (f : NatSig n)
    (hc : cond ∈ A) (hf : wordBits W f ⊆ A) :
    Build A (wordBits W (fun x => if cond x then f x else 0)) W := by
  have h := listBuild (List.range W) (fun i => an cond (fun x => (f x).testBit i)) 1
    (fun i hi => andG hc (hf ⟨i, List.mem_range.mp hi, rfl⟩))
  rw [List.length_range, Nat.mul_one] at h
  refine relax h le_rfl ?_ le_rfl
  rintro g ⟨i, hi, rfl⟩
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  funext x
  simp only [an]
  cases cond x <;> simp

lemma shiftNatG {A : Set (Sig n)} (W s : ℕ) (f : NatSig n)
    (hf : wordBits W f ⊆ A) (h0 : (fun _ => false) ∈ A) :
    Build A (wordBits W (fun x => f x * 2 ^ s)) 0 := by
  refine idle ?_
  rintro g ⟨i, hi, rfl⟩
  have he : (fun x => (f x * 2 ^ s).testBit i) =
      if i < s then (fun _ => false) else (fun x => (f x).testBit (i - s)) := by
    funext x
    rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
    by_cases his : i < s
    · have hns : ¬ s ≤ i := by omega
      simp [his, hns]
    · have hs : s ≤ i := by omega
      simp [his, hs]
  rw [he]
  split_ifs with his
  · exact h0
  · exact hf ⟨i - s, by omega, rfl⟩

lemma mul_eq_sum_bits (a b d : ℕ) (hb : b < 2 ^ d) :
    a * b = ((List.range d).map (fun j => if b.testBit j then a * 2 ^ j else 0)).sum := by
  have hval := bitsVal_of_testBit b d hb
  have hgen : ∀ m, a * bitsVal (fun j => b.testBit j) m =
      ((List.range m).map (fun j => if b.testBit j then a * 2 ^ j else 0)).sum := by
    intro m
    induction m with
    | zero => simp [bitsVal]
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton, ← ih]
      simp only [bitsVal]
      rcases Bool.eq_false_or_eq_true (b.testBit m) with hm | hm <;>
        simp [hm, Nat.mul_add]
  calc a * b = a * bitsVal (fun j => b.testBit j) d := by rw [hval]
    _ = ((List.range d).map (fun j => if b.testBit j then a * 2 ^ j else 0)).sum := hgen d

lemma mulConstNatG {A : Set (Sig n)} (W d c : ℕ) (f : NatSig n)
    (hc : c < 2 ^ d) (hlt : ∀ x, f x * c < 2 ^ W)
    (hf : wordBits W f ⊆ A) (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) :
    Build A (wordBits W (fun x => f x * c)) (d * (12 * W)) := by
  have he : (fun x => f x * c) =
      (fun x => ((List.range d).map (fun j => if c.testBit j then f x * 2 ^ j else 0)).sum) := by
    funext x; exact mul_eq_sum_bits (f x) c d hc
  rw [he]
  have hterm : ∀ j ∈ List.range d,
      wordBits W (fun x => if c.testBit j then f x * 2 ^ j else 0) ⊆ A := by
    intro j _
    by_cases hcb : c.testBit j = true
    · simp only [hcb, ↓reduceIte]
      rintro g ⟨i, hi, rfl⟩
      have he' : (fun x => (f x * 2 ^ j).testBit i) =
          if i < j then (fun _ => false) else (fun x => (f x).testBit (i - j)) := by
        funext x
        rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
        by_cases hij : i < j
        · simp [hij, show ¬ j ≤ i by omega]
        · simp [hij, show j ≤ i by omega]
      rw [he']
      split_ifs with hij
      · exact h0
      · exact hf ⟨i - j, by omega, rfl⟩
    · simp only [hcb]
      rintro g ⟨i, _, rfl⟩
      simpa using h0
  have h := sumListNatG W (List.range d)
    (fun j x => if c.testBit j then f x * 2 ^ j else 0) h0 h1 hterm
    (fun x => by rw [← mul_eq_sum_bits (f x) c d hc]; exact hlt x)
  rw [List.length_range] at h
  exact h

lemma mulNatG {A : Set (Sig n)} (W d : ℕ) (f g : NatSig n)
    (hgl : ∀ x, g x < 2 ^ d) (hlt : ∀ x, f x * g x < 2 ^ W)
    (hf : wordBits W f ⊆ A) (hg : wordBits d g ⊆ A)
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) :
    Build A (wordBits W (fun x => f x * g x)) (d * (13 * W)) := by
  have hmask : Build A
      {s | ∃ j ∈ List.range d, s ∈ wordBits W (fun x => if (g x).testBit j then f x * 2 ^ j else 0)}
      (d * W) := by
    have h := listBuildSets (List.range d)
      (fun j => wordBits W (fun x => if (g x).testBit j then f x * 2 ^ j else 0)) W
      (fun j hj => by
        have hsh : wordBits W (fun x => f x * 2 ^ j) ⊆ A := by
          rintro s ⟨i, hi, rfl⟩
          have he' : (fun x => (f x * 2 ^ j).testBit i) =
              if i < j then (fun _ => false) else (fun x => (f x).testBit (i - j)) := by
            funext x
            rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
            by_cases hij : i < j
            · simp [hij, show ¬ j ≤ i by omega]
            · simp [hij, show j ≤ i by omega]
          rw [he']
          split_ifs with hij
          · exact h0
          · exact hf ⟨i - j, by omega, rfl⟩
        exact maskNatG W (fun x => (g x).testBit j) (fun x => f x * 2 ^ j)
          (hg ⟨j, List.mem_range.mp hj, rfl⟩) hsh)
    rw [List.length_range] at h
    exact h
  have hsum : Build (A ∪ {s | ∃ j ∈ List.range d,
      s ∈ wordBits W (fun x => if (g x).testBit j then f x * 2 ^ j else 0)})
      (wordBits W (fun x => ((List.range d).map (fun j => if (g x).testBit j then f x * 2 ^ j else 0)).sum))
      (d * (12 * W)) := by
    have hsub : ∀ j ∈ List.range d,
        wordBits W (fun x => if (g x).testBit j then f x * 2 ^ j else 0) ⊆
        A ∪ {s | ∃ j ∈ List.range d, s ∈ wordBits W (fun x => if (g x).testBit j then f x * 2 ^ j else 0)} :=
      fun j hj s hs => Or.inr ⟨j, hj, hs⟩
    have h := sumListNatG W (List.range d)
      (fun j x => if (g x).testBit j then f x * 2 ^ j else 0)
      (Or.inl h0) (Or.inl h1) hsub
      (fun x => by rw [← mul_eq_sum_bits (f x) (g x) d (hgl x)]; exact hlt x)
    rw [List.length_range] at h
    exact h
  have he : (fun x => ((List.range d).map (fun j => if (g x).testBit j then f x * 2 ^ j else 0)).sum) =
      (fun x => f x * g x) := by
    funext x; exact (mul_eq_sum_bits (f x) (g x) d (hgl x)).symm
  rw [he] at hsum
  refine relax (seqRight hmask hsum) le_rfl le_rfl ?_
  have : d * W + d * (12 * W) = d * (13 * W) := by ring
  omega

lemma powNatG {A : Set (Sig n)} (W d : ℕ) (f : NatSig n)
    (hW : 1 ≤ W) (hfl : ∀ x, f x < 2 ^ d)
    (hf : wordBits d f ⊆ A) (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) :
    ∀ t : ℕ, (∀ x, (f x) ^ t < 2 ^ W) →
      Build A (wordBits W (fun x => (f x) ^ t)) (t * (13 * d * W))
  | 0, _ => by
    have he : (fun x : Fin n → Bool => (f x) ^ 0) = (fun _ => 1) := by funext x; simp
    rw [he]
    exact relax (constWordG W 1 h0 h1) le_rfl le_rfl (by simp)
  | t + 1, hlt => by
    have hlt_t : ∀ x, (f x) ^ t < 2 ^ W := by
      intro x
      by_cases hfx : f x = 0
      · cases t with
        | zero =>
          simp only [pow_zero]
          exact Nat.one_lt_two_pow (by omega)
        | succ t =>
          simp only [hfx, zero_pow (Nat.succ_ne_zero t)]
          exact Nat.two_pow_pos W
      · have hpos : 1 ≤ f x := Nat.pos_of_ne_zero hfx
        calc (f x) ^ t = (f x) ^ t * 1 := (Nat.mul_one _).symm
          _ ≤ (f x) ^ t * f x := Nat.mul_le_mul_left _ hpos
          _ = (f x) ^ (t + 1) := (pow_succ (f x) t).symm
          _ < 2 ^ W := hlt x
    have hprev := powNatG W d f hW hfl hf h0 h1 t hlt_t
    have hmul : Build (A ∪ wordBits W (fun x => (f x) ^ t))
        (wordBits W (fun x => (f x) ^ t * f x)) (d * (13 * W)) :=
      mulNatG W d (fun x => (f x) ^ t) f hfl
        (fun x => by simpa [pow_succ] using hlt x)
        Set.subset_union_right
        (hf.trans Set.subset_union_left)
        (Or.inl h0) (Or.inl h1)
    have he : (fun x => (f x) ^ t * f x) = (fun x => (f x) ^ (t + 1)) := by
      funext x; rw [pow_succ]
    rw [he] at hmul
    refine relax (seqRight hprev hmul) le_rfl le_rfl ?_
    have : t * (13 * d * W) + d * (13 * W) = (t + 1) * (13 * d * W) := by ring
    omega

end BuildComb

section CipherSem

def rotN (k d x : ℕ) : ℕ :=
  ((x <<< (d % k)) ||| (x >>> (k - d % k))) % 2 ^ k

def chiN (k x : ℕ) : ℕ :=
  (List.range k).foldl (fun (acc i : ℕ) =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0

def runStep (k r : ℕ) (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key z j : ℕ) : ℕ :=
  let gap : ℕ := if col then 2 else 1
  let mixed := z ^^^ rotN k gap z ^^^ rotN k (k - gap % k) z
  chiN k mixed ^^^ rotN k (if col then 3 * (j + 1) + 1 else 2 * j) key ^^^
    (masks (if col then r + j else j)).val

def runPrefix (k r : ℕ) (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key name m : ℕ) : ℕ :=
  (List.range m).foldl (runStep k r masks col key) (rotN k (if col then 3 else 1) key ^^^ name)

def runN (k r : ℕ) (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key name : ℕ) : ℕ :=
  runPrefix k r masks col key name r

lemma rotN_lt (k d x : ℕ) : rotN k d x < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma testBit_pack (f : ℕ → Bool) (m j : ℕ) :
    ((List.range m).foldl (fun acc i => acc ||| ((f i).toNat <<< i)) 0).testBit j =
      (decide (j < m) && f j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Nat.testBit_or, ih, Nat.shiftLeft_eq]
    by_cases h : m = j
    · subst h; cases f m <;> simp
    · have hcmp : j < m + 1 ↔ j < m := by omega
      cases f m <;> simp [h, hcmp]

lemma chiN_lt (k x : ℕ) : chiN k x < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  unfold chiN
  rw [testBit_pack]
  simp [Nat.not_lt_of_ge hj]

lemma chiN_testBit {k x j : ℕ} (hj : j < k) :
    (chiN k x).testBit j =
      xor (x.testBit j) (!(x.testBit ((j + 1) % k)) && x.testBit ((j + 2) % k)) := by
  unfold chiN
  rw [testBit_pack, decide_eq_true hj, Bool.true_and]

lemma runPrefix_zero (k r : ℕ) (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key name : ℕ) :
    runPrefix k r masks col key name 0 = rotN k (if col then 3 else 1) key ^^^ name := rfl

lemma runPrefix_succ (k r : ℕ) (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key name m : ℕ) :
    runPrefix k r masks col key name (m + 1) =
      runStep k r masks col key (runPrefix k r masks col key name m) m := by
  unfold runPrefix
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma runPrefix_lt {k r : ℕ} (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key name m : ℕ)
    (hname : name < 2 ^ k) : runPrefix k r masks col key name m < 2 ^ k := by
  induction m with
  | zero => exact Nat.xor_lt_two_pow (rotN_lt k _ key) hname
  | succ m _ =>
    rw [runPrefix_succ]
    unfold runStep
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (chiN_lt k _) (rotN_lt k _ key))
      (masks _).isLt

def cidx (k : ℕ) (i : ℤ) : ℕ := (i % (k : ℤ)).toNat

def cbit (k x : ℕ) (i : ℤ) : Bool := x.testBit (cidx k i)

lemma cidx_lt {k : ℕ} (hk : 0 < k) (i : ℤ) : cidx k i < k := by
  unfold cidx
  have hk0 : (0 : ℤ) < (k : ℤ) := by omega
  have h1 : 0 ≤ i % (k : ℤ) := Int.emod_nonneg i (ne_of_gt hk0)
  have h2 : i % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos i hk0
  omega

lemma cidx_nat {k i : ℕ} (hi : i < k) : cidx k (i : ℤ) = i := by
  unfold cidx
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  rfl

lemma cidx_nat_mod (k i : ℕ) : cidx k (i : ℤ) = i % k := by
  unfold cidx
  rw [← Int.natCast_emod]
  rfl

lemma cidx_congr {k : ℕ} {i j : ℤ} (h : i % (k : ℤ) = j % (k : ℤ)) :
    cidx k i = cidx k j := by
  unfold cidx; rw [h]

lemma cbit_xor (k x y : ℕ) (i : ℤ) : cbit k (x ^^^ y) i = xor (cbit k x i) (cbit k y i) :=
  Nat.testBit_xor x y (cidx k i)

lemma cbit_rotN {k d x : ℕ} (hk : 0 < k) (hx : x < 2 ^ k) (i : ℤ) :
    cbit k (rotN k d x) i = cbit k x (i - (d : ℤ)) := by
  have hi : cidx k i < k := cidx_lt hk i
  unfold cbit rotN
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  set r := cidx k i
  set s := d % k
  have hs : s < k := Nat.mod_lt d hk
  have hr_eq : (r : ℤ) = i % (k : ℤ) := by
    have hk0 : (0 : ℤ) < (k : ℤ) := by omega
    exact Int.toNat_of_nonneg (Int.emod_nonneg i (ne_of_gt hk0))
  by_cases hsi : s ≤ r
  · have hhi : x.testBit (k - s + r) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
    simp only [hsi, decide_true, Bool.true_and, hhi, Bool.or_false]
    congr 1
    have hmod : (i - (d : ℤ)) % (k : ℤ) = ((r - s : ℕ) : ℤ) := by
      have h1 : (i - (d : ℤ)) % (k : ℤ) = (i % (k : ℤ) - (d : ℤ) % (k : ℤ)) % (k : ℤ) := by
        rw [Int.sub_emod]
      have hds : (d : ℤ) % (k : ℤ) = (s : ℤ) := by
        simp [s]
      rw [h1, ← hr_eq, hds]
      have hge : 0 ≤ (r : ℤ) - (s : ℤ) := by omega
      have hlt : (r : ℤ) - (s : ℤ) < (k : ℤ) := by omega
      rw [Int.emod_eq_of_lt hge hlt]
      omega
    unfold cidx; rw [hmod]; rfl
  · have hmod : (i - (d : ℤ)) % (k : ℤ) = ((k - s + r : ℕ) : ℤ) := by
      have h1 : (i - (d : ℤ)) % (k : ℤ) = (i % (k : ℤ) - (d : ℤ) % (k : ℤ)) % (k : ℤ) := by
        rw [Int.sub_emod]
      have hds : (d : ℤ) % (k : ℤ) = (s : ℤ) := by
        simp [s]
      rw [h1, ← hr_eq, hds]
      have hadd : ((r : ℤ) - (s : ℤ)) % (k : ℤ) = ((r : ℤ) - (s : ℤ) + (k : ℤ)) % (k : ℤ) := by
        rw [Int.add_emod_right]
      rw [hadd, Int.emod_eq_of_lt (by omega) (by omega)]
      omega
    simp only [hsi, decide_false, Bool.false_and, Bool.false_or]
    congr 1
    unfold cidx; rw [hmod]; rfl

lemma cbit_rotN_neg {k d x : ℕ} (hk : 0 < k) (hx : x < 2 ^ k) (i : ℤ) :
    cbit k (rotN k (k - d % k) x) i = cbit k x (i + (d : ℤ)) := by
  rw [cbit_rotN hk hx i]
  unfold cbit
  congr 1
  apply cidx_congr
  have hs : d % k < k := Nat.mod_lt d hk
  have hcast : ((k - d % k : ℕ) : ℤ) = (k : ℤ) - ((d % k : ℕ) : ℤ) := by omega
  have hds : ((d % k : ℕ) : ℤ) = (d : ℤ) % (k : ℤ) := by
    simp
  rw [hcast, hds]
  calc (i - ((k : ℤ) - (d : ℤ) % (k : ℤ))) % (k : ℤ)
      = (i + (d : ℤ) % (k : ℤ) - (k : ℤ)) % (k : ℤ) := by ring_nf
    _ = (i + (d : ℤ) % (k : ℤ)) % (k : ℤ) := Int.sub_emod_right _ _
    _ = (i + (d : ℤ)) % (k : ℤ) := by rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]

lemma cbit_chiN {k x : ℕ} (hk : 0 < k) (i : ℤ) :
    cbit k (chiN k x) i = xor (cbit k x i) (!(cbit k x (i + 1)) && cbit k x (i + 2)) := by
  have hi : cidx k i < k := cidx_lt hk i
  unfold cbit
  rw [chiN_testBit hi]
  have h1 : (cidx k i + 1) % k = cidx k (i + 1) := by
    rw [← cidx_nat_mod]
    apply cidx_congr
    have hk0 : (0 : ℤ) < (k : ℤ) := by omega
    have hr : (cidx k i : ℤ) = i % (k : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg i (ne_of_gt hk0))
    push_cast
    rw [hr, Int.add_emod, Int.emod_emod, ← Int.add_emod]
  have h2 : (cidx k i + 2) % k = cidx k (i + 2) := by
    rw [← cidx_nat_mod]
    apply cidx_congr
    have hk0 : (0 : ℤ) < (k : ℤ) := by omega
    have hr : (cidx k i : ℤ) = i % (k : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg i (ne_of_gt hk0))
    push_cast
    rw [hr, Int.add_emod, Int.emod_emod, ← Int.add_emod]
  rw [h1, h2]

def srun (r : ℕ) (col : Bool) (key name : ℤ → Bool) (ms : ℕ → ℤ → Bool) : ℕ → ℤ → Bool
  | 0, i => xor (key (i - (if col then 3 else 1))) (name i)
  | m + 1, i =>
      let gap : ℤ := if col then 2 else 1
      let prev := srun r col key name ms m
      let mix := fun q => xor (xor (prev q) (prev (q - gap))) (prev (q + gap))
      let ch := xor (mix i) (!(mix (i + 1)) && mix (i + 2))
      let kshift : ℤ := if col then (3 * (m + 1) + 1 : ℕ) else (2 * m : ℕ)
      xor (xor ch (key (i - kshift))) (ms (if col then r + m else m) i)

lemma cbit_runPrefix {k r : ℕ} (hk : 0 < k) (masks : ℕ → Fin (2 ^ k)) (col : Bool)
    {key name : ℕ} (hkey : key < 2 ^ k) (hname : name < 2 ^ k) :
    ∀ m i, cbit k (runPrefix k r masks col key name m) i =
      srun r col (cbit k key) (cbit k name) (fun j => cbit k (masks j).val) m i
  | 0, i => by
    rw [runPrefix_zero, cbit_xor, cbit_rotN hk hkey]
    cases col <;> rfl
  | m + 1, i => by
    rw [runPrefix_succ]
    unfold runStep
    have hprev := runPrefix_lt (r := r) masks col key name m hname
    rw [cbit_xor, cbit_xor, cbit_rotN hk hkey, cbit_chiN hk]
    have hmix : ∀ q, cbit k (runPrefix k r masks col key name m ^^^
        rotN k (if col then 2 else 1) (runPrefix k r masks col key name m) ^^^
        rotN k (k - (if col then 2 else 1) % k) (runPrefix k r masks col key name m)) q =
        xor (xor (srun r col (cbit k key) (cbit k name) (fun j => cbit k (masks j).val) m q)
          (srun r col (cbit k key) (cbit k name) (fun j => cbit k (masks j).val) m
            (q - (if col then 2 else 1))))
          (srun r col (cbit k key) (cbit k name) (fun j => cbit k (masks j).val) m
            (q + (if col then 2 else 1))) := by
      intro q
      rw [cbit_xor, cbit_xor, cbit_rotN hk hprev, cbit_rotN_neg hk hprev,
        cbit_runPrefix hk masks col hkey hname m,
        cbit_runPrefix hk masks col hkey hname m,
        cbit_runPrefix hk masks col hkey hname m]
      cases col <;> rfl
    rw [hmix i, hmix (i + 1), hmix (i + 2)]
    cases col <;> rfl

lemma srun_translate (r : ℕ) (col : Bool) (key name : ℤ → Bool) (ms : ℕ → ℤ → Bool) (p : ℤ) :
    ∀ m i, srun r col (fun q => key (p + q)) (fun q => name (p + q)) (fun j q => ms j (p + q)) m i =
      srun r col key name ms m (p + i)
  | 0, i => by
    simp only [srun]
    congr 2; omega
  | m + 1, i => by
    simp only [srun]
    have ih := srun_translate r col key name ms p m
    have h1 : ∀ q : ℤ, p + q - (if col then (2 : ℤ) else 1) = p + (q - (if col then (2 : ℤ) else 1)) := by
      intro q; omega
    have h2 : ∀ q : ℤ, p + q + (if col then (2 : ℤ) else 1) = p + (q + (if col then (2 : ℤ) else 1)) := by
      intro q; omega
    simp only [ih, ← h1, ← h2]
    have ha1 : p + (i + 1) = p + i + 1 := by omega
    have ha2 : p + (i + 2) = p + i + 2 := by omega
    have hk : p + (i - (if col then ((3 * (m + 1) + 1 : ℕ) : ℤ) else ((2 * m : ℕ) : ℤ))) =
        p + i - (if col then ((3 * (m + 1) + 1 : ℕ) : ℤ) else ((2 * m : ℕ) : ℤ)) := by
      cases col <;> omega
    rw [ha1, ha2, hk]

def bName (r : ℕ) (col : Bool) : ℕ := if col then 6 * r else 4 * r

def lName (r : ℕ) (col : Bool) : ℤ := -(if col then (2 * r : ℤ) else (r : ℤ))

def bKey (r : ℕ) : ℕ := if r = 0 then 2 else if r = 1 then 7 else 7 * r - 2

def lKey (r : ℕ) : ℤ := if r = 0 then -3 else if r = 1 then -5 else -(3 * (r : ℤ)) - 1

lemma srun_local (r : ℕ) (col : Bool) (key1 key2 name1 name2 : ℤ → Bool) (ms : ℕ → ℤ → Bool)
    (hname : ∀ q : ℤ, lName r col ≤ q → q ≤ lName r col + (bName r col : ℤ) → name1 q = name2 q)
    (hkey : ∀ q : ℤ, lKey r ≤ q → q ≤ lKey r + (bKey r : ℤ) → key1 q = key2 q) :
    ∀ m ≤ r, ∀ i : ℤ,
      -((r - m : ℕ) : ℤ) * (if col then 2 else 1) ≤ i →
      i ≤ ((r - m : ℕ) : ℤ) * (if col then 4 else 3) →
      srun r col key1 name1 ms m i = srun r col key2 name2 ms m i
  | 0, _, i, hlo, hhi => by
    simp only [srun]
    have hn : name1 i = name2 i := by
      apply hname
      · unfold lName; cases col <;> simp at hlo ⊢ <;> omega
      · unfold lName bName; cases col <;> simp at hhi ⊢ <;> omega
    have hk : key1 (i - (if col then 3 else 1)) = key2 (i - (if col then 3 else 1)) := by
      apply hkey
      · unfold lKey; cases col <;> split_ifs at * <;> simp at hlo ⊢ <;> omega
      · unfold lKey bKey; cases col <;> split_ifs at * <;> simp at hhi ⊢ <;> omega
    rw [hn, hk]
  | m + 1, hm, i, hlo, hhi => by
    simp only [srun]
    have ih := srun_local r col key1 key2 name1 name2 ms hname hkey m (by omega)
    have hq : ∀ δ : ℤ, -(if col then (2 : ℤ) else 1) ≤ δ → δ ≤ (if col then (4 : ℤ) else 3) →
        srun r col key1 name1 ms m (i + δ) = srun r col key2 name2 ms m (i + δ) := by
      intro δ hd1 hd2
      apply ih
      · cases col <;> simp at hlo hd1 ⊢ <;> omega
      · cases col <;> simp at hhi hd2 ⊢ <;> omega
    have hmix : ∀ off : ℤ, 0 ≤ off → off ≤ 2 →
        (xor (xor (srun r col key1 name1 ms m (i + off))
          (srun r col key1 name1 ms m (i + off - (if col then 2 else 1))))
          (srun r col key1 name1 ms m (i + off + (if col then 2 else 1)))) =
        (xor (xor (srun r col key2 name2 ms m (i + off))
          (srun r col key2 name2 ms m (i + off - (if col then 2 else 1))))
          (srun r col key2 name2 ms m (i + off + (if col then 2 else 1)))) := by
      intro off ho1 ho2
      have e1 : srun r col key1 name1 ms m (i + off) = srun r col key2 name2 ms m (i + off) :=
        hq off (by cases col <;> omega) (by cases col <;> omega)
      have e2 : srun r col key1 name1 ms m (i + off - (if col then 2 else 1)) =
          srun r col key2 name2 ms m (i + off - (if col then 2 else 1)) := by
        rw [show i + off - (if col then (2 : ℤ) else 1) = i + (off - (if col then 2 else 1)) by omega]
        exact hq _ (by cases col <;> omega) (by cases col <;> omega)
      have e3 : srun r col key1 name1 ms m (i + off + (if col then 2 else 1)) =
          srun r col key2 name2 ms m (i + off + (if col then 2 else 1)) := by
        rw [show i + off + (if col then (2 : ℤ) else 1) = i + (off + (if col then 2 else 1)) by omega]
        exact hq _ (by cases col <;> simp <;> omega) (by cases col <;> simp <;> omega)
      rw [e1, e2, e3]
    have hm0 := hmix 0 (by omega) (by omega)
    simp only [Int.add_zero] at hm0
    have hm1 := hmix 1 (by omega) (by omega)
    have hm2 := hmix 2 (by omega) (by omega)
    have hk : key1 (i - (if col then ((3 * (m + 1) + 1 : ℕ) : ℤ) else ((2 * m : ℕ) : ℤ))) =
        key2 (i - (if col then ((3 * (m + 1) + 1 : ℕ) : ℤ) else ((2 * m : ℕ) : ℤ))) := by
      apply hkey
      · unfold lKey; cases col <;> split_ifs at * <;> simp at hlo ⊢ <;> omega
      · unfold lKey bKey; cases col <;> split_ifs at * <;> simp at hhi ⊢ <;> omega
    rw [hm0, hm1, hm2, hk]

def winExt (lo : ℤ) {b : ℕ} (w : Fin (b + 1) → Bool) (q : ℤ) : Bool :=
  if h : 0 ≤ q - lo ∧ (q - lo).toNat < b + 1 then w ⟨(q - lo).toNat, h.2⟩ else false

lemma winExt_eq (lo : ℤ) {b : ℕ} (w : Fin (b + 1) → Bool) (q : ℤ)
    (h1 : lo ≤ q) (h2 : q ≤ lo + (b : ℤ)) :
    winExt lo w q = w ⟨(q - lo).toNat, by omega⟩ := by
  unfold winExt
  have hc : 0 ≤ q - lo ∧ (q - lo).toNat < b + 1 := by omega
  simp [hc, h1]

lemma evalLocalSrunG {n : ℕ} {A : Set (Sig n)} (r : ℕ) (col : Bool)
    (keyWin : Fin (bKey r + 1) → Bool) (nameWin : Fin (bName r col + 1) → Bool)
    (msSig : ℕ → ℤ → Sig n)
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (hms : ∀ j < 2 * r, ∀ q : ℤ, msSig j q ∈ A) :
    Build A
      {fun x => srun r col (winExt (lKey r) keyWin) (winExt (lName r col) nameWin)
        (fun j q => msSig j q x) r 0}
      (250 * (r + 1) ^ 2) := by
  let gL : ℕ := if col then 2 else 1
  let gR : ℕ := if col then 4 else 3
  let W_m (m : ℕ) : ℕ := (r - m) * (gL + gR) + 1
  let posOf (m idx : ℕ) : ℤ := -(((r - m) * gL : ℕ) : ℤ) + (idx : ℤ)
  let layer (m : ℕ) : Set (Sig n) :=
    {f | ∃ idx < W_m m, f = fun x =>
      srun r col (winExt (lKey r) keyWin) (winExt (lName r col) nameWin)
        (fun j q => msSig j q x) m (posOf m idx)}
  have hlayer : ∀ m ≤ r, Build A (layer m) (m * (38 * (6 * r + 1))) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine relax (idle ?_) le_rfl le_rfl (by simp)
      rintro f ⟨idx, _, rfl⟩
      simp only [srun]
      cases xor (winExt (lKey r) keyWin (posOf 0 idx - (if col then 3 else 1)))
          (winExt (lName r col) nameWin (posOf 0 idx))
      · exact h0
      · exact h1
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have hW_le : W_m (m + 1) ≤ 6 * r + 1 := by
        dsimp [W_m, gL, gR]; cases col <;> simp <;> omega
      have hmemPrev : ∀ idx < W_m (m + 1), ∀ δ : ℤ,
          -(gL : ℤ) ≤ δ → δ ≤ (gR : ℤ) →
          (fun x => srun r col (winExt (lKey r) keyWin) (winExt (lName r col) nameWin)
            (fun j q => msSig j q x) m (posOf (m + 1) idx + δ)) ∈ A ∪ layer m := by
        intro idx hidx δ hd1 hd2
        right
        let idx' : ℕ := (posOf (m + 1) idx + δ + (((r - m) * gL : ℕ) : ℤ)).toNat
        have hpos_eq : posOf m idx' = posOf (m + 1) idx + δ := by
          dsimp [idx', posOf, gL, gR] at *
          cases col <;> simp at * <;> omega
        have hidx'_lt : idx' < W_m m := by
          dsimp [idx', posOf, W_m, gL, gR] at *
          cases col <;> simp at * <;> omega
        exact ⟨idx', hidx'_lt, by rw [hpos_eq]⟩
      have hstep : Build (A ∪ layer m) (layer (m + 1)) (W_m (m + 1) * 38) := by
        have hb := listBuild (List.range (W_m (m + 1)))
          (fun idx x => srun r col (winExt (lKey r) keyWin) (winExt (lName r col) nameWin)
            (fun j q => msSig j q x) (m + 1) (posOf (m + 1) idx))
          38
          (fun idx hidx => by
            have hidx' : idx < W_m (m + 1) := List.mem_range.mp hidx
            let p := posOf (m + 1) idx
            let F (q : ℤ) : Sig n := fun x =>
              srun r col (winExt (lKey r) keyWin) (winExt (lName r col) nameWin)
                (fun j q' => msSig j q' x) m q
            have hF : ∀ δ : ℤ, -(gL : ℤ) ≤ δ → δ ≤ (gR : ℤ) → F (p + δ) ∈ A ∪ layer m :=
              hmemPrev idx hidx'
            let mkMix (off : ℤ) : Sig n :=
              xr (xr (F (p + off)) (F (p + off - (if col then 2 else 1))))
                (F (p + off + (if col then 2 else 1)))
            have buildMix : ∀ off : ℤ, 0 ≤ off → off ≤ 2 →
                Build (A ∪ layer m) {mkMix off} 8 := by
              intro off ho1 ho2
              have hm1 : F (p + off) ∈ A ∪ layer m :=
                hF off (by dsimp [gL]; cases col <;> simp <;> omega)
                  (by dsimp [gR]; cases col <;> simp <;> omega)
              have hm2 : F (p + off - (if col then 2 else 1)) ∈ A ∪ layer m := by
                rw [show p + off - (if col then (2 : ℤ) else 1) = p + (off - (if col then 2 else 1)) by omega]
                exact hF _ (by dsimp [gL]; cases col <;> simp <;> omega)
                  (by dsimp [gR]; cases col <;> simp <;> omega)
              have hm3 : F (p + off + (if col then 2 else 1)) ∈ A ∪ layer m := by
                rw [show p + off + (if col then (2 : ℤ) else 1) = p + (off + (if col then 2 else 1)) by omega]
                exact hF _ (by dsimp [gL]; cases col <;> simp <;> omega)
                  (by dsimp [gR]; cases col <;> simp <;> omega)
              exact seqRight (xorG hm1 hm2) (xorG (Or.inr rfl) (Or.inl hm3))
            have hM0 : Build (A ∪ layer m) {mkMix 0} 8 := buildMix 0 (by omega) (by omega)
            have hM1 : Build ((A ∪ layer m) ∪ {mkMix 0}) {mkMix 1} 8 :=
              relax (buildMix 1 (by omega) (by omega)) Set.subset_union_left le_rfl le_rfl
            have hM2 : Build ((A ∪ layer m) ∪ ({mkMix 0} ∪ {mkMix 1})) {mkMix 2} 8 :=
              relax (buildMix 2 (by omega) (by omega)) Set.subset_union_left le_rfl le_rfl
            have hM012 := seq (seq hM0 hM1) hM2
            let chSig : Sig n := fun x => xor (mkMix 0 x) (!(mkMix 1 x) && mkMix 2 x)
            let S1 := (A ∪ layer m) ∪ (({mkMix 0} ∪ {mkMix 1}) ∪ {mkMix 2})
            have hCh : Build S1 {chSig} 6 :=
              chiGateG (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
            let kbit : Bool := winExt (lKey r) keyWin
              (p - (if col then ((3 * (m + 1) + 1 : ℕ) : ℤ) else ((2 * m : ℕ) : ℤ)))
            have hkConst : (fun _ : Fin n → Bool => kbit) ∈ A ∪ layer m := by
              left; cases kbit
              · exact h0
              · exact h1
            let xkSig : Sig n := xr chSig (fun _ => kbit)
            have hXk : Build ((A ∪ layer m) ∪ {chSig}) {xkSig} 4 :=
              xorG (Or.inr rfl) (Or.inl hkConst)
            have hmsMem : msSig (if col then r + m else m) p ∈ A ∪ layer m := by
              left; apply hms
              cases col <;> simp <;> omega
            let xmSig : Sig n := xr xkSig (msSig (if col then r + m else m) p)
            have hXm : Build ((A ∪ layer m) ∪ {xkSig}) {xmSig} 4 :=
              xorG (Or.inr rfl) (Or.inl hmsMem)
            have htot := seqRight (seqRight (seqRight hM012 hCh) hXk) hXm
            have he : xmSig =
                (fun x => srun r col (winExt (lKey r) keyWin) (winExt (lName r col) nameWin)
                  (fun j q => msSig j q x) (m + 1) p) := by
              funext x
              simp only [xmSig, xkSig, chSig, xr, mkMix, F, srun, Int.add_zero, kbit]
            rw [he] at htot
            exact relax htot le_rfl le_rfl (by omega))
        rw [List.length_range] at hb
        refine relax hb le_rfl ?_ le_rfl
        rintro f ⟨idx, hidx, rfl⟩
        exact ⟨idx, List.mem_range.mpr hidx, rfl⟩
      have hcomb := seqRight hprev hstep
      refine relax hcomb le_rfl le_rfl ?_
      have hmul : W_m (m + 1) * 38 ≤ 38 * (6 * r + 1) := by
        have := Nat.mul_le_mul_right 38 hW_le
        omega
      have hstepEq : m * (38 * (6 * r + 1)) + 38 * (6 * r + 1) = (m + 1) * (38 * (6 * r + 1)) := by ring
      omega
  have hfin := hlayer r le_rfl
  refine relax hfin le_rfl ?_ ?_
  · rintro f rfl
    refine ⟨0, by dsimp [W_m]; omega, ?_⟩
    have hp0 : posOf r 0 = 0 := by dsimp [posOf]; simp
    rw [hp0]
  · have h1 : 250 * (r + 1) ^ 2 = 250 * (r * r) + 500 * r + 250 := by ring
    have h2 : r * (38 * (6 * r + 1)) = 228 * (r * r) + 38 * r := by ring
    omega

end CipherSem

section InputDecode

def wiresIn (k r h : ℕ) : ℕ := 2 * r * k + 2 * h

def inputSet (k r h : ℕ) : Set (Sig (wiresIn k r h)) :=
  Set.range (fun i : Fin (wiresIn k r h) => fun x => x i)

def decMasks (k r h : ℕ) (x : Fin (wiresIn k r h) → Bool) (j : ℕ) : Fin (2 ^ k) :=
  if hj : j < 2 * r then
    ⟨bitsVal (fun i => if hi : i < k then x ⟨j * k + i, by
      unfold wiresIn
      have hmul : j * k + k ≤ 2 * r * k := by
        have h1 : j + 1 ≤ 2 * r := hj
        have h2 := Nat.mul_le_mul_right k h1
        rw [Nat.add_one_mul] at h2
        exact h2
      omega⟩ else false) k, bitsVal_lt _ k⟩
  else ⟨0, Nat.two_pow_pos k⟩

def decA (k r h : ℕ) (x : Fin (wiresIn k r h) → Bool) : Fin (2 ^ h) :=
  ⟨bitsVal (fun s => if hs : s < h then x ⟨2 * r * k + s, by unfold wiresIn; omega⟩ else false) h,
    bitsVal_lt _ h⟩

def decB (k r h : ℕ) (x : Fin (wiresIn k r h) → Bool) : Fin (2 ^ h) :=
  ⟨bitsVal (fun s => if hs : s < h then x ⟨2 * r * k + h + s, by unfold wiresIn; omega⟩ else false) h,
    bitsVal_lt _ h⟩

lemma decMasks_testBit (k r h : ℕ) (x : Fin (wiresIn k r h) → Bool)
    {j i : ℕ} (hj : j < 2 * r) (hi : i < k) :
    (decMasks k r h x j).val.testBit i = x ⟨j * k + i, by
      unfold wiresIn
      have hmul : j * k + k ≤ 2 * r * k := by
        have h1 : j + 1 ≤ 2 * r := hj
        have h2 := Nat.mul_le_mul_right k h1
        rw [Nat.add_one_mul] at h2
        exact h2
      omega⟩ := by
  unfold decMasks
  simp only [hj, ↓reduceDIte]
  rw [bitsVal_testBit _ k i hi]
  simp only [hi, ↓reduceDIte]

lemma decA_testBit (k r h : ℕ) (x : Fin (wiresIn k r h) → Bool) {s : ℕ} (hs : s < h) :
    (decA k r h x).val.testBit s = x ⟨2 * r * k + s, by unfold wiresIn; omega⟩ := by
  unfold decA
  rw [bitsVal_testBit _ h s hs]
  simp only [hs, ↓reduceDIte]

lemma decB_testBit (k r h : ℕ) (x : Fin (wiresIn k r h) → Bool) {s : ℕ} (hs : s < h) :
    (decB k r h x).val.testBit s = x ⟨2 * r * k + h + s, by unfold wiresIn; omega⟩ := by
  unfold decB
  rw [bitsVal_testBit _ h s hs]
  simp only [hs, ↓reduceDIte]

lemma decMasks_bit_mem (k r h : ℕ) {j i : ℕ} (hj : j < 2 * r) (hi : i < k) :
    (fun x : Fin (wiresIn k r h) → Bool => (decMasks k r h x j).val.testBit i) ∈ inputSet k r h := by
  refine ⟨⟨j * k + i, by
    unfold wiresIn
    have hmul : j * k + k ≤ 2 * r * k := by
      have h1 : j + 1 ≤ 2 * r := hj
      have h2 := Nat.mul_le_mul_right k h1
      rw [Nat.add_one_mul] at h2
      exact h2
    omega⟩, ?_⟩
  funext x
  exact (decMasks_testBit k r h x hj hi).symm

lemma decA_bit_mem (k r h : ℕ) {s : ℕ} (hs : s < h) :
    (fun x : Fin (wiresIn k r h) → Bool => (decA k r h x).val.testBit s) ∈ inputSet k r h := by
  refine ⟨⟨2 * r * k + s, by unfold wiresIn; omega⟩, ?_⟩
  funext x
  exact (decA_testBit k r h x hs).symm

lemma decB_bit_mem (k r h : ℕ) {s : ℕ} (hs : s < h) :
    (fun x : Fin (wiresIn k r h) → Bool => (decB k r h x).val.testBit s) ∈ inputSet k r h := by
  refine ⟨⟨2 * r * k + h + s, by unfold wiresIn; omega⟩, ?_⟩
  funext x
  exact (decB_testBit k r h x hs).symm

def numOf (k r h : ℕ) (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) (x y : Fin (2 ^ k)) : ℕ :=
  (Finset.univ.filter (fun key : Fin (2 ^ k) =>
    (runN k r masks false key.val x.val >>> (k - h)) = a.val ∧
    (runN k r masks true key.val y.val >>> (k - h)) = b.val)).card

def momentOf (k r h t : ℕ) (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) : ℕ :=
  ∑ x : Fin (2 ^ k), ∑ y : Fin (2 ^ k), (numOf k r h masks a b x y) ^ t

lemma numOf_le (k r h : ℕ) (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) (x y : Fin (2 ^ k)) :
    numOf k r h masks a b x y ≤ 2 ^ k := by
  unfold numOf
  calc (Finset.univ.filter _).card ≤ (Finset.univ : Finset (Fin (2 ^ k))).card := Finset.card_filter_le _ _
    _ = 2 ^ k := by simp

lemma numOf_pow_lt (k r h t : ℕ) (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h))
    (x y : Fin (2 ^ k)) :
    (numOf k r h masks a b x y) ^ t < 2 ^ ((t + 2) * k + 1) := by
  have h1 : (numOf k r h masks a b x y) ^ t ≤ (2 ^ k) ^ t :=
    Nat.pow_le_pow_left (numOf_le k r h masks a b x y) t
  have h2 : (2 ^ k) ^ t = 2 ^ (t * k) := by rw [← pow_mul, Nat.mul_comm]
  have h3 : t * k < (t + 2) * k + 1 := by
    have : (t + 2) * k = t * k + 2 * k := by ring
    omega
  calc (numOf k r h masks a b x y) ^ t ≤ 2 ^ (t * k) := h2 ▸ h1
    _ < 2 ^ ((t + 2) * k + 1) := Nat.pow_lt_pow_right (by omega) h3

lemma momentOf_le (k r h t : ℕ) (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) :
    momentOf k r h t masks a b ≤ 2 ^ ((t + 2) * k) := by
  unfold momentOf
  have hinner : ∀ x : Fin (2 ^ k),
      (∑ y : Fin (2 ^ k), (numOf k r h masks a b x y) ^ t) ≤ 2 ^ k * 2 ^ (t * k) := by
    intro x
    calc (∑ y : Fin (2 ^ k), (numOf k r h masks a b x y) ^ t)
        ≤ ∑ _y : Fin (2 ^ k), 2 ^ (t * k) := by
          apply Finset.sum_le_sum
          intro y _
          have h1 := Nat.pow_le_pow_left (numOf_le k r h masks a b x y) t
          rwa [← pow_mul, Nat.mul_comm] at h1
      _ = 2 ^ k * 2 ^ (t * k) := by simp
  calc (∑ x : Fin (2 ^ k), ∑ y : Fin (2 ^ k), (numOf k r h masks a b x y) ^ t)
      ≤ ∑ _x : Fin (2 ^ k), 2 ^ k * 2 ^ (t * k) := Finset.sum_le_sum (fun x _ => hinner x)
    _ = 2 ^ k * (2 ^ k * 2 ^ (t * k)) := by simp
    _ = 2 ^ ((t + 2) * k) := by
      rw [← pow_add, ← pow_add]
      congr 1; ring

lemma momentOf_lt (k r h t : ℕ) (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) :
    momentOf k r h t masks a b < 2 ^ ((t + 2) * k + 1) :=
  lt_of_le_of_lt (momentOf_le k r h t masks a b)
    (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _))

lemma shr_eq_iff {z k h : ℕ} (hz : z < 2 ^ k) (a : Fin (2 ^ h)) (hh : h ≤ k) :
    z >>> (k - h) = a.val ↔ ∀ s < h, z.testBit (k - h + s) = a.val.testBit s := by
  constructor
  · intro heq s _
    rw [← heq, Nat.testBit_shiftRight]
  · intro hbits
    apply Nat.eq_of_testBit_eq
    intro s
    rw [Nat.testBit_shiftRight]
    by_cases hs : s < h
    · exact hbits s hs
    · have h1 : z.testBit (k - h + s) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by omega) (by omega)))
      have h2 : a.val.testBit s = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [h1, h2]

end InputDecode

section Branch1

lemma fullRunBitsG {k r h : ℕ} (hk : 0 < k) {A : Set (Sig (wiresIn k r h))}
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (hIn : inputSet k r h ⊆ A) (col : Bool) (key name : Fin (2 ^ k)) :
    Build A
      {f | ∃ i < k, f = fun v => (runN k r (decMasks k r h v) col key.val name.val).testBit i}
      (r * (22 * k)) := by
  let layer (m : ℕ) : Set (Sig (wiresIn k r h)) :=
    {f | ∃ i < k, f = fun v => (runPrefix k r (decMasks k r h v) col key.val name.val m).testBit i}
  have hlayer : ∀ m ≤ r, Build A (layer m) (m * (22 * k)) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine relax (idle ?_) le_rfl le_rfl (by simp)
      rintro f ⟨i, _, rfl⟩
      simp only [runPrefix_zero]
      cases (rotN k (if col then 3 else 1) key.val ^^^ name.val).testBit i
      · exact h0
      · exact h1
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      let prevB (i : ℕ) : Sig (wiresIn k r h) :=
        fun v => (runPrefix k r (decMasks k r h v) col key.val name.val m).testBit i
      have hprevMem : ∀ i < k, prevB i ∈ A ∪ layer m := fun i hi => Or.inr ⟨i, hi, rfl⟩
      let gap : ℕ := if col then 2 else 1
      let idxL (i : ℕ) : ℕ := cidx k ((i : ℤ) - (gap : ℤ))
      let idxR (i : ℕ) : ℕ := cidx k ((i : ℤ) + (gap : ℤ))
      let mixS (i : ℕ) : Sig (wiresIn k r h) :=
        xr (xr (prevB i) (prevB (idxL i))) (prevB (idxR i))
      have hmixEq : ∀ i < k, ∀ v, mixS i v =
          (runPrefix k r (decMasks k r h v) col key.val name.val m ^^^
            rotN k gap (runPrefix k r (decMasks k r h v) col key.val name.val m) ^^^
            rotN k (k - gap % k) (runPrefix k r (decMasks k r h v) col key.val name.val m)).testBit i := by
        intro i hi v
        have hlt := runPrefix_lt (r := r) (decMasks k r h v) col key.val name.val m name.isLt
        have hci : cidx k (i : ℤ) = i := cidx_nat hi
        change xor (xor (prevB i v) (prevB (idxL i) v)) (prevB (idxR i) v) = _
        have hL := cbit_rotN (d := gap) hk hlt (i : ℤ)
        have hR := cbit_rotN_neg (d := gap) hk hlt (i : ℤ)
        unfold cbit at hL hR
        rw [hci] at hL hR
        rw [Nat.testBit_xor, Nat.testBit_xor, hL, hR]
      have hMixAll : Build (A ∪ layer m) {f | ∃ i < k, f = mixS i} (8 * k) := by
        have hb := listBuild (List.range k) mixS 8 (fun i hi => by
          have hi' : i < k := List.mem_range.mp hi
          exact seqRight (xorG (hprevMem i hi') (hprevMem (idxL i) (cidx_lt hk _)))
            (xorG (Or.inr rfl) (Or.inl (hprevMem (idxR i) (cidx_lt hk _)))))
        rw [List.length_range, Nat.mul_comm] at hb
        refine relax hb le_rfl ?_ le_rfl
        rintro f ⟨i, hi, rfl⟩
        exact ⟨i, List.mem_range.mpr hi, rfl⟩
      let nextSet := {f | ∃ i < k, f = mixS i}
      let S1 := (A ∪ layer m) ∪ nextSet
      have hNextAll : Build S1 (layer (m + 1)) (14 * k) := by
        have hb := listBuild (List.range k)
          (fun i v => (runPrefix k r (decMasks k r h v) col key.val name.val (m + 1)).testBit i)
          14
          (fun i hi => by
            have hi' : i < k := List.mem_range.mp hi
            have hm0 : mixS i ∈ S1 := Or.inr ⟨i, hi', rfl⟩
            have hm1 : mixS ((i + 1) % k) ∈ S1 :=
              Or.inr ⟨(i + 1) % k, Nat.mod_lt _ hk, rfl⟩
            have hm2 : mixS ((i + 2) % k) ∈ S1 :=
              Or.inr ⟨(i + 2) % k, Nat.mod_lt _ hk, rfl⟩
            let chS : Sig (wiresIn k r h) :=
              fun v => xor (mixS i v) (!(mixS ((i + 1) % k) v) && mixS ((i + 2) % k) v)
            have hCh : Build S1 {chS} 6 := chiGateG hm0 hm1 hm2
            let kbit : Bool := (rotN k (if col then 3 * (m + 1) + 1 else 2 * m) key.val).testBit i
            have hkC : (fun _ : Fin (wiresIn k r h) → Bool => kbit) ∈ S1 := by
              left; left; cases kbit
              · exact h0
              · exact h1
            let xkS : Sig (wiresIn k r h) := xr chS (fun _ => kbit)
            have hXk : Build (S1 ∪ {chS}) {xkS} 4 := xorG (Or.inr rfl) (Or.inl hkC)
            let mIdx : ℕ := if col then r + m else m
            have hmIdx : mIdx < 2 * r := by dsimp [mIdx]; cases col <;> simp <;> omega
            have hmsM : (fun v => (decMasks k r h v mIdx).val.testBit i) ∈ S1 :=
              Or.inl (Or.inl (hIn (decMasks_bit_mem k r h hmIdx hi')))
            let xmS : Sig (wiresIn k r h) := xr xkS (fun v => (decMasks k r h v mIdx).val.testBit i)
            have hXm : Build (S1 ∪ {xkS}) {xmS} 4 := xorG (Or.inr rfl) (Or.inl hmsM)
            have htot := seqRight (seqRight hCh hXk) hXm
            have he : xmS = (fun v => (runPrefix k r (decMasks k r h v) col key.val name.val (m + 1)).testBit i) := by
              funext v
              rw [runPrefix_succ]
              unfold runStep
              simp only [xmS, xkS, chS, xr, mIdx, kbit]
              rw [Nat.testBit_xor, Nat.testBit_xor, chiN_testBit hi',
                ← hmixEq i hi' v, ← hmixEq ((i + 1) % k) (Nat.mod_lt _ hk) v,
                ← hmixEq ((i + 2) % k) (Nat.mod_lt _ hk) v]
            rw [he] at htot
            exact relax htot le_rfl le_rfl (by omega))
        rw [List.length_range, Nat.mul_comm] at hb
        refine relax hb le_rfl ?_ le_rfl
        rintro f ⟨i, hi, rfl⟩
        exact ⟨i, List.mem_range.mpr hi, rfl⟩
      refine relax (seqRight hprev (seqRight hMixAll hNextAll)) le_rfl le_rfl ?_
      have : m * (22 * k) + (8 * k + 14 * k) = (m + 1) * (22 * k) := by ring
      omega
  exact hlayer r le_rfl

lemma fullHitG {k r h : ℕ} (hk : 0 < k) (hh : h ≤ k) {A : Set (Sig (wiresIn k r h))}
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (hIn : inputSet k r h ⊆ A) (col : Bool) (key name : Fin (2 ^ k)) :
    Build A
      {fun v => decide ((runN k r (decMasks k r h v) col key.val name.val >>> (k - h)) =
        (if col then decB k r h v else decA k r h v).val)}
      (28 * (r + 1) * k) := by
  have hbits := fullRunBitsG hk h0 h1 hIn col key name
  let BRun := {f : Sig (wiresIn k r h) | ∃ i < k,
    f = fun v => (runN k r (decMasks k r h v) col key.val name.val).testBit i}
  let eqS (s : ℕ) : Sig (wiresIn k r h) :=
    fun v => decide ((runN k r (decMasks k r h v) col key.val name.val).testBit (k - h + s) =
      (if col then decB k r h v else decA k r h v).val.testBit s)
  have hEqs : Build (A ∪ BRun) {f | ∃ s ∈ List.range h, f = eqS s} (5 * h) := by
    have hb := listBuild (List.range h) eqS 5 (fun s hs => by
      have hs' : s < h := List.mem_range.mp hs
      have hrunM : (fun v => (runN k r (decMasks k r h v) col key.val name.val).testBit (k - h + s)) ∈ A ∪ BRun :=
        Or.inr ⟨k - h + s, by omega, rfl⟩
      have htargM : (fun v => (if col then decB k r h v else decA k r h v).val.testBit s) ∈ A ∪ BRun := by
        left; cases col
        · exact hIn (decA_bit_mem k r h hs')
        · exact hIn (decB_bit_mem k r h hs')
      exact xnorG hrunM htargM)
    rw [List.length_range, Nat.mul_comm] at hb
    exact hb
  have hAll : Build ((A ∪ BRun) ∪ {f | ∃ s ∈ List.range h, f = eqS s})
      {fun v => (List.range h).all (fun s => eqS s v)} h := by
    have hmem : ∀ s ∈ List.range h,
        eqS s ∈ (A ∪ BRun) ∪ {f | ∃ s ∈ List.range h, f = eqS s} :=
      fun s hs => Or.inr ⟨s, hs, rfl⟩
    have hb := andListG (A := (A ∪ BRun) ∪ {f | ∃ s ∈ List.range h, f = eqS s})
      (List.range h) eqS (Or.inl (Or.inl h1)) hmem
    rw [List.length_range] at hb
    exact hb
  have hcomb := seqRight hbits (seqRight hEqs hAll)
  have he : (fun v => (List.range h).all (fun s => eqS s v)) =
      (fun v => decide ((runN k r (decMasks k r h v) col key.val name.val >>> (k - h)) =
        (if col then decB k r h v else decA k r h v).val)) := by
    funext v
    apply Bool.eq_iff_iff.mpr
    have hlt : runN k r (decMasks k r h v) col key.val name.val < 2 ^ k :=
      runPrefix_lt (r := r) (decMasks k r h v) col key.val name.val r name.isLt
    rw [List.all_eq_true, decide_eq_true_eq, shr_eq_iff hlt _ hh]
    constructor
    · intro hall s hs
      have := hall s (List.mem_range.mpr hs)
      simpa [eqS] using this
    · intro hall s hs
      simpa [eqS] using hall s (List.mem_range.mp hs)
  rw [he] at hcomb
  refine relax hcomb le_rfl le_rfl ?_
  have h1 : r * (22 * k) + (5 * h + h) ≤ 28 * (r + 1) * k := by
    have : 28 * (r + 1) * k = 28 * (r * k) + 28 * k := by ring
    have : r * (22 * k) = 22 * (r * k) := by ring
    omega
  exact h1

lemma sum_flatMap_nat {α : Type*} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

lemma directMomentG (k r h t : ℕ) (hh0 : 0 < h) (hh : h ≤ k) (ht : 0 < t) :
    let W := (t + 2) * k + 1
    Build (inputSet k r h)
      (wordBits W (fun v => momentOf k r h t (decMasks k r h v) (decA k r h v) (decB k r h v)))
      (1048576 * ((k + 1) * (r + 1) * (t + 2)) ^ 4 * 2 ^ (3 * k)) := by
  intro W
  have hk : 0 < k := by omega
  have hW1 : 1 ≤ W := by dsimp [W]; omega
  let A0 := inputSet k r h
  have hC0 : Build A0 {fun _ => false} 1 := constG false
  have hC1 : Build (A0 ∪ {fun _ => false}) {fun _ => true} 1 := constG true
  have hConsts := seq hC0 hC1
  let AC := A0 ∪ ({fun _ => false} ∪ {fun _ => true})
  have h0AC : (fun _ : Fin (wiresIn k r h) → Bool => false) ∈ AC := Or.inr (Or.inl rfl)
  have h1AC : (fun _ : Fin (wiresIn k r h) → Bool => true) ∈ AC := Or.inr (Or.inr rfl)
  have hInAC : inputSet k r h ⊆ AC := Set.subset_union_left
  let rowHit (x key : Fin (2 ^ k)) : Sig (wiresIn k r h) :=
    fun v => decide ((runN k r (decMasks k r h v) false key.val x.val >>> (k - h)) = (decA k r h v).val)
  let colHit (y key : Fin (2 ^ k)) : Sig (wiresIn k r h) :=
    fun v => decide ((runN k r (decMasks k r h v) true key.val y.val >>> (k - h)) = (decB k r h v).val)
  let allPairs : List (Fin (2 ^ k) × Fin (2 ^ k)) :=
    (List.finRange (2 ^ k)).flatMap (fun a => (List.finRange (2 ^ k)).map (fun b => (a, b)))
  have hallPairs_len : allPairs.length = 2 ^ (2 * k) := by
    dsimp [allPairs]
    rw [List.length_flatMap]
    simp only [List.length_map, List.length_finRange, List.map_const', List.sum_replicate,
      smul_eq_mul, ← pow_add, show k + k = 2 * k by omega]
  have hallPairs_mem : ∀ p : Fin (2 ^ k) × Fin (2 ^ k), p ∈ allPairs := by
    intro ⟨a, b⟩
    dsimp [allPairs]
    exact List.mem_flatMap.mpr ⟨a, List.mem_finRange a, List.mem_map.mpr ⟨b, List.mem_finRange b, rfl⟩⟩
  let SRow := {f : Sig (wiresIn k r h) | ∃ p ∈ allPairs, f = rowHit p.1 p.2}
  let SCol := {f : Sig (wiresIn k r h) | ∃ p ∈ allPairs, f = colHit p.1 p.2}
  have hRowAll : Build AC SRow (2 ^ (2 * k) * (28 * (r + 1) * k)) := by
    have hb := listBuild (A := AC) allPairs (fun p => rowHit p.1 p.2) (28 * (r + 1) * k)
      (fun p _ => fullHitG hk hh h0AC h1AC hInAC false p.2 p.1)
    rwa [hallPairs_len] at hb
  have hColAll : Build (AC ∪ SRow) SCol (2 ^ (2 * k) * (28 * (r + 1) * k)) := by
    have hb := listBuild (A := AC ∪ SRow) allPairs (fun p => colHit p.1 p.2) (28 * (r + 1) * k)
      (fun p _ => fullHitG hk hh (Or.inl h0AC) (Or.inl h1AC) (hInAC.trans Set.subset_union_left) true p.2 p.1)
    rwa [hallPairs_len] at hb
  let ARC := AC ∪ (SRow ∪ SCol)
  let powSig (p : Fin (2 ^ k) × Fin (2 ^ k)) : NatSig (wiresIn k r h) :=
    fun v => (numOf k r h (decMasks k r h v) (decA k r h v) (decB k r h v) p.1 p.2) ^ t
  let perPairCost := 2 ^ k + 2 ^ k * (12 * (k + 1)) + t * (13 * (k + 1) * W)
  have hPowAll : Build ARC {g | ∃ p ∈ allPairs, g ∈ wordBits W (powSig p)}
      (2 ^ (2 * k) * perPairCost) := by
    have hb := listBuildSets (A := ARC) allPairs (fun p => wordBits W (powSig p)) perPairCost (fun p _ => by
      let x := p.1
      let y := p.2
      let SBoth := {f : Sig (wiresIn k r h) | ∃ key ∈ List.finRange (2 ^ k), f = an (rowHit x key) (colHit y key)}
      have hBoth : Build ARC SBoth (2 ^ k) := by
        have hb0 := listBuild (A := ARC) (List.finRange (2 ^ k)) (fun key => an (rowHit x key) (colHit y key)) 1
          (fun key _ => andG (A := ARC)
            (Or.inr (Or.inl ⟨(x, key), hallPairs_mem (x, key), rfl⟩))
            (Or.inr (Or.inr ⟨(y, key), hallPairs_mem (y, key), rfl⟩)))
        rwa [List.length_finRange, Nat.mul_one] at hb0
      let numS : NatSig (wiresIn k r h) :=
        fun v => numOf k r h (decMasks k r h v) (decA k r h v) (decB k r h v) x y
      have hnumEq : ∀ v, numS v =
          ((List.finRange (2 ^ k)).map (fun key => (an (rowHit x key) (colHit y key) v).toNat)).sum := by
        intro v
        dsimp [numS, numOf, an, rowHit, colHit]
        have h1 : ((List.finRange (2 ^ k)).map (fun key =>
            (decide ((runN k r (decMasks k r h v) false key.val x.val >>> (k - h)) = (decA k r h v).val) &&
             decide ((runN k r (decMasks k r h v) true key.val y.val >>> (k - h)) = (decB k r h v).val)).toNat)).sum =
            ∑ key : Fin (2 ^ k),
              if (runN k r (decMasks k r h v) false key.val x.val >>> (k - h)) = (decA k r h v).val ∧
                 (runN k r (decMasks k r h v) true key.val y.val >>> (k - h)) = (decB k r h v).val
              then 1 else 0 := by
          rw [← Fin.sum_univ_def]
          congr 1; funext key
          by_cases h1' : (runN k r (decMasks k r h v) false key.val x.val >>> (k - h)) = (decA k r h v).val <;>
            by_cases h2' : (runN k r (decMasks k r h v) true key.val y.val >>> (k - h)) = (decB k r h v).val <;>
            simp [h1', h2']
        rw [h1, Finset.card_filter]
      have hNum : Build (ARC ∪ SBoth) (wordBits (k + 1) numS) (2 ^ k * (12 * (k + 1))) := by
        have hsubB : ∀ key ∈ List.finRange (2 ^ k),
            wordBits (k + 1) (fun v => (an (rowHit x key) (colHit y key) v).toNat) ⊆ ARC ∪ SBoth := by
          intro key hkey g hg
          rcases hg with ⟨i, _, rfl⟩
          cases i with
          | zero =>
            have he : (fun v => (an (rowHit x key) (colHit y key) v).toNat.testBit 0) =
                an (rowHit x key) (colHit y key) := by
              funext v; cases an (rowHit x key) (colHit y key) v <;> rfl
            rw [he]; exact Or.inr ⟨key, hkey, rfl⟩
          | succ i =>
            have he : (fun v => (an (rowHit x key) (colHit y key) v).toNat.testBit (i + 1)) =
                (fun _ => false) := by
              funext v
              cases an (rowHit x key) (colHit y key) v
              · simp
              · exact Nat.testBit_lt_two_pow (by
                  have : 2 ≤ 2 ^ (i + 1) := by
                    calc 2 = 2 ^ 1 := rfl
                      _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by omega) (by omega)
                  simp only [Bool.toNat_true]; omega)
            rw [he]; exact Or.inl (Or.inl h0AC)
        have hb1 := sumListNatG (A := ARC ∪ SBoth) (k + 1) (List.finRange (2 ^ k))
          (fun key v => (an (rowHit x key) (colHit y key) v).toNat)
          (Or.inl (Or.inl h0AC)) (Or.inl (Or.inl h1AC)) hsubB
          (fun v => by
            rw [← hnumEq v]
            exact lt_of_le_of_lt (numOf_le k r h _ _ _ x y)
              (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self k)))
        rw [List.length_finRange] at hb1
        have he : (fun v => ((List.finRange (2 ^ k)).map (fun key =>
            (an (rowHit x key) (colHit y key) v).toNat)).sum) = numS := by
          funext v; exact (hnumEq v).symm
        rwa [he] at hb1
      have hPow : Build ((ARC ∪ SBoth) ∪ wordBits (k + 1) numS)
          (wordBits W (powSig p)) (t * (13 * (k + 1) * W)) := by
        exact powNatG W (k + 1) numS hW1
          (fun v => lt_of_le_of_lt (numOf_le k r h _ _ _ x y)
            (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self k)))
          Set.subset_union_right
          (Or.inl (Or.inl (Or.inl h0AC)))
          (Or.inl (Or.inl (Or.inl h1AC)))
          t (fun v => numOf_pow_lt k r h t _ _ _ x y)
      exact relax (seqRight hBoth (seqRight hNum hPow)) le_rfl le_rfl (by dsimp [perPairCost]; omega))
    rwa [hallPairs_len] at hb
  have hSumAll : Build (ARC ∪ {g | ∃ p ∈ allPairs, g ∈ wordBits W (powSig p)})
      (wordBits W (fun v => momentOf k r h t (decMasks k r h v) (decA k r h v) (decB k r h v)))
      (2 ^ (2 * k) * (12 * W)) := by
    have hmomEq : ∀ v, momentOf k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) =
        (allPairs.map (fun p => powSig p v)).sum := by
      intro v
      dsimp [momentOf, allPairs, powSig]
      rw [List.map_flatMap, sum_flatMap_nat]
      have h1 : ∀ x : Fin (2 ^ k),
          (((List.finRange (2 ^ k)).map (fun b => (x, b))).map
            (fun p => (numOf k r h (decMasks k r h v) (decA k r h v) (decB k r h v) p.1 p.2) ^ t)).sum =
          ∑ y : Fin (2 ^ k), (numOf k r h (decMasks k r h v) (decA k r h v) (decB k r h v) x y) ^ t := by
        intro x
        rw [List.map_map, ← Fin.sum_univ_def]
        rfl
      have h2 : ((List.finRange (2 ^ k)).map (fun x =>
          (((List.finRange (2 ^ k)).map (fun b => (x, b))).map
            (fun p => (numOf k r h (decMasks k r h v) (decA k r h v) (decB k r h v) p.1 p.2) ^ t)).sum)).sum =
          ∑ x : Fin (2 ^ k), ∑ y : Fin (2 ^ k),
            (numOf k r h (decMasks k r h v) (decA k r h v) (decB k r h v) x y) ^ t := by
        rw [← Fin.sum_univ_def]
        congr 1; funext x; exact h1 x
      exact h2.symm
    have hsub : ∀ p ∈ allPairs,
        wordBits W (powSig p) ⊆ ARC ∪ {g | ∃ p ∈ allPairs, g ∈ wordBits W (powSig p)} :=
      fun p hp g hg => Or.inr ⟨p, hp, hg⟩
    have hb2 := sumListNatG W allPairs powSig
      (Or.inl (Or.inl h0AC)) (Or.inl (Or.inl h1AC)) hsub
      (fun v => by rw [← hmomEq v]; exact momentOf_lt k r h t _ _ _)
    rw [hallPairs_len] at hb2
    have he : (fun v => (allPairs.map (fun p => powSig p v)).sum) =
        (fun v => momentOf k r h t (decMasks k r h v) (decA k r h v) (decB k r h v)) := by
      funext v; exact (hmomEq v).symm
    rwa [he] at hb2
  have hfull := seqRight hConsts (seqRight (seq hRowAll hColAll) (seqRight hPowAll hSumAll))
  refine relax hfull le_rfl le_rfl ?_
  have h2k_le : 2 ^ (2 * k) ≤ 2 ^ (3 * k) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2k_mul : 2 ^ (2 * k) * 2 ^ k = 2 ^ (3 * k) := by
    rw [← pow_add]; congr 1; omega
  have hW_le : W ≤ (k + 1) * (t + 2) := by
    dsimp [W]
    have : (k + 1) * (t + 2) = (t + 2) * k + t + 2 := by ring
    omega
  set M := (k + 1) * (r + 1) * (t + 2)
  have hM1 : 1 ≤ M := by
    dsimp [M]
    exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos r)) (by omega)
  have hk_le_M : k + 1 ≤ M := by
    dsimp [M]
    calc k + 1 = (k + 1) * 1 * 1 := by ring
      _ ≤ (k + 1) * (r + 1) * (t + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hrk_le_M : (r + 1) * k ≤ M := by
    dsimp [M]
    calc (r + 1) * k ≤ (k + 1) * (r + 1) * 1 := by
          rw [Nat.mul_one, Nat.mul_comm (k + 1)]; exact Nat.mul_le_mul_left _ (by omega)
      _ ≤ (k + 1) * (r + 1) * (t + 2) := Nat.mul_le_mul_left _ (by omega)
  have hW_le_M : W ≤ M := by
    calc W ≤ (k + 1) * (t + 2) := hW_le
      _ = (k + 1) * 1 * (t + 2) := by ring
      _ ≤ (k + 1) * (r + 1) * (t + 2) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have ht_le_M : t ≤ M := by
    dsimp [M]
    calc t ≤ 1 * 1 * (t + 2) := by omega
      _ ≤ (k + 1) * (r + 1) * (t + 2) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
  have hStep1 : 2 ^ (2 * k) * perPairCost ≤ (13 * M + 13 * M ^ 3) * 2 ^ (3 * k) := by
    dsimp [perPairCost]
    have hA : 2 ^ (2 * k) * (2 ^ k + 2 ^ k * (12 * (k + 1))) =
        (1 + 12 * (k + 1)) * 2 ^ (3 * k) := by
      calc 2 ^ (2 * k) * (2 ^ k + 2 ^ k * (12 * (k + 1)))
          = (2 ^ (2 * k) * 2 ^ k) * (1 + 12 * (k + 1)) := by ring
        _ = (1 + 12 * (k + 1)) * 2 ^ (3 * k) := by rw [h2k_mul, Nat.mul_comm]
    have hB : 1 + 12 * (k + 1) ≤ 13 * M := by omega
    have hC : t * (13 * (k + 1) * W) ≤ 13 * M ^ 3 := by
      have h1 : t * (13 * (k + 1) * W) = 13 * (t * (k + 1) * W) := by ring
      have h2 : t * (k + 1) * W ≤ M * M * M :=
        Nat.mul_le_mul (Nat.mul_le_mul ht_le_M hk_le_M) hW_le_M
      have h3 : M * M * M = M ^ 3 := by ring
      omega
    have hD : 2 ^ (2 * k) * (t * (13 * (k + 1) * W)) ≤ 13 * M ^ 3 * 2 ^ (3 * k) := by
      calc 2 ^ (2 * k) * (t * (13 * (k + 1) * W))
          ≤ 2 ^ (3 * k) * (13 * M ^ 3) := Nat.mul_le_mul h2k_le hC
        _ = 13 * M ^ 3 * 2 ^ (3 * k) := Nat.mul_comm _ _
    have hE : 2 ^ (2 * k) * (2 ^ k + 2 ^ k * (12 * (k + 1)) + t * (13 * (k + 1) * W)) =
        2 ^ (2 * k) * (2 ^ k + 2 ^ k * (12 * (k + 1))) + 2 ^ (2 * k) * (t * (13 * (k + 1) * W)) := by
      ring
    have hF : (1 + 12 * (k + 1)) * 2 ^ (3 * k) ≤ 13 * M * 2 ^ (3 * k) :=
      Nat.mul_le_mul_right _ hB
    have hG : 13 * M * 2 ^ (3 * k) + 13 * M ^ 3 * 2 ^ (3 * k) =
        (13 * M + 13 * M ^ 3) * 2 ^ (3 * k) := by ring
    omega
  have hRowB : 2 ^ (2 * k) * (28 * (r + 1) * k) ≤ 28 * M * 2 ^ (3 * k) := by
    calc 2 ^ (2 * k) * (28 * (r + 1) * k)
        = (28 * ((r + 1) * k)) * 2 ^ (2 * k) := by ring
      _ ≤ (28 * M) * 2 ^ (3 * k) := Nat.mul_le_mul (Nat.mul_le_mul_left 28 hrk_le_M) h2k_le
  have hSumB : 2 ^ (2 * k) * (12 * W) ≤ 12 * M * 2 ^ (3 * k) := by
    calc 2 ^ (2 * k) * (12 * W)
        = (12 * W) * 2 ^ (2 * k) := by ring
      _ ≤ (12 * M) * 2 ^ (3 * k) := Nat.mul_le_mul (Nat.mul_le_mul_left 12 hW_le_M) h2k_le
  have hM1_le_M4 : M ≤ M ^ 4 := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by omega)
  have hM3_le_M4 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by omega)
  have h2_le : 2 ≤ 2 * (M ^ 4 * 2 ^ (3 * k)) := by
    have h1 : 1 ≤ M ^ 4 := Nat.one_le_pow 4 M hM1
    have h2 : 1 ≤ 2 ^ (3 * k) := Nat.one_le_pow (3 * k) 2 (by omega)
    have h3 : 1 ≤ M ^ 4 * 2 ^ (3 * k) := Nat.mul_pos h1 h2
    omega
  have hA : 28 * M + 28 * M + 13 * M + 13 * M ^ 3 + 12 * M ≤ 94 * M ^ 4 := by omega
  have hB : (28 * M + 28 * M + 13 * M + 13 * M ^ 3 + 12 * M) * 2 ^ (3 * k) ≤
      94 * (M ^ 4 * 2 ^ (3 * k)) := by
    calc (28 * M + 28 * M + 13 * M + 13 * M ^ 3 + 12 * M) * 2 ^ (3 * k)
        ≤ (94 * M ^ 4) * 2 ^ (3 * k) := Nat.mul_le_mul_right _ hA
      _ = 94 * (M ^ 4 * 2 ^ (3 * k)) := by ring
  have hC : 28 * M * 2 ^ (3 * k) + 28 * M * 2 ^ (3 * k) +
      ((13 * M + 13 * M ^ 3) * 2 ^ (3 * k) + 12 * M * 2 ^ (3 * k)) =
      (28 * M + 28 * M + 13 * M + 13 * M ^ 3 + 12 * M) * 2 ^ (3 * k) := by ring
  have hD : 1 + 1 + (2 ^ (2 * k) * (28 * (r + 1) * k) + 2 ^ (2 * k) * (28 * (r + 1) * k) +
      (2 ^ (2 * k) * perPairCost + 2 ^ (2 * k) * (12 * W))) ≤ 1048576 * M ^ 4 * 2 ^ (3 * k) := by
    have hE : 1048576 * M ^ 4 * 2 ^ (3 * k) = 1048576 * (M ^ 4 * 2 ^ (3 * k)) := by ring
    omega
  exact hD

end Branch1

section PinHist

noncomputable section
open Classical

def seam (k h b : ℕ) : ℕ := min k (h + b - k)

def AVal (k r h : ℕ) : ℕ := 2 ^ (bKey r + seam k h (bKey r) + 1)

def scanVal (k r h t : ℕ) : ℕ :=
  2 ^ (10 * r + seam k h (4 * r) + seam k h (6 * r) + 2) * Nat.choose (t + AVal k r h - 1) t

abbrev Trace (k h b : ℕ) := (Fin (seam k h b) → Bool) × (Fin (h + b) → Bool)

def pinOK (k h b : ℕ) (tr : Trace k h b) : Bool :=
  (List.finRange (h + b)).all (fun i =>
    if hi : i.val % k < seam k h b then decide (tr.2 i = tr.1 ⟨i.val % k, hi⟩) else true)

lemma pinOK_iff (k h b : ℕ) (tr : Trace k h b) :
    pinOK k h b tr = true ↔
      ∀ i : Fin (h + b), ∀ hi : i.val % k < seam k h b, tr.2 i = tr.1 ⟨i.val % k, hi⟩ := by
  unfold pinOK
  rw [List.all_eq_true]
  constructor
  · intro hall i hi
    have h1 := hall i (List.mem_finRange i)
    simp only [hi, ↓reduceDIte, decide_eq_true_eq] at h1
    exact h1
  · intro hall i _
    by_cases hi : i.val % k < seam k h b
    · simp only [hi, ↓reduceDIte, decide_eq_true_eq]
      exact hall i hi
    · simp only [hi, ↓reduceDIte]

def extractTrace (k h b : ℕ) (q0 : ℤ) (v : Fin (2 ^ k)) : Trace k h b :=
  (fun j => cbit k v.val (q0 + (j.val : ℤ)), fun i => cbit k v.val (q0 + (i.val : ℤ)))

lemma pinOK_extractTrace {k h b : ℕ} (_hk : 0 < k) (q0 : ℤ) (v : Fin (2 ^ k)) :
    pinOK k h b (extractTrace k h b q0 v) = true := by
  rw [pinOK_iff]
  intro i hi
  dsimp [extractTrace, cbit]
  congr 1
  apply cidx_congr
  rw [Int.add_emod q0, Int.add_emod q0, Int.emod_emod]

def toShiftVec {k : ℕ} (q0 : ℤ) (v : Fin (2 ^ k)) : Fin k → Bool :=
  fun r => cbit k v.val (q0 + (r.val : ℤ))

def fromShiftVec {k : ℕ} (hk : 0 < k) (q0 : ℤ) (f : Fin k → Bool) : Fin (2 ^ k) :=
  ⟨bitsVal (fun i => f ⟨cidx k ((i : ℤ) - q0), cidx_lt hk _⟩) k, bitsVal_lt _ k⟩

lemma toShiftVec_fromShiftVec {k : ℕ} (hk : 0 < k) (q0 : ℤ) (f : Fin k → Bool) :
    toShiftVec q0 (fromShiftVec hk q0 f) = f := by
  funext r
  unfold toShiftVec fromShiftVec cbit
  rw [bitsVal_testBit _ k _ (cidx_lt hk _)]
  congr 1
  apply Fin.ext
  have hk0 : (0 : ℤ) < (k : ℤ) := by omega
  have h1 : (cidx k (q0 + (r.val : ℤ)) : ℤ) = (q0 + (r.val : ℤ)) % (k : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hk0))
  have h2 : (((cidx k (q0 + (r.val : ℤ)) : ℕ) : ℤ) - q0) % (k : ℤ) = (r.val : ℤ) := by
    rw [h1, Int.sub_emod, Int.emod_emod, ← Int.sub_emod]
    have he : q0 + (r.val : ℤ) - q0 = (r.val : ℤ) := by ring
    rw [he, Int.emod_eq_of_lt (by omega) (by omega)]
  have h3 : cidx k (((cidx k (q0 + (r.val : ℤ)) : ℕ) : ℤ) - q0) = r.val := by
    show ((((cidx k (q0 + (r.val : ℤ)) : ℕ) : ℤ) - q0) % (k : ℤ)).toNat = r.val
    rw [h2]; rfl
  exact h3

lemma fromShiftVec_toShiftVec {k : ℕ} (hk : 0 < k) (q0 : ℤ) (v : Fin (2 ^ k)) :
    fromShiftVec hk q0 (toShiftVec q0 v) = v := by
  apply Fin.ext
  unfold fromShiftVec toShiftVec cbit
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · rw [bitsVal_testBit _ k i hi]
    congr 1
    have hk0 : (0 : ℤ) < (k : ℤ) := by omega
    have h1 : (cidx k ((i : ℤ) - q0) : ℤ) = ((i : ℤ) - q0) % (k : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hk0))
    have h2 : (q0 + ((cidx k ((i : ℤ) - q0) : ℕ) : ℤ)) % (k : ℤ) = (i : ℤ) := by
      rw [h1, Int.add_emod, Int.emod_emod, ← Int.add_emod]
      have he : q0 + ((i : ℤ) - q0) = (i : ℤ) := by ring
      rw [he, Int.emod_eq_of_lt (by omega) (by omega)]
    have h3 : cidx k (q0 + ((cidx k ((i : ℤ) - q0) : ℕ) : ℤ)) = i := by
      show ((q0 + ((cidx k ((i : ℤ) - q0) : ℕ) : ℤ)) % (k : ℤ)).toNat = i
      rw [h2]; rfl
    exact h3
  · have h1 := Nat.testBit_lt_two_pow
      ((bitsVal_lt (fun j => v.val.testBit (cidx k (q0 + (cidx k ((j : ℤ) - q0) : ℤ)))) k).trans_le
        (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hi)))
    have h2 := Nat.testBit_lt_two_pow
      (v.isLt.trans_le (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hi)))
    rw [h1, h2]

lemma card_vec_agree_prefix (k m : ℕ) (hm : m ≤ k) (ref : Fin k → Bool) :
    (Finset.univ.filter (fun f : Fin k → Bool => ∀ r : Fin k, r.val < m → f r = ref r)).card =
      2 ^ (k - m) := by
  let S := Finset.univ.filter (fun f : Fin k → Bool => ∀ r : Fin k, r.val < m → f r = ref r)
  have hbij : S.card = (Finset.univ : Finset (Fin (k - m) → Bool)).card := by
    apply Finset.card_nbij'
      (fun f (t : Fin (k - m)) => f ⟨m + t.val, by omega⟩)
      (fun g (r : Fin k) => if hr : r.val < m then ref r else g ⟨r.val - m, by omega⟩)
    · intro _ _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro g _
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      intro r hr
      simp only [hr, ↓reduceDIte]
    · intro f hf
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      funext r
      by_cases hr : r.val < m
      · simp only [hr, ↓reduceDIte]; exact (hf r hr).symm
      · simp only [hr, ↓reduceDIte]
        congr 1; apply Fin.ext; dsimp; omega
    · intro g _
      funext t
      have hnot : ¬ (m + t.val < m) := by omega
      simp only [hnot, ↓reduceDIte]
      congr 1; apply Fin.ext; dsimp; omega
  rw [hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

lemma card_fiber_extractTrace {k h b : ℕ} (hh0 : 0 < h) (hh : h ≤ k) (q0 : ℤ)
    (tr : Trace k h b) (hok : pinOK k h b tr = true) :
    (Finset.univ.filter (fun v : Fin (2 ^ k) => extractTrace k h b q0 v = tr)).card =
      2 ^ (k - (h + b)) := by
  have hk : 0 < k := by omega
  have hpin := (pinOK_iff k h b tr).mp hok
  let m := min k (h + b)
  have hm_le : m ≤ k := min_le_left _ _
  let ref : Fin k → Bool := fun r => if hr : r.val < h + b then tr.2 ⟨r.val, hr⟩ else false
  have hbij : (Finset.univ.filter (fun v : Fin (2 ^ k) => extractTrace k h b q0 v = tr)).card =
      (Finset.univ.filter (fun f : Fin k → Bool => ∀ r : Fin k, r.val < m → f r = ref r)).card := by
    apply Finset.card_nbij' (toShiftVec q0) (fromShiftVec hk q0)
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      intro r hr
      have hrhb : r.val < h + b := lt_of_lt_of_le hr (min_le_right _ _)
      dsimp [ref, toShiftVec]
      simp only [hrhb, ↓reduceDIte]
      have h2 := congrFun (congrArg Prod.snd hv) ⟨r.val, hrhb⟩
      exact h2
    · intro f hf
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      have htv : toShiftVec q0 (fromShiftVec hk q0 f) = f := toShiftVec_fromShiftVec hk q0 f
      apply Prod.ext
      · funext j
        have hj_lt_m : j.val < m := by
          have hj := j.isLt
          dsimp [m, seam] at *
          omega
        have hj_lt_k : j.val < k := lt_of_lt_of_le hj_lt_m hm_le
        have hj_lt_hb : j.val < h + b := lt_of_lt_of_le hj_lt_m (min_le_right _ _)
        have hstep1 : (extractTrace k h b q0 (fromShiftVec hk q0 f)).1 j =
            f ⟨j.val, hj_lt_k⟩ := by
          have := congrFun htv ⟨j.val, hj_lt_k⟩
          exact this
        rw [hstep1, hf ⟨j.val, hj_lt_k⟩ hj_lt_m]
        dsimp [ref]
        simp only [hj_lt_hb, ↓reduceDIte]
        have hmod : j.val % k = j.val := Nat.mod_eq_of_lt hj_lt_k
        have hp := hpin ⟨j.val, hj_lt_hb⟩ (by simp [hmod])
        simpa [hmod] using hp
      · funext i
        have him : i.val % k < k := Nat.mod_lt _ hk
        have hstep1 : (extractTrace k h b q0 (fromShiftVec hk q0 f)).2 i =
            f ⟨i.val % k, him⟩ := by
          have h1 := congrFun htv ⟨i.val % k, him⟩
          rw [← h1]
          dsimp [extractTrace, toShiftVec, cbit]
          congr 1
          apply cidx_congr
          rw [Int.add_emod q0, Int.add_emod q0, Int.emod_emod]
        rw [hstep1]
        by_cases hik : i.val < k
        · have hmod : i.val % k = i.val := Nat.mod_eq_of_lt hik
          have hm' : i.val < m := lt_min hik i.isLt
          have hfeq := hf ⟨i.val % k, him⟩ (by simpa [hmod] using hm')
          rw [hfeq]
          dsimp [ref]
          have hlt2 : i.val % k < h + b := by omega
          simp only [hlt2, ↓reduceDIte]
          exact congrArg tr.2 (Fin.ext hmod)
        · have hse : i.val % k < seam k h b := by
            dsimp [seam]
            by_cases h2k : h + b < 2 * k
            · have hi2 : i.val < 2 * k := lt_of_lt_of_le i.isLt (Nat.le_of_lt h2k)
              have hmod : i.val % k = i.val - k := by
                rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
              omega
            · omega
          have hm' : i.val % k < m := by dsimp [m]; omega
          have hfeq := hf ⟨i.val % k, him⟩ hm'
          rw [hfeq]
          dsimp [ref]
          have hlt2 : i.val % k < h + b := by omega
          simp only [hlt2, ↓reduceDIte]
          have hp1 := hpin ⟨i.val % k, hlt2⟩ (by simpa [Nat.mod_eq_of_lt him] using hse)
          have hp2 := hpin i hse
          rw [hp2]
          simpa [Nat.mod_eq_of_lt him] using hp1
    · intro v _; exact fromShiftVec_toShiftVec hk q0 v
    · intro f _; exact toShiftVec_fromShiftVec hk q0 f
  rw [hbij, card_vec_agree_prefix k m hm_le ref]
  congr 1
  dsimp [m]; omega

lemma card_pinOK_le {k h b : ℕ} (hh0 : 0 < h) (hh : h ≤ k) :
    (Finset.univ.filter (fun tr : Trace k h b => pinOK k h b tr = true)).card ≤ 2 ^ k := by
  have hk : 0 < k := by omega
  have hsum : ∑ tr ∈ Finset.univ.filter (fun tr : Trace k h b => pinOK k h b tr = true),
      (Finset.univ.filter (fun v : Fin (2 ^ k) => extractTrace k h b 0 v = tr)).card = 2 ^ k := by
    have h1 := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin (2 ^ k))))
      (t := Finset.univ.filter (fun tr : Trace k h b => pinOK k h b tr = true))
      (g := extractTrace k h b 0) (f := fun _ => (1 : ℕ))
      (fun v _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, pinOK_extractTrace hk 0 v⟩)
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  have hconst : ∑ tr ∈ Finset.univ.filter (fun tr : Trace k h b => pinOK k h b tr = true),
      (Finset.univ.filter (fun v : Fin (2 ^ k) => extractTrace k h b 0 v = tr)).card =
      (Finset.univ.filter (fun tr : Trace k h b => pinOK k h b tr = true)).card * 2 ^ (k - (h + b)) := by
    rw [Finset.sum_congr rfl (fun tr htr =>
      card_fiber_extractTrace hh0 hh 0 tr (Finset.mem_filter.mp htr).2)]
    simp [Finset.sum_const, smul_eq_mul]
  rw [hconst] at hsum
  have hpos : 1 ≤ 2 ^ (k - (h + b)) := Nat.one_le_pow _ 2 (by omega)
  calc (Finset.univ.filter (fun tr : Trace k h b => pinOK k h b tr = true)).card
      = (Finset.univ.filter (fun tr : Trace k h b => pinOK k h b tr = true)).card * 1 := (Nat.mul_one _).symm
    _ ≤ (Finset.univ.filter (fun tr : Trace k h b => pinOK k h b tr = true)).card * 2 ^ (k - (h + b)) :=
      Nat.mul_le_mul_left _ hpos
    _ = 2 ^ k := hsum

abbrev Hist (Q : Type) [Fintype Q] (t : ℕ) :=
  { c : Q → Fin (t + 1) // (∑ q : Q, (c q).val) = t }

lemma hockey_stick (n : ℕ) : ∀ t : ℕ,
    ∑ m ∈ Finset.range (t + 1), Nat.choose (m + n) m = Nat.choose (t + n + 1) t
  | 0 => by simp
  | t + 1 => by
    rw [Finset.sum_range_succ, hockey_stick n t]
    have h1 : t + 1 + n = t + n + 1 := by omega
    rw [h1]
    exact (Nat.choose_succ_succ (t + n + 1) t).symm

lemma card_hist_fin : ∀ (n : ℕ), 0 < n → ∀ t : ℕ,
    Fintype.card (Hist (Fin n) t) = Nat.choose (t + n - 1) t
  | 0, hn, _ => by omega
  | 1, _, t => by
    have huniq : Fintype.card (Hist (Fin 1) t) = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨fun _ => ⟨t, by omega⟩, by simp⟩, fun ⟨c, hc⟩ => ?_⟩
      apply Subtype.ext
      funext i
      have hi : i = 0 := Fin.eq_zero i
      subst hi
      apply Fin.ext
      simpa using hc
    rw [huniq]
    simp
  | n + 2, _, t => by
    have hstep : Fintype.card (Hist (Fin (n + 2)) t) =
        ∑ j : Fin (t + 1), Fintype.card (Hist (Fin (n + 1)) (t - j.val)) := by
      let S := (Finset.univ : Finset (Hist (Fin (n + 2)) t))
      have h1 := Finset.sum_fiberwise_of_maps_to (s := S) (t := (Finset.univ : Finset (Fin (t + 1))))
        (g := fun c : Hist (Fin (n + 2)) t => c.val 0) (f := fun _ => (1 : ℕ))
        (fun _ _ => Finset.mem_univ _)
      simp only [Finset.sum_const, smul_eq_mul, mul_one, S, Finset.card_univ] at h1
      rw [← h1]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.card_univ]
      symm
      apply Finset.card_bij
        (fun (c' : Hist (Fin (n + 1)) (t - j.val)) _ =>
          (⟨Fin.cons j (fun i => ⟨(c'.val i).val, by omega⟩), by
            rw [Fin.sum_univ_succ]; simp [c'.property]; omega⟩ : Hist (Fin (n + 2)) t))
      · intro c' _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.cons_zero]
      · intro c1 _ c2 _ heq
        apply Subtype.ext; funext i
        apply Fin.ext
        have h1 := congrFun (congrArg Subtype.val heq) i.succ
        simpa [Fin.cons_succ] using congrArg Fin.val h1
      · intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        have hsum := c.property
        rw [Fin.sum_univ_succ, hc] at hsum
        refine ⟨⟨fun i => ⟨(c.val i.succ).val, by
            have hle : (c.val i.succ).val ≤ ∑ x : Fin (n + 1), (c.val x.succ).val :=
              Finset.single_le_sum (f := fun x : Fin (n + 1) => (c.val x.succ).val)
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
            omega⟩, by dsimp; omega⟩, Finset.mem_univ _, ?_⟩
        apply Subtype.ext; funext i
        refine Fin.cases ?_ ?_ i
        · simp [hc]
        · intro i'; simp
    rw [hstep]
    have hrew : ∑ j : Fin (t + 1), Fintype.card (Hist (Fin (n + 1)) (t - j.val)) =
        ∑ m ∈ Finset.range (t + 1), Nat.choose (m + n) m := by
      rw [Fin.sum_univ_eq_sum_range (fun j => Fintype.card (Hist (Fin (n + 1)) (t - j))) (t + 1)]
      have hrev := Finset.sum_range_reflect (fun m => Nat.choose (m + n) m) (t + 1)
      rw [← hrev]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < t + 1 := Finset.mem_range.mp hj
      rw [card_hist_fin (n + 1) (by omega) (t - j)]
      congr 1
    have hfin : t + n + 1 = t + (n + 2) - 1 := by omega
    rw [hrew, hockey_stick n t, hfin]

lemma card_hist (Q : Type) [Fintype Q] [DecidableEq Q] (hQ : 0 < Fintype.card Q) (t : ℕ) :
    Fintype.card (Hist Q t) = Nat.choose (t + Fintype.card Q - 1) t := by
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  have heq : Fintype.card (Hist Q t) = Fintype.card (Hist (Fin (Fintype.card Q)) t) := by
    apply Fintype.card_congr
    refine
      { toFun := fun c => ⟨fun i => c.val (e.symm i),
          (Equiv.sum_comp e.symm (fun q => (c.val q).val)).trans c.property⟩
        invFun := fun c => ⟨fun q => c.val (e q),
          (Equiv.sum_comp e (fun i => (c.val i).val)).trans c.property⟩
        left_inv := fun c => by apply Subtype.ext; funext q; simp
        right_inv := fun c => by apply Subtype.ext; funext i; simp }
  rw [heq, card_hist_fin (Fintype.card Q) hQ t]

lemma card_hist_le_prod (Q : Type) [Fintype Q] [DecidableEq Q] (t : ℕ) :
    Fintype.card (Hist Q t) ≤ Fintype.card (Hist (Q × Bool) t) := by
  let inj : Hist Q t → Hist (Q × Bool) t := fun c =>
    ⟨fun p => if p.2 then ⟨0, by omega⟩ else c.val p.1, by
      rw [Fintype.sum_prod_type]
      simp [c.property]⟩
  have hinj : Function.Injective inj := by
    intro c1 c2 h
    apply Subtype.ext; funext q
    have hq := congrFun (congrArg Subtype.val h) (q, false)
    simpa [inj] using hq
  exact Fintype.card_le_of_injective inj hinj

def histSrc {Q : Type} [Fintype Q] {t : ℕ} (d : Hist (Q × Bool) t) : Hist Q t :=
  ⟨fun q => ⟨(d.val (q, false)).val + (d.val (q, true)).val, by
      have hsum := d.property
      rw [Fintype.sum_prod_type] at hsum
      have hle : (∑ b : Bool, (d.val (q, b)).val) ≤ ∑ x : Q, ∑ b : Bool, (d.val (x, b)).val :=
        Finset.single_le_sum (f := fun x : Q => ∑ b : Bool, (d.val (x, b)).val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
      simp only [Fintype.sum_bool] at hle hsum
      omega⟩, by
    have hsum := d.property
    rw [Fintype.sum_prod_type] at hsum
    simpa [Fintype.sum_bool, Nat.add_comm] using hsum⟩

def histDst {Q : Type} [Fintype Q] [DecidableEq Q] {t : ℕ}
    (step : Q × Bool → Q) (d : Hist (Q × Bool) t) : Hist Q t :=
  ⟨fun q' => ⟨∑ p ∈ Finset.univ.filter (fun p : Q × Bool => step p = q'), (d.val p).val, by
      have hle : (∑ p ∈ Finset.univ.filter (fun p : Q × Bool => step p = q'), (d.val p).val) ≤
          ∑ p : Q × Bool, (d.val p).val :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      rw [d.property] at hle
      omega⟩, by
    have h := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Q × Bool)))
      (t := (Finset.univ : Finset Q)) (g := step) (f := fun p => (d.val p).val)
      (fun _ _ => Finset.mem_univ _)
    simpa [d.property] using h⟩

def histSupp {Q : Type} [Fintype Q] [DecidableEq Q] {t : ℕ} (d : Hist (Q × Bool) t) :
    Finset (Q × Bool) :=
  Finset.univ.filter (fun p : Q × Bool => 0 < (d.val p).val)

lemma histSupp_card_le {Q : Type} [Fintype Q] [DecidableEq Q] {t : ℕ} (d : Hist (Q × Bool) t) :
    (histSupp d).card ≤ t := by
  calc (histSupp d).card = ∑ _p ∈ histSupp d, 1 := by simp
    _ ≤ ∑ p ∈ histSupp d, (d.val p).val := by
        apply Finset.sum_le_sum
        intro p hp
        exact (Finset.mem_filter.mp hp).2
    _ ≤ ∑ p : Q × Bool, (d.val p).val := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = t := d.property

def splitWeight {Q : Type} [Fintype Q] {t : ℕ} (d : Hist (Q × Bool) t) : ℕ :=
  ∏ q : Q, Nat.choose ((d.val (q, false)).val + (d.val (q, true)).val) (d.val (q, false)).val

lemma choose_le_two_pow (m j : ℕ) : Nat.choose m j ≤ 2 ^ m := by
  by_cases hj : j ≤ m
  · have hmem : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    calc Nat.choose m j ≤ ∑ i ∈ Finset.range (m + 1), Nat.choose m i :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
      _ = 2 ^ m := Nat.sum_range_choose m
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

lemma splitWeight_lt {Q : Type} [Fintype Q] {t : ℕ} (d : Hist (Q × Bool) t) :
    splitWeight d < 2 ^ (t + 1) := by
  have hle : splitWeight d ≤ 2 ^ t := by
    unfold splitWeight
    calc (∏ q : Q, Nat.choose ((d.val (q, false)).val + (d.val (q, true)).val) (d.val (q, false)).val)
        ≤ ∏ q : Q, 2 ^ ((d.val (q, false)).val + (d.val (q, true)).val) :=
          Finset.prod_le_prod (fun q _ => choose_le_two_pow _ _)
      _ = 2 ^ (∑ q : Q, ((d.val (q, false)).val + (d.val (q, true)).val)) := by
          rw [Finset.prod_pow_eq_pow_sum]
      _ = 2 ^ t := by
          congr 1
          have hsum := d.property
          rw [Fintype.sum_prod_type] at hsum
          simpa [Fintype.sum_bool, Nat.add_comm] using hsum
  exact lt_of_le_of_lt hle (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self t))

def histOf {Q : Type} [Fintype Q] [DecidableEq Q] {t : ℕ} (f : Fin t → Q) : Hist Q t :=
  ⟨fun q => ⟨(Finset.univ.filter (fun u : Fin t => f u = q)).card, by
      have hle : (Finset.univ.filter (fun u : Fin t => f u = q)).card ≤ (Finset.univ : Finset (Fin t)).card :=
        Finset.card_filter_le _ _
      simp only [Finset.card_univ, Fintype.card_fin] at hle
      omega⟩, by
    have h := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin t)))
      (t := (Finset.univ : Finset Q)) (g := f) (f := fun _ => (1 : ℕ))
      (fun _ _ => Finset.mem_univ _)
    simpa [Finset.sum_const, smul_eq_mul] using h⟩

lemma histSrc_histOf {Q : Type} [Fintype Q] [DecidableEq Q] {t : ℕ}
    (f : Fin t → Q) (e : Fin t → Bool) :
    histSrc (histOf (fun u => (f u, e u))) = histOf f := by
  apply Subtype.ext; funext q; apply Fin.ext
  dsimp [histSrc, histOf]
  have hpart : (Finset.univ.filter (fun u : Fin t => f u = q)).card =
      (Finset.univ.filter (fun u : Fin t => (f u, e u) = (q, false))).card +
      (Finset.univ.filter (fun u : Fin t => (f u, e u) = (q, true))).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Prod.mk.injEq]
      cases e u <;> simp
    · rw [Finset.disjoint_left]
      intro u h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at h1 h2
      rw [h1.2] at h2
      exact Bool.false_ne_true h2.2
  exact hpart.symm

lemma histDst_histOf {Q : Type} [Fintype Q] [DecidableEq Q] {t : ℕ}
    (step : Q × Bool → Q) (f : Fin t → Q) (e : Fin t → Bool) :
    histDst step (histOf (fun u => (f u, e u))) = histOf (fun u => step (f u, e u)) := by
  apply Subtype.ext; funext q'; apply Fin.ext
  dsimp [histDst, histOf]
  have h := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun u : Fin t => step (f u, e u) = q'))
    (t := Finset.univ.filter (fun p : Q × Bool => step p = q'))
    (g := fun u => (f u, e u)) (f := fun _ => (1 : ℕ))
    (fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1; ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  constructor
  · intro heq; exact ⟨by rw [heq]; exact hp, heq⟩
  · intro ⟨_, heq⟩; exact heq

lemma card_split_fiber {Q : Type} [Fintype Q] [DecidableEq Q] {t : ℕ}
    (f : Fin t → Q) (d : Hist (Q × Bool) t) (hsrc : histSrc d = histOf f) :
    (Finset.univ.filter (fun e : Fin t → Bool => histOf (fun u => (f u, e u)) = d)).card =
      splitWeight d := by
  let S (q : Q) : Finset (Fin t) := Finset.univ.filter (fun u : Fin t => f u = q)
  have hScard : ∀ q : Q, (S q).card = (d.val (q, false)).val + (d.val (q, true)).val := by
    intro q
    have hq := congrArg Fin.val (congrFun (congrArg Subtype.val hsrc) q)
    exact hq.symm
  let Choice := ∀ q : Q, { T : Finset (Fin t) // T ∈ (S q).powersetCard (d.val (q, false)).val }
  have hcardChoice : Fintype.card Choice = splitWeight d := by
    dsimp [Choice, splitWeight]
    rw [Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro q _
    rw [Fintype.card_coe, Finset.card_powersetCard, hScard q]
  rw [← hcardChoice, ← Finset.card_univ]
  symm
  apply Finset.card_bij (fun (ch : Choice) _ (u : Fin t) => decide (u ∉ (ch (f u)).val))
  · intro ch _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Subtype.ext; funext p; apply Fin.ext
    rcases p with ⟨q, b⟩
    have hch := Finset.mem_powersetCard.mp (ch q).property
    have hsub : (ch q).val ⊆ S q := hch.1
    have hcard : (ch q).val.card = (d.val (q, false)).val := hch.2
    cases b
    · have hfilt : Finset.univ.filter (fun u : Fin t => (f u, decide (u ∉ (ch (f u)).val)) = (q, false)) =
          (ch q).val := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq, decide_eq_false_iff_not,
          Classical.not_not]
        constructor
        · rintro ⟨hfq, hu⟩; rwa [hfq] at hu
        · intro hu
          have hmem : u ∈ S q := hsub hu
          have hfq : f u = q := (Finset.mem_filter.mp hmem).2
          exact ⟨hfq, by rw [hfq]; exact hu⟩
      dsimp [histOf]; rw [hfilt, hcard]
    · have hfilt : Finset.univ.filter (fun u : Fin t => (f u, decide (u ∉ (ch (f u)).val)) = (q, true)) =
          S q \ (ch q).val := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq, decide_eq_true_eq,
          Finset.mem_sdiff, S]
        constructor
        · rintro ⟨hfq, hu⟩; exact ⟨hfq, by rwa [hfq] at hu⟩
        · rintro ⟨hfq, hu⟩; exact ⟨hfq, by rw [hfq]; exact hu⟩
      dsimp [histOf]
      rw [hfilt, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hScard q, hcard]
      omega
  · intro ch1 _ ch2 _ heq
    funext q
    apply Subtype.ext
    ext u
    have hsub1 := (Finset.mem_powersetCard.mp (ch1 q).property).1
    have hsub2 := (Finset.mem_powersetCard.mp (ch2 q).property).1
    constructor
    · intro hu
      have hfq : f u = q := (Finset.mem_filter.mp (hsub1 hu)).2
      have h1 := congrFun heq u
      rw [hfq, decide_eq_decide] at h1
      by_contra hnot
      exact (h1.mpr hnot) hu
    · intro hu
      have hfq : f u = q := (Finset.mem_filter.mp (hsub2 hu)).2
      have h1 := congrFun heq u
      rw [hfq, decide_eq_decide] at h1
      by_contra hnot
      exact (h1.mp hnot) hu
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    have hmem : ∀ q : Q, (S q).filter (fun u => e u = false) ∈ (S q).powersetCard (d.val (q, false)).val := by
      intro q
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      have hq := congrArg Fin.val (congrFun (congrArg Subtype.val he) (q, false))
      dsimp [histOf] at hq
      rw [← hq]
      congr 1; ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq, S]
    refine ⟨fun q => ⟨(S q).filter (fun u => e u = false), hmem q⟩, Finset.mem_univ _, ?_⟩
    funext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
    cases e u <;> simp

end
end PinHist

section TrackDP

noncomputable section
open Classical

abbrev TrackState (k h b : ℕ) := (Fin (seam k h b) → Bool) × (Fin b → Bool)

def extWin (b : ℕ) (mem : Fin b → Bool) (e : Bool) : Fin (b + 1) → Bool :=
  fun i => if hi : i.val < b then mem ⟨i.val, hi⟩ else e

def shiftMem (b : ℕ) (mem : Fin b → Bool) (e : Bool) : Fin b → Bool :=
  fun i => if hi : i.val + 1 < b then mem ⟨i.val + 1, hi⟩ else e

def nextTrack (k h b : ℕ) (st : TrackState k h b) (e : Bool) : TrackState k h b :=
  (st.1, shiftMem b st.2 e)

def initPinOK (k h b : ℕ) (st : TrackState k h b) : Bool :=
  (List.finRange b).all (fun i =>
    if hi : i.val % k < seam k h b then decide (st.2 i = st.1 ⟨i.val % k, hi⟩) else true)

def stepPinOK (k h b s : ℕ) (st : TrackState k h b) (e : Bool) : Bool :=
  if hi : (s + b) % k < seam k h b then decide (e = st.1 ⟨(s + b) % k, hi⟩) else true

abbrev PrefTrace (k h b s : ℕ) := (Fin (seam k h b) → Bool) × (Fin (s + b) → Bool)

def prefPinOK (k h b s : ℕ) (pt : PrefTrace k h b s) : Bool :=
  (List.finRange (s + b)).all (fun i =>
    if hi : i.val % k < seam k h b then decide (pt.2 i = pt.1 ⟨i.val % k, hi⟩) else true)

lemma prefPinOK_iff (k h b s : ℕ) (pt : PrefTrace k h b s) :
    prefPinOK k h b s pt = true ↔
      ∀ i : Fin (s + b), ∀ hi : i.val % k < seam k h b, pt.2 i = pt.1 ⟨i.val % k, hi⟩ := by
  unfold prefPinOK
  rw [List.all_eq_true]
  constructor
  · intro hall i hi
    have h1 := hall i (List.mem_finRange i)
    simp only [hi, ↓reduceDIte, decide_eq_true_eq] at h1
    exact h1
  · intro hall i _
    by_cases hi : i.val % k < seam k h b
    · simp only [hi, ↓reduceDIte, decide_eq_true_eq]
      exact hall i hi
    · simp only [hi, ↓reduceDIte]

def endState (k h b s : ℕ) (pt : PrefTrace k h b s) : TrackState k h b :=
  (pt.1, fun i : Fin b => pt.2 ⟨s + i.val, by omega⟩)

def extPref (k h b s : ℕ) (pt : PrefTrace k h b s) (e : Bool) : PrefTrace k h b (s + 1) :=
  (pt.1, fun i : Fin (s + 1 + b) => if hi : i.val < s + b then pt.2 ⟨i.val, hi⟩ else e)

def prefWin (k h b s : ℕ) (pt : PrefTrace k h b s) (j : ℕ) (hj : j < s) : Fin (b + 1) → Bool :=
  fun i => pt.2 ⟨j + i.val, by omega⟩

lemma endState_extPref (k h b s : ℕ) (pt : PrefTrace k h b s) (e : Bool) :
    endState k h b (s + 1) (extPref k h b s pt e) = nextTrack k h b (endState k h b s pt) e := by
  apply Prod.ext
  · rfl
  · funext i
    dsimp [endState, extPref, nextTrack, shiftMem]
    by_cases hi : i.val + 1 < b
    · have hlt : s + 1 + i.val < s + b := by omega
      simp only [hi, hlt, ↓reduceDIte]
      exact congrArg pt.2 (Fin.ext (by dsimp; omega))
    · have hnot : ¬ (s + 1 + i.val < s + b) := by omega
      simp only [hi, hnot, ↓reduceDIte]

lemma prefWin_extPref_lt (k h b s : ℕ) (pt : PrefTrace k h b s) (e : Bool)
    (j : ℕ) (hj : j < s) :
    prefWin k h b (s + 1) (extPref k h b s pt e) j (by omega) = prefWin k h b s pt j hj := by
  funext i
  dsimp [prefWin, extPref]
  have hlt : j + i.val < s + b := by omega
  simp only [hlt, ↓reduceDIte]

lemma prefWin_extPref_last (k h b s : ℕ) (pt : PrefTrace k h b s) (e : Bool) :
    prefWin k h b (s + 1) (extPref k h b s pt e) s (by omega) =
      extWin b (endState k h b s pt).2 e := by
  funext i
  dsimp [prefWin, extPref, extWin, endState]
  by_cases hi : i.val < b
  · have hlt : s + i.val < s + b := by omega
    simp only [hi, hlt, ↓reduceDIte]
  · have hnot : ¬ (s + i.val < s + b) := by omega
    simp only [hi, hnot, ↓reduceDIte]

lemma prefPinOK_extPref (k h b s : ℕ) (pt : PrefTrace k h b s) (e : Bool) :
    prefPinOK k h b (s + 1) (extPref k h b s pt e) =
      (prefPinOK k h b s pt && stepPinOK k h b s (endState k h b s pt) e) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true, prefPinOK_iff, prefPinOK_iff]
  unfold stepPinOK endState
  constructor
  · intro hall
    refine ⟨fun i hi => ?_, ?_⟩
    · have h1 := hall ⟨i.val, by omega⟩ hi
      dsimp [extPref] at h1
      simpa [i.isLt] using h1
    · by_cases hi : (s + b) % k < seam k h b
      · simp only [hi, ↓reduceDIte, decide_eq_true_eq]
        have h1 := hall ⟨s + b, by omega⟩ hi
        dsimp [extPref] at h1
        simpa using h1
      · simp only [hi, ↓reduceDIte]
  · rintro ⟨hprev, hstep⟩ i hi
    dsimp [extPref]
    by_cases hlt : i.val < s + b
    · simp only [hlt, ↓reduceDIte]
      exact hprev ⟨i.val, hlt⟩ hi
    · have heq : i.val = s + b := by omega
      simp only [hlt, ↓reduceDIte]
      have hi' : (s + b) % k < seam k h b := by rwa [← heq]
      simp only [hi', ↓reduceDIte, decide_eq_true_eq] at hstep
      rw [hstep]
      exact congrArg pt.1 (Fin.ext (by dsimp; rw [heq]))

lemma card_prefPinOK_le {k h b s : ℕ} (hh0 : 0 < h) (hh : h ≤ k) (hs : s ≤ h) :
    (Finset.univ.filter (fun pt : PrefTrace k h b s => prefPinOK k h b s pt = true)).card ≤ 2 ^ k := by
  let pad : PrefTrace k h b s → Trace k h b := fun pt =>
    (pt.1, fun i : Fin (h + b) =>
      if hi : i.val < s + b then pt.2 ⟨i.val, hi⟩
      else if hmod : i.val % k < seam k h b then pt.1 ⟨i.val % k, hmod⟩
      else false)
  have hle : (Finset.univ.filter (fun pt : PrefTrace k h b s => prefPinOK k h b s pt = true)).card ≤
      (Finset.univ.filter (fun tr : Trace k h b => pinOK k h b tr = true)).card := by
    apply Finset.card_le_card_of_injOn pad
    · intro pt hpt
      have hok := (prefPinOK_iff k h b s pt).mp (Finset.mem_filter.mp (Finset.mem_coe.mp hpt)).2
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (pinOK_iff k h b (pad pt)).mpr ?_⟩
      intro i hi
      dsimp [pad]
      by_cases hlt : i.val < s + b
      · simp only [hlt, ↓reduceDIte]
        exact hok ⟨i.val, hlt⟩ hi
      · simp only [hlt, hi, ↓reduceDIte]
    · intro pt1 _ pt2 _ heq
      have heq' : (pt1.1, fun i : Fin (h + b) =>
          if hi : i.val < s + b then pt1.2 ⟨i.val, hi⟩
          else if hmod : i.val % k < seam k h b then pt1.1 ⟨i.val % k, hmod⟩ else false) =
        (pt2.1, fun i : Fin (h + b) =>
          if hi : i.val < s + b then pt2.2 ⟨i.val, hi⟩
          else if hmod : i.val % k < seam k h b then pt2.1 ⟨i.val % k, hmod⟩ else false) := heq
      rcases Prod.mk.inj heq' with ⟨hfst, hsnd⟩
      apply Prod.ext hfst
      funext i
      have hi : i.val < h + b := by omega
      have h1 := congrFun hsnd ⟨i.val, hi⟩
      simpa [i.isLt] using h1
  exact hle.trans (card_pinOK_le hh0 hh)

def rowLocalOK (k r h : ℕ) (masks : ℕ → Fin (2 ^ k)) (a : Fin (2 ^ h))
    (s : ℕ) (xWin : Fin (4 * r + 1) → Bool) (kWin : Fin (bKey r + 1) → Bool) : Bool :=
  decide (srun r false (winExt (lKey r) kWin) (winExt (lName r false) xWin)
    (fun j q => cbit k (masks j).val (((k - h + s : ℕ) : ℤ) + q)) r 0 = a.val.testBit s)

def colLocalOK (k r h : ℕ) (masks : ℕ → Fin (2 ^ k)) (b : Fin (2 ^ h))
    (s : ℕ) (yWin : Fin (6 * r + 1) → Bool) (kWin : Fin (bKey r + 1) → Bool) : Bool :=
  decide (srun r true (winExt (lKey r) kWin) (winExt (lName r true) yWin)
    (fun j q => cbit k (masks j).val (((k - h + s : ℕ) : ℤ) + q)) r 0 = b.val.testBit s)

abbrev CellT (k r h t : ℕ) :=
  TrackState k h (4 * r) × TrackState k h (6 * r) × Hist (TrackState k h (bKey r)) t

abbrev TransT (k r h t : ℕ) :=
  (TrackState k h (4 * r) × Bool) × (TrackState k h (6 * r) × Bool) ×
    Hist (TrackState k h (bKey r) × Bool) t

def transSrc {k r h t : ℕ} (tr : TransT k r h t) : CellT k r h t :=
  (tr.1.1, tr.2.1.1, histSrc tr.2.2)

def transDst {k r h t : ℕ} (tr : TransT k r h t) : CellT k r h t :=
  (nextTrack k h (4 * r) tr.1.1 tr.1.2,
   nextTrack k h (6 * r) tr.2.1.1 tr.2.1.2,
   histDst (fun p => nextTrack k h (bKey r) p.1 p.2) tr.2.2)

def transPinOK {k r h t : ℕ} (s : ℕ) (tr : TransT k r h t) : Bool :=
  stepPinOK k h (4 * r) s tr.1.1 tr.1.2 &&
  stepPinOK k h (6 * r) s tr.2.1.1 tr.2.1.2 &&
  (histSupp tr.2.2).toList.all (fun p => stepPinOK k h (bKey r) s p.1 p.2)

def transTestOK {k r h t : ℕ} (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h))
    (s : ℕ) (tr : TransT k r h t) : Bool :=
  (histSupp tr.2.2).toList.all (fun p =>
    rowLocalOK k r h masks a s (extWin (4 * r) tr.1.1.2 tr.1.2) (extWin (bKey r) p.1.2 p.2) &&
    colLocalOK k r h masks b s (extWin (6 * r) tr.2.1.1.2 tr.2.1.2) (extWin (bKey r) p.1.2 p.2))

def transValid {k r h t : ℕ} (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h))
    (s : ℕ) (tr : TransT k r h t) : Bool :=
  transPinOK s tr && transTestOK masks a b s tr

def baseMult {k r h t : ℕ} (c : Hist (TrackState k h (bKey r)) t) : ℕ :=
  (Finset.univ.filter (fun f : Fin t → TrackState k h (bKey r) => histOf f = c)).card

def initCellOK {k r h t : ℕ} (cell : CellT k r h t) : Bool :=
  initPinOK k h (4 * r) cell.1 &&
  initPinOK k h (6 * r) cell.2.1 &&
  (Finset.univ.filter (fun q : TrackState k h (bKey r) => 0 < (cell.2.2.val q).val)).toList.all
    (initPinOK k h (bKey r))

def dpVal (k r h t : ℕ) (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) :
    ℕ → CellT k r h t → ℕ
  | 0, cell => if initCellOK cell then baseMult cell.2.2 else 0
  | s + 1, cell' =>
      ∑ tr ∈ Finset.univ.filter (fun tr : TransT k r h t => transDst tr = cell'),
        (if transValid masks a b s tr then dpVal k r h t masks a b s (transSrc tr) else 0) *
          splitWeight tr.2.2

abbrev TuplePref (k r h t s : ℕ) :=
  PrefTrace k h (4 * r) s × PrefTrace k h (6 * r) s × (Fin t → PrefTrace k h (bKey r) s)

def tupleEnd {k r h t s : ℕ} (tp : TuplePref k r h t s) : CellT k r h t :=
  (endState k h (4 * r) s tp.1,
   endState k h (6 * r) s tp.2.1,
   histOf (fun u => endState k h (bKey r) s (tp.2.2 u)))

def tupleGood {k r h t s : ℕ} (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h))
    (tp : TuplePref k r h t s) : Bool :=
  prefPinOK k h (4 * r) s tp.1 &&
  prefPinOK k h (6 * r) s tp.2.1 &&
  (List.finRange t).all (fun u => prefPinOK k h (bKey r) s (tp.2.2 u)) &&
  (List.finRange s).all (fun j =>
    (List.finRange t).all (fun u =>
      rowLocalOK k r h masks a j.val
        (prefWin k h (4 * r) s tp.1 j.val j.isLt)
        (prefWin k h (bKey r) s (tp.2.2 u) j.val j.isLt) &&
      colLocalOK k r h masks b j.val
        (prefWin k h (6 * r) s tp.2.1 j.val j.isLt)
        (prefWin k h (bKey r) s (tp.2.2 u) j.val j.isLt)))

def goodPrefSet (k r h t : ℕ) (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h))
    (s : ℕ) (cell : CellT k r h t) : Finset (TuplePref k r h t s) :=
  Finset.univ.filter (fun tp => tupleGood masks a b tp = true ∧ tupleEnd tp = cell)

lemma initPinOK_eq_prefPinOK_zero (k h b : ℕ) (st : TrackState k h b) :
    initPinOK k h b st = prefPinOK k h b 0 (st.1, fun i : Fin (0 + b) => st.2 ⟨i.val, by omega⟩) := by
  apply Bool.eq_iff_iff.mpr
  unfold initPinOK prefPinOK
  rw [List.all_eq_true, List.all_eq_true]
  constructor
  · intro hall i _
    have h1 := hall ⟨i.val, by omega⟩ (List.mem_finRange _)
    simpa using h1
  · intro hall i _
    have h1 := hall ⟨i.val, by omega⟩ (List.mem_finRange _)
    simpa using h1

lemma dpVal_eq_card_goodPref (k r h t : ℕ) (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) :
    ∀ s cell, dpVal k r h t masks a b s cell = (goodPrefSet k r h t masks a b s cell).card
  | 0, cell => by
    rcases cell with ⟨sx, sy, c⟩
    dsimp [dpVal, goodPrefSet]
    by_cases hok : initCellOK (sx, sy, c) = true
    · simp only [hok, ↓reduceIte]
      dsimp [initCellOK] at hok
      simp only [Bool.and_eq_true, List.all_eq_true, Finset.mem_toList, Finset.mem_filter,
        Finset.mem_univ, true_and] at hok
      rcases hok with ⟨⟨hxok, hyok⟩, hkok⟩
      unfold baseMult
      apply Finset.card_bij
        (fun (f : Fin t → TrackState k h (bKey r)) _ =>
          ((sx.1, fun i : Fin (0 + 4 * r) => sx.2 ⟨i.val, by omega⟩),
           (sy.1, fun i : Fin (0 + 6 * r) => sy.2 ⟨i.val, by omega⟩),
           fun u => ((f u).1, fun i : Fin (0 + bKey r) => (f u).2 ⟨i.val, by omega⟩)))
      · intro f hf
        have hfc : histOf f = c := (Finset.mem_filter.mp hf).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hgood : tupleGood masks a b
            ((sx.1, fun i : Fin (0 + 4 * r) => sx.2 ⟨i.val, by omega⟩),
             (sy.1, fun i : Fin (0 + 6 * r) => sy.2 ⟨i.val, by omega⟩),
             fun u => ((f u).1, fun i : Fin (0 + bKey r) => (f u).2 ⟨i.val, by omega⟩)) = true := by
          unfold tupleGood
          simp only [List.finRange_zero, List.all_nil, Bool.and_true, Bool.and_eq_true,
            List.all_eq_true]
          refine ⟨⟨?_, ?_⟩, fun u _ => ?_⟩
          · rw [← initPinOK_eq_prefPinOK_zero]; exact hxok
          · rw [← initPinOK_eq_prefPinOK_zero]; exact hyok
          · rw [← initPinOK_eq_prefPinOK_zero]
            apply hkok (f u)
            have hq := congrArg Fin.val (congrFun (congrArg Subtype.val hfc) (f u))
            rw [← hq]
            dsimp [histOf]
            exact Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, rfl⟩⟩
        refine ⟨hgood, ?_⟩
        unfold tupleEnd endState
        refine Prod.ext (Prod.ext rfl (by funext i; simp))
          (Prod.ext (Prod.ext rfl (by funext i; simp)) ?_)
        simpa using hfc
      · intro f1 _ f2 _ heq
        funext u
        have hu := congrFun (congrArg (fun x => x.2.2) heq) u
        dsimp at hu
        rcases Prod.mk.inj hu with ⟨h1, h2⟩
        exact Prod.ext h1 (funext fun i => congrFun h2 ⟨i.val, by omega⟩)
      · intro tp htp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at htp
        rcases htp with ⟨_, hend⟩
        unfold tupleEnd at hend
        have hx : endState k h (4 * r) 0 tp.1 = sx := congrArg Prod.fst hend
        have hy : endState k h (6 * r) 0 tp.2.1 = sy := congrArg (fun p => p.2.1) hend
        have hc : histOf (fun u => endState k h (bKey r) 0 (tp.2.2 u)) = c :=
          congrArg (fun p => p.2.2) hend
        refine ⟨fun u => endState k h (bKey r) 0 (tp.2.2 u),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, ?_⟩
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · dsimp; rw [← hx]; apply Prod.ext; · rfl
          · funext i; dsimp [endState]; exact congrArg tp.1.2 (Fin.ext (by simp))
        · dsimp; rw [← hy]; apply Prod.ext; · rfl
          · funext i; dsimp [endState]; exact congrArg tp.2.1.2 (Fin.ext (by simp))
        · dsimp; funext u; apply Prod.ext; · rfl
          · funext i; dsimp [endState]; exact congrArg (tp.2.2 u).2 (Fin.ext (by simp))
    · have hokf : initCellOK (sx, sy, c) = false := Bool.eq_false_iff.mpr hok
      simp only [hokf, Bool.false_eq_true, ↓reduceIte]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro tp _ hmem
      rcases hmem with ⟨hgood, hend⟩
      apply hok
      dsimp [initCellOK]
      simp only [Bool.and_eq_true, List.all_eq_true, Finset.mem_toList, Finset.mem_filter,
        Finset.mem_univ, true_and]
      unfold tupleGood at hgood
      simp only [List.finRange_zero, List.all_nil, Bool.and_true, Bool.and_eq_true,
        List.all_eq_true] at hgood
      rcases hgood with ⟨⟨hgx, hgy⟩, hgk⟩
      have hx : endState k h (4 * r) 0 tp.1 = sx := congrArg Prod.fst hend
      have hy : endState k h (6 * r) 0 tp.2.1 = sy := congrArg (fun p => p.2.1) hend
      have hc : histOf (fun u => endState k h (bKey r) 0 (tp.2.2 u)) = c :=
        congrArg (fun p => p.2.2) hend
      refine ⟨⟨?_, ?_⟩, fun q hq => ?_⟩
      · rw [← hx, initPinOK_eq_prefPinOK_zero]
        have he : ((endState k h (4 * r) 0 tp.1).1,
            fun i : Fin (0 + 4 * r) => (endState k h (4 * r) 0 tp.1).2 ⟨i.val, by omega⟩) = tp.1 := by
          apply Prod.ext; · rfl
          · funext i; dsimp [endState]; exact congrArg tp.1.2 (Fin.ext (by simp))
        rwa [he]
      · rw [← hy, initPinOK_eq_prefPinOK_zero]
        have he : ((endState k h (6 * r) 0 tp.2.1).1,
            fun i : Fin (0 + 6 * r) => (endState k h (6 * r) 0 tp.2.1).2 ⟨i.val, by omega⟩) = tp.2.1 := by
          apply Prod.ext; · rfl
          · funext i; dsimp [endState]; exact congrArg tp.2.1.2 (Fin.ext (by simp))
        rwa [he]
      · have hq' : 0 < ((histOf (fun u => endState k h (bKey r) 0 (tp.2.2 u))).val q).val := by
          rwa [hc]
        dsimp [histOf] at hq'
        obtain ⟨u, hu⟩ := Finset.card_pos.mp hq'
        have huq : endState k h (bKey r) 0 (tp.2.2 u) = q := (Finset.mem_filter.mp hu).2
        rw [← huq, initPinOK_eq_prefPinOK_zero]
        have he : ((endState k h (bKey r) 0 (tp.2.2 u)).1,
            fun i : Fin (0 + bKey r) => (endState k h (bKey r) 0 (tp.2.2 u)).2 ⟨i.val, by omega⟩) = tp.2.2 u := by
          apply Prod.ext; · rfl
          · funext i; dsimp [endState]; exact congrArg (tp.2.2 u).2 (Fin.ext (by simp))
        rw [he]
        exact hgk u (List.mem_finRange u)
  | s + 1, cell' => by
    dsimp [dpVal]
    let stepPair : TuplePref k r h t s × (Bool × Bool × (Fin t → Bool)) → TuplePref k r h t (s + 1) :=
      fun ⟨tp, ex, ey, eK⟩ =>
        (extPref k h (4 * r) s tp.1 ex,
         extPref k h (6 * r) s tp.2.1 ey,
         fun u => extPref k h (bKey r) s (tp.2.2 u) (eK u))
    let transOfPair : TuplePref k r h t s × (Bool × Bool × (Fin t → Bool)) → TransT k r h t :=
      fun ⟨tp, ex, ey, eK⟩ =>
        ((endState k h (4 * r) s tp.1, ex),
         (endState k h (6 * r) s tp.2.1, ey),
         histOf (fun u => (endState k h (bKey r) s (tp.2.2 u), eK u)))
    have hstepEnd : ∀ z, tupleEnd (stepPair z) = transDst (transOfPair z) := by
      rintro ⟨tp, ex, ey, eK⟩
      dsimp [tupleEnd, stepPair, transDst, transOfPair]
      refine Prod.ext (endState_extPref k h (4 * r) s tp.1 ex)
        (Prod.ext (endState_extPref k h (6 * r) s tp.2.1 ey) ?_)
      dsimp
      rw [histDst_histOf]
      congr 1; funext u
      exact endState_extPref k h (bKey r) s (tp.2.2 u) (eK u)
    have hstepGood : ∀ z, tupleGood masks a b (stepPair z) =
        (tupleGood masks a b z.1 && transValid masks a b s (transOfPair z)) := by
      rintro ⟨tp, ex, ey, eK⟩
      apply Bool.eq_iff_iff.mpr
      dsimp [stepPair, transOfPair, tupleGood, transValid, transPinOK, transTestOK]
      simp only [Bool.and_eq_true, List.all_eq_true, Finset.mem_toList, histSupp,
        Finset.mem_filter, Finset.mem_univ, true_and, List.mem_finRange, true_implies]
      rw [prefPinOK_extPref, prefPinOK_extPref]
      simp only [Bool.and_eq_true]
      have hKpin : (∀ u : Fin t, prefPinOK k h (bKey r) (s + 1) (extPref k h (bKey r) s (tp.2.2 u) (eK u)) = true) ↔
          (∀ u : Fin t, prefPinOK k h (bKey r) s (tp.2.2 u) = true) ∧
          (∀ p : TrackState k h (bKey r) × Bool,
            0 < ((histOf (fun u => (endState k h (bKey r) s (tp.2.2 u), eK u))).val p).val →
            stepPinOK k h (bKey r) s p.1 p.2 = true) := by
        simp_rw [prefPinOK_extPref, Bool.and_eq_true, forall_and]
        refine and_congr Iff.rfl ⟨fun h1 p hp => ?_, fun h2 u => ?_⟩
        · dsimp [histOf] at hp
          obtain ⟨u, hu⟩ := Finset.card_pos.mp hp
          have heq : (endState k h (bKey r) s (tp.2.2 u), eK u) = p := (Finset.mem_filter.mp hu).2
          rw [← heq]; exact h1 u
        · apply h2 (endState k h (bKey r) s (tp.2.2 u), eK u)
          dsimp [histOf]
          exact Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, rfl⟩⟩
      have hTests : (∀ j : Fin (s + 1), ∀ u : Fin t,
          rowLocalOK k r h masks a j.val
            (prefWin k h (4 * r) (s + 1) (extPref k h (4 * r) s tp.1 ex) j.val j.isLt)
            (prefWin k h (bKey r) (s + 1) (extPref k h (bKey r) s (tp.2.2 u) (eK u)) j.val j.isLt) = true ∧
          colLocalOK k r h masks b j.val
            (prefWin k h (6 * r) (s + 1) (extPref k h (6 * r) s tp.2.1 ey) j.val j.isLt)
            (prefWin k h (bKey r) (s + 1) (extPref k h (bKey r) s (tp.2.2 u) (eK u)) j.val j.isLt) = true) ↔
          (∀ j : Fin s, ∀ u : Fin t,
            rowLocalOK k r h masks a j.val
              (prefWin k h (4 * r) s tp.1 j.val j.isLt)
              (prefWin k h (bKey r) s (tp.2.2 u) j.val j.isLt) = true ∧
            colLocalOK k r h masks b j.val
              (prefWin k h (6 * r) s tp.2.1 j.val j.isLt)
              (prefWin k h (bKey r) s (tp.2.2 u) j.val j.isLt) = true) ∧
          (∀ p : TrackState k h (bKey r) × Bool,
            0 < ((histOf (fun u => (endState k h (bKey r) s (tp.2.2 u), eK u))).val p).val →
            rowLocalOK k r h masks a s (extWin (4 * r) (endState k h (4 * r) s tp.1).2 ex)
              (extWin (bKey r) p.1.2 p.2) = true ∧
            colLocalOK k r h masks b s (extWin (6 * r) (endState k h (6 * r) s tp.2.1).2 ey)
              (extWin (bKey r) p.1.2 p.2) = true) := by
        constructor
        · intro hall
          refine ⟨fun j u => ?_, fun p hp => ?_⟩
          · have h1 := hall ⟨j.val, by omega⟩ u
            rwa [prefWin_extPref_lt, prefWin_extPref_lt, prefWin_extPref_lt] at h1
          · dsimp [histOf] at hp
            obtain ⟨u, hu⟩ := Finset.card_pos.mp hp
            have heq : (endState k h (bKey r) s (tp.2.2 u), eK u) = p := (Finset.mem_filter.mp hu).2
            rw [← heq]
            have h1 := hall ⟨s, by omega⟩ u
            rwa [prefWin_extPref_last, prefWin_extPref_last, prefWin_extPref_last] at h1
        · rintro ⟨hprev, hlast⟩ j u
          by_cases hjs : j.val < s
          · have h1 := hprev ⟨j.val, hjs⟩ u
            rwa [← prefWin_extPref_lt k h (4 * r) s tp.1 ex j.val hjs,
                 ← prefWin_extPref_lt k h (6 * r) s tp.2.1 ey j.val hjs,
                 ← prefWin_extPref_lt k h (bKey r) s (tp.2.2 u) (eK u) j.val hjs] at h1
          · have hjeq : j.val = s := by omega
            have h1 := hlast (endState k h (bKey r) s (tp.2.2 u), eK u) (by
              dsimp [histOf]
              exact Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, rfl⟩⟩)
            have hs' : s < s + 1 := Nat.lt_succ_self s
            have hjfin : j = ⟨s, hs'⟩ := Fin.ext hjeq
            rw [hjfin]
            rwa [← prefWin_extPref_last, ← prefWin_extPref_last, ← prefWin_extPref_last] at h1
      rw [hKpin, hTests]
      tauto
    have hbijStep : (goodPrefSet k r h t masks a b (s + 1) cell').card =
        (Finset.univ.filter (fun z : TuplePref k r h t s × (Bool × Bool × (Fin t → Bool)) =>
          tupleGood masks a b z.1 = true ∧ transValid masks a b s (transOfPair z) = true ∧
          transDst (transOfPair z) = cell')).card := by
      symm
      apply Finset.card_bij (fun z _ => stepPair z)
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        simp only [goodPrefSet, Finset.mem_filter, Finset.mem_univ, true_and, hstepGood, hstepEnd,
          Bool.and_eq_true]
        exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩
      · rintro ⟨tp1, ex1, ey1, eK1⟩ _ ⟨tp2, ex2, ey2, eK2⟩ _ heq
        have hExtInj : ∀ {b' : ℕ} {p1 p2 : PrefTrace k h b' s} {e1 e2 : Bool},
            extPref k h b' s p1 e1 = extPref k h b' s p2 e2 → p1 = p2 ∧ e1 = e2 := by
          intro b' p1 p2 e1 e2 he
          have he' : (p1.1, fun i : Fin (s + 1 + b') => if hi : i.val < s + b' then p1.2 ⟨i.val, hi⟩ else e1) =
            (p2.1, fun i : Fin (s + 1 + b') => if hi : i.val < s + b' then p2.2 ⟨i.val, hi⟩ else e2) := he
          rcases Prod.mk.inj he' with ⟨hfst, hsnd⟩
          refine ⟨Prod.ext hfst (funext fun i => ?_), ?_⟩
          · have hi := congrFun hsnd ⟨i.val, by omega⟩
            simpa [i.isLt] using hi
          · have hi := congrFun hsnd ⟨s + b', by omega⟩
            simpa using hi
        have hx := hExtInj (congrArg Prod.fst heq)
        have hy := hExtInj (congrArg (fun p => p.2.1) heq)
        have hK : ∀ u, tp1.2.2 u = tp2.2.2 u ∧ eK1 u = eK2 u := fun u =>
          hExtInj (congrFun (congrArg (fun p => p.2.2) heq) u)
        refine Prod.ext (Prod.ext hx.1 (Prod.ext hy.1 (funext fun u => (hK u).1)))
          (Prod.ext hx.2 (Prod.ext hy.2 (funext fun u => (hK u).2)))
      · intro tp' htp'
        simp only [goodPrefSet, Finset.mem_filter, Finset.mem_univ, true_and] at htp'
        let splitPref (b' : ℕ) (pt : PrefTrace k h b' (s + 1)) : PrefTrace k h b' s × Bool :=
          ((pt.1, fun i => pt.2 ⟨i.val, by omega⟩), pt.2 ⟨s + b', by omega⟩)
        have hsplitEq : ∀ (b' : ℕ) (pt : PrefTrace k h b' (s + 1)),
            extPref k h b' s (splitPref b' pt).1 (splitPref b' pt).2 = pt := by
          intro b' pt
          apply Prod.ext
          · rfl
          · funext i
            dsimp [extPref, splitPref]
            split_ifs with hi
            · rfl
            · exact congrArg pt.2 (Fin.ext (by dsimp; omega))
        let z : TuplePref k r h t s × (Bool × Bool × (Fin t → Bool)) :=
          (((splitPref (4 * r) tp'.1).1, (splitPref (6 * r) tp'.2.1).1, fun u => (splitPref (bKey r) (tp'.2.2 u)).1),
           ((splitPref (4 * r) tp'.1).2, (splitPref (6 * r) tp'.2.1).2, fun u => (splitPref (bKey r) (tp'.2.2 u)).2))
        have hsz : stepPair z = tp' :=
          Prod.ext (hsplitEq (4 * r) tp'.1)
            (Prod.ext (hsplitEq (6 * r) tp'.2.1) (funext fun u => hsplitEq (bKey r) (tp'.2.2 u)))
        refine ⟨z, ?_, hsz⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hg := htp'.1
        have he := htp'.2
        have hsg := hstepGood z
        have hse := hstepEnd z
        rw [hsz] at hsg hse
        rw [hsg, Bool.and_eq_true] at hg
        rw [hse] at he
        exact ⟨hg.1, hg.2, he⟩
    rw [hbijStep]
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ.filter (fun z : TuplePref k r h t s × (Bool × Bool × (Fin t → Bool)) =>
        tupleGood masks a b z.1 = true ∧ transValid masks a b s (transOfPair z) = true ∧
        transDst (transOfPair z) = cell'))
      (t := Finset.univ.filter (fun tr : TransT k r h t => transDst tr = cell'))
      (g := transOfPair) (f := fun _ => (1 : ℕ))
      (fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2.2.2⟩)
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hfib
    rw [← hfib]
    apply Finset.sum_congr rfl
    intro tr htr
    have htrDst : transDst tr = cell' := (Finset.mem_filter.mp htr).2
    by_cases hval : transValid masks a b s tr = true
    · simp only [hval, ↓reduceIte]
      rw [dpVal_eq_card_goodPref k r h t masks a b s (transSrc tr)]
      have hcardEq : (Finset.univ.filter (fun z : TuplePref k r h t s × (Bool × Bool × (Fin t → Bool)) =>
          (tupleGood masks a b z.1 = true ∧ transValid masks a b s (transOfPair z) = true ∧
            transDst (transOfPair z) = cell') ∧ transOfPair z = tr)).card =
          ∑ tp ∈ goodPrefSet k r h t masks a b s (transSrc tr),
            (Finset.univ.filter (fun eK : Fin t → Bool =>
              histOf (fun u => (endState k h (bKey r) s (tp.2.2 u), eK u)) = tr.2.2)).card := by
        rw [← Finset.card_sigma]
        symm
        apply Finset.card_bij
          (fun (x : Σ tp : TuplePref k r h t s, Fin t → Bool) _ => (x.1, (tr.1.2, tr.2.1.2, x.2)))
        · intro x hx
          rcases Finset.mem_sigma.mp hx with ⟨h1, h2⟩
          simp only [goodPrefSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          have htrEq : transOfPair (x.1, (tr.1.2, tr.2.1.2, x.2)) = tr := by
            unfold transOfPair
            have hx1 : endState k h (4 * r) s x.1.1 = tr.1.1 := congrArg Prod.fst h1.2
            have hy1 : endState k h (6 * r) s x.1.2.1 = tr.2.1.1 := congrArg (fun p => p.2.1) h1.2
            exact Prod.ext (Prod.ext hx1 rfl) (Prod.ext (Prod.ext hy1 rfl) h2)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, htrEq, hval]
          exact ⟨⟨h1.1, htrDst⟩, trivial⟩
        · intro x1 _ x2 _ heq
          have h1 : x1.1 = x2.1 := congrArg Prod.fst heq
          have h2 : x1.2 = x2.2 := congrArg (fun p => p.2.2.2) heq
          cases x1; cases x2; simp at h1 h2; subst h1; subst h2; rfl
        · intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
          rcases hz with ⟨⟨hgz, _, _⟩, htz⟩
          have hsrc : tupleEnd z.1 = transSrc tr := by
            rw [← htz]
            unfold tupleEnd transSrc transOfPair
            exact Prod.ext rfl (Prod.ext rfl (histSrc_histOf _ _).symm)
          have hK : histOf (fun u => (endState k h (bKey r) s (z.1.2.2 u), z.2.2.2 u)) = tr.2.2 :=
            congrArg (fun p => p.2.2) htz
          have hex : z.2.1 = tr.1.2 := congrArg (fun p => p.1.2) htz
          have hey : z.2.2.1 = tr.2.1.2 := congrArg (fun p => p.2.1.2) htz
          refine ⟨⟨z.1, z.2.2.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgz, hsrc⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK⟩⟩, ?_⟩
          rcases z with ⟨tp, ex, ey, eK⟩
          dsimp at hex hey
          rw [hex, hey]
      rw [Finset.filter_filter]
      have hcardEq' : (Finset.univ.filter (fun z : TuplePref k r h t s × (Bool × Bool × (Fin t → Bool)) =>
          (tupleGood masks a b z.1 = true ∧ transValid masks a b s (transOfPair z) = true ∧
            transDst (transOfPair z) = cell') ∧ transOfPair z = tr)).card =
          (goodPrefSet k r h t masks a b s (transSrc tr)).card * splitWeight tr.2.2 := by
        rw [hcardEq]
        have hconst : ∀ tp ∈ goodPrefSet k r h t masks a b s (transSrc tr),
            (Finset.univ.filter (fun eK : Fin t → Bool =>
              histOf (fun u => (endState k h (bKey r) s (tp.2.2 u), eK u)) = tr.2.2)).card =
            splitWeight tr.2.2 := by
          intro tp htp
          dsimp [goodPrefSet] at htp
          have hend := (Finset.mem_filter.mp htp).2.2
          have hsrc : histSrc tr.2.2 = histOf (fun u => endState k h (bKey r) s (tp.2.2 u)) :=
            (congrArg (fun p => p.2.2) hend).symm
          exact card_split_fiber _ tr.2.2 hsrc
        rw [Finset.sum_congr rfl hconst]
        simp [Finset.sum_const, smul_eq_mul]
      exact hcardEq'.symm
    · have hvalf : transValid masks a b s tr = false := Bool.eq_false_iff.mpr hval
      simp only [hvalf, Bool.false_eq_true, ↓reduceIte, zero_mul]
      rw [Finset.filter_filter]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z _ ⟨⟨_, hv, _⟩, htz⟩
      rw [htz] at hv
      exact hval hv

lemma card_tupleGood_le {k r h t s : ℕ} (hh0 : 0 < h) (hh : h ≤ k) (hs : s ≤ h)
    (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) :
    (Finset.univ.filter (fun tp : TuplePref k r h t s => tupleGood masks a b tp = true)).card ≤
      2 ^ ((t + 2) * k) := by
  let SX := Finset.univ.filter (fun pt : PrefTrace k h (4 * r) s => prefPinOK k h (4 * r) s pt = true)
  let SY := Finset.univ.filter (fun pt : PrefTrace k h (6 * r) s => prefPinOK k h (6 * r) s pt = true)
  let SK1 := Finset.univ.filter (fun pt : PrefTrace k h (bKey r) s => prefPinOK k h (bKey r) s pt = true)
  let SK := Fintype.piFinset (fun _ : Fin t => SK1)
  have hsub : Finset.univ.filter (fun tp : TuplePref k r h t s => tupleGood masks a b tp = true) ⊆
      SX ×ˢ (SY ×ˢ SK) := by
    intro tp htp
    have hg := (Finset.mem_filter.mp htp).2
    unfold tupleGood at hg
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at hg
    rcases hg with ⟨⟨⟨hx, hy⟩, hK⟩, _⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩,
      Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩,
        Fintype.mem_piFinset.mpr (fun u => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK u⟩)⟩⟩
  calc (Finset.univ.filter (fun tp : TuplePref k r h t s => tupleGood masks a b tp = true)).card
      ≤ (SX ×ˢ (SY ×ˢ SK)).card := Finset.card_le_card hsub
    _ = SX.card * (SY.card * SK.card) := by rw [Finset.card_product, Finset.card_product]
    _ = SX.card * (SY.card * SK1.card ^ t) := by
        simp only [SK, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ 2 ^ k * (2 ^ k * (2 ^ k) ^ t) :=
        Nat.mul_le_mul (card_prefPinOK_le hh0 hh hs)
          (Nat.mul_le_mul (card_prefPinOK_le hh0 hh hs)
            (Nat.pow_le_pow_left (card_prefPinOK_le hh0 hh hs) t))
    _ = 2 ^ ((t + 2) * k) := by
        rw [← pow_mul, Nat.mul_comm k t, ← pow_add, ← pow_add]
        congr 1; ring

lemma dpVal_le {k r h t s : ℕ} (hh0 : 0 < h) (hh : h ≤ k) (hs : s ≤ h)
    (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) (cell : CellT k r h t) :
    dpVal k r h t masks a b s cell ≤ 2 ^ ((t + 2) * k) := by
  rw [dpVal_eq_card_goodPref]
  have hsub : goodPrefSet k r h t masks a b s cell ⊆
      Finset.univ.filter (fun tp : TuplePref k r h t s => tupleGood masks a b tp = true) := by
    intro tp htp
    dsimp [goodPrefSet] at htp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp htp).2.1⟩
  exact (Finset.card_le_card hsub).trans (card_tupleGood_le hh0 hh hs masks a b)

lemma dpVal_sum_eq_card {k r h t : ℕ} (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) (s : ℕ) :
    ∑ cell : CellT k r h t, dpVal k r h t masks a b s cell =
      (Finset.univ.filter (fun tp : TuplePref k r h t s => tupleGood masks a b tp = true)).card := by
  have h1 := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun tp : TuplePref k r h t s => tupleGood masks a b tp = true))
    (t := (Finset.univ : Finset (CellT k r h t)))
    (g := tupleEnd) (f := fun _ => (1 : ℕ))
    (fun _ _ => Finset.mem_univ _)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h1
  rw [← h1]
  apply Finset.sum_congr rfl
  intro cell _
  rw [dpVal_eq_card_goodPref]
  unfold goodPrefSet
  rw [Finset.filter_filter]

lemma dpVal_term_lt {k r h t s : ℕ} (hh0 : 0 < h) (hh : h ≤ k) (hs : s < h)
    (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) (tr : TransT k r h t) :
    (if transValid masks a b s tr then dpVal k r h t masks a b s (transSrc tr) else 0) *
        splitWeight tr.2.2 < 2 ^ ((t + 2) * k + 1) := by
  have hle : (if transValid masks a b s tr then dpVal k r h t masks a b s (transSrc tr) else 0) *
      splitWeight tr.2.2 ≤ dpVal k r h t masks a b (s + 1) (transDst tr) := by
    dsimp [dpVal]
    exact Finset.single_le_sum
      (f := fun tr' : TransT k r h t =>
        (if transValid masks a b s tr' then dpVal k r h t masks a b s (transSrc tr') else 0) *
          splitWeight tr'.2.2)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ tr, rfl⟩)
  exact lt_of_le_of_lt (hle.trans (dpVal_le hh0 hh (by omega) masks a b (transDst tr)))
    (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _))

lemma local_run_eq {k r h : ℕ} (hh : h ≤ k)
    (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key name : Fin (2 ^ k))
    (s : ℕ) (hs : s < h) :
    let q0N : ℤ := ((k - h : ℕ) : ℤ) + lName r col
    let q0K : ℤ := ((k - h : ℕ) : ℤ) + lKey r
    let trN := extractTrace k h (bName r col) q0N name
    let trK := extractTrace k h (bKey r) q0K key
    (runN k r masks col key.val name.val).testBit (k - h + s) =
      srun r col (winExt (lKey r) (prefWin k h (bKey r) h trK s hs))
        (winExt (lName r col) (prefWin k h (bName r col) h trN s hs))
        (fun j q => cbit k (masks j).val (((k - h + s : ℕ) : ℤ) + q)) r 0 := by
  intro q0N q0K trN trK
  have hk : 0 < k := by omega
  have hsite_lt : k - h + s < k := by omega
  have h1 : (runN k r masks col key.val name.val).testBit (k - h + s) =
      cbit k (runPrefix k r masks col key.val name.val r) ((k - h + s : ℕ) : ℤ) := by
    unfold runN cbit
    rw [cidx_nat hsite_lt]
  rw [h1, cbit_runPrefix hk masks col key.isLt name.isLt]
  have htr := srun_translate r col (cbit k key.val) (cbit k name.val)
    (fun j => cbit k (masks j).val) ((k - h + s : ℕ) : ℤ) r 0
  rw [Int.add_zero] at htr
  rw [← htr]
  apply srun_local r col
    (fun q => cbit k key.val (((k - h + s : ℕ) : ℤ) + q))
    (winExt (lKey r) (prefWin k h (bKey r) h trK s hs))
    (fun q => cbit k name.val (((k - h + s : ℕ) : ℤ) + q))
    (winExt (lName r col) (prefWin k h (bName r col) h trN s hs))
    (fun j q => cbit k (masks j).val (((k - h + s : ℕ) : ℤ) + q))
  · intro q hq1 hq2
    rw [winExt_eq (lName r col) _ q hq1 hq2]
    dsimp [prefWin, trN, extractTrace, q0N]
    congr 1; omega
  · intro q hq1 hq2
    rw [winExt_eq (lKey r) _ q hq1 hq2]
    dsimp [prefWin, trK, extractTrace, q0K]
    congr 1; omega
  · exact le_rfl
  · simp
  · simp

lemma moment_eq_dpVal_sum_shift {k r h t : ℕ} (hh0 : 0 < h) (hh : h ≤ k)
    (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) :
    let U := (k - (h + 4 * r)) + (k - (h + 6 * r)) + t * (k - (h + bKey r))
    momentOf k r h t masks a b =
      (∑ cell : CellT k r h t, dpVal k r h t masks a b h cell) * 2 ^ U := by
  intro U
  have hk : 0 < k := by omega
  let q0X : ℤ := ((k - h : ℕ) : ℤ) + lName r false
  let q0Y : ℤ := ((k - h : ℕ) : ℤ) + lName r true
  let q0K : ℤ := ((k - h : ℕ) : ℤ) + lKey r
  let rawGood (z : Fin (2 ^ k) × Fin (2 ^ k) × (Fin t → Fin (2 ^ k))) : Prop :=
    ∀ u : Fin t,
      (runN k r masks false (z.2.2 u).val z.1.val >>> (k - h)) = a.val ∧
      (runN k r masks true (z.2.2 u).val z.2.1.val >>> (k - h)) = b.val
  have hmomRaw : momentOf k r h t masks a b =
      (Finset.univ.filter (fun z : Fin (2 ^ k) × Fin (2 ^ k) × (Fin t → Fin (2 ^ k)) =>
        rawGood z)).card := by
    unfold momentOf numOf
    have hpow : ∀ x y : Fin (2 ^ k),
        ((Finset.univ.filter (fun key : Fin (2 ^ k) =>
          (runN k r masks false key.val x.val >>> (k - h)) = a.val ∧
          (runN k r masks true key.val y.val >>> (k - h)) = b.val)).card) ^ t =
        (Finset.univ.filter (fun K : Fin t → Fin (2 ^ k) =>
          ∀ u : Fin t,
            (runN k r masks false (K u).val x.val >>> (k - h)) = a.val ∧
            (runN k r masks true (K u).val y.val >>> (k - h)) = b.val)).card := by
      intro x y
      let S := Finset.univ.filter (fun key : Fin (2 ^ k) =>
        (runN k r masks false key.val x.val >>> (k - h)) = a.val ∧
        (runN k r masks true key.val y.val >>> (k - h)) = b.val)
      have h1 : (Fintype.piFinset (fun _ : Fin t => S)).card = S.card ^ t := by
        simp [Fintype.card_piFinset]
      rw [← h1]
      congr 1; ext K
      simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and, S]
    simp_rw [hpow]
    have hsum1 : ∑ x : Fin (2 ^ k), ∑ y : Fin (2 ^ k),
        (Finset.univ.filter (fun K : Fin t → Fin (2 ^ k) => rawGood (x, y, K))).card =
        ∑ p : Fin (2 ^ k) × Fin (2 ^ k),
          (Finset.univ.filter (fun K : Fin t → Fin (2 ^ k) => rawGood (p.1, p.2, K))).card := by
      rw [Fintype.sum_prod_type]
    rw [hsum1]
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ.filter (fun z : Fin (2 ^ k) × Fin (2 ^ k) × (Fin t → Fin (2 ^ k)) => rawGood z))
      (t := (Finset.univ : Finset (Fin (2 ^ k) × Fin (2 ^ k))))
      (g := fun z => (z.1, z.2.1)) (f := fun _ => (1 : ℕ))
      (fun _ _ => Finset.mem_univ _)
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hfib
    rw [← hfib]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.card_bij (fun K _ => (p.1, p.2, K))
    · intro K hK
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK ⊢
      exact ⟨hK, trivial⟩
    · intro K1 _ K2 _ heq
      exact congrArg (fun z => z.2.2) heq
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rcases z with ⟨x, y, K⟩
      rcases hz with ⟨hg, hxy⟩
      rcases Prod.mk.inj hxy with ⟨rfl, rfl⟩
      exact ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩, rfl⟩
  let extTup : Fin (2 ^ k) × Fin (2 ^ k) × (Fin t → Fin (2 ^ k)) → TuplePref k r h t h :=
    fun ⟨x, y, K⟩ =>
      (extractTrace k h (4 * r) q0X x,
       extractTrace k h (6 * r) q0Y y,
       fun u => extractTrace k h (bKey r) q0K (K u))
  have hraw_iff_good : ∀ z, rawGood z ↔ tupleGood masks a b (extTup z) = true := by
    rintro ⟨x, y, K⟩
    dsimp [rawGood, tupleGood, extTup]
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies]
    have hpx : prefPinOK k h (4 * r) h (extractTrace k h (4 * r) q0X x) = true :=
      pinOK_extractTrace hk q0X x
    have hpy : prefPinOK k h (6 * r) h (extractTrace k h (6 * r) q0Y y) = true :=
      pinOK_extractTrace hk q0Y y
    have hpK : ∀ u : Fin t, prefPinOK k h (bKey r) h (extractTrace k h (bKey r) q0K (K u)) = true :=
      fun u => pinOK_extractTrace hk q0K (K u)
    simp only [hpx, hpy, hpK, implies_true, true_and]
    constructor
    · intro hall j u
      rcases hall u with ⟨hrow, hcol⟩
      have hltR : runN k r masks false (K u).val x.val < 2 ^ k :=
        runPrefix_lt (r := r) masks false (K u).val x.val r x.isLt
      have hltC : runN k r masks true (K u).val y.val < 2 ^ k :=
        runPrefix_lt (r := r) masks true (K u).val y.val r y.isLt
      have hbr := (shr_eq_iff hltR a hh).mp hrow j.val j.isLt
      have hbc := (shr_eq_iff hltC b hh).mp hcol j.val j.isLt
      have hlr := local_run_eq (r := r) hh masks false (K u) x j.val j.isLt
      have hlc := local_run_eq (r := r) hh masks true (K u) y j.val j.isLt
      refine ⟨?_, ?_⟩
      · unfold rowLocalOK; rw [decide_eq_true_eq]
        exact hlr.symm.trans hbr
      · unfold colLocalOK; rw [decide_eq_true_eq]
        exact hlc.symm.trans hbc
    · intro hall u
      have hltR : runN k r masks false (K u).val x.val < 2 ^ k :=
        runPrefix_lt (r := r) masks false (K u).val x.val r x.isLt
      have hltC : runN k r masks true (K u).val y.val < 2 ^ k :=
        runPrefix_lt (r := r) masks true (K u).val y.val r y.isLt
      refine ⟨(shr_eq_iff hltR a hh).mpr ?_, (shr_eq_iff hltC b hh).mpr ?_⟩
      · intro s hs
        have h1 := (hall ⟨s, hs⟩ u).1
        unfold rowLocalOK at h1; rw [decide_eq_true_eq] at h1
        rw [local_run_eq (r := r) hh masks false (K u) x s hs]
        exact h1
      · intro s hs
        have h1 := (hall ⟨s, hs⟩ u).2
        unfold colLocalOK at h1; rw [decide_eq_true_eq] at h1
        rw [local_run_eq (r := r) hh masks true (K u) y s hs]
        exact h1
  rw [hmomRaw, dpVal_sum_eq_card]
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun z : Fin (2 ^ k) × Fin (2 ^ k) × (Fin t → Fin (2 ^ k)) => rawGood z))
    (t := Finset.univ.filter (fun tp : TuplePref k r h t h => tupleGood masks a b tp = true))
    (g := extTup) (f := fun _ => (1 : ℕ))
    (fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hraw_iff_good z).mp (Finset.mem_filter.mp hz).2⟩)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hfib
  rw [← hfib]
  have hconst : ∀ tp ∈ Finset.univ.filter (fun tp : TuplePref k r h t h => tupleGood masks a b tp = true),
      ((Finset.univ.filter (fun z => rawGood z)).filter (fun z => extTup z = tp)).card = 2 ^ U := by
    intro tp htp
    have hgtp : tupleGood masks a b tp = true := (Finset.mem_filter.mp htp).2
    have hfiltEq : (Finset.univ.filter (fun z => rawGood z)).filter (fun z => extTup z = tp) =
        Finset.univ.filter (fun z => extTup z = tp) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact h.2
      · intro heq; exact ⟨(hraw_iff_good z).mpr (by rw [heq]; exact hgtp), heq⟩
    rw [hfiltEq]
    unfold tupleGood at hgtp
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at hgtp
    rcases hgtp with ⟨⟨⟨hpx, hpy⟩, hpK⟩, _⟩
    let FX := Finset.univ.filter (fun x : Fin (2 ^ k) => extractTrace k h (4 * r) q0X x = tp.1)
    let FY := Finset.univ.filter (fun y : Fin (2 ^ k) => extractTrace k h (6 * r) q0Y y = tp.2.1)
    let FK := Fintype.piFinset (fun u : Fin t =>
      Finset.univ.filter (fun key : Fin (2 ^ k) => extractTrace k h (bKey r) q0K key = tp.2.2 u))
    have hprodEq : Finset.univ.filter (fun z => extTup z = tp) = FX ×ˢ (FY ×ˢ FK) := by
      rcases tp with ⟨tpx, tpy, tpK⟩
      ext ⟨x, y, K⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, extTup, Prod.mk.injEq,
        Finset.mem_product, FX, FY, FK, Fintype.mem_piFinset, funext_iff]
    rw [hprodEq, Finset.card_product, Finset.card_product,
      card_fiber_extractTrace hh0 hh q0X tp.1 hpx,
      card_fiber_extractTrace hh0 hh q0Y tp.2.1 hpy]
    have hFKcard : FK.card = (2 ^ (k - (h + bKey r))) ^ t := by
      dsimp [FK]
      rw [Fintype.card_piFinset]
      rw [Finset.prod_congr rfl (fun u _ => card_fiber_extractTrace hh0 hh q0K (tp.2.2 u) (hpK u))]
      simp
    rw [hFKcard, ← pow_mul, Nat.mul_comm (k - (h + bKey r)) t, ← Nat.mul_assoc, ← pow_add, ← pow_add]
  rw [Finset.sum_congr rfl hconst]
  simp only [Finset.sum_const, smul_eq_mul]

end
end TrackDP

section Branch2

noncomputable section
open Classical

lemma sum_map_toList {α : Type*} (s : Finset α) (f : α → ℕ) :
    (s.toList.map f).sum = ∑ a ∈ s, f a := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
  rfl

lemma le_choose_add_sub_one {a t : ℕ} (ha : 1 ≤ a) (ht : 1 ≤ t) :
    a ≤ Nat.choose (t + a - 1) t := by
  induction t with
  | zero => omega
  | succ t ih =>
    cases t with
    | zero =>
      have h1 : 1 + a - 1 = a := by omega
      rw [h1, Nat.choose_one_right]
    | succ t =>
      have ih' := ih (by omega)
      have h1 : t + 1 + 1 + a - 1 = (t + 1 + a - 1) + 1 := by omega
      rw [h1, Nat.choose_succ_succ]
      omega

lemma card_trackState (k h b : ℕ) :
    Fintype.card (TrackState k h b) = 2 ^ (b + seam k h b) := by
  dsimp [TrackState]
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_fin, ← pow_add, Nat.add_comm]

lemma card_transT (k r h t : ℕ) :
    Fintype.card (TransT k r h t) = scanVal k r h t := by
  have hQX : Fintype.card (TrackState k h (4 * r) × Bool) = 2 ^ (4 * r + seam k h (4 * r) + 1) := by
    rw [Fintype.card_prod (α := TrackState k h (4 * r)), card_trackState, Fintype.card_bool, pow_succ]
  have hQY : Fintype.card (TrackState k h (6 * r) × Bool) = 2 ^ (6 * r + seam k h (6 * r) + 1) := by
    rw [Fintype.card_prod (α := TrackState k h (6 * r)), card_trackState, Fintype.card_bool, pow_succ]
  have hQK : Fintype.card (TrackState k h (bKey r) × Bool) = 2 ^ (bKey r + seam k h (bKey r) + 1) := by
    rw [Fintype.card_prod (α := TrackState k h (bKey r)), card_trackState, Fintype.card_bool, pow_succ]
  have hQK_pos : 0 < Fintype.card (TrackState k h (bKey r) × Bool) := by
    rw [hQK]; exact Nat.two_pow_pos _
  have hsplit : Fintype.card (TransT k r h t) =
      Fintype.card (TrackState k h (4 * r) × Bool) *
      (Fintype.card (TrackState k h (6 * r) × Bool) *
       Fintype.card (Hist (TrackState k h (bKey r) × Bool) t)) :=
    (Fintype.card_prod _ _).trans (congrArg _ (Fintype.card_prod _ _))
  rw [hsplit, hQX, hQY, card_hist _ hQK_pos t, hQK, ← Nat.mul_assoc, ← pow_add]
  unfold scanVal AVal
  congr 2; omega

lemma card_cellT_le_scan (k r h t : ℕ) :
    Fintype.card (CellT k r h t) ≤ scanVal k r h t := by
  rw [← card_transT k r h t]
  have hL : Fintype.card (CellT k r h t) =
      Fintype.card (TrackState k h (4 * r)) *
      (Fintype.card (TrackState k h (6 * r)) * Fintype.card (Hist (TrackState k h (bKey r)) t)) :=
    (Fintype.card_prod _ _).trans (congrArg _ (Fintype.card_prod _ _))
  have hR : Fintype.card (TransT k r h t) =
      Fintype.card (TrackState k h (4 * r) × Bool) *
      (Fintype.card (TrackState k h (6 * r) × Bool) *
       Fintype.card (Hist (TrackState k h (bKey r) × Bool) t)) :=
    (Fintype.card_prod _ _).trans (congrArg _ (Fintype.card_prod _ _))
  rw [hL, hR]
  have h1 : Fintype.card (TrackState k h (4 * r)) ≤ Fintype.card (TrackState k h (4 * r) × Bool) := by
    rw [Fintype.card_prod (α := TrackState k h (4 * r)), Fintype.card_bool]; omega
  have h2 : Fintype.card (TrackState k h (6 * r)) ≤ Fintype.card (TrackState k h (6 * r) × Bool) := by
    rw [Fintype.card_prod (α := TrackState k h (6 * r)), Fintype.card_bool]; omega
  have h3 := card_hist_le_prod (TrackState k h (bKey r)) t
  exact Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)

lemma card_rowWin_le_scan {k r h t : ℕ} (ht : 0 < t) :
    Fintype.card ((Fin (4 * r + 1) → Bool) × (Fin (bKey r + 1) → Bool)) ≤ scanVal k r h t := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_fin]
  unfold scanVal
  have h1 : 2 ^ (4 * r + 1) ≤ 2 ^ (10 * r + seam k h (4 * r) + seam k h (6 * r) + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ (bKey r + 1) ≤ AVal k r h := by
    unfold AVal
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : AVal k r h ≤ Nat.choose (t + AVal k r h - 1) t :=
    le_choose_add_sub_one (Nat.one_le_pow _ 2 (by omega)) ht
  exact Nat.mul_le_mul h1 (h2.trans h3)

lemma card_colWin_le_scan {k r h t : ℕ} (ht : 0 < t) :
    Fintype.card ((Fin (6 * r + 1) → Bool) × (Fin (bKey r + 1) → Bool)) ≤ scanVal k r h t := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_fin]
  unfold scanVal
  have h1 : 2 ^ (6 * r + 1) ≤ 2 ^ (10 * r + seam k h (4 * r) + seam k h (6 * r) + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ (bKey r + 1) ≤ AVal k r h := by
    unfold AVal
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : AVal k r h ≤ Nat.choose (t + AVal k r h - 1) t :=
    le_choose_add_sub_one (Nat.one_le_pow _ 2 (by omega)) ht
  exact Nat.mul_le_mul h1 (h2.trans h3)

lemma rowLocalOKG {k r h : ℕ} (hh : h ≤ k) {A : Set (Sig (wiresIn k r h))}
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) (hIn : inputSet k r h ⊆ A)
    (s : ℕ) (hs : s < h) (xWin : Fin (4 * r + 1) → Bool) (kWin : Fin (bKey r + 1) → Bool) :
    Build A
      {fun v => rowLocalOK k r h (decMasks k r h v) (decA k r h v) s xWin kWin}
      (250 * (r + 1) ^ 2 + 5) := by
  have hk : 0 < k := by omega
  let msSig : ℕ → ℤ → Sig (wiresIn k r h) := fun j q v =>
    cbit k (decMasks k r h v j).val (((k - h + s : ℕ) : ℤ) + q)
  have hms : ∀ j < 2 * r, ∀ q : ℤ, msSig j q ∈ A := fun j hj q =>
    hIn (decMasks_bit_mem k r h hj (cidx_lt hk _))
  have hEval := evalLocalSrunG r false kWin xWin msSig h0 h1 hms
  let outS : Sig (wiresIn k r h) := fun v =>
    srun r false (winExt (lKey r) kWin) (winExt (lName r false) xWin)
      (fun j q => msSig j q v) r 0
  have hAbit : (fun v => (decA k r h v).val.testBit s) ∈ A ∪ {outS} :=
    Or.inl (hIn (decA_bit_mem k r h hs))
  have hXnor : Build (A ∪ {outS}) {fun v => decide (outS v = (decA k r h v).val.testBit s)} 5 :=
    xnorG (Or.inr rfl) hAbit
  exact seqRight hEval hXnor

lemma colLocalOKG {k r h : ℕ} (hh : h ≤ k) {A : Set (Sig (wiresIn k r h))}
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) (hIn : inputSet k r h ⊆ A)
    (s : ℕ) (hs : s < h) (yWin : Fin (6 * r + 1) → Bool) (kWin : Fin (bKey r + 1) → Bool) :
    Build A
      {fun v => colLocalOK k r h (decMasks k r h v) (decB k r h v) s yWin kWin}
      (250 * (r + 1) ^ 2 + 5) := by
  have hk : 0 < k := by omega
  let msSig : ℕ → ℤ → Sig (wiresIn k r h) := fun j q v =>
    cbit k (decMasks k r h v j).val (((k - h + s : ℕ) : ℤ) + q)
  have hms : ∀ j < 2 * r, ∀ q : ℤ, msSig j q ∈ A := fun j hj q =>
    hIn (decMasks_bit_mem k r h hj (cidx_lt hk _))
  have hEval := evalLocalSrunG r true kWin yWin msSig h0 h1 hms
  let outS : Sig (wiresIn k r h) := fun v =>
    srun r true (winExt (lKey r) kWin) (winExt (lName r true) yWin)
      (fun j q => msSig j q v) r 0
  have hBbit : (fun v => (decB k r h v).val.testBit s) ∈ A ∪ {outS} :=
    Or.inl (hIn (decB_bit_mem k r h hs))
  have hXnor : Build (A ∪ {outS}) {fun v => decide (outS v = (decB k r h v).val.testBit s)} 5 :=
    xnorG (Or.inr rfl) hBbit
  exact seqRight hEval hXnor

lemma dpStepG {k r h t : ℕ} (hh0 : 0 < h) (hh : h ≤ k) (ht : 0 < t)
    {A : Set (Sig (wiresIn k r h))}
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) (hIn : inputSet k r h ⊆ A)
    (s : ℕ) (hs : s < h)
    (hPrev : ∀ cell : CellT k r h t,
      wordBits ((t + 2) * k + 1)
        (fun v => dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) s cell) ⊆ A) :
    let W := (t + 2) * k + 1
    let stepCost := scanVal k r h t * (500 * (r + 1) ^ 2 + 10 + 2 * t + W + (t + 1) * (12 * W) + 12 * W)
    Build A
      {g | ∃ cell' : CellT k r h t, g ∈ wordBits W
        (fun v => dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) (s + 1) cell')}
      stepCost := by
  intro W stepCost
  let rowList := (Finset.univ : Finset ((Fin (4 * r + 1) → Bool) × (Fin (bKey r + 1) → Bool))).toList
  let colList := (Finset.univ : Finset ((Fin (6 * r + 1) → Bool) × (Fin (bKey r + 1) → Bool))).toList
  let rowSig (p : (Fin (4 * r + 1) → Bool) × (Fin (bKey r + 1) → Bool)) : Sig (wiresIn k r h) :=
    fun v => rowLocalOK k r h (decMasks k r h v) (decA k r h v) s p.1 p.2
  let colSig (p : (Fin (6 * r + 1) → Bool) × (Fin (bKey r + 1) → Bool)) : Sig (wiresIn k r h) :=
    fun v => colLocalOK k r h (decMasks k r h v) (decB k r h v) s p.1 p.2
  let SRow := {f : Sig (wiresIn k r h) | ∃ p ∈ rowList, f = rowSig p}
  let SCol := {f : Sig (wiresIn k r h) | ∃ p ∈ colList, f = colSig p}
  have hRowAll : Build A SRow (scanVal k r h t * (250 * (r + 1) ^ 2 + 5)) := by
    have hb := listBuild (A := A) rowList rowSig (250 * (r + 1) ^ 2 + 5)
      (fun p _ => rowLocalOKG hh h0 h1 hIn s hs p.1 p.2)
    refine relax hb le_rfl le_rfl ?_
    have hlen : rowList.length ≤ scanVal k r h t := by
      dsimp [rowList]
      rw [Finset.length_toList, Finset.card_univ]
      exact card_rowWin_le_scan ht
    exact Nat.mul_le_mul_right _ hlen
  have hColAll : Build (A ∪ SRow) SCol (scanVal k r h t * (250 * (r + 1) ^ 2 + 5)) := by
    have hb := listBuild (A := A ∪ SRow) colList colSig (250 * (r + 1) ^ 2 + 5)
      (fun p _ => colLocalOKG hh (Or.inl h0) (Or.inl h1) (hIn.trans Set.subset_union_left) s hs p.1 p.2)
    refine relax hb le_rfl le_rfl ?_
    have hlen : colList.length ≤ scanVal k r h t := by
      dsimp [colList]
      rw [Finset.length_toList, Finset.card_univ]
      exact card_colWin_le_scan ht
    exact Nat.mul_le_mul_right _ hlen
  let ARC := A ∪ (SRow ∪ SCol)
  let transList := (Finset.univ : Finset (TransT k r h t)).toList
  have htransLen : transList.length = scanVal k r h t := by
    dsimp [transList]
    rw [Finset.length_toList, Finset.card_univ, card_transT]
  let termSig (tr : TransT k r h t) : NatSig (wiresIn k r h) := fun v =>
    (if transValid (decMasks k r h v) (decA k r h v) (decB k r h v) s tr then
      dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) s (transSrc tr) else 0) *
      splitWeight tr.2.2
  let perTransCost := 2 * t + W + (t + 1) * (12 * W)
  let STerm := {g : Sig (wiresIn k r h) | ∃ tr ∈ transList, g ∈ wordBits W (termSig tr)}
  have hTerms : Build ARC STerm (scanVal k r h t * perTransCost) := by
    have hb := listBuildSets (A := ARC) transList (fun tr => wordBits W (termSig tr)) perTransCost (fun tr _ => by
      let valSig : Sig (wiresIn k r h) := fun v =>
        transValid (decMasks k r h v) (decA k r h v) (decB k r h v) s tr
      have hVal : Build ARC {valSig} (2 * t) := by
        by_cases hpin : transPinOK s tr = true
        · let suppL := (histSupp tr.2.2).toList
          have hsuppLen : suppL.length ≤ t := by
            dsimp [suppL]; rw [Finset.length_toList]; exact histSupp_card_le tr.2.2
          let pairS (p : TrackState k h (bKey r) × Bool) : Sig (wiresIn k r h) :=
            an (rowSig (extWin (4 * r) tr.1.1.2 tr.1.2, extWin (bKey r) p.1.2 p.2))
               (colSig (extWin (6 * r) tr.2.1.1.2 tr.2.1.2, extWin (bKey r) p.1.2 p.2))
          have hPairs : Build ARC {f | ∃ p ∈ suppL, f = pairS p} suppL.length := by
            have hb1 := listBuild (A := ARC) suppL pairS 1 (fun p _ =>
              andG (A := ARC)
                (Or.inr (Or.inl ⟨_, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩))
                (Or.inr (Or.inr ⟨_, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩)))
            rwa [Nat.mul_one] at hb1
          have hAll : Build (ARC ∪ {f | ∃ p ∈ suppL, f = pairS p})
              {fun v => suppL.all (fun p => pairS p v)} suppL.length := by
            have hmem : ∀ p ∈ suppL, pairS p ∈ ARC ∪ {f | ∃ p ∈ suppL, f = pairS p} :=
              fun p hp => Or.inr ⟨p, hp, rfl⟩
            exact andListG (A := ARC ∪ {f | ∃ p ∈ suppL, f = pairS p})
              suppL pairS (Or.inl (Or.inl h1)) hmem
          have he : (fun v => suppL.all (fun p => pairS p v)) = valSig := by
            funext v
            simp only [valSig, transValid, hpin, Bool.true_and, transTestOK, suppL, pairS, an, rowSig, colSig]
          rw [he] at hAll
          refine relax (seqRight hPairs hAll) le_rfl le_rfl (by omega)
        · have he : valSig = (fun _ => false) := by
            funext v
            have hf : transPinOK s tr = false := Bool.eq_false_iff.mpr hpin
            simp [valSig, transValid, hf]
          rw [he]
          exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl h0))) le_rfl le_rfl (by omega)
      let maskedSig : NatSig (wiresIn k r h) := fun v =>
        if valSig v then dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) s (transSrc tr) else 0
      have hMask : Build (ARC ∪ {valSig}) (wordBits W maskedSig) W :=
        maskNatG W valSig
          (fun v => dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) s (transSrc tr))
          (Or.inr rfl)
          ((hPrev (transSrc tr)).trans (Set.subset_union_left.trans Set.subset_union_left))
      have hMul : Build ((ARC ∪ {valSig}) ∪ wordBits W maskedSig) (wordBits W (termSig tr))
          ((t + 1) * (12 * W)) :=
        mulConstNatG W (t + 1) (splitWeight tr.2.2) maskedSig
          (splitWeight_lt tr.2.2)
          (fun v => dpVal_term_lt hh0 hh hs (decMasks k r h v) (decA k r h v) (decB k r h v) tr)
          Set.subset_union_right
          (Or.inl (Or.inl (Or.inl h0)))
          (Or.inl (Or.inl (Or.inl h1)))
      exact relax (seqRight hVal (seqRight hMask hMul)) le_rfl le_rfl (by dsimp [perTransCost]; omega))
    rwa [htransLen] at hb
  let cellList := (Finset.univ : Finset (CellT k r h t)).toList
  have hAcc : Build (ARC ∪ STerm)
      {g | ∃ cell' ∈ cellList, g ∈ wordBits W
        (fun v => dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) (s + 1) cell')}
      (scanVal k r h t * (12 * W)) := by
    let fib (cell' : CellT k r h t) := Finset.univ.filter (fun tr : TransT k r h t => transDst tr = cell')
    have hb := listBuildSetsVar (A := ARC ∪ STerm) cellList
      (fun cell' => wordBits W
        (fun v => dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) (s + 1) cell'))
      (fun cell' => (fib cell').card * (12 * W))
      (fun cell' _ => by
        have hsub : ∀ tr ∈ (fib cell').toList, wordBits W (termSig tr) ⊆ ARC ∪ STerm :=
          fun tr _ g hg => Or.inr ⟨tr, Finset.mem_toList.mpr (Finset.mem_univ tr), hg⟩
        have hsumEq : ∀ v, dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) (s + 1) cell' =
            ((fib cell').toList.map (fun tr => termSig tr v)).sum := by
          intro v
          dsimp [dpVal, fib, termSig]
          exact (sum_map_toList _ _).symm
        have hsumB := sumListNatG (A := ARC ∪ STerm) W (fib cell').toList termSig
          (Or.inl (Or.inl h0)) (Or.inl (Or.inl h1)) hsub
          (fun v => by
            rw [← hsumEq v]
            exact lt_of_le_of_lt (dpVal_le hh0 hh (by omega) _ _ _ cell')
              (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _)))
        rw [Finset.length_toList] at hsumB
        have he : (fun v => ((fib cell').toList.map (fun tr => termSig tr v)).sum) =
            (fun v => dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) (s + 1) cell') := by
          funext v; exact (hsumEq v).symm
        rwa [he] at hsumB)
    refine relax hb le_rfl le_rfl ?_
    have hsumC : (cellList.map (fun cell' => (fib cell').card * (12 * W))).sum =
        scanVal k r h t * (12 * W) := by
      dsimp [cellList]
      rw [sum_map_toList, ← Finset.sum_mul]
      congr 1
      have h1 := Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (TransT k r h t)))
        (t := (Finset.univ : Finset (CellT k r h t)))
        (g := transDst) (f := fun _ => (1 : ℕ))
        (fun _ _ => Finset.mem_univ _)
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, card_transT] at h1
      exact h1
    rw [hsumC]
  have hAll := seqRight (seq hRowAll hColAll) (seqRight hTerms hAcc)
  refine relax hAll le_rfl ?_ ?_
  · rintro g ⟨cell', hg⟩
    exact ⟨cell', Finset.mem_toList.mpr (Finset.mem_univ cell'), hg⟩
  · dsimp [stepCost, perTransCost]
    have heq : scanVal k r h t * (250 * (r + 1) ^ 2 + 5) + scanVal k r h t * (250 * (r + 1) ^ 2 + 5) +
        (scanVal k r h t * (2 * t + W + (t + 1) * (12 * W)) + scanVal k r h t * (12 * W)) =
        scanVal k r h t * (500 * (r + 1) ^ 2 + 10 + 2 * t + W + (t + 1) * (12 * W) + 12 * W) := by ring
    omega

lemma scanMomentG (k r h t : ℕ) (hh0 : 0 < h) (hh : h ≤ k) (ht : 0 < t) :
    let W := (t + 2) * k + 1
    Build (inputSet k r h)
      (wordBits W (fun v => momentOf k r h t (decMasks k r h v) (decA k r h v) (decB k r h v)))
      (1048576 * ((k + 1) * (r + 1) * (t + 2)) ^ 4 * scanVal k r h t) := by
  intro W
  let A0 := inputSet k r h
  have hC0 : Build A0 {fun _ => false} 1 := constG false
  have hC1 : Build (A0 ∪ {fun _ => false}) {fun _ => true} 1 := constG true
  have hConsts := seq hC0 hC1
  let AC := A0 ∪ ({fun _ => false} ∪ {fun _ => true})
  have h0AC : (fun _ : Fin (wiresIn k r h) → Bool => false) ∈ AC := Or.inr (Or.inl rfl)
  have h1AC : (fun _ : Fin (wiresIn k r h) → Bool => true) ∈ AC := Or.inr (Or.inr rfl)
  have hInAC : inputSet k r h ⊆ AC := Set.subset_union_left
  let stepCost := scanVal k r h t * (500 * (r + 1) ^ 2 + 10 + 2 * t + W + (t + 1) * (12 * W) + 12 * W)
  let dpLayer (s : ℕ) : Set (Sig (wiresIn k r h)) :=
    {g | ∃ cell : CellT k r h t, g ∈ wordBits W
      (fun v => dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) s cell)}
  have hDP : ∀ s ≤ h, Build AC (dpLayer s) (s * stepCost) := by
    intro s
    induction s with
    | zero =>
      intro _
      refine relax (idle ?_) le_rfl le_rfl (by simp)
      rintro g ⟨cell, i, _, rfl⟩
      dsimp [dpVal]
      cases hbit : (if initCellOK cell = true then baseMult cell.2.2 else 0).testBit i
      · simpa only [hbit] using h0AC
      · simpa only [hbit] using h1AC
    | succ s ih =>
      intro hs
      have hprev := ih (by omega)
      have hsubDP : ∀ cell : CellT k r h t,
          wordBits W (fun v => dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) s cell) ⊆
            AC ∪ dpLayer s :=
        fun cell g hg => Or.inr ⟨cell, hg⟩
      have hstep := dpStepG (A := AC ∪ dpLayer s) hh0 hh ht (Or.inl h0AC) (Or.inl h1AC)
        (hInAC.trans Set.subset_union_left) s (by omega) hsubDP
      refine relax (seqRight hprev hstep) le_rfl le_rfl ?_
      have heq : s * stepCost + stepCost = (s + 1) * stepCost := by ring
      exact le_of_eq heq
  have hDPh := hDP h le_rfl
  let cellList := (Finset.univ : Finset (CellT k r h t)).toList
  have hSum : Build (AC ∪ dpLayer h)
      (wordBits W (fun v => ∑ cell : CellT k r h t,
        dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) h cell))
      (scanVal k r h t * (12 * W)) := by
    have hsub : ∀ cell ∈ cellList,
        wordBits W (fun v => dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) h cell) ⊆
          AC ∪ dpLayer h :=
      fun cell _ g hg => Or.inr ⟨cell, hg⟩
    have hsumEq : ∀ v, (∑ cell : CellT k r h t,
        dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) h cell) =
        (cellList.map (fun cell => dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) h cell)).sum := by
      intro v; dsimp [cellList]; exact (sum_map_toList _ _).symm
    have hb := sumListNatG (A := AC ∪ dpLayer h) W cellList
      (fun cell v => dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) h cell)
      (Or.inl h0AC) (Or.inl h1AC) hsub
      (fun v => by
        rw [← hsumEq v, dpVal_sum_eq_card]
        exact lt_of_le_of_lt (card_tupleGood_le hh0 hh le_rfl _ _ _)
          (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _)))
    have he : (fun v => (cellList.map (fun cell =>
        dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) h cell)).sum) =
        (fun v => ∑ cell : CellT k r h t,
          dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) h cell) := by
      funext v; exact (hsumEq v).symm
    rw [he] at hb
    refine relax hb le_rfl le_rfl ?_
    have hlen : cellList.length ≤ scanVal k r h t := by
      dsimp [cellList]; rw [Finset.length_toList, Finset.card_univ]; exact card_cellT_le_scan k r h t
    exact Nat.mul_le_mul_right _ hlen
  let U := (k - (h + 4 * r)) + (k - (h + 6 * r)) + t * (k - (h + bKey r))
  let SFinal := (AC ∪ dpLayer h) ∪ wordBits W (fun v => ∑ cell : CellT k r h t,
      dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) h cell)
  have hShift : Build SFinal
      (wordBits W (fun v => momentOf k r h t (decMasks k r h v) (decA k r h v) (decB k r h v))) 0 := by
    have hsh := shiftNatG (A := SFinal) W U (fun v => ∑ cell : CellT k r h t,
      dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) h cell)
      Set.subset_union_right (Or.inl (Or.inl h0AC))
    have he : (fun v => (∑ cell : CellT k r h t,
        dpVal k r h t (decMasks k r h v) (decA k r h v) (decB k r h v) h cell) * 2 ^ U) =
        (fun v => momentOf k r h t (decMasks k r h v) (decA k r h v) (decB k r h v)) := by
      funext v; exact (moment_eq_dpVal_sum_shift hh0 hh (decMasks k r h v) (decA k r h v) (decB k r h v)).symm
    rwa [he] at hsh
  have hFull := seqRight hConsts (seqRight hDPh (seqRight hSum hShift))
  refine relax hFull le_rfl le_rfl ?_
  set M := (k + 1) * (r + 1) * (t + 2)
  set S := scanVal k r h t
  have hM1 : 1 ≤ M := Nat.mul_pos (Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos r)) (by omega)
  have hS1 : 1 ≤ S := by
    dsimp [S, scanVal]
    have h1 : 1 ≤ 2 ^ (10 * r + seam k h (4 * r) + seam k h (6 * r) + 2) := Nat.one_le_pow _ 2 (by omega)
    have hA1 : 1 ≤ AVal k r h := Nat.one_le_pow _ 2 (by omega)
    have h2 : 1 ≤ Nat.choose (t + AVal k r h - 1) t :=
      hA1.trans (le_choose_add_sub_one hA1 ht)
    exact Nat.mul_pos h1 h2
  have hk_le_M : k + 1 ≤ M := by
    dsimp [M]; calc k + 1 = (k + 1) * 1 * 1 := by ring
      _ ≤ (k + 1) * (r + 1) * (t + 2) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hr_le_M : r + 1 ≤ M := by
    dsimp [M]; calc r + 1 = 1 * (r + 1) * 1 := by ring
      _ ≤ (k + 1) * (r + 1) * (t + 2) := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (by omega)
  have ht_le_M : t + 1 ≤ M := by
    dsimp [M]; calc t + 1 ≤ 1 * 1 * (t + 2) := by omega
      _ ≤ (k + 1) * (r + 1) * (t + 2) := Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
  have hW_le_M : W ≤ M := by
    dsimp [W, M]
    have h1 : (t + 2) * k + 1 ≤ (k + 1) * (t + 2) := by
      have : (k + 1) * (t + 2) = (t + 2) * k + t + 2 := by ring
      omega
    calc (t + 2) * k + 1 ≤ (k + 1) * 1 * (t + 2) := by simpa using h1
      _ ≤ (k + 1) * (r + 1) * (t + 2) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have hM1_M2 : M ≤ M ^ 2 := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 2 := Nat.pow_le_pow_right hM1 (by omega)
  have hM1_M4 : M ≤ M ^ 4 := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by omega)
  have hM2_M4 : M ^ 2 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by omega)
  have hM3_M4 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by omega)
  have hr2 : (r + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hr_le_M 2
  have htW : (t + 1) * W ≤ M ^ 2 := by
    have : M * M = M ^ 2 := by ring
    exact (Nat.mul_le_mul ht_le_M hW_le_M).trans (le_of_eq this)
  have hInner : 500 * (r + 1) ^ 2 + 10 + 2 * t + W + (t + 1) * (12 * W) + 12 * W ≤ 550 * M ^ 2 := by
    have h1 : (t + 1) * (12 * W) = 12 * ((t + 1) * W) := by ring
    omega
  have hStepB : h * stepCost ≤ 550 * (M ^ 4 * S) := by
    dsimp [stepCost]
    have h1 : h * (S * (500 * (r + 1) ^ 2 + 10 + 2 * t + W + (t + 1) * (12 * W) + 12 * W)) =
        (h * (500 * (r + 1) ^ 2 + 10 + 2 * t + W + (t + 1) * (12 * W) + 12 * W)) * S := by ring
    rw [h1]
    have hhM : h ≤ M := by omega
    have h2 : h * (500 * (r + 1) ^ 2 + 10 + 2 * t + W + (t + 1) * (12 * W) + 12 * W) ≤
        M * (550 * M ^ 2) := Nat.mul_le_mul hhM hInner
    have h3 : M * (550 * M ^ 2) = 550 * M ^ 3 := by ring
    have h4 : 550 * M ^ 3 ≤ 550 * M ^ 4 := Nat.mul_le_mul_left 550 hM3_M4
    calc (h * (500 * (r + 1) ^ 2 + 10 + 2 * t + W + (t + 1) * (12 * W) + 12 * W)) * S
        ≤ (550 * M ^ 4) * S := Nat.mul_le_mul_right S (h2.trans (h3 ▸ h4))
      _ = 550 * (M ^ 4 * S) := by ring
  have hSumB : S * (12 * W) ≤ 12 * (M ^ 4 * S) := by
    calc S * (12 * W) = (12 * W) * S := Nat.mul_comm _ _
      _ ≤ (12 * M ^ 4) * S := Nat.mul_le_mul_right S (by omega)
      _ = 12 * (M ^ 4 * S) := by ring
  have h2B : 2 ≤ 2 * (M ^ 4 * S) := by
    have h1 : 1 ≤ M ^ 4 * S := Nat.mul_pos (Nat.one_le_pow 4 M hM1) hS1
    omega
  have hFinalEq : 1048576 * M ^ 4 * S = 1048576 * (M ^ 4 * S) := by ring
  omega

end
end Branch2

section MainBridge

noncomputable section
open Classical

def mkInput (k r h : ℕ) (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) :
    Fin (wiresIn k r h) → Bool := fun i =>
  if i.val < 2 * r * k then (masks (i.val / k)).val.testBit (i.val % k)
  else if i.val < 2 * r * k + h then a.val.testBit (i.val - 2 * r * k)
  else b.val.testBit (i.val - (2 * r * k + h))

lemma flatMap_bits_len (m k : ℕ) (f : ℕ → ℕ) :
    ((List.range m).flatMap (fun j => (List.range k).map (fun i => (f j).testBit i))).length = m * k := by
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range, List.map_const', List.sum_replicate, smul_eq_mul]

lemma flatMap_bits_getElem (m k : ℕ) (f : ℕ → ℕ) (idx : ℕ) (hidx : idx < m * k) :
    ((List.range m).flatMap (fun j => (List.range k).map (fun i => (f j).testBit i)))[idx]'(by
      rw [flatMap_bits_len]; exact hidx) = (f (idx / k)).testBit (idx % k) := by
  induction m generalizing idx with
  | zero => simp at hidx
  | succ m ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hlen1 : ((List.range m).flatMap (fun j => (List.range k).map (fun i => (f j).testBit i))).length = m * k :=
      flatMap_bits_len m k f
    by_cases hlt : idx < m * k
    · rw [List.getElem_append_left (by omega)]
      exact ih idx hlt
    · rw [List.getElem_append_right (by omega)]
      simp only [hlen1, List.getElem_map, List.getElem_range]
      have hk : 0 < k := by
        by_contra hk0
        have : k = 0 := by omega
        subst this; simp at hidx
      have hdiv : idx / k = m := by
        have h1 : idx = m * k + (idx - m * k) := by omega
        have h2 : idx - k * m < k := by
          have : (m + 1) * k = k * m + k := by ring
          omega
        rw [h1, Nat.mul_comm m k, Nat.mul_add_div hk, Nat.div_eq_of_lt h2, Nat.add_zero]
      have hmod : idx % k = idx - m * k := by
        have hdm := Nat.div_add_mod idx k
        rw [hdiv, Nat.mul_comm] at hdm
        omega
      rw [hdiv, hmod]

lemma ofFn_mkInput (k r h : ℕ) (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) :
    List.ofFn (mkInput k r h masks a b) =
      (List.range (2 * r)).flatMap (fun j => (List.range k).map (fun i => (masks j).val.testBit i)) ++
        (List.range h).map (fun i => a.val.testBit i) ++
        (List.range h).map (fun i => b.val.testBit i) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, flatMap_bits_len, List.length_map, List.length_range]
    unfold wiresIn; omega
  · intro idx h1 h2
    rw [List.getElem_ofFn]
    dsimp [mkInput]
    have hlenM : ((List.range (2 * r)).flatMap (fun j => (List.range k).map (fun i => (masks j).val.testBit i))).length =
        2 * r * k := flatMap_bits_len (2 * r) k (fun j => (masks j).val)
    have hlenA : ((List.range h).map (fun i => a.val.testBit i)).length = h := by simp
    by_cases hlt1 : idx < 2 * r * k
    · simp only [hlt1, ↓reduceIte]
      rw [List.getElem_append_left (by simp [hlenM, hlenA]; omega),
          List.getElem_append_left (by omega)]
      exact (flatMap_bits_getElem (2 * r) k (fun j => (masks j).val) idx hlt1).symm
    · simp only [hlt1, ↓reduceIte]
      by_cases hlt2 : idx < 2 * r * k + h
      · simp only [hlt2, ↓reduceIte]
        rw [List.getElem_append_left (by simp [hlenM, hlenA]; omega),
            List.getElem_append_right (by omega)]
        simp [hlenM]
      · simp only [hlt2, ↓reduceIte]
        rw [List.getElem_append_right (by simp [hlenM, hlenA]; omega)]
        simp [hlenM, hlenA]

lemma runPrefix_congr_masks {k r : ℕ} {masks1 masks2 : ℕ → Fin (2 ^ k)}
    (heq : ∀ j < 2 * r, masks1 j = masks2 j) (col : Bool) (key name : ℕ) :
    ∀ m ≤ r, runPrefix k r masks1 col key name m = runPrefix k r masks2 col key name m
  | 0, _ => rfl
  | m + 1, hm => by
    rw [runPrefix_succ, runPrefix_succ, runPrefix_congr_masks heq col key name m (by omega)]
    unfold runStep
    have hidx : (if col then r + m else m) < 2 * r := by cases col <;> simp <;> omega
    rw [heq _ hidx]

lemma dec_mkInput {k r h : ℕ} (hk : 0 < k) (masks : ℕ → Fin (2 ^ k)) (a b : Fin (2 ^ h)) :
    (∀ j < 2 * r, decMasks k r h (mkInput k r h masks a b) j = masks j) ∧
    decA k r h (mkInput k r h masks a b) = a ∧
    decB k r h (mkInput k r h masks a b) = b := by
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · rw [decMasks_testBit k r h _ hj hi]
      dsimp [mkInput]
      have hlt : j * k + i < 2 * r * k := by
        have h1 : j + 1 ≤ 2 * r := hj
        have h2 := Nat.mul_le_mul_right k h1
        rw [Nat.add_one_mul] at h2
        omega
      simp only [hlt, ↓reduceIte]
      have hdiv : (j * k + i) / k = j := by
        rw [Nat.mul_comm, Nat.mul_add_div hk, Nat.div_eq_of_lt hi, Nat.add_zero]
      have hmod : (j * k + i) % k = i := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
      rw [hdiv, hmod]
    · rw [Nat.testBit_lt_two_pow ((decMasks k r h _ j).isLt.trans_le
            (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hi))),
          Nat.testBit_lt_two_pow ((masks j).isLt.trans_le
            (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hi)))]
  · apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro s
    by_cases hs : s < h
    · rw [decA_testBit k r h _ hs]
      dsimp [mkInput]
      have h1 : ¬ (2 * r * k + s < 2 * r * k) := by omega
      have h2 : 2 * r * k + s < 2 * r * k + h := by omega
      simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
    · rw [Nat.testBit_lt_two_pow ((decA k r h _).isLt.trans_le
            (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hs))),
          Nat.testBit_lt_two_pow (a.isLt.trans_le
            (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hs)))]
  · apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro s
    by_cases hs : s < h
    · rw [decB_testBit k r h _ hs]
      dsimp [mkInput]
      have h1 : ¬ (2 * r * k + h + s < 2 * r * k) := by omega
      have h2 : ¬ (2 * r * k + h + s < 2 * r * k + h) := by omega
      simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
    · rw [Nat.testBit_lt_two_pow ((decB k r h _).isLt.trans_le
            (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hs))),
          Nat.testBit_lt_two_pow (b.isLt.trans_le
            (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hs)))]

lemma main_29778 : ∀ (k r h t : ℕ), 0 < h → h ≤ k → 0 < t →
  let rot := fun (d x : ℕ) => ((x <<< (d % k)) ||| (x >>> (k-d % k))) % 2^k
  let chi := fun (x : ℕ) => (List.range k).foldl (fun (acc i : ℕ) =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i+1) % k)) && x.testBit ((i+2) % k))).toNat <<< i)) 0
  let run := fun (masks : ℕ → Fin (2^k)) (col : Bool) (key name : ℕ) =>
    let gap : ℕ := if col then 2 else 1
    (List.range r).foldl (fun z j =>
      let mixed := z ^^^ rot gap z ^^^ rot (k-gap % k) z
      chi mixed ^^^ rot (if col then 3*(j+1)+1 else 2*j) key ^^^
        (masks (if col then r+j else j)).val) (rot (if col then 3 else 1) key ^^^ name)
  let B := if r = 0 then 2 else if r = 1 then 7 else 7*r-2
  let seam := fun (b : ℕ) => min k (h+b-k)
  let A := 2^(B+seam B+1)
  let scan := 2^(10*r+seam (4*r)+seam (6*r)+2) * Nat.choose (t+A-1) t
  let wiresIn := 2*r*k+2*h
  let bits := fun (len word : ℕ) => (List.range len).map (fun i => word.testBit i)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
    (out : Fin ((t+2)*k+1) → Fin (wiresIn+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack wiresIn C ∧
    C.output < wiresIn+C.size ∧
    C.size ≤ 1048576*((k+1)*(r+1)*(t+2))^4 * min (2^(3*k)) scan ∧
    ∀ (masks : ℕ → Fin (2^k)) (a b : Fin (2^h)),
      let input := (List.range (2*r)).flatMap (fun j => bits k (masks j).val) ++
        bits h a.val ++ bits h b.val
      let num := fun (x y : Fin (2^k)) => (Finset.univ.filter (fun key : Fin (2^k) =>
        (run masks false key.val x.val >>> (k-h)) = a.val ∧
        (run masks true key.val y.val >>> (k-h)) = b.val)).card
      let moment := ∑ x : Fin (2^k), ∑ y : Fin (2^k), (num x y)^t
      ∀ j : Fin ((t+2)*k+1), (C.wires input).getD (out j).val false = moment.testBit j.val := by
  intro k r h t hh0 hh ht
  have hk : 0 < k := by omega
  let W := (t + 2) * k + 1
  have hBuild : Build (inputSet k r h)
      (wordBits W (fun v => momentOf k r h t (decMasks k r h v) (decA k r h v) (decB k r h v)))
      (1048576 * ((k + 1) * (r + 1) * (t + 2)) ^ 4 * min (2 ^ (3 * k)) (scanVal k r h t)) := by
    by_cases hbr : 2 ^ (3 * k) ≤ scanVal k r h t
    · rw [min_eq_left hbr]
      exact directMomentG k r h t hh0 hh ht
    · rw [min_eq_right (le_of_not_ge hbr)]
      exact scanMomentG k r h t hh0 hh ht
  have hStart : Scheduled (wiresIn k r h) id 0 (inputSet k r h) :=
    schedStart (fun i => fun x : Fin (wiresIn k r h) → Bool => x i) (fun _ _ => rfl)
  obtain ⟨c, hc, hSched⟩ := hBuild.run hStart le_rfl
  rw [Nat.zero_add] at hSched
  obtain ⟨gs, hgs, hrb, hft, hwire⟩ := hSched
  let C : Circuit := ⟨gs, 0⟩
  have hCsize : C.size = c := hgs
  have hex : ∀ j : Fin W, ∃ i : Fin (wiresIn k r h + C.size),
      ∀ v : Fin (wiresIn k r h) → Bool,
        (C.wires (List.ofFn v)).getD i.val false =
          (momentOf k r h t (decMasks k r h v) (decA k r h v) (decB k r h v)).testBit j.val := by
    intro j
    obtain ⟨i, hi, hval⟩ := hwire (fun v =>
      (momentOf k r h t (decMasks k r h v) (decA k r h v) (decB k r h v)).testBit j.val)
      (Or.inr ⟨j.val, j.isLt, rfl⟩)
    exact ⟨⟨i, by rw [hCsize]; exact hi⟩, hval⟩
  let out : Fin W → Fin (wiresIn k r h + C.size) := fun j => Classical.choose (hex j)
  refine ⟨C, out, hft, hrb, ?_, ?_, ?_⟩
  · change 0 < wiresIn k r h + C.size
    unfold wiresIn; omega
  · rw [hCsize]
    exact hc
  · intro masks a b input num moment j
    have hout := Classical.choose_spec (hex j) (mkInput k r h masks a b)
    rw [ofFn_mkInput] at hout
    have hdec := dec_mkInput (r := r) hk masks a b
    have hmomEq : momentOf k r h t (decMasks k r h (mkInput k r h masks a b))
        (decA k r h (mkInput k r h masks a b)) (decB k r h (mkInput k r h masks a b)) =
        momentOf k r h t masks a b := by
      rw [hdec.2.1, hdec.2.2]
      unfold momentOf numOf
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      congr 2; ext key
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold runN
      rw [runPrefix_congr_masks hdec.1 false key.val x.val r le_rfl,
          runPrefix_congr_masks hdec.1 true key.val y.val r le_rfl]
    rw [hmomEq] at hout
    exact hout

end
end MainBridge

end PEqualNP.Outside.L_meta_29778

theorem PEqualNP.Outside.L_meta_29778 : ∀ (k r h t : ℕ), 0 < h → h ≤ k → 0 < t →
  let rot := fun (d x : ℕ) => ((x <<< (d % k)) ||| (x >>> (k-d % k))) % 2^k
  let chi := fun (x : ℕ) => (List.range k).foldl (fun (acc i : ℕ) =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i+1) % k)) && x.testBit ((i+2) % k))).toNat <<< i)) 0
  let run := fun (masks : ℕ → Fin (2^k)) (col : Bool) (key name : ℕ) =>
    let gap : ℕ := if col then 2 else 1
    (List.range r).foldl (fun z j =>
      let mixed := z ^^^ rot gap z ^^^ rot (k-gap % k) z
      chi mixed ^^^ rot (if col then 3*(j+1)+1 else 2*j) key ^^^
        (masks (if col then r+j else j)).val) (rot (if col then 3 else 1) key ^^^ name)
  let B := if r = 0 then 2 else if r = 1 then 7 else 7*r-2
  let seam := fun (b : ℕ) => min k (h+b-k)
  let A := 2^(B+seam B+1)
  let scan := 2^(10*r+seam (4*r)+seam (6*r)+2) * Nat.choose (t+A-1) t
  let wiresIn := 2*r*k+2*h
  let bits := fun (len word : ℕ) => (List.range len).map (fun i => word.testBit i)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
    (out : Fin ((t+2)*k+1) → Fin (wiresIn+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack wiresIn C ∧
    C.output < wiresIn+C.size ∧
    C.size ≤ 1048576*((k+1)*(r+1)*(t+2))^4 * min (2^(3*k)) scan ∧
    ∀ (masks : ℕ → Fin (2^k)) (a b : Fin (2^h)),
      let input := (List.range (2*r)).flatMap (fun j => bits k (masks j).val) ++
        bits h a.val ++ bits h b.val
      let num := fun (x y : Fin (2^k)) => (Finset.univ.filter (fun key : Fin (2^k) =>
        (run masks false key.val x.val >>> (k-h)) = a.val ∧
        (run masks true key.val y.val >>> (k-h)) = b.val)).card
      let moment := ∑ x : Fin (2^k), ∑ y : Fin (2^k), (num x y)^t
      ∀ j : Fin ((t+2)*k+1), (C.wires input).getD (out j).val false = moment.testBit j.val :=
  PEqualNP.Outside.L_meta_29778.main_29778
