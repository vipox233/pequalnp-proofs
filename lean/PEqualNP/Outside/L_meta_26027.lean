import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26027

open PEqualNP.CircuitLowerBounds

private def legal (g : Gate) : Prop := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
private def posG (G : List Gate) : Prop := ∀ g ∈ G, legal g

private def tape (G : List Gate) (xs : List Bool) := (Circuit.mk G 0).wires xs

private theorem tapeSnoc (G : List Gate) (g : Gate) (xs : List Bool) :
    tape (G ++ [g]) xs = tape G xs ++ [g.op.eval (g.inputs.map fun i => (tape G xs).getD i false)] := by
  simp [tape, Circuit.wires, List.foldl_append]

private theorem tapeLen (G : List Gate) (xs : List Bool) : (tape G xs).length = xs.length + G.length := by
  induction G using List.reverseRecOn with
  | nil => simp [tape, Circuit.wires]
  | append_singleton G g ih => simp [tapeSnoc, ih, Nat.add_assoc]

private theorem lookSnoc (xs : List Bool) (x : Bool) (i : ℕ) :
    (xs ++ [x]).getD i false = if i = xs.length then x else xs.getD i false := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons y ys ih => cases i with
    | zero => simp [List.getD]
    | succ i => simpa [List.getD] using ih i

private def sig {U : Type*} (xs : U → List Bool) (G : List Gate) (i : ℕ) (u : U) : Bool :=
  (tape G (xs u)).getD i false

private def applyG {U : Type*} (g : Gate) (f : ℕ → U → Bool) (u : U) := g.op.eval (g.inputs.map fun i => f i u)

private theorem sigNext {U : Type*} {n : ℕ} (xs : U → List Bool) (hn : ∀ u, (xs u).length = n)
    (G : List Gate) (g : Gate) (i : ℕ) : sig xs (G ++ [g]) i =
      if i = n + G.length then applyG g (sig xs G) else sig xs G i := by
  funext u; simp only [sig, tapeSnoc, lookSnoc, tapeLen, hn]; split <;> rfl

private structure Scene (U V Q : Type*) where
  emb : V → U
  src : Q → U
  dst : Q → U
  small : V → List Bool
  width : ℕ
  len : ∀ v, (small v).length = width

variable {U V Q : Type*} [DecidableEq Q] (c : Scene U V Q)

private def Safe (s : Finset Q) (f : U → Bool) : Prop := ∀ q ∉ s, f (c.src q) ≤ f (c.dst q)

private theorem safeGrow {s t : Finset Q} {f : U → Bool} (h : Safe c s f) (incl : s ⊆ t) : Safe c t f :=
  fun q hq => h q (fun h => hq (incl h))

private def Av (G : List Gate) (f : U → Bool) : Prop :=
  ∃ i < c.width + G.length, ∀ v, sig c.small G i v = f (c.emb v)

private theorem avGrow {G : List Gate} {f : U → Bool} (h : Av c G f) (T : List Gate) : Av c (G ++ T) f := by
  induction T using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton T g ih =>
    obtain ⟨i, hi, he⟩ := ih
    rw [← List.append_assoc]
    refine ⟨i, by simp only [List.length_append, List.length_singleton] at *; omega, ?_⟩
    rwa [sigNext _ c.len, ite_eq_right (Nat.ne_of_lt hi)]

private def OK (s : Finset Q) (G : List Gate) (f : U → Bool) : Prop :=
  (Safe c s f ∧ Av c G f) ∨ ((∀ v, f (c.emb v) = false) ∧
    ∃ e : Finset Q, e.card ≤ 1 ∧ Safe c (s ∪ e) f)

private theorem okGrow {s : Finset Q} {G : List Gate} {f : U → Bool} (h : OK c s G f)
    (e : Finset Q) (T : List Gate) : OK c (s ∪ e) (G ++ T) f := by
  rcases h with ⟨h,a⟩ | ⟨h,b,hb,a⟩
  · exact Or.inl ⟨safeGrow c h Finset.subset_union_left, avGrow c a T⟩
  · exact Or.inr ⟨h, b, hb, safeGrow c a (by intro q; simp only [Finset.mem_union]; tauto)⟩

private def Next (s : Finset Q) (G : List Gate) (f : U → Bool) : Prop :=
  ∃ (e : Finset Q) (T : List Gate), e.card + T.length ≤ 1 ∧ posG T ∧ OK c (s ∪ e) (G ++ T) f

private theorem idle {s G f} (h : OK c s G f) : Next c s G f :=
  ⟨∅, [], by simp, by simp [posG], by simpa using h⟩

private def bop (o x y : Bool) := if o then x && y else x || y
private def op2 (o : Bool) : GateOp := if o then .and else .or
private theorem bopMono : ∀ (o x y x' y' : Bool), x ≤ x' → y ≤ y' → bop o x y ≤ bop o x' y' := by decide
private theorem bopSwap : ∀ o x y, bop o x y = bop o y x := by decide

private theorem safeBop {o s f g} (hf : Safe c s f) (hg : Safe c s g) :
    Safe c s (fun u => bop o (f u) (g u)) := fun q hq => bopMono _ _ _ _ _ (hf q hq) (hg q hq)

private theorem bothReal {s G f g} (o : Bool) (hf : Safe c s f) (af : Av c G f) (hg : Safe c s g) (ag : Av c G g) :
    Next c s G (fun u => bop o (f u) (g u)) := by
  obtain ⟨i, _, ei⟩ := af; obtain ⟨j, _, ej⟩ := ag
  let gate := Gate.mk (op2 o) [i,j]
  refine ⟨∅, [gate], by simp, ?_, Or.inl ⟨by simpa using safeBop c (o := o) hf hg, ?_⟩⟩
  · cases o <;> simp [posG, legal, gate, op2]
  · refine ⟨c.width + G.length, by simp, ?_⟩
    rw [sigNext _ c.len, ite_eq_left rfl]
    intro v; cases o <;> simp [applyG, gate, op2, GateOp.eval, bop, ei, ej]

private theorem oneGhost {s G f g} (o : Bool) (zero : ∀ v, f (c.emb v) = false)
    (e : Finset Q) (he : e.card ≤ 1) (hf : Safe c (s ∪ e) f) (K : OK c s G g) :
    Next c s G (fun u => bop o (f u) (g u)) := by
  refine ⟨e, [], by simpa using he, by simp [posG], ?_⟩
  rw [List.append_nil]
  rcases K with ⟨hg,ag⟩ | ⟨zg,e',he',hg⟩
  · have H := safeBop c (o := o) hf (safeGrow c hg Finset.subset_union_left)
    cases o with
    | true => exact Or.inr ⟨fun v => by simp [bop, zero], ∅, by simp, by simpa using H⟩
    | false =>
      obtain ⟨j,hj,h⟩ := ag
      exact Or.inl ⟨H,j,hj,fun v => by simpa [bop, zero] using h v⟩
  · refine Or.inr ⟨fun v => by cases o <;> simp [bop,zero,zg], e', he', safeBop c ?_ ?_⟩
    · exact safeGrow c hf Finset.subset_union_left
    · exact safeGrow c hg (by intro q; simp only [Finset.mem_union]; tauto)

private theorem binary {s G f g} (o : Bool) (hf : OK c s G f) (hg : OK c s G g) :
    Next c s G (fun u => bop o (f u) (g u)) := by
  rcases hf with ⟨hf,af⟩ | ⟨zf,e,he,sf⟩
  · rcases hg with ⟨hg,ag⟩ | ⟨zg,e,he,sg⟩
    · exact bothReal c o hf af hg ag
    · simpa only [bopSwap o (g _) (f _)] using oneGhost c o zg e he sg (Or.inl ⟨hf,af⟩)
  · exact oneGhost c o zf e he sf hg

end PEqualNP.Outside.L_meta_26027

namespace PEqualNP.Outside.L_meta_26027

open PEqualNP.CircuitLowerBounds

variable {U V Q : Type*} [DecidableEq Q] (c : Scene U V Q)

private theorem constGate {s : Finset Q} {G : List Gate} (op : GateOp)
    (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    Next c s G (fun _ => op.eval []) := by
  let g := Gate.mk op []
  refine ⟨∅, [g], by simp, ?_, Or.inl ⟨fun _ _ => le_rfl, ?_⟩⟩
  · simpa [posG, legal, g] using hop
  · refine ⟨c.width + G.length, by simp, ?_⟩
    rw [sigNext _ c.len, ite_eq_left rfl]; intro v; rfl

private theorem singleVal (b : Bool) : GateOp.and.eval [b] = b ∧ GateOp.or.eval [b] = b := by cases b <;> decide

private theorem gateStep {s G} (g : Gate) (hg : legal g) (f : ℕ → U → Bool)
    (H : ∀ i, OK c s G (f i)) : Next c s G (applyG g f) := by
  rcases g with ⟨op, l⟩; rcases hg with ⟨hop, hl⟩
  change op ∈ ({GateOp.and, GateOp.or} : Set GateOp) at hop
  change l.length ≤ 2 at hl
  cases l with
  | nil => exact constGate c op hop
  | cons i l =>
    change op = .and ∨ op = .or at hop
    cases l with
    | nil =>
      have eq : applyG ⟨op, [i]⟩ f = f i := by
        funext u; rcases hop with rfl | rfl
        · exact (singleVal _).1
        · exact (singleVal _).2
      rw [eq]; exact idle c (H i)
    | cons j l =>
      cases l with
      | nil =>
        rcases hop with rfl | rfl
        · change Next c s G (fun u => GateOp.and.eval [f i u, f j u])
          simpa [GateOp.eval, bop] using binary c true (H i) (H j)
        · change Next c s G (fun u => GateOp.or.eval [f i u, f j u])
          simpa [GateOp.eval, bop] using binary c false (H i) (H j)
      | cons k ks => simp at hl

private theorem compile {width : ℕ} (big : U → List Bool) (hw : ∀ u, (big u).length = width)
    (initial : ∀ i, OK c ∅ [] (sig big [] i)) (C : List Gate) (legalC : posG C) :
    ∃ (s : Finset Q) (G : List Gate), posG G ∧ G.length + s.card ≤ C.length ∧
      ∀ i, OK c s G (sig big C i) := by
  induction C using List.reverseRecOn with
  | nil => exact ⟨∅, [], by simp [posG], by simp, initial⟩
  | append_singleton C g ih =>
    obtain ⟨s,G,hG,bound,sim⟩ := ih (fun x hx => legalC x (by simp [hx]))
    obtain ⟨e,T,he,hT,out⟩ := gateStep c g (legalC g (by simp)) _ sim
    refine ⟨s ∪ e, G ++ T, ?_, ?_, fun i => ?_⟩
    · intro x hx; rcases List.mem_append.mp hx with h|h; exact hG x h; exact hT x h
    · have hCard := Finset.card_union_le s e
      simp only [List.length_append, List.length_singleton]; omega
    · rw [sigNext _ hw]; split
      · exact out
      · exact okGrow c (sim i) e T

end PEqualNP.Outside.L_meta_26027

namespace PEqualNP.Outside.L_meta_26027

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents Finset

private def inputs {n m : ℕ} (u : Fin n × Fin m) := oneEach u.1 u.2

private theorem inputLen {n m : ℕ} (u : Fin n × Fin m) : (inputs u).length = n + m := by simp [inputs,oneEach]

private theorem bitTrue {n m : ℕ} (u : Fin n × Fin m) (i : ℕ) :
    (inputs u).getD i false = true ↔ i = u.1.val ∨ i = n + u.2.val := by
  simp only [inputs, oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn, List.getElem?_ofFn]
  split_ifs <;> simp [Fin.ext_iff] <;> omega

private def rowBit {n m : ℕ} (i : Fin n) (z : Fin n × Fin m) := decide (i = z.1)
private def colBit {n m : ℕ} (j : Fin m) (z : Fin n × Fin m) := decide (j = z.2)

private theorem rawRow {n m : ℕ} (i : Fin n) :
    sig (inputs (n := n) (m := m)) [] i.val = rowBit i := by
  funext z; apply Bool.eq_iff_iff.mpr
  change (inputs z).getD i.val false = true ↔ decide (i = z.1) = true
  rw [bitTrue]; simp [Fin.ext_iff, show i.val ≠ n + z.2.val by omega]

private theorem rawCol {n m : ℕ} (j : Fin m) :
    sig (inputs (n := n) (m := m)) [] (n + j.val) = colBit j := by
  funext z; apply Bool.eq_iff_iff.mpr
  change (inputs z).getD (n + j.val) false = true ↔ decide (j = z.2) = true
  rw [bitTrue]; simp [Fin.ext_iff, show n + j.val ≠ z.1.val by omega]

private theorem rawOff {n m i : ℕ} (h : n+m ≤ i) :
    sig (inputs (n := n) (m := m)) [] i = fun _ => false := by
  funext z; apply Bool.eq_iff_iff.mpr
  change (inputs z).getD i false = true ↔ false = true
  rw [bitTrue]; simp only [Bool.false_eq_true, iff_false]; omega

private theorem restrictTable (n m a b : ℕ) (A : Fin n → Fin m → Bool)
    (x : Fin a ↪ Fin n) (y : Fin b ↪ Fin m)
    (varies : ∃ i k j l, A (x i) (y j) ≠ A (x k) (y l))
    (row : ∀ i, (∀ h, x h ≠ i) → ∃ k j, A i j = true ∧ A k j = false)
    (col : ∀ j, (∀ h, y h ≠ j) → ∃ l i, A i j = true ∧ A i l = false)
    (C : Circuit) (hC : Monotone2 C) (hA : Represents A C) :
    ∃ D : Circuit, Monotone2 D ∧ Represents (fun i j => A (x i) (y j)) D ∧
      D.size + (n-a) + (m-b) ≤ C.size := by
  classical
  let R := univ \ univ.map x
  let B := univ \ univ.map y
  have ar (r : ↥R) (t : Fin a) : x t ≠ r.val := fun h =>
    (mem_sdiff.mp r.property).2 (mem_map.mpr ⟨t,mem_univ _,h⟩)
  have ab (j : ↥B) (t : Fin b) : y t ≠ j.val := fun h =>
    (mem_sdiff.mp j.property).2 (mem_map.mpr ⟨t,mem_univ _,h⟩)
  choose kr jr hr using fun r : ↥R => row r.val (ar r)
  choose lc ic hc using fun j : ↥B => col j.val (ab j)
  let U := Fin n × Fin m
  let V := Fin a × Fin b
  let Q := ↥R ⊕ ↥B
  let c : Scene U V Q := ⟨fun z => (x z.1, y z.2),
    Sum.elim (fun r => (r.val, jr r)) (fun j => (ic j, j.val)),
    Sum.elim (fun r => (kr r, jr r)) (fun j => (ic j, lc j)), inputs, a+b, inputLen⟩
  have rs (i : Fin n) (s : Finset Q) (t : ∀ r : ↥R, r.val = i → Sum.inl r ∈ s) : Safe c s (rowBit i) := by
    rintro (r|j) h
    · have hne : i ≠ r.val := fun eq => h (t r eq.symm)
      change decide (i = r.val) ≤ decide (i = kr r); simp [hne]
    · exact le_rfl
  have cs (i : Fin m) (s : Finset Q) (t : ∀ j : ↥B, j.val = i → Sum.inr j ∈ s) : Safe c s (colBit i) := by
    rintro (r|j) h
    · exact le_rfl
    · have hne : i ≠ j.val := fun eq => h (t j eq.symm)
      change decide (i = j.val) ≤ decide (i = lc j); simp [hne]
  have rOK (i : Fin n) : OK c ∅ [] (rowBit i) := by
    by_cases h : ∃ t, x t = i
    · obtain ⟨t,rfl⟩ := h
      refine Or.inl ⟨rs _ _ (fun r eq => (ar r t eq.symm).elim), t.val, by change t.val < a+b+0; omega, ?_⟩
      intro z; change sig inputs [] t.val z = decide (x t = x z.1)
      rw [rawRow]; simp [rowBit, x.injective.eq_iff]
    · have hi : i ∈ R := mem_sdiff.mpr ⟨mem_univ _, fun hi => by
          obtain ⟨t,_,e⟩ := mem_map.mp hi; exact h ⟨t,e⟩⟩
      refine Or.inr ⟨fun z => ?_, {Sum.inl (⟨i,hi⟩ : ↥R)}, by simp, rs _ _ ?_⟩
      · change decide (i = x z.1) = false; simp [show i ≠ x z.1 from fun e => h ⟨_,e.symm⟩]
      · intro r eq; simp; exact Subtype.ext eq
  have cOK (i : Fin m) : OK c ∅ [] (colBit i) := by
    by_cases h : ∃ t, y t = i
    · obtain ⟨t,rfl⟩ := h
      refine Or.inl ⟨cs _ _ (fun j eq => (ab j t eq.symm).elim), a+t.val, by change a+t.val < a+b+0; omega, ?_⟩
      intro z; change sig inputs [] (a+t.val) z = decide (y t = y z.2)
      rw [rawCol]; simp [colBit, y.injective.eq_iff]
    · have hi : i ∈ B := mem_sdiff.mpr ⟨mem_univ _, fun hi => by
          obtain ⟨t,_,e⟩ := mem_map.mp hi; exact h ⟨t,e⟩⟩
      refine Or.inr ⟨fun z => ?_, {Sum.inr (⟨i,hi⟩ : ↥B)}, by simp, cs _ _ ?_⟩
      · change decide (i = y z.2) = false; simp [show i ≠ y z.2 from fun e => h ⟨_,e.symm⟩]
      · intro j eq; simp; exact Subtype.ext eq
  have start (i : ℕ) : OK c ∅ [] (sig inputs [] i) := by
    by_cases h : i < n
    · exact rawRow (m := m) ⟨i,h⟩ ▸ rOK ⟨i,h⟩
    by_cases h' : i < n + m
    · let j : Fin m := ⟨i-n,by omega⟩
      have e : n + j.val = i := by dsimp [j]; omega
      rw [← e, rawCol]; exact cOK j
    · rw [rawOff (Nat.le_of_not_gt h')]; exact Or.inr ⟨fun _ => rfl, ∅, by simp, fun _ _ => le_rfl⟩
  obtain ⟨s,G,good,cost,hs⟩ := compile c inputs inputLen start C.gates hC
  have out (z : U) : sig inputs C.gates C.output z = A z.1 z.2 := hA _ _
  rcases hs C.output with ⟨safe,wire,_,val⟩ | ⟨zero,_⟩
  · have all : s = univ := eq_univ_of_forall (fun q => by
        by_contra miss
        have e := safe q miss
        rw [out, out] at e
        rcases q with r | j
        · change A r.val (jr r) ≤ A (kr r) (jr r) at e
          exact (by decide : ¬ true ≤ false) (by simpa only [(hr r).1,(hr r).2] using e)
        · change A (ic j) j.val ≤ A (ic j) (lc j) at e
          exact (by decide : ¬ true ≤ false) (by simpa only [(hc j).1,(hc j).2] using e))
    have count : s.card = (n-a)+(m-b) := by
      rw [all, card_univ]; change Fintype.card (↥R ⊕ ↥B) = _
      rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
      simp only [R, B, card_sdiff_of_subset (subset_univ _), card_map, card_univ, Fintype.card_fin]
    refine ⟨⟨G,wire⟩,good,fun i j => (val (i,j)).trans (out _), ?_⟩
    change G.length + (n-a) + (m-b) ≤ C.gates.length
    omega
  · obtain ⟨i,k,j,l,diff⟩ := varies
    exact (diff (((out _).symm.trans (zero (i,j))).trans ((zero (k,l)).symm.trans (out _)))).elim

end PEqualNP.Outside.L_meta_26027

theorem PEqualNP.Outside.L_meta_26027 : (∀ (n m a b : Nat) (A : Fin n → Fin m → Bool)
    (x : Fin a ↪ Fin n) (y : Fin b ↪ Fin m),
  (∃ i k j l, A (x i) (y j) ≠ A (x k) (y l)) →
  (∀ i, (∀ h, x h ≠ i) → ∃ k j, A i j = true ∧ A k j = false) →
  (∀ j, (∀ h, y h ≠ j) → ∃ l i, A i j = true ∧ A i l = false) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.Represents.Represents A C →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.Represents.Represents (fun i j => A (x i) (y j)) D ∧
      D.size + (n-a) + (m-b) ≤ C.size) := by
  exact PEqualNP.Outside.L_meta_26027.restrictTable
