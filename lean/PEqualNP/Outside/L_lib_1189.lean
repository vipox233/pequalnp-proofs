import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1189_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

section Part1_Wires

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

lemma isNotOp_eq_true (op : GateOp) : isNotOp op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNotOp]

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_stepWire_length (gs : List Gate) (x : List Bool) :
    (gs.foldl stepWire x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepWire, List.length_append, List.length_singleton,
      List.length_cons, List.length_nil]
    omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size :=
  foldl_stepWire_length C.gates x

lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (d : α) {i : ℕ} (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD]
  rw [List.getElem?_append_left hi]

lemma foldl_stepWire_getD_lt (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (gs.foldl stepWire x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire x g).length := by
      simp [stepWire]; omega
    rw [ih (stepWire x g) hlt]
    exact getD_append_left x _ false hi

lemma foldl_stepWire_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    ((gs₁ ++ gs₂).foldl stepWire x) = gs₂.foldl stepWire (gs₁.foldl stepWire x) :=
  List.foldl_append

lemma wires_getD_lt (C : Circuit) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_stepWire_getD_lt C.gates x hi

lemma wires_gate_eq (C : Circuit) (x : List Bool) (hrb : ReadsBack x.length C)
    {j : ℕ} (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have ht := List.take_append_drop j C.gates
    have hd : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    rw [hd] at ht
    exact ht.symm
  have hw0len : ((C.gates.take j).foldl stepWire x).length = x.length + j := by
    rw [foldl_stepWire_length, List.length_take_of_le (Nat.le_of_lt hj)]
  have hwires : C.wires x =
      (C.gates.drop (j + 1)).foldl stepWire
        (stepWire ((C.gates.take j).foldl stepWire x) C.gates[j]) := by
    change C.gates.foldl stepWire x = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  conv_lhs => rw [hwires]
  have hlt1 : x.length + j < (stepWire ((C.gates.take j).foldl stepWire x) C.gates[j]).length := by
    simp [stepWire, hw0len]
  rw [foldl_stepWire_getD_lt _ _ hlt1]
  simp only [stepWire, List.getD]
  rw [List.getElem?_append_right (by rw [hw0len])]
  simp only [hw0len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  have hgate : C.gates[j] = gateAt C j := by
    simp [gateAt, List.getD, List.getElem?_eq_getElem hj]
  rw [hgate]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < x.length + j := hrb j hj i hi
  have hi0 : i < ((C.gates.take j).foldl stepWire x).length := by omega
  have heq : (C.wires x).getD i false = ((C.gates.take j).foldl stepWire x).getD i false := by
    rw [hwires, foldl_stepWire_getD_lt _ _ (by simp [stepWire]; omega)]
    exact getD_append_left _ _ false hi0
  exact heq.symm

def effInputsGate (g : Gate) : Finset ℕ :=
  if isNotOp g.op then
    match g.inputs with
    | [] => ∅
    | u :: _ => {u}
  else
    g.inputs.toFinset

def eff (C : Circuit) (n : ℕ) (w : ℕ) : Finset ℕ :=
  if h : n + 2 ≤ w ∧ w - (n + 2) < C.gates.length then
    effInputsGate (gateAt C (w - (n + 2)))
  else
    ∅

lemma eff_lt {C : Circuit} {n : ℕ} (hrb : ReadsBack (n + 2) C) {w u : ℕ}
    (hu : u ∈ eff C n w) : u < w := by
  unfold eff at hu
  split_ifs at hu with h
  · unfold effInputsGate at hu
    split_ifs at hu
    · cases hlist : (gateAt C (w - (n + 2))).inputs with
      | nil => rw [hlist] at hu; simp at hu
      | cons a l =>
        rw [hlist] at hu
        simp only [Finset.mem_singleton] at hu
        subst hu
        have := hrb (w - (n + 2)) h.2 u (by rw [hlist]; simp)
        omega
    · rw [List.mem_toFinset] at hu
      have := hrb (w - (n + 2)) h.2 u hu
      omega
  · simp at hu

lemma gateOp_eval_congr (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (f₁ f₂ : ℕ → Bool) (h : ∀ u ∈ effInputsGate g, f₁ u = f₂ u) :
    g.op.eval (g.inputs.map f₁) = g.op.eval (g.inputs.map f₂) := by
  rcases hg with h1 | h1 | h1 <;> rw [h1]
  · simp only [GateOp.eval]
    congr 1
    apply List.map_congr_left
    intro u hu
    apply h
    simp [effInputsGate, isNotOp, hu, h1]
  · simp only [GateOp.eval]
    congr 1
    apply List.map_congr_left
    intro u hu
    apply h
    simp [effInputsGate, isNotOp, hu, h1]
  · cases hlist : g.inputs with
    | nil => simp [GateOp.eval, hlist]
    | cons a l =>
      simp only [GateOp.eval, hlist, List.map_cons, List.headD_cons]
      congr 1
      apply h
      simp [effInputsGate, isNotOp, hlist, h1]

lemma gateOp_eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f₁ f₂ : ℕ → Bool) (h : ∀ u ∈ effInputsGate g, f₁ u = true → f₂ u = true) :
    g.op.eval (g.inputs.map f₁) = true → g.op.eval (g.inputs.map f₂) = true := by
  have heff : ∀ u ∈ g.inputs, f₁ u = true → f₂ u = true := by
    intro u hu
    apply h
    rcases hg with h1 | h1 <;> simp [effInputsGate, isNotOp, hu, h1]
  rcases hg with h1 | h1 <;> rw [h1]
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro ha u hu
    exact heff u hu (ha u hu)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
    rintro ⟨u, hu, htu⟩
    exact ⟨u, hu, heff u hu htu⟩

lemma list_filter_length_eq_card {α : Type*} (l : List α) (p : α → Bool) (d : α) :
    (l.filter p).length = ((Finset.range l.length).filter (fun j => p (l.getD j d))).card := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons, List.length_cons]
    have hsplit : (Finset.range (t.length + 1)).filter (fun j => p ((a :: t).getD j d)) =
        (if p a then {0} else ∅) ∪
          ((Finset.range t.length).filter (fun j => p (t.getD j d))).image Nat.succ := by
      ext j
      cases j with
      | zero =>
        have hget : (a :: t)[0]?.getD d = a := rfl
        simp only [Finset.mem_filter, Finset.mem_range, Nat.zero_lt_succ, true_and, hget,
          Finset.mem_union, Finset.mem_image, Nat.succ_ne_zero, and_false, exists_false, or_false]
        cases hpa : p a <;> simp [hpa]
      | succ k =>
        have hget : (a :: t)[k + 1]?.getD d = t[k]?.getD d := rfl
        simp only [Finset.mem_filter, Finset.mem_range, Nat.succ_lt_succ_iff, hget,
          Finset.mem_union, Finset.mem_image, Nat.succ_inj, exists_eq_right]
        cases hpa : p a <;> simp [hpa]
    rw [hsplit, Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective _ Nat.succ_injective]
      cases hpa : p a <;> simp [ih, hpa, Nat.add_comm]
    · cases p a <;> simp

lemma notCount_eq_card (C : Circuit) :
    notCount C = ((Finset.range C.gates.length).filter
      (fun j => isNotOp (gateAt C j).op = true)).card := by
  unfold notCount
  have hfl : (C.gates.filter (fun g => @decide (g.op = GateOp.not)
      (lineDegreeGateOpDecEq g.op GateOp.not))).length =
      (C.gates.filter (fun g => isNotOp g.op)).length := by
    congr 1
    apply List.filter_congr
    intro g _
    cases g.op <;> rfl
  change (C.gates.filter (fun g => @decide (g.op = GateOp.not)
      (lineDegreeGateOpDecEq g.op GateOp.not))).length = _
  rw [hfl, list_filter_length_eq_card C.gates (fun g => isNotOp g.op) ⟨GateOp.or, []⟩]
  rfl

end Part1_Wires

open Classical

section Part2_TreeBound

def stepFrom (U : Finset ℕ) (eff : ℕ → Finset ℕ) (a b : ℕ) : Prop :=
  (a ∈ U ∧ b ∈ eff a) ∨ (b ∈ U ∧ a ∈ eff b)

def conn (U : Finset ℕ) (eff : ℕ → Finset ℕ) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (stepFrom U eff)

lemma conn_refl (U : Finset ℕ) (eff : ℕ → Finset ℕ) (a : ℕ) : conn U eff a a :=
  Relation.ReflTransGen.refl

lemma conn_symm {U : Finset ℕ} {eff : ℕ → Finset ℕ} {a b : ℕ}
    (h : conn U eff a b) : conn U eff b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y _ hstep ih =>
    have hrev : stepFrom U eff y x := by
      rcases hstep with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · exact Or.inr ⟨ha, hb⟩
      · exact Or.inl ⟨hb, ha⟩
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hrev) ih

lemma conn_trans {U : Finset ℕ} {eff : ℕ → Finset ℕ} {a b c : ℕ}
    (h1 : conn U eff a b) (h2 : conn U eff b c) : conn U eff a c :=
  Relation.ReflTransGen.trans h1 h2

lemma conn_lift {A B : Finset ℕ} {eff : ℕ → Finset ℕ} (hAB : A ⊆ B)
    {a b : ℕ} (h : conn A eff a b) : conn B eff a b := by
  induction h with
  | refl => exact conn_refl _ _ _
  | @tail c d _ hs ih =>
    have hs' : stepFrom B eff c d := by
      rcases hs with ⟨hc, hcd⟩ | ⟨hd, hdc⟩
      · exact Or.inl ⟨hAB hc, hcd⟩
      · exact Or.inr ⟨hAB hd, hdc⟩
    exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single hs')

lemma conn_mono_sub {U H : Finset ℕ} {eff : ℕ → Finset ℕ}
    (hclosed : ∀ a ∈ H, ∀ b, stepFrom U eff a b → b ∈ H)
    {a b : ℕ} (ha : a ∈ H) (h : conn U eff a b) : conn H eff a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d h1 hstep ih =>
    have hc : c ∈ H := by
      clear hstep ih
      induction h1 with
      | refl => exact ha
      | tail _ hs ih1 => exact hclosed _ ih1 _ hs
    have hd : d ∈ H := hclosed c hc d hstep
    have hstepH : stepFrom H eff c d := by
      rcases hstep with ⟨_, hcd⟩ | ⟨_, hdc⟩
      · exact Or.inl ⟨hc, hcd⟩
      · exact Or.inr ⟨hd, hdc⟩
    exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single hstepH)

lemma exists_boundary_edge {U T : Finset ℕ} {eff : ℕ → Finset ℕ}
    {a b : ℕ} (ha : a ∈ T) (hb : b ∉ T) (h : conn U eff a b) :
    ∃ x y, x ∈ T ∧ y ∉ T ∧ stepFrom U eff x y := by
  induction h with
  | refl => exact False.elim (hb ha)
  | @tail c d _ hstep ih =>
    by_cases hc : c ∈ T
    · exact ⟨c, d, hc, hb, hstep⟩
    · exact ih hc

lemma exists_edge_into {H T : Finset ℕ} {eff : ℕ → Finset ℕ}
    (hclosed : ∀ w ∈ H, eff w ⊆ H)
    (hHT : T ⊆ H) (hT : T.Nonempty) (hconn : ∀ a ∈ H, ∀ b ∈ H, conn H eff a b)
    (hne : (H \ T).Nonempty) :
    ∃ w ∈ H, ∃ u ∈ eff w, (w ∈ T ∧ u ∈ H \ T) ∨ (u ∈ T ∧ w ∈ H \ T) := by
  obtain ⟨r, hr⟩ := hT
  obtain ⟨v, hv⟩ := hne
  have hvH : v ∈ H := (Finset.mem_sdiff.mp hv).1
  have hvT : v ∉ T := (Finset.mem_sdiff.mp hv).2
  obtain ⟨x, y, hx, hy, hstep⟩ := exists_boundary_edge hr hvT (hconn r (hHT hr) v hvH)
  rcases hstep with ⟨hxH, hxy⟩ | ⟨hyH, hyx⟩
  · have hyH : y ∈ H := hclosed x hxH hxy
    exact ⟨x, hxH, y, hxy, Or.inl ⟨hx, Finset.mem_sdiff.mpr ⟨hyH, hy⟩⟩⟩
  · exact ⟨y, hyH, x, hyx, Or.inr ⟨hx, Finset.mem_sdiff.mpr ⟨hyH, hy⟩⟩⟩

def internalEdges (T : Finset ℕ) (eff : ℕ → Finset ℕ) : Finset ((_ : ℕ) × ℕ) :=
  T.sigma (fun w => (eff w).filter (fun u => u ∈ T))

lemma mem_internalEdges {T : Finset ℕ} {eff : ℕ → Finset ℕ} {w u : ℕ} :
    ⟨w, u⟩ ∈ internalEdges T eff ↔ w ∈ T ∧ u ∈ eff w ∧ u ∈ T := by
  simp only [internalEdges, Finset.mem_sigma, Finset.mem_filter]

lemma internalEdges_eq_sigma {H : Finset ℕ} {eff : ℕ → Finset ℕ}
    (hclosed : ∀ w ∈ H, eff w ⊆ H) :
    internalEdges H eff = H.sigma eff := by
  ext ⟨w, u⟩
  rw [mem_internalEdges, Finset.mem_sigma]
  constructor
  · rintro ⟨hw, hu, _⟩; exact ⟨hw, hu⟩
  · rintro ⟨hw, hu⟩; exact ⟨hw, hu, hclosed w hw hu⟩

lemma card_le_edges_add_one {H : Finset ℕ} {eff : ℕ → Finset ℕ}
    (hclosed : ∀ w ∈ H, eff w ⊆ H)
    (hne : H.Nonempty) (hconn : ∀ a ∈ H, ∀ b ∈ H, conn H eff a b) :
    H.card ≤ (H.sigma eff).card + 1 := by
  have hbuild : ∀ k : ℕ, 1 ≤ k → k ≤ H.card →
      ∃ T : Finset ℕ, T ⊆ H ∧ T.card = k ∧ T.card ≤ (internalEdges T eff).card + 1 := by
    intro k hk1
    induction k with
    | zero => omega
    | succ d ih =>
      intro hle
      by_cases hd0 : d = 0
      · subst hd0
        obtain ⟨r, hr⟩ := hne
        refine ⟨{r}, Finset.singleton_subset_iff.mpr hr, Finset.card_singleton r, ?_⟩
        rw [Finset.card_singleton]; omega
      · obtain ⟨T, hTH, hTc, hTe⟩ := ih (by omega) (by omega)
        have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
        have hsdiff : (H \ T).Nonempty := by
          by_contra hem
          rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hem
          have := Finset.card_le_card hem
          omega
        obtain ⟨w, hwH, u, hu_eff, hbu⟩ := exists_edge_into hclosed hTH hTne hconn hsdiff
        have hstep_ins : ∀ y ∈ H \ T,
            ((w ∈ T ∧ u = y) ∨ (u ∈ T ∧ w = y)) →
            ∃ T' : Finset ℕ, T' ⊆ H ∧ T'.card = d + 1 ∧ T'.card ≤ (internalEdges T' eff).card + 1 := by
          intro y hy hcase
          have hyH : y ∈ H := (Finset.mem_sdiff.mp hy).1
          have hyT : y ∉ T := (Finset.mem_sdiff.mp hy).2
          let T' := insert y T
          have hT'H : T' ⊆ H := Finset.insert_subset_iff.mpr ⟨hyH, hTH⟩
          have hT'c : T'.card = d + 1 := by rw [Finset.card_insert_of_notMem hyT, hTc]
          have hsub : internalEdges T eff ⊆ internalEdges T' eff := by
            intro ⟨a, b⟩ hab
            rw [mem_internalEdges] at hab ⊢
            exact ⟨Finset.mem_insert_of_mem hab.1, hab.2.1, Finset.mem_insert_of_mem hab.2.2⟩
          have hnmem : (⟨w, u⟩ : (_ : ℕ) × ℕ) ∉ internalEdges T eff := by
            intro hm
            rw [mem_internalEdges] at hm
            rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩
            · exact hyT hm.2.2
            · exact hyT hm.1
          have hmem : (⟨w, u⟩ : (_ : ℕ) × ℕ) ∈ internalEdges T' eff := by
            rw [mem_internalEdges]
            rcases hcase with ⟨hwT, rfl⟩ | ⟨huT, rfl⟩
            · exact ⟨Finset.mem_insert_of_mem hwT, hu_eff, Finset.mem_insert_self _ _⟩
            · exact ⟨Finset.mem_insert_self _ _, hu_eff, Finset.mem_insert_of_mem huT⟩
          have hins : insert (⟨w, u⟩ : (_ : ℕ) × ℕ) (internalEdges T eff) ⊆ internalEdges T' eff :=
            Finset.insert_subset_iff.mpr ⟨hmem, hsub⟩
          have hcard : (internalEdges T eff).card + 1 ≤ (internalEdges T' eff).card := by
            rw [← Finset.card_insert_of_notMem hnmem]
            exact Finset.card_le_card hins
          exact ⟨T', hT'H, hT'c, by omega⟩
        rcases hbu with ⟨hwT, hu⟩ | ⟨huT, hw⟩
        · exact hstep_ins u hu (Or.inl ⟨hwT, rfl⟩)
        · exact hstep_ins w hw (Or.inr ⟨huT, rfl⟩)
  obtain ⟨T, hTH, hTc, hTe⟩ := hbuild H.card (Finset.card_pos.mpr hne) le_rfl
  have hHT : T = H := Finset.eq_of_subset_of_card_le hTH (by omega)
  subst hHT
  rw [internalEdges_eq_sigma hclosed] at hTe
  exact hTe

lemma card_le_sum_eff {H : Finset ℕ} {eff : ℕ → Finset ℕ}
    (hclosed : ∀ w ∈ H, eff w ⊆ H)
    (hne : H.Nonempty) (hconn : ∀ a ∈ H, ∀ b ∈ H, conn H eff a b) :
    H.card ≤ (∑ w ∈ H, (eff w).card) + 1 := by
  have h := card_le_edges_add_one hclosed hne hconn
  rwa [Finset.card_sigma] at h

end Part2_TreeBound

section Part3_Cones

def cone (C : Circuit) (n : ℕ) (w : ℕ) : Finset ℕ :=
  if h : n + 2 ≤ w ∧ w - (n + 2) < C.gates.length then
    insert w ((eff C n w).biUnion fun u => if u < w then cone C n u else ∅)
  else
    if w < n + 2 then {w} else ∅
termination_by w

lemma cone_eq_of_lt {C : Circuit} {n w : ℕ} (hw : w < n + 2) :
    cone C n w = {w} := by
  unfold cone
  rw [dif_neg (by omega), if_pos hw]

lemma cone_eq_of_gate {C : Circuit} {n w : ℕ} (hrb : ReadsBack (n + 2) C)
    (hlo : n + 2 ≤ w) (hhi : w < n + 2 + C.gates.length) :
    cone C n w = insert w ((eff C n w).biUnion (cone C n)) := by
  conv_lhs => unfold cone
  rw [dif_pos ⟨hlo, by omega⟩]
  congr 1
  apply Finset.biUnion_congr rfl
  intro u hu
  rw [if_pos (eff_lt hrb hu)]

lemma cone_self {C : Circuit} {n w : ℕ} (hw : w < n + 2 + C.gates.length) :
    w ∈ cone C n w := by
  by_cases h : n + 2 ≤ w
  · conv_lhs => unfold cone
    rw [dif_pos ⟨h, by omega⟩]
    exact Finset.mem_insert_self _ _
  · rw [cone_eq_of_lt (by omega)]
    exact Finset.mem_singleton_self _

lemma cone_le {C : Circuit} {n w u : ℕ} (hu : u ∈ cone C n w) : u ≤ w := by
  induction w using Nat.strong_induction_on generalizing u with
  | ind w ih =>
    unfold cone at hu
    split_ifs at hu with h1 h2
    · rcases Finset.mem_insert.mp hu with rfl | hbi
      · exact le_rfl
      · rcases Finset.mem_biUnion.mp hbi with ⟨z, _, hz⟩
        split_ifs at hz with hzw
        · exact (ih z hzw hz).trans (Nat.le_of_lt hzw)
        · simp at hz
    · simp only [Finset.mem_singleton] at hu; omega
    · simp at hu

lemma cone_lt_bound {C : Circuit} {n w u : ℕ}
    (hw : w < n + 2 + C.gates.length) (hu : u ∈ cone C n w) :
    u < n + 2 + C.gates.length :=
  lt_of_le_of_lt (cone_le hu) hw

lemma cone_closed {C : Circuit} {n w : ℕ} (hrb : ReadsBack (n + 2) C)
    (hw : w < n + 2 + C.gates.length) :
    ∀ z ∈ cone C n w, eff C n z ⊆ cone C n w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro z hz u hu
    by_cases hlt : z < n + 2
    · unfold eff at hu
      rw [dif_neg (by omega)] at hu
      simp at hu
    · have hzle : z ≤ w := cone_le hz
      have hzlo : n + 2 ≤ z := by omega
      have hzhi : z < n + 2 + C.gates.length := lt_of_le_of_lt hzle hw
      by_cases hzw : z = w
      · subst hzw
        rw [cone_eq_of_gate hrb hzlo hzhi]
        exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, hu, cone_self (lt_trans (eff_lt hrb hu) hzhi)⟩)
      · have hltw : z < w := Nat.lt_of_le_of_ne hzle hzw
        have hwlo : n + 2 ≤ w := by omega
        rw [cone_eq_of_gate hrb hwlo hw] at hz ⊢
        rcases Finset.mem_insert.mp hz with rfl | hbi
        · exact False.elim (hzw rfl)
        · rcases Finset.mem_biUnion.mp hbi with ⟨a, ha, hza⟩
          have haw : a < w := eff_lt hrb ha
          have ha_lt : a < n + 2 + C.gates.length := lt_trans haw hw
          exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha, ih a haw ha_lt z hza hu⟩)

lemma cone_conn {C : Circuit} {n w : ℕ} (hrb : ReadsBack (n + 2) C)
    (hw : w < n + 2 + C.gates.length) :
    ∀ u ∈ cone C n w, conn (cone C n w) (eff C n) w u := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro u hu
    by_cases hwlo : w < n + 2
    · rw [cone_eq_of_lt hwlo, Finset.mem_singleton] at hu
      subst hu
      exact conn_refl _ _ _
    · rw [cone_eq_of_gate hrb (by omega) hw] at hu
      rcases Finset.mem_insert.mp hu with rfl | hbi
      · exact conn_refl _ _ _
      · rcases Finset.mem_biUnion.mp hbi with ⟨a, ha, hua⟩
        have haw : a < w := eff_lt hrb ha
        have ha_lt : a < n + 2 + C.gates.length := lt_trans haw hw
        have hstep1 : stepFrom (cone C n w) (eff C n) w a :=
          Or.inl ⟨cone_self hw, ha⟩
        have ha_sub : cone C n a ⊆ cone C n w := by
          intro x hx
          rw [cone_eq_of_gate hrb (by omega) hw]
          exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha, hx⟩)
        have hsub : conn (cone C n a) (eff C n) a u := ih a haw ha_lt u hua
        exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep1)
          (conn_lift ha_sub hsub)

lemma cone_all_conn {C : Circuit} {n w : ℕ} (hrb : ReadsBack (n + 2) C)
    (hw : w < n + 2 + C.gates.length) :
    ∀ a ∈ cone C n w, ∀ b ∈ cone C n w, conn (cone C n w) (eff C n) a b := by
  intro a ha b hb
  exact conn_trans (conn_symm (cone_conn hrb hw a ha)) (cone_conn hrb hw b hb)

lemma cone_sub_of_closed {C : Circuit} {n : ℕ} (hrb : ReadsBack (n + 2) C)
    {H : Finset ℕ} (hclosed : ∀ w ∈ H, eff C n w ⊆ H)
    {w : ℕ} (hw : w < n + 2 + C.gates.length) (hwH : w ∈ H) :
    cone C n w ⊆ H := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlo : w < n + 2
    · rw [cone_eq_of_lt hlo]; exact Finset.singleton_subset_iff.mpr hwH
    · rw [cone_eq_of_gate hrb (by omega) hw]
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hbi
      · exact hwH
      · rcases Finset.mem_biUnion.mp hbi with ⟨u, hu, hzu⟩
        exact ih u (eff_lt hrb hu) (lt_trans (eff_lt hrb hu) hw) (hclosed w hwH hu) hzu

lemma cone_agrees {C : Circuit} {n : ℕ} (hrb : ReadsBack (n + 2) C) (hfan : FanInTwo C)
    {w : ℕ} (hw : w < n + 2 + C.gates.length)
    (x₁ x₂ : List Bool) (hx₁ : x₁.length = n + 2) (hx₂ : x₂.length = n + 2)
    (hagree : ∀ u ∈ cone C n w, u < n + 2 → x₁.getD u false = x₂.getD u false) :
    (C.wires x₁).getD w false = (C.wires x₂).getD w false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwlo : w < n + 2
    · rw [wires_getD_lt C x₁ (by omega), wires_getD_lt C x₂ (by omega)]
      exact hagree w (cone_self hw) hwlo
    · let j := w - (n + 2)
      have hj : j < C.gates.length := by omega
      have hweq : n + 2 + j = w := by omega
      have h1 : (C.wires x₁).getD w false =
          (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x₁).getD i false) := by
        have hg := wires_gate_eq C x₁ (by rwa [hx₁]) hj
        rwa [hx₁, hweq] at hg
      have h2 : (C.wires x₂).getD w false =
          (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x₂).getD i false) := by
        have hg := wires_gate_eq C x₂ (by rwa [hx₂]) hj
        rwa [hx₂, hweq] at hg
      rw [h1, h2]
      have hgmem : gateAt C j ∈ C.gates := by
        have : gateAt C j = C.gates[j] := by simp [gateAt, List.getD, List.getElem?_eq_getElem hj]
        rw [this]
        exact List.getElem_mem hj
      have hop := (hfan (gateAt C j) hgmem).1
      apply gateOp_eval_congr (gateAt C j) hop
      intro u hu
      have hueff : u ∈ eff C n w := by
        unfold eff
        rw [dif_pos ⟨by omega, hj⟩]
        exact hu
      have huw : u < w := eff_lt hrb hueff
      have hu_lt : u < n + 2 + C.gates.length := lt_trans huw hw
      apply ih u huw hu_lt
      intro z hz hzl
      apply hagree z _ hzl
      rw [cone_eq_of_gate hrb (by omega) hw]
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, hueff, hz⟩)

lemma monotone_on_closed {C : Circuit} {n : ℕ} (hrb : ReadsBack (n + 2) C) (hfan : FanInTwo C)
    {S : Finset ℕ} (hsub : ∀ w ∈ S, w < n + 2 + C.gates.length)
    (hclosed : ∀ w ∈ S, eff C n w ⊆ S)
    (x₁ x₂ : List Bool) (hx₁ : x₁.length = n + 2) (hx₂ : x₂.length = n + 2)
    (hinp : ∀ u ∈ S, u < n + 2 → x₁.getD u false = true → x₂.getD u false = true)
    (hnot : ∀ w ∈ S, n + 2 ≤ w → isNotOp (gateAt C (w - (n + 2))).op = true →
      (C.wires x₁).getD w false = true → (C.wires x₂).getD w false = true) :
    ∀ w ∈ S, (C.wires x₁).getD w false = true → (C.wires x₂).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwS hval1
    by_cases hwlo : w < n + 2
    · rw [wires_getD_lt C x₁ (by omega)] at hval1
      rw [wires_getD_lt C x₂ (by omega)]
      exact hinp w hwS hwlo hval1
    · let j := w - (n + 2)
      have hj : j < C.gates.length := by have := hsub w hwS; omega
      by_cases hni : isNotOp (gateAt C j).op = true
      · exact hnot w hwS (by omega) hni hval1
      · have hgmem : gateAt C j ∈ C.gates := by
          have : gateAt C j = C.gates[j] := by simp [gateAt, List.getD, List.getElem?_eq_getElem hj]
          rw [this]; exact List.getElem_mem hj
        have hop_all := (hfan (gateAt C j) hgmem).1
        have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
          rcases hop_all with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · rw [h] at hni; simp [isNotOp] at hni
        have hweq : n + 2 + j = w := by omega
        have h1 : (C.wires x₁).getD w false =
            (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x₁).getD i false) := by
          have hg := wires_gate_eq C x₁ (by rwa [hx₁]) hj
          rwa [hx₁, hweq] at hg
        have h2 : (C.wires x₂).getD w false =
            (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x₂).getD i false) := by
          have hg := wires_gate_eq C x₂ (by rwa [hx₂]) hj
          rwa [hx₂, hweq] at hg
        rw [h1] at hval1
        rw [h2]
        apply gateOp_eval_mono (gateAt C j) hop _ _ _ hval1
        intro u hu
        have hueff : u ∈ eff C n w := by
          unfold eff
          rw [dif_pos ⟨by omega, hj⟩]
          exact hu
        exact ih u (eff_lt hrb hueff) (hclosed w hwS hueff)

end Part3_Cones

section Part4_LowerBound

def xList {n : ℕ} (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ [false, true]

lemma xList_length {n : ℕ} (x : Fin n → Bool) : (xList x).length = n + 2 := by
  simp [xList]

lemma xList_getD_fin {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    (xList x).getD u.val false = x u := by
  simp only [xList, List.getD]
  have hlt : u.val < (List.ofFn x).length := by simp
  rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt]
  simp

lemma xList_getD_n {n : ℕ} (x : Fin n → Bool) :
    (xList x).getD n false = false := by
  simp [xList, List.getD]

lemma xList_getD_n1 {n : ℕ} (x : Fin n → Bool) :
    (xList x).getD (n + 1) false = true := by
  simp [xList, List.getD]

def xTop (n : ℕ) : Fin n → Bool := fun _ => true

def xZero {n : ℕ} (u : Fin n) : Fin n → Bool := fun z => decide (z ≠ u)

lemma xTop_cover {n : ℕ} (G : Finset (Fin n × Fin n)) :
    ∀ e ∈ G, xTop n e.1 = true ∨ xTop n e.2 = true := by
  intro _ _; exact Or.inl rfl

lemma xZero_cover {n : ℕ} (G : Finset (Fin n × Fin n)) (hG : ∀ e ∈ G, e.1 < e.2)
    (u : Fin n) : ∀ e ∈ G, xZero u e.1 = true ∨ xZero u e.2 = true := by
  intro e he
  have hlt : e.1 ≠ e.2 := Fin.ne_of_lt (hG e he)
  by_cases h1 : e.1 = u
  · right; simp [xZero, Ne.symm (h1 ▸ hlt)]
  · left; simp [xZero, h1]

lemma xList_zero_le_top {n : ℕ} (u₀ : Fin n) {u : ℕ} (hu : u < n + 2) :
    (xList (xZero u₀)).getD u false = true → (xList (xTop n)).getD u false = true := by
  intro h
  by_cases hn : u < n
  · rw [xList_getD_fin (xTop n) ⟨u, hn⟩]; rfl
  · have hcases : u = n ∨ u = n + 1 := by omega
    rcases hcases with rfl | rfl
    · rw [xList_getD_n] at h; cases h
    · rw [xList_getD_n1]

lemma xList_zero_agrees_top {n : ℕ} (u₀ : Fin n) {u : ℕ} (hu : u < n + 2) (hne : u ≠ u₀.val) :
    (xList (xZero u₀)).getD u false = (xList (xTop n)).getD u false := by
  by_cases hn : u < n
  · rw [xList_getD_fin (xZero u₀) ⟨u, hn⟩, xList_getD_fin (xTop n) ⟨u, hn⟩]
    have hfin : (⟨u, hn⟩ : Fin n) ≠ u₀ := fun h => hne (congrArg Fin.val h)
    simp [xZero, xTop, hfin]
  · have hcases : u = n ∨ u = n + 1 := by omega
    rcases hcases with rfl | rfl
    · rw [xList_getD_n, xList_getD_n]
    · rw [xList_getD_n1, xList_getD_n1]

lemma lower_and_equality {n m : ℕ} (G : Finset (Fin n × Fin n)) (v : (Fin m × Bool) ↪ Fin n)
    (hG : ∀ e ∈ G, e.1 < e.2)
    (C : Circuit) (tap : Fin m → Fin (n + 2 + C.size))
    (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C)
    (hcomp : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
      ∀ i, (C.wires (List.ofFn x ++ [false, true])).getD (tap i).val false =
        xor (x (v (i, false))) (x (v (i, true)))) :
    2 * m ≤ C.size ∧ (C.size ≤ 2 * m → m ≤ notCount C) := by
  let val : (Fin n → Bool) → ℕ → Bool := fun x w => (C.wires (xList x)).getD w false
  have htap_top : ∀ i : Fin m, val (xTop n) (tap i).val = false := by
    intro i
    change (C.wires (List.ofFn (xTop n) ++ [false, true])).getD (tap i).val false = false
    rw [hcomp (xTop n) (xTop_cover G) i]
    simp [xTop]
  have htap_zero_self : ∀ i : Fin m, ∀ b : Bool, val (xZero (v (i, b))) (tap i).val = true := by
    intro i b
    change (C.wires (List.ofFn (xZero (v (i, b))) ++ [false, true])).getD (tap i).val false = true
    rw [hcomp (xZero (v (i, b))) (xZero_cover G hG _) i]
    cases b <;> simp [xZero, v.injective.eq_iff]
  have htap_zero_other : ∀ i j : Fin m, j ≠ i → ∀ b : Bool,
      val (xZero (v (i, b))) (tap j).val = false := by
    intro i j hji b
    change (C.wires (List.ofFn (xZero (v (i, b))) ++ [false, true])).getD (tap j).val false = false
    rw [hcomp (xZero (v (i, b))) (xZero_cover G hG _) j]
    have h1 : v (j, false) ≠ v (i, b) := fun h => hji (congrArg Prod.fst (v.injective h))
    have h2 : v (j, true) ≠ v (i, b) := fun h => hji (congrArg Prod.fst (v.injective h))
    simp [xZero, h1, h2]
  have htaps_lt : ∀ i : Fin m, (tap i).val < n + 2 + C.gates.length := fun i => (tap i).isLt
  have hendpoint_in_cone : ∀ i : Fin m, ∀ b : Bool,
      (v (i, b)).val ∈ cone C n (tap i).val := by
    intro i b
    by_contra hnmem
    have hsame : val (xZero (v (i, b))) (tap i).val = val (xTop n) (tap i).val := by
      apply cone_agrees hrb hfan (htaps_lt i) _ _ (xList_length _) (xList_length _)
      intro u hu hult
      have hne : u ≠ (v (i, b)).val := fun heq => hnmem (heq ▸ hu)
      exact xList_zero_agrees_top (v (i, b)) hult hne
    rw [htap_zero_self i b, htap_top i] at hsame
    cases hsame

  let U : Finset ℕ := Finset.univ.biUnion (fun i => cone C n (tap i).val)
  have hU_sub : ∀ w ∈ U, w < n + 2 + C.gates.length := by
    intro w hw
    rcases Finset.mem_biUnion.mp hw with ⟨i, _, hi⟩
    exact cone_lt_bound (htaps_lt i) hi
  have hU_closed : ∀ w ∈ U, eff C n w ⊆ U := by
    intro w hw u hu
    rcases Finset.mem_biUnion.mp hw with ⟨i, _, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, cone_closed hrb (htaps_lt i) w hi hu⟩
  let comp : ℕ → Finset ℕ := fun r => U.filter (fun w => decide (conn U (eff C n) r w))
  let CompSet : Finset (Finset ℕ) := Finset.univ.image (fun i => comp (tap i).val)
  let pairs : Finset ℕ → Finset (Fin m) := fun H => Finset.univ.filter (fun i => (tap i).val ∈ H)

  have hcomp_self : ∀ i : Fin m, (tap i).val ∈ comp (tap i).val := by
    intro i
    refine Finset.mem_filter.mpr ⟨?_, decide_eq_true (conn_refl _ _ _)⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, cone_self (htaps_lt i)⟩
  have hcomp_eq_of_mem : ∀ r₁ r₂ : ℕ, r₁ ∈ U → r₂ ∈ comp r₁ → comp r₁ = comp r₂ := by
    intro r₁ r₂ _ hr₂
    have hc : conn U (eff C n) r₁ r₂ := of_decide_eq_true (Finset.mem_filter.mp hr₂).2
    ext w
    simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hwU, h1w⟩
      exact ⟨hwU, decide_eq_true (conn_trans (conn_symm hc) (of_decide_eq_true h1w))⟩
    · rintro ⟨hwU, h2w⟩
      exact ⟨hwU, decide_eq_true (conn_trans hc (of_decide_eq_true h2w))⟩
  have hComp_disj : ∀ H₁ ∈ CompSet, ∀ H₂ ∈ CompSet, H₁ ≠ H₂ → Disjoint H₁ H₂ := by
    intro H₁ h1 H₂ h2 hne
    rcases Finset.mem_image.mp h1 with ⟨i₁, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨i₂, _, rfl⟩
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    have h12 : conn U (eff C n) (tap i₁).val (tap i₂).val :=
      conn_trans (of_decide_eq_true (Finset.mem_filter.mp hw1).2)
        (conn_symm (of_decide_eq_true (Finset.mem_filter.mp hw2).2))
    apply hne
    exact hcomp_eq_of_mem (tap i₁).val (tap i₂).val
      (Finset.mem_filter.mp (hcomp_self i₁)).1
      (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (hcomp_self i₂)).1, decide_eq_true h12⟩)

  have hpairs_disj : ∀ H₁ ∈ CompSet, ∀ H₂ ∈ CompSet, H₁ ≠ H₂ → Disjoint (pairs H₁) (pairs H₂) := by
    intro H₁ h1 H₂ h2 hne
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have hH : Disjoint H₁ H₂ := hComp_disj H₁ h1 H₂ h2 hne
    exact Finset.disjoint_left.mp hH (Finset.mem_filter.mp hi1).2 (Finset.mem_filter.mp hi2).2
  have hpairs_sum : ∑ H ∈ CompSet, (pairs H).card = m := by
    rw [← Finset.card_biUnion]
    · have huniv : CompSet.biUnion pairs = Finset.univ := by
        ext i
        simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
        exact ⟨comp (tap i).val, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcomp_self i⟩⟩
      rw [huniv, Finset.card_univ, Fintype.card_fin]
    · intro H₁ h1 H₂ h2 hne; exact hpairs_disj H₁ h1 H₂ h2 hne

  let H_inp : Finset ℕ → Finset ℕ := fun H => H.filter (· < n + 2)
  let H_gates : Finset ℕ → Finset ℕ := fun H => H.filter (n + 2 ≤ ·)
  let H_not : Finset ℕ → Finset ℕ := fun H =>
    (H_gates H).filter (fun w => isNotOp (gateAt C (w - (n + 2))).op = true)
  let H_bin : Finset ℕ → Finset ℕ := fun H =>
    (H_gates H).filter (fun w => !isNotOp (gateAt C (w - (n + 2))).op && decide ((eff C n w).card = 2))
  let H_una : Finset ℕ → Finset ℕ := fun H =>
    (H_gates H).filter (fun w => !isNotOp (gateAt C (w - (n + 2))).op && decide ((eff C n w).card ≤ 1))
  let H_zeroNot : Finset ℕ → Finset ℕ := fun H =>
    (H_not H).filter (fun w => (eff C n w).card = 0)

  have hH_props : ∀ H ∈ CompSet,
      (∀ w ∈ H, w < n + 2 + C.gates.length) ∧
      (∀ w ∈ H, eff C n w ⊆ H) ∧
      (∀ a ∈ H, ∀ b ∈ H, conn H (eff C n) a b) ∧
      H.Nonempty ∧
      (pairs H).Nonempty ∧
      2 * (pairs H).card ≤ (H_inp H).card ∧
      (H_not H).Nonempty ∧
      2 * (pairs H).card ≤ (H_gates H).card ∧
      ((H_gates H).card ≤ 2 * (pairs H).card →
        (H_inp H).card = 2 * (pairs H).card ∧
        (H_una H).card = 0 ∧
        (H_zeroNot H).card = 0 ∧
        (H_not H).card = 1 ∧
        (H_bin H).card = 2 * (pairs H).card - 1) ∧
      (H_gates H = H_not H ∪ H_bin H ∪ H_una H) := by
    intro H hH
    rcases Finset.mem_image.mp hH with ⟨i₀, _, rfl⟩
    set H := comp (tap i₀).val
    have hH_subU : H ⊆ U := Finset.filter_subset _ _
    have hH_lt : ∀ w ∈ H, w < n + 2 + C.gates.length :=
      fun w hw => hU_sub w (hH_subU hw)
    have hH_step_closed : ∀ a ∈ H, ∀ b,
        stepFrom U (eff C n) a b → b ∈ H := by
      intro a ha b hs
      have haU : a ∈ U := hH_subU ha
      have ha_conn := of_decide_eq_true (Finset.mem_filter.mp ha).2
      have hbU : b ∈ U := by
        rcases hs with ⟨_, hab⟩ | ⟨hbU, _⟩
        · exact hU_closed a haU hab
        · exact hbU
      have hconn_b : conn U (eff C n) (tap i₀).val b :=
        Relation.ReflTransGen.trans ha_conn (Relation.ReflTransGen.single hs)
      exact Finset.mem_filter.mpr ⟨hbU, decide_eq_true hconn_b⟩
    have hH_closed : ∀ w ∈ H, eff C n w ⊆ H := by
      intro w hw u hu
      exact hH_step_closed w hw u (Or.inl ⟨hH_subU hw, hu⟩)
    have hH_conn : ∀ a ∈ H, ∀ b ∈ H, conn H (eff C n) a b := by
      intro a ha b hb
      have hU_ab : conn U (eff C n) a b :=
        conn_trans (conn_symm (of_decide_eq_true (Finset.mem_filter.mp ha).2))
          (of_decide_eq_true (Finset.mem_filter.mp hb).2)
      exact conn_mono_sub hH_step_closed ha hU_ab
    have hH_ne : H.Nonempty := ⟨(tap i₀).val, hcomp_self i₀⟩
    have hp_ne : (pairs H).Nonempty :=
      ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcomp_self i₀⟩⟩
    have hend_sub : (pairs H ×ˢ (Finset.univ : Finset Bool)).image
        (fun ib : Fin m × Bool => (v ib).val) ⊆ H_inp H := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨⟨i, b⟩, hib, rfl⟩
      have hiH : (tap i).val ∈ H :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hib).1).2
      have hcomp_eq : H = comp (tap i).val :=
        hcomp_eq_of_mem (tap i₀).val (tap i).val (hH_subU (hcomp_self i₀)) hiH
      have hvc : (v (i, b)).val ∈ cone C n (tap i).val := hendpoint_in_cone i b
      have hv_conn : conn U (eff C n) (tap i).val (v (i, b)).val := by
        apply conn_lift (A := cone C n (tap i).val) (B := U)
        · intro x hx; exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
        · exact cone_conn hrb (htaps_lt i) _ hvc
      have hvU : (v (i, b)).val ∈ U := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hvc⟩
      have hv_in_comp : (v (i, b)).val ∈ comp (tap i).val :=
        Finset.mem_filter.mpr ⟨hvU, decide_eq_true hv_conn⟩
      rw [← hcomp_eq] at hv_in_comp
      exact Finset.mem_filter.mpr ⟨hv_in_comp, Nat.lt_trans (v (i, b)).isLt (by omega)⟩
    have h2p_le_inp : 2 * (pairs H).card ≤ (H_inp H).card := by
      have hinj : Function.Injective (fun ib : Fin m × Bool => (v ib).val) :=
        Fin.val_injective.comp v.injective
      have hc := Finset.card_le_card hend_sub
      rw [Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_univ,
        Fintype.card_bool, Nat.mul_comm] at hc
      exact hc
    have hnot_ne : (H_not H).Nonempty := by
      by_contra hem
      rw [Finset.not_nonempty_iff_eq_empty] at hem
      have hmono := monotone_on_closed hrb hfan hH_lt hH_closed
        (xList (xZero (v (i₀, false)))) (xList (xTop n)) (xList_length _) (xList_length _)
        (fun u _ hult h => xList_zero_le_top (v (i₀, false)) hult h)
        (fun w hw hlo hni _ => by
          have hw_not : w ∈ H_not H :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hw, hlo⟩, hni⟩
          rw [hem] at hw_not; simp at hw_not)
      have htap_val : val (xTop n) (tap i₀).val = true :=
        hmono (tap i₀).val (hcomp_self i₀) (htap_zero_self i₀ false)
      rw [htap_top i₀] at htap_val
      cases htap_val
    have hH_part_gates : H_gates H = H_not H ∪ H_bin H ∪ H_una H := by
      ext w
      simp only [H_gates, H_not, H_bin, H_una, Finset.mem_union, Finset.mem_filter, Bool.and_eq_true,
        Bool.not_eq_true', decide_eq_true_eq]
      constructor
      · intro hwG
        have hwlt : w < n + 2 + C.gates.length := hH_lt w hwG.1
        by_cases hno : isNotOp (gateAt C (w - (n + 2))).op = true
        · left; left; exact ⟨hwG, hno⟩
        · have hnoF : isNotOp (gateAt C (w - (n + 2))).op = false :=
            Bool.eq_false_iff.mpr hno
          have hj : w - (n + 2) < C.gates.length := by omega
          have hmem : gateAt C (w - (n + 2)) ∈ C.gates := by
            have heq : gateAt C (w - (n + 2)) = C.gates[w - (n + 2)] := by
              simp [gateAt, List.getD, List.getElem?_eq_getElem hj]
            rw [heq]; exact List.getElem_mem hj
          have hlen : (gateAt C (w - (n + 2))).inputs.length ≤ 2 := (hfan _ hmem).2
          have heff_eq : eff C n w = (gateAt C (w - (n + 2))).inputs.toFinset := by
            unfold eff effInputsGate
            rw [dif_pos ⟨hwG.2, hj⟩, hnoF]; rfl
          have hcard2 : (eff C n w).card ≤ 2 := by
            rw [heff_eq]; exact (List.toFinset_card_le _).trans hlen
          by_cases hc2 : (eff C n w).card = 2
          · left; right; exact ⟨hwG, hnoF, hc2⟩
          · right; exact ⟨hwG, hnoF, by omega⟩
      · rintro ((⟨hwG, _⟩ | ⟨hwG, _⟩) | ⟨hwG, _⟩) <;> exact hwG
    have hdisj_nb : Disjoint (H_not H) (H_bin H) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      have a := (Finset.mem_filter.mp h1).2
      have b := (Finset.mem_filter.mp h2).2
      simp [a] at b
    have hdisj_nu : Disjoint (H_not H) (H_una H) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      have a := (Finset.mem_filter.mp h1).2
      have b := (Finset.mem_filter.mp h2).2
      simp [a] at b
    have hdisj_bu : Disjoint (H_bin H) (H_una H) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      have h1f := (Finset.mem_filter.mp h1).2
      have h2f := (Finset.mem_filter.mp h2).2
      have a : (eff C n w).card = 2 := by
        simpa [Bool.and_eq_true, decide_eq_true_eq] using (Bool.and_eq_true _ _ |>.mp h1f).2
      have b : (eff C n w).card ≤ 1 := by
        simpa [Bool.and_eq_true, decide_eq_true_eq] using (Bool.and_eq_true _ _ |>.mp h2f).2
      omega
    have hgates_card : (H_gates H).card = (H_not H).card + (H_bin H).card + (H_una H).card := by
      rw [hH_part_gates, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint hdisj_nb]
      exact Finset.disjoint_union_left.mpr ⟨hdisj_nu, hdisj_bu⟩
    have hH_split : H = H_inp H ∪ H_gates H := by
      ext w
      simp only [H_inp, H_gates, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hw; by_cases hlt : w < n + 2 <;> [left; right] <;> exact ⟨hw, by omega⟩
      · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
    have hdisj_ig : Disjoint (H_inp H) (H_gates H) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      have h1lt := (Finset.mem_filter.mp h1).2
      have h2ge := (Finset.mem_filter.mp h2).2
      omega
    have hH_card : H.card = (H_inp H).card + (H_gates H).card := by
      conv_lhs => rw [hH_split]
      rw [Finset.card_union_of_disjoint hdisj_ig]
    have htree := card_le_sum_eff hH_closed hH_ne hH_conn
    have hsum_split : ∑ w ∈ H, (eff C n w).card =
        (∑ w ∈ H_inp H, (eff C n w).card) +
        ((∑ w ∈ H_not H, (eff C n w).card) + (∑ w ∈ H_bin H, (eff C n w).card) +
          (∑ w ∈ H_una H, (eff C n w).card)) := by
      conv_lhs => rw [hH_split, Finset.sum_union hdisj_ig, hH_part_gates,
        Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdisj_nu, hdisj_bu⟩),
        Finset.sum_union hdisj_nb]
    have hsum_inp : ∑ w ∈ H_inp H, (eff C n w).card = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      have hlt : w < n + 2 := (Finset.mem_filter.mp hw).2
      unfold eff; rw [dif_neg (by omega)]; simp
    have hsum_bin : ∑ w ∈ H_bin H, (eff C n w).card = 2 * (H_bin H).card := by
      calc ∑ w ∈ H_bin H, (eff C n w).card
          = ∑ _w ∈ H_bin H, 2 := Finset.sum_congr rfl fun w hw => by
              have hwf := (Finset.mem_filter.mp hw).2
              simpa [Bool.and_eq_true, decide_eq_true_eq] using (Bool.and_eq_true _ _ |>.mp hwf).2
        _ = 2 * (H_bin H).card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    have hsum_una : ∑ w ∈ H_una H, (eff C n w).card ≤ (H_una H).card := by
      calc ∑ w ∈ H_una H, (eff C n w).card
          ≤ ∑ _w ∈ H_una H, 1 := Finset.sum_le_sum fun w hw => by
              have hwf := (Finset.mem_filter.mp hw).2
              simpa [Bool.and_eq_true, decide_eq_true_eq] using (Bool.and_eq_true _ _ |>.mp hwf).2
        _ = (H_una H).card := by simp
    have hsum_not : ∑ w ∈ H_not H, (eff C n w).card + (H_zeroNot H).card ≤ (H_not H).card := by
      have hzn_sub : H_zeroNot H ⊆ H_not H := Finset.filter_subset _ _
      have hsdiff : (H_not H) = H_zeroNot H ∪ (H_not H \ H_zeroNot H) :=
        (Finset.union_sdiff_of_subset hzn_sub).symm
      have hdisj_zn : Disjoint (H_zeroNot H) (H_not H \ H_zeroNot H) :=
        Finset.disjoint_left.mpr fun _ hw1 hw2 => (Finset.mem_sdiff.mp hw2).2 hw1
      have hsum0 : ∑ w ∈ H_zeroNot H, (eff C n w).card = 0 :=
        Finset.sum_eq_zero fun w hw => (Finset.mem_filter.mp hw).2
      have hsum1 : ∑ w ∈ (H_not H \ H_zeroNot H), (eff C n w).card ≤ (H_not H \ H_zeroNot H).card := by
        calc ∑ w ∈ (H_not H \ H_zeroNot H), (eff C n w).card
            ≤ ∑ _w ∈ (H_not H \ H_zeroNot H), 1 := by
              apply Finset.sum_le_sum
              intro w hw
              have hwn : w ∈ H_not H := (Finset.mem_sdiff.mp hw).1
              have hwG := (Finset.mem_filter.mp hwn).1
              have hlo : n + 2 ≤ w := (Finset.mem_filter.mp hwG).2
              have hlt : w < n + 2 + C.gates.length := hH_lt w (Finset.mem_filter.mp hwG).1
              have hni : isNotOp (gateAt C (w - (n + 2))).op = true := (Finset.mem_filter.mp hwn).2
              unfold eff effInputsGate
              rw [dif_pos ⟨hlo, by omega⟩, if_pos hni]
              cases (gateAt C (w - (n + 2))).inputs <;> simp
          _ = (H_not H \ H_zeroNot H).card := by simp
      have hcard_zn : (H_not H).card = (H_zeroNot H).card + (H_not H \ H_zeroNot H).card := by
        conv_lhs => rw [hsdiff]
        rw [Finset.card_union_of_disjoint hdisj_zn]
      conv_lhs => rw [hsdiff, Finset.sum_union hdisj_zn, hsum0, Nat.zero_add]
      omega
    have hnot_pos : 1 ≤ (H_not H).card := Finset.card_pos.mpr hnot_ne
    have h2p_inp_H : 2 * (pairs H).card ≤ (H_inp H).card := h2p_le_inp
    have hsum_bd : (∑ w ∈ H, (eff C n w).card) + (H_zeroNot H).card ≤
        2 * (H_bin H).card + (H_una H).card + (H_not H).card := by
      rw [hsum_split, hsum_inp, hsum_bin]
      omega
    have h2p_gates : 2 * (pairs H).card ≤ (H_gates H).card := by omega
    refine ⟨hH_lt, hH_closed, hH_conn, hH_ne, hp_ne, h2p_le_inp, hnot_ne, h2p_gates, ?_, hH_part_gates⟩
    intro hle
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩

  have hgates_disj : ∀ H₁ ∈ CompSet, ∀ H₂ ∈ CompSet, H₁ ≠ H₂ → Disjoint (H_gates H₁) (H_gates H₂) :=
    fun H₁ h1 H₂ h2 hne => Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hComp_disj H₁ h1 H₂ h2 hne))
  have hgates_sub : CompSet.biUnion H_gates ⊆ (Finset.range C.gates.length).image (fun j => n + 2 + j) := by
    intro w hw
    rcases Finset.mem_biUnion.mp hw with ⟨H, hH, hwG⟩
    have hwlt := (hH_props H hH).1 w (Finset.mem_filter.mp hwG).1
    have hwlo : n + 2 ≤ w := (Finset.mem_filter.mp hwG).2
    exact Finset.mem_image.mpr ⟨w - (n + 2), Finset.mem_range.mpr (by omega), by omega⟩
  have hsum_gates_le_size : ∑ H ∈ CompSet, (H_gates H).card ≤ C.size := by
    rw [← Finset.card_biUnion hgates_disj]
    have hc := Finset.card_le_card hgates_sub
    rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range] at hc
    exact hc
  have h2m_le_sum : 2 * m ≤ ∑ H ∈ CompSet, (H_gates H).card := by
    calc 2 * m = 2 * ∑ H ∈ CompSet, (pairs H).card := by rw [hpairs_sum]
      _ = ∑ H ∈ CompSet, 2 * (pairs H).card := by rw [Finset.mul_sum]
      _ ≤ ∑ H ∈ CompSet, (H_gates H).card := Finset.sum_le_sum fun H hH => (hH_props H hH).2.2.2.2.2.2.2.1
  have h2m_le_size : 2 * m ≤ C.size := h2m_le_sum.trans hsum_gates_le_size
  refine ⟨h2m_le_size, ?_⟩
  intro hsize_le
  have hall_eq : ∀ H ∈ CompSet, (H_gates H).card ≤ 2 * (pairs H).card := by
    intro H hH
    by_contra hgt
    have hlt : 2 * (pairs H).card < (H_gates H).card := Nat.lt_of_not_le hgt
    have hsum_gt : ∑ K ∈ CompSet, 2 * (pairs K).card < ∑ K ∈ CompSet, (H_gates K).card := by
      have hsplit1 : ∑ K ∈ CompSet, 2 * (pairs K).card =
          2 * (pairs H).card + ∑ K ∈ CompSet.erase H, 2 * (pairs K).card :=
        (Finset.add_sum_erase CompSet (fun K => 2 * (pairs K).card) hH).symm
      have hsplit2 : ∑ K ∈ CompSet, (H_gates K).card =
          (H_gates H).card + ∑ K ∈ CompSet.erase H, (H_gates K).card :=
        (Finset.add_sum_erase CompSet (fun K => (H_gates K).card) hH).symm
      have her : ∑ K ∈ CompSet.erase H, 2 * (pairs K).card ≤
          ∑ K ∈ CompSet.erase H, (H_gates K).card :=
        Finset.sum_le_sum fun K hK => (hH_props K (Finset.mem_of_mem_erase hK)).2.2.2.2.2.2.2.1
      rw [hsplit1, hsplit2]
      omega
    have h2m_eq : 2 * m = ∑ K ∈ CompSet, 2 * (pairs K).card := by
      calc 2 * m = 2 * ∑ K ∈ CompSet, (pairs K).card := by rw [hpairs_sum]
        _ = ∑ K ∈ CompSet, 2 * (pairs K).card := by rw [Finset.mul_sum]
    omega

  have heach_one : ∀ H ∈ CompSet, (pairs H).card = (H_not H).card := by
    intro H hH
    have ⟨hH_lt, hH_closed, _, _, hp_ne, h2p_le_inp, _, _, hEq, hH_part_gates⟩ := hH_props H hH
    obtain ⟨hinp_eq, huna_eq, hzn_eq, hnot_eq, hbin_eq⟩ := hEq (hall_eq H hH)
    obtain ⟨gnot, hgnot_set⟩ := Finset.card_eq_one.mp hnot_eq
    have hgnot_mem : gnot ∈ H_not H := by rw [hgnot_set]; exact Finset.mem_singleton_self _
    have hgnot_H : gnot ∈ H := (Finset.mem_filter.mp (Finset.mem_filter.mp hgnot_mem).1).1
    have hgnot_lo : n + 2 ≤ gnot := (Finset.mem_filter.mp (Finset.mem_filter.mp hgnot_mem).1).2
    have hgnot_hi : gnot < n + 2 + C.gates.length := hH_lt gnot hgnot_H
    have hgnot_ni : isNotOp (gateAt C (gnot - (n + 2))).op = true :=
      (Finset.mem_filter.mp hgnot_mem).2
    have hgnot_op : (gateAt C (gnot - (n + 2))).op = GateOp.not :=
      (isNotOp_eq_true _).mp hgnot_ni
    have hgnot_nz : (eff C n gnot).card ≠ 0 := by
      intro hc0
      have hzmem : gnot ∈ H_zeroNot H := Finset.mem_filter.mpr ⟨hgnot_mem, hc0⟩
      rw [Finset.card_eq_zero.mp hzn_eq] at hzmem; simp at hzmem
    have hgnot_le1 : (eff C n gnot).card ≤ 1 := by
      unfold eff effInputsGate
      rw [dif_pos ⟨hgnot_lo, by omega⟩, if_pos hgnot_ni]
      cases (gateAt C (gnot - (n + 2))).inputs <;> simp
    have hgnot_c1 : (eff C n gnot).card = 1 := by omega
    obtain ⟨win, hwin_set⟩ := Finset.card_eq_one.mp hgnot_c1
    have hwin_eff : win ∈ eff C n gnot := by rw [hwin_set]; exact Finset.mem_singleton_self _
    have hwin_lt_gnot : win < gnot := eff_lt hrb hwin_eff
    have hwin_H : win ∈ H := hH_closed gnot hgnot_H hwin_eff
    have hwin_hi : win < n + 2 + C.gates.length := hH_lt win hwin_H

    have hnot_eval : ∀ x : Fin n → Bool, val x gnot = !(val x win) := by
      intro x
      have hj : gnot - (n + 2) < C.gates.length := by omega
      have hg := wires_gate_eq C (xList x) (by rw [xList_length]; exact hrb) hj
      have hweq : (xList x).length + (gnot - (n + 2)) = gnot := by rw [xList_length]; omega
      rw [hweq] at hg
      have hinp_nonnil : ∃ l, (gateAt C (gnot - (n + 2))).inputs = win :: l := by
        unfold eff effInputsGate at hwin_set
        rw [dif_pos ⟨hgnot_lo, hj⟩, if_pos hgnot_ni] at hwin_set
        cases hlst : (gateAt C (gnot - (n + 2))).inputs with
        | nil => rw [hlst] at hwin_set; simp at hwin_set
        | cons u l =>
          rw [hlst] at hwin_set
          have huw : u = win := Finset.singleton_injective hwin_set
          subst huw; exact ⟨l, rfl⟩
      rcases hinp_nonnil with ⟨l, hl⟩
      change val x gnot = !(val x win)
      dsimp [val]
      rw [hg, hgnot_op, hl]
      simp [GateOp.eval]

    have hwin_in_cone : ∀ i ∈ pairs H, ∀ b : Bool, (v (i, b)).val ∈ cone C n win := by
      intro i hi b
      have hnot_rise : val (xZero (v (i, b))) gnot = true ∧ val (xTop n) gnot = false := by
        by_contra hbad
        have hnot_mono : val (xZero (v (i, b))) gnot = true → val (xTop n) gnot = true := by
          intro h1
          cases h2 : val (xTop n) gnot with
          | true => rfl
          | false => exact False.elim (hbad ⟨h1, h2⟩)
        have hmono := monotone_on_closed hrb hfan hH_lt hH_closed
          (xList (xZero (v (i, b)))) (xList (xTop n)) (xList_length _) (xList_length _)
          (fun u _ hult h => xList_zero_le_top (v (i, b)) hult h)
          (fun w hw hlo hni h1 => by
            have hw_not : w ∈ H_not H := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hw, hlo⟩, hni⟩
            rw [hgnot_set, Finset.mem_singleton] at hw_not
            subst hw_not
            exact hnot_mono h1)
        have hiH : (tap i).val ∈ H := (Finset.mem_filter.mp hi).2
        have hres : val (xTop n) (tap i).val = true := hmono (tap i).val hiH (htap_zero_self i b)
        rw [htap_top i] at hres
        cases hres
      have hwin0 : val (xZero (v (i, b))) win = false := by
        have h := hnot_eval (xZero (v (i, b)))
        rw [hnot_rise.1] at h
        cases hvw : val (xZero (v (i, b))) win <;> simp [hvw] at h; rfl
      have hwin1 : val (xTop n) win = true := by
        have h := hnot_eval (xTop n)
        rw [hnot_rise.2] at h
        cases hvw : val (xTop n) win <;> simp [hvw] at h; rfl
      by_contra hnmem
      have hsame : val (xZero (v (i, b))) win = val (xTop n) win := by
        apply cone_agrees hrb hfan hwin_hi _ _ (xList_length _) (xList_length _)
        intro u hu hult
        exact xList_zero_agrees_top (v (i, b)) hult (fun heq => hnmem (heq ▸ hu))
      rw [hwin0, hwin1] at hsame
      cases hsame

    let K := cone C n win
    have hK_sub_H : K ⊆ H := cone_sub_of_closed hrb hH_closed hwin_hi hwin_H
    have hK_ne : K.Nonempty := ⟨win, cone_self hwin_hi⟩
    have hK_closed : ∀ w ∈ K, eff C n w ⊆ K := cone_closed hrb hwin_hi
    have hK_conn : ∀ a ∈ K, ∀ b ∈ K, conn K (eff C n) a b := cone_all_conn hrb hwin_hi
    have hK_lt : ∀ w ∈ K, w < n + 2 + C.gates.length := fun w hw => hH_lt w (hK_sub_H hw)
    have hgnot_nmem_K : gnot ∉ K := fun hmem => by
      have := cone_le hmem
      omega
    have hK_bin_sub : H_bin K ⊆ H_bin H := by
      intro w hw
      simp only [H_bin, H_gates, Finset.mem_filter] at hw ⊢
      exact ⟨⟨hK_sub_H hw.1.1, hw.1.2⟩, hw.2⟩
    have hK_split_sub : K ⊆ H_inp K ∪ H_bin H := by
      intro w hw
      rw [Finset.mem_union]
      by_cases hwlo : w < n + 2
      · left; exact Finset.mem_filter.mpr ⟨hw, hwlo⟩
      · right
        have hwH : w ∈ H := hK_sub_H hw
        have hwG : w ∈ H_gates H := Finset.mem_filter.mpr ⟨hwH, by omega⟩
        have hpart : w ∈ H_not H ∪ H_bin H ∪ H_una H := by
          rw [hH_part_gates] at hwG; exact hwG
        have hnot_una : ∀ x, x ∈ H_una H → False := by
          intro x hx; rw [Finset.card_eq_zero.mp huna_eq] at hx; simp at hx
        rcases Finset.mem_union.mp hpart with hnb | hu
        · rcases Finset.mem_union.mp hnb with hn | hb
          · rw [hgnot_set, Finset.mem_singleton] at hn
            subst hn
            exact False.elim (hgnot_nmem_K hw)
          · exact hb
        · exact False.elim (hnot_una w hu)
    have hK_sub_part : K ⊆ H_inp K ∪ H_bin K := by
      intro w hw
      rw [Finset.mem_union]
      by_cases hwlo : w < n + 2
      · left; exact Finset.mem_filter.mpr ⟨hw, hwlo⟩
      · right
        have hw_in : w ∈ H_inp K ∪ H_bin H := hK_split_sub hw
        rcases Finset.mem_union.mp hw_in with hi | hb
        · have := (Finset.mem_filter.mp hi).2; omega
        · simp only [H_bin, H_gates, Finset.mem_filter] at hb ⊢
          exact ⟨⟨hw, hb.1.2⟩, hb.2⟩
    have hK_disj : Disjoint (H_inp K) (H_bin K) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      have h1lt := (Finset.mem_filter.mp h1).2
      have h2ge := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
      omega
    have hK_eq_union : K = H_inp K ∪ H_bin K :=
      Finset.Subset.antisymm hK_sub_part
        (Finset.union_subset (Finset.filter_subset _ _)
          ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)))
    have hK_card : K.card = (H_inp K).card + (H_bin K).card := by
      conv_lhs => rw [hK_eq_union]
      rw [Finset.card_union_of_disjoint hK_disj]
    have hK_sum : ∑ w ∈ K, (eff C n w).card ≤ 2 * (H_bin K).card := by
      conv_lhs => rw [hK_eq_union, Finset.sum_union hK_disj]
      have h0 : ∑ w ∈ H_inp K, (eff C n w).card = 0 := by
        apply Finset.sum_eq_zero; intro w hw
        have hlt := (Finset.mem_filter.mp hw).2
        unfold eff; rw [dif_neg (by omega)]; simp
      have h2 : ∑ w ∈ H_bin K, (eff C n w).card = 2 * (H_bin K).card := by
        calc ∑ w ∈ H_bin K, (eff C n w).card
            = ∑ _w ∈ H_bin K, 2 := Finset.sum_congr rfl fun w hw => by
                have hwf := (Finset.mem_filter.mp hw).2
                simpa [Bool.and_eq_true, decide_eq_true_eq] using (Bool.and_eq_true _ _ |>.mp hwf).2
          _ = 2 * (H_bin K).card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      omega
    have hK_tree := card_le_sum_eff hK_closed hK_ne hK_conn
    have hK_end_sub : (pairs H ×ˢ (Finset.univ : Finset Bool)).image
        (fun ib : Fin m × Bool => (v ib).val) ⊆ H_inp K := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨⟨i, b⟩, hib, rfl⟩
      have hiH : i ∈ pairs H := (Finset.mem_product.mp hib).1
      exact Finset.mem_filter.mpr ⟨hwin_in_cone i hiH b, Nat.lt_trans (v (i, b)).isLt (by omega)⟩
    have h2p_le_Kinp : 2 * (pairs H).card ≤ (H_inp K).card := by
      have hinj : Function.Injective (fun ib : Fin m × Bool => (v ib).val) :=
        Fin.val_injective.comp v.injective
      have hc := Finset.card_le_card hK_end_sub
      rw [Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_univ,
        Fintype.card_bool, Nat.mul_comm] at hc
      exact hc
    have hK_bin_ge : 2 * (pairs H).card - 1 ≤ (H_bin K).card := by omega
    have hK_bin_eq : H_bin K = H_bin H :=
      Finset.eq_of_subset_of_card_le hK_bin_sub (by rw [hbin_eq]; exact hK_bin_ge)
    have hbin_sub_K : H_bin H ⊆ K := by
      rw [← hK_bin_eq]
      exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have htap_is_gnot : ∀ i ∈ pairs H, (tap i).val = gnot := by
      intro i hi
      have htap_H : (tap i).val ∈ H := (Finset.mem_filter.mp hi).2
      have hK_mono : ∀ w ∈ K, val (xZero (v (i, false))) w = true → val (xTop n) w = true := by
        apply monotone_on_closed hrb hfan hK_lt hK_closed
          (xList (xZero (v (i, false)))) (xList (xTop n)) (xList_length _) (xList_length _)
        · intro u _ hult h; exact xList_zero_le_top (v (i, false)) hult h
        · intro w hw hlo hni _
          have hw_in : w ∈ H_inp K ∪ H_bin H := hK_split_sub hw
          rcases Finset.mem_union.mp hw_in with h1 | h2
          · have := (Finset.mem_filter.mp h1).2; omega
          · have h2f := (Finset.mem_filter.mp h2).2
            have : !isNotOp (gateAt C (w - (n + 2))).op = true := (Bool.and_eq_true _ _ |>.mp h2f).1
            simp [hni] at this
      by_cases hlo : (tap i).val < n + 2
      · exfalso
        have h1 : val (xZero (v (i, false))) (tap i).val = true := htap_zero_self i false
        have h2 : val (xTop n) (tap i).val = true := by
          dsimp [val] at h1 ⊢
          rw [wires_getD_lt C _ (by rw [xList_length]; exact hlo)] at h1
          rw [wires_getD_lt C _ (by rw [xList_length]; exact hlo)]
          exact xList_zero_le_top (v (i, false)) hlo h1
        rw [htap_top i] at h2; cases h2
      · have htap_G : (tap i).val ∈ H_gates H := Finset.mem_filter.mpr ⟨htap_H, by omega⟩
        rw [hH_part_gates] at htap_G
        rcases Finset.mem_union.mp htap_G with hnb | hu
        · rcases Finset.mem_union.mp hnb with hn | hb
          · rw [hgnot_set, Finset.mem_singleton] at hn
            exact hn
          · exfalso
            have hres : val (xTop n) (tap i).val = true :=
              hK_mono (tap i).val (hbin_sub_K hb) (htap_zero_self i false)
            rw [htap_top i] at hres
            cases hres
        · rw [Finset.card_eq_zero.mp huna_eq] at hu
          simp at hu
    have hp_le1 : (pairs H).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hne
      have hga := htap_is_gnot a ha
      have hgb := htap_is_gnot b hb
      have h1 := htap_zero_self a false
      have h2 := htap_zero_other a b (Ne.symm hne) false
      rw [hga, ← hgb, h2] at h1
      cases h1
    have hp_pos : 1 ≤ (pairs H).card := Finset.card_pos.mpr hp_ne
    omega

  have hnot_disj : ∀ H₁ ∈ CompSet, ∀ H₂ ∈ CompSet, H₁ ≠ H₂ → Disjoint (H_not H₁) (H_not H₂) :=
    fun H₁ h1 H₂ h2 hne => Finset.disjoint_of_subset_left
      ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
      (Finset.disjoint_of_subset_right
        ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)) (hComp_disj H₁ h1 H₂ h2 hne))
  have hnot_sub : CompSet.biUnion H_not ⊆
      ((Finset.range C.gates.length).filter (fun j => isNotOp (gateAt C j).op = true)).image
        (fun j => n + 2 + j) := by
    intro w hw
    rcases Finset.mem_biUnion.mp hw with ⟨H, hH, hwN⟩
    have hwG := (Finset.mem_filter.mp hwN).1
    have hwlt := (hH_props H hH).1 w (Finset.mem_filter.mp hwG).1
    have hwlo : n + 2 ≤ w := (Finset.mem_filter.mp hwG).2
    have hni := (Finset.mem_filter.mp hwN).2
    exact Finset.mem_image.mpr ⟨w - (n + 2),
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hni⟩, by omega⟩
  calc m = ∑ H ∈ CompSet, (pairs H).card := hpairs_sum.symm
    _ = ∑ H ∈ CompSet, (H_not H).card := Finset.sum_congr rfl heach_one
    _ = (CompSet.biUnion H_not).card := (Finset.card_biUnion hnot_disj).symm
    _ ≤ (((Finset.range C.gates.length).filter (fun j => isNotOp (gateAt C j).op = true)).image
          (fun j => n + 2 + j)).card := Finset.card_le_card hnot_sub
    _ = ((Finset.range C.gates.length).filter (fun j => isNotOp (gateAt C j).op = true)).card :=
          Finset.card_image_of_injective _ (fun a b h => by omega)
    _ = notCount C := (notCount_eq_card C).symm

end Part4_LowerBound

section Part5_UpperBound

lemma upper_construction {n m : ℕ} (G : Finset (Fin n × Fin n)) (v : (Fin m × Bool) ↪ Fin n)
    (hadj : ∀ i : Fin m, (v (i, false), v (i, true)) ∈ G ∨ (v (i, true), v (i, false)) ∈ G)
    {r : ℕ} (hr : m ≤ r) :
    ∃ (C : Circuit) (tap : Fin m → Fin (n + 2 + C.size)),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
      C.size ≤ 2 * m ∧ notCount C ≤ r ∧
      ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
        ∀ i, (C.wires (List.ofFn x ++ [false, true])).getD (tap i).val false =
          xor (x (v (i, false))) (x (v (i, true))) := by
  let gates : List Gate := List.ofFn fun q : Fin (2 * m) =>
    let i : Fin m := ⟨q.val / 2, Nat.div_lt_of_lt_mul (by omega)⟩
    if q.val % 2 = 0 then
      ⟨GateOp.and, [(v (i, false)).val, (v (i, true)).val]⟩
    else
      ⟨GateOp.not, [n + 2 + 2 * i.val]⟩
  let C : Circuit := ⟨gates, 0⟩
  have hlen : C.size = 2 * m := by simp [C, Circuit.size, gates]
  let tap : Fin m → Fin (n + 2 + C.size) := fun i => ⟨n + 2 + (2 * i.val + 1), by omega⟩
  refine ⟨C, tap, ?_, ?_, ?_, by omega, ?_, ?_⟩
  · intro g hg
    rw [List.mem_ofFn] at hg
    rcases hg with ⟨q, rfl⟩
    dsimp only
    split_ifs <;> simp
  · intro j hj u hu
    change j < gates.length at hj
    have hgate : gateAt C j = gates[j] := by simp [gateAt, C, List.getD, List.getElem?_eq_getElem hj]
    rw [hgate] at hu
    simp only [gates, List.getElem_ofFn] at hu
    split_ifs at hu with hmod
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact Nat.lt_trans (v _).isLt (by omega)
      · exact Nat.lt_trans (v _).isLt (by omega)
    · simp only [List.mem_singleton] at hu
      subst hu
      have hlt : 2 * (j / 2) < j := by omega
      omega
  · simp [C]
  · rw [notCount_eq_card]
    have hset : (Finset.range C.gates.length).filter (fun j => isNotOp (gateAt C j).op = true) =
        (Finset.univ : Finset (Fin m)).image (fun i => 2 * i.val + 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hj, hni⟩
        have hj2 : j < 2 * m := by change j < C.size at hj; omega
        have hgate : gateAt C j = gates[j] := by simp [gateAt, C, List.getD, List.getElem?_eq_getElem hj]
        rw [hgate] at hni
        simp only [gates, List.getElem_ofFn] at hni
        split_ifs at hni with hmod
        · simp [isNotOp] at hni
        · have hj2 : j < 2 * m := by change j < C.size at hj; rw [hlen] at hj; exact hj
          refine ⟨⟨j / 2, Nat.div_lt_of_lt_mul hj2⟩, ?_⟩
          dsimp
          omega
      · rintro ⟨i, rfl⟩
        have hj : 2 * i.val + 1 < C.gates.length := by change 2 * i.val + 1 < C.size; omega
        have hgate : gateAt C (2 * i.val + 1) = gates[2 * i.val + 1] := by
          simp [gateAt, C, List.getD, List.getElem?_eq_getElem hj]
        refine ⟨hj, ?_⟩
        rw [hgate]
        simp only [gates, List.getElem_ofFn]
        have hmod : (2 * i.val + 1) % 2 ≠ 0 := by omega
        rw [if_neg hmod]
        rfl
    rw [hset, Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega)),
      Finset.card_univ, Fintype.card_fin]
    exact hr
  · intro x hcov i
    have hrb : ReadsBack (List.ofFn x ++ [false, true]).length C := by
      simpa using (show ReadsBack (n + 2) C from fun j hj u hu => by
        change j < gates.length at hj
        have hgate : gateAt C j = gates[j] := by simp [gateAt, C, List.getD, List.getElem?_eq_getElem hj]
        rw [hgate] at hu
        simp only [gates, List.getElem_ofFn] at hu
        split_ifs at hu with hmod
        · rcases List.mem_cons.mp hu with rfl | h2
          · exact Nat.lt_trans (v _).isLt (by omega)
          · simp only [List.mem_singleton] at h2; subst h2; exact Nat.lt_trans (v _).isLt (by omega)
        · simp only [List.mem_singleton] at hu; subst hu; omega)
    have hlenx : (List.ofFn x ++ [false, true]).length = n + 2 := by simp
    have hj_even : 2 * i.val < C.gates.length := by change 2 * i.val < C.size; omega
    have hj_odd : 2 * i.val + 1 < C.gates.length := by change 2 * i.val + 1 < C.size; omega
    have h_even := wires_gate_eq C (List.ofFn x ++ [false, true]) hrb hj_even
    have h_odd := wires_gate_eq C (List.ofFn x ++ [false, true]) hrb hj_odd
    rw [hlenx] at h_even h_odd
    have hgate_even : gateAt C (2 * i.val) = ⟨GateOp.and, [(v (i, false)).val, (v (i, true)).val]⟩ := by
      have hg : gateAt C (2 * i.val) = gates[2 * i.val] := by
        simp [gateAt, C, List.getD, List.getElem?_eq_getElem hj_even]
      rw [hg]; simp only [gates, List.getElem_ofFn]
      have hmod : (2 * i.val) % 2 = 0 := by omega
      rw [if_pos hmod]
      simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2), Fin.eta]
    have hgate_odd : gateAt C (2 * i.val + 1) = ⟨GateOp.not, [n + 2 + 2 * i.val]⟩ := by
      have hg : gateAt C (2 * i.val + 1) = gates[2 * i.val + 1] := by
        simp [gateAt, C, List.getD, List.getElem?_eq_getElem hj_odd]
      rw [hg]; simp only [gates, List.getElem_ofFn]
      have hmod : (2 * i.val + 1) % 2 ≠ 0 := by omega
      rw [if_neg hmod]
      have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
      simp [hdiv]
    dsimp only [tap]
    rw [h_odd, hgate_odd]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
    rw [h_even, hgate_even]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
    have hx0 : (C.wires (List.ofFn x ++ [false, true])).getD (v (i, false)).val false = x (v (i, false)) := by
      rw [wires_getD_lt C _ (by rw [hlenx]; exact Nat.lt_trans (v _).isLt (by omega))]
      exact xList_getD_fin x (v (i, false))
    have hx1 : (C.wires (List.ofFn x ++ [false, true])).getD (v (i, true)).val false = x (v (i, true)) := by
      rw [wires_getD_lt C _ (by rw [hlenx]; exact Nat.lt_trans (v _).isLt (by omega))]
      exact xList_getD_fin x (v (i, true))
    rw [hx0, hx1]
    have hpair : x (v (i, false)) = true ∨ x (v (i, true)) = true := by
      rcases hadj i with h1 | h1
      · exact hcov _ h1
      · exact (hcov _ h1).symm
    cases ha : x (v (i, false)) <;> cases hb : x (v (i, true)) <;> simp_all

end Part5_UpperBound

end PEqualNP.Outside.L_lib_1189_aux

theorem PEqualNP.Outside.L_lib_1189 :
    ∀ (n m : Nat) (G : Finset (Fin n × Fin n)) (v : (Fin m × Bool) ↪ Fin n),
      (∀ e ∈ G, e.1 < e.2) →
      let adj := fun (a b : Fin n) => (a,b) ∈ G ∨ (b,a) ∈ G
      (∀ i, adj (v (i,false)) (v (i,true))) →
      let fits := fun (s r : Nat) =>
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (n+2+C.size)),
          PEqualNP.MetaComplexity.FanInTwo C ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
          C.size ≤ s ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
          ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
            ∀ i, (C.wires (List.ofFn x ++ [false,true])).getD (tap i).val false =
              xor (x (v (i,false))) (x (v (i,true)))
      (∀ s r, fits s r → 2*m ≤ s) ∧ (∀ r, fits (2*m) r ↔ m ≤ r) := by
  intro n m G v hG adj hadj fits
  refine ⟨?_, ?_⟩
  · rintro s r ⟨C, tap, hfan, hrb, _, hs, _, hcomp⟩
    exact (PEqualNP.Outside.L_lib_1189_aux.lower_and_equality G v hG C tap hfan hrb hcomp).1.trans hs
  · intro r
    constructor
    · rintro ⟨C, tap, hfan, hrb, _, hs, hr, hcomp⟩
      exact ((PEqualNP.Outside.L_lib_1189_aux.lower_and_equality G v hG C tap hfan hrb hcomp).2 hs).trans hr
    · intro hr
      obtain ⟨C, tap, hfan, hrb, hout, hs, hnc, hcomp⟩ :=
        PEqualNP.Outside.L_lib_1189_aux.upper_construction G v hadj hr
      exact ⟨C, tap, hfan, hrb, hout, hs, hnc, hcomp⟩
