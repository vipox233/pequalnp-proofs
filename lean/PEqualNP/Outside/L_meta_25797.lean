import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25797_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

abbrev F2 := ZMod 2

def b2f (b : Bool) : F2 := if b then 1 else 0

def f2b (x : F2) : Bool := decide (x ≠ 0)

lemma b2f_false : b2f false = 0 := rfl

lemma b2f_true : b2f true = 1 := rfl

lemma b2f_injective : Function.Injective b2f := by
  intro a b h
  cases a <;> cases b <;> simp [b2f] at h ⊢

lemma b2f_xor (a b : Bool) : b2f (xor a b) = b2f a + b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_f2b (x : F2) : b2f (f2b x) = x := by
  fin_cases x <;> rfl

lemma f2_add_self (x : F2) : x + x = 0 := by
  fin_cases x <;> rfl

lemma f2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma f2_cancel_four (a b d x y : F2) :
    a + x + b + d = (x + y) + (a + y + b + d) := by
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases x <;> fin_cases y <;> rfl

lemma f2_cancel_four_mid (a b d x y : F2) :
    a + b + x + d = (x + y) + (a + b + y + d) := by
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases x <;> fin_cases y <;> rfl

lemma f2_add_cancel_left (a b c : F2) : b + c = a + (a + b + c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

lemma f2_add_cancel_right (a b c : F2) : a + b = (a + b + c) + c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

def isNL (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def gateConst (g : Gate) : F2 :=
  match g.inputs with
  | [] => b2f (g.op.eval [])
  | [_] => b2f (g.op.eval [false])
  | [_, _] => b2f (g.op.eval [false, false])
  | _ => 0

def gateDeps (g : Gate) : Finset ℕ :=
  match g.inputs with
  | [] => ∅
  | [w1] =>
    if b2f (g.op.eval [false]) = b2f (g.op.eval [true]) then ∅ else {w1}
  | [w1, w2] =>
    let f00 := b2f (g.op.eval [false, false])
    let f01 := b2f (g.op.eval [false, true])
    let f10 := b2f (g.op.eval [true, false])
    let a := f00 + f10
    let b := f00 + f01
    if a = 0 then
      if b = 0 then ∅ else {w2}
    else
      if b = 0 then {w1} else if w1 = w2 then ∅ else {w1, w2}
  | _ => ∅

lemma gateDeps_subset_inputs (g : Gate) : ∀ w ∈ gateDeps g, w ∈ g.inputs := by
  unfold gateDeps
  cases h : g.inputs with
  | nil => simp
  | cons w1 t1 =>
    cases t1 with
    | nil =>
      intro w hw
      split_ifs at hw <;> simp_all
    | cons w2 t2 =>
      cases t2 with
      | nil =>
        intro w hw
        dsimp at hw
        split_ifs at hw <;> simp_all
      | cons w3 t3 => simp

lemma gateDeps_card_le_two (g : Gate) : (gateDeps g).card ≤ 2 := by
  unfold gateDeps
  cases g.inputs with
  | nil => simp
  | cons w1 t1 =>
    cases t1 with
    | nil =>
      split_ifs <;> simp
    | cons w2 t2 =>
      cases t2 with
      | nil =>
        dsimp
        split_ifs
        · simp
        · simp
        · simp
        · simp
        · exact le_trans (Finset.card_insert_le w1 {w2}) (by simp)
      | cons w3 t3 => simp

lemma gateDeps_card_eq_two_imp (g : Gate) (h : (gateDeps g).card = 2) :
    g.inputs.length = 2 := by
  unfold gateDeps at h
  cases h1 : g.inputs with
  | nil => rw [h1] at h; simp at h
  | cons w1 t1 =>
    cases h2 : t1 with
    | nil =>
      rw [h1, h2] at h
      dsimp at h
      split_ifs at h <;> simp at h
    | cons w2 t2 =>
      cases h3 : t2 with
      | nil => rfl
      | cons w3 t3 =>
        rw [h1, h2, h3] at h
        simp at h

lemma eval_not_nl_eq_affine (g : Gate) (hlen : g.inputs.length ≤ 2) (hnl : isNL g = false)
    (valb : ℕ → Bool) :
    b2f (g.op.eval (g.inputs.map valb)) =
      gateConst g + ∑ w ∈ gateDeps g, b2f (valb w) := by
  cases h1 : g.inputs with
  | nil =>
    simp [gateConst, gateDeps, h1]
  | cons w1 t1 =>
    cases h2 : t1 with
    | nil =>
      simp only [gateConst, gateDeps, h1, h2, List.map_cons, List.map_nil]
      split_ifs with heq
      · simp only [Finset.sum_empty, add_zero]
        cases valb w1
        · rfl
        · exact heq.symm
      · simp only [Finset.sum_singleton]
        cases h0 : g.op.eval [false] <;> cases h1' : g.op.eval [true]
        · exfalso; exact heq (by rw [h0, h1'])
        · cases valb w1 <;> simp [h0, h1', b2f]
        · cases valb w1 <;> simp [h0, h1', b2f]; rfl
        · exfalso; exact heq (by rw [h0, h1'])
    | cons w2 t2 =>
      cases h3 : t2 with
      | nil =>
        simp only [isNL, h1, h2, h3, List.length_cons, List.length_nil, beq_self_eq_true,
          Bool.true_and] at hnl
        simp only [gateConst, gateDeps, h1, h2, h3, List.map_cons, List.map_nil]
        set b00 := g.op.eval [false, false] with hb00
        set b01 := g.op.eval [false, true] with hb01
        set b10 := g.op.eval [true, false] with hb10
        set b11 := g.op.eval [true, true] with hb11
        have hlin : b2f b11 = b2f b00 + b2f b01 + b2f b10 := by
          revert hnl
          cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;> decide
        have hform : ∀ x y : Bool,
            b2f (g.op.eval [x, y]) =
              b2f b00 + (b2f b00 + b2f b10) * b2f x + (b2f b00 + b2f b01) * b2f y := by
          intro x y
          cases x <;> cases y
          · simp [← hb00, b2f]
          · simp only [← hb01, b2f_false, mul_zero, add_zero, b2f_true, mul_one]
            rw [← add_assoc, f2_add_self, zero_add]
          · simp only [← hb10, b2f_false, mul_zero, add_zero, b2f_true, mul_one]
            rw [← add_assoc, f2_add_self, zero_add]
          · simp only [← hb11, b2f_true, mul_one, hlin]
            cases b00 <;> cases b01 <;> cases b10 <;> rfl
        rw [hform (valb w1) (valb w2)]
        set a := b2f b00 + b2f b10
        set b := b2f b00 + b2f b01
        rcases f2_eq_zero_or_one a with ha | ha <;> rcases f2_eq_zero_or_one b with hb | hb
        · simp [ha, hb]
        · simp [ha, hb]
        · simp [ha, hb]
        · by_cases hw : w1 = w2
          · subst hw
            simp only [ha, hb, one_ne_zero, ↓reduceIte, one_mul, Finset.sum_empty, add_zero]
            rw [add_assoc, f2_add_self, add_zero]
          · simp only [ha, hb, one_ne_zero, ↓reduceIte, one_mul, hw,
              Finset.sum_pair hw, add_assoc]
      | cons w3 t3 =>
        rw [h1, h2, h3] at hlen
        simp at hlen

lemma foldl_wires_step_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_prefix (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp; omega
    rw [ih _ hi']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_gate_eval (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ gs[j].inputs, i < acc.length + j) :
    let w := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc
    w.getD (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => w.getD i false) := by
  induction gs generalizing acc j with
  | nil => simp at hj
  | cons g gs ih =>
    dsimp only [List.foldl_cons]
    set acc1 := acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]
    have hlen1 : acc1.length = acc.length + 1 := by simp [acc1]
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero] at hrb ⊢
      have hidx : acc.length < acc1.length := by omega
      rw [foldl_wires_prefix gs acc1 acc.length hidx]
      have hacc1 : acc1.getD acc.length false =
          g.op.eval (g.inputs.map fun i => acc.getD i false) := by
        simp [acc1, List.getD_eq_getElem?_getD]
      rw [hacc1]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hil : i < acc.length := hrb i hi
      have hil1 : i < acc1.length := by omega
      rw [foldl_wires_prefix gs acc1 i hil1]
      simp [acc1, List.getD_eq_getElem?_getD, List.getElem?_append_left hil]
    | succ j' =>
      have hj' : j' < gs.length := by simp at hj; omega
      have hrb' : ∀ i ∈ gs[j'].inputs, i < acc1.length + j' := by
        intro i hi
        have := hrb i hi
        omega
      have hstep := ih acc1 j' hj' hrb'
      have heq : acc.length + (j' + 1) = acc1.length + j' := by omega
      simpa only [heq, List.getElem_cons_succ] using hstep

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_step_len C.gates x

lemma wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_wires_prefix C.gates x i hi

lemma wires_gate (C : Circuit) (x : List Bool) (j : Fin C.gates.length)
    (hrb : ReadsBack x.length C) :
    (C.wires x).getD (x.length + j.val) false =
      (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun i => (C.wires x).getD i false) := by
  have hrbj : ∀ i ∈ C.gates[j.val].inputs, i < x.length + j.val := by
    intro i hi
    have hgate : gateAt C j.val = C.gates[j.val] := by
      simp [gateAt, List.getD_eq_getElem?_getD]
    exact hrb j.val j.isLt i (by rw [hgate]; exact hi)
  simpa [Circuit.wires] using foldl_wires_gate_eval C.gates x j.val j.isLt hrbj

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

lemma oneEach_getD_left {n m : ℕ} (u : Fin n) (v : Fin m) (i : Fin n) :
    (oneEach u v).getD i.val false = decide (i = u) := by
  have hi : i.val < (List.ofFn (fun k : Fin n => decide (k = u))).length := by simp
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma oneEach_getD_right {n m : ℕ} (u : Fin n) (v : Fin m) (j : Fin m) :
    (oneEach u v).getD (n + j.val) false = decide (j = v) := by
  have hlen : (List.ofFn (fun k : Fin n => decide (k = u))).length = n := by simp
  simp [oneEach, List.getD_eq_getElem?_getD, hlen]

lemma countP_eq_card_filter_fin {α : Type*} (l : List α) (p : α → Bool) :
    l.countP p = ((Finset.univ : Finset (Fin l.length)).filter (fun j => p (l.get j) = true)).card := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons, ih]
    rw [Fin.univ_succ, Finset.cons_eq_insert, Finset.filter_insert]
    have hcard :
        ((Finset.univ.map ⟨Fin.succ, Fin.succ_injective _⟩).filter
          (fun j => p ((a :: t).get j) = true)).card =
        (Finset.univ.filter (fun j : Fin t.length => p (t.get j) = true)).card := by
      rw [Finset.filter_map]
      simp [Finset.card_map]
    have hnotmem : (0 : Fin (t.length + 1)) ∉
        (Finset.univ.map ⟨Fin.succ, Fin.succ_injective _⟩).filter
          (fun j => p ((a :: t).get j) = true) := by
      simp
    have h0 : (a :: t).get 0 = a := rfl
    cases hp : p a
    · rw [h0, hp]
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      exact hcard.symm
    · rw [h0, hp]
      simp only [↓reduceIte, Finset.card_insert_of_notMem hnotmem, hcard]

lemma nodup_of_length_le_toFinset_card {α : Type*} [DecidableEq α] (l : List α)
    (h : l.length ≤ l.toFinset.card) : l.Nodup := by
  have h1 : l.toFinset.card = l.dedup.length := List.card_toFinset l
  have h2 : l.dedup.Sublist l := List.dedup_sublist l
  have h3 : l.dedup.length = l.length := le_antisymm h2.length_le (by omega)
  have h4 : l.dedup = l := h2.eq_of_length h3
  rw [← h4]
  exact List.nodup_dedup l

lemma finset_card_le_sum_indicator {α : Type*} [DecidableEq α] (S : Finset α) (P : α → Prop)
    [DecidablePred P] :
    (S.filter P).card = ∑ a ∈ S, if P a then 1 else 0 := by
  simp [Finset.sum_boole]

abbrev wireCount (n m : ℕ) (C : Circuit) : ℕ := n + m + C.gates.length

def embL (n m : ℕ) (C : Circuit) : Fin n ↪ Fin (wireCount n m C) :=
  ⟨fun i => ⟨i.val, by unfold wireCount; omega⟩, fun a b h => by ext; simpa using congrArg Fin.val h⟩

def embR (n m : ℕ) (C : Circuit) : Fin m ↪ Fin (wireCount n m C) :=
  ⟨fun j => ⟨n + j.val, by unfold wireCount; omega⟩, fun a b h => by ext; have := congrArg Fin.val h; dsimp at this; omega⟩

def embN (n m : ℕ) (C : Circuit) : Fin C.gates.length ↪ Fin (wireCount n m C) :=
  ⟨fun k => ⟨n + m + k.val, by unfold wireCount; omega⟩, fun a b h => by ext; have := congrArg Fin.val h; dsimp at this; omega⟩

lemma embL_eq (n m : ℕ) (C : Circuit) (i : Fin n) :
    embL n m C i = ⟨i.val, by unfold wireCount; omega⟩ := rfl

lemma embR_eq (n m : ℕ) (C : Circuit) (j : Fin m) :
    embR n m C j = ⟨n + j.val, by unfold wireCount; omega⟩ := rfl

lemma embN_eq (n m : ℕ) (C : Circuit) (k : Fin C.gates.length) :
    embN n m C k = ⟨n + m + k.val, by unfold wireCount; omega⟩ := rfl

lemma output_lt_wireCount (n m : ℕ) (H : Fin n → Fin m → Bool) (C : Circuit) (hn : 2 ≤ n)
    (hrow : ∀ i j : Fin n, i ≠ j → ∀ f : Bool, ∃ y, H i y ≠ xor f (H j y))
    (hrep : Represents H C) :
    C.output < wireCount n m C := by
  by_contra hge
  push Not at hge
  have hall : ∀ u v, H u v = false := by
    intro u v
    rw [← hrep u v]
    unfold Circuit.eval
    have hlen : (C.wires (oneEach u v)).length = wireCount n m C := by
      rw [wires_length, oneEach_length]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  obtain ⟨y, hy⟩ := hrow ⟨0, by omega⟩ ⟨1, by omega⟩ (by intro h; simp at h) false
  rw [hall, hall] at hy
  exact hy rfl

def nlSet (C : Circuit) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun j => isNL (C.gates.get j) = true)

def binSet (C : Circuit) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun j => (C.gates.get j).inputs.length == 2)

def linBinSet (C : Circuit) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun j => (C.gates.get j).inputs.length == 2 && !(isNL (C.gates.get j)))

lemma nlSet_card (C : Circuit) :
    (nlSet C).card = C.gates.countP (fun g => (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true]))) := by
  rw [countP_eq_card_filter_fin]
  rfl

lemma binSet_card (C : Circuit) :
    (binSet C).card = C.gates.countP (fun g => g.inputs.length == 2) := by
  rw [countP_eq_card_filter_fin]
  rfl

lemma linBinSet_card_plus_nlSet (C : Circuit) :
    (linBinSet C).card + (nlSet C).card = (binSet C).card := by
  have hdisj : Disjoint (linBinSet C) (nlSet C) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [linBinSet, nlSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, Bool.not_eq_true'] at hj1 hj2
    rw [hj2] at hj1
    exact Bool.noConfusion hj1.2
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext j
  simp only [Finset.mem_union, linBinSet, nlSet, binSet, Finset.mem_filter, Finset.mem_univ,
    true_and, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro (⟨h1, _⟩ | h2)
    · exact h1
    · simp only [isNL, Bool.and_eq_true] at h2
      exact h2.1
  · intro h1
    cases hnl : isNL (C.gates.get j)
    · exact Or.inl ⟨h1, rfl⟩
    · exact Or.inr rfl

def isSrc (n m : ℕ) (C : Circuit) (w : Fin (wireCount n m C)) : Bool :=
  if h : w.val < n + m then true
  else isNL (C.gates.get ⟨w.val - (n + m), by
    have := w.isLt; unfold wireCount at this; omega⟩)

def srcFinset (n m : ℕ) (C : Circuit) : Finset (Fin (wireCount n m C)) :=
  Finset.univ.filter (fun w => isSrc n m C w = true)

def gateDepsFin (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (j : Fin C.gates.length) : Finset (Fin (wireCount n m C)) :=
  (gateDeps (C.gates.get j)).attach.map
    ⟨fun x => ⟨x.val, by
      have h1 : x.val ∈ (C.gates.get j).inputs := gateDeps_subset_inputs _ _ x.property
      have hgate : gateAt C j.val = C.gates.get j := by
        simp [gateAt, List.getD_eq_getElem?_getD]
      have hlt : x.val < n + m + j.val := hrb j.val j.isLt x.val (by rw [hgate]; exact h1)
      have := j.isLt; unfold wireCount; omega⟩,
     fun a b hab => by
       ext; simpa using congrArg Fin.val hab⟩

lemma gateDepsFin_lt (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (j : Fin C.gates.length) (u : Fin (wireCount n m C))
    (hu : u ∈ gateDepsFin n m C hrb j) :
    u.val < n + m + j.val := by
  simp only [gateDepsFin, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists] at hu
  rcases hu with ⟨x, hx, hux⟩
  have h1 : x ∈ (C.gates.get j).inputs := gateDeps_subset_inputs _ _ hx
  have hgate : gateAt C j.val = C.gates.get j := by
    simp [gateAt, List.getD_eq_getElem?_getD]
  have hlt : x < n + m + j.val := hrb j.val j.isLt x (by rw [hgate]; exact h1)
  have hv : x = u.val := congrArg Fin.val hux
  omega

lemma gateDepsFin_card (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (j : Fin C.gates.length) :
    (gateDepsFin n m C hrb j).card = (gateDeps (C.gates.get j)).card := by
  simp [gateDepsFin]

lemma sum_gateDepsFin_eq (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (j : Fin C.gates.length) (f : ℕ → F2) :
    ∑ u ∈ gateDepsFin n m C hrb j, f u.val = ∑ x ∈ gateDeps (C.gates.get j), f x := by
  unfold gateDepsFin
  rw [Finset.sum_map]
  simpa using Finset.sum_attach (gateDeps (C.gates.get j)) f

lemma mem_gateDepsFin_iff (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (j : Fin C.gates.length) (u : Fin (wireCount n m C)) :
    u ∈ gateDepsFin n m C hrb j ↔ u.val ∈ gateDeps (C.gates.get j) := by
  constructor
  · intro hu
    simp only [gateDepsFin, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists] at hu
    rcases hu with ⟨x, hx, hux⟩
    have hv : x = u.val := congrArg Fin.val hux
    rwa [← hv]
  · intro hu
    simp only [gateDepsFin, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists]
    exact ⟨u.val, hu, by ext; rfl⟩

def linVec (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C) :
    Fin (wireCount n m C) → Fin (wireCount n m C) → F2 :=
  fun w =>
    WellFounded.fix (InvImage.wf Fin.val Nat.lt_wfRel.wf)
      (fun v rec =>
        if hsrc : isSrc n m C v = true then
          fun s => if v = s then 1 else 0
        else
          let j : Fin C.gates.length :=
            ⟨v.val - (n + m), by
              have hge : n + m ≤ v.val := by
                by_contra hlt; push Not at hlt
                simp [isSrc, hlt] at hsrc
              have := v.isLt; unfold wireCount at this; omega⟩
          fun s => ∑ u ∈ (gateDepsFin n m C hrb j).attach,
            rec u.val (by
              have hlt := gateDepsFin_lt n m C hrb j u.val u.property
              have hge : n + m ≤ v.val := by
                by_contra hlt2; push Not at hlt2
                simp [isSrc, hlt2] at hsrc
              dsimp [j] at hlt
              change u.val.val < v.val
              omega) s)
      w

lemma linVec_src (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (v : Fin (wireCount n m C)) (hsrc : isSrc n m C v = true) :
    linVec n m C hrb v = fun s => if v = s then 1 else 0 := by
  unfold linVec
  rw [WellFounded.fix_eq]
  simp [hsrc]

lemma linVec_gate (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (j : Fin C.gates.length) (hnl : isNL (C.gates.get j) = false) (s : Fin (wireCount n m C)) :
    linVec n m C hrb ⟨n + m + j.val, by unfold wireCount; omega⟩ s =
      ∑ u ∈ gateDepsFin n m C hrb j, linVec n m C hrb u s := by
  set v : Fin (wireCount n m C) := ⟨n + m + j.val, by unfold wireCount; omega⟩
  have hnsrc : isSrc n m C v = false := by
    have hnotlt : ¬ v.val < n + m := by simp [v]
    simpa [isSrc, hnotlt, v] using hnl
  conv_lhs => unfold linVec; rw [WellFounded.fix_eq]
  simp only [hnsrc, Bool.false_eq_true, ↓reduceDIte]
  have h1 : ∀ (j' : Fin C.gates.length), j' = j →
      (∑ u ∈ (gateDepsFin n m C hrb j').attach, linVec n m C hrb u.val s) =
        ∑ u ∈ gateDepsFin n m C hrb j, linVec n m C hrb u s := by
    rintro j' rfl; exact Finset.sum_attach (gateDepsFin n m C hrb j') (fun u => linVec n m C hrb u s)
  exact h1 _ (by ext; simp [v])

def constVec (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C) :
    Fin (wireCount n m C) → F2 :=
  fun w =>
    WellFounded.fix (InvImage.wf Fin.val Nat.lt_wfRel.wf)
      (fun v rec =>
        if hsrc : isSrc n m C v = true then 0
        else
          let j : Fin C.gates.length :=
            ⟨v.val - (n + m), by
              have hge : n + m ≤ v.val := by
                by_contra hlt; push Not at hlt
                simp [isSrc, hlt] at hsrc
              have := v.isLt; unfold wireCount at this; omega⟩
          gateConst (C.gates.get j) +
            ∑ u ∈ (gateDepsFin n m C hrb j).attach,
              rec u.val (by
                have hlt := gateDepsFin_lt n m C hrb j u.val u.property
                have hge : n + m ≤ v.val := by
                  by_contra hlt2; push Not at hlt2
                  simp [isSrc, hlt2] at hsrc
                dsimp [j] at hlt
                change u.val.val < v.val
                omega))
      w

lemma constVec_src (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (v : Fin (wireCount n m C)) (hsrc : isSrc n m C v = true) :
    constVec n m C hrb v = 0 := by
  unfold constVec
  rw [WellFounded.fix_eq]
  simp [hsrc]

lemma constVec_gate (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (j : Fin C.gates.length) (hnl : isNL (C.gates.get j) = false) :
    constVec n m C hrb ⟨n + m + j.val, by unfold wireCount; omega⟩ =
      gateConst (C.gates.get j) +
        ∑ u ∈ gateDepsFin n m C hrb j, constVec n m C hrb u := by
  set v : Fin (wireCount n m C) := ⟨n + m + j.val, by unfold wireCount; omega⟩
  have hnsrc : isSrc n m C v = false := by
    have hnotlt : ¬ v.val < n + m := by simp [v]
    simpa [isSrc, hnotlt, v] using hnl
  conv_lhs => unfold constVec; rw [WellFounded.fix_eq]
  simp only [hnsrc, Bool.false_eq_true, ↓reduceDIte]
  have h1 : ∀ (j' : Fin C.gates.length), j' = j →
      gateConst (C.gates.get j') +
        (∑ u ∈ (gateDepsFin n m C hrb j').attach, constVec n m C hrb u.val) =
      gateConst (C.gates.get j) +
        ∑ u ∈ gateDepsFin n m C hrb j, constVec n m C hrb u := by
    rintro _ rfl; congr 1; exact Finset.sum_attach _ _
  exact h1 _ (by ext; simp [v])

lemma linVec_support_le (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (v s : Fin (wireCount n m C)) (hne : linVec n m C hrb v s ≠ 0) :
    s.val ≤ v.val := by
  induction hv : v.val using Nat.strong_induction_on generalizing v with
  | ind k ih =>
    by_cases hsrc : isSrc n m C v = true
    · rw [linVec_src n m C hrb v hsrc] at hne
      by_cases hvs : v = s
      · subst hvs; omega
      · simp [hvs] at hne
    · have hge : n + m ≤ v.val := by
        by_contra hlt; push Not at hlt
        exact hsrc (by simp [isSrc, hlt])
      let j : Fin C.gates.length := ⟨v.val - (n + m), by have := v.isLt; unfold wireCount at this; omega⟩
      have hnl : isNL (C.gates.get j) = false := by
        have hnotlt : ¬ v.val < n + m := by omega
        have h1 : isSrc n m C v = isNL (C.gates.get j) := by simp [isSrc, hnotlt, j]
        cases h2 : isNL (C.gates.get j)
        · rfl
        · exact False.elim (hsrc (by rw [h1, h2]))
      have hv_eq : v = ⟨n + m + j.val, by unfold wireCount; omega⟩ := by
        ext; simp [j]; omega
      rw [hv_eq, linVec_gate n m C hrb j hnl s] at hne
      obtain ⟨u, hu, hune⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hlt : u.val < n + m + j.val := gateDepsFin_lt n m C hrb j u hu
      dsimp [j] at hlt
      have hle : s.val ≤ u.val := ih u.val (by omega) u hune rfl
      omega

def wireVal (n m : ℕ) (C : Circuit) (u : Fin n) (v : Fin m)
    (w : Fin (wireCount n m C)) : F2 :=
  b2f ((C.wires (oneEach u v)).getD w.val false)

lemma wireVal_eq_linVec (n m : ℕ) (C : Circuit)
    (hfan : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (u : Fin n) (v : Fin m) (w : Fin (wireCount n m C)) :
    wireVal n m C u v w =
      constVec n m C hrb w +
        ∑ s ∈ srcFinset n m C, linVec n m C hrb w s * wireVal n m C u v s := by
  induction hw : w.val using Nat.strong_induction_on generalizing w with
  | ind k ih =>
    by_cases hsrc : isSrc n m C w = true
    · rw [constVec_src n m C hrb w hsrc, zero_add]
      have hmem : w ∈ srcFinset n m C := by simp [srcFinset, hsrc]
      rw [Finset.sum_eq_single w]
      · rw [linVec_src n m C hrb w hsrc]; simp
      · intro s _ hsne
        rw [linVec_src n m C hrb w hsrc]
        have : w ≠ s := hsne.symm
        simp [this]
      · intro hnot; exact False.elim (hnot hmem)
    · have hge : n + m ≤ w.val := by
        by_contra hlt; push Not at hlt
        exact hsrc (by simp [isSrc, hlt])
      let j : Fin C.gates.length := ⟨w.val - (n + m), by
        have := w.isLt; unfold wireCount at this; omega⟩
      have hnl : isNL (C.gates.get j) = false := by
        have hnotlt : ¬ w.val < n + m := by omega
        have h1 : isSrc n m C w = isNL (C.gates.get j) := by simp [isSrc, hnotlt, j]
        cases h2 : isNL (C.gates.get j)
        · rfl
        · exact False.elim (hsrc (by rw [h1, h2]))
      have hw_eq : w = ⟨n + m + j.val, by unfold wireCount; omega⟩ := by
        ext; simp [j]; omega
      rw [hw_eq]
      have hrb' : ReadsBack (oneEach u v).length C := by
        rw [oneEach_length]; exact hrb
      have hwg : (C.wires (oneEach u v)).getD (n + m + j.val) false =
          (C.gates.get j).op.eval
            ((C.gates.get j).inputs.map fun i => (C.wires (oneEach u v)).getD i false) := by
        have := wires_gate C (oneEach u v) j hrb'
        rwa [oneEach_length] at this
      have hlenj : (C.gates.get j).inputs.length ≤ 2 :=
        hfan (C.gates.get j) (List.get_mem C.gates j)
      have hval : wireVal n m C u v ⟨n + m + j.val, by unfold wireCount; omega⟩ =
          gateConst (C.gates.get j) +
            ∑ d ∈ gateDepsFin n m C hrb j, wireVal n m C u v d := by
        unfold wireVal
        dsimp only
        rw [hwg, eval_not_nl_eq_affine _ hlenj hnl]
        congr 1
        exact (sum_gateDepsFin_eq n m C hrb j (fun i => b2f ((C.wires (oneEach u v)).getD i false))).symm
      rw [hval, constVec_gate n m C hrb j hnl]
      have hsum_ih : ∑ d ∈ gateDepsFin n m C hrb j, wireVal n m C u v d =
          ∑ d ∈ gateDepsFin n m C hrb j,
            (constVec n m C hrb d +
              ∑ s ∈ srcFinset n m C, linVec n m C hrb d s * wireVal n m C u v s) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hlt := gateDepsFin_lt n m C hrb j d hd
        dsimp [j] at hlt
        exact ih d.val (by omega) d rfl
      rw [hsum_ih, Finset.sum_add_distrib, ← add_assoc]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [linVec_gate n m C hrb j hnl s, Finset.sum_mul]

lemma wireVal_expand (n m : ℕ) (C : Circuit)
    (hfan : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (u : Fin n) (v : Fin m) (w : Fin (wireCount n m C)) :
    wireVal n m C u v w =
      constVec n m C hrb w +
        linVec n m C hrb w ⟨u.val, by unfold wireCount; omega⟩ +
        linVec n m C hrb w ⟨n + v.val, by unfold wireCount; omega⟩ +
        ∑ k ∈ nlSet C,
          linVec n m C hrb w ⟨n + m + k.val, by unfold wireCount; omega⟩ *
            wireVal n m C u v ⟨n + m + k.val, by unfold wireCount; omega⟩ := by
  rw [wireVal_eq_linVec n m C hfan hrb u v w]
  have hpart : srcFinset n m C =
      (Finset.univ.map (embL n m C) ∪ Finset.univ.map (embR n m C)) ∪
        (nlSet C).map (embN n m C) := by
    ext s
    simp only [srcFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_map, nlSet]
    constructor
    · intro hsrc
      by_cases h1 : s.val < n
      · left; left; exact ⟨⟨s.val, h1⟩, by ext; rfl⟩
      · by_cases h2 : s.val < n + m
        · left; right; exact ⟨⟨s.val - n, by omega⟩, by ext; rw [embR_eq]; dsimp; omega⟩
        · right
          refine ⟨⟨s.val - (n + m), by have := s.isLt; unfold wireCount at this; omega⟩, ?_, ?_⟩
          · simpa [isSrc, h2] using hsrc
          · ext; rw [embN_eq]; dsimp; omega
    · rintro ((⟨i, rfl⟩ | ⟨j, rfl⟩) | ⟨k, hk, rfl⟩)
      · rw [embL_eq]; have : i.val < n + m := by omega
        simp [isSrc, this]
      · rw [embR_eq]; have : n + j.val < n + m := by omega
        simp [isSrc, this]
      · rw [embN_eq]; have : ¬ n + m + k.val < n + m := by omega
        simpa [isSrc, this] using hk
  have hd1 : Disjoint (Finset.univ.map (embL n m C)) (Finset.univ.map (embR n m C)) := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hs1 hs2
    rcases hs1 with ⟨i, rfl⟩
    rcases hs2 with ⟨j, hj⟩
    have := congrArg Fin.val hj
    rw [embL_eq, embR_eq] at this
    dsimp at this; omega
  have hd2 : Disjoint (Finset.univ.map (embL n m C) ∪ Finset.univ.map (embR n m C))
      ((nlSet C).map (embN n m C)) := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and] at hs1 hs2
    rcases hs2 with ⟨k, _, rfl⟩
    rcases hs1 with ⟨i, hi⟩ | ⟨j, hj⟩
    · have := congrArg Fin.val hi; rw [embL_eq, embN_eq] at this; dsimp at this; omega
    · have := congrArg Fin.val hj; rw [embR_eq, embN_eq] at this; dsimp at this; omega
  rw [hpart, Finset.sum_union hd2, Finset.sum_union hd1, Finset.sum_map, Finset.sum_map,
    Finset.sum_map]
  have hsumL : ∑ i : Fin n, linVec n m C hrb w (embL n m C i) * wireVal n m C u v (embL n m C i) =
      linVec n m C hrb w (embL n m C u) := by
    rw [Finset.sum_eq_single u]
    · have hwL : wireVal n m C u v (embL n m C u) = 1 := by
        unfold wireVal; rw [embL_eq]; dsimp only
        rw [wires_input C (oneEach u v) u.val (by rw [oneEach_length]; omega), oneEach_getD_left]
        simp [b2f]
      rw [hwL, mul_one]
    · intro i _ hne
      have hwL : wireVal n m C u v (embL n m C i) = 0 := by
        unfold wireVal; rw [embL_eq]; dsimp only
        rw [wires_input C (oneEach u v) i.val (by rw [oneEach_length]; omega), oneEach_getD_left]
        simp [hne, b2f]
      rw [hwL, mul_zero]
    · intro h; exact False.elim (h (Finset.mem_univ u))
  have hsumR : ∑ j : Fin m, linVec n m C hrb w (embR n m C j) * wireVal n m C u v (embR n m C j) =
      linVec n m C hrb w (embR n m C v) := by
    rw [Finset.sum_eq_single v]
    · have hwR : wireVal n m C u v (embR n m C v) = 1 := by
        unfold wireVal; rw [embR_eq]; dsimp only
        rw [wires_input C (oneEach u v) (n + v.val) (by rw [oneEach_length]; omega), oneEach_getD_right]
        simp [b2f]
      rw [hwR, mul_one]
    · intro j _ hne
      have hwR : wireVal n m C u v (embR n m C j) = 0 := by
        unfold wireVal; rw [embR_eq]; dsimp only
        rw [wires_input C (oneEach u v) (n + j.val) (by rw [oneEach_length]; omega), oneEach_getD_right]
        simp [hne, b2f]
      rw [hwR, mul_zero]
    · intro h; exact False.elim (h (Finset.mem_univ v))
  rw [hsumL, hsumR, embL_eq, embR_eq]
  have hsumN : ∑ k ∈ nlSet C, linVec n m C hrb w (embN n m C k) * wireVal n m C u v (embN n m C k) =
      ∑ k ∈ nlSet C, linVec n m C hrb w ⟨n + m + k.val, by unfold wireCount; omega⟩ *
        wireVal n m C u v ⟨n + m + k.val, by unfold wireCount; omega⟩ := by
    apply Finset.sum_congr rfl
    intro k _; rw [embN_eq]
  rw [hsumN, ← add_assoc, ← add_assoc]

def nlInput (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (k : Fin C.gates.length) (hk : k ∈ nlSet C) (b : Bool) : Fin (wireCount n m C) :=
  let g := C.gates.get k
  have hlen : g.inputs.length = 2 := by
    simp only [nlSet, Finset.mem_filter, Finset.mem_univ, true_and, isNL, Bool.and_eq_true,
      beq_iff_eq] at hk
    exact hk.1
  let idx : ℕ := if b then g.inputs[1]'(by omega) else g.inputs[0]'(by omega)
  ⟨idx, by
    have hmem : idx ∈ g.inputs := by
      dsimp only [idx]
      split_ifs <;> exact List.getElem_mem _
    have hgate : gateAt C k.val = g := by
      simp [gateAt, g, List.getD_eq_getElem?_getD]
    have hlt : idx < n + m + k.val := hrb k.val k.isLt idx (by rw [hgate]; exact hmem)
    have := k.isLt; unfold wireCount; omega⟩

lemma nlInput_lt (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (k : Fin C.gates.length) (hk : k ∈ nlSet C) (b : Bool) :
    (nlInput n m C hrb k hk b).val < n + m + k.val := by
  dsimp only [nlInput]
  set g := C.gates.get k
  have hlen : g.inputs.length = 2 := by
    simp only [nlSet, Finset.mem_filter, Finset.mem_univ, true_and, isNL, Bool.and_eq_true,
      beq_iff_eq] at hk
    exact hk.1
  have hmem : (if b then g.inputs[1]'(by omega) else g.inputs[0]'(by omega)) ∈ g.inputs := by
    split_ifs <;> exact List.getElem_mem _
  have hgate : gateAt C k.val = g := by
    simp [gateAt, g, List.getD_eq_getElem?_getD]
  exact hrb k.val k.isLt _ (by rw [hgate]; exact hmem)

lemma nl_wireVal_eq (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (k : Fin C.gates.length) (hk : k ∈ nlSet C) (u : Fin n) (v : Fin m) :
    wireVal n m C u v ⟨n + m + k.val, by unfold wireCount; omega⟩ =
      b2f ((C.gates.get k).op.eval
        [f2b (wireVal n m C u v (nlInput n m C hrb k hk false)),
         f2b (wireVal n m C u v (nlInput n m C hrb k hk true))]) := by
  have hrb' : ReadsBack (oneEach u v).length C := by rw [oneEach_length]; exact hrb
  have hwg := wires_gate C (oneEach u v) k hrb'
  rw [oneEach_length] at hwg
  unfold wireVal
  dsimp only
  rw [hwg]
  congr 2
  have hlen : (C.gates.get k).inputs.length = 2 := by
    simp only [nlSet, Finset.mem_filter, Finset.mem_univ, true_and, isNL, Bool.and_eq_true,
      beq_iff_eq] at hk
    exact hk.1
  cases h : (C.gates.get k).inputs with
  | nil => rw [h] at hlen; simp at hlen
  | cons a t1 =>
    cases h2 : t1 with
    | nil => rw [h, h2] at hlen; simp at hlen
    | cons b t2 =>
      cases h3 : t2 with
      | nil =>
        have h' : C.gates[k.val].inputs = [a, b] := by
          rw [← List.get_eq_getElem, h, h2, h3]
        have ha : (nlInput n m C hrb k hk false).val = a := by
          simp [nlInput, h']
        have hb : (nlInput n m C hrb k hk true).val = b := by
          simp [nlInput, h']
        simp only [List.map_cons, List.map_nil, ha, hb]
        have hfb : ∀ x : Bool, f2b (b2f x) = x := by intro x; cases x <;> decide
        rw [hfb, hfb]
      | cons c t3 => rw [h, h2, h3] at hlen; simp at hlen

def effStep (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (S : Finset (Fin C.gates.length)) : Finset (Fin C.gates.length) :=
  S ∪ (nlSet C).filter (fun k' =>
    ∃ k ∈ S, ∃ hk : k ∈ nlSet C,
      linVec n m C hrb (nlInput n m C hrb k hk false)
        ⟨n + m + k'.val, by unfold wireCount; omega⟩ ≠ 0 ∨
      linVec n m C hrb (nlInput n m C hrb k hk true)
        ⟨n + m + k'.val, by unfold wireCount; omega⟩ ≠ 0)

def effIter (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) : ℕ → Finset (Fin C.gates.length)
  | 0 => (nlSet C).filter (fun k =>
      linVec n m C hrb outW ⟨n + m + k.val, by unfold wireCount; omega⟩ ≠ 0)
  | r + 1 => effStep n m C hrb (effIter n m C hrb outW r)

def effSet (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) : Finset (Fin C.gates.length) :=
  effIter n m C hrb outW C.gates.length

lemma effIter_subset_nl (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (r : ℕ) :
    effIter n m C hrb outW r ⊆ nlSet C := by
  induction r with
  | zero => exact Finset.filter_subset _ _
  | succ r ih =>
    intro x hx
    simp only [effIter, effStep, Finset.mem_union, Finset.mem_filter] at hx
    rcases hx with hx | ⟨hx, _⟩
    · exact ih hx
    · exact hx

lemma effIter_mono_step (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (r : ℕ) :
    effIter n m C hrb outW r ⊆ effIter n m C hrb outW (r + 1) :=
  Finset.subset_union_left

lemma effIter_mono (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) {r1 r2 : ℕ} (h : r1 ≤ r2) :
    effIter n m C hrb outW r1 ⊆ effIter n m C hrb outW r2 := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact Finset.Subset.trans ih (effIter_mono_step n m C hrb outW _)

lemma effStep_eq_of_eq (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (r : ℕ)
    (heq : effIter n m C hrb outW (r + 1) = effIter n m C hrb outW r) (d : ℕ) :
    effIter n m C hrb outW (r + d) = effIter n m C hrb outW r := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change effStep n m C hrb (effIter n m C hrb outW (r + d)) = effIter n m C hrb outW r
    rw [ih]
    exact heq

lemma effSet_fixed (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) :
    effStep n m C hrb (effSet n m C hrb outW) = effSet n m C hrb outW := by
  by_contra hne
  have hstrict : ∀ r ≤ C.gates.length,
      (effIter n m C hrb outW r).card < (effIter n m C hrb outW (r + 1)).card := by
    intro r hr
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨effIter_mono_step n m C hrb outW r, ?_⟩
    intro heq
    apply hne
    have := effStep_eq_of_eq n m C hrb outW r heq.symm (C.gates.length - r)
    have h1 : r + (C.gates.length - r) = C.gates.length := by omega
    rw [h1] at this
    change effIter n m C hrb outW (C.gates.length + 1) = effIter n m C hrb outW C.gates.length
    have h2 := effStep_eq_of_eq n m C hrb outW r heq.symm (C.gates.length + 1 - r)
    have h3 : r + (C.gates.length + 1 - r) = C.gates.length + 1 := by omega
    rw [h3] at h2
    rw [h2, this]
  have hge : ∀ r ≤ C.gates.length + 1, r ≤ (effIter n m C hrb outW r).card := by
    intro r hr
    induction r with
    | zero => omega
    | succ r ih =>
      have h1 := ih (by omega)
      have h2 := hstrict r (by omega)
      omega
  have hbig := hge (C.gates.length + 1) le_rfl
  have hle : (effIter n m C hrb outW (C.gates.length + 1)).card ≤ C.gates.length := by
    have := Finset.card_le_univ (effIter n m C hrb outW (C.gates.length + 1))
    simpa using this
  omega

lemma effSet_closed_out (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (k : Fin C.gates.length) (hk : k ∈ nlSet C)
    (hne : linVec n m C hrb outW ⟨n + m + k.val, by unfold wireCount; omega⟩ ≠ 0) :
    k ∈ effSet n m C hrb outW := by
  apply effIter_mono n m C hrb outW (Nat.zero_le C.gates.length)
  simp [effIter, hk, hne]

lemma effSet_closed_input (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (k : Fin C.gates.length)
    (hk : k ∈ effSet n m C hrb outW) (b : Bool)
    (k' : Fin C.gates.length) (hk' : k' ∈ nlSet C)
    (hne : linVec n m C hrb (nlInput n m C hrb k (effIter_subset_nl n m C hrb outW _ hk) b)
      ⟨n + m + k'.val, by unfold wireCount; omega⟩ ≠ 0) :
    k' ∈ effSet n m C hrb outW := by
  rw [← effSet_fixed n m C hrb outW]
  simp only [effStep, Finset.mem_union, Finset.mem_filter]
  right
  refine ⟨hk', k, hk, effIter_subset_nl n m C hrb outW _ hk, ?_⟩
  cases b
  · exact Or.inl hne
  · exact Or.inr hne

lemma effIter_witness (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (r : ℕ) (k' : Fin C.gates.length)
    (hk' : k' ∈ effIter n m C hrb outW r) :
    linVec n m C hrb outW ⟨n + m + k'.val, by unfold wireCount; omega⟩ ≠ 0 ∨
      ∃ k, ∃ hk : k ∈ effIter n m C hrb outW r, ∃ b : Bool,
        linVec n m C hrb (nlInput n m C hrb k (effIter_subset_nl n m C hrb outW r hk) b)
          ⟨n + m + k'.val, by unfold wireCount; omega⟩ ≠ 0 := by
  induction r with
  | zero =>
    left
    simp only [effIter, Finset.mem_filter] at hk'
    exact hk'.2
  | succ r ih =>
    simp only [effIter, effStep, Finset.mem_union, Finset.mem_filter] at hk'
    rcases hk' with hk' | ⟨_, k, hk, hk_nl, hne⟩
    · rcases ih hk' with h1 | ⟨k, hk, b, hne⟩
      · exact Or.inl h1
      · exact Or.inr ⟨k, effIter_mono_step n m C hrb outW r hk, b, hne⟩
    · right
      rcases hne with h0 | h1
      · exact ⟨k, effIter_mono_step n m C hrb outW r hk, false, h0⟩
      · exact ⟨k, effIter_mono_step n m C hrb outW r hk, true, h1⟩

abbrev EffElem (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) :=
  {k : Fin C.gates.length // k ∈ effSet n m C hrb outW}

abbrev QueryIdx (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) :=
  (EffElem n m C hrb outW × Bool) ⊕ Unit

def queryTgt (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) :
    QueryIdx n m C hrb outW → Fin (wireCount n m C)
  | Sum.inl ⟨k, b⟩ => nlInput n m C hrb k.val (effIter_subset_nl n m C hrb outW _ k.property) b
  | Sum.inr () => outW

def pLeft (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (u : Fin n) :
    EffElem n m C hrb outW × Bool → F2 :=
  fun p => linVec n m C hrb (queryTgt n m C hrb outW (Sum.inl p))
    ⟨u.val, by unfold wireCount; omega⟩

def pRight (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (v : Fin m) :
    EffElem n m C hrb outW × Bool → F2 :=
  fun p => linVec n m C hrb (queryTgt n m C hrb outW (Sum.inl p))
    ⟨n + v.val, by unfold wireCount; omega⟩

lemma eff_wireVal_eq_of_sum_eq (n m : ℕ) (C : Circuit)
    (hfan : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C) (outW : Fin (wireCount n m C))
    (u1 u2 : Fin n) (v1 v2 : Fin m)
    (hsum : pLeft n m C hrb outW u1 + pRight n m C hrb outW v1 =
            pLeft n m C hrb outW u2 + pRight n m C hrb outW v2)
    (k : Fin C.gates.length) (hk : k ∈ effSet n m C hrb outW) :
    wireVal n m C u1 v1 ⟨n + m + k.val, by unfold wireCount; omega⟩ =
      wireVal n m C u2 v2 ⟨n + m + k.val, by unfold wireCount; omega⟩ := by
  have hmain : ∀ mval (k : Fin C.gates.length), k.val = mval → k ∈ effSet n m C hrb outW →
      wireVal n m C u1 v1 ⟨n + m + k.val, by unfold wireCount; omega⟩ =
        wireVal n m C u2 v2 ⟨n + m + k.val, by unfold wireCount; omega⟩ := by
    intro mval
    induction mval using Nat.strong_induction_on with
    | ind mval ih =>
      intro k hkval hk
      have hknl : k ∈ nlSet C := effIter_subset_nl n m C hrb outW _ hk
      rw [nl_wireVal_eq n m C hrb k hknl u1 v1, nl_wireVal_eq n m C hrb k hknl u2 v2]
      have hinput : ∀ b : Bool,
          wireVal n m C u1 v1 (nlInput n m C hrb k hknl b) =
            wireVal n m C u2 v2 (nlInput n m C hrb k hknl b) := by
        intro b
        set w := nlInput n m C hrb k hknl b
        rw [wireVal_expand n m C hfan hrb u1 v1 w, wireVal_expand n m C hfan hrb u2 v2 w]
        have hmid :
            linVec n m C hrb w ⟨u1.val, by unfold wireCount; omega⟩ +
              linVec n m C hrb w ⟨n + v1.val, by unfold wireCount; omega⟩ =
            linVec n m C hrb w ⟨u2.val, by unfold wireCount; omega⟩ +
              linVec n m C hrb w ⟨n + v2.val, by unfold wireCount; omega⟩ := by
          have h1 := congrFun hsum (⟨k, hk⟩, b)
          simpa [pLeft, pRight, queryTgt, w] using h1
        have hsum_nl :
            ∑ k' ∈ nlSet C,
              linVec n m C hrb w ⟨n + m + k'.val, by unfold wireCount; omega⟩ *
                wireVal n m C u1 v1 ⟨n + m + k'.val, by unfold wireCount; omega⟩ =
            ∑ k' ∈ nlSet C,
              linVec n m C hrb w ⟨n + m + k'.val, by unfold wireCount; omega⟩ *
                wireVal n m C u2 v2 ⟨n + m + k'.val, by unfold wireCount; omega⟩ := by
          apply Finset.sum_congr rfl
          intro k' hk'
          by_cases hcoeff : linVec n m C hrb w ⟨n + m + k'.val, by unfold wireCount; omega⟩ = 0
          · simp [hcoeff]
          · have hk'eff : k' ∈ effSet n m C hrb outW :=
              effSet_closed_input n m C hrb outW k hk b k' hk' hcoeff
            have hle : n + m + k'.val ≤ w.val :=
              linVec_support_le n m C hrb w ⟨n + m + k'.val, by unfold wireCount; omega⟩ hcoeff
            have hlt : w.val < n + m + k.val := nlInput_lt n m C hrb k hknl b
            have hval_eq := ih k'.val (by omega) k' rfl hk'eff
            rw [hval_eq]
        rw [add_assoc (constVec n m C hrb w) (linVec n m C hrb w ⟨u1.val, by unfold wireCount; omega⟩)]
        rw [add_assoc (constVec n m C hrb w) (linVec n m C hrb w ⟨u2.val, by unfold wireCount; omega⟩)]
        rw [hmid, hsum_nl]
      rw [hinput false, hinput true]
  exact hmain k.val k rfl hk

lemma pLeft_injective (n m : ℕ) (H : Fin n → Fin m → Bool) (C : Circuit)
    (hrow : ∀ i j : Fin n, i ≠ j → ∀ f : Bool, ∃ y, H i y ≠ xor f (H j y))
    (hfan : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C) (hrep : Represents H C)
    (hout : C.output < wireCount n m C) :
    Function.Injective (pLeft n m C hrb ⟨C.output, hout⟩) := by
  intro u1 u2 heq
  by_contra hne
  set outW : Fin (wireCount n m C) := ⟨C.output, hout⟩
  set cdiff : F2 :=
    linVec n m C hrb outW ⟨u1.val, by unfold wireCount; omega⟩ +
      linVec n m C hrb outW ⟨u2.val, by unfold wireCount; omega⟩
  obtain ⟨v, hv⟩ := hrow u1 u2 hne (f2b cdiff)
  have hsum : pLeft n m C hrb outW u1 + pRight n m C hrb outW v =
              pLeft n m C hrb outW u2 + pRight n m C hrb outW v := by
    rw [heq]
  have h1 : b2f (H u1 v) = wireVal n m C u1 v outW := by
    rw [← hrep u1 v]; rfl
  have h2 : b2f (H u2 v) = wireVal n m C u2 v outW := by
    rw [← hrep u2 v]; rfl
  have hsum_nl :
      ∑ k ∈ nlSet C,
        linVec n m C hrb outW ⟨n + m + k.val, by unfold wireCount; omega⟩ *
          wireVal n m C u1 v ⟨n + m + k.val, by unfold wireCount; omega⟩ =
      ∑ k ∈ nlSet C,
        linVec n m C hrb outW ⟨n + m + k.val, by unfold wireCount; omega⟩ *
          wireVal n m C u2 v ⟨n + m + k.val, by unfold wireCount; omega⟩ := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hc : linVec n m C hrb outW ⟨n + m + k.val, by unfold wireCount; omega⟩ = 0
    · simp [hc]
    · have hkeff : k ∈ effSet n m C hrb outW := effSet_closed_out n m C hrb outW k hk hc
      rw [eff_wireVal_eq_of_sum_eq n m C hfan hrb outW u1 u2 v v hsum k hkeff]
  have hxor_eq : b2f (H u1 v) = b2f (xor (f2b cdiff) (H u2 v)) := by
    rw [b2f_xor, b2f_f2b, h1, h2, wireVal_expand n m C hfan hrb u1 v outW,
      wireVal_expand n m C hfan hrb u2 v outW, hsum_nl]
    set A := constVec n m C hrb outW
    set B := linVec n m C hrb outW ⟨n + v.val, by unfold wireCount; omega⟩
    set D := ∑ k ∈ nlSet C,
      linVec n m C hrb outW ⟨n + m + k.val, by unfold wireCount; omega⟩ *
        wireVal n m C u2 v ⟨n + m + k.val, by unfold wireCount; omega⟩
    set L1 := linVec n m C hrb outW ⟨u1.val, by unfold wireCount; omega⟩
    set L2 := linVec n m C hrb outW ⟨u2.val, by unfold wireCount; omega⟩
    change A + L1 + B + D = (L1 + L2) + (A + L2 + B + D)
    exact f2_cancel_four A B D L1 L2
  exact hv (b2f_injective hxor_eq)

lemma pRight_injective (n m : ℕ) (H : Fin n → Fin m → Bool) (C : Circuit)
    (hcol : ∀ i j : Fin m, i ≠ j → ∀ f : Bool, ∃ x, H x i ≠ xor f (H x j))
    (hfan : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C) (hrep : Represents H C)
    (hout : C.output < wireCount n m C) :
    Function.Injective (pRight n m C hrb ⟨C.output, hout⟩) := by
  intro v1 v2 heq
  by_contra hne
  set outW : Fin (wireCount n m C) := ⟨C.output, hout⟩
  set cdiff : F2 :=
    linVec n m C hrb outW ⟨n + v1.val, by unfold wireCount; omega⟩ +
      linVec n m C hrb outW ⟨n + v2.val, by unfold wireCount; omega⟩
  obtain ⟨u, hu⟩ := hcol v1 v2 hne (f2b cdiff)
  have hsum : pLeft n m C hrb outW u + pRight n m C hrb outW v1 =
              pLeft n m C hrb outW u + pRight n m C hrb outW v2 := by
    rw [heq]
  have h1 : b2f (H u v1) = wireVal n m C u v1 outW := by
    rw [← hrep u v1]; rfl
  have h2 : b2f (H u v2) = wireVal n m C u v2 outW := by
    rw [← hrep u v2]; rfl
  have hsum_nl :
      ∑ k ∈ nlSet C,
        linVec n m C hrb outW ⟨n + m + k.val, by unfold wireCount; omega⟩ *
          wireVal n m C u v1 ⟨n + m + k.val, by unfold wireCount; omega⟩ =
      ∑ k ∈ nlSet C,
        linVec n m C hrb outW ⟨n + m + k.val, by unfold wireCount; omega⟩ *
          wireVal n m C u v2 ⟨n + m + k.val, by unfold wireCount; omega⟩ := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hc : linVec n m C hrb outW ⟨n + m + k.val, by unfold wireCount; omega⟩ = 0
    · simp [hc]
    · have hkeff : k ∈ effSet n m C hrb outW := effSet_closed_out n m C hrb outW k hk hc
      rw [eff_wireVal_eq_of_sum_eq n m C hfan hrb outW u u v1 v2 hsum k hkeff]
  have hxor_eq : b2f (H u v1) = b2f (xor (f2b cdiff) (H u v2)) := by
    rw [b2f_xor, b2f_f2b, h1, h2, wireVal_expand n m C hfan hrb u v1 outW,
      wireVal_expand n m C hfan hrb u v2 outW, hsum_nl]
    set A := constVec n m C hrb outW
    set B := linVec n m C hrb outW ⟨u.val, by unfold wireCount; omega⟩
    set D := ∑ k ∈ nlSet C,
      linVec n m C hrb outW ⟨n + m + k.val, by unfold wireCount; omega⟩ *
        wireVal n m C u v2 ⟨n + m + k.val, by unfold wireCount; omega⟩
    set R1 := linVec n m C hrb outW ⟨n + v1.val, by unfold wireCount; omega⟩
    set R2 := linVec n m C hrb outW ⟨n + v2.val, by unfold wireCount; omega⟩
    change A + B + R1 + D = (R1 + R2) + (A + B + R2 + D)
    exact f2_cancel_four_mid A B D R1 R2
  exact hu (b2f_injective hxor_eq)

lemma card_eff_fun (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) :
    Fintype.card (EffElem n m C hrb outW × Bool → F2) = 4 ^ (effSet n m C hrb outW).card := by
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, ZMod.card]
  rw [mul_comm, pow_mul]
  rfl

def fwdCoeff (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (w : Fin (wireCount n m C)) : Fin (wireCount n m C) → F2 :=
  WellFounded.fix (InvImage.wf Fin.val Nat.lt_wfRel.wf)
    (fun v rec =>
      if v = w then 1
      else if hsrc : isSrc n m C v = true then 0
      else
        let j : Fin C.gates.length :=
          ⟨v.val - (n + m), by
            have hge : n + m ≤ v.val := by
              by_contra hlt; push Not at hlt
              simp [isSrc, hlt] at hsrc
            have := v.isLt; unfold wireCount at this; omega⟩
        ∑ u ∈ (gateDepsFin n m C hrb j).attach,
          rec u.val (by
            have hlt := gateDepsFin_lt n m C hrb j u.val u.property
            have hge : n + m ≤ v.val := by
              by_contra hlt2; push Not at hlt2
              simp [isSrc, hlt2] at hsrc
            dsimp [j] at hlt
            change u.val.val < v.val
            omega))

lemma fwdCoeff_self (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (w : Fin (wireCount n m C)) :
    fwdCoeff n m C hrb w w = 1 := by
  unfold fwdCoeff; rw [WellFounded.fix_eq]; simp

lemma fwdCoeff_src_ne (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (w v : Fin (wireCount n m C)) (hne : v ≠ w) (hsrc : isSrc n m C v = true) :
    fwdCoeff n m C hrb w v = 0 := by
  unfold fwdCoeff; rw [WellFounded.fix_eq]; simp [hne, hsrc]

lemma fwdCoeff_gate_ne (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (w : Fin (wireCount n m C)) (j : Fin C.gates.length)
    (hnl : isNL (C.gates.get j) = false)
    (hne : (⟨n + m + j.val, by unfold wireCount; omega⟩ : Fin (wireCount n m C)) ≠ w) :
    fwdCoeff n m C hrb w ⟨n + m + j.val, by unfold wireCount; omega⟩ =
      ∑ u ∈ gateDepsFin n m C hrb j, fwdCoeff n m C hrb w u := by
  set v : Fin (wireCount n m C) := ⟨n + m + j.val, by unfold wireCount; omega⟩
  have hnsrc : isSrc n m C v = false := by
    have hnotlt : ¬ v.val < n + m := by simp [v]
    simpa [isSrc, hnotlt, v] using hnl
  conv_lhs => unfold fwdCoeff; rw [WellFounded.fix_eq]
  simp only [hne, ↓reduceIte, hnsrc, Bool.false_eq_true, ↓reduceDIte]
  have h1 : ∀ (j' : Fin C.gates.length), j' = j →
      (∑ u ∈ (gateDepsFin n m C hrb j').attach, fwdCoeff n m C hrb w u.val) =
        ∑ u ∈ gateDepsFin n m C hrb j, fwdCoeff n m C hrb w u := by
    rintro j' rfl; exact Finset.sum_attach (gateDepsFin n m C hrb j') (fun u => fwdCoeff n m C hrb w u)
  exact h1 _ (by ext; simp [v])

lemma fwdCoeff_eq_zero_of_lt (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (w v : Fin (wireCount n m C)) (hlt : v.val < w.val) :
    fwdCoeff n m C hrb w v = 0 := by
  induction hv : v.val using Nat.strong_induction_on generalizing v with
  | ind k ih =>
    have hne : v ≠ w := by intro h; subst h; omega
    by_cases hsrc : isSrc n m C v = true
    · exact fwdCoeff_src_ne n m C hrb w v hne hsrc
    · have hge : n + m ≤ v.val := by
        by_contra h1; push Not at h1
        exact hsrc (by simp [isSrc, h1])
      let j : Fin C.gates.length := ⟨v.val - (n + m), by have := v.isLt; unfold wireCount at this; omega⟩
      have hnl : isNL (C.gates.get j) = false := by
        have hnotlt : ¬ v.val < n + m := by omega
        have h1 : isSrc n m C v = isNL (C.gates.get j) := by simp [isSrc, hnotlt, j]
        cases h2 : isNL (C.gates.get j)
        · rfl
        · exact False.elim (hsrc (by rw [h1, h2]))
      have hv_eq : v = ⟨n + m + j.val, by unfold wireCount; omega⟩ := by
        ext; simp [j]; omega
      rw [hv_eq, fwdCoeff_gate_ne n m C hrb w j hnl (by rwa [← hv_eq])]
      apply Finset.sum_eq_zero
      intro u hu
      have hult := gateDepsFin_lt n m C hrb j u hu
      dsimp [j] at hult
      exact ih u.val (by omega) u (by omega) rfl

lemma fwdCoeff_eq_linVec (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (w : Fin (wireCount n m C)) (hw : isSrc n m C w = true) (v : Fin (wireCount n m C)) :
    fwdCoeff n m C hrb w v = linVec n m C hrb v w := by
  induction hv : v.val using Nat.strong_induction_on generalizing v with
  | ind k ih =>
    by_cases hsrc : isSrc n m C v = true
    · rw [linVec_src n m C hrb v hsrc]
      by_cases hvw : v = w
      · subst hvw; simp [fwdCoeff_self]
      · simp [hvw, fwdCoeff_src_ne n m C hrb w v hvw hsrc]
    · have hvw : v ≠ w := by intro h; subst h; exact hsrc hw
      have hge : n + m ≤ v.val := by
        by_contra h1; push Not at h1
        exact hsrc (by simp [isSrc, h1])
      let j : Fin C.gates.length := ⟨v.val - (n + m), by have := v.isLt; unfold wireCount at this; omega⟩
      have hnl : isNL (C.gates.get j) = false := by
        have hnotlt : ¬ v.val < n + m := by omega
        have h1 : isSrc n m C v = isNL (C.gates.get j) := by simp [isSrc, hnotlt, j]
        cases h2 : isNL (C.gates.get j)
        · rfl
        · exact False.elim (hsrc (by rw [h1, h2]))
      have hv_eq : v = ⟨n + m + j.val, by unfold wireCount; omega⟩ := by
        ext; simp [j]; omega
      rw [hv_eq, fwdCoeff_gate_ne n m C hrb w j hnl (by rwa [← hv_eq]),
        linVec_gate n m C hrb j hnl w]
      apply Finset.sum_congr rfl
      intro u hu
      have hult := gateDepsFin_lt n m C hrb j u hu
      dsimp [j] at hult
      exact ih u.val (by omega) u rfl

def nonNLReaders (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (w : Fin (wireCount n m C)) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun j => isNL (C.gates.get j) = false ∧ w ∈ gateDepsFin n m C hrb j)

lemma fwdCoeff_dual_rec (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (w v : Fin (wireCount n m C)) :
    fwdCoeff n m C hrb w v =
      (if v = w then 1 else 0) +
        ∑ j ∈ nonNLReaders n m C hrb w,
          fwdCoeff n m C hrb ⟨n + m + j.val, by unfold wireCount; omega⟩ v := by
  induction hv : v.val using Nat.strong_induction_on generalizing v with
  | ind k ih =>
    by_cases hvw : v.val ≤ w.val
    · have hsum0 :
          ∑ j ∈ nonNLReaders n m C hrb w,
            fwdCoeff n m C hrb ⟨n + m + j.val, by unfold wireCount; omega⟩ v = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp only [nonNLReaders, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hlt := gateDepsFin_lt n m C hrb j w hj.2
        exact fwdCoeff_eq_zero_of_lt n m C hrb _ v (by dsimp; omega)
      rw [hsum0, add_zero]
      by_cases heq : v = w
      · subst heq; simp [fwdCoeff_self]
      · have hlt : v.val < w.val := by
          have : v.val ≠ w.val := fun h => heq (Fin.ext h)
          omega
        simp [heq, fwdCoeff_eq_zero_of_lt n m C hrb w v hlt]
    · push Not at hvw
      have hne : v ≠ w := by intro h; subst h; omega
      simp only [hne, ↓reduceIte, zero_add]
      by_cases hsrc : isSrc n m C v = true
      · rw [fwdCoeff_src_ne n m C hrb w v hne hsrc]
        symm
        apply Finset.sum_eq_zero
        intro j hj
        simp only [nonNLReaders, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hvne : v ≠ ⟨n + m + j.val, by unfold wireCount; omega⟩ := by
          intro heq
          have hsrc_v : isSrc n m C v = isNL (C.gates.get j) := by
            rw [heq]; simp [isSrc]
          rw [hsrc_v, hj.1] at hsrc
          exact Bool.noConfusion hsrc
        exact fwdCoeff_src_ne n m C hrb _ v hvne hsrc
      · have hge : n + m ≤ v.val := by
          by_contra h1; push Not at h1
          exact hsrc (by simp [isSrc, h1])
        let k0 : Fin C.gates.length := ⟨v.val - (n + m), by have := v.isLt; unfold wireCount at this; omega⟩
        have hnl0 : isNL (C.gates.get k0) = false := by
          have hnotlt : ¬ v.val < n + m := by omega
          have h1 : isSrc n m C v = isNL (C.gates.get k0) := by simp [isSrc, hnotlt, k0]
          cases h2 : isNL (C.gates.get k0)
          · rfl
          · exact False.elim (hsrc (by rw [h1, h2]))
        have hv_eq : v = ⟨n + m + k0.val, by unfold wireCount; omega⟩ := by
          ext; simp [k0]; omega
        rw [hv_eq, fwdCoeff_gate_ne n m C hrb w k0 hnl0 (by rwa [← hv_eq])]
        have hstep :
            ∑ u ∈ gateDepsFin n m C hrb k0, fwdCoeff n m C hrb w u =
              (∑ u ∈ gateDepsFin n m C hrb k0, if u = w then (1 : F2) else 0) +
                ∑ j ∈ nonNLReaders n m C hrb w,
                  ∑ u ∈ gateDepsFin n m C hrb k0,
                    fwdCoeff n m C hrb ⟨n + m + j.val, by unfold wireCount; omega⟩ u := by
          rw [← Finset.sum_comm, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro u hu
          have hult := gateDepsFin_lt n m C hrb k0 u hu
          dsimp [k0] at hult
          exact ih u.val (by omega) u rfl
        rw [hstep]
        have hfirst :
            (∑ u ∈ gateDepsFin n m C hrb k0, if u = w then (1 : F2) else 0) =
              if k0 ∈ nonNLReaders n m C hrb w then 1 else 0 := by
          by_cases hw_mem : w ∈ gateDepsFin n m C hrb k0
          · have hk0_mem : k0 ∈ nonNLReaders n m C hrb w := by
              simp only [nonNLReaders, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hnl0, hw_mem⟩
            simp only [hk0_mem, ↓reduceIte]
            rw [Finset.sum_eq_single w]
            · simp
            · intro u _ hune; simp [hune]
            · intro hnot; exact False.elim (hnot hw_mem)
          · have hk0_not : k0 ∉ nonNLReaders n m C hrb w := by
              simp [nonNLReaders, hw_mem]
            simp only [hk0_not, ↓reduceIte]
            apply Finset.sum_eq_zero
            intro u hu
            have : u ≠ w := fun h => hw_mem (h ▸ hu)
            simp [this]
        rw [hfirst]
        by_cases hk0_mem : k0 ∈ nonNLReaders n m C hrb w
        · simp only [hk0_mem, ↓reduceIte]
          rw [← Finset.add_sum_erase _ _ hk0_mem]
          symm
          rw [← Finset.add_sum_erase _ _ hk0_mem]
          have hself_lhs :
              ∑ u ∈ gateDepsFin n m C hrb k0,
                fwdCoeff n m C hrb ⟨n + m + k0.val, by unfold wireCount; omega⟩ u = 0 := by
            apply Finset.sum_eq_zero
            intro u hu
            exact fwdCoeff_eq_zero_of_lt n m C hrb _ u (by dsimp; exact gateDepsFin_lt n m C hrb k0 u hu)
          rw [hself_lhs, zero_add, fwdCoeff_self]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          have hjne : j ≠ k0 := (Finset.mem_erase.mp hj).1
          have hne_j : (⟨n + m + k0.val, by unfold wireCount; omega⟩ : Fin (wireCount n m C)) ≠
              ⟨n + m + j.val, by unfold wireCount; omega⟩ := by
            intro h; apply hjne; ext; have := congrArg Fin.val h; dsimp at this; omega
          exact fwdCoeff_gate_ne n m C hrb _ k0 hnl0 hne_j
        · simp only [hk0_mem, ↓reduceIte, zero_add]
          apply Finset.sum_congr rfl
          intro j hj
          have hjne : j ≠ k0 := fun h => hk0_mem (h ▸ hj)
          have hne_j : (⟨n + m + k0.val, by unfold wireCount; omega⟩ : Fin (wireCount n m C)) ≠
              ⟨n + m + j.val, by unfold wireCount; omega⟩ := by
            intro h; apply hjne; ext; have := congrArg Fin.val h; dsimp at this; omega
          exact (fwdCoeff_gate_ne n m C hrb _ k0 hnl0 hne_j).symm

def dualVec (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (w : Fin (wireCount n m C)) :
    QueryIdx n m C hrb outW → F2 :=
  fun q => fwdCoeff n m C hrb w (queryTgt n m C hrb outW q)

def basisQ (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (q : QueryIdx n m C hrb outW) :
    QueryIdx n m C hrb outW → F2 :=
  fun q' => if q' = q then 1 else 0

lemma dualVec_src (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (w : Fin (wireCount n m C)) (hw : isSrc n m C w = true)
    (q : QueryIdx n m C hrb outW) :
    dualVec n m C hrb outW w q = linVec n m C hrb (queryTgt n m C hrb outW q) w :=
  fwdCoeff_eq_linVec n m C hrb w hw (queryTgt n m C hrb outW q)

def srcAct (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) : Finset (Fin (wireCount n m C)) :=
  (srcFinset n m C).filter (fun w => dualVec n m C hrb outW w ≠ 0)

def gateAct (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun j =>
    isNL (C.gates.get j) = false ∧
      dualVec n m C hrb outW ⟨n + m + j.val, by unfold wireCount; omega⟩ ≠ 0)

def gateAct2 (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) : Finset (Fin C.gates.length) :=
  (gateAct n m C hrb outW).filter (fun j => (gateDeps (C.gates.get j)).card = 2)

def gateAct1 (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) : Finset (Fin C.gates.length) :=
  (gateAct n m C hrb outW).filter (fun j => (gateDeps (C.gates.get j)).card ≤ 1)

def allAct (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) : Finset (Fin (wireCount n m C)) :=
  srcAct n m C hrb outW ∪ (gateAct n m C hrb outW).map (embN n m C)

lemma allAct_card (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) :
    (allAct n m C hrb outW).card =
      (srcAct n m C hrb outW).card + (gateAct2 n m C hrb outW).card +
        (gateAct1 n m C hrb outW).card := by
  have hdisj : Disjoint (srcAct n m C hrb outW) ((gateAct n m C hrb outW).map (embN n m C)) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [srcAct, srcFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hw1
    simp only [Finset.mem_map, gateAct, Finset.mem_filter, Finset.mem_univ, true_and] at hw2
    rcases hw2 with ⟨j, ⟨hnl, _⟩, rfl⟩
    rw [embN_eq] at hw1
    have hnotlt : ¬ (n + m + j.val) < n + m := by omega
    have hsrc : isSrc n m C ⟨n + m + j.val, by unfold wireCount; omega⟩ = isNL (C.gates.get j) := by
      simp [isSrc, hnotlt]
    rw [hsrc, hnl] at hw1
    exact Bool.noConfusion hw1.1
  have hpart : gateAct n m C hrb outW = gateAct2 n m C hrb outW ∪ gateAct1 n m C hrb outW := by
    ext j
    simp only [gateAct2, gateAct1, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hj
      have hle := gateDeps_card_le_two (C.gates.get j)
      by_cases h2 : (gateDeps (C.gates.get j)).card = 2
      · exact Or.inl ⟨hj, h2⟩
      · exact Or.inr ⟨hj, by omega⟩
    · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
  have hdisj2 : Disjoint (gateAct2 n m C hrb outW) (gateAct1 n m C hrb outW) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [gateAct2, gateAct1, Finset.mem_filter] at hj1 hj2
    omega
  rw [allAct, Finset.card_union_of_disjoint hdisj, Finset.card_map, hpart,
    Finset.card_union_of_disjoint hdisj2, add_assoc]

lemma gateAct2_subset_linBin (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) :
    gateAct2 n m C hrb outW ⊆ linBinSet C := by
  intro j hj
  simp only [gateAct2, gateAct, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have hlen := gateDeps_card_eq_two_imp (C.gates.get j) hj.2
  simp only [linBinSet, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true']
  exact ⟨hlen, hj.1.1⟩

def incQ (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (w : Fin (wireCount n m C)) :
    Finset (QueryIdx n m C hrb outW) :=
  Finset.univ.filter (fun q => queryTgt n m C hrb outW q = w)

def incG (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (w : Fin (wireCount n m C)) :
    Finset (Fin C.gates.length) :=
  (gateAct n m C hrb outW).filter (fun j => w ∈ gateDepsFin n m C hrb j)

def incSet (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (w : Fin (wireCount n m C)) :
    Finset (QueryIdx n m C hrb outW ⊕ Fin C.gates.length) :=
  (incQ n m C hrb outW w).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (incG n m C hrb outW w).map ⟨Sum.inr, Sum.inr_injective⟩

def incTerm (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) :
    QueryIdx n m C hrb outW ⊕ Fin C.gates.length → (QueryIdx n m C hrb outW → F2)
  | Sum.inl q => basisQ n m C hrb outW q
  | Sum.inr j => dualVec n m C hrb outW ⟨n + m + j.val, by unfold wireCount; omega⟩

lemma incSet_card (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (w : Fin (wireCount n m C)) :
    (incSet n m C hrb outW w).card =
      (incQ n m C hrb outW w).card + (incG n m C hrb outW w).card := by
  have hdisj : Disjoint ((incQ n m C hrb outW w).map ⟨Sum.inl, Sum.inl_injective⟩)
      ((incG n m C hrb outW w).map ⟨Sum.inr, Sum.inr_injective⟩) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx1 hx2
    rcases hx1 with ⟨a, _, rfl⟩
    rcases hx2 with ⟨b, _, hb⟩
    cases hb
  rw [incSet, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]

lemma dualVec_eq_sum_incSet (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (w : Fin (wireCount n m C)) :
    dualVec n m C hrb outW w = ∑ e ∈ incSet n m C hrb outW w, incTerm n m C hrb outW e := by
  have hdisj : Disjoint ((incQ n m C hrb outW w).map ⟨Sum.inl, Sum.inl_injective⟩)
      ((incG n m C hrb outW w).map ⟨Sum.inr, Sum.inr_injective⟩) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx1 hx2
    rcases hx1 with ⟨a, _, rfl⟩
    rcases hx2 with ⟨b, _, hb⟩
    cases hb
  ext q
  rw [incSet, Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map]
  simp only [Finset.sum_apply, Pi.add_apply, Function.Embedding.coeFn_mk, incTerm]
  unfold dualVec
  rw [fwdCoeff_dual_rec n m C hrb w (queryTgt n m C hrb outW q)]
  congr 1
  · by_cases hq : queryTgt n m C hrb outW q = w
    · simp only [hq, ↓reduceIte]
      have hmem : q ∈ incQ n m C hrb outW w := by simp [incQ, hq]
      rw [Finset.sum_eq_single q]
      · simp [basisQ]
      · intro q' _ hne; simp [basisQ, hne.symm]
      · intro hnot; exact False.elim (hnot hmem)
    · simp only [hq, ↓reduceIte]
      symm
      apply Finset.sum_eq_zero
      intro q' hq'
      have hne : q ≠ q' := by
        intro heq; subst heq
        simp only [incQ, Finset.mem_filter, Finset.mem_univ, true_and] at hq'
        exact hq hq'
      simp [basisQ, hne]
  · have hsub : incG n m C hrb outW w ⊆ nonNLReaders n m C hrb w := by
      intro j hj
      simp only [incG, gateAct, nonNLReaders, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact ⟨hj.1.1, hj.2⟩
    symm
    apply Finset.sum_subset hsub
    intro j hj hnot
    simp only [nonNLReaders, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [incG, gateAct, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hnot
    have hzero : dualVec n m C hrb outW ⟨n + m + j.val, by unfold wireCount; omega⟩ = 0 := by
      by_contra hne
      exact hnot ⟨hj.1, hne⟩ hj.2
    exact congrFun hzero q

lemma allAct_dual_ne_zero (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (w : Fin (wireCount n m C))
    (hw : w ∈ allAct n m C hrb outW) :
    dualVec n m C hrb outW w ≠ 0 := by
  simp only [allAct, srcAct, gateAct, Finset.mem_union, Finset.mem_filter, Finset.mem_map,
    Finset.mem_univ, true_and] at hw
  rcases hw with ⟨_, hne⟩ | ⟨j, ⟨_, hne⟩, rfl⟩
  · exact hne
  · rw [embN_eq]; exact hne

lemma incSet_nonempty_of_allAct (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (w : Fin (wireCount n m C))
    (hw : w ∈ allAct n m C hrb outW) :
    (incSet n m C hrb outW w).Nonempty := by
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  have h0 : dualVec n m C hrb outW w = 0 := by
    rw [dualVec_eq_sum_incSet, hemp, Finset.sum_empty]
  exact allAct_dual_ne_zero n m C hrb outW w hw h0

lemma sum_incSet_card_le (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) :
    ∑ w ∈ allAct n m C hrb outW, (incSet n m C hrb outW w).card ≤
      (2 * (effSet n m C hrb outW).card + 1) +
        2 * (gateAct2 n m C hrb outW).card + (gateAct1 n m C hrb outW).card := by
  have h1 : ∑ w ∈ allAct n m C hrb outW, (incSet n m C hrb outW w).card =
      (∑ w ∈ allAct n m C hrb outW, (incQ n m C hrb outW w).card) +
        (∑ w ∈ allAct n m C hrb outW, (incG n m C hrb outW w).card) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    exact incSet_card n m C hrb outW w
  rw [h1]
  have hQ : ∑ w ∈ allAct n m C hrb outW, (incQ n m C hrb outW w).card ≤
      2 * (effSet n m C hrb outW).card + 1 := by
    calc ∑ w ∈ allAct n m C hrb outW, (incQ n m C hrb outW w).card
        ≤ ∑ w : Fin (wireCount n m C), (incQ n m C hrb outW w).card :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      _ = ∑ w : Fin (wireCount n m C), ∑ q : QueryIdx n m C hrb outW,
            if queryTgt n m C hrb outW q = w then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro w _
          exact finset_card_le_sum_indicator Finset.univ (fun q => queryTgt n m C hrb outW q = w)
      _ = ∑ q : QueryIdx n m C hrb outW, ∑ w : Fin (wireCount n m C),
            if queryTgt n m C hrb outW q = w then 1 else 0 := Finset.sum_comm
      _ = ∑ _q : QueryIdx n m C hrb outW, 1 := by
          apply Finset.sum_congr rfl
          intro q _
          rw [Finset.sum_eq_single (queryTgt n m C hrb outW q)]
          · simp
          · intro w _ hne; simp [hne.symm]
          · intro h; exact False.elim (h (Finset.mem_univ _))
      _ = Fintype.card (QueryIdx n m C hrb outW) := by simp
      _ = 2 * (effSet n m C hrb outW).card + 1 := by
          rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_coe, Fintype.card_bool,
            Fintype.card_unit, mul_comm]
  have hG : ∑ w ∈ allAct n m C hrb outW, (incG n m C hrb outW w).card ≤
      2 * (gateAct2 n m C hrb outW).card + (gateAct1 n m C hrb outW).card := by
    calc ∑ w ∈ allAct n m C hrb outW, (incG n m C hrb outW w).card
        ≤ ∑ w : Fin (wireCount n m C), (incG n m C hrb outW w).card :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      _ = ∑ w : Fin (wireCount n m C), ∑ j ∈ gateAct n m C hrb outW,
            if w ∈ gateDepsFin n m C hrb j then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro w _
          exact finset_card_le_sum_indicator (gateAct n m C hrb outW)
            (fun j => w ∈ gateDepsFin n m C hrb j)
      _ = ∑ j ∈ gateAct n m C hrb outW, ∑ w : Fin (wireCount n m C),
            if w ∈ gateDepsFin n m C hrb j then 1 else 0 := Finset.sum_comm
      _ = ∑ j ∈ gateAct n m C hrb outW, (gateDeps (C.gates.get j)).card := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← finset_card_le_sum_indicator, Finset.filter_mem_eq_inter, Finset.univ_inter,
            gateDepsFin_card]
      _ = (∑ j ∈ gateAct2 n m C hrb outW, (gateDeps (C.gates.get j)).card) +
            (∑ j ∈ gateAct1 n m C hrb outW, (gateDeps (C.gates.get j)).card) := by
          have hpart : gateAct n m C hrb outW =
              gateAct2 n m C hrb outW ∪ gateAct1 n m C hrb outW := by
            ext j
            simp only [gateAct2, gateAct1, Finset.mem_union, Finset.mem_filter]
            constructor
            · intro hj
              have hle := gateDeps_card_le_two (C.gates.get j)
              by_cases h2 : (gateDeps (C.gates.get j)).card = 2
              · exact Or.inl ⟨hj, h2⟩
              · exact Or.inr ⟨hj, by omega⟩
            · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
          have hdisj2 : Disjoint (gateAct2 n m C hrb outW) (gateAct1 n m C hrb outW) := by
            rw [Finset.disjoint_left]
            intro j hj1 hj2
            simp only [gateAct2, gateAct1, Finset.mem_filter] at hj1 hj2
            omega
          rw [hpart, Finset.sum_union hdisj2]
      _ ≤ 2 * (gateAct2 n m C hrb outW).card + (gateAct1 n m C hrb outW).card := by
          have h2 : ∑ j ∈ gateAct2 n m C hrb outW, (gateDeps (C.gates.get j)).card ≤
              2 * (gateAct2 n m C hrb outW).card := by
            calc ∑ j ∈ gateAct2 n m C hrb outW, (gateDeps (C.gates.get j)).card
                ≤ ∑ _j ∈ gateAct2 n m C hrb outW, 2 := by
                  apply Finset.sum_le_sum
                  intro j hj
                  simp only [gateAct2, Finset.mem_filter] at hj
                  omega
              _ = 2 * (gateAct2 n m C hrb outW).card := by simp [mul_comm]
          have h1' : ∑ j ∈ gateAct1 n m C hrb outW, (gateDeps (C.gates.get j)).card ≤
              (gateAct1 n m C hrb outW).card := by
            calc ∑ j ∈ gateAct1 n m C hrb outW, (gateDeps (C.gates.get j)).card
                ≤ ∑ _j ∈ gateAct1 n m C hrb outW, 1 := by
                  apply Finset.sum_le_sum
                  intro j hj
                  simp only [gateAct1, Finset.mem_filter] at hj
                  exact hj.2
              _ = (gateAct1 n m C hrb outW).card := by simp
          omega
  omega

lemma rT_bound (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) :
    (∑ w ∈ allAct n m C hrb outW, ((incSet n m C hrb outW w).card - 1)) +
      (srcAct n m C hrb outW).card + (nlSet C).card ≤
      (2 * (effSet n m C hrb outW).card + 1) + (binSet C).card := by
  have hsum_add :
      (∑ w ∈ allAct n m C hrb outW, ((incSet n m C hrb outW w).card - 1)) +
        (allAct n m C hrb outW).card =
      ∑ w ∈ allAct n m C hrb outW, (incSet n m C hrb outW w).card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    have hpos : 1 ≤ (incSet n m C hrb outW w).card :=
      Finset.Nonempty.card_pos (incSet_nonempty_of_allAct n m C hrb outW w hw)
    omega
  have hle1 := sum_incSet_card_le n m C hrb outW
  have hall := allAct_card n m C hrb outW
  have hga2 : (gateAct2 n m C hrb outW).card ≤ (linBinSet C).card :=
    Finset.card_le_card (gateAct2_subset_linBin n m C hrb outW)
  have hbin := linBinSet_card_plus_nlSet C
  omega

def leftAct (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) : Finset (Fin n) :=
  Finset.univ.filter (fun u =>
    dualVec n m C hrb outW ⟨u.val, by unfold wireCount; omega⟩ ≠ 0)

def rightAct (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) : Finset (Fin m) :=
  Finset.univ.filter (fun v =>
    dualVec n m C hrb outW ⟨n + v.val, by unfold wireCount; omega⟩ ≠ 0)

lemma srcAct_card_ge (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) :
    (leftAct n m C hrb outW).card + (rightAct n m C hrb outW).card +
      (effSet n m C hrb outW).card ≤ (srcAct n m C hrb outW).card := by
  have hsub :
      ((leftAct n m C hrb outW).map (embL n m C) ∪ (rightAct n m C hrb outW).map (embR n m C)) ∪
        (effSet n m C hrb outW).map (embN n m C) ⊆ srcAct n m C hrb outW := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_map] at hw
    simp only [srcAct, srcFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw with (⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩) | ⟨k, hk, rfl⟩
    · simp only [leftAct, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rw [embL_eq]
      have hlt : u.val < n + m := by omega
      exact ⟨by simp [isSrc, hlt], hu⟩
    · simp only [rightAct, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      rw [embR_eq]
      have hlt : n + v.val < n + m := by omega
      exact ⟨by simp [isSrc, hlt], hv⟩
    · rw [embN_eq]
      have hknl : k ∈ nlSet C := effIter_subset_nl n m C hrb outW _ hk
      have hnotlt : ¬ (n + m + k.val) < n + m := by omega
      have hsrc : isSrc n m C ⟨n + m + k.val, by unfold wireCount; omega⟩ = true := by
        simp only [nlSet, Finset.mem_filter, Finset.mem_univ, true_and] at hknl
        simpa [isSrc, hnotlt] using hknl
      refine ⟨hsrc, ?_⟩
      intro hzero
      rcases effIter_witness n m C hrb outW C.gates.length k hk with h1 | ⟨k0, hk0, b, h2⟩
      · have hq := congrFun hzero (Sum.inr ())
        rw [dualVec_src n m C hrb outW ⟨n + m + k.val, by unfold wireCount; omega⟩ hsrc (Sum.inr ())] at hq
        exact h1 hq
      · have hq := congrFun hzero (Sum.inl (⟨k0, hk0⟩, b))
        rw [dualVec_src n m C hrb outW ⟨n + m + k.val, by unfold wireCount; omega⟩ hsrc (Sum.inl (⟨k0, hk0⟩, b))] at hq
        exact h2 hq
  have hd1 : Disjoint ((leftAct n m C hrb outW).map (embL n m C))
      ((rightAct n m C hrb outW).map (embR n m C)) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [Finset.mem_map] at hw1 hw2
    rcases hw1 with ⟨u, _, rfl⟩; rcases hw2 with ⟨v, _, hv⟩
    have := congrArg Fin.val hv; rw [embL_eq, embR_eq] at this; dsimp at this; omega
  have hd2 : Disjoint ((leftAct n m C hrb outW).map (embL n m C) ∪
      (rightAct n m C hrb outW).map (embR n m C))
      ((effSet n m C hrb outW).map (embN n m C)) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [Finset.mem_union, Finset.mem_map] at hw1 hw2
    rcases hw2 with ⟨k, _, rfl⟩
    rcases hw1 with ⟨u, _, hu⟩ | ⟨v, _, hv⟩
    · have := congrArg Fin.val hu; rw [embL_eq, embN_eq] at this; dsimp at this; omega
    · have := congrArg Fin.val hv; rw [embR_eq, embN_eq] at this; dsimp at this; omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
    Finset.card_map, Finset.card_map, Finset.card_map] at hcard
  exact hcard

lemma leftAct_card_ge (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C))
    (hinj : Function.Injective (pLeft n m C hrb outW)) :
    n ≤ (leftAct n m C hrb outW).card + 1 := by
  by_cases hex : ∃ u0 : Fin n, pLeft n m C hrb outW u0 = 0
  · rcases hex with ⟨u0, hu0⟩
    have hsub : (Finset.univ : Finset (Fin n)).erase u0 ⊆ leftAct n m C hrb outW := by
      intro u hu
      have hne : u ≠ u0 := (Finset.mem_erase.mp hu).1
      have hpne : pLeft n m C hrb outW u ≠ 0 := by
        intro h0; exact hne (hinj (h0.trans hu0.symm))
      simp only [leftAct, Finset.mem_filter, Finset.mem_univ, true_and]
      intro hd0
      apply hpne
      ext p
      have h1 := congrFun hd0 (Sum.inl p)
      have hlt : u.val < n + m := by omega
      have hsrc : isSrc n m C ⟨u.val, by unfold wireCount; omega⟩ = true := by simp [isSrc, hlt]
      rw [dualVec_src n m C hrb outW _ hsrc (Sum.inl p)] at h1
      exact h1
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_fin] at hc
    omega
  · push Not at hex
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ leftAct n m C hrb outW := by
      intro u _
      simp only [leftAct, Finset.mem_filter, Finset.mem_univ, true_and]
      intro hd0
      apply hex u
      ext p
      have h1 := congrFun hd0 (Sum.inl p)
      have hlt : u.val < n + m := by omega
      have hsrc : isSrc n m C ⟨u.val, by unfold wireCount; omega⟩ = true := by simp [isSrc, hlt]
      rw [dualVec_src n m C hrb outW _ hsrc (Sum.inl p)] at h1
      exact h1
    have hc := Finset.card_le_card hsub
    rw [Finset.card_fin] at hc
    omega

lemma rightAct_card_ge (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C))
    (hinj : Function.Injective (pRight n m C hrb outW)) :
    m ≤ (rightAct n m C hrb outW).card + 1 := by
  by_cases hex : ∃ v0 : Fin m, pRight n m C hrb outW v0 = 0
  · rcases hex with ⟨v0, hv0⟩
    have hsub : (Finset.univ : Finset (Fin m)).erase v0 ⊆ rightAct n m C hrb outW := by
      intro v hv
      have hne : v ≠ v0 := (Finset.mem_erase.mp hv).1
      have hpne : pRight n m C hrb outW v ≠ 0 := by
        intro h0; exact hne (hinj (h0.trans hv0.symm))
      simp only [rightAct, Finset.mem_filter, Finset.mem_univ, true_and]
      intro hd0
      apply hpne
      ext p
      have h1 := congrFun hd0 (Sum.inl p)
      have hlt : n + v.val < n + m := by omega
      have hsrc : isSrc n m C ⟨n + v.val, by unfold wireCount; omega⟩ = true := by simp [isSrc, hlt]
      rw [dualVec_src n m C hrb outW _ hsrc (Sum.inl p)] at h1
      exact h1
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ v0), Finset.card_fin] at hc
    omega
  · push Not at hex
    have hsub : (Finset.univ : Finset (Fin m)) ⊆ rightAct n m C hrb outW := by
      intro v _
      simp only [rightAct, Finset.mem_filter, Finset.mem_univ, true_and]
      intro hd0
      apply hex v
      ext p
      have h1 := congrFun hd0 (Sum.inl p)
      have hlt : n + v.val < n + m := by omega
      have hsrc : isSrc n m C ⟨n + v.val, by unfold wireCount; omega⟩ = true := by simp [isSrc, hlt]
      rw [dualVec_src n m C hrb outW _ hsrc (Sum.inl p)] at h1
      exact h1
    have hc := Finset.card_le_card hsub
    rw [Finset.card_fin] at hc
    omega

noncomputable def initList (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) : List (QueryIdx n m C hrb outW → F2) :=
  (Finset.univ : Finset (QueryIdx n m C hrb outW)).toList.map (basisQ n m C hrb outW)

lemma initList_length (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) :
    (initList n m C hrb outW).length = 2 * (effSet n m C hrb outW).card + 1 := by
  simp only [initList, List.length_map, Finset.length_toList, Finset.card_univ]
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_coe, Fintype.card_bool,
    Fintype.card_unit, mul_comm]

lemma basisQ_mem_initList (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (q : QueryIdx n m C hrb outW) :
    basisQ n m C hrb outW q ∈ initList n m C hrb outW := by
  simp [initList]

inductive GenList (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) : List (QueryIdx n m C hrb outW → F2) → Prop
  | base : GenList n m C hrb outW (initList n m C hrb outW)
  | step {L : List (QueryIdx n m C hrb outW → F2)}
      {a b : QueryIdx n m C hrb outW → F2} :
      GenList n m C hrb outW L → a ∈ L → b ∈ L →
      GenList n m C hrb outW (L ++ [a + b])

lemma append_finset_sum {α : Type*} [DecidableEq α]
    (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C))
    (L : List (QueryIdx n m C hrb outW → F2))
    (hL : GenList n m C hrb outW L)
    (S : Finset α) (hS : S.Nonempty) (f : α → QueryIdx n m C hrb outW → F2)
    (hf : ∀ a ∈ S, f a ∈ L) :
    ∃ L', GenList n m C hrb outW L' ∧
      L'.length = L.length + (S.card - 1) ∧
      (∀ x ∈ L, x ∈ L') ∧
      (∑ a ∈ S, f a) ∈ L' := by
  induction S using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hS)
  | insert a s ha ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨L1, hL1, hlen1, hsub1, hsum1⟩ :=
        ih hs (fun x hx => hf x (Finset.mem_insert_of_mem hx))
      have hfa : f a ∈ L1 := hsub1 _ (hf a (Finset.mem_insert_self a s))
      refine ⟨L1 ++ [f a + ∑ x ∈ s, f x], GenList.step hL1 hfa hsum1, ?_, ?_, ?_⟩
      · rw [List.length_append, List.length_singleton, hlen1, Finset.card_insert_of_notMem ha]
        have hpos : 1 ≤ s.card := Finset.Nonempty.card_pos hs
        omega
      · intro x hx
        exact List.mem_append_left _ (hsub1 x hx)
      · rw [Finset.sum_insert ha]
        exact List.mem_append_right _ (by simp)
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      refine ⟨L, hL, by simp, fun x hx => hx, ?_⟩
      simpa using hf a (Finset.mem_insert_self a ∅)

lemma exists_genList_covering_allAct (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) :
    ∃ L : List (QueryIdx n m C hrb outW → F2),
      GenList n m C hrb outW L ∧
      L.length = (2 * (effSet n m C hrb outW).card + 1) +
        ∑ w ∈ allAct n m C hrb outW, ((incSet n m C hrb outW w).card - 1) ∧
      (∀ q : QueryIdx n m C hrb outW, basisQ n m C hrb outW q ∈ L) ∧
      (∀ w ∈ allAct n m C hrb outW, dualVec n m C hrb outW w ∈ L) := by
  have hrec : ∀ k ≤ wireCount n m C,
      ∃ L : List (QueryIdx n m C hrb outW → F2),
        GenList n m C hrb outW L ∧
        L.length = (2 * (effSet n m C hrb outW).card + 1) +
          ∑ w ∈ (allAct n m C hrb outW).filter (fun w => wireCount n m C - k ≤ w.val),
            ((incSet n m C hrb outW w).card - 1) ∧
        (∀ q : QueryIdx n m C hrb outW, basisQ n m C hrb outW q ∈ L) ∧
        (∀ w ∈ allAct n m C hrb outW, wireCount n m C - k ≤ w.val →
          dualVec n m C hrb outW w ∈ L) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨initList n m C hrb outW, GenList.base, ?_,
        basisQ_mem_initList n m C hrb outW, ?_⟩
      · have hemp : (allAct n m C hrb outW).filter (fun w => wireCount n m C - 0 ≤ w.val) = ∅ := by
          ext w
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro _; have := w.isLt; omega
        rw [hemp, Finset.sum_empty, add_zero, initList_length]
      · intro w _ hge
        have := w.isLt; omega
    | succ k ih =>
      obtain ⟨L, hL, hlen, hbas, hcov⟩ := ih (by omega)
      let w0 : Fin (wireCount n m C) := ⟨wireCount n m C - 1 - k, by omega⟩
      by_cases hw0 : w0 ∈ allAct n m C hrb outW
      · have hne0 : (incSet n m C hrb outW w0).Nonempty :=
          incSet_nonempty_of_allAct n m C hrb outW w0 hw0
        have hmem_terms : ∀ e ∈ incSet n m C hrb outW w0, incTerm n m C hrb outW e ∈ L := by
          intro e he
          simp only [incSet, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk] at he
          rcases he with ⟨q, _, rfl⟩ | ⟨j, hj, rfl⟩
          · exact hbas q
          · simp only [incG, Finset.mem_filter] at hj
            have hlt : w0.val < n + m + j.val := gateDepsFin_lt n m C hrb j w0 hj.2
            have hall_j : (⟨n + m + j.val, by unfold wireCount; omega⟩ : Fin (wireCount n m C)) ∈
                allAct n m C hrb outW := by
              simp only [allAct, Finset.mem_union, Finset.mem_map]
              right; exact ⟨j, hj.1, embN_eq n m C j⟩
            exact hcov _ hall_j (by dsimp [w0] at hlt ⊢; omega)
        obtain ⟨L', hL', hlen', hsub', hsum'⟩ :=
          append_finset_sum n m C hrb outW L hL (incSet n m C hrb outW w0) hne0
            (incTerm n m C hrb outW) hmem_terms
        have hfilt_eq :
            (allAct n m C hrb outW).filter (fun w => wireCount n m C - (k + 1) ≤ w.val) =
              insert w0 ((allAct n m C hrb outW).filter (fun w => wireCount n m C - k ≤ w.val)) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hw, hge⟩
            by_cases hweq : w.val = wireCount n m C - 1 - k
            · left; ext; exact hweq
            · right; exact ⟨hw, by omega⟩
          · rintro (rfl | ⟨hw, hge⟩)
            · exact ⟨hw0, by dsimp [w0]; omega⟩
            · exact ⟨hw, by omega⟩
        have hnotmem : w0 ∉ (allAct n m C hrb outW).filter (fun w => wireCount n m C - k ≤ w.val) := by
          simp only [Finset.mem_filter, not_and]; intro _; dsimp [w0]; omega
        refine ⟨L', hL', ?_, fun q => hsub' _ (hbas q), ?_⟩
        · rw [hfilt_eq, Finset.sum_insert hnotmem, hlen', hlen]
          omega
        · intro w hw hge
          by_cases hweq : w = w0
          · subst hweq
            rwa [dualVec_eq_sum_incSet]
          · have hge' : wireCount n m C - k ≤ w.val := by
              have : w.val ≠ wireCount n m C - 1 - k := fun h => hweq (Fin.ext h)
              omega
            exact hsub' _ (hcov w hw hge')
      · have hfilt_eq :
            (allAct n m C hrb outW).filter (fun w => wireCount n m C - (k + 1) ≤ w.val) =
              (allAct n m C hrb outW).filter (fun w => wireCount n m C - k ≤ w.val) := by
          ext w
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hw, hge⟩
            have hne : w.val ≠ wireCount n m C - 1 - k := by
              intro h; apply hw0
              have : w0 = w := by ext; exact h.symm
              rwa [this]
            exact ⟨hw, by omega⟩
          · rintro ⟨hw, hge⟩
            exact ⟨hw, by omega⟩
        refine ⟨L, hL, by rw [hfilt_eq]; exact hlen, hbas, ?_⟩
        intro w hw hge
        have hne : w.val ≠ wireCount n m C - 1 - k := by
          intro h; apply hw0
          have : w0 = w := by ext; exact h.symm
          rwa [this]
        exact hcov w hw (by omega)
  obtain ⟨L, hL, hlen, hbas, hcov⟩ := hrec (wireCount n m C) le_rfl
  have hfilt_all :
      (allAct n m C hrb outW).filter (fun w => wireCount n m C - wireCount n m C ≤ w.val) =
        allAct n m C hrb outW := by
    ext w; simp
  rw [hfilt_all] at hlen
  exact ⟨L, hL, hlen, hbas, fun w hw => hcov w hw (by omega)⟩

def projQ (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (v : QueryIdx n m C hrb outW → F2) :
    EffElem n m C hrb outW × Bool → F2 :=
  fun p => v (Sum.inl p)

lemma projQ_add (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) (a b : QueryIdx n m C hrb outW → F2) :
    projQ n m C hrb outW (a + b) = projQ n m C hrb outW a + projQ n m C hrb outW b :=
  rfl

lemma projQ_basisQ_last (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C)) :
    projQ n m C hrb outW (basisQ n m C hrb outW (Sum.inr ())) = 0 := by
  ext p
  simp [projQ, basisQ]

lemma projQ_list_contains_left (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C))
    (L : List (QueryIdx n m C hrb outW → F2))
    (hbas : ∀ q, basisQ n m C hrb outW q ∈ L)
    (hcov : ∀ w ∈ allAct n m C hrb outW, dualVec n m C hrb outW w ∈ L) :
    Finset.univ.image (pLeft n m C hrb outW) ⊆ (L.map (projQ n m C hrb outW)).toFinset := by
  intro f hf
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hf
  rcases hf with ⟨u, rfl⟩
  simp only [List.mem_toFinset, List.mem_map]
  by_cases hp0 : pLeft n m C hrb outW u = 0
  · refine ⟨basisQ n m C hrb outW (Sum.inr ()), hbas _, ?_⟩
    rw [projQ_basisQ_last, hp0]
  · let wu : Fin (wireCount n m C) := ⟨u.val, by unfold wireCount; omega⟩
    have hsrc : isSrc n m C wu = true := by
      have : wu.val < n + m := by simp [wu]; omega
      simp [isSrc, this]
    have hproj : projQ n m C hrb outW (dualVec n m C hrb outW wu) = pLeft n m C hrb outW u := by
      ext p
      exact dualVec_src n m C hrb outW wu hsrc (Sum.inl p)
    have hdne : dualVec n m C hrb outW wu ≠ 0 := by
      intro h0
      apply hp0
      rw [← hproj, h0]
      rfl
    have hmem : wu ∈ allAct n m C hrb outW := by
      simp only [allAct, srcAct, srcFinset, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact Or.inl ⟨hsrc, hdne⟩
    exact ⟨dualVec n m C hrb outW wu, hcov wu hmem, hproj⟩

lemma projQ_list_contains_right (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C))
    (L : List (QueryIdx n m C hrb outW → F2))
    (hbas : ∀ q, basisQ n m C hrb outW q ∈ L)
    (hcov : ∀ w ∈ allAct n m C hrb outW, dualVec n m C hrb outW w ∈ L) :
    Finset.univ.image (pRight n m C hrb outW) ⊆ (L.map (projQ n m C hrb outW)).toFinset := by
  intro f hf
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hf
  rcases hf with ⟨v, rfl⟩
  simp only [List.mem_toFinset, List.mem_map]
  by_cases hp0 : pRight n m C hrb outW v = 0
  · refine ⟨basisQ n m C hrb outW (Sum.inr ()), hbas _, ?_⟩
    rw [projQ_basisQ_last, hp0]
  · let wv : Fin (wireCount n m C) := ⟨n + v.val, by unfold wireCount; omega⟩
    have hsrc : isSrc n m C wv = true := by
      have : wv.val < n + m := by simp [wv]
      simp [isSrc, this]
    have hproj : projQ n m C hrb outW (dualVec n m C hrb outW wv) = pRight n m C hrb outW v := by
      ext p
      exact dualVec_src n m C hrb outW wv hsrc (Sum.inl p)
    have hdne : dualVec n m C hrb outW wv ≠ 0 := by
      intro h0
      apply hp0
      rw [← hproj, h0]
      rfl
    have hmem : wv ∈ allAct n m C hrb outW := by
      simp only [allAct, srcAct, srcFinset, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact Or.inl ⟨hsrc, hdne⟩
    exact ⟨dualVec n m C hrb outW wv, hcov wv hmem, hproj⟩

lemma genList_last_bit_zero (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C)
    (outW : Fin (wireCount n m C))
    (L : List (QueryIdx n m C hrb outW → F2))
    (hL : GenList n m C hrb outW L)
    (hnodup : (L.map (projQ n m C hrb outW)).Nodup) :
    ∀ x ∈ L, x = basisQ n m C hrb outW (Sum.inr ()) ∨ x (Sum.inr ()) = 0 := by
  induction hL with
  | base =>
    intro x hx
    simp only [initList, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨q, rfl⟩
    cases q with
    | inl p =>
      right
      simp [basisQ]
    | inr u =>
      left
      cases u
      rfl
  | @step L0 a b hL0 ha hb ih =>
    rw [List.map_append, List.map_singleton, List.nodup_append] at hnodup
    rcases hnodup with ⟨hnodup0, _, hdisj⟩
    have hih := ih hnodup0
    have hnotmem : projQ n m C hrb outW (a + b) ∉ L0.map (projQ n m C hrb outW) := by
      intro hmem
      exact hdisj _ hmem _ (by simp) rfl
    have ha0 : a (Sum.inr ()) = 0 := by
      rcases hih a ha with rfl | ha_zero
      · exfalso
        apply hnotmem
        rw [projQ_add, projQ_basisQ_last, zero_add]
        exact List.mem_map_of_mem hb
      · exact ha_zero
    have hb0 : b (Sum.inr ()) = 0 := by
      rcases hih b hb with rfl | hb_zero
      · exfalso
        apply hnotmem
        rw [projQ_add, projQ_basisQ_last, add_zero]
        exact List.mem_map_of_mem ha
      · exact hb_zero
    intro x hx
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx0 | rfl
    · exact hih x hx0
    · right
      simp [Pi.add_apply, ha0, hb0]

lemma pow_four_eq_imp (h t : ℕ) (heq : 4 ^ h = 4 ^ t) : h = t := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := Nat.pow_lt_pow_right (by omega : 1 < 4) hlt
    omega
  · have := Nat.pow_lt_pow_right (by omega : 1 < 4) hgt
    omega

lemma main_proof
    (n m : ℕ) (H : Fin n → Fin m → Bool) (C : Circuit)
    (hn : 2 ≤ n) (_hm : 2 ≤ m)
    (hrow : ∀ i j : Fin n, i ≠ j → ∀ f : Bool, ∃ y, H i y ≠ xor f (H j y))
    (hcol : ∀ i j : Fin m, i ≠ j → ∀ f : Bool, ∃ x, H x i ≠ xor f (H x j))
    (hfan : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (hrep : Represents H C) :
    let b := C.gates.countP (fun g => g.inputs.length == 2)
    let t := C.gates.countP (fun g => (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true])))
    max n m ≤ 4 ^ t ∧ n + m + max n m ≤ b + 2 * t + 4 ∧
      (n = 4 ^ t → m = n →
        ((∃ i c, ∀ y, H i y = c) ∨ (∃ j c, ∀ x, H x j = c)) →
        3 * n ≤ b + 2 * t + 3) := by
  dsimp only
  rw [← binSet_card C, ← nlSet_card C]
  set b := (binSet C).card
  set t := (nlSet C).card
  have hout : C.output < wireCount n m C := output_lt_wireCount n m H C hn hrow hrep
  set outW : Fin (wireCount n m C) := ⟨C.output, hout⟩
  set h := (effSet n m C hrb outW).card
  have hht : h ≤ t := Finset.card_le_card (effIter_subset_nl n m C hrb outW C.gates.length)
  have hinjL := pLeft_injective n m H C hrow hfan hrb hrep hout
  have hinjR := pRight_injective n m H C hcol hfan hrb hrep hout
  have hn_le_4h : n ≤ 4 ^ h := by
    have hc := Fintype.card_le_of_injective _ hinjL
    rw [Fintype.card_fin, card_eff_fun] at hc
    exact hc
  have hm_le_4h : m ≤ 4 ^ h := by
    have hc := Fintype.card_le_of_injective _ hinjR
    rw [Fintype.card_fin, card_eff_fun] at hc
    exact hc
  have h4h_le_4t : 4 ^ h ≤ 4 ^ t := Nat.pow_le_pow_right (by omega) hht
  have hbound1 : max n m ≤ 4 ^ t := by
    exact max_le (le_trans hn_le_4h h4h_le_4t) (le_trans hm_le_4h h4h_le_4t)
  obtain ⟨L, hLgen, hLlen, hLbas, hLcov⟩ := exists_genList_covering_allAct n m C hrb outW
  have hsubL := projQ_list_contains_left n m C hrb outW L hLbas hLcov
  have hsubR := projQ_list_contains_right n m C hrb outW L hLbas hLcov
  have hn_le_toFin : n ≤ (L.map (projQ n m C hrb outW)).toFinset.card := by
    calc n = (Finset.univ.image (pLeft n m C hrb outW)).card := by
            rw [Finset.card_image_of_injective _ hinjL, Finset.card_fin]
      _ ≤ (L.map (projQ n m C hrb outW)).toFinset.card := Finset.card_le_card hsubL
  have hm_le_toFin : m ≤ (L.map (projQ n m C hrb outW)).toFinset.card := by
    calc m = (Finset.univ.image (pRight n m C hrb outW)).card := by
            rw [Finset.card_image_of_injective _ hinjR, Finset.card_fin]
      _ ≤ (L.map (projQ n m C hrb outW)).toFinset.card := Finset.card_le_card hsubR
  have htoFin_le_L : (L.map (projQ n m C hrb outW)).toFinset.card ≤ L.length := by
    calc (L.map (projQ n m C hrb outW)).toFinset.card
        ≤ (L.map (projQ n m C hrb outW)).length := List.toFinset_card_le _
      _ = L.length := List.length_map _
  have hmax_le_L : max n m ≤ L.length := max_le (le_trans hn_le_toFin htoFin_le_L)
    (le_trans hm_le_toFin htoFin_le_L)
  have hleft_ge := leftAct_card_ge n m C hrb outW hinjL
  have hright_ge := rightAct_card_ge n m C hrb outW hinjR
  have hsrc_ge := srcAct_card_ge n m C hrb outW
  have hrT := rT_bound n m C hrb outW
  have hbound2 : n + m + max n m ≤ b + 2 * t + 4 := by
    omega
  refine ⟨hbound1, hbound2, ?_⟩
  intro hn_eq hm_eq hconst
  by_contra hgt
  push Not at hgt
  have h4h_eq : 4 ^ h = 4 ^ t := le_antisymm h4h_le_4t (by omega)
  have hh_eq_t : h = t := pow_four_eq_imp h t h4h_eq
  have hL_eq_n : L.length = n := by omega
  have hleft_eq : (leftAct n m C hrb outW).card + 1 = n := by omega
  have hright_eq : (rightAct n m C hrb outW).card + 1 = m := by omega
  have hnodup : (L.map (projQ n m C hrb outW)).Nodup := by
    apply nodup_of_length_le_toFinset_card
    rw [List.length_map]
    omega
  have hlast0 := genList_last_bit_zero n m C hrb outW L hLgen hnodup
  have hcard_eq_L : Fintype.card (Fin n) = Fintype.card (EffElem n m C hrb outW × Bool → F2) := by
    rw [Fintype.card_fin, card_eff_fun]
    change n = 4 ^ h
    rw [hh_eq_t, hn_eq]
  have hbijL : Function.Bijective (pLeft n m C hrb outW) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinjL, hcard_eq_L⟩
  have hcard_eq_R : Fintype.card (Fin m) = Fintype.card (EffElem n m C hrb outW × Bool → F2) := by
    rw [Fintype.card_fin, card_eff_fun]
    change m = 4 ^ h
    rw [hh_eq_t, hm_eq, hn_eq]
  have hbijR : Function.Bijective (pRight n m C hrb outW) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinjR, hcard_eq_R⟩
  have hout_left_zero : ∀ u : Fin n,
      linVec n m C hrb outW ⟨u.val, by unfold wireCount; omega⟩ = 0 := by
    obtain ⟨u0, hu0⟩ := hbijL.2 0
    have hu0_not : u0 ∉ leftAct n m C hrb outW := by
      have hsub : (Finset.univ : Finset (Fin n)).erase u0 ⊆ leftAct n m C hrb outW := by
        intro u hu
        have hne : u ≠ u0 := (Finset.mem_erase.mp hu).1
        have hpne : pLeft n m C hrb outW u ≠ 0 := by
          intro h0; exact hne (hinjL (h0.trans hu0.symm))
        simp only [leftAct, Finset.mem_filter, Finset.mem_univ, true_and]
        intro hd0
        apply hpne
        ext p
        have h1 := congrFun hd0 (Sum.inl p)
        have hlt : u.val < n + m := by omega
        have hsrc : isSrc n m C ⟨u.val, by unfold wireCount; omega⟩ = true := by simp [isSrc, hlt]
        rw [dualVec_src n m C hrb outW _ hsrc (Sum.inl p)] at h1
        exact h1
      have hcard_eq : ((Finset.univ : Finset (Fin n)).erase u0).card =
          (leftAct n m C hrb outW).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_fin]
        omega
      have heq_set : (Finset.univ : Finset (Fin n)).erase u0 = leftAct n m C hrb outW :=
        Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_eq.symm)
      rw [← heq_set]
      exact Finset.notMem_erase u0 _
    intro u
    let wu : Fin (wireCount n m C) := ⟨u.val, by unfold wireCount; omega⟩
    have hsrc : isSrc n m C wu = true := by
      have : wu.val < n + m := by simp [wu]; omega
      simp [isSrc, this]
    have htrans : linVec n m C hrb outW wu = dualVec n m C hrb outW wu (Sum.inr ()) :=
      (dualVec_src n m C hrb outW wu hsrc (Sum.inr ())).symm
    rw [htrans]
    by_cases hu : u = u0
    · subst hu
      simp only [leftAct, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hu0_not
      exact congrFun hu0_not (Sum.inr ())
    · have hpne : pLeft n m C hrb outW u ≠ 0 := by
        intro h0; exact hu (hinjL (h0.trans hu0.symm))
      have hproj : projQ n m C hrb outW (dualVec n m C hrb outW wu) = pLeft n m C hrb outW u := by
        ext p; exact dualVec_src n m C hrb outW wu hsrc (Sum.inl p)
      have hdne : dualVec n m C hrb outW wu ≠ 0 := by
        intro h0; apply hpne; rw [← hproj, h0]; rfl
      have hmemL : dualVec n m C hrb outW wu ∈ L := by
        apply hLcov
        simp only [allAct, srcAct, srcFinset, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact Or.inl ⟨hsrc, hdne⟩
      rcases hlast0 _ hmemL with heq_last | hzero
      · exfalso
        apply hpne
        rw [← hproj, heq_last, projQ_basisQ_last]
      · exact hzero
  have hout_right_zero : ∀ v : Fin m,
      linVec n m C hrb outW ⟨n + v.val, by unfold wireCount; omega⟩ = 0 := by
    obtain ⟨v0, hv0⟩ := hbijR.2 0
    have hv0_not : v0 ∉ rightAct n m C hrb outW := by
      have hsub : (Finset.univ : Finset (Fin m)).erase v0 ⊆ rightAct n m C hrb outW := by
        intro v hv
        have hne : v ≠ v0 := (Finset.mem_erase.mp hv).1
        have hpne : pRight n m C hrb outW v ≠ 0 := by
          intro h0; exact hne (hinjR (h0.trans hv0.symm))
        simp only [rightAct, Finset.mem_filter, Finset.mem_univ, true_and]
        intro hd0
        apply hpne
        ext p
        have h1 := congrFun hd0 (Sum.inl p)
        have hlt : n + v.val < n + m := by omega
        have hsrc : isSrc n m C ⟨n + v.val, by unfold wireCount; omega⟩ = true := by simp [isSrc, hlt]
        rw [dualVec_src n m C hrb outW _ hsrc (Sum.inl p)] at h1
        exact h1
      have hcard_eq : ((Finset.univ : Finset (Fin m)).erase v0).card =
          (rightAct n m C hrb outW).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ v0), Finset.card_fin]
        omega
      have heq_set : (Finset.univ : Finset (Fin m)).erase v0 = rightAct n m C hrb outW :=
        Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_eq.symm)
      rw [← heq_set]
      exact Finset.notMem_erase v0 _
    intro v
    let wv : Fin (wireCount n m C) := ⟨n + v.val, by unfold wireCount; omega⟩
    have hsrc : isSrc n m C wv = true := by
      have : wv.val < n + m := by simp [wv]
      simp [isSrc, this]
    have htrans : linVec n m C hrb outW wv = dualVec n m C hrb outW wv (Sum.inr ()) :=
      (dualVec_src n m C hrb outW wv hsrc (Sum.inr ())).symm
    rw [htrans]
    by_cases hv : v = v0
    · subst hv
      simp only [rightAct, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hv0_not
      exact congrFun hv0_not (Sum.inr ())
    · have hpne : pRight n m C hrb outW v ≠ 0 := by
        intro h0; exact hv (hinjR (h0.trans hv0.symm))
      have hproj : projQ n m C hrb outW (dualVec n m C hrb outW wv) = pRight n m C hrb outW v := by
        ext p; exact dualVec_src n m C hrb outW wv hsrc (Sum.inl p)
      have hdne : dualVec n m C hrb outW wv ≠ 0 := by
        intro h0; apply hpne; rw [← hproj, h0]; rfl
      have hmemL : dualVec n m C hrb outW wv ∈ L := by
        apply hLcov
        simp only [allAct, srcAct, srcFinset, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact Or.inl ⟨hsrc, hdne⟩
      rcases hlast0 _ hmemL with heq_last | hzero
      · exfalso
        apply hpne
        rw [← hproj, heq_last, projQ_basisQ_last]
      · exact hzero
  have hH_of_sum : ∀ u1 u2 : Fin n, ∀ v1 v2 : Fin m,
      pLeft n m C hrb outW u1 + pRight n m C hrb outW v1 =
      pLeft n m C hrb outW u2 + pRight n m C hrb outW v2 →
      H u1 v1 = H u2 v2 := by
    intro u1 u2 v1 v2 hsum
    apply b2f_injective
    have h1 : b2f (H u1 v1) = wireVal n m C u1 v1 outW := by rw [← hrep u1 v1]; rfl
    have h2 : b2f (H u2 v2) = wireVal n m C u2 v2 outW := by rw [← hrep u2 v2]; rfl
    rw [h1, h2, wireVal_expand n m C hfan hrb u1 v1 outW, wireVal_expand n m C hfan hrb u2 v2 outW,
      hout_left_zero u1, hout_left_zero u2, hout_right_zero v1, hout_right_zero v2]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hc : linVec n m C hrb outW ⟨n + m + k.val, by unfold wireCount; omega⟩ = 0
    · simp [hc]
    · have hkeff : k ∈ effSet n m C hrb outW := effSet_closed_out n m C hrb outW k hk hc
      rw [eff_wireVal_eq_of_sum_eq n m C hfan hrb outW u1 u2 v1 v2 hsum k hkeff]
  have hall_const : ∃ c : Bool, ∀ u v, H u v = c := by
    rcases hconst with ⟨i, c, hi⟩ | ⟨j, c, hj⟩
    · refine ⟨c, fun u v => ?_⟩
      obtain ⟨y, hy⟩ := hbijR.2 (pLeft n m C hrb outW i + pLeft n m C hrb outW u + pRight n m C hrb outW v)
      have hsum : pLeft n m C hrb outW u + pRight n m C hrb outW v =
                  pLeft n m C hrb outW i + pRight n m C hrb outW y := by
        rw [hy]
        ext p
        simp only [Pi.add_apply]
        exact f2_add_cancel_left (pLeft n m C hrb outW i p)
          (pLeft n m C hrb outW u p) (pRight n m C hrb outW v p)
      rw [hH_of_sum u i v y hsum, hi y]
    · refine ⟨c, fun u v => ?_⟩
      obtain ⟨x, hx⟩ := hbijL.2 (pLeft n m C hrb outW u + pRight n m C hrb outW v + pRight n m C hrb outW j)
      have hsum : pLeft n m C hrb outW u + pRight n m C hrb outW v =
                  pLeft n m C hrb outW x + pRight n m C hrb outW j := by
        rw [hx]
        ext p
        simp only [Pi.add_apply]
        exact f2_add_cancel_right (pLeft n m C hrb outW u p)
          (pRight n m C hrb outW v p) (pRight n m C hrb outW j p)
      rw [hH_of_sum u x v j hsum, hj x]
  rcases hall_const with ⟨c, hc⟩
  obtain ⟨y, hy⟩ := hrow ⟨0, by omega⟩ ⟨1, by omega⟩ (by intro h; simp at h) false
  rw [hc, hc] at hy
  exact hy (by cases c <;> rfl)

end PEqualNP.Outside.L_meta_25797_aux

theorem PEqualNP.Outside.L_meta_25797 :
  ∀ (n m : ℕ) (H : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
    2 ≤ n → 2 ≤ m →
    (∀ i j : Fin n, i ≠ j → ∀ f : Bool, ∃ y, H i y ≠ xor f (H j y)) →
    (∀ i j : Fin m, i ≠ j → ∀ f : Bool, ∃ x, H x i ≠ xor f (H x j)) →
    (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C →
    PEqualNP.Represents.Represents H C →
    let b := C.gates.countP (fun g => g.inputs.length == 2)
    let t := C.gates.countP (fun g => (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
          (xor (g.op.eval [true,false]) (g.op.eval [true,true])))
    max n m ≤ 4^t ∧ n + m + max n m ≤ b + 2*t + 4 ∧
      (n = 4^t → m = n →
        ((∃ i c, ∀ y, H i y = c) ∨ (∃ j c, ∀ x, H x j = c)) →
        3*n ≤ b + 2*t + 3) :=
  PEqualNP.Outside.L_meta_25797_aux.main_proof
