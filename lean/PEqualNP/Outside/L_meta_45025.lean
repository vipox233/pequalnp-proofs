import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45025_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def valid (w : Nat) (C : Circuit) : Prop :=
  ReadsBack w C ∧ ∀ g ∈ C.gates, g.inputs.length ≤ 2

lemma ite_pos {α : Sort _} {P : Prop} [Decidable P] {a b : α} (h : P) :
    (if P then a else b) = a := ite_eq_left h

lemma ite_neg {α : Sort _} {P : Prop} [Decidable P] {a b : α} (h : ¬P) :
    (if P then a else b) = b := ite_eq_right h

lemma dite_pos {α : Sort _} {P : Prop} [Decidable P] {t : P → α} {e : ¬P → α} (h : P) :
    (if hp : P then t hp else e hp) = t h := dite_eq_left h

lemma dite_neg {α : Sort _} {P : Prop} [Decidable P] {t : P → α} {e : ¬P → α} (h : ¬P) :
    (if hp : P then t hp else e hp) = e h := dite_eq_right h

lemma decide_eq_decide_of_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    decide P = decide Q := by
  by_cases hp : P
  · rw [decide_eq_true hp, decide_eq_true (h.mp hp)]
  · rw [decide_eq_false hp, decide_eq_false (fun hq => hp (h.mpr hq))]

def xorFin {n : Nat} (f : Fin n → Bool) : Bool :=
  (List.finRange n).foldr (fun i acc => xor (f i) acc) false

lemma xorFin_zero (f : Fin 0 → Bool) : xorFin f = false := rfl

lemma foldr_xor_eq_false {α : Type _} (l : List α) (f : α → Bool)
    (h : ∀ x ∈ l, f x = false) :
    l.foldr (fun x acc => xor (f x) acc) false = false := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldr_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
    rfl

lemma xorFin_eq_false {n : Nat} (f : Fin n → Bool) (h : ∀ i, f i = false) :
    xorFin f = false :=
  foldr_xor_eq_false _ f (fun i _ => h i)

lemma xorFin_congr {n : Nat} (f g : Fin n → Bool) (h : ∀ i, f i = g i) :
    xorFin f = xorFin g := by
  have : f = g := funext h
  rw [this]

lemma foldr_xor_xor {α : Type _} (l : List α) (f g : α → Bool) :
    l.foldr (fun x acc => xor (xor (f x) (g x)) acc) false =
    xor (l.foldr (fun x acc => xor (f x) acc) false)
        (l.foldr (fun x acc => xor (g x) acc) false) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldr_cons, ih]
    cases f a <;> cases g a <;>
      cases t.foldr (fun x acc => xor (f x) acc) false <;>
      cases t.foldr (fun x acc => xor (g x) acc) false <;> rfl

lemma xorFin_xor {n : Nat} (f g : Fin n → Bool) :
    xorFin (fun i => xor (f i) (g i)) = xor (xorFin f) (xorFin g) :=
  foldr_xor_xor _ f g

lemma foldr_xor_and_left {α : Type _} (l : List α) (c : Bool) (f : α → Bool) :
    l.foldr (fun x acc => xor (c && f x) acc) false =
    (c && l.foldr (fun x acc => xor (f x) acc) false) := by
  cases c
  · simp only [Bool.false_and]
    exact foldr_xor_eq_false l (fun _ => false) (fun _ _ => rfl)
  · simp only [Bool.true_and]

lemma xorFin_and_left {n : Nat} (c : Bool) (f : Fin n → Bool) :
    xorFin (fun i => c && f i) = (c && xorFin f) :=
  foldr_xor_and_left _ c f

lemma xorFin_and_right {n : Nat} (f : Fin n → Bool) (c : Bool) :
    xorFin (fun i => f i && c) = (xorFin f && c) := by
  have h1 : (fun i => f i && c) = (fun i => c && f i) := funext (fun i => Bool.and_comm _ _)
  rw [h1, xorFin_and_left, Bool.and_comm]

lemma foldr_xor_single {α : Type _} [DecidableEq α] (l : List α) (x0 : α) (f : α → Bool)
    (hnd : l.Nodup) (hmem : x0 ∈ l) (hzero : ∀ x ∈ l, x ≠ x0 → f x = false) :
    l.foldr (fun x acc => xor (f x) acc) false = f x0 := by
  induction l with
  | nil => cases hmem
  | cons a t ih =>
    simp only [List.foldr_cons]
    rcases List.nodup_cons.mp hnd with ⟨ha_not, ht_nd⟩
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · rw [foldr_xor_eq_false t f (fun x hx => hzero x (List.mem_cons_of_mem x0 hx) (fun heq => ha_not (heq ▸ hx)))]
      exact Bool.xor_false _
    · have ha0 : a ≠ x0 := fun heq => ha_not (heq ▸ hmem')
      rw [hzero a List.mem_cons_self ha0, Bool.false_xor]
      exact ih ht_nd hmem' (fun x hx hne => hzero x (List.mem_cons_of_mem a hx) hne)

lemma xorFin_single' {n : Nat} (i0 : Fin n) (f : Fin n → Bool)
    (hzero : ∀ i : Fin n, i ≠ i0 → f i = false) :
    xorFin f = f i0 :=
  foldr_xor_single (List.finRange n) i0 f (List.nodup_finRange n) (List.mem_finRange i0)
    (fun i _ hne => hzero i hne)

lemma xorFin_swap {m n : Nat} (f : Fin m → Fin n → Bool) :
    xorFin (fun i => xorFin (fun j => f i j)) = xorFin (fun j => xorFin (fun i => f i j)) := by
  unfold xorFin
  induction (List.finRange m) with
  | nil =>
    simp only [List.foldr_nil]
    exact (foldr_xor_eq_false _ _ (fun _ _ => rfl)).symm
  | cons a t ih =>
    simp only [List.foldr_cons, ih]
    rw [← foldr_xor_xor]

lemma xorFin_succ {n : Nat} (f : Fin (n + 1) → Bool) :
    xorFin f = xor (xorFin (fun i : Fin n => f i.castSucc)) (f (Fin.last n)) := by
  unfold xorFin
  have hfr : List.finRange (n + 1) = (List.finRange n).map Fin.castSucc ++ [Fin.last n] := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.length_finRange] at h1
      by_cases hi : i < n
      · rw [List.getElem_finRange, List.getElem_append_left (by simp; omega), List.getElem_map, List.getElem_finRange]
        rfl
      · have hie : i = n := by omega
        subst hie
        rw [List.getElem_finRange, List.getElem_append_right (by simp)]
        simp [Fin.last]
  rw [hfr, List.foldr_append, List.foldr_cons, List.foldr_nil, Bool.xor_false]
  have hgen : ∀ (l : List (Fin n)) (b : Bool),
      (l.map Fin.castSucc).foldr (fun i acc => xor (f i) acc) b =
      xor (l.foldr (fun i acc => xor (f i.castSucc) acc) false) b := by
    intro l b
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.foldr_cons, ih]
      cases f a.castSucc <;> cases t.foldr (fun i acc => xor (f i.castSucc) acc) false <;> cases b <;> rfl
  exact hgen (List.finRange n) (f (Fin.last n))

lemma xorFin_cast {m n : Nat} (h : m = n) (f : Fin m → Bool) (g : Fin n → Bool)
    (heq : ∀ i (h1 : i < m) (h2 : i < n), f ⟨i, h1⟩ = g ⟨i, h2⟩) :
    xorFin f = xorFin g := by
  subst h
  exact xorFin_congr f g (fun ⟨i, hi⟩ => heq i hi hi)

lemma xorFin_add_split {a b : Nat} (f : Fin (a + b) → Bool) :
    xorFin f = xor (xorFin (fun i : Fin a => f ⟨i.val, by omega⟩))
                   (xorFin (fun j : Fin b => f ⟨a + j.val, by omega⟩)) := by
  induction b with
  | zero =>
    rw [xorFin_zero, Bool.xor_false]
    exact xorFin_cast (Nat.add_zero a) _ _ (fun _ _ _ => rfl)
  | succ b ih =>
    have h_ih := ih (fun i : Fin (a + b) => f ⟨i.val, by omega⟩)
    rw [xorFin_cast (show a + (b + 1) = (a + b) + 1 by omega) f (fun i => f ⟨i.val, by omega⟩) (fun _ _ _ => rfl),
      xorFin_succ]
    have hL : xorFin (fun i : Fin (a + b) => f ⟨i.castSucc.val, by omega⟩) =
        xor (xorFin (fun i : Fin a => f ⟨i.val, by omega⟩)) (xorFin (fun j : Fin b => f ⟨a + j.val, by omega⟩)) := h_ih
    rw [hL, xorFin_succ (fun j : Fin (b + 1) => f ⟨a + j.val, by omega⟩)]
    have h3 : f ⟨(Fin.last (a + b)).val, by omega⟩ = f ⟨a + (Fin.last b).val, by omega⟩ :=
      congrArg f (Fin.ext (by simp [Fin.last]))
    rw [h3, Bool.xor_assoc]; rfl

lemma xorFin_split_pred {n : Nat} (p : Fin n → Bool) (f : Fin n → Bool) :
    xorFin f = xor (xorFin (fun i => p i && f i)) (xorFin (fun i => !(p i) && f i)) := by
  rw [← xorFin_xor]
  apply xorFin_congr; intro i; cases p i <;> cases f i <;> rfl

def dot {n : Nat} (a b : Fin n → Bool) : Bool :=
  xorFin (fun i => a i && b i)

lemma dot_comm {n : Nat} (a b : Fin n → Bool) : dot a b = dot b a := by
  unfold dot; apply xorFin_congr; intro i; exact Bool.and_comm _ _

lemma dot_zero_right {n : Nat} (a : Fin n → Bool) : dot a (fun _ => false) = false := by
  unfold dot; exact xorFin_eq_false _ (fun i => Bool.and_false _)

lemma dot_zero_left {n : Nat} (b : Fin n → Bool) : dot (fun _ => false) b = false := by
  rw [dot_comm]; exact dot_zero_right b

lemma dot_xor_left {n : Nat} (a b c : Fin n → Bool) :
    dot (fun i => xor (a i) (b i)) c = xor (dot a c) (dot b c) := by
  unfold dot; rw [← xorFin_xor]; apply xorFin_congr; intro i; dsimp only
  cases a i <;> cases b i <;> cases c i <;> rfl

lemma dot_xor_right {n : Nat} (a b c : Fin n → Bool) :
    dot a (fun i => xor (b i) (c i)) = xor (dot a b) (dot a c) := by
  rw [dot_comm, dot_xor_left, dot_comm b a, dot_comm c a]

def eVec {n : Nat} (p : Fin n) : Fin n → Bool := fun i => decide (i = p)

lemma dot_eVec {n : Nat} (a : Fin n → Bool) (p : Fin n) : dot a (eVec p) = a p := by
  unfold dot eVec
  rw [xorFin_single' p]
  · simp
  · intro i hi; simp [hi]

lemma dot_eVec_left {n : Nat} (p : Fin n) (b : Fin n → Bool) : dot (eVec p) b = b p := by
  rw [dot_comm]; exact dot_eVec b p

def IsAffine {n : Nat} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (c : Bool) (coeff : Fin n → Bool), ∀ y, f y = xor c (dot coeff y)

lemma isAffine_const {n : Nat} (c : Bool) : IsAffine (fun _ : Fin n → Bool => c) :=
  ⟨c, fun _ => false, fun y => by rw [dot_zero_left, Bool.xor_false]⟩

lemma isAffine_coord {n : Nat} (p : Fin n) : IsAffine (fun y : Fin n → Bool => y p) :=
  ⟨false, eVec p, fun y => by rw [dot_eVec_left, Bool.false_xor]⟩

lemma isAffine_xor {n : Nat} {f g : (Fin n → Bool) → Bool}
    (hf : IsAffine f) (hg : IsAffine g) : IsAffine (fun y => xor (f y) (g y)) := by
  rcases hf with ⟨cf, af, hfe⟩
  rcases hg with ⟨cg, ag, hge⟩
  refine ⟨xor cf cg, fun i => xor (af i) (ag i), fun y => ?_⟩
  dsimp only; rw [hfe y, hge y, dot_xor_left]
  cases cf <;> cases cg <;> cases dot af y <;> cases dot ag y <;> rfl

lemma isAffine_not {n : Nat} {f : (Fin n → Bool) → Bool} (hf : IsAffine f) :
    IsAffine (fun y => !(f y)) := by
  have heq : (fun y => !(f y)) = (fun y => xor true (f y)) := funext fun y => by cases f y <;> rfl
  rw [heq]; exact isAffine_xor (isAffine_const true) hf

lemma isAffine_and_const {n : Nat} (b : Bool) {f : (Fin n → Bool) → Bool} (hf : IsAffine f) :
    IsAffine (fun y => b && f y) := by
  cases b
  · simpa using isAffine_const false
  · simpa using hf

lemma isAffine_xorFin {n m : Nat} (fs : Fin m → (Fin n → Bool) → Bool)
    (hfs : ∀ i, IsAffine (fs i)) :
    IsAffine (fun y => xorFin (fun i => fs i y)) := by
  induction m with
  | zero => exact isAffine_const false
  | succ m ih =>
    have heq : (fun y => xorFin (fun i : Fin (m + 1) => fs i y)) =
        (fun y => xor (xorFin (fun i : Fin m => fs i.castSucc y)) (fs (Fin.last m) y)) :=
      funext (fun y => xorFin_succ (fun i => fs i y))
    rw [heq]
    exact isAffine_xor (ih (fun i => fs i.castSucc) (fun i => hfs i.castSucc)) (hfs (Fin.last m))

lemma isAffine_comp {m n : Nat} {f : (Fin m → Bool) → Bool} {g : (Fin n → Bool) → (Fin m → Bool)}
    (hf : IsAffine f) (hg : ∀ i, IsAffine (fun y => g y i)) :
    IsAffine (fun y => f (g y)) := by
  rcases hf with ⟨c, a, hfe⟩
  have heq : (fun y => f (g y)) = (fun y => xor c (xorFin (fun i => a i && g y i))) :=
    funext (fun y => hfe (g y))
  rw [heq]
  exact isAffine_xor (isAffine_const c) (isAffine_xorFin _ (fun i => isAffine_and_const (a i) (hg i)))

def pol {n : Nat} (f : (Fin n → Bool) → Bool) (a b : Fin n → Bool) : Bool :=
  xor (xor (f (fun i => xor (a i) (b i))) (f a)) (xor (f b) (f (fun _ => false)))

lemma pol_const {n : Nat} (c : Bool) (a b : Fin n → Bool) :
    pol (fun _ : Fin n → Bool => c) a b = false := by
  unfold pol; cases c <;> rfl

lemma pol_xor {n : Nat} (f g : (Fin n → Bool) → Bool) (a b : Fin n → Bool) :
    pol (fun y => xor (f y) (g y)) a b = xor (pol f a b) (pol g a b) := by
  unfold pol; dsimp only
  cases f (fun i => xor (a i) (b i)) <;> cases g (fun i => xor (a i) (b i)) <;>
    cases f a <;> cases g a <;> cases f b <;> cases g b <;>
    cases f (fun _ => false) <;> cases g (fun _ => false) <;> rfl

lemma pol_xorFin {n m : Nat} (fs : Fin m → (Fin n → Bool) → Bool) (a b : Fin n → Bool) :
    pol (fun y => xorFin (fun i => fs i y)) a b = xorFin (fun i => pol (fs i) a b) := by
  induction m with
  | zero => exact pol_const false a b
  | succ m ih =>
    have h1 : (fun y => xorFin (fun i : Fin (m + 1) => fs i y)) =
        (fun y => xor (xorFin (fun i : Fin m => fs i.castSucc y)) (fs (Fin.last m) y)) :=
      funext (fun y => xorFin_succ (fun i => fs i y))
    rw [h1, pol_xor, ih (fun i => fs i.castSucc), xorFin_succ]

lemma pol_and_const {n : Nat} (c : Bool) (f : (Fin n → Bool) → Bool) (a b : Fin n → Bool) :
    pol (fun y => c && f y) a b = (c && pol f a b) := by
  cases c
  · simpa using pol_const false a b
  · simp

lemma pol_affine {n : Nat} {f : (Fin n → Bool) → Bool} (hf : IsAffine f) (a b : Fin n → Bool) :
    pol f a b = false := by
  rcases hf with ⟨c, coeff, hfe⟩
  unfold pol
  rw [hfe, hfe, hfe, hfe, dot_xor_right, dot_zero_right]
  cases c <;> cases dot coeff a <;> cases dot coeff b <;> rfl

lemma pol_not_and_affine {n : Nat} (c1 c2 : Bool) (L1 L2 : (Fin n → Bool) → Bool)
    (h1 : ∀ a b, L1 (fun i => xor (a i) (b i)) = xor (L1 a) (L1 b))
    (h10 : L1 (fun _ => false) = false)
    (h2 : ∀ a b, L2 (fun i => xor (a i) (b i)) = xor (L2 a) (L2 b))
    (h20 : L2 (fun _ => false) = false) (a b : Fin n → Bool) :
    pol (fun y => !(xor c1 (L1 y)) && xor c2 (L2 y)) a b =
    xor (L1 a && L2 b) (L1 b && L2 a) := by
  unfold pol; dsimp only
  rw [h1 a b, h2 a b, h10, h20]
  cases c1 <;> cases c2 <;> cases L1 a <;> cases L1 b <;> cases L2 a <;> cases L2 b <;> rfl

lemma gate_eval_0 (op : GateOp) :
    ∃ c0 : Bool, op.eval [] = c0 := ⟨op.eval [], rfl⟩

lemma gate_eval_1 (op : GateOp) :
    ∃ (c0 c1 : Bool), ∀ b1 : Bool, op.eval [b1] = xor c0 (c1 && b1) :=
  ⟨op.eval [false], xor (op.eval [false]) (op.eval [true]), fun b1 => by
    cases b1 <;> cases op.eval [false] <;> cases op.eval [true] <;> rfl⟩

lemma gate_eval_2_linear (op : GateOp)
    (hlin : xor (xor (op.eval [false, false]) (op.eval [false, true]))
                (xor (op.eval [true, false]) (op.eval [true, true])) = false) :
    ∃ (c0 c1 c2 : Bool), ∀ b1 b2 : Bool,
      op.eval [b1, b2] = xor c0 (xor (c1 && b1) (c2 && b2)) :=
  ⟨op.eval [false, false],
   xor (op.eval [false, false]) (op.eval [true, false]),
   xor (op.eval [false, false]) (op.eval [false, true]),
   fun b1 b2 => by
     cases h00 : op.eval [false, false] <;> cases h01 : op.eval [false, true] <;>
       cases h10 : op.eval [true, false] <;> cases h11 : op.eval [true, true] <;>
       rw [h00, h01, h10, h11] at hlin <;> cases b1 <;> cases b2 <;> simp [h00, h01, h10, h11] at hlin ⊢⟩

lemma getD_append_lt {α : Type _} (l : List α) (x : α) (d : α) {i : Nat} (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_eq {α : Type _} (l : List α) (x : α) (d : α) :
    (l ++ [x]).getD l.length d = x := by
  simp [List.getD_eq_getElem?_getD]

lemma wires_append_gate (gs : List Gate) (g : Gate) (inp : List Bool) :
    Circuit.wires ⟨gs ++ [g], 0⟩ inp =
    Circuit.wires ⟨gs, 0⟩ inp ++ [g.op.eval (g.inputs.map (fun i => (Circuit.wires ⟨gs, 0⟩ inp).getD i false))] := by
  unfold Circuit.wires
  simp [List.foldl_append]

lemma wires_length (gs : List Gate) (inp : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ inp).length = inp.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    rw [wires_append_gate, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
    omega

lemma wires_output_irrel (gs : List Gate) (o : Nat) (inp : List Bool) :
    Circuit.wires ⟨gs, o⟩ inp = Circuit.wires ⟨gs, 0⟩ inp := rfl

lemma circuit_in_span {X : Type _} {a : Nat} (dataFn : Fin a → X → Bool)
    (gs : List Gate) (hval : valid a ⟨gs, 0⟩) :
    ∃ (G : Fin (gs.countP nonlinear) → X → Bool),
      ∀ (w : Nat), w < a + gs.length →
        ∃ (c0 : Bool) (α : Fin a → Bool) (β : Fin (gs.countP nonlinear) → Bool),
          ∀ x : X,
            (Circuit.wires ⟨gs, 0⟩ (List.ofFn (fun l => dataFn l x))).getD w false =
            xor c0 (xor (xorFin (fun l => α l && dataFn l x))
                        (xorFin (fun m => β m && G m x))) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun m => m.elim0, fun w hw => ?_⟩
    have hwa : w < a := by simpa using hw
    refine ⟨false, eVec ⟨w, hwa⟩, fun m => m.elim0, fun x => ?_⟩
    simp only [Circuit.wires, List.foldl_nil, List.countP_nil, xorFin_zero, Bool.xor_false, Bool.false_xor]
    have hget : (List.ofFn (fun l : Fin a => dataFn l x)).getD w false = dataFn ⟨w, hwa⟩ x := by
      simp [List.getD_eq_getElem?_getD, hwa]
    rw [hget]
    exact (dot_eVec_left ⟨w, hwa⟩ (fun l => dataFn l x)).symm
  | append_singleton gs g ih =>
    have hval_prev : valid a ⟨gs, 0⟩ := by
      refine ⟨fun j hj i hi => ?_, fun g' hg' => hval.2 g' (List.mem_append_left _ hg')⟩
      change j < gs.length at hj
      have h1 := hval.1 j (by simp only [List.length_append, List.length_singleton]; omega)
      have hga : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        unfold gateAt; exact getD_append_lt gs g _ hj
      rw [hga] at h1; exact h1 i hi
    have hrb_g : ∀ i ∈ g.inputs, i < a + gs.length := by
      have h1 := hval.1 gs.length (by simp)
      have hga : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
        unfold gateAt; exact getD_append_eq gs g _
      rw [hga] at h1; exact h1
    have hlen_g : g.inputs.length ≤ 2 := hval.2 g (List.mem_append_right _ List.mem_cons_self)
    rcases ih hval_prev with ⟨G, hG⟩
    have hcnt : (gs ++ [g]).countP nonlinear = gs.countP nonlinear + (if nonlinear g then 1 else 0) := by
      rw [List.countP_append]; cases h : nonlinear g <;> simp [List.countP, List.countP.go, h]
    cases hnl : nonlinear g
    ·
      have hM : (gs ++ [g]).countP nonlinear = gs.countP nonlinear := by rw [hcnt, hnl]; simp
      refine ⟨fun m => G ⟨m.val, by omega⟩, fun w hw => ?_⟩
      by_cases hlt : w < a + gs.length
      · rcases hG w hlt with ⟨c0, α, β, hwe⟩
        refine ⟨c0, α, fun m => β ⟨m.val, by omega⟩, fun x => ?_⟩
        rw [wires_append_gate, getD_append_lt _ _ _ (by rw [wires_length, List.length_ofFn]; exact hlt), hwe x]
        congr 1; congr 1
        exact xorFin_cast hM.symm _ _ (fun _ _ _ => rfl)
      · have hweq : w = a + gs.length := by simp only [List.length_append, List.length_singleton] at hw; omega
        subst hweq

        have hstep : ∃ (c0 : Bool) (α : Fin a → Bool) (β : Fin (gs.countP nonlinear) → Bool),
            ∀ x : X,
              g.op.eval (g.inputs.map (fun i => (Circuit.wires ⟨gs, 0⟩ (List.ofFn (fun l => dataFn l x))).getD i false)) =
              xor c0 (xor (xorFin (fun l => α l && dataFn l x)) (xorFin (fun m => β m && G m x))) := by
          match hinp : g.inputs with
          | [] =>
            exact ⟨g.op.eval [], fun _ => false, fun _ => false, fun x => by
              simp [xorFin_eq_false]⟩
          | [i1] =>
            have hi1 : i1 < a + gs.length := hrb_g i1 (by rw [hinp]; exact List.mem_cons_self)
            rcases hG i1 hi1 with ⟨c1, α1, β1, h1⟩
            rcases gate_eval_1 g.op with ⟨d0, d1, hd⟩
            refine ⟨xor d0 (d1 && c1), fun l => d1 && α1 l, fun m => d1 && β1 m, fun x => ?_⟩
            simp only [List.map_cons, List.map_nil, hd, h1 x]
            have ha1 : xorFin (fun l => (d1 && α1 l) && dataFn l x) = (d1 && xorFin (fun l => α1 l && dataFn l x)) := by
              rw [← xorFin_and_left]; apply xorFin_congr; intro l; exact Bool.and_assoc _ _ _
            have hb1 : xorFin (fun m => (d1 && β1 m) && G m x) = (d1 && xorFin (fun m => β1 m && G m x)) := by
              rw [← xorFin_and_left]; apply xorFin_congr; intro m; exact Bool.and_assoc _ _ _
            rw [ha1, hb1]
            cases d0 <;> cases d1 <;> cases c1 <;>
              cases xorFin (fun l => α1 l && dataFn l x) <;> cases xorFin (fun m => β1 m && G m x) <;> rfl
          | [i1, i2] =>
            have hi1 : i1 < a + gs.length := hrb_g i1 (by rw [hinp]; exact List.mem_cons_self)
            have hi2 : i2 < a + gs.length := hrb_g i2 (by rw [hinp]; exact List.mem_cons_of_mem _ List.mem_cons_self)
            rcases hG i1 hi1 with ⟨c1, α1, β1, h1⟩
            rcases hG i2 hi2 with ⟨c2, α2, β2, h2⟩
            have hlin : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                            (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              unfold nonlinear at hnl; rw [hinp] at hnl; simpa using hnl
            rcases gate_eval_2_linear g.op hlin with ⟨d0, d1, d2, hd⟩
            refine ⟨xor d0 (xor (d1 && c1) (d2 && c2)),
              fun l => xor (d1 && α1 l) (d2 && α2 l),
              fun m => xor (d1 && β1 m) (d2 && β2 m), fun x => ?_⟩
            simp only [List.map_cons, List.map_nil, hd, h1 x, h2 x]
            have ha1 : xorFin (fun l => xor (d1 && α1 l) (d2 && α2 l) && dataFn l x) =
                xor (d1 && xorFin (fun l => α1 l && dataFn l x)) (d2 && xorFin (fun l => α2 l && dataFn l x)) := by
              rw [← xorFin_and_left, ← xorFin_and_left, ← xorFin_xor]
              apply xorFin_congr; intro l
              cases d1 <;> cases d2 <;> cases α1 l <;> cases α2 l <;> cases dataFn l x <;> rfl
            have hb1 : xorFin (fun m => xor (d1 && β1 m) (d2 && β2 m) && G m x) =
                xor (d1 && xorFin (fun m => β1 m && G m x)) (d2 && xorFin (fun m => β2 m && G m x)) := by
              rw [← xorFin_and_left, ← xorFin_and_left, ← xorFin_xor]
              apply xorFin_congr; intro m
              cases d1 <;> cases d2 <;> cases β1 m <;> cases β2 m <;> cases G m x <;> rfl
            rw [ha1, hb1]
            cases d0 <;> cases d1 <;> cases d2 <;> cases c1 <;> cases c2 <;>
              cases xorFin (fun l => α1 l && dataFn l x) <;> cases xorFin (fun l => α2 l && dataFn l x) <;>
              cases xorFin (fun m => β1 m && G m x) <;> cases xorFin (fun m => β2 m && G m x) <;> rfl
          | _ :: _ :: _ :: _ => rw [hinp] at hlen_g; simp at hlen_g
        rcases hstep with ⟨c0, α, β, hst⟩
        refine ⟨c0, α, fun m => β ⟨m.val, by omega⟩, fun x => ?_⟩
        rw [wires_append_gate]
        have hlen : (Circuit.wires ⟨gs, 0⟩ (List.ofFn (fun l => dataFn l x))).length = a + gs.length := by
          rw [wires_length, List.length_ofFn]
        rw [← hlen, getD_append_eq, hst x]
        congr 1; congr 1
        exact xorFin_cast hM.symm _ _ (fun _ _ _ => rfl)
    ·
      have hM : (gs ++ [g]).countP nonlinear = gs.countP nonlinear + 1 := by rw [hcnt, hnl]; simp
      let newFn : X → Bool := fun x =>
        g.op.eval (g.inputs.map (fun i => (Circuit.wires ⟨gs, 0⟩ (List.ofFn (fun l => dataFn l x))).getD i false))
      let G' : Fin ((gs ++ [g]).countP nonlinear) → X → Bool := fun m =>
        if hm : m.val < gs.countP nonlinear then G ⟨m.val, hm⟩ else newFn
      refine ⟨G', fun w hw => ?_⟩
      by_cases hlt : w < a + gs.length
      · rcases hG w hlt with ⟨c0, α, β, hwe⟩
        refine ⟨c0, α, fun m => if hm : m.val < gs.countP nonlinear then β ⟨m.val, hm⟩ else false, fun x => ?_⟩
        rw [wires_append_gate, getD_append_lt _ _ _ (by rw [wires_length, List.length_ofFn]; exact hlt), hwe x]
        congr 1; congr 1
        have hcast := xorFin_cast hM (fun m => (if hm : m.val < gs.countP nonlinear then β ⟨m.val, hm⟩ else false) && G' m x)
          (fun m : Fin (gs.countP nonlinear + 1) =>
            (if hm : m.val < gs.countP nonlinear then β ⟨m.val, hm⟩ else false) &&
            (if hm : m.val < gs.countP nonlinear then G ⟨m.val, hm⟩ x else newFn x))
          (fun i h1 h2 => by dsimp only [G']; split_ifs <;> rfl)
        rw [hcast, xorFin_succ]
        have hlast : ¬((Fin.last (gs.countP nonlinear)).val < gs.countP nonlinear) := by simp [Fin.last]
        rw [dite_neg hlast, Bool.false_and, Bool.xor_false]
        apply xorFin_congr; intro m
        simp only [Fin.val_castSucc, dite_pos m.isLt]
      · have hweq : w = a + gs.length := by simp only [List.length_append, List.length_singleton] at hw; omega
        subst hweq
        let lastM : Fin ((gs ++ [g]).countP nonlinear) := ⟨gs.countP nonlinear, by omega⟩
        refine ⟨false, fun _ => false, eVec lastM, fun x => ?_⟩
        rw [wires_append_gate]
        have hlen : (Circuit.wires ⟨gs, 0⟩ (List.ofFn (fun l => dataFn l x))).length = a + gs.length := by
          rw [wires_length, List.length_ofFn]
        rw [← hlen, getD_append_eq]
        rw [xorFin_eq_false _ (fun _ => Bool.false_and _), Bool.false_xor, Bool.false_xor]
        rw [xorFin_single' lastM]
        · simp only [eVec, decide_true, Bool.true_and, G', lastM]
          rw [dite_neg (by omega)]
        · intro m hm; simp [eVec, hm]

lemma per_key_card_lb {k n a : Nat} {read : Fin a → (Fin k → Bool) → Bool}
    (key : Fin a → Fin n)
    (C : Circuit) (tap : Fin n → Fin k → Nat)
    (hval : valid a C) (htap : ∀ j i, tap j i < a + C.gates.length)
    (hcomp : ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
      (C.wires (List.ofFn (fun l : Fin a => read l (x (key l))))).getD (tap j i) false = x j i)
    (S : Fin n → Finset (Fin k → Bool))
    (hS : ∀ (j : Fin n) (w : Fin k → Bool),
      (∃ (γ : Fin a → Bool) (c : Bool),
        ∀ (y : Fin k → Bool),
          dot w y = xor c (xorFin (fun l : Fin a => (decide (key l = j) && γ l) && read l y))) →
      w ∈ S j) :
    2 ^ (n * k) ≤ 2 ^ (C.gates.countP nonlinear) * ∏ j : Fin n, (S j).card := by
  let X := Fin n → Fin k → Bool
  let dataFn : Fin a → X → Bool := fun l x => read l (x (key l))
  have hval0 : valid a ⟨C.gates, 0⟩ := hval
  rcases circuit_in_span dataFn C.gates hval0 with ⟨G, hG⟩
  let M := C.gates.countP nonlinear
  have hex : ∀ (j : Fin n) (i : Fin k),
      ∃ (p : Bool × (Fin a → Bool) × (Fin M → Bool)),
        ∀ x : X, x j i = xor p.1 (xor (xorFin (fun l => p.2.1 l && dataFn l x))
                                      (xorFin (fun m => p.2.2 m && G m x))) := by
    intro j i
    rcases hG (tap j i) (htap j i) with ⟨c0, α, β, h⟩
    refine ⟨⟨c0, α, β⟩, fun x => ?_⟩
    rw [← hcomp x j i, wires_output_irrel C.gates C.output]
    exact h x
  choose P hP using hex
  let c0 : Fin n → Fin k → Bool := fun j i => (P j i).1
  let α : Fin n → Fin k → Fin a → Bool := fun j i => (P j i).2.1
  let β : Fin n → Fin k → Fin M → Bool := fun j i => (P j i).2.2

  let f : X → (Fin M → Bool) := fun v m => xorFin (fun j => xorFin (fun i => v j i && β j i m))
  let Vker : Finset X := Finset.univ.filter (fun v => f v = fun _ => false)
  have hf_add : ∀ u v : X, f (fun j i => xor (u j i) (v j i)) = fun m => xor (f u m) (f v m) := by
    intro u v; funext m; unfold f
    rw [← xorFin_xor]; apply xorFin_congr; intro j
    rw [← xorFin_xor]; apply xorFin_congr; intro i; dsimp only
    cases u j i <;> cases v j i <;> cases β j i m <;> rfl

  have hcard_X : (Finset.univ : Finset X).card = 2 ^ (n * k) := by
    simp [X, Fintype.card_fin, Fintype.card_bool, ← pow_mul, Nat.mul_comm]
  have hcard_M : (Finset.univ : Finset (Fin M → Bool)).card = 2 ^ M := by
    simp [Fintype.card_fin, Fintype.card_bool]
  have hfib_le : ∀ y : Fin M → Bool,
      (Finset.univ.filter (fun v : X => f v = y)).card ≤ Vker.card := by
    intro y
    by_cases hne : (Finset.univ.filter (fun v : X => f v = y)).Nonempty
    · rcases hne with ⟨v0, hv0⟩
      have hv0_eq : f v0 = y := (Finset.mem_filter.mp hv0).2
      apply Finset.card_le_card_of_injOn (fun v j i => xor (v j i) (v0 j i))
      · intro v hv
        have hv_eq : f v = y := (Finset.mem_filter.mp hv).2
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hf_add, hv_eq, hv0_eq]; funext m; exact Bool.xor_self (y m)
      · intro v1 _ v2 _ heq
        funext j i
        have hji := congrFun (congrFun heq j) i
        dsimp only at hji
        cases h1 : v1 j i <;> cases h2 : v2 j i <;> cases h0 : v0 j i <;>
          rw [h1, h2, h0] at hji <;> simp at hji ⊢
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]; exact Nat.zero_le _
  have hker_lb : 2 ^ (n * k) ≤ 2 ^ M * Vker.card := by
    rw [← hcard_X, ← hcard_M]
    have hsum : (Finset.univ : Finset X).card =
        ∑ y ∈ (Finset.univ : Finset (Fin M → Bool)), (Finset.univ.filter (fun v : X => f v = y)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    rw [hsum]
    calc ∑ y ∈ (Finset.univ : Finset (Fin M → Bool)), (Finset.univ.filter (fun v : X => f v = y)).card
        ≤ ∑ _y ∈ (Finset.univ : Finset (Fin M → Bool)), Vker.card := Finset.sum_le_sum (fun y _ => hfib_le y)
      _ = (Finset.univ : Finset (Fin M → Bool)).card * Vker.card := by rw [Finset.sum_const, smul_eq_mul]

  have hsub : Vker ⊆ Fintype.piFinset S := by
    intro v hv
    have hv0 : f v = fun _ => false := (Finset.mem_filter.mp hv).2
    rw [Fintype.mem_piFinset]
    intro j0
    apply hS j0 (v j0)
    let γ : Fin a → Bool := fun l => xorFin (fun j => xorFin (fun i => v j i && α j i l))

    let cv : Bool := xorFin (fun j => xorFin (fun i => v j i && c0 j i))
    have hmain : ∀ x : X,
        xorFin (fun j => dot (v j) (x j)) = xor cv (xorFin (fun l => γ l && dataFn l x)) := by
      intro x
      have h1 : xorFin (fun j => dot (v j) (x j)) =
          xorFin (fun j => xorFin (fun i => v j i &&
            xor (c0 j i) (xor (xorFin (fun l => α j i l && dataFn l x))
                              (xorFin (fun m => β j i m && G m x))))) := by
        apply xorFin_congr; intro j; unfold dot; apply xorFin_congr; intro i
        rw [← hP j i x]
      have h2 : ∀ (j : Fin n),
          xorFin (fun i => v j i &&
            xor (c0 j i) (xor (xorFin (fun l => α j i l && dataFn l x))
                              (xorFin (fun m => β j i m && G m x)))) =
          xor (xorFin (fun i => v j i && c0 j i))
              (xor (xorFin (fun l => xorFin (fun i => v j i && α j i l) && dataFn l x))
                   (xorFin (fun m => xorFin (fun i => v j i && β j i m) && G m x))) := by
        intro j
        have hdist : ∀ i, (v j i && xor (c0 j i) (xor (xorFin (fun l => α j i l && dataFn l x))
                                                      (xorFin (fun m => β j i m && G m x)))) =
            xor (v j i && c0 j i)
                (xor (v j i && xorFin (fun l => α j i l && dataFn l x))
                     (v j i && xorFin (fun m => β j i m && G m x))) := fun i => by
          cases v j i <;> simp
        rw [xorFin_congr _ _ hdist, xorFin_xor, xorFin_xor]
        congr 1; congr 1
        · rw [xorFin_congr _ _ (fun i => (xorFin_and_left (v j i) _).symm), xorFin_swap]
          apply xorFin_congr; intro l
          rw [← xorFin_and_right]; apply xorFin_congr; intro i; exact (Bool.and_assoc _ _ _).symm
        · rw [xorFin_congr _ _ (fun i => (xorFin_and_left (v j i) _).symm), xorFin_swap]
          apply xorFin_congr; intro m
          rw [← xorFin_and_right]; apply xorFin_congr; intro i; exact (Bool.and_assoc _ _ _).symm
      rw [h1, xorFin_congr _ _ h2, xorFin_xor, xorFin_xor]
      have hG0 : xorFin (fun j => xorFin (fun m => xorFin (fun i => v j i && β j i m) && G m x)) = false := by
        rw [xorFin_swap]
        apply xorFin_eq_false; intro m
        rw [xorFin_and_right]
        have hm := congrFun hv0 m
        dsimp only [f] at hm
        rw [hm, Bool.false_and]
      have hA : xorFin (fun j => xorFin (fun l => xorFin (fun i => v j i && α j i l) && dataFn l x)) =
          xorFin (fun l => γ l && dataFn l x) := by
        rw [xorFin_swap]; apply xorFin_congr; intro l; rw [xorFin_and_right]
      rw [hG0, Bool.xor_false, hA]

    let cOther : Bool := xorFin (fun l => (!(decide (key l = j0)) && γ l) && read l (fun _ => false))
    refine ⟨γ, xor cv cOther, fun y => ?_⟩
    let x : X := fun j => if j = j0 then y else (fun _ => false)
    have hx := hmain x
    have hlhs : xorFin (fun j => dot (v j) (x j)) = dot (v j0) y := by
      rw [xorFin_single' j0]
      · dsimp only [x]; rw [ite_pos rfl]
      · intro j hj; dsimp only [x]; rw [ite_neg hj, dot_zero_right]
    have hrhs : xorFin (fun l => γ l && dataFn l x) =
        xor (xorFin (fun l => (decide (key l = j0) && γ l) && read l y)) cOther := by
      rw [xorFin_split_pred (fun l => decide (key l = j0))]
      congr 1
      · apply xorFin_congr; intro l
        by_cases hkj : key l = j0
        · rw [decide_eq_true hkj, Bool.true_and, Bool.true_and]
          dsimp only [dataFn, x]; rw [ite_pos hkj]
        · rw [decide_eq_false hkj, Bool.false_and, Bool.false_and, Bool.false_and]
      · apply xorFin_congr; intro l
        by_cases hkj : key l = j0
        · rw [decide_eq_true hkj]; simp
        · rw [decide_eq_false hkj, Bool.not_false, Bool.true_and, Bool.true_and]
          dsimp only [dataFn, x]; rw [ite_neg hkj]
    rw [hlhs, hrhs] at hx
    rw [hx]
    cases cv <;> cases cOther <;> cases xorFin (fun l => (decide (key l = j0) && γ l) && read l y) <;> rfl
  have hker_ub : Vker.card ≤ ∏ j : Fin n, (S j).card := by
    calc Vker.card ≤ (Fintype.piFinset S).card := Finset.card_le_card hsub
      _ = ∏ j : Fin n, (S j).card := Fintype.card_piFinset S
  exact le_trans hker_lb (Nat.mul_le_mul_left _ hker_ub)

def ix {k : Nat} (hk : 0 < k) (i : Nat) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩

def add {k : Nat} (u v : Fin k → Bool) (i : Fin k) : Bool := xor (u i) (v i)

def rot {k : Nat} (hk : 0 < k) (s : Nat) (w : Fin k → Bool) (i : Fin k) : Bool :=
  w (ix hk (i.val + k - s % k))

def mix {k : Nat} (hk : 0 < k) (d : Nat) (w : Fin k → Bool) (i : Fin k) : Bool :=
  xor (w (ix hk (i.val + k - d % k))) (xor (w i) (w (ix hk (i.val + d))))

def readBit {k : Nat} (hk : 0 < k) (col : Bool) (u x : Fin k → Bool) (i : Fin k) : Bool :=
  let d := if col then 2 else 1
  let R := mix hk d (add u (rot hk (if col then 3 else 1) x))
  xor (rot hk (if col then 4 else 0) x i)
    (xor (R i) (!(R (ix hk (i.val + 1))) && R (ix hk (i.val + 2))))

def R0 {k : Nat} (hk : 0 < k) (col : Bool) (x : Fin k → Bool) : Fin k → Bool :=
  mix hk (if col then 2 else 1) (rot hk (if col then 3 else 1) x)

def QBit {k : Nat} (hk : 0 < k) (col : Bool) (i : Fin k) (a b : Fin k → Bool) : Bool :=
  xor (R0 hk col a (ix hk (i.val + 1)) && R0 hk col b (ix hk (i.val + 2)))
      (R0 hk col b (ix hk (i.val + 1)) && R0 hk col a (ix hk (i.val + 2)))

def R0Vec {k : Nat} (hk : 0 < k) (col : Bool) (j : Fin k) : Fin k → Bool :=
  fun p => R0 hk col (eVec p) j

lemma rot_add {k : Nat} (hk : 0 < k) (s : Nat) (u v : Fin k → Bool) :
    rot hk s (add u v) = add (rot hk s u) (rot hk s v) := by
  funext i; rfl

lemma rot_zero {k : Nat} (hk : 0 < k) (s : Nat) :
    rot hk s (fun _ => false) = fun _ => false := by
  funext i; rfl

lemma mix_add {k : Nat} (hk : 0 < k) (d : Nat) (u v : Fin k → Bool) :
    mix hk d (add u v) = add (mix hk d u) (mix hk d v) := by
  funext i; unfold mix add; dsimp only
  cases u (ix hk (i.val + k - d % k)) <;> cases v (ix hk (i.val + k - d % k)) <;>
    cases u i <;> cases v i <;> cases u (ix hk (i.val + d)) <;> cases v (ix hk (i.val + d)) <;> rfl

lemma mix_zero {k : Nat} (hk : 0 < k) (d : Nat) :
    mix hk d (fun _ => false) = fun _ => false := by
  funext i; rfl

lemma R0_xor {k : Nat} (hk : 0 < k) (col : Bool) (a b : Fin k → Bool) (j : Fin k) :
    R0 hk col (fun p => xor (a p) (b p)) j = xor (R0 hk col a j) (R0 hk col b j) := by
  unfold R0
  change mix hk (if col then 2 else 1) (rot hk (if col then 3 else 1) (add a b)) j = _
  rw [rot_add, mix_add]; rfl

lemma R0_zero {k : Nat} (hk : 0 < k) (col : Bool) (j : Fin k) :
    R0 hk col (fun _ => false) j = false := by
  unfold R0; rw [rot_zero, mix_zero]

lemma vec_eq_xorFin_eVec {k : Nat} (x : Fin k → Bool) :
    x = fun q => xorFin (fun p : Fin k => x p && eVec p q) := by
  funext q
  rw [xorFin_single' q]
  · simp [eVec]
  · intro p hp; simp [eVec, Ne.symm hp]

lemma R0_eq_dot {k : Nat} (hk : 0 < k) (col : Bool) (x : Fin k → Bool) (j : Fin k) :
    R0 hk col x j = dot (R0Vec hk col j) x := by
  have hlin : ∀ (m : Nat) (f : Fin m → Fin k → Bool),
      R0 hk col (fun q => xorFin (fun p : Fin m => f p q)) j = xorFin (fun p : Fin m => R0 hk col (f p) j) := by
    intro m; induction m with
    | zero => intro f; exact R0_zero hk col j
    | succ m ih =>
      intro f
      have h1 : (fun q => xorFin (fun p : Fin (m + 1) => f p q)) =
          (fun q => xor (xorFin (fun p : Fin m => f p.castSucc q)) (f (Fin.last m) q)) :=
        funext (fun q => xorFin_succ (fun p => f p q))
      rw [h1, R0_xor, ih (fun p => f p.castSucc), xorFin_succ]
  conv_lhs => rw [vec_eq_xorFin_eVec x]
  rw [hlin]
  unfold dot R0Vec
  apply xorFin_congr; intro p
  cases hx : x p
  · simp only [Bool.false_and, Bool.and_false]; exact R0_zero hk col j
  · simp only [Bool.true_and, Bool.and_true]

lemma isAffine_rot {k : Nat} (hk : 0 < k) (s : Nat) (i : Fin k) :
    IsAffine (fun x : Fin k → Bool => rot hk s x i) :=
  isAffine_coord (ix hk (i.val + k - s % k))

lemma isAffine_R0 {k : Nat} (hk : 0 < k) (col : Bool) (j : Fin k) :
    IsAffine (fun x : Fin k → Bool => R0 hk col x j) :=
  ⟨false, R0Vec hk col j, fun x => by dsimp only; rw [Bool.false_xor, R0_eq_dot]⟩

lemma pol_readBit {k : Nat} (hk : 0 < k) (col : Bool) (u : Fin k → Bool) (i : Fin k)
    (a b : Fin k → Bool) :
    pol (fun x => readBit hk col u x i) a b = QBit hk col i a b := by
  unfold readBit
  let d := if col then 2 else 1
  let U := mix hk d u
  have hR : ∀ x, mix hk d (add u (rot hk (if col then 3 else 1) x)) = add U (R0 hk col x) :=
    fun x => mix_add hk d u _
  have heq : (fun x => xor (rot hk (if col then 4 else 0) x i)
      (xor (mix hk d (add u (rot hk (if col then 3 else 1) x)) i)
           (!(mix hk d (add u (rot hk (if col then 3 else 1) x)) (ix hk (i.val + 1))) &&
            mix hk d (add u (rot hk (if col then 3 else 1) x)) (ix hk (i.val + 2))))) =
      (fun x => xor (xor (rot hk (if col then 4 else 0) x i) (xor (U i) (R0 hk col x i)))
                    (!(xor (U (ix hk (i.val + 1))) (R0 hk col x (ix hk (i.val + 1)))) &&
                     xor (U (ix hk (i.val + 2))) (R0 hk col x (ix hk (i.val + 2))))) := by
    funext x; rw [hR x]; unfold add
    cases rot hk (if col then 4 else 0) x i <;> cases U i <;> cases R0 hk col x i <;>
      cases (!(xor (U (ix hk (i.val + 1))) (R0 hk col x (ix hk (i.val + 1)))) &&
             xor (U (ix hk (i.val + 2))) (R0 hk col x (ix hk (i.val + 2)))) <;> rfl
  change pol (fun x => xor (rot hk (if col then 4 else 0) x i)
      (xor (mix hk d (add u (rot hk (if col then 3 else 1) x)) i)
           (!(mix hk d (add u (rot hk (if col then 3 else 1) x)) (ix hk (i.val + 1))) &&
            mix hk d (add u (rot hk (if col then 3 else 1) x)) (ix hk (i.val + 2))))) a b = _
  rw [heq, pol_xor, pol_affine (isAffine_xor (isAffine_rot hk _ i) (isAffine_xor (isAffine_const _) (isAffine_R0 hk col i))), Bool.false_xor]
  exact pol_not_and_affine (U (ix hk (i.val + 1))) (U (ix hk (i.val + 2)))
    (fun x => R0 hk col x (ix hk (i.val + 1))) (fun x => R0 hk col x (ix hk (i.val + 2)))
    (fun x y => R0_xor hk col x y _) (R0_zero hk col _)
    (fun x y => R0_xor hk col x y _) (R0_zero hk col _) a b

lemma readBit_diff {k : Nat} (hk : 0 < k) (col : Bool) (u1 u2 x : Fin k → Bool) (i : Fin k) :
    let d := if col then 2 else 1
    let Δ := mix hk d (add u1 u2)
    xor (readBit hk col u1 x i) (readBit hk col u2 x i) =
    xor (xor (readBit hk col u1 (fun _ => false) i) (readBit hk col u2 (fun _ => false) i))
        (xor (Δ (ix hk (i.val + 1)) && R0 hk col x (ix hk (i.val + 2)))
             (Δ (ix hk (i.val + 2)) && R0 hk col x (ix hk (i.val + 1)))) := by
  intro d Δ
  unfold readBit
  have h1 : mix hk d (add u1 (rot hk (if col then 3 else 1) x)) = add (mix hk d u1) (R0 hk col x) :=
    mix_add hk d u1 _
  have h2 : mix hk d (add u2 (rot hk (if col then 3 else 1) x)) = add (mix hk d u2) (R0 hk col x) :=
    mix_add hk d u2 _
  have h10 : mix hk d (add u1 (rot hk (if col then 3 else 1) (fun _ => false))) = mix hk d u1 := by
    rw [rot_zero]; congr 1; funext p; exact Bool.xor_false (u1 p)
  have h20 : mix hk d (add u2 (rot hk (if col then 3 else 1) (fun _ => false))) = mix hk d u2 := by
    rw [rot_zero]; congr 1; funext p; exact Bool.xor_false (u2 p)
  have hΔ : Δ = add (mix hk d u1) (mix hk d u2) := mix_add hk d u1 u2
  dsimp only
  change xor (xor (rot hk (if col then 4 else 0) x i)
      (xor (mix hk d (add u1 (rot hk (if col then 3 else 1) x)) i)
           (!(mix hk d (add u1 (rot hk (if col then 3 else 1) x)) (ix hk (i.val + 1))) &&
            mix hk d (add u1 (rot hk (if col then 3 else 1) x)) (ix hk (i.val + 2)))))
    (xor (rot hk (if col then 4 else 0) x i)
      (xor (mix hk d (add u2 (rot hk (if col then 3 else 1) x)) i)
           (!(mix hk d (add u2 (rot hk (if col then 3 else 1) x)) (ix hk (i.val + 1))) &&
            mix hk d (add u2 (rot hk (if col then 3 else 1) x)) (ix hk (i.val + 2))))) = _
  rw [h1, h2, h10, h20, hΔ, rot_zero]
  unfold add
  cases rot hk (if col then 4 else 0) x i <;>
    cases mix hk d u1 i <;> cases mix hk d u2 i <;> cases R0 hk col x i <;>
    cases mix hk d u1 (ix hk (i.val + 1)) <;> cases mix hk d u2 (ix hk (i.val + 1)) <;>
    cases mix hk d u1 (ix hk (i.val + 2)) <;> cases mix hk d u2 (ix hk (i.val + 2)) <;>
    cases R0 hk col x (ix hk (i.val + 1)) <;> cases R0 hk col x (ix hk (i.val + 2)) <;> rfl

lemma readBit_diff_zero {k : Nat} (hk : 0 < k) (col : Bool) (u x : Fin k → Bool) (i : Fin k) :
    let d := if col then 2 else 1
    let U := mix hk d u
    xor (readBit hk col (fun _ => false) x i) (readBit hk col u x i) =
    xor (readBit hk col u (fun _ => false) i)
        (xor (U (ix hk (i.val + 1)) && R0 hk col x (ix hk (i.val + 2)))
             (U (ix hk (i.val + 2)) && R0 hk col x (ix hk (i.val + 1)))) := by
  intro d U
  have h := readBit_diff hk col (fun _ => false) u x i
  have h00 : readBit hk col (fun _ => false) (fun _ => false) i = false := by
    unfold readBit; dsimp only
    have ha : add (fun _ : Fin k => false) (rot hk (if col then 3 else 1) (fun _ => false)) = fun _ => false := by
      funext p; unfold add rot; rfl
    rw [ha, mix_zero, rot_zero]; rfl
  have ha0 : add (fun _ : Fin k => false) u = u := by funext p; exact Bool.false_xor (u p)
  dsimp only at h
  rw [h00, Bool.false_xor, ha0] at h
  exact h

def resSum {k : Nat} (w : Fin k → Bool) (c : Nat) : Bool :=
  xorFin (fun i : Fin k => decide (i.val % 3 = c) && w i)

lemma resSum_xor {k : Nat} (u v : Fin k → Bool) (c : Nat) :
    resSum (fun i => xor (u i) (v i)) c = xor (resSum u c) (resSum v c) := by
  unfold resSum; rw [← xorFin_xor]; apply xorFin_congr; intro i; dsimp only
  cases decide (i.val % 3 = c) <;> cases u i <;> cases v i <;> rfl

lemma resSum_zero {k : Nat} (c : Nat) : resSum (fun _ : Fin k => false) c = false := by
  unfold resSum; exact xorFin_eq_false _ (fun _ => Bool.and_false _)

lemma resSum_and_const {k : Nat} (b : Bool) (w : Fin k → Bool) (c : Nat) :
    resSum (fun i => b && w i) c = (b && resSum w c) := by
  cases b
  · simpa using resSum_zero (k := k) c
  · simp [resSum]

lemma resSum_xorFin {k m : Nat} (fs : Fin m → Fin k → Bool) (c : Nat) :
    resSum (fun i => xorFin (fun t => fs t i)) c = xorFin (fun t => resSum (fs t) c) := by
  induction m with
  | zero => exact resSum_zero c
  | succ m ih =>
    have h1 : (fun i => xorFin (fun t : Fin (m + 1) => fs t i)) =
        (fun i => xor (xorFin (fun t : Fin m => fs t.castSucc i)) (fs (Fin.last m) i)) :=
      funext (fun i => xorFin_succ (fun t => fs t i))
    rw [h1, resSum_xor, ih (fun t => fs t.castSucc), xorFin_succ]

lemma mod_sub_eq {k x c : Nat} (hx : x < k) (hc : c < k) :
    (x + k - c) % k = if c ≤ x then x - c else x + k - c := by
  split_ifs with h
  · have heq : x + k - c = (x - c) + k := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

lemma mod_add_eq {k x c : Nat} (hx : x < k) (hc : c < k) :
    (x + c) % k = if x + c < k then x + c else x + c - k := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · calc (x + c) % k = ((x + c - k) + k) % k := congrArg (· % k) (by omega)
      _ = (x + c - k) % k := Nat.add_mod_right _ _
      _ = x + c - k := Nat.mod_eq_of_lt (by omega)

lemma mod_add_mod_eq {k a b : Nat} : (a % k + b) % k = (a + b) % k := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma shift_mod_eq {k i j a b : Nat} (hi : i < k) (hj : j < k) (ha : a < k) (hb : b < k) :
    (i + a) % k = (j + b) % k ↔
    (i + a = j + b ∨ i + a + k = j + b ∨ i + a = j + b + k) := by
  rw [mod_add_eq hi ha, mod_add_eq hj hb]; split_ifs <;> omega

lemma shift_mod_sub_eq {k i j a c : Nat} (hi : i < k) (hj : j < k) (ha : a < k) (hc : c < k) :
    (i + a) % k = (j + k - c) % k ↔
    (i + a + c = j ∨ i + a + c = j + k ∨ i + a + c = j + 2 * k) := by
  rw [mod_add_eq hi ha, mod_sub_eq hj hc]; split_ifs <;> omega

lemma resSum_R0Vec_eq {k : Nat} (hk : 0 < k) (h3 : 3 ∣ k) (hk5 : 5 ≤ k)
    (col : Bool) (j : Fin k) (c : Nat) (hc : c < 3) :
    resSum (R0Vec hk col j) c = true := by
  rcases h3 with ⟨r, hr⟩
  have hr2 : 2 ≤ r := by omega
  have hsup : ∃ (a0 a1 a2 : Fin k),
      a0 ≠ a1 ∧ a0 ≠ a2 ∧ a1 ≠ a2 ∧
      (a0.val % 3 = 0 ∧ a1.val % 3 = 1 ∧ a2.val % 3 = 2 ∨
       a0.val % 3 = 1 ∧ a1.val % 3 = 2 ∧ a2.val % 3 = 0 ∨
       a0.val % 3 = 2 ∧ a1.val % 3 = 0 ∧ a2.val % 3 = 1) ∧
      ∀ p : Fin k, R0Vec hk col j p = xor (decide (p = a0)) (xor (decide (p = a1)) (decide (p = a2))) := by
    cases col
    · let a0 := ix hk (j.val + k - 2)
      let a1 := ix hk (j.val + k - 1)
      let a2 := j
      have ha0 : a0.val = if 2 ≤ j.val then j.val - 2 else j.val + k - 2 := mod_sub_eq j.isLt (by omega)
      have ha1 : a1.val = if 1 ≤ j.val then j.val - 1 else j.val + k - 1 := mod_sub_eq j.isLt (by omega)
      refine ⟨a0, a1, a2, ?_, ?_, ?_, ?_, ?_⟩
      · intro h; have hv := congrArg Fin.val h; rw [ha0, ha1] at hv; split_ifs at hv <;> omega
      · intro h; have hv := congrArg Fin.val h; rw [ha0] at hv; split_ifs at hv <;> omega
      · intro h; have hv := congrArg Fin.val h; rw [ha1] at hv; split_ifs at hv <;> omega
      · rw [ha0, ha1]; split_ifs <;> omega
      · intro p; unfold R0Vec R0 mix rot eVec ix; simp only [Bool.false_eq_true, ite_false]
        have h1 : (⟨((j.val + k - 1 % k) % k + k - 1 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = a0 :=
          Fin.ext (by
            dsimp only; rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_sub_eq j.isLt (by omega), ha0]
            split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega)
        have h2 : (⟨(j.val + k - 1 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = a1 :=
          Fin.ext (by dsimp only; rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_sub_eq j.isLt (by omega), ha1])
        have h3' : (⟨((j.val + 1) % k + k - 1 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = a2 :=
          Fin.ext (by
            dsimp only; rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_add_eq j.isLt (by omega)]
            split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega)
        rw [h1, h2, h3']
        simp only [eq_comm]
    · let a0 := ix hk (j.val + k - 5)
      let a1 := ix hk (j.val + k - 1)
      let a2 := ix hk (j.val + k - 3)
      have ha0 : a0.val = if 5 ≤ j.val then j.val - 5 else j.val + k - 5 := mod_sub_eq j.isLt (by omega)
      have ha1 : a1.val = if 1 ≤ j.val then j.val - 1 else j.val + k - 1 := mod_sub_eq j.isLt (by omega)
      have ha2 : a2.val = if 3 ≤ j.val then j.val - 3 else j.val + k - 3 := mod_sub_eq j.isLt (by omega)
      refine ⟨a0, a1, a2, ?_, ?_, ?_, ?_, ?_⟩
      · intro h; have hv := congrArg Fin.val h; rw [ha0, ha1] at hv; split_ifs at hv <;> omega
      · intro h; have hv := congrArg Fin.val h; rw [ha0, ha2] at hv; split_ifs at hv <;> omega
      · intro h; have hv := congrArg Fin.val h; rw [ha1, ha2] at hv; split_ifs at hv <;> omega
      · rw [ha0, ha1, ha2]; split_ifs <;> omega
      · intro p; unfold R0Vec R0 mix rot eVec ix; simp only [ite_true]
        have h1 : (⟨((j.val + k - 2 % k) % k + k - 3 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = a0 :=
          Fin.ext (by
            dsimp only; rw [Nat.mod_eq_of_lt (by omega : 2 < k), Nat.mod_eq_of_lt (by omega : 3 < k),
              mod_sub_eq j.isLt (by omega), ha0]
            split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega)
        have h2 : (⟨(j.val + k - 3 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = a2 :=
          Fin.ext (by dsimp only; rw [Nat.mod_eq_of_lt (by omega : 3 < k), mod_sub_eq j.isLt (by omega), ha2])
        have h3' : (⟨((j.val + 2) % k + k - 3 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = a1 :=
          Fin.ext (by
            dsimp only; rw [Nat.mod_eq_of_lt (by omega : 3 < k), mod_add_eq j.isLt (by omega), ha1]
            split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega)
        rw [h1, h2, h3']
        simp only [eq_comm]
        cases decide (p = a0) <;> cases decide (p = a1) <;> cases decide (p = a2) <;> rfl
  rcases hsup with ⟨a0, a1, a2, h01, h02, h12, hmods, hvec⟩
  unfold resSum
  have heq : (fun p : Fin k => decide (p.val % 3 = c) && R0Vec hk col j p) =
      (fun p : Fin k => xor (decide (p.val % 3 = c) && decide (p = a0))
                        (xor (decide (p.val % 3 = c) && decide (p = a1))
                             (decide (p.val % 3 = c) && decide (p = a2)))) := by
    funext p; rw [hvec p]
    cases decide (p.val % 3 = c) <;> cases decide (p = a0) <;> cases decide (p = a1) <;> cases decide (p = a2) <;> rfl
  rw [heq, xorFin_xor, xorFin_xor]
  have hs : ∀ a : Fin k, xorFin (fun p : Fin k => decide (p.val % 3 = c) && decide (p = a)) = decide (a.val % 3 = c) := by
    intro a; rw [xorFin_single' a]; · simp
    · intro p hp; simp [hp]
  rw [hs a0, hs a1, hs a2]
  rcases hmods with ⟨m0, m1, m2⟩ | ⟨m0, m1, m2⟩ | ⟨m0, m1, m2⟩ <;>
    rw [m0, m1, m2] <;> (match c, hc with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl)

lemma resSum_subspace_card {k : Nat} (h3 : 3 ∣ k) (hk6 : 6 ≤ k) :
    (Finset.univ.filter (fun w : Fin k → Bool => resSum w 0 = resSum w 1 ∧ resSum w 1 = resSum w 2)).card ≤
    2 ^ (k - 2) := by

  let proj : (Fin k → Bool) → (Fin (k - 2) → Bool) := fun w i => w ⟨i.val + 1, by omega⟩
  have hinj : Set.InjOn proj (Finset.univ.filter (fun w : Fin k → Bool => resSum w 0 = resSum w 1 ∧ resSum w 1 = resSum w 2)) := by
    intro u hu v hv hproj
    have hu' := (Finset.mem_filter.mp hu).2
    have hv' := (Finset.mem_filter.mp hv).2
    have hmid : ∀ i : Fin k, 1 ≤ i.val → i.val < k - 1 → u i = v i := fun i h1 h2 => by
      have hp := congrFun hproj ⟨i.val - 1, by omega⟩
      dsimp only [proj] at hp
      have heq : (⟨i.val - 1 + 1, by omega⟩ : Fin k) = i := Fin.ext (by dsimp only; omega)
      rw [heq] at hp; exact hp
    have hd_mid : ∀ i : Fin k, 1 ≤ i.val → i.val < k - 1 → xor (u i) (v i) = false := fun i h1 h2 => by
      rw [hmid i h1 h2]; exact Bool.xor_self _
    have hres_diff : ∀ c, resSum (fun i => xor (u i) (v i)) c = xor (resSum u c) (resSum v c) :=
      fun c => resSum_xor u v c
    have hres1 : resSum (fun i => xor (u i) (v i)) 1 = false := by
      unfold resSum; apply xorFin_eq_false; intro i
      by_cases h0 : i.val = 0
      · rw [h0]; rfl
      · by_cases hk1 : i.val = k - 1
        · have hm : i.val % 3 ≠ 1 := by omega
          rw [decide_eq_false hm, Bool.false_and]
        · dsimp only; rw [hd_mid i (by omega) (by omega), Bool.and_false]
    have hres0 : resSum (fun i => xor (u i) (v i)) 0 = false := by
      rw [hres_diff, hu'.1, hv'.1, ← hres_diff, hres1]
    have hres2 : resSum (fun i => xor (u i) (v i)) 2 = false := by
      rw [hres_diff, ← hu'.2, ← hv'.2, ← hres_diff, hres1]
    have hu0 : u ⟨0, by omega⟩ = v ⟨0, by omega⟩ := by
      have h0 : resSum (fun i => xor (u i) (v i)) 0 = xor (u ⟨0, by omega⟩) (v ⟨0, by omega⟩) := by
        unfold resSum
        rw [xorFin_single' ⟨0, by omega⟩]
        · simp
        · intro i hi
          have hne0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
          by_cases hk1 : i.val = k - 1
          · have hm : i.val % 3 ≠ 0 := by omega
            rw [decide_eq_false hm, Bool.false_and]
          · dsimp only; rw [hd_mid i (by omega) (by omega), Bool.and_false]
      rw [h0] at hres0
      cases h1 : u ⟨0, by omega⟩ <;> cases h2 : v ⟨0, by omega⟩ <;> rw [h1, h2] at hres0 <;> simp at hres0 ⊢
    have huk1 : u ⟨k - 1, by omega⟩ = v ⟨k - 1, by omega⟩ := by
      have hk1 : resSum (fun i => xor (u i) (v i)) 2 = xor (u ⟨k - 1, by omega⟩) (v ⟨k - 1, by omega⟩) := by
        unfold resSum
        rw [xorFin_single' ⟨k - 1, by omega⟩]
        · have hm : (k - 1) % 3 = 2 := by omega
          dsimp only; rw [decide_eq_true hm, Bool.true_and]
        · intro i hi
          have hnek1 : i.val ≠ k - 1 := fun h => hi (Fin.ext h)
          by_cases h0 : i.val = 0
          · rw [h0]; rfl
          · dsimp only; rw [hd_mid i (by omega) (by omega), Bool.and_false]
      rw [hk1] at hres2
      cases h1 : u ⟨k - 1, by omega⟩ <;> cases h2 : v ⟨k - 1, by omega⟩ <;> rw [h1, h2] at hres2 <;> simp at hres2 ⊢
    funext i
    by_cases h0 : i.val = 0
    · have heq : i = ⟨0, by omega⟩ := Fin.ext h0; rw [heq]; exact hu0
    · by_cases hk1 : i.val = k - 1
      · have heq : i = ⟨k - 1, by omega⟩ := Fin.ext hk1; rw [heq]; exact huk1
      · exact hmid i (by omega) (by omega)
  calc (Finset.univ.filter (fun w : Fin k → Bool => resSum w 0 = resSum w 1 ∧ resSum w 1 = resSum w 2)).card
      ≤ (Finset.univ : Finset (Fin (k - 2) → Bool)).card :=
        Finset.card_le_card_of_injOn proj (fun _ _ => Finset.mem_univ _) hinj
    _ = 2 ^ (k - 2) := by simp [Fintype.card_fin, Fintype.card_bool]

lemma R0_false_eVec_eq {k : Nat} (hk : 0 < k) (hk5 : 5 ≤ k) (p j : Fin k) :
    R0 hk false (eVec p) j = decide (j.val = p.val ∨ j.val = (p.val + 1) % k ∨ j.val = (p.val + 2) % k) := by
  unfold R0 mix rot eVec ix; simp only [Bool.false_eq_true, ite_false]
  have h0 : ((j.val + k - 1 % k) % k + k - 1 % k) % k = p.val ↔ j.val = (p.val + 2) % k := by
    rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_sub_eq j.isLt (by omega), mod_add_eq p.isLt (by omega)]
    split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega
  have h1 : (j.val + k - 1 % k) % k = p.val ↔ j.val = (p.val + 1) % k := by
    rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_sub_eq j.isLt (by omega), mod_add_eq p.isLt (by omega)]
    split_ifs <;> omega
  have h2 : ((j.val + 1) % k + k - 1 % k) % k = p.val ↔ j.val = p.val := by
    rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_add_eq j.isLt (by omega)]
    split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega
  have he0 : decide ((⟨((j.val + k - 1 % k) % k + k - 1 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = p) =
      decide (j.val = (p.val + 2) % k) := decide_eq_decide_of_iff (by rw [Fin.ext_iff]; exact h0)
  have he1 : decide ((⟨(j.val + k - 1 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = p) =
      decide (j.val = (p.val + 1) % k) := decide_eq_decide_of_iff (by rw [Fin.ext_iff]; exact h1)
  have he2 : decide ((⟨((j.val + 1) % k + k - 1 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = p) =
      decide (j.val = p.val) := decide_eq_decide_of_iff (by rw [Fin.ext_iff]; exact h2)
  rw [he0, he1, he2]
  by_cases ha : j.val = p.val
  · have hb : j.val ≠ (p.val + 1) % k := by rw [mod_add_eq p.isLt (by omega)]; split_ifs <;> omega
    have hc : j.val ≠ (p.val + 2) % k := by rw [mod_add_eq p.isLt (by omega)]; split_ifs <;> omega
    rw [decide_eq_true ha, decide_eq_false hb, decide_eq_false hc, decide_eq_true (Or.inl ha)]; rfl
  · by_cases hb : j.val = (p.val + 1) % k
    · have hc : j.val ≠ (p.val + 2) % k := by
        rw [mod_add_eq p.isLt (by omega)] at hb; rw [mod_add_eq p.isLt (by omega)]; split_ifs at hb ⊢ <;> omega
      rw [decide_eq_false ha, decide_eq_true hb, decide_eq_false hc, decide_eq_true (Or.inr (Or.inl hb))]; rfl
    · by_cases hc : j.val = (p.val + 2) % k
      · rw [decide_eq_false ha, decide_eq_false hb, decide_eq_true hc, decide_eq_true (Or.inr (Or.inr hc))]; rfl
      · have hno : ¬(j.val = p.val ∨ j.val = (p.val + 1) % k ∨ j.val = (p.val + 2) % k) := by tauto
        rw [decide_eq_false ha, decide_eq_false hb, decide_eq_false hc, decide_eq_false hno]; rfl

lemma R0_true_eVec_eq {k : Nat} (hk : 0 < k) (hk6 : 6 ≤ k) (p j : Fin k) :
    R0 hk true (eVec p) j =
    decide (j.val = (p.val + 1) % k ∨ j.val = (p.val + 3) % k ∨ j.val = (p.val + 5) % k) := by
  unfold R0 mix rot eVec ix; simp only [ite_true]
  have h0 : ((j.val + k - 2 % k) % k + k - 3 % k) % k = p.val ↔ j.val = (p.val + 5) % k := by
    rw [Nat.mod_eq_of_lt (by omega : 2 < k), Nat.mod_eq_of_lt (by omega : 3 < k),
      mod_sub_eq j.isLt (by omega), mod_add_eq p.isLt (by omega)]
    split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega
  have h1 : (j.val + k - 3 % k) % k = p.val ↔ j.val = (p.val + 3) % k := by
    rw [Nat.mod_eq_of_lt (by omega : 3 < k), mod_sub_eq j.isLt (by omega), mod_add_eq p.isLt (by omega)]
    split_ifs <;> omega
  have h2 : ((j.val + 2) % k + k - 3 % k) % k = p.val ↔ j.val = (p.val + 1) % k := by
    rw [Nat.mod_eq_of_lt (by omega : 3 < k), mod_add_eq j.isLt (by omega), mod_add_eq p.isLt (by omega)]
    split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega
  have he0 : decide ((⟨((j.val + k - 2 % k) % k + k - 3 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = p) =
      decide (j.val = (p.val + 5) % k) := decide_eq_decide_of_iff (by rw [Fin.ext_iff]; exact h0)
  have he1 : decide ((⟨(j.val + k - 3 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = p) =
      decide (j.val = (p.val + 3) % k) := decide_eq_decide_of_iff (by rw [Fin.ext_iff]; exact h1)
  have he2 : decide ((⟨((j.val + 2) % k + k - 3 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = p) =
      decide (j.val = (p.val + 1) % k) := decide_eq_decide_of_iff (by rw [Fin.ext_iff]; exact h2)
  rw [he0, he1, he2]
  by_cases ha : j.val = (p.val + 1) % k
  · have hb : j.val ≠ (p.val + 3) % k := by
      rw [mod_add_eq p.isLt (by omega)] at ha; rw [mod_add_eq p.isLt (by omega)]; split_ifs at ha ⊢ <;> omega
    have hc : j.val ≠ (p.val + 5) % k := by
      rw [mod_add_eq p.isLt (by omega)] at ha; rw [mod_add_eq p.isLt (by omega)]; split_ifs at ha ⊢ <;> omega
    rw [decide_eq_true ha, decide_eq_false hb, decide_eq_false hc, decide_eq_true (Or.inl ha)]; rfl
  · by_cases hb : j.val = (p.val + 3) % k
    · have hc : j.val ≠ (p.val + 5) % k := by
        rw [mod_add_eq p.isLt (by omega)] at hb; rw [mod_add_eq p.isLt (by omega)]; split_ifs at hb ⊢ <;> omega
      rw [decide_eq_false ha, decide_eq_true hb, decide_eq_false hc, decide_eq_true (Or.inr (Or.inl hb))]; rfl
    · by_cases hc : j.val = (p.val + 5) % k
      · rw [decide_eq_false ha, decide_eq_false hb, decide_eq_true hc, decide_eq_true (Or.inr (Or.inr hc))]; rfl
      · have hno : ¬(j.val = (p.val + 1) % k ∨ j.val = (p.val + 3) % k ∨ j.val = (p.val + 5) % k) := by tauto
        rw [decide_eq_false ha, decide_eq_false hb, decide_eq_false hc, decide_eq_false hno]; rfl

lemma decide_and' (p q : Prop) [Decidable p] [Decidable q] :
    decide (p ∧ q) = (decide p && decide q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

lemma QBit_false_dist5 {k : Nat} (hk : 0 < k) (hk9 : 9 ≤ k) (i j : Fin k) :
    QBit hk false i (eVec (ix hk (j.val + k - 4))) (eVec (ix hk (j.val + 1))) = false := by
  unfold QBit
  rw [R0_false_eVec_eq hk (by omega), R0_false_eVec_eq hk (by omega),
      R0_false_eVec_eq hk (by omega), R0_false_eVec_eq hk (by omega)]
  rw [← decide_and', ← decide_and']
  have hs1 : ((j.val + k - 4) % k + 1) % k = (j.val + k - 3) % k := by rw [mod_add_mod_eq]; congr 1; omega
  have hs2 : ((j.val + k - 4) % k + 2) % k = (j.val + k - 2) % k := by rw [mod_add_mod_eq]; congr 1; omega
  have ha1 : ((j.val + 1) % k + 1) % k = (j.val + 2) % k := mod_add_mod_eq
  have ha2 : ((j.val + 1) % k + 2) % k = (j.val + 3) % k := mod_add_mod_eq
  have h1 : ¬(((ix hk (i.val + 1)).val = (ix hk (j.val + k - 4)).val ∨
               (ix hk (i.val + 1)).val = ((ix hk (j.val + k - 4)).val + 1) % k ∨
               (ix hk (i.val + 1)).val = ((ix hk (j.val + k - 4)).val + 2) % k) ∧
              ((ix hk (i.val + 2)).val = (ix hk (j.val + 1)).val ∨
               (ix hk (i.val + 2)).val = ((ix hk (j.val + 1)).val + 1) % k ∨
               (ix hk (i.val + 2)).val = ((ix hk (j.val + 1)).val + 2) % k)) := by
    dsimp only [ix]
    rw [hs1, hs2, ha1, ha2,
        shift_mod_sub_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_sub_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_sub_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega)]
    omega
  have h2 : ¬(((ix hk (i.val + 1)).val = (ix hk (j.val + 1)).val ∨
               (ix hk (i.val + 1)).val = ((ix hk (j.val + 1)).val + 1) % k ∨
               (ix hk (i.val + 1)).val = ((ix hk (j.val + 1)).val + 2) % k) ∧
              ((ix hk (i.val + 2)).val = (ix hk (j.val + k - 4)).val ∨
               (ix hk (i.val + 2)).val = ((ix hk (j.val + k - 4)).val + 1) % k ∨
               (ix hk (i.val + 2)).val = ((ix hk (j.val + k - 4)).val + 2) % k)) := by
    dsimp only [ix]
    rw [hs1, hs2, ha1, ha2,
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_sub_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_sub_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_sub_eq i.isLt j.isLt (by omega) (by omega)]
    omega
  rw [decide_eq_false h1, decide_eq_false h2]; rfl

lemma QBit_true_dist5 {k : Nat} (hk : 0 < k) (hk9 : 9 ≤ k) (hk10 : k ≠ 10) (i j : Fin k) :
    QBit hk true i (eVec (ix hk (j.val + k - 4))) (eVec (ix hk (j.val + 1))) = decide (i = j) := by
  unfold QBit
  rw [R0_true_eVec_eq hk (by omega), R0_true_eVec_eq hk (by omega),
      R0_true_eVec_eq hk (by omega), R0_true_eVec_eq hk (by omega)]
  rw [← decide_and', ← decide_and']
  have hs1 : ((j.val + k - 4) % k + 1) % k = (j.val + k - 3) % k := by rw [mod_add_mod_eq]; congr 1; omega
  have hs3 : ((j.val + k - 4) % k + 3) % k = (j.val + k - 1) % k := by rw [mod_add_mod_eq]; congr 1; omega
  have hs5 : ((j.val + k - 4) % k + 5) % k = (j.val + 1) % k := by
    rw [mod_add_mod_eq, show j.val + k - 4 + 5 = (j.val + 1) + k by omega, Nat.add_mod_right]
  have ha1 : ((j.val + 1) % k + 1) % k = (j.val + 2) % k := mod_add_mod_eq
  have ha3 : ((j.val + 1) % k + 3) % k = (j.val + 4) % k := mod_add_mod_eq
  have ha5 : ((j.val + 1) % k + 5) % k = (j.val + 6) % k := mod_add_mod_eq
  have hfwd : (((ix hk (i.val + 1)).val = ((ix hk (j.val + k - 4)).val + 1) % k ∨
                (ix hk (i.val + 1)).val = ((ix hk (j.val + k - 4)).val + 3) % k ∨
                (ix hk (i.val + 1)).val = ((ix hk (j.val + k - 4)).val + 5) % k) ∧
               ((ix hk (i.val + 2)).val = ((ix hk (j.val + 1)).val + 1) % k ∨
                (ix hk (i.val + 2)).val = ((ix hk (j.val + 1)).val + 3) % k ∨
                (ix hk (i.val + 2)).val = ((ix hk (j.val + 1)).val + 5) % k)) ↔ i = j := by
    dsimp only [ix]
    rw [hs1, hs3, hs5, ha1, ha3, ha5, Fin.ext_iff,
        shift_mod_sub_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_sub_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega)]
    omega
  have hbwd : ¬(((ix hk (i.val + 1)).val = ((ix hk (j.val + 1)).val + 1) % k ∨
                 (ix hk (i.val + 1)).val = ((ix hk (j.val + 1)).val + 3) % k ∨
                 (ix hk (i.val + 1)).val = ((ix hk (j.val + 1)).val + 5) % k) ∧
                ((ix hk (i.val + 2)).val = ((ix hk (j.val + k - 4)).val + 1) % k ∨
                 (ix hk (i.val + 2)).val = ((ix hk (j.val + k - 4)).val + 3) % k ∨
                 (ix hk (i.val + 2)).val = ((ix hk (j.val + k - 4)).val + 5) % k)) := by
    dsimp only [ix]
    rw [hs1, hs3, hs5, ha1, ha3, ha5,
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_sub_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_sub_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega)]
    omega
  rw [decide_eq_false hbwd, Bool.xor_false]
  exact decide_eq_decide_of_iff hfwd

lemma QBit_false_dist3 {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (i j : Fin k) :
    QBit hk false i (eVec (ix hk (j.val + k - 1))) (eVec (ix hk (j.val + 2))) = decide (i = j) := by
  unfold QBit
  rw [R0_false_eVec_eq hk (by omega), R0_false_eVec_eq hk (by omega),
      R0_false_eVec_eq hk (by omega), R0_false_eVec_eq hk (by omega)]
  rw [← decide_and', ← decide_and']
  have hs1 : ((j.val + k - 1) % k + 1) % k = (j.val + 0) % k := by
    rw [mod_add_mod_eq, show j.val + k - 1 + 1 = j.val + k by omega, Nat.add_mod_right, Nat.add_zero]
  have hs2 : ((j.val + k - 1) % k + 2) % k = (j.val + 1) % k := by
    rw [mod_add_mod_eq, show j.val + k - 1 + 2 = (j.val + 1) + k by omega, Nat.add_mod_right]
  have ha1 : ((j.val + 2) % k + 1) % k = (j.val + 3) % k := mod_add_mod_eq
  have ha2 : ((j.val + 2) % k + 2) % k = (j.val + 4) % k := mod_add_mod_eq
  have hfwd : (((ix hk (i.val + 1)).val = (ix hk (j.val + k - 1)).val ∨
                (ix hk (i.val + 1)).val = ((ix hk (j.val + k - 1)).val + 1) % k ∨
                (ix hk (i.val + 1)).val = ((ix hk (j.val + k - 1)).val + 2) % k) ∧
               ((ix hk (i.val + 2)).val = (ix hk (j.val + 2)).val ∨
                (ix hk (i.val + 2)).val = ((ix hk (j.val + 2)).val + 1) % k ∨
                (ix hk (i.val + 2)).val = ((ix hk (j.val + 2)).val + 2) % k)) ↔ i = j := by
    dsimp only [ix]
    rw [hs1, hs2, ha1, ha2, Fin.ext_iff,
        shift_mod_sub_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega)]
    omega
  have hbwd : ¬(((ix hk (i.val + 1)).val = (ix hk (j.val + 2)).val ∨
                 (ix hk (i.val + 1)).val = ((ix hk (j.val + 2)).val + 1) % k ∨
                 (ix hk (i.val + 1)).val = ((ix hk (j.val + 2)).val + 2) % k) ∧
                ((ix hk (i.val + 2)).val = (ix hk (j.val + k - 1)).val ∨
                 (ix hk (i.val + 2)).val = ((ix hk (j.val + k - 1)).val + 1) % k ∨
                 (ix hk (i.val + 2)).val = ((ix hk (j.val + k - 1)).val + 2) % k)) := by
    dsimp only [ix]
    rw [hs1, hs2, ha1, ha2,
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_sub_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega),
        shift_mod_eq i.isLt j.isLt (by omega) (by omega)]
    omega
  rw [decide_eq_false hbwd, Bool.xor_false]
  exact decide_eq_decide_of_iff hfwd

lemma QBit_eval_5 :
    (∀ j i : Fin 5,
      QBit (by omega : 0 < 5) false i (eVec j) (eVec (ix (by omega : 0 < 5) (j.val + 1))) =
        decide (i = ix (by omega : 0 < 5) (j.val + 1) ∨ i = ix (by omega : 0 < 5) (j.val + 4)) ∧
      QBit (by omega : 0 < 5) true i (eVec j) (eVec (ix (by omega : 0 < 5) (j.val + 1))) = true ∧
      QBit (by omega : 0 < 5) false i (eVec j) (eVec (ix (by omega : 0 < 5) (j.val + 2))) =
        decide (i = j ∨ i = ix (by omega : 0 < 5) (j.val + 1) ∨ i = ix (by omega : 0 < 5) (j.val + 3)) ∧
      QBit (by omega : 0 < 5) true i (eVec j) (eVec (ix (by omega : 0 < 5) (j.val + 2))) =
        decide (i = j ∨ i = ix (by omega : 0 < 5) (j.val + 1) ∨ i = ix (by omega : 0 < 5) (j.val + 4))) := by decide

lemma QBit_indep_5 (a b : Fin 5 → Bool)
    (hz : ∀ p q : Fin 5,
      xor (xorFin (fun i : Fin 5 => a i && QBit (by omega : 0 < 5) false i (eVec p) (eVec q)))
          (xorFin (fun i : Fin 5 => b i && QBit (by omega : 0 < 5) true i (eVec p) (eVec q))) = false) :
    (∀ i, a i = false) ∧ (∀ i, b i = false) := by
  have h1 : ∀ j : Fin 5, xor (xor (a (ix (by omega) (j.val + 1))) (a (ix (by omega) (j.val + 4)))) (xorFin b) = false := by
    intro j
    have h := hz j (ix (by omega) (j.val + 1))
    have hA : xorFin (fun i : Fin 5 => a i && QBit (by omega) false i (eVec j) (eVec (ix (by omega) (j.val + 1)))) =
        xor (a (ix (by omega) (j.val + 1))) (a (ix (by omega) (j.val + 4))) := by
      have hr : ∀ i : Fin 5, (a i && QBit (by omega) false i (eVec j) (eVec (ix (by omega) (j.val + 1)))) =
          xor (a i && decide (i = ix (by omega) (j.val + 1))) (a i && decide (i = ix (by omega) (j.val + 4))) := fun i => by
        rw [(QBit_eval_5 j i).1]
        have hne : ix (by omega : 0 < 5) (j.val + 1) ≠ ix (by omega : 0 < 5) (j.val + 4) := by
          intro heq; have := congrArg Fin.val heq; dsimp [ix] at this; omega
        by_cases h1' : i = ix (by omega) (j.val + 1)
        · subst h1'; simp [hne]
        · by_cases h2' : i = ix (by omega) (j.val + 4)
          · subst h2'; simp [hne.symm]
          · simp [h1', h2']
      rw [xorFin_congr _ _ hr, xorFin_xor, xorFin_single' (ix (by omega) (j.val + 1)), xorFin_single' (ix (by omega) (j.val + 4))]
      · simp
      · intro i hi; simp [hi]
      · intro i hi; simp [hi]
    have hB : xorFin (fun i : Fin 5 => b i && QBit (by omega) true i (eVec j) (eVec (ix (by omega) (j.val + 1)))) = xorFin b := by
      apply xorFin_congr; intro i; rw [(QBit_eval_5 j i).2.1, Bool.and_true]
    rw [hA, hB] at h; exact h
  have h2 : ∀ j : Fin 5,
      xor (xor (a j) (xor (a (ix (by omega) (j.val + 1))) (a (ix (by omega) (j.val + 3)))))
          (xor (b j) (xor (b (ix (by omega) (j.val + 1))) (b (ix (by omega) (j.val + 4))))) = false := by
    intro j
    have h := hz j (ix (by omega) (j.val + 2))
    have h3s : ∀ (f : Fin 5 → Bool) (x0 x1 x2 : Fin 5), x0 ≠ x1 → x0 ≠ x2 → x1 ≠ x2 →
        xorFin (fun i : Fin 5 => f i && decide (i = x0 ∨ i = x1 ∨ i = x2)) = xor (f x0) (xor (f x1) (f x2)) := by
      intro f x0 x1 x2 h01 h02 h12
      have hr : ∀ i : Fin 5, (f i && decide (i = x0 ∨ i = x1 ∨ i = x2)) =
          xor (f i && decide (i = x0)) (xor (f i && decide (i = x1)) (f i && decide (i = x2))) := fun i => by
        by_cases c0 : i = x0
        · subst c0; simp [h01, h02]
        · by_cases c1 : i = x1
          · subst c1; simp [h01.symm, h12]
          · by_cases c2 : i = x2
            · subst c2; simp [h02.symm, h12.symm]
            · simp [c0, c1, c2]
      rw [xorFin_congr _ _ hr, xorFin_xor, xorFin_xor, xorFin_single' x0, xorFin_single' x1, xorFin_single' x2]
      · simp
      · intro i hi; simp [hi]
      · intro i hi; simp [hi]
      · intro i hi; simp [hi]
    have hA : xorFin (fun i : Fin 5 => a i && QBit (by omega) false i (eVec j) (eVec (ix (by omega) (j.val + 2)))) =
        xor (a j) (xor (a (ix (by omega) (j.val + 1))) (a (ix (by omega) (j.val + 3)))) := by
      rw [xorFin_congr _ _ (fun i => by rw [(QBit_eval_5 j i).2.2.1])]
      exact h3s a j _ _ (by intro h; have := congrArg Fin.val h; dsimp [ix] at this; omega)
        (by intro h; have := congrArg Fin.val h; dsimp [ix] at this; omega)
        (by intro h; have := congrArg Fin.val h; dsimp [ix] at this; omega)
    have hB : xorFin (fun i : Fin 5 => b i && QBit (by omega) true i (eVec j) (eVec (ix (by omega) (j.val + 2)))) =
        xor (b j) (xor (b (ix (by omega) (j.val + 1))) (b (ix (by omega) (j.val + 4)))) := by
      rw [xorFin_congr _ _ (fun i => by rw [(QBit_eval_5 j i).2.2.2])]
      exact h3s b j _ _ (by intro h; have := congrArg Fin.val h; dsimp [ix] at this; omega)
        (by intro h; have := congrArg Fin.val h; dsimp [ix] at this; omega)
        (by intro h; have := congrArg Fin.val h; dsimp [ix] at this; omega)
    rw [hA, hB] at h; exact h
  have h10 := h1 0; have h11 := h1 1; have h12 := h1 2; have h13 := h1 3; have h14 := h1 4
  have h20 := h2 0; have h21 := h2 1; have h22 := h2 2; have h23 := h2 3; have h24 := h2 4
  have hxb : xorFin b = xor (b 0) (xor (b 1) (xor (b 2) (xor (b 3) (b 4)))) := by
    unfold xorFin; have : List.finRange 5 = [0, 1, 2, 3, 4] := rfl; rw [this]; simp
  change xor (xor (a 1) (a 4)) (xorFin b) = false at h10
  change xor (xor (a 2) (a 0)) (xorFin b) = false at h11
  change xor (xor (a 3) (a 1)) (xorFin b) = false at h12
  change xor (xor (a 4) (a 2)) (xorFin b) = false at h13
  change xor (xor (a 0) (a 3)) (xorFin b) = false at h14
  change xor (xor (a 0) (xor (a 1) (a 3))) (xor (b 0) (xor (b 1) (b 4))) = false at h20
  change xor (xor (a 1) (xor (a 2) (a 4))) (xor (b 1) (xor (b 2) (b 0))) = false at h21
  change xor (xor (a 2) (xor (a 3) (a 0))) (xor (b 2) (xor (b 3) (b 1))) = false at h22
  change xor (xor (a 3) (xor (a 4) (a 1))) (xor (b 3) (xor (b 4) (b 2))) = false at h23
  change xor (xor (a 4) (xor (a 0) (a 2))) (xor (b 4) (xor (b 0) (b 3))) = false at h24
  have hstep1 : ∀ a0 a1 a2 a3 a4 S : Bool,
      xor (xor a1 a4) S = false → xor (xor a2 a0) S = false → xor (xor a3 a1) S = false →
      xor (xor a4 a2) S = false → xor (xor a0 a3) S = false →
      S = false ∧ a1 = a0 ∧ a2 = a0 ∧ a3 = a0 ∧ a4 = a0 := by
    intro a0 a1 a2 a3 a4 S; cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases S <;> simp
  rcases hstep1 (a 0) (a 1) (a 2) (a 3) (a 4) (xorFin b) h10 h11 h12 h13 h14 with ⟨hS, ha1, ha2, ha3, ha4⟩
  rw [hxb] at hS
  simp only [ha1, ha2, ha3, ha4] at h20 h21 h22 h23 h24
  have hstep2 : ∀ A b0 b1 b2 b3 b4 : Bool,
      xor b0 (xor b1 (xor b2 (xor b3 b4))) = false →
      xor (xor A (xor A A)) (xor b0 (xor b1 b4)) = false →
      xor (xor A (xor A A)) (xor b1 (xor b2 b0)) = false →
      xor (xor A (xor A A)) (xor b2 (xor b3 b1)) = false →
      xor (xor A (xor A A)) (xor b3 (xor b4 b2)) = false →
      xor (xor A (xor A A)) (xor b4 (xor b0 b3)) = false →
      A = false ∧ b0 = false ∧ b1 = false ∧ b2 = false ∧ b3 = false ∧ b4 = false := by
    intro A b0 b1 b2 b3 b4; cases A <;> cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> simp
  rcases hstep2 (a 0) (b 0) (b 1) (b 2) (b 3) (b 4) hS h20 h21 h22 h23 h24 with ⟨ha0, hb0, hb1, hb2, hb3, hb4⟩
  exact ⟨fun i => by fin_cases i <;> simp [ha0, ha1, ha2, ha3, ha4],
         fun i => by fin_cases i <;> simp [hb0, hb1, hb2, hb3, hb4]⟩

lemma QBit_eval_7 :
    ∀ j i : Fin 7,
      QBit (by omega : 0 < 7) false i (eVec j) (eVec (ix (by omega : 0 < 7) (j.val + 2))) =
        decide (i = j ∨ i = ix (by omega : 0 < 7) (j.val + 1)) ∧
      QBit (by omega : 0 < 7) true i (eVec j) (eVec (ix (by omega : 0 < 7) (j.val + 2))) =
        decide (i = ix (by omega : 0 < 7) (j.val + 6)) ∧
      QBit (by omega : 0 < 7) false i (eVec j) (eVec (ix (by omega : 0 < 7) (j.val + 3))) =
        decide (i = ix (by omega : 0 < 7) (j.val + 1)) ∧
      QBit (by omega : 0 < 7) true i (eVec j) (eVec (ix (by omega : 0 < 7) (j.val + 3))) =
        decide (i = ix (by omega : 0 < 7) (j.val + 2) ∨ i = ix (by omega : 0 < 7) (j.val + 3) ∨ i = ix (by omega : 0 < 7) (j.val + 4)) := by decide

lemma QBit_indep_7 (a b : Fin 7 → Bool)
    (hz : ∀ p q : Fin 7,
      xor (xorFin (fun i : Fin 7 => a i && QBit (by omega : 0 < 7) false i (eVec p) (eVec q)))
          (xorFin (fun i : Fin 7 => b i && QBit (by omega : 0 < 7) true i (eVec p) (eVec q))) = false) :
    (∀ i, a i = false) ∧ (∀ i, b i = false) := by
  have hb_eq : ∀ j : Fin 7, b (ix (by omega) (j.val + 6)) = xor (a j) (a (ix (by omega) (j.val + 1))) := by
    intro j
    have h := hz j (ix (by omega) (j.val + 2))
    have hA : xorFin (fun i : Fin 7 => a i && QBit (by omega) false i (eVec j) (eVec (ix (by omega) (j.val + 2)))) =
        xor (a j) (a (ix (by omega) (j.val + 1))) := by
      have hr : ∀ i : Fin 7, (a i && QBit (by omega) false i (eVec j) (eVec (ix (by omega) (j.val + 2)))) =
          xor (a i && decide (i = j)) (a i && decide (i = ix (by omega) (j.val + 1))) := fun i => by
        rw [(QBit_eval_7 j i).1]
        have hne : j ≠ ix (by omega : 0 < 7) (j.val + 1) := by
          intro heq; have := congrArg Fin.val heq; dsimp [ix] at this; omega
        by_cases c0 : i = j
        · subst c0; simp [hne]
        · by_cases c1 : i = ix (by omega) (j.val + 1)
          · subst c1; simp [hne.symm]
          · simp [c0, c1]
      rw [xorFin_congr _ _ hr, xorFin_xor, xorFin_single' j, xorFin_single' (ix (by omega) (j.val + 1))]
      · simp
      · intro i hi; simp [hi]
      · intro i hi; simp [hi]
    have hB : xorFin (fun i : Fin 7 => b i && QBit (by omega) true i (eVec j) (eVec (ix (by omega) (j.val + 2)))) =
        b (ix (by omega) (j.val + 6)) := by
      rw [xorFin_single' (ix (by omega) (j.val + 6))]
      · rw [(QBit_eval_7 j _).2.1, decide_eq_true rfl, Bool.and_true]
      · intro i hi; rw [(QBit_eval_7 j i).2.1, decide_eq_false hi, Bool.and_false]
    rw [hA, hB] at h
    cases x : xor (a j) (a (ix (by omega) (j.val + 1))) <;> cases y : b (ix (by omega) (j.val + 6)) <;>
      rw [x, y] at h <;> simp at h ⊢
  have ha_rel : ∀ j : Fin 7,
      xor (a (ix (by omega) (j.val + 1)))
          (xor (a (ix (by omega) (j.val + 3))) (a (ix (by omega) (j.val + 6)))) = false := by
    intro j
    have h := hz j (ix (by omega) (j.val + 3))
    have hA : xorFin (fun i : Fin 7 => a i && QBit (by omega) false i (eVec j) (eVec (ix (by omega) (j.val + 3)))) =
        a (ix (by omega) (j.val + 1)) := by
      rw [xorFin_single' (ix (by omega) (j.val + 1))]
      · rw [(QBit_eval_7 j _).2.2.1, decide_eq_true rfl, Bool.and_true]
      · intro i hi; rw [(QBit_eval_7 j i).2.2.1, decide_eq_false hi, Bool.and_false]
    have hB : xorFin (fun i : Fin 7 => b i && QBit (by omega) true i (eVec j) (eVec (ix (by omega) (j.val + 3)))) =
        xor (b (ix (by omega) (j.val + 2))) (xor (b (ix (by omega) (j.val + 3))) (b (ix (by omega) (j.val + 4)))) := by
      have hr : ∀ i : Fin 7, (b i && QBit (by omega) true i (eVec j) (eVec (ix (by omega) (j.val + 3)))) =
          xor (b i && decide (i = ix (by omega) (j.val + 2)))
              (xor (b i && decide (i = ix (by omega) (j.val + 3))) (b i && decide (i = ix (by omega) (j.val + 4)))) := fun i => by
        rw [(QBit_eval_7 j i).2.2.2]
        have h23 : ix (by omega : 0 < 7) (j.val + 2) ≠ ix (by omega : 0 < 7) (j.val + 3) := by
          intro h; have := congrArg Fin.val h; dsimp [ix] at this; omega
        have h24 : ix (by omega : 0 < 7) (j.val + 2) ≠ ix (by omega : 0 < 7) (j.val + 4) := by
          intro h; have := congrArg Fin.val h; dsimp [ix] at this; omega
        have h34 : ix (by omega : 0 < 7) (j.val + 3) ≠ ix (by omega : 0 < 7) (j.val + 4) := by
          intro h; have := congrArg Fin.val h; dsimp [ix] at this; omega
        by_cases c0 : i = ix (by omega) (j.val + 2)
        · subst c0; simp [h23, h24]
        · by_cases c1 : i = ix (by omega) (j.val + 3)
          · subst c1; simp [h23.symm, h34]
          · by_cases c2 : i = ix (by omega) (j.val + 4)
            · subst c2; simp [h24.symm, h34.symm]
            · simp [c0, c1, c2]
      rw [xorFin_congr _ _ hr, xorFin_xor, xorFin_xor,
          xorFin_single' (ix (by omega) (j.val + 2)), xorFin_single' (ix (by omega) (j.val + 3)),
          xorFin_single' (ix (by omega) (j.val + 4))]
      · simp
      · intro i hi; simp [hi]
      · intro i hi; simp [hi]
      · intro i hi; simp [hi]
    rw [hA, hB] at h
    have hb2 := hb_eq (ix (by omega) (j.val + 3))
    have hb3 := hb_eq (ix (by omega) (j.val + 4))
    have hb4 := hb_eq (ix (by omega) (j.val + 5))
    have e1 : ix (by omega : 0 < 7) ((ix (by omega : 0 < 7) (j.val + 3)).val + 6) = ix (by omega : 0 < 7) (j.val + 2) := Fin.ext (by dsimp [ix]; omega)
    have e2 : ix (by omega : 0 < 7) ((ix (by omega : 0 < 7) (j.val + 4)).val + 6) = ix (by omega : 0 < 7) (j.val + 3) := Fin.ext (by dsimp [ix]; omega)
    have e3 : ix (by omega : 0 < 7) ((ix (by omega : 0 < 7) (j.val + 5)).val + 6) = ix (by omega : 0 < 7) (j.val + 4) := Fin.ext (by dsimp [ix]; omega)
    have e4 : ix (by omega : 0 < 7) ((ix (by omega : 0 < 7) (j.val + 3)).val + 1) = ix (by omega : 0 < 7) (j.val + 4) := Fin.ext (by dsimp [ix]; omega)
    have e5 : ix (by omega : 0 < 7) ((ix (by omega : 0 < 7) (j.val + 4)).val + 1) = ix (by omega : 0 < 7) (j.val + 5) := Fin.ext (by dsimp [ix]; omega)
    have e6 : ix (by omega : 0 < 7) ((ix (by omega : 0 < 7) (j.val + 5)).val + 1) = ix (by omega : 0 < 7) (j.val + 6) := Fin.ext (by dsimp [ix]; omega)
    rw [e1, e4] at hb2; rw [e2, e5] at hb3; rw [e3, e6] at hb4
    rw [hb2, hb3, hb4] at h
    revert h
    cases a (ix (by omega) (j.val + 1)) <;> cases a (ix (by omega) (j.val + 3)) <;>
      cases a (ix (by omega) (j.val + 4)) <;> cases a (ix (by omega) (j.val + 5)) <;>
      cases a (ix (by omega) (j.val + 6)) <;> simp
  have hcancel7 : ∀ a0 a1 a2 a3 a4 a5 a6 : Bool,
      xor a1 (xor a3 a6) = false → xor a2 (xor a4 a0) = false →
      xor a5 (xor a0 a3) = false → xor a6 (xor a1 a4) = false → xor a0 (xor a2 a5) = false →
      a0 = false := by
    intro a0 a1 a2 a3 a4 a5 a6 r0 r1 r4 r5 r6
    have h05 : xor a3 a4 = false := by
      cases a1 <;> cases a3 <;> cases a4 <;> cases a6 <;> simp at r0 r5 ⊢
    have h16 : xor a4 a5 = false := by
      cases a0 <;> cases a2 <;> cases a4 <;> cases a5 <;> simp at r1 r6 ⊢
    cases a0 <;> cases a3 <;> cases a4 <;> cases a5 <;> simp at h05 h16 r4 ⊢
  have ha0 : ∀ j : Fin 7, a j = false := fun j => by
    have r0 := ha_rel j
    have r1 := ha_rel (ix (by omega) (j.val + 1))
    have r4 := ha_rel (ix (by omega) (j.val + 4))
    have r5 := ha_rel (ix (by omega) (j.val + 5))
    have r6 := ha_rel (ix (by omega) (j.val + 6))
    have s : ∀ (c d : Nat), ix (by omega : 0 < 7) ((ix (by omega : 0 < 7) (j.val + c)).val + d) =
        ix (by omega : 0 < 7) (j.val + (c + d) % 7) := fun c d => Fin.ext (by dsimp [ix]; omega)
    have s0 : ix (by omega : 0 < 7) (j.val + 0) = j := Fin.ext (by dsimp [ix]; omega)
    rw [s 1 1, s 1 3, s 1 6, s0] at r1
    rw [s 4 1, s 4 3, s 4 6, s0] at r4
    rw [s 5 1, s 5 3, s 5 6] at r5
    rw [s 6 1, s 6 3, s 6 6, s0] at r6
    exact hcancel7 (a j) (a (ix (by omega) (j.val + 1))) (a (ix (by omega) (j.val + 2)))
      (a (ix (by omega) (j.val + 3))) (a (ix (by omega) (j.val + 4)))
      (a (ix (by omega) (j.val + 5))) (a (ix (by omega) (j.val + 6))) r0 r1 r4 r5 r6
  refine ⟨ha0, fun i => ?_⟩
  have hbi := hb_eq (ix (by omega) (i.val + 1))
  have ei : ix (by omega : 0 < 7) ((ix (by omega : 0 < 7) (i.val + 1)).val + 6) = i := Fin.ext (by dsimp [ix]; omega)
  rw [ei, ha0, ha0] at hbi; exact hbi

lemma QBit_eval_8 :
    ∀ j i : Fin 8,
      QBit (by omega : 0 < 8) false i (eVec j) (eVec (ix (by omega : 0 < 8) (j.val + 2))) =
        decide (i = j ∨ i = ix (by omega : 0 < 8) (j.val + 1)) ∧
      QBit (by omega : 0 < 8) true i (eVec j) (eVec (ix (by omega : 0 < 8) (j.val + 2))) = false ∧
      QBit (by omega : 0 < 8) false i (eVec j) (eVec (ix (by omega : 0 < 8) (j.val + 1))) =
        decide (i = ix (by omega : 0 < 8) (j.val + 1) ∨ i = ix (by omega : 0 < 8) (j.val + 7)) ∧
      QBit (by omega : 0 < 8) true i (eVec j) (eVec (ix (by omega : 0 < 8) (j.val + 1))) =
        decide (i = j ∨ i = ix (by omega : 0 < 8) (j.val + 1) ∨ i = ix (by omega : 0 < 8) (j.val + 2) ∨
                i = ix (by omega : 0 < 8) (j.val + 3) ∨ i = ix (by omega : 0 < 8) (j.val + 4)) ∧
      QBit (by omega : 0 < 8) false i (eVec j) (eVec (ix (by omega : 0 < 8) (j.val + 3))) =
        decide (i = ix (by omega : 0 < 8) (j.val + 1)) ∧
      QBit (by omega : 0 < 8) true i (eVec j) (eVec (ix (by omega : 0 < 8) (j.val + 3))) =
        decide (i = ix (by omega : 0 < 8) (j.val + 2) ∨ i = ix (by omega : 0 < 8) (j.val + 3) ∨
                i = ix (by omega : 0 < 8) (j.val + 4) ∨ i = ix (by omega : 0 < 8) (j.val + 7)) := by decide

lemma QBit_indep_8 (a b : Fin 8 → Bool)
    (hz : ∀ p q : Fin 8,
      xor (xorFin (fun i : Fin 8 => a i && QBit (by omega : 0 < 8) false i (eVec p) (eVec q)))
          (xorFin (fun i : Fin 8 => b i && QBit (by omega : 0 < 8) true i (eVec p) (eVec q))) = false) :
    (∀ i, a i = false) ∧ (∀ i, b i = false) := by
  have ha_step : ∀ j : Fin 8, a j = a (ix (by omega) (j.val + 1)) := by
    intro j
    have h := hz j (ix (by omega) (j.val + 2))
    rw [xorFin_eq_false (fun i => b i && QBit (by omega) true i (eVec j) (eVec (ix (by omega) (j.val + 2))))
          (fun i => by rw [(QBit_eval_8 j i).2.1, Bool.and_false]), Bool.xor_false] at h
    have hr : ∀ i : Fin 8, (a i && QBit (by omega) false i (eVec j) (eVec (ix (by omega) (j.val + 2)))) =
        xor (a i && decide (i = j)) (a i && decide (i = ix (by omega) (j.val + 1))) := fun i => by
      rw [(QBit_eval_8 j i).1]
      have hne : j ≠ ix (by omega : 0 < 8) (j.val + 1) := by intro heq; have := congrArg Fin.val heq; dsimp [ix] at this; omega
      by_cases c0 : i = j
      · subst c0; simp [hne]
      · by_cases c1 : i = ix (by omega) (j.val + 1)
        · subst c1; simp [hne.symm]
        · simp [c0, c1]
    rw [xorFin_congr _ _ hr, xorFin_xor, xorFin_single' j, xorFin_single' (ix (by omega) (j.val + 1))] at h
    · simp only [decide_true, Bool.and_true] at h
      cases x : a j <;> cases y : a (ix (by omega) (j.val + 1)) <;> rw [x, y] at h <;> simp at h ⊢
    · intro i hi; simp [hi]
    · intro i hi; simp [hi]
  have ha_const : ∀ i : Fin 8, a i = a 0 := by
    have h0 := ha_step 0; have h1 := ha_step 1; have h2 := ha_step 2
    have h3 := ha_step 3; have h4 := ha_step 4; have h5 := ha_step 5; have h6 := ha_step 6
    change a 0 = a 1 at h0; change a 1 = a 2 at h1; change a 2 = a 3 at h2
    change a 3 = a 4 at h3; change a 4 = a 5 at h4; change a 5 = a 6 at h5; change a 6 = a 7 at h6
    intro i; fin_cases i
    · rfl
    · exact h0.symm
    · exact (h0.trans h1).symm
    · exact ((h0.trans h1).trans h2).symm
    · exact (((h0.trans h1).trans h2).trans h3).symm
    · exact ((((h0.trans h1).trans h2).trans h3).trans h4).symm
    · exact (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).symm
    · exact ((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).symm
  have hb_sum5 : ∀ j : Fin 8,
      xor (b j) (xor (b (ix (by omega) (j.val + 1))) (xor (b (ix (by omega) (j.val + 2)))
        (xor (b (ix (by omega) (j.val + 3))) (b (ix (by omega) (j.val + 4)))))) = false := by
    intro j
    have h := hz j (ix (by omega) (j.val + 1))
    have hA0 : xorFin (fun i : Fin 8 => a i && QBit (by omega) false i (eVec j) (eVec (ix (by omega) (j.val + 1)))) = false := by
      have hr : ∀ i : Fin 8, (a i && QBit (by omega) false i (eVec j) (eVec (ix (by omega) (j.val + 1)))) =
          xor (a i && decide (i = ix (by omega) (j.val + 1))) (a i && decide (i = ix (by omega) (j.val + 7))) := fun i => by
        rw [(QBit_eval_8 j i).2.2.1]
        have hne : ix (by omega : 0 < 8) (j.val + 1) ≠ ix (by omega : 0 < 8) (j.val + 7) := by
          intro heq; have := congrArg Fin.val heq; dsimp [ix] at this; omega
        by_cases c0 : i = ix (by omega) (j.val + 1)
        · subst c0; simp [hne]
        · by_cases c1 : i = ix (by omega) (j.val + 7)
          · subst c1; simp [hne.symm]
          · simp [c0, c1]
      rw [xorFin_congr _ _ hr, xorFin_xor, xorFin_single' (ix (by omega) (j.val + 1)), xorFin_single' (ix (by omega) (j.val + 7))]
      · simp [ha_const]
      · intro i hi; simp [hi]
      · intro i hi; simp [hi]
    rw [hA0, Bool.false_xor] at h
    have hB : xorFin (fun i : Fin 8 => b i && QBit (by omega) true i (eVec j) (eVec (ix (by omega) (j.val + 1)))) =
        xor (b j) (xor (b (ix (by omega) (j.val + 1))) (xor (b (ix (by omega) (j.val + 2)))
          (xor (b (ix (by omega) (j.val + 3))) (b (ix (by omega) (j.val + 4)))))) := by
      rw [xorFin_congr _ _ (fun i => by rw [(QBit_eval_8 j i).2.2.2.1])]
      unfold xorFin; have : List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl; rw [this]
      have hrot5 : ∀ x0 x1 x2 x3 x4 : Bool,
          xor x0 (xor x1 (xor x2 (xor x3 x4))) = xor x1 (xor x2 (xor x3 (xor x4 x0))) := by decide
      fin_cases j
      · simp [ix]
      · simp [ix]
      · simp [ix]
      · simp [ix]
      · simp [ix]; exact hrot5 (b 0) (b 4) (b 5) (b 6) (b 7)
      · simp [ix]; rw [hrot5 (b 0) (b 1) (b 5) (b 6) (b 7), hrot5 (b 1) (b 5) (b 6) (b 7) (b 0)]
      · simp [ix]; rw [hrot5 (b 0) (b 1) (b 2) (b 6) (b 7), hrot5 (b 1) (b 2) (b 6) (b 7) (b 0), hrot5 (b 2) (b 6) (b 7) (b 0) (b 1)]
      · simp [ix]; exact (hrot5 (b 7) (b 0) (b 1) (b 2) (b 3)).symm
    rw [hB] at h; exact h
  have hcancel8 : ∀ u v w z : Bool,
      xor u v = false → xor v w = false → xor w (xor z u) = false → z = false := by
    intro u v w z; cases u <;> cases v <;> cases w <;> cases z <;> simp
  have hb0 : ∀ j : Fin 8, b j = false := fun j => by
    have r1 := hb_sum5 (ix (by omega) (j.val + 1))
    have r3 := hb_sum5 (ix (by omega) (j.val + 3))
    have r6 := hb_sum5 (ix (by omega) (j.val + 6))
    have s : ∀ (c d : Nat), ix (by omega : 0 < 8) ((ix (by omega : 0 < 8) (j.val + c)).val + d) =
        ix (by omega : 0 < 8) (j.val + (c + d) % 8) := fun c d => Fin.ext (by dsimp [ix]; omega)
    have s0 : ix (by omega : 0 < 8) (j.val + 0) = j := Fin.ext (by dsimp [ix]; omega)
    rw [s 1 1, s 1 2, s 1 3, s 1 4] at r1
    rw [s 3 1, s 3 2, s 3 3, s 3 4] at r3
    rw [s 6 1, s 6 2, s 6 3, s 6 4, s0] at r6
    have r1' : xor (xor (b (ix (by omega) (j.val + 1))) (b (ix (by omega) (j.val + 2))))
        (xor (b (ix (by omega) (j.val + 3))) (xor (b (ix (by omega) (j.val + 4))) (b (ix (by omega) (j.val + 5))))) = false := by
      simpa [Bool.xor_assoc] using r1
    have r3' : xor (xor (b (ix (by omega) (j.val + 3))) (xor (b (ix (by omega) (j.val + 4))) (b (ix (by omega) (j.val + 5)))))
        (xor (b (ix (by omega) (j.val + 6))) (b (ix (by omega) (j.val + 7)))) = false := by
      simpa [Bool.xor_assoc] using r3
    have r6' : xor (xor (b (ix (by omega) (j.val + 6))) (b (ix (by omega) (j.val + 7))))
        (xor (b j) (xor (b (ix (by omega) (j.val + 1))) (b (ix (by omega) (j.val + 2))))) = false := by
      simpa [Bool.xor_assoc] using r6
    exact hcancel8 _ _ _ (b j) r1' r3' r6'
  have ha1 : a 1 = false := by
    have h := hz 0 3
    rw [xorFin_eq_false (fun i => b i && QBit (by omega) true i (eVec 0) (eVec 3))
          (fun i => by rw [hb0 i, Bool.false_and]), Bool.xor_false] at h
    rw [xorFin_single' 1] at h
    · have he : QBit (by omega : 0 < 8) false 1 (eVec 0) (eVec 3) = true := (QBit_eval_8 0 1).2.2.2.2.1
      rw [he, Bool.and_true] at h; exact h
    · intro i hi
      have he : QBit (by omega : 0 < 8) false i (eVec 0) (eVec 3) = decide (i = 1) := (QBit_eval_8 0 i).2.2.2.2.1
      rw [he, decide_eq_false hi, Bool.and_false]
  exact ⟨fun i => by rw [ha_const i, ← ha_const 1, ha1], hb0⟩

lemma QBit_eval_10 :
    ∀ j i : Fin 10,
      QBit (by omega : 0 < 10) false i (eVec j) (eVec (ix (by omega : 0 < 10) (j.val + 2))) =
        decide (i = j ∨ i = ix (by omega : 0 < 10) (j.val + 1)) ∧
      QBit (by omega : 0 < 10) true i (eVec j) (eVec (ix (by omega : 0 < 10) (j.val + 2))) = false ∧
      QBit (by omega : 0 < 10) false i (eVec j) (eVec (ix (by omega : 0 < 10) (j.val + 5))) = false ∧
      QBit (by omega : 0 < 10) true i (eVec j) (eVec (ix (by omega : 0 < 10) (j.val + 5))) =
        decide (i = ix (by omega : 0 < 10) (j.val + 4) ∨ i = ix (by omega : 0 < 10) (j.val + 9)) ∧
      QBit (by omega : 0 < 10) false i (eVec j) (eVec (ix (by omega : 0 < 10) (j.val + 1))) =
        decide (i = ix (by omega : 0 < 10) (j.val + 1) ∨ i = ix (by omega : 0 < 10) (j.val + 9)) ∧
      QBit (by omega : 0 < 10) true i (eVec j) (eVec (ix (by omega : 0 < 10) (j.val + 1))) =
        decide (i = j ∨ i = ix (by omega : 0 < 10) (j.val + 1) ∨ i = ix (by omega : 0 < 10) (j.val + 2) ∨
                i = ix (by omega : 0 < 10) (j.val + 3) ∨ i = ix (by omega : 0 < 10) (j.val + 4)) ∧
      QBit (by omega : 0 < 10) false i (eVec j) (eVec (ix (by omega : 0 < 10) (j.val + 3))) =
        decide (i = ix (by omega : 0 < 10) (j.val + 1)) ∧
      QBit (by omega : 0 < 10) true i (eVec j) (eVec (ix (by omega : 0 < 10) (j.val + 3))) =
        decide (i = ix (by omega : 0 < 10) (j.val + 2) ∨ i = ix (by omega : 0 < 10) (j.val + 3) ∨
                i = ix (by omega : 0 < 10) (j.val + 4)) := by decide

lemma QBit_indep_10 (a b : Fin 10 → Bool)
    (hz : ∀ p q : Fin 10,
      xor (xorFin (fun i : Fin 10 => a i && QBit (by omega : 0 < 10) false i (eVec p) (eVec q)))
          (xorFin (fun i : Fin 10 => b i && QBit (by omega : 0 < 10) true i (eVec p) (eVec q))) = false) :
    (∀ i, a i = false) ∧ (∀ i, b i = false) := by
  have ha_step : ∀ j : Fin 10, a j = a (ix (by omega) (j.val + 1)) := by
    intro j
    have h := hz j (ix (by omega) (j.val + 2))
    rw [xorFin_eq_false (fun i => b i && QBit (by omega) true i (eVec j) (eVec (ix (by omega) (j.val + 2))))
          (fun i => by rw [(QBit_eval_10 j i).2.1, Bool.and_false]), Bool.xor_false] at h
    have hr : ∀ i : Fin 10, (a i && QBit (by omega) false i (eVec j) (eVec (ix (by omega) (j.val + 2)))) =
        xor (a i && decide (i = j)) (a i && decide (i = ix (by omega) (j.val + 1))) := fun i => by
      rw [(QBit_eval_10 j i).1]
      have hne : j ≠ ix (by omega : 0 < 10) (j.val + 1) := by intro heq; have := congrArg Fin.val heq; dsimp [ix] at this; omega
      by_cases c0 : i = j
      · subst c0; simp [hne]
      · by_cases c1 : i = ix (by omega) (j.val + 1)
        · subst c1; simp [hne.symm]
        · simp [c0, c1]
    rw [xorFin_congr _ _ hr, xorFin_xor, xorFin_single' j, xorFin_single' (ix (by omega) (j.val + 1))] at h
    · simp only [decide_true, Bool.and_true] at h
      cases x : a j <;> cases y : a (ix (by omega) (j.val + 1)) <;> rw [x, y] at h <;> simp at h ⊢
    · intro i hi; simp [hi]
    · intro i hi; simp [hi]
  have ha_const : ∀ i : Fin 10, a i = a 0 := by
    have h0 := ha_step 0; have h1 := ha_step 1; have h2 := ha_step 2
    have h3 := ha_step 3; have h4 := ha_step 4; have h5 := ha_step 5
    have h6 := ha_step 6; have h7 := ha_step 7; have h8 := ha_step 8
    change a 0 = a 1 at h0; change a 1 = a 2 at h1; change a 2 = a 3 at h2
    change a 3 = a 4 at h3; change a 4 = a 5 at h4; change a 5 = a 6 at h5
    change a 6 = a 7 at h6; change a 7 = a 8 at h7; change a 8 = a 9 at h8
    intro i; fin_cases i
    · rfl
    · exact h0.symm
    · exact (h0.trans h1).symm
    · exact ((h0.trans h1).trans h2).symm
    · exact (((h0.trans h1).trans h2).trans h3).symm
    · exact ((((h0.trans h1).trans h2).trans h3).trans h4).symm
    · exact (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).symm
    · exact ((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).symm
    · exact (((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).symm
    · exact ((((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).symm
  have hb_per5 : ∀ j : Fin 10, b (ix (by omega) (j.val + 4)) = b (ix (by omega) (j.val + 9)) := by
    intro j
    have h := hz j (ix (by omega) (j.val + 5))
    rw [xorFin_eq_false (fun i => a i && QBit (by omega) false i (eVec j) (eVec (ix (by omega) (j.val + 5))))
          (fun i => by rw [(QBit_eval_10 j i).2.2.1, Bool.and_false]), Bool.false_xor] at h
    have hr : ∀ i : Fin 10, (b i && QBit (by omega) true i (eVec j) (eVec (ix (by omega) (j.val + 5)))) =
        xor (b i && decide (i = ix (by omega) (j.val + 4))) (b i && decide (i = ix (by omega) (j.val + 9))) := fun i => by
      rw [(QBit_eval_10 j i).2.2.2.1]
      have hne : ix (by omega : 0 < 10) (j.val + 4) ≠ ix (by omega : 0 < 10) (j.val + 9) := by
        intro heq; have := congrArg Fin.val heq; dsimp [ix] at this; omega
      by_cases c0 : i = ix (by omega) (j.val + 4)
      · subst c0; simp [hne]
      · by_cases c1 : i = ix (by omega) (j.val + 9)
        · subst c1; simp [hne.symm]
        · simp [c0, c1]
    rw [xorFin_congr _ _ hr, xorFin_xor, xorFin_single' (ix (by omega) (j.val + 4)), xorFin_single' (ix (by omega) (j.val + 9))] at h
    · simp only [decide_true, Bool.and_true] at h
      cases x : b (ix (by omega) (j.val + 4)) <;> cases y : b (ix (by omega) (j.val + 9)) <;> rw [x, y] at h <;> simp at h ⊢
    · intro i hi; simp [hi]
    · intro i hi; simp [hi]
  have hb5 : b 5 = b 0 ∧ b 6 = b 1 ∧ b 7 = b 2 ∧ b 8 = b 3 ∧ b 9 = b 4 := by
    have p0 := hb_per5 1; have p1 := hb_per5 2; have p2 := hb_per5 3
    have p3 := hb_per5 4; have p4 := hb_per5 5
    change b 5 = b 0 at p0; change b 6 = b 1 at p1; change b 7 = b 2 at p2
    change b 8 = b 3 at p3; change b 9 = b 4 at p4
    exact ⟨p0, p1, p2, p3, p4⟩
  have hsum5 : xor (b 0) (xor (b 1) (xor (b 2) (xor (b 3) (b 4)))) = false := by
    have h := hz 0 1
    have hA0 : xorFin (fun i : Fin 10 => a i && QBit (by omega) false i (eVec 0) (eVec 1)) = false := by
      have hr : ∀ i : Fin 10, (a i && QBit (by omega) false i (eVec 0) (eVec 1)) =
          xor (a i && decide (i = 1)) (a i && decide (i = 9)) := fun i => by
        have he : QBit (by omega : 0 < 10) false i (eVec 0) (eVec 1) = decide (i = 1 ∨ i = 9) :=
          (QBit_eval_10 0 i).2.2.2.2.1
        rw [he]
        by_cases c0 : i = 1
        · subst c0; simp
        · by_cases c1 : i = 9
          · subst c1; simp
          · simp [c0, c1]
      rw [xorFin_congr _ _ hr, xorFin_xor, xorFin_single' 1, xorFin_single' 9]
      · simp [ha_const]
      · intro i hi; simp [hi]
      · intro i hi; simp [hi]
    rw [hA0, Bool.false_xor] at h
    have hB : xorFin (fun i : Fin 10 => b i && QBit (by omega) true i (eVec 0) (eVec 1)) =
        xor (b 0) (xor (b 1) (xor (b 2) (xor (b 3) (b 4)))) := by
      rw [xorFin_congr _ _ (fun i => by
        have he : QBit (by omega : 0 < 10) true i (eVec 0) (eVec 1) =
            decide (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := (QBit_eval_10 0 i).2.2.2.2.2.1
        rw [he])]
      unfold xorFin; have : List.finRange 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl; rw [this]; simp
    rw [hB] at h; exact h
  have hd3 : ∀ j : Fin 5,
      xor (a 0)
          (xor (b (ix (by omega) (j.val + 2))) (xor (b (ix (by omega) (j.val + 3))) (b (ix (by omega) (j.val + 4))))) = false := by
    intro j
    let j10 : Fin 10 := ⟨j.val, by omega⟩
    have h := hz j10 (ix (by omega) (j10.val + 3))
    have hA : xorFin (fun i : Fin 10 => a i && QBit (by omega) false i (eVec j10) (eVec (ix (by omega) (j10.val + 3)))) =
        a 0 := by
      rw [xorFin_single' (ix (by omega) (j10.val + 1))]
      · rw [(QBit_eval_10 j10 _).2.2.2.2.2.2.1, decide_eq_true rfl, Bool.and_true, ha_const]
      · intro i hi; rw [(QBit_eval_10 j10 i).2.2.2.2.2.2.1, decide_eq_false hi, Bool.and_false]
    have hB : xorFin (fun i : Fin 10 => b i && QBit (by omega) true i (eVec j10) (eVec (ix (by omega) (j10.val + 3)))) =
        xor (b (ix (by omega) (j.val + 2))) (xor (b (ix (by omega) (j.val + 3))) (b (ix (by omega) (j.val + 4)))) := by
      rw [xorFin_congr _ _ (fun i => by rw [(QBit_eval_10 j10 i).2.2.2.2.2.2.2])]
      unfold xorFin; have : List.finRange 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl; rw [this]
      fin_cases j <;> simp [j10, ix]
    rw [hA, hB] at h; exact h
  have e0 := hd3 0; have e1 := hd3 1; have e2 := hd3 2; have e3 := hd3 3; have e4 := hd3 4
  change xor (a 0) (xor (b 2) (xor (b 3) (b 4))) = false at e0
  change xor (a 0) (xor (b 3) (xor (b 4) (b 5))) = false at e1
  change xor (a 0) (xor (b 4) (xor (b 5) (b 6))) = false at e2
  change xor (a 0) (xor (b 5) (xor (b 6) (b 7))) = false at e3
  change xor (a 0) (xor (b 6) (xor (b 7) (b 8))) = false at e4
  simp only [hb5.1, hb5.2.1, hb5.2.2.1, hb5.2.2.2.1] at e0 e1 e2 e3 e4
  have hsol10 : ∀ A b0 b1 b2 b3 b4 : Bool,
      xor b0 (xor b1 (xor b2 (xor b3 b4))) = false →
      xor A (xor b2 (xor b3 b4)) = false → xor A (xor b3 (xor b4 b0)) = false →
      xor A (xor b4 (xor b0 b1)) = false → xor A (xor b0 (xor b1 b2)) = false →
      xor A (xor b1 (xor b2 b3)) = false →
      A = false ∧ b0 = false ∧ b1 = false ∧ b2 = false ∧ b3 = false ∧ b4 = false := by
    intro A b0 b1 b2 b3 b4; cases A <;> cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> simp
  rcases hsol10 (a 0) (b 0) (b 1) (b 2) (b 3) (b 4) hsum5 e0 e1 e2 e3 e4 with ⟨hA, hb0, hb1, hb2, hb3, hb4⟩
  exact ⟨fun i => by rw [ha_const i, hA], fun i => by fin_cases i <;> simp [hb5, hb0, hb1, hb2, hb3, hb4]⟩

lemma QBit_indep {k : Nat} (hk : 0 < k) (hk5 : 5 ≤ k) (hk6 : k ≠ 6)
    (a b : Fin k → Bool)
    (hz : ∀ p q : Fin k,
      xor (xorFin (fun i : Fin k => a i && QBit hk false i (eVec p) (eVec q)))
          (xorFin (fun i : Fin k => b i && QBit hk true i (eVec p) (eVec q))) = false) :
    (∀ i, a i = false) ∧ (∀ i, b i = false) := by
  by_cases h5 : k = 5
  · subst h5; exact QBit_indep_5 a b hz
  · by_cases h7 : k = 7
    · subst h7; exact QBit_indep_7 a b hz
    · by_cases h8 : k = 8
      · subst h8; exact QBit_indep_8 a b hz
      · by_cases h10 : k = 10
        · subst h10; exact QBit_indep_10 a b hz
        · have hk9 : 9 ≤ k := by omega
          have hb0 : ∀ j : Fin k, b j = false := by
            intro j
            have h := hz (ix hk (j.val + k - 4)) (ix hk (j.val + 1))
            rw [xorFin_eq_false (fun i => a i && QBit hk false i (eVec (ix hk (j.val + k - 4))) (eVec (ix hk (j.val + 1))))
                  (fun i => by rw [QBit_false_dist5 hk hk9 i j, Bool.and_false]),
                Bool.false_xor] at h
            rw [xorFin_single' j] at h
            · rw [QBit_true_dist5 hk hk9 h10 j j, decide_eq_true rfl, Bool.and_true] at h; exact h
            · intro i hi; rw [QBit_true_dist5 hk hk9 h10 i j, decide_eq_false hi, Bool.and_false]
          have ha0 : ∀ j : Fin k, a j = false := by
            intro j
            have h := hz (ix hk (j.val + k - 1)) (ix hk (j.val + 2))
            rw [xorFin_eq_false (fun i => b i && QBit hk true i (eVec (ix hk (j.val + k - 1))) (eVec (ix hk (j.val + 2))))
                  (fun i => by rw [hb0 i, Bool.false_and]),
                Bool.xor_false] at h
            rw [xorFin_single' j] at h
            · rw [QBit_false_dist3 hk (by omega) j j, decide_eq_true rfl, Bool.and_true] at h; exact h
            · intro i hi; rw [QBit_false_dist3 hk (by omega) i j, decide_eq_false hi, Bool.and_false]
          exact ⟨ha0, hb0⟩

lemma group_span_card {k a : Nat} (hk : 0 < k) (col : Bool) (i : Fin k)
    (name : Fin a → Fin k → Bool) (P : Fin a → Bool) :
    ∃ (G : Finset (Fin k → Bool)),
      G.card ≤ 2 ^ (min ((Finset.univ.filter (fun l : Fin a => P l = true)).card - 1) 2) ∧
      ∀ (γ : Fin a → Bool),
        xorFin (fun l : Fin a => P l && γ l) = false →
        ∃ w ∈ G, ∀ x : Fin k → Bool,
          xorFin (fun l : Fin a => (P l && γ l) && readBit hk col (name l) x i) =
          xor (xorFin (fun l : Fin a => (P l && γ l) && readBit hk col (name l) (fun _ => false) i))
              (dot w x) := by
  let S := Finset.univ.filter (fun l : Fin a => P l = true)
  by_cases hs0 : S.card ≤ 1
  ·
    refine ⟨{fun _ => false}, by rw [Finset.card_singleton]; exact Nat.one_le_two_pow, fun γ heven => ?_⟩
    refine ⟨fun _ => false, Finset.mem_singleton_self _, fun x => ?_⟩
    rw [dot_zero_left, Bool.xor_false]
    have hall0 : ∀ l : Fin a, (P l && γ l) = false := by
      intro l
      by_cases hpl : P l = true
      · have hlS : l ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩
        have hsing : ∀ l' : Fin a, l' ≠ l → (P l' && γ l') = false := fun l' hne => by
          by_cases hpl' : P l' = true
          · exfalso
            have hl'S : l' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl'⟩
            have h2 : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨l, hlS, l', hl'S, hne.symm⟩
            omega
          · have hpf : P l' = false := Bool.eq_false_iff.mpr hpl'
            rw [hpf, Bool.false_and]
        rw [xorFin_single' l _ hsing] at heven
        exact heven
      · have hpf : P l = false := Bool.eq_false_iff.mpr hpl
        rw [hpf, Bool.false_and]
    rw [xorFin_eq_false _ (fun l => by rw [hall0 l, Bool.false_and]),
        xorFin_eq_false _ (fun l => by rw [hall0 l, Bool.false_and])]
  · by_cases hs2 : S.card = 2
    ·
      rcases Finset.card_eq_two.mp hs2 with ⟨l0, l1, hne, hSeq⟩
      let d := if col then 2 else 1
      let Δ := mix hk d (add (name l0) (name l1))
      let w01 : Fin k → Bool := fun p =>
        xor (Δ (ix hk (i.val + 1)) && R0Vec hk col (ix hk (i.val + 2)) p)
            (Δ (ix hk (i.val + 2)) && R0Vec hk col (ix hk (i.val + 1)) p)
      let G : Finset (Fin k → Bool) := {fun _ => false, w01}
      have hcard : G.card ≤ 2 ^ (min (S.card - 1) 2) := by
        rw [hs2]; exact Finset.card_le_two
      refine ⟨G, hcard, fun γ heven => ?_⟩
      have hl0S : P l0 = true := by
        have hm : l0 ∈ S := by rw [hSeq]; exact Finset.mem_insert_self l0 {l1}
        exact (Finset.mem_filter.mp hm).2
      have hl1S : P l1 = true := by
        have hm : l1 ∈ S := by rw [hSeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self l1)
        exact (Finset.mem_filter.mp hm).2
      have hother : ∀ l : Fin a, l ≠ l0 → l ≠ l1 → P l = false := fun l h0 h1 => by
        by_contra hne_f
        have hpt : P l = true := Bool.eq_true_of_not_eq_false hne_f
        have hm : l ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpt⟩
        rw [hSeq] at hm; simp [h0, h1] at hm
      have hpair_xor : ∀ f : Fin a → Bool,
          (∀ l, l ≠ l0 → l ≠ l1 → f l = false) →
          xorFin f = xor (f l0) (f l1) := fun f hf => by
        rw [xorFin_split_pred (fun l => decide (l = l0))]
        have hA : xorFin (fun l => decide (l = l0) && f l) = f l0 := by
          rw [xorFin_single' l0]; · simp
          · intro l hl; simp [hl]
        have hB : xorFin (fun l => !(decide (l = l0)) && f l) = f l1 := by
          rw [xorFin_single' l1]
          · simp [hne.symm]
          · intro l hl
            by_cases hl0 : l = l0
            · simp [hl0]
            · rw [hf l hl0 hl, Bool.and_false]
        rw [hA, hB]
      have hge : γ l0 = γ l1 := by
        have h1 := hpair_xor (fun l => P l && γ l) (fun l h0 h1 => by rw [hother l h0 h1, Bool.false_and])
        rw [h1, hl0S, hl1S, Bool.true_and, Bool.true_and] at heven
        cases ha : γ l0 <;> cases hb : γ l1 <;> rw [ha, hb] at heven <;> simp at heven ⊢
      cases hg0 : γ l0
      · have hg1 : γ l1 = false := by rw [← hge, hg0]
        refine ⟨fun _ => false, Finset.mem_insert_self _ _, fun x => ?_⟩
        rw [dot_zero_left, Bool.xor_false]
        have hz : ∀ l, (P l && γ l) = false := fun l => by
          by_cases h0 : l = l0
          · subst h0; rw [hg0, Bool.and_false]
          · by_cases h1 : l = l1
            · subst h1; rw [hg1, Bool.and_false]
            · rw [hother l h0 h1, Bool.false_and]
        rw [xorFin_eq_false _ (fun l => by rw [hz l, Bool.false_and]),
            xorFin_eq_false _ (fun l => by rw [hz l, Bool.false_and])]
      · have hg1 : γ l1 = true := by rw [← hge, hg0]
        refine ⟨w01, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), fun x => ?_⟩
        rw [hpair_xor (fun l => (P l && γ l) && readBit hk col (name l) x i)
              (fun l h0 h1 => by rw [hother l h0 h1, Bool.false_and, Bool.false_and]),
            hpair_xor (fun l => (P l && γ l) && readBit hk col (name l) (fun _ => false) i)
              (fun l h0 h1 => by rw [hother l h0 h1, Bool.false_and, Bool.false_and])]
        rw [hl0S, hl1S, hg0, hg1, Bool.true_and, Bool.true_and, Bool.true_and, Bool.true_and]
        rw [readBit_diff hk col (name l0) (name l1) x i]
        congr 1
        have hsc : ∀ (c : Bool) (w : Fin k → Bool), dot (fun p => c && w p) x = (c && dot w x) := fun c w => by
          unfold dot; rw [← xorFin_and_left]; apply xorFin_congr; intro p; exact Bool.and_assoc _ _ _
        dsimp only [w01, Δ, d]
        rw [dot_xor_left, hsc, hsc, R0_eq_dot, R0_eq_dot]
    ·
      have hs3 : 3 ≤ S.card := by omega
      let wA := R0Vec hk col (ix hk (i.val + 1))
      let wB := R0Vec hk col (ix hk (i.val + 2))
      let G : Finset (Fin k → Bool) :=
        Finset.univ.image (fun ab : Bool × Bool => fun p => xor (ab.1 && wA p) (ab.2 && wB p))
      have hcard : G.card ≤ 2 ^ (min (S.card - 1) 2) := by
        have hmin : min (S.card - 1) 2 = 2 := by omega
        rw [hmin]
        calc G.card ≤ (Finset.univ : Finset (Bool × Bool)).card := Finset.card_image_le
          _ = 4 := rfl
      refine ⟨G, hcard, fun γ heven => ?_⟩

      let d := if col then 2 else 1
      let c1 : Bool := xorFin (fun l : Fin a => (P l && γ l) && mix hk d (name l) (ix hk (i.val + 2)))
      let c2 : Bool := xorFin (fun l : Fin a => (P l && γ l) && mix hk d (name l) (ix hk (i.val + 1)))
      refine ⟨fun p => xor (c1 && wA p) (c2 && wB p),
        Finset.mem_image.mpr ⟨(c1, c2), Finset.mem_univ _, rfl⟩, fun x => ?_⟩
      have hbase : xorFin (fun l : Fin a => (P l && γ l) && readBit hk col (fun _ => false) x i) = false := by
        rw [xorFin_and_right, heven, Bool.false_and]
      have hcomb : xorFin (fun l : Fin a => (P l && γ l) && readBit hk col (name l) x i) =
          xorFin (fun l : Fin a => (P l && γ l) && xor (readBit hk col (fun _ => false) x i) (readBit hk col (name l) x i)) := by
        conv_lhs => rw [← Bool.false_xor (xorFin (fun l => (P l && γ l) && readBit hk col (name l) x i)), ← hbase, ← xorFin_xor]
        have hdist : ∀ a b c : Bool, xor (a && b) (a && c) = (a && xor b c) := by decide
        apply xorFin_congr; intro l; exact hdist _ _ _
      rw [hcomb]
      have hrew : ∀ l : Fin a,
          ((P l && γ l) && xor (readBit hk col (fun _ => false) x i) (readBit hk col (name l) x i)) =
          xor ((P l && γ l) && readBit hk col (name l) (fun _ => false) i)
              (xor (((P l && γ l) && mix hk d (name l) (ix hk (i.val + 1))) && R0 hk col x (ix hk (i.val + 2)))
                   (((P l && γ l) && mix hk d (name l) (ix hk (i.val + 2))) && R0 hk col x (ix hk (i.val + 1)))) := fun l => by
        dsimp only [d]; rw [readBit_diff_zero hk col (name l) x i]
        cases P l <;> cases γ l <;> simp
      rw [xorFin_congr _ _ hrew, xorFin_xor, xorFin_xor, xorFin_and_right, xorFin_and_right]
      congr 1
      rw [dot_xor_left, R0_eq_dot, R0_eq_dot]
      have hdotA : dot (fun p => c1 && wA p) x = (c1 && dot wA x) := by
        unfold dot; rw [← xorFin_and_left]; apply xorFin_congr; intro p; exact Bool.and_assoc _ _ _
      have hdotB : dot (fun p => c2 && wB p) x = (c2 && dot wB x) := by
        unfold dot; rw [← xorFin_and_left]; apply xorFin_congr; intro p; exact Bool.and_assoc _ _ _
      rw [hdotA, hdotB, Bool.xor_comm]

lemma linear_from_dot {k : Nat} (w : Fin k → Bool) (c : Bool) (f : (Fin k → Bool) → Bool)
    (h : ∀ y, dot w y = xor c (f y)) :
    (∀ a b, pol f a b = false) ∧
    (∀ y, f y = xor (f (fun _ => false)) (dot w y)) := by
  have hc : c = f (fun _ => false) := by
    have h0 := h (fun _ => false)
    rw [dot_zero_right] at h0
    revert h0; cases c <;> cases f (fun _ => false) <;> simp
  refine ⟨fun a b => ?_, fun y => ?_⟩
  · have hf : f = fun y => xor c (dot w y) := by
      funext y; have hy := h y; revert hy; cases dot w y <;> cases c <;> cases f y <;> simp
    rw [hf]; exact pol_affine ⟨c, w, fun _ => rfl⟩ a b
  · have hy := h y; rw [← hc]; revert hy; cases dot w y <;> cases c <;> cases f y <;> simp

lemma even_parity_per_site {k a n : Nat} (hk : 0 < k) (hk5 : 5 ≤ k) (hk6 : k ≠ 6)
    (bank : Fin a → Bool) (key : Fin a → Fin n) (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
    (j : Fin n) (γ : Fin a → Bool)
    (hpol0 : ∀ x y : Fin k → Bool,
      pol (fun z => xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (name l) z (site l))) x y = false) :
    ∀ (col : Bool) (i : Fin k),
      xorFin (fun l : Fin a => decide (key l = j ∧ bank l = col ∧ site l = i) && γ l) = false := by
  let aa : Fin k → Bool := fun i => xorFin (fun l : Fin a => decide (key l = j ∧ bank l = false ∧ site l = i) && γ l)
  let bb : Fin k → Bool := fun i => xorFin (fun l : Fin a => decide (key l = j ∧ bank l = true ∧ site l = i) && γ l)
  have hpol_eq : ∀ p q : Fin k,
      xor (xorFin (fun i : Fin k => aa i && QBit hk false i (eVec p) (eVec q)))
          (xorFin (fun i : Fin k => bb i && QBit hk true i (eVec p) (eVec q))) = false := by
    intro p q
    have h0 := hpol0 (eVec p) (eVec q)
    rw [pol_xorFin] at h0
    have hterm : ∀ l : Fin a,
        pol (fun z => (decide (key l = j) && γ l) && readBit hk (bank l) (name l) z (site l)) (eVec p) (eVec q) =
        ((decide (key l = j) && γ l) && QBit hk (bank l) (site l) (eVec p) (eVec q)) := fun l => by
      rw [pol_and_const, pol_readBit]
    rw [xorFin_congr _ _ hterm] at h0
    have hsplit : xorFin (fun l : Fin a => (decide (key l = j) && γ l) && QBit hk (bank l) (site l) (eVec p) (eVec q)) =
        xor (xorFin (fun i : Fin k => aa i && QBit hk false i (eVec p) (eVec q)))
            (xorFin (fun i : Fin k => bb i && QBit hk true i (eVec p) (eVec q))) := by
      have hA : xorFin (fun i : Fin k => aa i && QBit hk false i (eVec p) (eVec q)) =
          xorFin (fun l : Fin a => (decide (key l = j ∧ bank l = false) && γ l) && QBit hk false (site l) (eVec p) (eVec q)) := by
        have h1 : ∀ i, (aa i && QBit hk false i (eVec p) (eVec q)) =
            xorFin (fun l : Fin a => (decide (key l = j ∧ bank l = false ∧ site l = i) && γ l) && QBit hk false i (eVec p) (eVec q)) :=
          fun i => (xorFin_and_right _ _).symm
        rw [xorFin_congr _ _ h1, xorFin_swap]
        apply xorFin_congr; intro l
        rw [xorFin_single' (site l)]
        · by_cases hkj : key l = j ∧ bank l = false
          · simp [hkj]
          · simp [hkj]
        · intro i hi
          have hf : ¬(key l = j ∧ bank l = false ∧ site l = i) := fun h => hi h.2.2.symm
          rw [decide_eq_false hf, Bool.false_and, Bool.false_and]
      have hB : xorFin (fun i : Fin k => bb i && QBit hk true i (eVec p) (eVec q)) =
          xorFin (fun l : Fin a => (decide (key l = j ∧ bank l = true) && γ l) && QBit hk true (site l) (eVec p) (eVec q)) := by
        have h1 : ∀ i, (bb i && QBit hk true i (eVec p) (eVec q)) =
            xorFin (fun l : Fin a => (decide (key l = j ∧ bank l = true ∧ site l = i) && γ l) && QBit hk true i (eVec p) (eVec q)) :=
          fun i => (xorFin_and_right _ _).symm
        rw [xorFin_congr _ _ h1, xorFin_swap]
        apply xorFin_congr; intro l
        rw [xorFin_single' (site l)]
        · by_cases hkj : key l = j ∧ bank l = true
          · simp [hkj]
          · simp [hkj]
        · intro i hi
          have hf : ¬(key l = j ∧ bank l = true ∧ site l = i) := fun h => hi h.2.2.symm
          rw [decide_eq_false hf, Bool.false_and, Bool.false_and]
      rw [hA, hB, ← xorFin_xor]
      apply xorFin_congr; intro l
      cases bank l <;> by_cases hkj : key l = j <;> simp [hkj]
    rw [← hsplit]; exact h0
  rcases QBit_indep hk hk5 hk6 aa bb hpol_eq with ⟨ha0, hb0⟩
  intro col i
  cases col
  · exact ha0 i
  · exact hb0 i

lemma key_group_bound {k a n : Nat} (hk : 0 < k) (hk5 : 5 ≤ k) (hk6 : k ≠ 6)
    (bank : Fin a → Bool) (key : Fin a → Fin n) (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
    (j : Fin n) :
    let a_j := (Finset.univ.filter (fun l : Fin a => key l = j)).card
    ∃ (S_j : Finset (Fin k → Bool)) (B_j : Nat),
      S_j.card ≤ 2 ^ B_j ∧ 3 * B_j ≤ 2 * a_j ∧
      ∀ (w : Fin k → Bool),
        (∃ (γ : Fin a → Bool) (c : Bool),
          ∀ (y : Fin k → Bool),
            dot w y = xor c (xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (name l) y (site l)))) →
        w ∈ S_j := by
  intro a_j
  let P : Bool × Fin k → Fin a → Bool := fun ci l => decide (key l = j ∧ bank l = ci.1 ∧ site l = ci.2)
  have hgrp : ∀ ci : Bool × Fin k,
      ∃ (G : Finset (Fin k → Bool)),
        G.card ≤ 2 ^ (min ((Finset.univ.filter (fun l : Fin a => P ci l = true)).card - 1) 2) ∧
        ∀ (γ : Fin a → Bool),
          xorFin (fun l : Fin a => P ci l && γ l) = false →
          ∃ w ∈ G, ∀ x : Fin k → Bool,
            xorFin (fun l : Fin a => (P ci l && γ l) && readBit hk ci.1 (name l) x ci.2) =
            xor (xorFin (fun l : Fin a => (P ci l && γ l) && readBit hk ci.1 (name l) (fun _ => false) ci.2))
                (dot w x) := fun ci => group_span_card hk ci.1 ci.2 name (P ci)
  choose G hG_card hG_mem using hgrp
  let sumVec : ((Bool × Fin k) → Fin k → Bool) → (Fin k → Bool) :=
    fun ws p => xor (xorFin (fun i : Fin k => ws (false, i) p)) (xorFin (fun i : Fin k => ws (true, i) p))
  let S_j : Finset (Fin k → Bool) := (Fintype.piFinset G).image sumVec
  let B_j : Nat := ∑ ci : Bool × Fin k, min ((Finset.univ.filter (fun l : Fin a => P ci l = true)).card - 1) 2
  have hSj_card : S_j.card ≤ 2 ^ B_j := by
    calc S_j.card ≤ (Fintype.piFinset G).card := Finset.card_image_le
      _ = ∏ ci : Bool × Fin k, (G ci).card := Fintype.card_piFinset G
      _ ≤ ∏ ci : Bool × Fin k, 2 ^ (min ((Finset.univ.filter (fun l : Fin a => P ci l = true)).card - 1) 2) :=
        Finset.prod_le_prod (fun ci _ => hG_card ci)
      _ = 2 ^ B_j := by rw [Finset.prod_pow_eq_pow_sum]
  have h3B : 3 * B_j ≤ 2 * a_j := by
    have hsum_s : ∑ ci : Bool × Fin k, (Finset.univ.filter (fun l : Fin a => P ci l = true)).card = a_j := by
      have hpart := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter (fun l : Fin a => key l = j))
        (f := fun l : Fin a => (bank l, site l)) (t := (Finset.univ : Finset (Bool × Fin k)))
        (fun _ _ => Finset.mem_univ _)
      dsimp only [a_j]; rw [hpart]
      apply Finset.sum_congr rfl; intro ci _
      congr 1; ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, decide_eq_true_eq, Prod.ext_iff]
    calc 3 * B_j = ∑ ci : Bool × Fin k, 3 * min ((Finset.univ.filter (fun l : Fin a => P ci l = true)).card - 1) 2 := by
          rw [Finset.mul_sum]
      _ ≤ ∑ ci : Bool × Fin k, 2 * (Finset.univ.filter (fun l : Fin a => P ci l = true)).card := by
          apply Finset.sum_le_sum; intro ci _; omega
      _ = 2 * ∑ ci : Bool × Fin k, (Finset.univ.filter (fun l : Fin a => P ci l = true)).card := by
          rw [Finset.mul_sum]
      _ = 2 * a_j := by rw [hsum_s]
  refine ⟨S_j, B_j, hSj_card, h3B, fun w hw => ?_⟩
  rcases hw with ⟨γ, c, hγ⟩
  rcases linear_from_dot w c _ hγ with ⟨hpol0, hlin⟩
  have heven := even_parity_per_site hk hk5 hk6 bank key name site j γ hpol0
  have hpick : ∀ ci : Bool × Fin k, ∃ wg ∈ G ci, ∀ x : Fin k → Bool,
      xorFin (fun l : Fin a => (P ci l && γ l) && readBit hk ci.1 (name l) x ci.2) =
      xor (xorFin (fun l : Fin a => (P ci l && γ l) && readBit hk ci.1 (name l) (fun _ => false) ci.2))
          (dot wg x) := fun ci => hG_mem ci γ (heven ci.1 ci.2)
  choose ws hws_mem hws_eq using hpick

  have hdecomp : ∀ x : Fin k → Bool,
      xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (name l) x (site l)) =
      xor (xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (false, i) l && γ l) && readBit hk false (name l) x i)))
          (xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (true, i) l && γ l) && readBit hk true (name l) x i))) := by
    intro x
    rw [xorFin_swap (fun i l => (P (false, i) l && γ l) && readBit hk false (name l) x i),
        xorFin_swap (fun i l => (P (true, i) l && γ l) && readBit hk true (name l) x i),
        ← xorFin_xor]
    apply xorFin_congr; intro l
    have hF : xorFin (fun i : Fin k => (P (false, i) l && γ l) && readBit hk false (name l) x i) =
        ((decide (key l = j ∧ bank l = false) && γ l) && readBit hk false (name l) x (site l)) := by
      rw [xorFin_single' (site l)]
      · by_cases hkj : key l = j ∧ bank l = false <;> simp [P, hkj]
      · intro i hi; have hf : ¬(key l = j ∧ bank l = false ∧ site l = i) := fun h => hi h.2.2.symm
        simp [P, hf]
    have hT : xorFin (fun i : Fin k => (P (true, i) l && γ l) && readBit hk true (name l) x i) =
        ((decide (key l = j ∧ bank l = true) && γ l) && readBit hk true (name l) x (site l)) := by
      rw [xorFin_single' (site l)]
      · by_cases hkj : key l = j ∧ bank l = true <;> simp [P, hkj]
      · intro i hi; have hf : ¬(key l = j ∧ bank l = true ∧ site l = i) := fun h => hi h.2.2.symm
        simp [P, hf]
    rw [hF, hT]
    cases bank l <;> by_cases hkj : key l = j <;> simp [hkj]

  have hw_eq : w = sumVec ws := by
    funext p
    have h1 := hlin (eVec p)
    rw [dot_eVec] at h1
    have h2 : xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (name l) (eVec p) (site l)) =
        xor (xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (name l) (fun _ => false) (site l)))
            (sumVec ws p) := by
      rw [hdecomp (eVec p), hdecomp (fun _ => false)]
      rw [xorFin_congr _ _ (fun i => hws_eq (false, i) (eVec p)),
          xorFin_congr _ _ (fun i => hws_eq (true, i) (eVec p)),
          xorFin_xor, xorFin_xor]
      have hdF : xorFin (fun i : Fin k => dot (ws (false, i)) (eVec p)) = xorFin (fun i : Fin k => ws (false, i) p) :=
        xorFin_congr _ _ (fun i => dot_eVec _ p)
      have hdT : xorFin (fun i : Fin k => dot (ws (true, i)) (eVec p)) = xorFin (fun i : Fin k => ws (true, i) p) :=
        xorFin_congr _ _ (fun i => dot_eVec _ p)
      rw [hdF, hdT]; dsimp only [sumVec]
      cases xorFin (fun i => xorFin (fun l => (P (false, i) l && γ l) && readBit hk false (name l) (fun _ => false) i)) <;>
        cases xorFin (fun i => xorFin (fun l => (P (true, i) l && γ l) && readBit hk true (name l) (fun _ => false) i)) <;>
        cases xorFin (fun i => ws (false, i) p) <;> cases xorFin (fun i => ws (true, i) p) <;> rfl
    rw [h2] at h1
    cases hA : xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (name l) (fun _ => false) (site l)) <;>
      cases hB : sumVec ws p <;> cases hW : w p <;> rw [hA, hB, hW] at h1 <;> simp at h1 ⊢
  rw [hw_eq]
  exact Finset.mem_image.mpr ⟨ws, Fintype.mem_piFinset.mpr hws_mem, rfl⟩

lemma key_in_resSum_subspace {k a n : Nat} (hk : 0 < k) (hk9 : 9 ≤ k) (h3 : 3 ∣ k)
    (bank : Fin a → Bool) (key : Fin a → Fin n) (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
    (j : Fin n) (w : Fin k → Bool)
    (hw : ∃ (γ : Fin a → Bool) (c : Bool),
      ∀ (y : Fin k → Bool),
        dot w y = xor c (xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (name l) y (site l)))) :
    resSum w 0 = resSum w 1 ∧ resSum w 1 = resSum w 2 := by
  rcases hw with ⟨γ, c, hγ⟩
  rcases linear_from_dot w c _ hγ with ⟨hpol0, hlin⟩
  have heven := even_parity_per_site hk (by omega) (by omega) bank key name site j γ hpol0
  let P : Bool × Fin k → Fin a → Bool := fun ci l => decide (key l = j ∧ bank l = ci.1 ∧ site l = ci.2)

  let c1 : Bool × Fin k → Bool := fun ci =>
    xorFin (fun l : Fin a => (P ci l && γ l) && mix hk (if ci.1 then 2 else 1) (name l) (ix hk (ci.2.val + 2)))
  let c2 : Bool × Fin k → Bool := fun ci =>
    xorFin (fun l : Fin a => (P ci l && γ l) && mix hk (if ci.1 then 2 else 1) (name l) (ix hk (ci.2.val + 1)))
  let wExp : Fin k → Bool := fun p =>
    xor (xorFin (fun i : Fin k => xor (c1 (false, i) && R0Vec hk false (ix hk (i.val + 1)) p)
                                      (c2 (false, i) && R0Vec hk false (ix hk (i.val + 2)) p)))
        (xorFin (fun i : Fin k => xor (c1 (true, i) && R0Vec hk true (ix hk (i.val + 1)) p)
                                      (c2 (true, i) && R0Vec hk true (ix hk (i.val + 2)) p)))
  have hgroup : ∀ (col : Bool) (i : Fin k) (x : Fin k → Bool),
      xorFin (fun l : Fin a => (P (col, i) l && γ l) && readBit hk col (name l) x i) =
      xor (xorFin (fun l : Fin a => (P (col, i) l && γ l) && readBit hk col (name l) (fun _ => false) i))
          (xor (c1 (col, i) && R0 hk col x (ix hk (i.val + 1)))
               (c2 (col, i) && R0 hk col x (ix hk (i.val + 2)))) := by
    intro col i x
    have hbase : xorFin (fun l : Fin a => (P (col, i) l && γ l) && readBit hk col (fun _ => false) x i) = false := by
      rw [xorFin_and_right, heven col i, Bool.false_and]
    have hcomb : xorFin (fun l : Fin a => (P (col, i) l && γ l) && readBit hk col (name l) x i) =
        xorFin (fun l : Fin a => (P (col, i) l && γ l) && xor (readBit hk col (fun _ => false) x i) (readBit hk col (name l) x i)) := by
      conv_lhs => rw [← Bool.false_xor (xorFin (fun l => (P (col, i) l && γ l) && readBit hk col (name l) x i)), ← hbase, ← xorFin_xor]
      have hdist : ∀ a b c : Bool, xor (a && b) (a && c) = (a && xor b c) := by decide
      apply xorFin_congr; intro l; exact hdist _ _ _
    rw [hcomb]
    have hrew : ∀ l : Fin a,
        ((P (col, i) l && γ l) && xor (readBit hk col (fun _ => false) x i) (readBit hk col (name l) x i)) =
        xor ((P (col, i) l && γ l) && readBit hk col (name l) (fun _ => false) i)
            (xor (((P (col, i) l && γ l) && mix hk (if col then 2 else 1) (name l) (ix hk (i.val + 2))) && R0 hk col x (ix hk (i.val + 1)))
                 (((P (col, i) l && γ l) && mix hk (if col then 2 else 1) (name l) (ix hk (i.val + 1))) && R0 hk col x (ix hk (i.val + 2)))) := fun l => by
      rw [readBit_diff_zero hk col (name l) x i]
      cases P (col, i) l <;> cases γ l <;> simp [Bool.xor_comm]
    rw [xorFin_congr _ _ hrew, xorFin_xor, xorFin_xor, xorFin_and_right, xorFin_and_right]
  have hdecomp : ∀ x : Fin k → Bool,
      xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (name l) x (site l)) =
      xor (xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (false, i) l && γ l) && readBit hk false (name l) x i)))
          (xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (true, i) l && γ l) && readBit hk true (name l) x i))) := by
    intro x
    rw [xorFin_swap (fun i l => (P (false, i) l && γ l) && readBit hk false (name l) x i),
        xorFin_swap (fun i l => (P (true, i) l && γ l) && readBit hk true (name l) x i),
        ← xorFin_xor]
    apply xorFin_congr; intro l
    have hF : xorFin (fun i : Fin k => (P (false, i) l && γ l) && readBit hk false (name l) x i) =
        ((decide (key l = j ∧ bank l = false) && γ l) && readBit hk false (name l) x (site l)) := by
      rw [xorFin_single' (site l)]
      · by_cases hkj : key l = j ∧ bank l = false <;> simp [P, hkj]
      · intro i hi; have hf : ¬(key l = j ∧ bank l = false ∧ site l = i) := fun h => hi h.2.2.symm
        simp [P, hf]
    have hT : xorFin (fun i : Fin k => (P (true, i) l && γ l) && readBit hk true (name l) x i) =
        ((decide (key l = j ∧ bank l = true) && γ l) && readBit hk true (name l) x (site l)) := by
      rw [xorFin_single' (site l)]
      · by_cases hkj : key l = j ∧ bank l = true <;> simp [P, hkj]
      · intro i hi; have hf : ¬(key l = j ∧ bank l = true ∧ site l = i) := fun h => hi h.2.2.symm
        simp [P, hf]
    rw [hF, hT]
    cases bank l <;> by_cases hkj : key l = j <;> simp [hkj]
  have hw_eq : w = wExp := by
    funext p
    have h1 := hlin (eVec p)
    rw [dot_eVec] at h1
    have h2 : xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (name l) (eVec p) (site l)) =
        xor (xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (name l) (fun _ => false) (site l)))
            (wExp p) := by
      rw [hdecomp (eVec p), hdecomp (fun _ => false)]
      have hF_rw : xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (false, i) l && γ l) && readBit hk false (name l) (eVec p) i)) =
          xor (xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (false, i) l && γ l) && readBit hk false (name l) (fun _ => false) i)))
              (xorFin (fun i : Fin k => xor (c1 (false, i) && R0 hk false (eVec p) (ix hk (i.val + 1)))
                                            (c2 (false, i) && R0 hk false (eVec p) (ix hk (i.val + 2))))) := by
        rw [xorFin_congr _ _ (fun i => hgroup false i (eVec p)), xorFin_xor]
      have hT_rw : xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (true, i) l && γ l) && readBit hk true (name l) (eVec p) i)) =
          xor (xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (true, i) l && γ l) && readBit hk true (name l) (fun _ => false) i)))
              (xorFin (fun i : Fin k => xor (c1 (true, i) && R0 hk true (eVec p) (ix hk (i.val + 1)))
                                            (c2 (true, i) && R0 hk true (eVec p) (ix hk (i.val + 2))))) := by
        rw [xorFin_congr _ _ (fun i => hgroup true i (eVec p)), xorFin_xor]
      rw [hF_rw, hT_rw]
      dsimp only [wExp, R0Vec]
      cases xorFin (fun i => xorFin (fun l => (P (false, i) l && γ l) && readBit hk false (name l) (fun _ => false) i)) <;>
        cases xorFin (fun i => xorFin (fun l => (P (true, i) l && γ l) && readBit hk true (name l) (fun _ => false) i)) <;>
        cases xorFin (fun i => xor (c1 (false, i) && R0 hk false (eVec p) (ix hk (i.val + 1))) (c2 (false, i) && R0 hk false (eVec p) (ix hk (i.val + 2)))) <;>
        cases xorFin (fun i => xor (c1 (true, i) && R0 hk true (eVec p) (ix hk (i.val + 1))) (c2 (true, i) && R0 hk true (eVec p) (ix hk (i.val + 2)))) <;> rfl
    rw [h2] at h1
    cases hA : xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (name l) (fun _ => false) (site l)) <;>
      cases hB : wExp p <;> cases hW : w p <;> rw [hA, hB, hW] at h1 <;> simp at h1 ⊢

  have hrc : ∀ c : Nat, c < 3 →
      resSum wExp c =
      xor (xorFin (fun i : Fin k => xor (c1 (false, i)) (c2 (false, i))))
          (xorFin (fun i : Fin k => xor (c1 (true, i)) (c2 (true, i)))) := by
    intro c hc
    dsimp only [wExp]
    rw [resSum_xor, resSum_xorFin, resSum_xorFin]
    congr 1
    · apply xorFin_congr; intro i
      rw [resSum_xor, resSum_and_const, resSum_and_const,
          resSum_R0Vec_eq hk h3 (by omega) false _ c hc,
          resSum_R0Vec_eq hk h3 (by omega) false _ c hc, Bool.and_true, Bool.and_true]
    · apply xorFin_congr; intro i
      rw [resSum_xor, resSum_and_const, resSum_and_const,
          resSum_R0Vec_eq hk h3 (by omega) true _ c hc,
          resSum_R0Vec_eq hk h3 (by omega) true _ c hc, Bool.and_true, Bool.and_true]
  rw [hw_eq, hrc 0 (by omega), hrc 1 (by omega), hrc 2 (by omega)]
  exact ⟨rfl, rfl⟩

lemma single_key_card_ge {k n a : Nat} (hk : 0 < k)
    (bank : Fin a → Bool) (key : Fin a → Fin n) (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
    (C : Circuit) (tap : Fin n → Fin k → Nat)
    (hval : valid a C)
    (loss : Nat) (hloss_le : loss ≤ k) (hcnt : C.gates.countP nonlinear ≤ n * loss)
    (htap : ∀ j i, tap j i < a + C.gates.length)
    (hcomp : ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
      (C.wires (List.ofFn (fun l : Fin a => readBit hk (bank l) (name l) (x (key l)) (site l)))).getD (tap j i) false = x j i)
    (j0 : Fin n) (S0 : Finset (Fin k → Bool))
    (hS0 : ∀ w : Fin k → Bool,
      (∃ (γ : Fin a → Bool) (c : Bool),
        ∀ (y : Fin k → Bool),
          dot w y = xor c (xorFin (fun l : Fin a => (decide (key l = j0) && γ l) && readBit hk (bank l) (name l) y (site l)))) →
      w ∈ S0)
    (hother : ∀ (j : Fin n),
      ∃ (Sj : Finset (Fin k → Bool)),
        Sj.card ≤ 2 ^ (k - loss) ∧
        ∀ w : Fin k → Bool,
          (∃ (γ : Fin a → Bool) (c : Bool),
            ∀ (y : Fin k → Bool),
              dot w y = xor c (xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (name l) y (site l)))) →
          w ∈ Sj) :
    2 ^ (k - loss) ≤ S0.card := by
  choose Sother hSother_card hSother_mem using hother
  let S : Fin n → Finset (Fin k → Bool) := fun j => if j = j0 then S0 else Sother j
  have hlb := per_key_card_lb (read := fun l y => readBit hk (bank l) (name l) y (site l))
    key C tap hval htap hcomp S (fun j w hw => by
      dsimp only [S]; by_cases h : j = j0
      · subst h; rw [ite_pos rfl]; exact hS0 w hw
      · rw [ite_neg h]; exact hSother_mem j w hw)
  have hprod_le : (∏ j : Fin n, (S j).card) ≤ S0.card * (2 ^ (k - loss)) ^ (n - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (S j).card) (Finset.mem_univ j0)]
    have hSj0 : S j0 = S0 := by dsimp only [S]; rw [ite_pos rfl]
    rw [hSj0]
    apply Nat.mul_le_mul_left
    calc ∏ j ∈ Finset.univ.erase j0, (S j).card
        ≤ ∏ _j ∈ Finset.univ.erase j0, 2 ^ (k - loss) := by
          apply Finset.prod_le_prod
          intro j hj
          have hne : j ≠ j0 := (Finset.mem_erase.mp hj).1
          dsimp only [S]; rw [ite_neg hne]; exact hSother_card j
      _ = (2 ^ (k - loss)) ^ (Finset.univ.erase j0).card := Finset.prod_const _
      _ = (2 ^ (k - loss)) ^ (n - 1) := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin]
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero (fun h => by subst h; exact j0.elim0)
  have hpow_M : 2 ^ (C.gates.countP nonlinear) ≤ 2 ^ (n * loss) :=
    Nat.pow_le_pow_right (by omega) hcnt
  have hcomb : 2 ^ (n * k) ≤ 2 ^ (n * loss) * (S0.card * 2 ^ ((k - loss) * (n - 1))) := by
    calc 2 ^ (n * k) ≤ 2 ^ (C.gates.countP nonlinear) * ∏ j : Fin n, (S j).card := hlb
      _ ≤ 2 ^ (n * loss) * (S0.card * (2 ^ (k - loss)) ^ (n - 1)) := Nat.mul_le_mul hpow_M hprod_le
      _ = 2 ^ (n * loss) * (S0.card * 2 ^ ((k - loss) * (n - 1))) := by rw [← pow_mul]
  have hexp : n * k = (n * loss + (k - loss) * (n - 1)) + (k - loss) := by
    have h1 : n * k = n * (loss + (k - loss)) := by congr 1; omega
    have h2 : n * (k - loss) = (k - loss) * (n - 1) + (k - loss) := by
      have : n = (n - 1) + 1 := by omega
      conv_lhs => rw [this]
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n - 1)]
    rw [h1, Nat.mul_add, h2, Nat.add_assoc]
  have hrearr : 2 ^ (n * loss) * (S0.card * 2 ^ ((k - loss) * (n - 1))) =
      2 ^ (n * loss + (k - loss) * (n - 1)) * S0.card := by
    rw [pow_add, Nat.mul_comm S0.card, ← Nat.mul_assoc]
  rw [hexp, pow_add, hrearr] at hcomb
  exact Nat.le_of_mul_le_mul_left hcomb (Nat.pow_pos (by omega : 0 < 2))

lemma group_span_card_h1 {k a h : Nat} (hk : 0 < k) (hh : h ≤ 1) (col : Bool) (i : Fin k)
    (names : Fin h → Fin k → Bool) (pick : Fin a → Fin h) (P : Fin a → Bool) :
    ∀ (γ : Fin a → Bool),
      xorFin (fun l : Fin a => P l && γ l) = false →
      ∀ x : Fin k → Bool,
        xorFin (fun l : Fin a => (P l && γ l) && readBit hk col (names (pick l)) x i) =
        xorFin (fun l : Fin a => (P l && γ l) && readBit hk col (names (pick l)) (fun _ => false) i) := by
  intro γ heven x
  by_cases ha0 : a = 0
  · subst ha0; rfl
  · have hpos : 0 < a := Nat.pos_of_ne_zero ha0
    let l0 : Fin a := ⟨0, hpos⟩
    have hp_eq : ∀ l : Fin a, pick l = pick l0 := fun l => Fin.ext (by omega)
    have h1 : (fun l : Fin a => (P l && γ l) && readBit hk col (names (pick l)) x i) =
        (fun l : Fin a => (P l && γ l) && readBit hk col (names (pick l0)) x i) := by
      funext l; rw [hp_eq l]
    have h2 : (fun l : Fin a => (P l && γ l) && readBit hk col (names (pick l)) (fun _ => false) i) =
        (fun l : Fin a => (P l && γ l) && readBit hk col (names (pick l0)) (fun _ => false) i) := by
      funext l; rw [hp_eq l]
    rw [h1, h2, xorFin_and_right, xorFin_and_right, heven, Bool.false_and, Bool.false_and]

def w01Vec {k : Nat} (hk : 0 < k) (col : Bool) (u0 u1 : Fin k → Bool) (i : Fin k) : Fin k → Bool :=
  let d := if col then 2 else 1
  let Δ := mix hk d (add u0 u1)
  fun p => xor (Δ (ix hk (i.val + 1)) && R0Vec hk col (ix hk (i.val + 2)) p)
               (Δ (ix hk (i.val + 2)) && R0Vec hk col (ix hk (i.val + 1)) p)

lemma group_span_card_h2 {k a : Nat} (hk : 0 < k) (col : Bool) (i : Fin k)
    (names : Fin 2 → Fin k → Bool) (pick : Fin a → Fin 2) (P : Fin a → Bool) :
    let S := Finset.univ.filter (fun l : Fin a => P l = true)
    let u0 := names ⟨0, by omega⟩
    let u1 := names ⟨1, by omega⟩
    let G : Finset (Fin k → Bool) := if S.card ≤ 1 then {fun _ => false} else {fun _ => false, w01Vec hk col u0 u1 i}
    G.card ≤ 2 ^ (min (S.card - 1) 1) ∧
    ∀ (γ : Fin a → Bool),
      xorFin (fun l : Fin a => P l && γ l) = false →
      ∃ w ∈ G, ∀ x : Fin k → Bool,
        xorFin (fun l : Fin a => (P l && γ l) && readBit hk col (names (pick l)) x i) =
        xor (xorFin (fun l : Fin a => (P l && γ l) && readBit hk col (names (pick l)) (fun _ => false) i))
            (dot w x) := by
  intro S u0 u1 G
  by_cases hs1 : S.card ≤ 1
  · have hG : G = {fun _ => false} := by dsimp only [G]; rw [ite_pos hs1]
    refine ⟨by rw [hG, Finset.card_singleton]; exact Nat.one_le_two_pow, fun γ heven => ?_⟩
    refine ⟨fun _ => false, by rw [hG]; exact Finset.mem_singleton_self _, fun x => ?_⟩
    rw [dot_zero_left, Bool.xor_false]
    have hall0 : ∀ l : Fin a, (P l && γ l) = false := by
      intro l
      by_cases hpl : P l = true
      · have hlS : l ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩
        have hsing : ∀ l' : Fin a, l' ≠ l → (P l' && γ l') = false := fun l' hne => by
          by_cases hpl' : P l' = true
          · exfalso
            have hl'S : l' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl'⟩
            have h2 : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨l, hlS, l', hl'S, hne.symm⟩
            omega
          · have hpf : P l' = false := Bool.eq_false_iff.mpr hpl'
            rw [hpf, Bool.false_and]
        rw [xorFin_single' l _ hsing] at heven; exact heven
      · have hpf : P l = false := Bool.eq_false_iff.mpr hpl
        rw [hpf, Bool.false_and]
    rw [xorFin_eq_false _ (fun l => by rw [hall0 l, Bool.false_and]),
        xorFin_eq_false _ (fun l => by rw [hall0 l, Bool.false_and])]
  · have hG : G = {fun _ => false, w01Vec hk col u0 u1 i} := by dsimp only [G]; rw [ite_neg hs1]
    have hmin : min (S.card - 1) 1 = 1 := by omega
    refine ⟨by rw [hG, hmin]; exact Finset.card_le_two, fun γ heven => ?_⟩
    let c1 : Bool := xorFin (fun l : Fin a => (P l && γ l) && decide ((pick l).val = 1))
    let w : Fin k → Bool := if c1 then w01Vec hk col u0 u1 i else fun _ => false
    have hw_mem : w ∈ G := by
      rw [hG]; dsimp only [w]; cases c1
      · simp
      · simp
    refine ⟨w, hw_mem, fun x => ?_⟩
    have hbase : xorFin (fun l : Fin a => (P l && γ l) && readBit hk col u0 x i) = false := by
      rw [xorFin_and_right, heven, Bool.false_and]
    have hbase0 : xorFin (fun l : Fin a => (P l && γ l) && readBit hk col u0 (fun _ => false) i) = false := by
      rw [xorFin_and_right, heven, Bool.false_and]
    have hcomb : xorFin (fun l : Fin a => (P l && γ l) && readBit hk col (names (pick l)) x i) =
        xorFin (fun l : Fin a => (P l && γ l) && xor (readBit hk col u0 x i) (readBit hk col (names (pick l)) x i)) := by
      conv_lhs => rw [← Bool.false_xor (xorFin (fun l => (P l && γ l) && readBit hk col (names (pick l)) x i)), ← hbase, ← xorFin_xor]
      have hdist : ∀ a b c : Bool, xor (a && b) (a && c) = (a && xor b c) := by decide
      apply xorFin_congr; intro l; exact hdist _ _ _
    have hcomb0 : xorFin (fun l : Fin a => (P l && γ l) && readBit hk col (names (pick l)) (fun _ => false) i) =
        xorFin (fun l : Fin a => (P l && γ l) && xor (readBit hk col u0 (fun _ => false) i) (readBit hk col (names (pick l)) (fun _ => false) i)) := by
      conv_lhs => rw [← Bool.false_xor (xorFin (fun l => (P l && γ l) && readBit hk col (names (pick l)) (fun _ => false) i))]
      conv_lhs => arg 1; rw [← hbase0]
      rw [← xorFin_xor]
      have hdist : ∀ a b c : Bool, xor (a && b) (a && c) = (a && xor b c) := by decide
      apply xorFin_congr; intro l; exact hdist _ _ _
    have hdiff_dot : dot (w01Vec hk col u0 u1 i) x =
        xor (mix hk (if col then 2 else 1) (add u0 u1) (ix hk (i.val + 1)) && R0 hk col x (ix hk (i.val + 2)))
            (mix hk (if col then 2 else 1) (add u0 u1) (ix hk (i.val + 2)) && R0 hk col x (ix hk (i.val + 1))) := by
      have hsc : ∀ (c : Bool) (v : Fin k → Bool), dot (fun p => c && v p) x = (c && dot v x) := fun c v => by
        unfold dot; rw [← xorFin_and_left]; apply xorFin_congr; intro p; exact Bool.and_assoc _ _ _
      unfold w01Vec; dsimp only; rw [dot_xor_left, hsc, hsc, ← R0_eq_dot, ← R0_eq_dot]
    have hterm : ∀ l : Fin a,
        ((P l && γ l) && xor (readBit hk col u0 x i) (readBit hk col (names (pick l)) x i)) =
        xor ((P l && γ l) && xor (readBit hk col u0 (fun _ => false) i) (readBit hk col (names (pick l)) (fun _ => false) i))
            (((P l && γ l) && decide ((pick l).val = 1)) && dot (w01Vec hk col u0 u1 i) x) := fun l => by
      have hp01 : (pick l).val = 0 ∨ (pick l).val = 1 := by omega
      rcases hp01 with h0 | h1
      · have hpeq : pick l = ⟨0, by omega⟩ := Fin.ext h0
        rw [hpeq]
        have hn0 : names ⟨0, by omega⟩ = u0 := rfl
        have hd0 : decide ((⟨0, by omega⟩ : Fin 2).val = 1) = false := rfl
        rw [hn0, hd0, Bool.xor_self, Bool.xor_self, Bool.and_false, Bool.false_and, Bool.xor_false]
      · have hpeq : pick l = ⟨1, by omega⟩ := Fin.ext h1
        rw [hpeq]
        have hn1 : names ⟨1, by omega⟩ = u1 := rfl
        have hd1 : decide ((⟨1, by omega⟩ : Fin 2).val = 1) = true := rfl
        rw [hn1, hd1, readBit_diff hk col u0 u1 x i, ← hdiff_dot, Bool.and_true]
        cases P l <;> cases γ l <;> simp
    rw [hcomb, hcomb0, xorFin_congr _ _ hterm, xorFin_xor, xorFin_and_right]
    congr 1
    dsimp only [w]
    change (c1 && dot (w01Vec hk col u0 u1 i) x) = dot (if c1 then w01Vec hk col u0 u1 i else fun _ => false) x
    cases c1
    · rw [Bool.false_and]; simp only [Bool.false_eq_true, ite_false, dot_zero_left]
    · rw [Bool.true_and]; simp only [ite_true]

lemma key_group_bound_h2 {k a n : Nat} (hk : 0 < k) (hk7 : 7 ≤ k)
    (names : Fin 2 → Fin k → Bool) (pick : Fin a → Fin 2)
    (bank : Fin a → Bool) (key : Fin a → Fin n) (site : Fin a → Fin k)
    (j : Fin n) :
    let a_j := (Finset.univ.filter (fun l : Fin a => key l = j)).card
    let c_j := (Finset.univ.filter (fun l : Fin a => key l = j ∧ bank l = true)).card
    let u0 := names ⟨0, by omega⟩
    let u1 := names ⟨1, by omega⟩
    let xStar := rot hk (k - 1) (add u0 u1)
    ∃ (S_j : Finset (Fin k → Bool)) (B_j : Nat),
      S_j.card ≤ 2 ^ B_j ∧ 2 * B_j ≤ a_j ∧
      (c_j ≤ 1 → ∀ w ∈ S_j, dot w xStar = false) ∧
      (c_j ≤ 1 → (∀ q, mix hk 1 (add u0 u1) q = false) → ∀ w ∈ S_j, w = fun _ => false) ∧
      ∀ (w : Fin k → Bool),
        (∃ (γ : Fin a → Bool) (c : Bool),
          ∀ (y : Fin k → Bool),
            dot w y = xor c (xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (names (pick l)) y (site l)))) →
        w ∈ S_j := by
  intro a_j c_j u0 u1 xStar
  let P : Bool × Fin k → Fin a → Bool := fun ci l => decide (key l = j ∧ bank l = ci.1 ∧ site l = ci.2)
  let G : Bool × Fin k → Finset (Fin k → Bool) := fun ci =>
    if (Finset.univ.filter (fun l : Fin a => P ci l = true)).card ≤ 1
    then {fun _ => false}
    else {fun _ => false, w01Vec hk ci.1 u0 u1 ci.2}
  have hG_card : ∀ ci : Bool × Fin k, (G ci).card ≤ 2 ^ (min ((Finset.univ.filter (fun l : Fin a => P ci l = true)).card - 1) 1) :=
    fun ci => (group_span_card_h2 hk ci.1 ci.2 names pick (P ci)).1
  have hG_mem : ∀ ci : Bool × Fin k, ∀ (γ : Fin a → Bool),
      xorFin (fun l : Fin a => P ci l && γ l) = false →
      ∃ w ∈ G ci, ∀ x : Fin k → Bool,
        xorFin (fun l : Fin a => (P ci l && γ l) && readBit hk ci.1 (names (pick l)) x ci.2) =
        xor (xorFin (fun l : Fin a => (P ci l && γ l) && readBit hk ci.1 (names (pick l)) (fun _ => false) ci.2))
            (dot w x) :=
    fun ci => (group_span_card_h2 hk ci.1 ci.2 names pick (P ci)).2
  let sumVec : ((Bool × Fin k) → Fin k → Bool) → (Fin k → Bool) :=
    fun ws p => xor (xorFin (fun i : Fin k => ws (false, i) p)) (xorFin (fun i : Fin k => ws (true, i) p))
  let S_j : Finset (Fin k → Bool) := (Fintype.piFinset G).image sumVec
  let B_j : Nat := ∑ ci : Bool × Fin k, min ((Finset.univ.filter (fun l : Fin a => P ci l = true)).card - 1) 1
  have hSj_card : S_j.card ≤ 2 ^ B_j := by
    calc S_j.card ≤ (Fintype.piFinset G).card := Finset.card_image_le
      _ = ∏ ci : Bool × Fin k, (G ci).card := Fintype.card_piFinset G
      _ ≤ ∏ ci : Bool × Fin k, 2 ^ (min ((Finset.univ.filter (fun l : Fin a => P ci l = true)).card - 1) 1) :=
        Finset.prod_le_prod (fun ci _ => hG_card ci)
      _ = 2 ^ B_j := by rw [Finset.prod_pow_eq_pow_sum]
  have h2B : 2 * B_j ≤ a_j := by
    have hsum_s : ∑ ci : Bool × Fin k, (Finset.univ.filter (fun l : Fin a => P ci l = true)).card = a_j := by
      have hpart := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter (fun l : Fin a => key l = j))
        (f := fun l : Fin a => (bank l, site l)) (t := (Finset.univ : Finset (Bool × Fin k)))
        (fun _ _ => Finset.mem_univ _)
      dsimp only [a_j]; rw [hpart]
      apply Finset.sum_congr rfl; intro ci _
      congr 1; ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, decide_eq_true_eq, Prod.ext_iff]
    calc 2 * B_j = ∑ ci : Bool × Fin k, 2 * min ((Finset.univ.filter (fun l : Fin a => P ci l = true)).card - 1) 1 := by
          rw [Finset.mul_sum]
      _ ≤ ∑ ci : Bool × Fin k, (Finset.univ.filter (fun l : Fin a => P ci l = true)).card := by
          apply Finset.sum_le_sum; intro ci _; omega
      _ = a_j := hsum_s
  have hR0_xStar : R0 hk false xStar = mix hk 1 (add u0 u1) := by
    unfold R0; simp only [Bool.false_eq_true, ite_false]
    congr 1; funext q; unfold xStar rot
    apply congrArg (add u0 u1); apply Fin.ext; dsimp [ix]
    rw [Nat.mod_eq_of_lt (by omega : 1 < k), Nat.mod_eq_of_lt (by omega : k - 1 < k), mod_sub_eq q.isLt (by omega)]
    split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega
  have hdot_w01_xStar : ∀ i : Fin k, dot (w01Vec hk false u0 u1 i) xStar = false := fun i => by
    have hsc : ∀ (c : Bool) (v : Fin k → Bool), dot (fun p => c && v p) xStar = (c && dot v xStar) := fun c v => by
      unfold dot; rw [← xorFin_and_left]; apply xorFin_congr; intro p; exact Bool.and_assoc _ _ _
    unfold w01Vec; simp only [Bool.false_eq_true, ite_false]
    rw [dot_xor_left, hsc, hsc, ← R0_eq_dot, ← R0_eq_dot, hR0_xStar]
    rw [Bool.and_comm (mix hk 1 (add u0 u1) (ix hk (i.val + 2)))]; exact Bool.xor_self _
  have htrue_le : c_j ≤ 1 → ∀ i : Fin k, (Finset.univ.filter (fun l : Fin a => P (true, i) l = true)).card ≤ 1 := by
    intro hcj i
    have hsub : Finset.univ.filter (fun l : Fin a => P (true, i) l = true) ⊆
        Finset.univ.filter (fun l : Fin a => key l = j ∧ bank l = true) := by
      intro l hl
      have h1 := (Finset.mem_filter.mp hl).2
      simp only [P, decide_eq_true_eq] at h1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨h1.1, h1.2.1⟩⟩
    exact le_trans (Finset.card_le_card hsub) hcj
  have horth : c_j ≤ 1 → ∀ w ∈ S_j, dot w xStar = false := by
    intro hcj w hw
    rcases Finset.mem_image.mp hw with ⟨ws, hws, rfl⟩
    have hws_m := Fintype.mem_piFinset.mp hws
    have hF : ∀ i : Fin k, dot (ws (false, i)) xStar = false := fun i => by
      have hm := hws_m (false, i)
      dsimp only [G] at hm
      split_ifs at hm
      · rw [Finset.mem_singleton.mp hm, dot_zero_left]
      · rcases Finset.mem_insert.mp hm with h0 | h1
        · rw [h0, dot_zero_left]
        · rw [Finset.mem_singleton.mp h1]; exact hdot_w01_xStar i
    have hT : ∀ i : Fin k, ws (true, i) = fun _ => false := fun i => by
      have hm := hws_m (true, i)
      dsimp only [G] at hm; rw [ite_pos (htrue_le hcj i)] at hm
      exact Finset.mem_singleton.mp hm
    unfold dot sumVec
    have h1 : xorFin (fun p : Fin k => xor (xorFin (fun i : Fin k => ws (false, i) p)) (xorFin (fun i : Fin k => ws (true, i) p)) && xStar p) =
        xor (xorFin (fun i : Fin k => dot (ws (false, i)) xStar)) (xorFin (fun i : Fin k => dot (ws (true, i)) xStar)) := by
      have hdist : ∀ a b c : Bool, (xor a b && c) = xor (a && c) (b && c) := by decide
      rw [xorFin_congr _ _ (fun p => hdist _ _ _), xorFin_xor]
      congr 1
      · rw [xorFin_congr _ _ (fun p => (xorFin_and_right _ _).symm), xorFin_swap]; rfl
      · rw [xorFin_congr _ _ (fun p => (xorFin_and_right _ _).symm), xorFin_swap]; rfl
    rw [h1, xorFin_eq_false _ hF, xorFin_eq_false _ (fun i => by rw [hT i, dot_zero_left])]; rfl
  have hzero_of_Δ0 : c_j ≤ 1 → (∀ q, mix hk 1 (add u0 u1) q = false) → ∀ w ∈ S_j, w = fun _ => false := by
    intro hcj hΔ0 w hw
    rcases Finset.mem_image.mp hw with ⟨ws, hws, rfl⟩
    have hws_m := Fintype.mem_piFinset.mp hws
    have hw01_0 : ∀ i : Fin k, w01Vec hk false u0 u1 i = fun _ => false := fun i => by
      funext p; unfold w01Vec; simp only [Bool.false_eq_true, ite_false, hΔ0, Bool.false_and]; rfl
    have hF : ∀ i : Fin k, ws (false, i) = fun _ => false := fun i => by
      have hm := hws_m (false, i); dsimp only [G] at hm
      split_ifs at hm
      · exact Finset.mem_singleton.mp hm
      · rcases Finset.mem_insert.mp hm with h0 | h1
        · exact h0
        · rw [Finset.mem_singleton.mp h1, hw01_0 i]
    have hT : ∀ i : Fin k, ws (true, i) = fun _ => false := fun i => by
      have hm := hws_m (true, i); dsimp only [G] at hm; rw [ite_pos (htrue_le hcj i)] at hm
      exact Finset.mem_singleton.mp hm
    funext p; dsimp only [sumVec]
    rw [xorFin_eq_false _ (fun i => by rw [hF i]), xorFin_eq_false _ (fun i => by rw [hT i])]; rfl
  refine ⟨S_j, B_j, hSj_card, h2B, horth, hzero_of_Δ0, fun w hw => ?_⟩
  rcases hw with ⟨γ, c, hγ⟩
  rcases linear_from_dot w c _ hγ with ⟨hpol0, hlin⟩
  have heven := even_parity_per_site hk (by omega) (by omega) bank key (fun l => names (pick l)) site j γ hpol0
  have hpick : ∀ ci : Bool × Fin k, ∃ wg ∈ G ci, ∀ x : Fin k → Bool,
      xorFin (fun l : Fin a => (P ci l && γ l) && readBit hk ci.1 (names (pick l)) x ci.2) =
      xor (xorFin (fun l : Fin a => (P ci l && γ l) && readBit hk ci.1 (names (pick l)) (fun _ => false) ci.2))
          (dot wg x) := fun ci => hG_mem ci γ (heven ci.1 ci.2)
  choose ws hws_mem hws_eq using hpick
  have hdecomp : ∀ x : Fin k → Bool,
      xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (names (pick l)) x (site l)) =
      xor (xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (false, i) l && γ l) && readBit hk false (names (pick l)) x i)))
          (xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (true, i) l && γ l) && readBit hk true (names (pick l)) x i))) := by
    intro x
    rw [xorFin_swap (fun i l => (P (false, i) l && γ l) && readBit hk false (names (pick l)) x i),
        xorFin_swap (fun i l => (P (true, i) l && γ l) && readBit hk true (names (pick l)) x i),
        ← xorFin_xor]
    apply xorFin_congr; intro l
    have hF : xorFin (fun i : Fin k => (P (false, i) l && γ l) && readBit hk false (names (pick l)) x i) =
        ((decide (key l = j ∧ bank l = false) && γ l) && readBit hk false (names (pick l)) x (site l)) := by
      rw [xorFin_single' (site l)]
      · by_cases hkj : key l = j ∧ bank l = false <;> simp [P, hkj]
      · intro i hi; have hf : ¬(key l = j ∧ bank l = false ∧ site l = i) := fun h => hi h.2.2.symm
        simp [P, hf]
    have hT : xorFin (fun i : Fin k => (P (true, i) l && γ l) && readBit hk true (names (pick l)) x i) =
        ((decide (key l = j ∧ bank l = true) && γ l) && readBit hk true (names (pick l)) x (site l)) := by
      rw [xorFin_single' (site l)]
      · by_cases hkj : key l = j ∧ bank l = true <;> simp [P, hkj]
      · intro i hi; have hf : ¬(key l = j ∧ bank l = true ∧ site l = i) := fun h => hi h.2.2.symm
        simp [P, hf]
    rw [hF, hT]
    cases bank l <;> by_cases hkj : key l = j <;> simp [hkj]
  have hw_eq : w = sumVec ws := by
    funext p
    have h1 := hlin (eVec p)
    rw [dot_eVec] at h1
    have h2 : xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (names (pick l)) (eVec p) (site l)) =
        xor (xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (names (pick l)) (fun _ => false) (site l)))
            (sumVec ws p) := by
      rw [hdecomp (eVec p), hdecomp (fun _ => false)]
      have hF_rw : xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (false, i) l && γ l) && readBit hk false (names (pick l)) (eVec p) i)) =
          xor (xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (false, i) l && γ l) && readBit hk false (names (pick l)) (fun _ => false) i)))
              (xorFin (fun i : Fin k => ws (false, i) p)) := by
        rw [xorFin_congr _ _ (fun i => hws_eq (false, i) (eVec p)), xorFin_xor]
        congr 1; exact xorFin_congr _ _ (fun i => dot_eVec _ p)
      have hT_rw : xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (true, i) l && γ l) && readBit hk true (names (pick l)) (eVec p) i)) =
          xor (xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (true, i) l && γ l) && readBit hk true (names (pick l)) (fun _ => false) i)))
              (xorFin (fun i : Fin k => ws (true, i) p)) := by
        rw [xorFin_congr _ _ (fun i => hws_eq (true, i) (eVec p)), xorFin_xor]
        congr 1; exact xorFin_congr _ _ (fun i => dot_eVec _ p)
      rw [hF_rw, hT_rw]; dsimp only [sumVec]
      cases xorFin (fun i => xorFin (fun l => (P (false, i) l && γ l) && readBit hk false (names (pick l)) (fun _ => false) i)) <;>
        cases xorFin (fun i => xorFin (fun l => (P (true, i) l && γ l) && readBit hk true (names (pick l)) (fun _ => false) i)) <;>
        cases xorFin (fun i => ws (false, i) p) <;> cases xorFin (fun i => ws (true, i) p) <;> rfl
    rw [h2] at h1
    cases hA : xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (names (pick l)) (fun _ => false) (site l)) <;>
      cases hB : sumVec ws p <;> cases hW : w p <;> rw [hA, hB, hW] at h1 <;> simp at h1 ⊢
  rw [hw_eq]
  exact Finset.mem_image.mpr ⟨ws, Fintype.mem_piFinset.mpr hws_mem, rfl⟩

theorem lower_bound_45025 {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (n h q c : Nat)
    (a : Nat) (names : Fin h → Fin k → Bool) (pick : Fin a → Fin h)
    (bank : Fin a → Bool) (key : Fin a → Fin n) (site : Fin a → Fin k)
    (C : Circuit) (tap : Fin n → Fin k → Nat)
    (haq : a ≤ q) (hbc : (Finset.univ.filter (fun j : Fin a => bank j = true)).card ≤ c)
    (hval : valid a C)
    (hcnt : C.gates.countP nonlinear ≤ n * (if 3 ∣ k then 2 else 0))
    (htap : ∀ j i, tap j i < a + C.gates.length)
    (hcomp : ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
      (C.wires (List.ofFn (fun l : Fin a => readBit hk (bank l) (names (pick l)) (x (key l)) (site l)))).getD (tap j i) false = x j i) :
    let e := if 3 ∣ k then 2 else 0
    let d := k - e
    n = 0 ∨ (h = 2 ∧ 2 * n * d ≤ q ∧ 2 * n ≤ c) ∨ (3 ≤ h ∧ n * (d + (d + 1) / 2) ≤ q) := by
  intro e d
  by_cases hn0 : n = 0
  · exact Or.inl hn0
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  have he_le : e ≤ k := by dsimp only [e]; split_ifs <;> omega
  have hd_ge5 : 5 ≤ d := by dsimp only [d, e]; split_ifs <;> omega
  have hother : ∀ (j : Fin n),
      ∃ (Sj : Finset (Fin k → Bool)),
        Sj.card ≤ 2 ^ d ∧
        ∀ w : Fin k → Bool,
          (∃ (γ : Fin a → Bool) (c0 : Bool),
            ∀ (y : Fin k → Bool),
              dot w y = xor c0 (xorFin (fun l : Fin a => (decide (key l = j) && γ l) && readBit hk (bank l) (names (pick l)) y (site l)))) →
          w ∈ Sj := by
    intro j
    by_cases h3 : 3 ∣ k
    · have hk9 : 9 ≤ k := by rcases h3 with ⟨r, hr⟩; omega
      have hd_eq : d = k - 2 := by dsimp only [d, e]; rw [ite_pos h3]
      refine ⟨Finset.univ.filter (fun w : Fin k → Bool => resSum w 0 = resSum w 1 ∧ resSum w 1 = resSum w 2),
        by rw [hd_eq]; exact resSum_subspace_card h3 (by omega),
        fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          key_in_resSum_subspace hk hk9 h3 bank key (fun l => names (pick l)) site j w hw⟩⟩
    · have hd_eq : d = k := by dsimp only [d, e]; rw [ite_neg h3]; omega
      refine ⟨Finset.univ, by rw [hd_eq]; simp [Fintype.card_fin, Fintype.card_bool],
        fun _ _ => Finset.mem_univ _⟩
  by_cases hh1 : h ≤ 1
  ·
    exfalso
    let j0 : Fin n := ⟨0, hn_pos⟩
    have hlb := single_key_card_ge hk bank key (fun l => names (pick l)) site C tap hval e he_le hcnt htap hcomp j0
      {fun _ => false} (fun w hw => by
        rcases hw with ⟨γ, c0, hγ⟩
        rcases linear_from_dot w c0 _ hγ with ⟨hpol0, hlin⟩
        have heven := even_parity_per_site hk (by omega) (by omega) bank key (fun l => names (pick l)) site j0 γ hpol0
        let P : Bool × Fin k → Fin a → Bool := fun ci l => decide (key l = j0 ∧ bank l = ci.1 ∧ site l = ci.2)
        have hdecomp : ∀ x : Fin k → Bool,
            xorFin (fun l : Fin a => (decide (key l = j0) && γ l) && readBit hk (bank l) (names (pick l)) x (site l)) =
            xor (xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (false, i) l && γ l) && readBit hk false (names (pick l)) x i)))
                (xorFin (fun i : Fin k => xorFin (fun l : Fin a => (P (true, i) l && γ l) && readBit hk true (names (pick l)) x i))) := by
          intro x
          rw [xorFin_swap (fun i l => (P (false, i) l && γ l) && readBit hk false (names (pick l)) x i),
              xorFin_swap (fun i l => (P (true, i) l && γ l) && readBit hk true (names (pick l)) x i),
              ← xorFin_xor]
          apply xorFin_congr; intro l
          have hF : xorFin (fun i : Fin k => (P (false, i) l && γ l) && readBit hk false (names (pick l)) x i) =
              ((decide (key l = j0 ∧ bank l = false) && γ l) && readBit hk false (names (pick l)) x (site l)) := by
            rw [xorFin_single' (site l)]
            · by_cases hkj : key l = j0 ∧ bank l = false <;> simp [P, hkj]
            · intro i hi; have hf : ¬(key l = j0 ∧ bank l = false ∧ site l = i) := fun h => hi h.2.2.symm; simp [P, hf]
          have hT : xorFin (fun i : Fin k => (P (true, i) l && γ l) && readBit hk true (names (pick l)) x i) =
              ((decide (key l = j0 ∧ bank l = true) && γ l) && readBit hk true (names (pick l)) x (site l)) := by
            rw [xorFin_single' (site l)]
            · by_cases hkj : key l = j0 ∧ bank l = true <;> simp [P, hkj]
            · intro i hi; have hf : ¬(key l = j0 ∧ bank l = true ∧ site l = i) := fun h => hi h.2.2.symm; simp [P, hf]
          rw [hF, hT]; cases bank l <;> by_cases hkj : key l = j0 <;> simp [hkj]
        rw [Finset.mem_singleton]; funext p
        have hp := hlin (eVec p); rw [dot_eVec] at hp
        have hconst : xorFin (fun l : Fin a => (decide (key l = j0) && γ l) && readBit hk (bank l) (names (pick l)) (eVec p) (site l)) =
            xorFin (fun l : Fin a => (decide (key l = j0) && γ l) && readBit hk (bank l) (names (pick l)) (fun _ => false) (site l)) := by
          rw [hdecomp (eVec p), hdecomp (fun _ => false)]
          congr 1
          · apply xorFin_congr; intro i; exact group_span_card_h1 hk hh1 false i names pick (P (false, i)) γ (heven false i) (eVec p)
          · apply xorFin_congr; intro i; exact group_span_card_h1 hk hh1 true i names pick (P (true, i)) γ (heven true i) (eVec p)
        rw [hconst] at hp
        revert hp
        cases xorFin (fun l => (decide (key l = j0) && γ l) && readBit hk (bank l) (names (pick l)) (fun _ => false) (site l)) <;>
          cases w p <;> simp) hother
    rw [Finset.card_singleton] at hlb
    have hpow : 2 ≤ 2 ^ (k - e) := le_trans (by omega : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  · by_cases hh2 : h = 2
    · subst hh2
      refine Or.inr (Or.inl ⟨rfl, ?_, ?_⟩)
      ·
        have hper : ∀ j : Fin n, 2 * d ≤ (Finset.univ.filter (fun l : Fin a => key l = j)).card := by
          intro j
          rcases key_group_bound_h2 hk hk7 names pick bank key site j with ⟨Sj, Bj, hSj_card, h2B, _, _, hSj_mem⟩
          have hlb := single_key_card_ge hk bank key (fun l => names (pick l)) site C tap hval e he_le hcnt htap hcomp j Sj hSj_mem hother
          have hd_le_B : d ≤ Bj := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp (le_trans hlb hSj_card)
          omega
        have hsum_a : ∑ j : Fin n, (Finset.univ.filter (fun l : Fin a => key l = j)).card = a := by
          have hp := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin a)))
            (f := key) (t := (Finset.univ : Finset (Fin n))) (fun _ _ => Finset.mem_univ _)
          simp only [Finset.card_univ, Fintype.card_fin] at hp; exact hp.symm
        calc 2 * n * d = n * (2 * d) := by ring
          _ = ∑ _j : Fin n, (2 * d) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          _ ≤ ∑ j : Fin n, (Finset.univ.filter (fun l : Fin a => key l = j)).card := Finset.sum_le_sum (fun j _ => hper j)
          _ = a := hsum_a
          _ ≤ q := haq
      ·
        let u0 := names ⟨0, by omega⟩
        let u1 := names ⟨1, by omega⟩
        let Δ := mix hk 1 (add u0 u1)
        let xStar := rot hk (k - 1) (add u0 u1)
        have hR0_xStar : R0 hk false xStar = Δ := by
          unfold R0; simp only [Bool.false_eq_true, ite_false]
          congr 1; funext q; unfold xStar rot
          apply congrArg (add u0 u1); apply Fin.ext; dsimp [ix]
          rw [Nat.mod_eq_of_lt (by omega : 1 < k), Nat.mod_eq_of_lt (by omega : k - 1 < k), mod_sub_eq q.isLt (by omega)]
          split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega
        have hper_c : ∀ j : Fin n, 2 ≤ (Finset.univ.filter (fun l : Fin a => key l = j ∧ bank l = true)).card := by
          intro j
          by_contra hlt; push Not at hlt
          have hcj1 : (Finset.univ.filter (fun l : Fin a => key l = j ∧ bank l = true)).card ≤ 1 := by omega
          rcases key_group_bound_h2 hk hk7 names pick bank key site j with ⟨Sj, _, _, _, horth, hzero, hSj_mem⟩
          by_cases hΔ0 : ∀ q : Fin k, Δ q = false
          · have hsub : Sj ⊆ {fun _ => false} := fun w hw => Finset.mem_singleton.mpr (hzero hcj1 hΔ0 w hw)
            have hlb := single_key_card_ge hk bank key (fun l => names (pick l)) site C tap hval e he_le hcnt htap hcomp j Sj hSj_mem hother
            have hc1 : Sj.card ≤ 1 := le_trans (Finset.card_le_card hsub) (by simp)
            have hpow : 2 ≤ 2 ^ (k - e) := le_trans (by omega : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by omega) (by omega))
            omega
          · push Not at hΔ0
            rcases hΔ0 with ⟨q0, hq0⟩
            have hq0_t : Δ q0 = true := Bool.eq_true_of_not_eq_false hq0
            let w0 : Fin k → Bool := R0Vec hk false q0
            have hdot_w0 : dot w0 xStar = true := by
              dsimp only [w0]; rw [← R0_eq_dot, hR0_xStar, hq0_t]
            let T : Finset (Fin k → Bool) :=
              if 3 ∣ k then Finset.univ.filter (fun w : Fin k → Bool => resSum w 0 = resSum w 1 ∧ resSum w 1 = resSum w 2)
              else Finset.univ
            have hT_card : T.card ≤ 2 ^ d := by
              dsimp only [T]; by_cases h3 : 3 ∣ k
              · rw [ite_pos h3]; have hd_eq : d = k - 2 := by dsimp only [d, e]; rw [ite_pos h3]
                rw [hd_eq]; exact resSum_subspace_card h3 (by omega)
              · rw [ite_neg h3]; have hd_eq : d = k := by dsimp only [d, e]; rw [ite_neg h3]; omega
                rw [hd_eq]; simp [Fintype.card_fin, Fintype.card_bool]
            let T0 : Finset (Fin k → Bool) := T.filter (fun w => dot w xStar = false)
            let T1 : Finset (Fin k → Bool) := T.filter (fun w => dot w xStar = true)
            have hT0_le_T1 : T0.card ≤ T1.card := by
              refine Finset.card_le_card_of_injOn (fun w => add w w0) (fun w hw => ?_) (fun u _ v _ heq => ?_)
              · have hwT := (Finset.mem_filter.mp hw).1
                have hw0 := (Finset.mem_filter.mp hw).2
                refine Finset.mem_filter.mpr ⟨?_, ?_⟩
                · dsimp only [T] at hwT ⊢; by_cases h3 : 3 ∣ k
                  · rw [ite_pos h3] at hwT ⊢
                    have hrw := (Finset.mem_filter.mp hwT).2
                    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                    have hr0 := resSum_R0Vec_eq hk h3 (by omega) false q0 0 (by omega)
                    have hr1 := resSum_R0Vec_eq hk h3 (by omega) false q0 1 (by omega)
                    have hr2 := resSum_R0Vec_eq hk h3 (by omega) false q0 2 (by omega)
                    unfold add; dsimp only [w0]
                    rw [resSum_xor, resSum_xor, resSum_xor, hr0, hr1, hr2, hrw.1, hrw.2]
                    exact ⟨rfl, rfl⟩
                  · rw [ite_neg h3]; exact Finset.mem_univ _
                · unfold add; rw [dot_xor_left, hw0, hdot_w0]; rfl
              · funext p; have hp := congrFun heq p; dsimp only [add] at hp
                revert hp; cases u p <;> cases v p <;> cases w0 p <;> simp
            have hdisj : Disjoint T0 T1 := Finset.disjoint_left.mpr (fun w h0 h1 => by
              have e0 := (Finset.mem_filter.mp h0).2
              have e1 := (Finset.mem_filter.mp h1).2
              rw [e0] at e1; cases e1)
            have hunion : T0 ∪ T1 ⊆ T := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
            have h2T0 : 2 * T0.card ≤ 2 ^ d := by
              have hc := Finset.card_le_card hunion
              rw [Finset.card_union_of_disjoint hdisj] at hc
              omega
            have hlb := single_key_card_ge hk bank key (fun l => names (pick l)) site C tap hval e he_le hcnt htap hcomp j
              T0 (fun w hw => by
                refine Finset.mem_filter.mpr ⟨?_, horth hcj1 w (hSj_mem w hw)⟩
                dsimp only [T]; by_cases h3 : 3 ∣ k
                · rw [ite_pos h3]
                  have hk9 : 9 ≤ k := by rcases h3 with ⟨r, hr⟩; omega
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                    key_in_resSum_subspace hk hk9 h3 bank key (fun l => names (pick l)) site j w hw⟩
                · rw [ite_neg h3]; exact Finset.mem_univ _) hother
            have hpow : 1 ≤ 2 ^ d := Nat.one_le_two_pow
            change 2 ^ d ≤ T0.card at hlb
            omega
        have hsum_c : ∑ j : Fin n, (Finset.univ.filter (fun l : Fin a => key l = j ∧ bank l = true)).card =
            (Finset.univ.filter (fun l : Fin a => bank l = true)).card := by
          have hp := Finset.card_eq_sum_card_fiberwise
            (s := Finset.univ.filter (fun l : Fin a => bank l = true))
            (f := key) (t := (Finset.univ : Finset (Fin n))) (fun _ _ => Finset.mem_univ _)
          rw [hp]
          apply Finset.sum_congr rfl; intro j _
          congr 1; ext l
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          tauto
        calc 2 * n = n * 2 := by ring
          _ = ∑ _j : Fin n, 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          _ ≤ ∑ j : Fin n, (Finset.univ.filter (fun l : Fin a => key l = j ∧ bank l = true)).card :=
              Finset.sum_le_sum (fun j _ => hper_c j)
          _ = (Finset.univ.filter (fun l : Fin a => bank l = true)).card := hsum_c
          _ ≤ c := hbc
    ·
      have hh3 : 3 ≤ h := by omega
      refine Or.inr (Or.inr ⟨hh3, ?_⟩)
      have hper : ∀ j : Fin n, d + (d + 1) / 2 ≤ (Finset.univ.filter (fun l : Fin a => key l = j)).card := by
        intro j
        rcases key_group_bound hk (by omega) (by omega) bank key (fun l => names (pick l)) site j with
          ⟨Sj, Bj, hSj_card, h3B, hSj_mem⟩
        have hlb := single_key_card_ge hk bank key (fun l => names (pick l)) site C tap hval e he_le hcnt htap hcomp j Sj hSj_mem hother
        have hd_le_B : d ≤ Bj := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp (le_trans hlb hSj_card)
        omega
      have hsum_a : ∑ j : Fin n, (Finset.univ.filter (fun l : Fin a => key l = j)).card = a := by
        have hp := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin a)))
          (f := key) (t := (Finset.univ : Finset (Fin n))) (fun _ _ => Finset.mem_univ _)
        simp only [Finset.card_univ, Fintype.card_fin] at hp; exact hp.symm
      calc n * (d + (d + 1) / 2) = ∑ _j : Fin n, (d + (d + 1) / 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        _ ≤ ∑ j : Fin n, (Finset.univ.filter (fun l : Fin a => key l = j)).card :=
            Finset.sum_le_sum (fun j _ => hper j)
        _ = a := hsum_a
        _ ≤ q := haq

def Good (width : Nat) (gs : List Gate) : Prop :=
  valid width ⟨gs, 0⟩

def WireSpec (width : Nat) (gs : List Gate) (w : Nat) (f : List Bool → Bool) : Prop :=
  w < width + gs.length ∧
  ∀ inp : List Bool, inp.length = width →
    (Circuit.wires ⟨gs, 0⟩ inp).getD w false = f inp

lemma good_nil (width : Nat) : Good width [] :=
  ⟨fun _ hj => by simp at hj, fun _ hg => by cases hg⟩

lemma wireSpec_input (width w : Nat) (hw : w < width) :
    WireSpec width [] w (fun inp => inp.getD w false) :=
  ⟨by simpa using hw, fun _ _ => rfl⟩

lemma append_gate {width : Nat} (gs : List Gate) (hgood : Good width gs)
    (g : Gate) (hlen : g.inputs.length ≤ 2) (hrb : ∀ i ∈ g.inputs, i < width + gs.length) :
    Good width (gs ++ [g]) ∧
    (gs ++ [g]).countP nonlinear = gs.countP nonlinear + (nonlinear g).toNat ∧
    (∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width (gs ++ [g]) w0 f0) ∧
    WireSpec width (gs ++ [g]) (width + gs.length)
      (fun inp => g.op.eval (g.inputs.map (fun i => (Circuit.wires ⟨gs, 0⟩ inp).getD i false))) := by
  have hgood' : Good width (gs ++ [g]) := by
    refine ⟨fun j hj => ?_, fun g' hg' => ?_⟩
    · change j < (gs ++ [g]).length at hj
      rw [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < gs.length
      · have hga : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
          unfold gateAt; exact getD_append_lt gs g _ hlt
        rw [hga]; exact hgood.1 j hlt
      · have heq : j = gs.length := by omega
        subst heq
        have hga : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
          unfold gateAt; exact getD_append_eq gs g _
        rw [hga]; exact hrb
    · rcases List.mem_append.mp hg' with h | h
      · exact hgood.2 g' h
      · rw [List.mem_singleton.mp h]; exact hlen
  have hcnt : (gs ++ [g]).countP nonlinear = gs.countP nonlinear + (nonlinear g).toNat := by
    rw [List.countP_append, List.countP_singleton]; cases nonlinear g <;> rfl
  have hpres : ∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width (gs ++ [g]) w0 f0 := by
    intro w0 f0 hw0
    have hw0_lt := hw0.1
    refine ⟨by rw [List.length_append, List.length_singleton]; omega, fun inp hlen' => ?_⟩
    rw [wires_append_gate, getD_append_lt _ _ _ (by rw [wires_length, hlen']; exact hw0.1)]
    exact hw0.2 inp hlen'
  have hnew : WireSpec width (gs ++ [g]) (width + gs.length)
      (fun inp => g.op.eval (g.inputs.map (fun i => (Circuit.wires ⟨gs, 0⟩ inp).getD i false))) := by
    refine ⟨by rw [List.length_append, List.length_singleton]; omega, fun inp hlen' => ?_⟩
    rw [wires_append_gate]
    have hwl : (Circuit.wires ⟨gs, 0⟩ inp).length = width + gs.length := by rw [wires_length, hlen']
    rw [← hwl, getD_append_eq]
  exact ⟨hgood', hcnt, hpres, hnew⟩

lemma addConst {width : Nat} (gs : List Gate) (hgood : Good width gs) (c : Bool) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width gs' w0 f0) ∧
      WireSpec width gs' w (fun _ => c) := by
  let g : Gate := ⟨if c then GateOp.and else GateOp.or, []⟩
  have hnl : nonlinear g = false := rfl
  have hstep := append_gate gs hgood g (by simp [g]) (by intro i hi; simp [g] at hi)
  refine ⟨gs ++ [g], width + gs.length, hstep.1, by rw [hstep.2.1, hnl]; simp, hstep.2.2.1, ?_⟩
  refine ⟨hstep.2.2.2.1, fun inp hlen => ?_⟩
  rw [hstep.2.2.2.2 inp hlen]; cases c <;> rfl

lemma addNot {width : Nat} (gs : List Gate) (hgood : Good width gs)
    {a : Nat} {fa : List Bool → Bool} (ha : WireSpec width gs a fa) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width gs' w0 f0) ∧
      WireSpec width gs' w (fun inp => !(fa inp)) := by
  let g : Gate := ⟨GateOp.not, [a]⟩
  have hnl : nonlinear g = false := rfl
  have hstep := append_gate gs hgood g (by simp [g]) (by intro i hi; simp [g] at hi; subst hi; exact ha.1)
  refine ⟨gs ++ [g], width + gs.length, hstep.1, by rw [hstep.2.1, hnl]; simp, hstep.2.2.1, ?_⟩
  refine ⟨hstep.2.2.2.1, fun inp hlen => ?_⟩
  rw [hstep.2.2.2.2 inp hlen]
  dsimp only [g]; rw [List.map_cons, List.map_nil, ha.2 inp hlen]; rfl

lemma addXor {width : Nat} (gs : List Gate) (hgood : Good width gs)
    {a b : Nat} {fa fb : List Bool → Bool}
    (ha : WireSpec width gs a fa) (hb : WireSpec width gs b fb) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width gs' w0 f0) ∧
      WireSpec width gs' w (fun inp => xor (fa inp) (fb inp)) := by
  let g : Gate := ⟨GateOp.mod 2, [a, b]⟩
  have hnl : nonlinear g = false := rfl
  have hstep := append_gate gs hgood g (by simp [g])
    (by intro i hi; simp [g] at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1)
  have hxnor : WireSpec width (gs ++ [g]) (width + gs.length) (fun inp => !(xor (fa inp) (fb inp))) := by
    refine ⟨hstep.2.2.2.1, fun inp hlen => ?_⟩
    rw [hstep.2.2.2.2 inp hlen]
    simp only [g, List.map_cons, List.map_nil, ha.2 inp hlen, hb.2 inp hlen]
    cases fa inp <;> cases fb inp <;> decide
  rcases addNot (gs ++ [g]) hstep.1 hxnor with ⟨gs2, w2, hg2, hc2, hp2, hw2⟩
  refine ⟨gs2, w2, hg2, by rw [hc2, hstep.2.1, hnl]; simp, fun w0 f0 h0 => hp2 _ _ (hstep.2.2.1 _ _ h0),
    hw2.1, fun inp hlen => by rw [hw2.2 inp hlen]; exact Bool.not_not _⟩

lemma addAnd {width : Nat} (gs : List Gate) (hgood : Good width gs)
    {a b : Nat} {fa fb : List Bool → Bool}
    (ha : WireSpec width gs a fa) (hb : WireSpec width gs b fb) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear + 1 ∧
      (∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width gs' w0 f0) ∧
      WireSpec width gs' w (fun inp => fa inp && fb inp) := by
  let g : Gate := ⟨GateOp.and, [a, b]⟩
  have hnl : nonlinear g = true := rfl
  have hstep := append_gate gs hgood g (by simp [g])
    (by intro i hi; simp [g] at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1)
  refine ⟨gs ++ [g], width + gs.length, hstep.1, by rw [hstep.2.1, hnl]; rfl, hstep.2.2.1, ?_⟩
  refine ⟨hstep.2.2.2.1, fun inp hlen => ?_⟩
  rw [hstep.2.2.2.2 inp hlen]
  simp only [g, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true,
    ha.2 inp hlen, hb.2 inp hlen]

lemma addAffine {width M : Nat} (gs : List Gate) (hgood : Good width gs)
    (ws : Fin M → Nat) (vals : Fin M → List Bool → Bool)
    (hws : ∀ p, WireSpec width gs (ws p) (vals p))
    (c : Bool) (coeff : Fin M → Bool) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width gs' w0 f0) ∧
      WireSpec width gs' w (fun inp => xor c (xorFin (fun p => coeff p && vals p inp))) := by
  induction M generalizing gs with
  | zero =>
    rcases addConst gs hgood c with ⟨gs1, w1, hg1, hc1, hp1, hw1⟩
    refine ⟨gs1, w1, hg1, hc1, hp1, hw1.1, fun inp hlen => ?_⟩
    rw [hw1.2 inp hlen]; exact (Bool.xor_false c).symm
  | succ M ih =>
    rcases ih gs hgood (fun p => ws p.castSucc) (fun p => vals p.castSucc)
      (fun p => hws p.castSucc) (fun p => coeff p.castSucc) with ⟨gs1, w1, hg1, hc1, hp1, hw1⟩
    cases hcl : coeff (Fin.last M)
    · refine ⟨gs1, w1, hg1, hc1, hp1, hw1.1, fun inp hlen => ?_⟩
      rw [hw1.2 inp hlen]; dsimp only; rw [xorFin_succ, hcl, Bool.false_and, Bool.xor_false]
    · have hw_last : WireSpec width gs1 (ws (Fin.last M)) (vals (Fin.last M)) := hp1 _ _ (hws (Fin.last M))
      rcases addXor gs1 hg1 hw1 hw_last with ⟨gs2, w2, hg2, hc2, hp2, hw2⟩
      refine ⟨gs2, w2, hg2, by rw [hc2, hc1], fun w0 f0 h0 => hp2 _ _ (hp1 _ _ h0), hw2.1, fun inp hlen => ?_⟩
      rw [hw2.2 inp hlen]; dsimp only; rw [xorFin_succ, hcl, Bool.true_and, Bool.xor_assoc]

lemma addAffineFn {width M : Nat} (gs : List Gate) (hgood : Good width gs)
    (ws : Fin M → Nat) (vals : Fin M → List Bool → Bool)
    (hws : ∀ p, WireSpec width gs (ws p) (vals p))
    (f : (Fin M → Bool) → Bool) (hf : IsAffine f) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width gs' w0 f0) ∧
      WireSpec width gs' w (fun inp => f (fun p => vals p inp)) := by
  rcases hf with ⟨c, coeff, hfe⟩
  rcases addAffine gs hgood ws vals hws c coeff with ⟨gs1, w1, hg1, hc1, hp1, hw1⟩
  refine ⟨gs1, w1, hg1, hc1, hp1, ?_⟩
  have heq : (fun inp => xor c (xorFin (fun p => coeff p && vals p inp))) =
      (fun inp => f (fun p => vals p inp)) := by funext inp; exact (hfe _).symm
  rw [heq] at hw1; exact hw1

lemma addAffineVec {width M K : Nat} (gs : List Gate) (hgood : Good width gs)
    (ws : Fin M → Nat) (vals : Fin M → List Bool → Bool)
    (hws : ∀ p, WireSpec width gs (ws p) (vals p))
    (fs : Fin K → (Fin M → Bool) → Bool) (hfs : ∀ i, IsAffine (fs i)) :
    ∃ (gs' : List Gate) (outs : Fin K → Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width gs' w0 f0) ∧
      ∀ i : Fin K, WireSpec width gs' (outs i) (fun inp => fs i (fun p => vals p inp)) := by
  induction K generalizing gs with
  | zero => exact ⟨gs, fun i => i.elim0, hgood, rfl, fun _ _ h => h, fun i => i.elim0⟩
  | succ K ih =>
    rcases ih gs hgood hws (fun i => fs i.castSucc) (fun i => hfs i.castSucc) with
      ⟨gs1, outs1, hg1, hc1, hp1, houts1⟩
    rcases addAffineFn gs1 hg1 ws vals (fun p => hp1 _ _ (hws p)) (fs (Fin.last K)) (hfs (Fin.last K)) with
      ⟨gs2, w2, hg2, hc2, hp2, hw2⟩
    refine ⟨gs2, fun i => if hi : i.val < K then outs1 ⟨i.val, hi⟩ else w2, hg2, by rw [hc2, hc1],
      fun w0 f0 h0 => hp2 _ _ (hp1 _ _ h0), fun i => ?_⟩
    by_cases hi : i.val < K
    · dsimp only; rw [dite_pos hi]
      have hie : (⟨i.val, hi⟩ : Fin K).castSucc = i := Fin.ext rfl
      have hfe : (fun inp => fs (⟨i.val, hi⟩ : Fin K).castSucc (fun p => vals p inp)) =
          (fun inp => fs i (fun p => vals p inp)) := by rw [hie]
      rw [← hfe]; exact hp2 _ _ (houts1 ⟨i.val, hi⟩)
    · dsimp only; rw [dite_neg hi]
      have hie : Fin.last K = i := Fin.ext (by simp [Fin.last]; omega)
      rw [← hie]; exact hw2

lemma wireSpec_input_good {width w : Nat} (gs : List Gate) (hgood : Good width gs) (hw : w < width) :
    WireSpec width gs w (fun inp => inp.getD w false) := by
  induction gs using List.reverseRecOn with
  | nil => exact wireSpec_input width w hw
  | append_singleton gs g ih =>
    have hgs : Good width gs := by
      refine ⟨fun j hj => ?_, fun g' hg' => hgood.2 g' (List.mem_append_left _ hg')⟩
      change j < gs.length at hj
      have h1 := hgood.1 j (by rw [List.length_append, List.length_singleton]; omega)
      have hga : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        unfold gateAt; exact getD_append_lt gs g _ hj
      rw [hga] at h1; exact h1
    have hrb_g : ∀ i ∈ g.inputs, i < width + gs.length := by
      have h1 := hgood.1 gs.length (by simp)
      have hga : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
        unfold gateAt; exact getD_append_eq gs g _
      rw [hga] at h1; exact h1
    exact (append_gate gs hgs g (hgood.2 g (List.mem_append_right _ List.mem_cons_self)) hrb_g).2.2.1 _ _ (ih hgs)

def zPair {k : Nat} (hk : 0 < k) (w : Fin k → Bool) (a b : Bool) : Nat → Bool × Bool
  | 0 => (a, b)
  | j + 1 =>
    let p := zPair hk w a b j
    (p.2, xor (w (ix hk (j + 1))) (xor p.1 p.2))

def zOf {k : Nat} (hk : 0 < k) (w : Fin k → Bool) (a b : Bool) (i : Fin k) : Bool :=
  (zPair hk w a b i.val).1

lemma zPair_rec_at {k : Nat} (hk : 0 < k) (w : Fin k → Bool) (a b : Bool) (j : Nat) :
    (zPair hk w a b (j + 1)).1 = (zPair hk w a b j).2 ∧
    (zPair hk w a b (j + 2)).1 = xor (w (ix hk (j + 1))) (xor (zPair hk w a b j).1 (zPair hk w a b (j + 1)).1) :=
  ⟨rfl, rfl⟩

lemma zOf_eq_of_mix1 {k : Nat} (hk : 0 < k) (hk2 : 2 ≤ k) (y : Fin k → Bool) :
    ∀ i : Fin k, zOf hk (mix hk 1 y) (y ⟨0, hk⟩) (y ⟨1, by omega⟩) i = y i := by
  intro ⟨iv, hiv⟩
  induction iv using Nat.strong_induction_on with
  | ind m ih =>
    match m with
    | 0 => rfl
    | 1 => rfl
    | j + 2 =>
      unfold zOf
      rw [(zPair_rec_at hk (mix hk 1 y) (y ⟨0, hk⟩) (y ⟨1, by omega⟩) j).2]
      have h0 := ih j (by omega) (by omega)
      have h1 := ih (j + 1) (by omega) (by omega)
      unfold zOf at h0 h1
      rw [h0, h1]
      have hix : ix hk (j + 1) = ⟨j + 1, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
      rw [hix]
      unfold mix
      have hm1 : ix hk (j + 1 + k - 1 % k) = ⟨j, by omega⟩ := Fin.ext (by
        dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)]; omega)
      have hp1 : ix hk (j + 1 + 1) = ⟨j + 2, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
      rw [hm1, hp1]
      cases y ⟨j, by omega⟩ <;> cases y ⟨j + 1, by omega⟩ <;> cases y ⟨j + 2, by omega⟩ <;> rfl

lemma zPair_xor {k : Nat} (hk : 0 < k) (w1 w2 : Fin k → Bool) (a1 b1 a2 b2 : Bool) (j : Nat) :
    zPair hk (add w1 w2) (xor a1 a2) (xor b1 b2) j =
    (xor (zPair hk w1 a1 b1 j).1 (zPair hk w2 a2 b2 j).1,
     xor (zPair hk w1 a1 b1 j).2 (zPair hk w2 a2 b2 j).2) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    unfold zPair; rw [ih]; dsimp only [add]
    congr 1
    cases w1 (ix hk (j + 1)) <;> cases w2 (ix hk (j + 1)) <;>
      cases (zPair hk w1 a1 b1 j).1 <;> cases (zPair hk w2 a2 b2 j).1 <;>
      cases (zPair hk w1 a1 b1 j).2 <;> cases (zPair hk w2 a2 b2 j).2 <;> rfl

lemma zPair_zero {k : Nat} (hk : 0 < k) (a b : Bool) (j : Nat) :
    zPair hk (fun _ => false) a b j =
    (if j % 3 = 0 then a else if j % 3 = 1 then b else xor a b,
     if (j + 1) % 3 = 0 then a else if (j + 1) % 3 = 1 then b else xor a b) := by
  induction j with
  | zero => simp [zPair]
  | succ j ih =>
    unfold zPair; rw [ih]; dsimp only
    congr 1
    by_cases h0 : j % 3 = 0
    · have h1 : (j + 1) % 3 = 1 := by omega
      have h2 : (j + 1 + 1) % 3 = 2 := by omega
      simp [h0, h1, h2]
    · by_cases h1 : j % 3 = 1
      · have h2 : (j + 1) % 3 = 2 := by omega
        have h3 : (j + 1 + 1) % 3 = 0 := by omega
        simp [h1, h2, h3]; cases a <;> cases b <;> rfl
      · have h2 : j % 3 = 2 := by omega
        have h3 : (j + 1) % 3 = 0 := by omega
        have h4 : (j + 1 + 1) % 3 = 1 := by omega
        simp [h0, h1, h3, h4]; cases a <;> cases b <;> rfl

lemma isAffine_zPair {k M : Nat} (hk : 0 < k)
    (w : (Fin M → Bool) → Fin k → Bool) (a b : (Fin M → Bool) → Bool)
    (hw : ∀ i, IsAffine (fun v => w v i)) (ha : IsAffine a) (hb : IsAffine b) (j : Nat) :
    IsAffine (fun v => (zPair hk (w v) (a v) (b v) j).1) ∧
    IsAffine (fun v => (zPair hk (w v) (a v) (b v) j).2) := by
  induction j with
  | zero => exact ⟨ha, hb⟩
  | succ j ih =>
    exact ⟨ih.2, isAffine_xor (hw (ix hk (j + 1))) (isAffine_xor ih.1 ih.2)⟩

lemma isAffine_zOf {k M : Nat} (hk : 0 < k)
    (w : (Fin M → Bool) → Fin k → Bool) (a b : (Fin M → Bool) → Bool)
    (hw : ∀ i, IsAffine (fun v => w v i)) (ha : IsAffine a) (hb : IsAffine b) (i : Fin k) :
    IsAffine (fun v => zOf hk (w v) (a v) (b v) i) :=
  (isAffine_zPair hk w a b hw ha hb i.val).1

lemma mix1_zOf_mid {k : Nat} (hk : 0 < k) (hk3 : 3 ≤ k) (w : Fin k → Bool) (a b : Bool)
    (i : Fin k) (h1 : 1 ≤ i.val) (h2 : i.val < k - 1) :
    mix hk 1 (zOf hk w a b) i = w i := by
  unfold mix zOf
  have hm : ix hk (i.val + k - 1 % k) = ⟨i.val - 1, by omega⟩ := Fin.ext (by
    dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_sub_eq i.isLt (by omega), ite_pos (by omega)])
  have hp : ix hk (i.val + 1) = ⟨i.val + 1, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
  rw [hm, hp]
  change xor (zPair hk w a b (i.val - 1)).1 (xor (zPair hk w a b i.val).1 (zPair hk w a b (i.val + 1)).1) = w i
  have heq : i.val + 1 = (i.val - 1) + 2 := by omega
  have heq1 : i.val = (i.val - 1) + 1 := by omega
  rw [heq, (zPair_rec_at hk w a b (i.val - 1)).2, ← heq1]
  have hix : ix hk i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [hix]
  cases (zPair hk w a b (i.val - 1)).1 <;> cases (zPair hk w a b i.val).1 <;> cases w i <;> rfl

lemma resSum_mix1 {k : Nat} (hk : 0 < k) (h3 : 3 ∣ k) (hk6 : 6 ≤ k) (z : Fin k → Bool)
    (c : Nat) (hc : c < 3) :
    resSum (mix hk 1 z) c = xorFin z := by
  unfold resSum mix
  have hsplit : xorFin (fun i : Fin k => decide (i.val % 3 = c) &&
        xor (z (ix hk (i.val + k - 1 % k))) (xor (z i) (z (ix hk (i.val + 1))))) =
      xor (xorFin (fun i : Fin k => decide (i.val % 3 = c) && z (ix hk (i.val + k - 1 % k))))
          (xor (xorFin (fun i : Fin k => decide (i.val % 3 = c) && z i))
               (xorFin (fun i : Fin k => decide (i.val % 3 = c) && z (ix hk (i.val + 1))))) := by
    rw [← xorFin_xor, ← xorFin_xor]; apply xorFin_congr; intro i
    cases decide (i.val % 3 = c) <;> cases z (ix hk (i.val + k - 1 % k)) <;>
      cases z i <;> cases z (ix hk (i.val + 1)) <;> rfl
  rw [hsplit]

  have hshift : ∀ (s : Nat),
      xorFin (fun i : Fin k => decide (i.val % 3 = c) && z (ix hk (i.val + s))) =
      xorFin (fun j : Fin k => decide ((j.val + k - s % k) % 3 = c) && z j) := by
    intro s
    have h1 : ∀ i : Fin k, (decide (i.val % 3 = c) && z (ix hk (i.val + s))) =
        xorFin (fun j : Fin k => decide (i.val % 3 = c) && (decide (ix hk (i.val + s) = j) && z j)) := fun i => by
      rw [xorFin_single' (ix hk (i.val + s))]
      · simp
      · intro j hj; simp [Ne.symm hj]
    rw [xorFin_congr _ _ h1, xorFin_swap]
    apply xorFin_congr; intro j
    let i0 : Fin k := ix hk (j.val + k - s % k)
    have hsm : s % k < k := Nat.mod_lt s hk
    have hi0_val : i0.val = if s % k ≤ j.val then j.val - s % k else j.val + k - s % k := by
      dsimp only [i0, ix]; exact mod_sub_eq j.isLt hsm
    rw [xorFin_single' i0]
    · have heq : ix hk (i0.val + s) = j := Fin.ext (by
        dsimp [ix]
        rw [Nat.add_mod, hi0_val]
        split_ifs with hle
        · have : j.val - s % k + s % k = j.val := by omega
          rw [Nat.mod_eq_of_lt (by omega : j.val - s % k < k), this, Nat.mod_eq_of_lt j.isLt]
        · have : j.val + k - s % k + s % k = j.val + k := by omega
          rw [Nat.mod_eq_of_lt (by omega : j.val + k - s % k < k), this, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt])
      have hmod : i0.val % 3 = (j.val + k - s % k) % 3 := by
        rcases h3 with ⟨r, hr⟩; rw [hi0_val]; split_ifs <;> omega
      rw [heq, decide_eq_true rfl, Bool.true_and, hmod]
    · intro i hi
      have hne : ix hk (i.val + s) ≠ j := fun h => hi (Fin.ext (by
        have hv := congrArg Fin.val h; dsimp [ix] at hv
        rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, mod_add_eq i.isLt hsm] at hv
        rw [hi0_val]; split_ifs at hv ⊢ <;> omega))
      rw [decide_eq_false hne, Bool.false_and, Bool.and_false]
  have hm1 : xorFin (fun i : Fin k => decide (i.val % 3 = c) && z (ix hk (i.val + k - 1 % k))) =
      xorFin (fun j : Fin k => decide ((j.val + 1) % 3 = c) && z j) := by
    have heq : (fun i : Fin k => decide (i.val % 3 = c) && z (ix hk (i.val + k - 1 % k))) =
        (fun i : Fin k => decide (i.val % 3 = c) && z (ix hk (i.val + (k - 1)))) := by
      funext i; congr 2; exact Fin.ext (by dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k)]; congr 1; omega)
    rw [heq, hshift (k - 1)]
    apply xorFin_congr; intro j
    have hm : (j.val + k - (k - 1) % k) % 3 = (j.val + 1) % 3 := by
      rcases h3 with ⟨r, hr⟩; rw [Nat.mod_eq_of_lt (by omega : k - 1 < k)]; omega
    rw [hm]
  have hp1 : xorFin (fun i : Fin k => decide (i.val % 3 = c) && z (ix hk (i.val + 1))) =
      xorFin (fun j : Fin k => decide ((j.val + 2) % 3 = c) && z j) := by
    rw [hshift 1]
    apply xorFin_congr; intro j
    have hm : (j.val + k - 1 % k) % 3 = (j.val + 2) % 3 := by
      rcases h3 with ⟨r, hr⟩; rw [Nat.mod_eq_of_lt (by omega : 1 < k)]; omega
    rw [hm]
  rw [hm1, hp1, ← xorFin_xor, ← xorFin_xor]
  apply xorFin_congr; intro j
  have h1 : (j.val + 1) % 3 = c ∨ j.val % 3 = c ∨ (j.val + 2) % 3 = c := by omega
  by_cases ha : (j.val + 1) % 3 = c
  · have hb : j.val % 3 ≠ c := by omega
    have hc' : (j.val + 2) % 3 ≠ c := by omega
    simp [ha, hb, hc']
  · by_cases hb : j.val % 3 = c
    · have hc' : (j.val + 2) % 3 ≠ c := by omega
      simp [ha, hb, hc']
    · have hc' : (j.val + 2) % 3 = c := by omega
      simp [ha, hb, hc']

lemma mix1_zOf_div3 {k : Nat} (hk : 0 < k) (h3 : 3 ∣ k) (hk6 : 6 ≤ k) (w : Fin k → Bool)
    (hw : resSum w 0 = resSum w 1 ∧ resSum w 1 = resSum w 2) :
    mix hk 1 (zOf hk w false false) = w := by
  let z := zOf hk w false false
  have hmid : ∀ i : Fin k, 1 ≤ i.val → i.val < k - 1 → mix hk 1 z i = w i :=
    fun i h1 h2 => mix1_zOf_mid hk (by omega) w false false i h1 h2
  have hres1 : resSum (mix hk 1 z) 1 = resSum w 1 := by
    unfold resSum; apply xorFin_congr; intro i
    by_cases h0 : i.val = 0
    · rw [h0]; rfl
    · by_cases hk1 : i.val = k - 1
      · have hm : i.val % 3 ≠ 1 := by omega
        rw [decide_eq_false hm, Bool.false_and, Bool.false_and]
      · rw [hmid i (by omega) (by omega)]
  have hres0 : resSum (mix hk 1 z) 0 = resSum w 0 := by
    rw [resSum_mix1 hk h3 hk6 z 0 (by omega), ← resSum_mix1 hk h3 hk6 z 1 (by omega), hres1, hw.1]
  have hres2 : resSum (mix hk 1 z) 2 = resSum w 2 := by
    rw [resSum_mix1 hk h3 hk6 z 2 (by omega), ← resSum_mix1 hk h3 hk6 z 1 (by omega), hres1, hw.2]
  have h0 : mix hk 1 z ⟨0, hk⟩ = w ⟨0, hk⟩ := by
    have hd : resSum (fun i => xor (mix hk 1 z i) (w i)) 0 = false := by
      rw [resSum_xor, hres0]; exact Bool.xor_self _
    unfold resSum at hd
    rw [xorFin_single' ⟨0, hk⟩] at hd
    · simp only [Nat.zero_mod, decide_true, Bool.true_and] at hd
      cases ha : mix hk 1 z ⟨0, hk⟩ <;> cases hb : w ⟨0, hk⟩ <;> rw [ha, hb] at hd <;> simp at hd ⊢
    · intro i hi
      have hne0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
      by_cases hk1 : i.val = k - 1
      · have hm : i.val % 3 ≠ 0 := by omega
        rw [decide_eq_false hm, Bool.false_and]
      · dsimp only; rw [hmid i (by omega) (by omega), Bool.xor_self, Bool.and_false]
  have hk1 : mix hk 1 z ⟨k - 1, by omega⟩ = w ⟨k - 1, by omega⟩ := by
    have hd : resSum (fun i => xor (mix hk 1 z i) (w i)) 2 = false := by
      rw [resSum_xor, hres2]; exact Bool.xor_self _
    unfold resSum at hd
    rw [xorFin_single' ⟨k - 1, by omega⟩] at hd
    · have hm : (k - 1) % 3 = 2 := by omega
      dsimp only at hd; rw [decide_eq_true hm, Bool.true_and] at hd
      cases ha : mix hk 1 z ⟨k - 1, by omega⟩ <;> cases hb : w ⟨k - 1, by omega⟩ <;> rw [ha, hb] at hd <;> simp at hd ⊢
    · intro i hi
      have hnek1 : i.val ≠ k - 1 := fun h => hi (Fin.ext h)
      by_cases h0' : i.val = 0
      · rw [h0']; rfl
      · dsimp only; rw [hmid i (by omega) (by omega), Bool.xor_self, Bool.and_false]
  funext i
  by_cases h0' : i.val = 0
  · have : i = ⟨0, hk⟩ := Fin.ext h0'; rw [this]; exact h0
  · by_cases hk1' : i.val = k - 1
    · have : i = ⟨k - 1, by omega⟩ := Fin.ext hk1'; rw [this]; exact hk1
    · exact hmid i (by omega) (by omega)

def invMix1 {k : Nat} (hk : 0 < k) (hk2 : 2 ≤ k) (w : Fin k → Bool) : Fin k → Bool :=
  let z0 := zOf hk w false false
  let a := if k % 3 = 1
           then xor (xor (w ⟨0, hk⟩) (z0 ⟨k - 1, by omega⟩))
                    (xor (w ⟨k - 1, by omega⟩) (xor (z0 ⟨k - 2, by omega⟩) (z0 ⟨k - 1, by omega⟩)))
           else xor (w ⟨0, hk⟩) (z0 ⟨k - 1, by omega⟩)
  let b := if k % 3 = 1
           then xor (w ⟨0, hk⟩) (z0 ⟨k - 1, by omega⟩)
           else xor (w ⟨k - 1, by omega⟩) (xor (z0 ⟨k - 2, by omega⟩) (z0 ⟨k - 1, by omega⟩))
  zOf hk w a b

lemma isAffine_invMix1 {k M : Nat} (hk : 0 < k) (hk2 : 2 ≤ k)
    (w : (Fin M → Bool) → Fin k → Bool) (hw : ∀ i, IsAffine (fun v => w v i)) (i : Fin k) :
    IsAffine (fun v => invMix1 hk hk2 (w v) i) := by
  unfold invMix1
  have hz0 : ∀ q : Fin k, IsAffine (fun v => zOf hk (w v) false false q) := fun q =>
    isAffine_zOf hk w (fun _ => false) (fun _ => false) hw (isAffine_const false) (isAffine_const false) q
  have ha : IsAffine (fun v => if k % 3 = 1
      then xor (xor (w v ⟨0, hk⟩) (zOf hk (w v) false false ⟨k - 1, by omega⟩))
               (xor (w v ⟨k - 1, by omega⟩) (xor (zOf hk (w v) false false ⟨k - 2, by omega⟩) (zOf hk (w v) false false ⟨k - 1, by omega⟩)))
      else xor (w v ⟨0, hk⟩) (zOf hk (w v) false false ⟨k - 1, by omega⟩)) := by
    by_cases h1 : k % 3 = 1
    · rw [show (fun v => if k % 3 = 1 then _ else _) =
          (fun v => xor (xor (w v ⟨0, hk⟩) (zOf hk (w v) false false ⟨k - 1, by omega⟩))
                        (xor (w v ⟨k - 1, by omega⟩) (xor (zOf hk (w v) false false ⟨k - 2, by omega⟩) (zOf hk (w v) false false ⟨k - 1, by omega⟩))))
          from funext fun _ => ite_pos h1]
      exact isAffine_xor (isAffine_xor (hw _) (hz0 _)) (isAffine_xor (hw _) (isAffine_xor (hz0 _) (hz0 _)))
    · rw [show (fun v => if k % 3 = 1 then _ else _) =
          (fun v => xor (w v ⟨0, hk⟩) (zOf hk (w v) false false ⟨k - 1, by omega⟩))
          from funext fun _ => ite_neg h1]
      exact isAffine_xor (hw _) (hz0 _)
  have hb : IsAffine (fun v => if k % 3 = 1
      then xor (w v ⟨0, hk⟩) (zOf hk (w v) false false ⟨k - 1, by omega⟩)
      else xor (w v ⟨k - 1, by omega⟩) (xor (zOf hk (w v) false false ⟨k - 2, by omega⟩) (zOf hk (w v) false false ⟨k - 1, by omega⟩))) := by
    by_cases h1 : k % 3 = 1
    · rw [show (fun v => if k % 3 = 1 then _ else _) =
          (fun v => xor (w v ⟨0, hk⟩) (zOf hk (w v) false false ⟨k - 1, by omega⟩))
          from funext fun _ => ite_pos h1]
      exact isAffine_xor (hw _) (hz0 _)
    · rw [show (fun v => if k % 3 = 1 then _ else _) =
          (fun v => xor (w v ⟨k - 1, by omega⟩) (xor (zOf hk (w v) false false ⟨k - 2, by omega⟩) (zOf hk (w v) false false ⟨k - 1, by omega⟩)))
          from funext fun _ => ite_neg h1]
      exact isAffine_xor (hw _) (isAffine_xor (hz0 _) (hz0 _))
  exact isAffine_zOf hk w _ _ hw ha hb i

lemma invMix1_mix1 {k : Nat} (hk : 0 < k) (hk2 : 2 ≤ k) (hndiv : ¬(3 ∣ k)) (y : Fin k → Bool) :
    invMix1 hk hk2 (mix hk 1 y) = y := by
  let w := mix hk 1 y
  have hy_z : ∀ i : Fin k, y i = xor (zOf hk w false false i)
      (if i.val % 3 = 0 then y ⟨0, hk⟩ else if i.val % 3 = 1 then y ⟨1, by omega⟩ else xor (y ⟨0, hk⟩) (y ⟨1, by omega⟩)) := by
    intro i
    rw [← zOf_eq_of_mix1 hk hk2 y i]
    have hadd : w = add w (fun _ => false) := by funext p; unfold add; exact (Bool.xor_false _).symm
    unfold zOf
    change (zPair hk w (y ⟨0, hk⟩) (y ⟨1, by omega⟩) i.val).1 = _
    conv_lhs => rw [hadd, show y ⟨0, hk⟩ = xor false (y ⟨0, hk⟩) from (Bool.false_xor _).symm,
      show y ⟨1, by omega⟩ = xor false (y ⟨1, by omega⟩) from (Bool.false_xor _).symm]
    rw [zPair_xor, zPair_zero]
  have hw0 : w ⟨0, hk⟩ = xor (y ⟨k - 1, by omega⟩) (xor (y ⟨0, hk⟩) (y ⟨1, by omega⟩)) := by
    dsimp only [w]; unfold mix
    have hm : ix hk (0 + k - 1 % k) = ⟨k - 1, by omega⟩ := Fin.ext (by
      dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k), Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega : k - 1 < k))
    have hp : ix hk (0 + 1) = ⟨1, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [hm, hp]
  have hwk : w ⟨k - 1, by omega⟩ = xor (y ⟨k - 2, by omega⟩) (xor (y ⟨k - 1, by omega⟩) (y ⟨0, hk⟩)) := by
    dsimp only [w]; unfold mix
    have hm : ix hk (k - 1 + k - 1 % k) = ⟨k - 2, by omega⟩ := Fin.ext (by
      dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)]; omega)
    have hp : ix hk (k - 1 + 1) = ⟨0, hk⟩ := Fin.ext (by
      dsimp [ix]; rw [show k - 1 + 1 = k by omega, Nat.mod_self])
    rw [hm, hp]
  have hmod12 : k % 3 = 1 ∨ k % 3 = 2 := by omega
  unfold invMix1; dsimp only
  rcases hmod12 with h1 | h2
  · rw [ite_pos h1, ite_pos h1]
    have hkm1 : (k - 1) % 3 = 0 := by omega
    have hkm2 : (k - 2) % 3 = 2 := by omega
    have hy1 := hy_z ⟨k - 1, by omega⟩; dsimp only at hy1; rw [ite_pos hkm1] at hy1
    have hy2 := hy_z ⟨k - 2, by omega⟩; dsimp only at hy2; rw [ite_neg (by omega), ite_neg (by omega)] at hy2
    have hb : xor (w ⟨0, hk⟩) (zOf hk w false false ⟨k - 1, by omega⟩) = y ⟨1, by omega⟩ := by
      rw [hw0, hy1]
      cases zOf hk w false false ⟨k - 1, by omega⟩ <;> cases y ⟨0, hk⟩ <;> cases y ⟨1, by omega⟩ <;> rfl
    have ha : xor (xor (w ⟨0, hk⟩) (zOf hk w false false ⟨k - 1, by omega⟩))
        (xor (w ⟨k - 1, by omega⟩) (xor (zOf hk w false false ⟨k - 2, by omega⟩) (zOf hk w false false ⟨k - 1, by omega⟩))) = y ⟨0, hk⟩ := by
      rw [hb, hwk, hy1, hy2]
      cases zOf hk w false false ⟨k - 2, by omega⟩ <;> cases zOf hk w false false ⟨k - 1, by omega⟩ <;>
        cases y ⟨0, hk⟩ <;> cases y ⟨1, by omega⟩ <;> rfl
    rw [ha, hb]; funext i; exact zOf_eq_of_mix1 hk hk2 y i
  · rw [ite_neg (by omega), ite_neg (by omega)]
    have hkm1 : (k - 1) % 3 = 1 := by omega
    have hkm2 : (k - 2) % 3 = 0 := by omega
    have hy1 := hy_z ⟨k - 1, by omega⟩; dsimp only at hy1; rw [ite_neg (by omega), ite_pos hkm1] at hy1
    have hy2 := hy_z ⟨k - 2, by omega⟩; dsimp only at hy2; rw [ite_pos hkm2] at hy2
    have ha : xor (w ⟨0, hk⟩) (zOf hk w false false ⟨k - 1, by omega⟩) = y ⟨0, hk⟩ := by
      rw [hw0, hy1]
      cases zOf hk w false false ⟨k - 1, by omega⟩ <;> cases y ⟨0, hk⟩ <;> cases y ⟨1, by omega⟩ <;> rfl
    have hb : xor (w ⟨k - 1, by omega⟩) (xor (zOf hk w false false ⟨k - 2, by omega⟩) (zOf hk w false false ⟨k - 1, by omega⟩)) = y ⟨1, by omega⟩ := by
      rw [hwk, hy1, hy2]
      cases zOf hk w false false ⟨k - 2, by omega⟩ <;> cases zOf hk w false false ⟨k - 1, by omega⟩ <;>
        cases y ⟨0, hk⟩ <;> cases y ⟨1, by omega⟩ <;> rfl
    rw [ha, hb]; funext i; exact zOf_eq_of_mix1 hk hk2 y i

lemma mix1_invMix1 {k : Nat} (hk : 0 < k) (hk2 : 2 ≤ k) (hndiv : ¬(3 ∣ k)) (w : Fin k → Bool) :
    mix hk 1 (invMix1 hk hk2 w) = w := by
  have hinj : Function.Injective (mix hk 1) :=
    Function.LeftInverse.injective (invMix1_mix1 hk hk2 hndiv)
  rcases Finite.injective_iff_surjective.mp hinj w with ⟨y, hy⟩
  rw [← hy, invMix1_mix1 hk hk2 hndiv y]

lemma single_key_spec_h3 {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) :
    let e := if 3 ∣ k then 2 else 0
    let d := k - e
    let price := d + (d + 1) / 2
    ∃ (names3 : Fin 3 → Fin k → Bool) (pick1 : Fin price → Fin 3) (site1 : Fin price → Fin k),
      ∀ (width : Nat) (gs : List Gate), Good width gs →
        ∀ (baseW : Fin price → Nat) (baseVals : Fin price → List Bool → Bool),
        (∀ p, WireSpec width gs (baseW p) (baseVals p)) →
        ∃ (gs' : List Gate) (tapJ : Fin k → Nat),
          Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear + e ∧
          (∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width gs' w0 f0) ∧
          (∀ i : Fin k, tapJ i < width + gs'.length) ∧
          ∀ (inp : List Bool) (x : Fin k → Bool),
            inp.length = width →
            (∀ p : Fin price, baseVals p inp = readBit hk false (names3 (pick1 p)) x (site1 p)) →
            ∀ i : Fin k, (Circuit.wires ⟨gs', 0⟩ inp).getD (tapJ i) false = x i := by
  intro e d price
  have hloss_eq : (if 9 ≤ k ∧ 3 ∣ k then 2 else 0) = e := by
    dsimp only [e]; by_cases h3 : 3 ∣ k
    · rcases h3 with ⟨r, hr⟩; rw [ite_pos ⟨by omega, ⟨r, hr⟩⟩, ite_pos ⟨r, hr⟩]
    · rw [ite_neg (fun h => h3 h.2), ite_neg h3]
  let loss := if 9 ≤ k ∧ 3 ∣ k then 2 else 0
  have hd_eq_loss : d = k - loss := by dsimp only [d, loss]; rw [hloss_eq]
  have hk1 : k ≠ 1 := by omega
  have hk3 : k ≠ 3 := by omega
  have hk2 : k ≠ 2 := by omega
  have hk6 : k ≠ 6 := by omega
  have hk4 : 4 ≤ k := by omega
  have hpr : price = d + (d + 1) / 2 := rfl
  have hd_ge4 : 4 ≤ d := by rw [hd_eq_loss]; dsimp only [loss]; split_ifs <;> omega
  have h93_iff : (9 ≤ k ∧ 3 ∣ k) ↔ 3 ∣ k := by
    constructor
    · exact fun h => h.2
    · intro h3; refine ⟨?_, h3⟩; rcases h3 with ⟨r, hr⟩; omega

  let U1raw : Fin k → Bool := fun i =>
    if h : 1 ≤ i.val ∧ i.val ≤ d then decide ((i.val - 1) % 2 = 0)
    else if i.val = 0 ∧ ¬(9 ≤ k ∧ 3 ∣ k) then decide ((k - 1) % 2 = 0)
    else false
  let U2raw : Fin k → Bool := fun i =>
    if h : 1 ≤ i.val ∧ i.val ≤ d then decide ((i.val - 1) % 2 = 1)
    else if i.val = 0 ∧ ¬(9 ≤ k ∧ 3 ∣ k) then decide ((k - 1) % 2 = 1)
    else false
  let adjU : (Fin k → Bool) → Fin k → Bool := fun U i =>
    if 9 ≤ k ∧ 3 ∣ k then
      if i.val = 0 then xor (U i) (xor (resSum U 0) (resSum U 1))
      else if i.val = k - 1 then xor (U i) (xor (resSum U 2) (resSum U 1))
      else U i
    else U i
  let U1 : Fin k → Bool := adjU U1raw
  let U2 : Fin k → Bool := adjU U2raw
  have hU_mid : ∀ (U : Fin k → Bool) (i : Fin k), 1 ≤ i.val → i.val ≤ d → adjU U i = U i := by
    intro U i h1 h2; unfold adjU
    by_cases h93 : 9 ≤ k ∧ 3 ∣ k
    · have hd2 : d = k - 2 := by rw [hd_eq_loss]; dsimp only [loss]; rw [ite_pos h93]
      rw [ite_pos h93, ite_neg (by omega), ite_neg (by omega)]
    · rw [ite_neg h93]
  have hU_res : ∀ (U : Fin k → Bool), 9 ≤ k ∧ 3 ∣ k →
      resSum (adjU U) 0 = resSum (adjU U) 1 ∧ resSum (adjU U) 1 = resSum (adjU U) 2 := by
    intro U h93
    have h1 : resSum (adjU U) 1 = resSum U 1 := by
      unfold resSum; apply xorFin_congr; intro i
      by_cases hi0 : i.val = 0
      · rw [hi0]; rfl
      · by_cases hik : i.val = k - 1
        · have hm : i.val % 3 ≠ 1 := by rcases h93.2 with ⟨r, hr⟩; omega
          rw [decide_eq_false hm, Bool.false_and, Bool.false_and]
        · unfold adjU; rw [ite_pos h93, ite_neg hi0, ite_neg hik]
    have h0 : resSum (adjU U) 0 = resSum U 1 := by
      have hdiff : resSum (fun i => xor (adjU U i) (U i)) 0 = xor (resSum U 0) (resSum U 1) := by
        conv_lhs => unfold resSum
        rw [xorFin_single' ⟨0, hk⟩]
        · dsimp only [adjU]; simp only [Nat.zero_mod, decide_true, Bool.true_and, ite_pos h93, ite_true]
          cases U ⟨0, hk⟩ <;> cases resSum U 0 <;> cases resSum U 1 <;> rfl
        · intro i hi
          have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
          by_cases hik : i.val = k - 1
          · have hm : i.val % 3 ≠ 0 := by rcases h93.2 with ⟨r, hr⟩; omega
            rw [decide_eq_false hm, Bool.false_and]
          · dsimp only [adjU]; rw [ite_pos h93, ite_neg hi0, ite_neg hik, Bool.xor_self, Bool.and_false]
      rw [resSum_xor] at hdiff
      revert hdiff; cases resSum (adjU U) 0 <;> cases resSum U 0 <;> cases resSum U 1 <;> simp
    have h2 : resSum (adjU U) 2 = resSum U 1 := by
      have hdiff : resSum (fun i => xor (adjU U i) (U i)) 2 = xor (resSum U 2) (resSum U 1) := by
        conv_lhs => unfold resSum
        rw [xorFin_single' ⟨k - 1, by omega⟩]
        · have hm : (k - 1) % 3 = 2 := by rcases h93.2 with ⟨r, hr⟩; omega
          dsimp only [adjU]; rw [decide_eq_true hm, Bool.true_and, ite_pos h93, ite_neg (by omega), ite_pos rfl]
          cases U ⟨k - 1, by omega⟩ <;> cases resSum U 2 <;> cases resSum U 1 <;> rfl
        · intro i hi
          have hik : i.val ≠ k - 1 := fun h => hi (Fin.ext h)
          by_cases hi0 : i.val = 0
          · rw [hi0]; rfl
          · dsimp only [adjU]; rw [ite_pos h93, ite_neg hi0, ite_neg hik, Bool.xor_self, Bool.and_false]
      rw [resSum_xor] at hdiff
      revert hdiff; cases resSum (adjU U) 2 <;> cases resSum U 2 <;> cases resSum U 1 <;> simp
    rw [h0, h1, h2]; exact ⟨rfl, rfl⟩
  let u0 : Fin k → Bool := fun _ => false
  let u1 : Fin k → Bool := if 9 ≤ k ∧ 3 ∣ k then zOf hk U1 false false else invMix1 hk (by omega) U1
  let u2 : Fin k → Bool := if 9 ≤ k ∧ 3 ∣ k then zOf hk U2 false false else invMix1 hk (by omega) U2
  have hmix_u1 : mix hk 1 u1 = U1 := by
    dsimp only [u1]; by_cases h93 : 9 ≤ k ∧ 3 ∣ k
    · rw [ite_pos h93]; exact mix1_zOf_div3 hk h93.2 (by omega) U1 (hU_res U1raw h93)
    · rw [ite_neg h93]; exact mix1_invMix1 hk (by omega) (fun h3 => h93 (h93_iff.mpr h3)) U1
  have hmix_u2 : mix hk 1 u2 = U2 := by
    dsimp only [u2]; by_cases h93 : 9 ≤ k ∧ 3 ∣ k
    · rw [ite_pos h93]; exact mix1_zOf_div3 hk h93.2 (by omega) U2 (hU_res U2raw h93)
    · rw [ite_neg h93]; exact mix1_invMix1 hk (by omega) (fun h3 => h93 (h93_iff.mpr h3)) U2
  have hU_at : ∀ t : Nat, t < d →
      U1 (ix hk (1 + t)) = decide (t % 2 = 0) ∧ U2 (ix hk (1 + t)) = decide (t % 2 = 1) := by
    intro t ht
    by_cases hlt : 1 + t < k
    · have hix : ix hk (1 + t) = ⟨1 + t, hlt⟩ := Fin.ext (Nat.mod_eq_of_lt hlt)
      rw [hix]
      have h1 : 1 ≤ (⟨1 + t, hlt⟩ : Fin k).val := by dsimp only; omega
      have h2 : (⟨1 + t, hlt⟩ : Fin k).val ≤ d := by dsimp only; omega
      dsimp only [U1, U2]
      rw [hU_mid U1raw _ h1 h2, hU_mid U2raw _ h1 h2]
      dsimp only [U1raw, U2raw]
      rw [dite_pos ⟨h1, h2⟩, dite_pos ⟨h1, h2⟩]
      have hsub : 1 + t - 1 = t := by omega
      rw [hsub]; exact ⟨rfl, rfl⟩
    ·
      have hn93 : ¬(9 ≤ k ∧ 3 ∣ k) := by
        intro h93
        have hd2 : d = k - 2 := by rw [hd_eq_loss]; dsimp only [loss]; rw [ite_pos h93]
        omega
      have hdk : d = k := by rw [hd_eq_loss]; dsimp only [loss]; rw [ite_neg hn93]; omega
      have hteq : t = k - 1 := by omega
      have hix : ix hk (1 + t) = ⟨0, hk⟩ := Fin.ext (by
        dsimp [ix]; rw [show 1 + t = k by omega, Nat.mod_self])
      rw [hix]; dsimp only [U1, U2, adjU]
      rw [ite_neg hn93, ite_neg hn93]; dsimp only [U1raw, U2raw]
      rw [dite_neg (by omega), dite_neg (by omega), ite_pos ⟨rfl, hn93⟩, ite_pos ⟨rfl, hn93⟩, hteq]
      exact ⟨rfl, rfl⟩

  let m := d / 2
  have hpr_eq : price = 3 * m + (if d % 2 = 1 then 2 else 0) := by
    dsimp only [m]; rw [hpr]; split_ifs <;> omega
  let bank1 : Fin price → Bool := fun _ => false
  let site1 : Fin price → Fin k := fun l =>
    if h : l.val < 3 * m then ⟨2 * (l.val / 3), by omega⟩
    else ⟨d - 2, by omega⟩
  let name1 : Fin price → Fin k → Bool := fun l =>
    if h : l.val < 3 * m then
      if l.val % 3 = 0 then u0 else if l.val % 3 = 1 then u1 else u2
    else
      if l.val = 3 * m then u0 else u2
  let names3 : Fin 3 → Fin k → Bool := fun r => if r.val = 0 then u0 else if r.val = 1 then u1 else u2
  let pick1 : Fin price → Fin 3 := fun l =>
    if h : l.val < 3 * m then
      if l.val % 3 = 0 then ⟨0, by omega⟩ else if l.val % 3 = 1 then ⟨1, by omega⟩ else ⟨2, by omega⟩
    else
      if l.val = 3 * m then ⟨0, by omega⟩ else ⟨2, by omega⟩
  have hnp_eq : ∀ p : Fin price, names3 (pick1 p) = name1 p := fun p => by
    dsimp only [names3, pick1, name1]
    by_cases hlt : p.val < 3 * m
    · rw [dite_pos hlt, dite_pos hlt]
      by_cases m0 : p.val % 3 = 0
      · rw [ite_pos m0, ite_pos m0]; rfl
      · by_cases m1 : p.val % 3 = 1
        · rw [ite_neg m0, ite_pos m1, ite_neg m0, ite_pos m1]; rfl
        · rw [ite_neg m0, ite_neg m1, ite_neg m0, ite_neg m1]; rfl
    · rw [dite_neg hlt, dite_neg hlt]
      by_cases hm0 : p.val = 3 * m
      · rw [ite_pos hm0, ite_pos hm0]; rfl
      · rw [ite_neg hm0, ite_neg hm0]; rfl
  refine ⟨names3, pick1, site1, fun width gs hgood baseW baseVals hbase => ?_⟩

  let wMidFn : (t : Nat) → (t < d) → (Fin price → Bool) → Bool := fun t ht v =>
    if hpair : t / 2 < m then
      if t % 2 = 0 then
        xor (xor (v ⟨3 * (t / 2), by omega⟩) (v ⟨3 * (t / 2) + 2, by omega⟩))
            (readBit hk false u2 u0 ⟨2 * (t / 2), by omega⟩)
      else
        xor (xor (v ⟨3 * (t / 2), by omega⟩) (v ⟨3 * (t / 2) + 1, by omega⟩))
            (readBit hk false u1 u0 ⟨2 * (t / 2), by omega⟩)
    else
      xor (xor (v ⟨3 * m, by omega⟩) (v ⟨3 * m + 1, by omega⟩))
          (readBit hk false u2 u0 ⟨d - 2, by omega⟩)
  have hwMid_aff : ∀ t (ht : t < d), IsAffine (wMidFn t ht) := fun t ht => by
    unfold wMidFn; split_ifs
    · exact isAffine_xor (isAffine_xor (isAffine_coord _) (isAffine_coord _)) (isAffine_const _)
    · exact isAffine_xor (isAffine_xor (isAffine_coord _) (isAffine_coord _)) (isAffine_const _)
    · exact isAffine_xor (isAffine_xor (isAffine_coord _) (isAffine_coord _)) (isAffine_const _)
  have hwMid_val : ∀ (x : Fin k → Bool) (t : Nat) (ht : t < d),
      wMidFn t ht (fun p => readBit hk (bank1 p) (name1 p) x (site1 p)) =
      R0 hk false x (ix hk (1 + t)) := by
    intro x t ht
    unfold wMidFn
    by_cases hpair : t / 2 < m
    · rw [dite_pos hpair]
      have hi0 : 3 * (t / 2) < 3 * m := by omega
      have hi1 : 3 * (t / 2) + 1 < 3 * m := by omega
      have hi2 : 3 * (t / 2) + 2 < 3 * m := by omega
      have hst0 : site1 ⟨3 * (t / 2), by omega⟩ = ⟨2 * (t / 2), by omega⟩ := by
        dsimp only [site1]; rw [dite_pos hi0]; exact Fin.ext (by dsimp only; omega)
      have hst1 : site1 ⟨3 * (t / 2) + 1, by omega⟩ = ⟨2 * (t / 2), by omega⟩ := by
        dsimp only [site1]; rw [dite_pos hi1]; exact Fin.ext (by dsimp only; omega)
      have hst2 : site1 ⟨3 * (t / 2) + 2, by omega⟩ = ⟨2 * (t / 2), by omega⟩ := by
        dsimp only [site1]; rw [dite_pos hi2]; exact Fin.ext (by dsimp only; omega)
      have hnm0 : name1 ⟨3 * (t / 2), by omega⟩ = u0 := by
        dsimp only [name1]; rw [dite_pos hi0, ite_pos (by omega)]
      have hnm1 : name1 ⟨3 * (t / 2) + 1, by omega⟩ = u1 := by
        dsimp only [name1]; rw [dite_pos hi1, ite_neg (by omega), ite_pos (by omega)]
      have hnm2 : name1 ⟨3 * (t / 2) + 2, by omega⟩ = u2 := by
        dsimp only [name1]; rw [dite_pos hi2, ite_neg (by omega), ite_neg (by omega)]
      have huA := hU_at (2 * (t / 2)) (by omega)
      have huB := hU_at (2 * (t / 2) + 1) (by omega)
      have hmodA : 2 * (t / 2) % 2 = 0 := by omega
      have hmodB : (2 * (t / 2) + 1) % 2 = 1 := by omega
      by_cases hte : t % 2 = 0
      · rw [ite_pos hte]; dsimp only [bank1]; rw [hst0, hst2, hnm0, hnm2]
        have hd := readBit_diff_zero hk false u2 x ⟨2 * (t / 2), by omega⟩
        simp only [Bool.false_eq_true, ite_false] at hd; rw [hmix_u2] at hd
        have hix1 : ix hk (2 * (t / 2) + 1) = ix hk (1 + 2 * (t / 2)) := congrArg (ix hk) (by omega)
        have hix2 : ix hk (2 * (t / 2) + 2) = ix hk (1 + (2 * (t / 2) + 1)) := congrArg (ix hk) (by omega)
        rw [hix1, hix2, huA.2, huB.2, decide_eq_false (by omega), decide_eq_true hmodB,
            Bool.false_and, Bool.true_and, Bool.false_xor] at hd
        rw [hd]
        have hixt : ix hk (1 + 2 * (t / 2)) = ix hk (1 + t) := congrArg (ix hk) (by omega)
        rw [hixt]
        cases readBit hk false u2 u0 ⟨2 * (t / 2), by omega⟩ <;> cases R0 hk false x (ix hk (1 + t)) <;> rfl
      · rw [ite_neg hte]; dsimp only [bank1]; rw [hst0, hst1, hnm0, hnm1]
        have hd := readBit_diff_zero hk false u1 x ⟨2 * (t / 2), by omega⟩
        simp only [Bool.false_eq_true, ite_false] at hd; rw [hmix_u1] at hd
        have hix1 : ix hk (2 * (t / 2) + 1) = ix hk (1 + 2 * (t / 2)) := congrArg (ix hk) (by omega)
        have hix2 : ix hk (2 * (t / 2) + 2) = ix hk (1 + (2 * (t / 2) + 1)) := congrArg (ix hk) (by omega)
        rw [hix1, hix2, huA.1, huB.1, decide_eq_true hmodA, decide_eq_false (by omega),
            Bool.true_and, Bool.false_and, Bool.xor_false] at hd
        rw [hd]
        have hixt : ix hk (1 + (2 * (t / 2) + 1)) = ix hk (1 + t) := congrArg (ix hk) (by omega)
        rw [hixt]
        cases readBit hk false u1 u0 ⟨2 * (t / 2), by omega⟩ <;> cases R0 hk false x (ix hk (1 + t)) <;> rfl
    ·
      rw [dite_neg hpair]
      have hd_odd : d % 2 = 1 := by omega
      have hteq : t = d - 1 := by omega
      have hst0 : site1 ⟨3 * m, by omega⟩ = ⟨d - 2, by omega⟩ := by
        dsimp only [site1]; rw [dite_neg (by omega)]
      have hst1 : site1 ⟨3 * m + 1, by omega⟩ = ⟨d - 2, by omega⟩ := by
        dsimp only [site1]; rw [dite_neg (by omega)]
      have hnm0 : name1 ⟨3 * m, by omega⟩ = u0 := by
        dsimp only [name1]; rw [dite_neg (by omega), ite_pos rfl]
      have hnm1 : name1 ⟨3 * m + 1, by omega⟩ = u2 := by
        dsimp only [name1]; rw [dite_neg (by omega), ite_neg (by omega)]
      dsimp only [bank1]; rw [hst0, hst1, hnm0, hnm1]
      have hd := readBit_diff_zero hk false u2 x ⟨d - 2, by omega⟩
      simp only [Bool.false_eq_true, ite_false] at hd; rw [hmix_u2] at hd
      have huA := hU_at (d - 2) (by omega)
      have huB := hU_at (d - 1) (by omega)
      have hix1 : ix hk (d - 2 + 1) = ix hk (1 + (d - 2)) := congrArg (ix hk) (by omega)
      have hix2 : ix hk (d - 2 + 2) = ix hk (1 + (d - 1)) := congrArg (ix hk) (by omega)
      rw [hix1, hix2, huA.2, huB.2, decide_eq_true (by omega), decide_eq_false (by omega),
          Bool.true_and, Bool.false_and, Bool.xor_false] at hd
      rw [hd]
      have hixt : ix hk (1 + (d - 1)) = ix hk (1 + t) := congrArg (ix hk) (by omega)
      rw [hixt]
      cases readBit hk false u2 u0 ⟨d - 2, by omega⟩ <;> cases R0 hk false x (ix hk (1 + t)) <;> rfl

  let wRaw : (Fin price → Bool) → Fin k → Bool := fun v i =>
    if h : 1 ≤ i.val ∧ i.val ≤ d then wMidFn (i.val - 1) (by omega) v
    else if h0 : i.val = 0 ∧ ¬(9 ≤ k ∧ 3 ∣ k) then wMidFn (k - 1) (by rw [hd_eq_loss]; dsimp only [loss]; rw [ite_neg h0.2]; omega) v
    else false
  let wFn : (Fin price → Bool) → Fin k → Bool := fun v i =>
    if 9 ≤ k ∧ 3 ∣ k then
      if i.val = 0 then xor (resSum (wRaw v) 0) (resSum (wRaw v) 1)
      else if i.val = k - 1 then xor (resSum (wRaw v) 2) (resSum (wRaw v) 1)
      else wRaw v i
    else wRaw v i
  have hwRaw_aff : ∀ i : Fin k, IsAffine (fun v => wRaw v i) := fun i => by
    dsimp only [wRaw]
    by_cases h : 1 ≤ i.val ∧ i.val ≤ d
    · simp only [dite_pos h]; exact hwMid_aff (i.val - 1) (by omega)
    · by_cases h0 : i.val = 0 ∧ ¬(9 ≤ k ∧ 3 ∣ k)
      · simp only [dite_neg h, dite_pos h0]; exact hwMid_aff (k - 1) (by rw [hd_eq_loss]; dsimp only [loss]; rw [ite_neg h0.2]; omega)
      · simp only [dite_neg h, dite_neg h0]; exact isAffine_const false
  have hres_wRaw_aff : ∀ c : Nat, IsAffine (fun v => resSum (wRaw v) c) := fun c =>
    isAffine_xorFin _ (fun i => isAffine_and_const _ (hwRaw_aff i))
  have hwFn_aff : ∀ i : Fin k, IsAffine (fun v => wFn v i) := fun i => by
    unfold wFn; split_ifs
    · exact isAffine_xor (hres_wRaw_aff 0) (hres_wRaw_aff 1)
    · exact isAffine_xor (hres_wRaw_aff 2) (hres_wRaw_aff 1)
    · exact hwRaw_aff i
    · exact hwRaw_aff i
  have hwFn_val : ∀ x : Fin k → Bool,
      wFn (fun p => readBit hk (bank1 p) (name1 p) x (site1 p)) = R0 hk false x := by
    intro x; let v : Fin price → Bool := fun p => readBit hk (bank1 p) (name1 p) x (site1 p)
    by_cases h93 : 9 ≤ k ∧ 3 ∣ k
    · have hd2 : d = k - 2 := by rw [hd_eq_loss]; dsimp only [loss]; rw [ite_pos h93]
      have hmid : ∀ i : Fin k, 1 ≤ i.val → i.val < k - 1 → wRaw v i = R0 hk false x i := fun i h1 h2 => by
        dsimp only [wRaw]; rw [dite_pos ⟨h1, by omega⟩, hwMid_val x (i.val - 1) (by omega)]
        exact congrArg (R0 hk false x) (Fin.ext (by
          dsimp [ix]; rw [show 1 + (i.val - 1) = i.val by omega, Nat.mod_eq_of_lt i.isLt]))
      have hraw0 : wRaw v ⟨0, hk⟩ = false := by
        dsimp only [wRaw]; rw [dite_neg (by omega), dite_neg (by intro h; exact h.2 h93)]
      have hrawk : wRaw v ⟨k - 1, by omega⟩ = false := by
        dsimp only [wRaw]; rw [dite_neg (by omega), dite_neg (by omega)]
      have hres1 : resSum (wRaw v) 1 = resSum (R0 hk false x) 1 := by
        unfold resSum; apply xorFin_congr; intro i
        by_cases hi0 : i.val = 0
        · rw [hi0]; rfl
        · by_cases hik : i.val = k - 1
          · have hm : i.val % 3 ≠ 1 := by rcases h93.2 with ⟨r, hr⟩; omega
            rw [decide_eq_false hm, Bool.false_and, Bool.false_and]
          · rw [hmid i (by omega) (by omega)]
      have hR_res : ∀ c, c < 3 → resSum (R0 hk false x) c = xorFin (rot hk 1 x) := fun c hc =>
        resSum_mix1 hk h93.2 (by omega) (rot hk 1 x) c hc
      have h0 : xor (resSum (wRaw v) 0) (resSum (wRaw v) 1) = R0 hk false x ⟨0, hk⟩ := by
        have hdiff : resSum (fun i => xor (wRaw v i) (R0 hk false x i)) 0 = R0 hk false x ⟨0, hk⟩ := by
          unfold resSum; rw [xorFin_single' ⟨0, hk⟩]
          · dsimp only; rw [hraw0]; simp
          · intro i hi
            have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            by_cases hik : i.val = k - 1
            · have hm : i.val % 3 ≠ 0 := by rcases h93.2 with ⟨r, hr⟩; omega
              rw [decide_eq_false hm, Bool.false_and]
            · dsimp only; rw [hmid i (by omega) (by omega), Bool.xor_self, Bool.and_false]
        rw [resSum_xor, hR_res 0 (by omega), ← hR_res 1 (by omega), ← hres1] at hdiff
        exact hdiff
      have hk1 : xor (resSum (wRaw v) 2) (resSum (wRaw v) 1) = R0 hk false x ⟨k - 1, by omega⟩ := by
        have hdiff : resSum (fun i => xor (wRaw v i) (R0 hk false x i)) 2 = R0 hk false x ⟨k - 1, by omega⟩ := by
          unfold resSum; rw [xorFin_single' ⟨k - 1, by omega⟩]
          · have hm : (k - 1) % 3 = 2 := by rcases h93.2 with ⟨r, hr⟩; omega
            dsimp only; rw [decide_eq_true hm, Bool.true_and, hrawk, Bool.false_xor]
          · intro i hi
            have hik : i.val ≠ k - 1 := fun h => hi (Fin.ext h)
            by_cases hi0 : i.val = 0
            · rw [hi0]; rfl
            · dsimp only; rw [hmid i (by omega) (by omega), Bool.xor_self, Bool.and_false]
        rw [resSum_xor, hR_res 2 (by omega), ← hR_res 1 (by omega), ← hres1] at hdiff
        exact hdiff
      funext i; dsimp only [wFn]; rw [ite_pos h93]
      by_cases hi0 : i.val = 0
      · rw [ite_pos hi0]; have : i = ⟨0, hk⟩ := Fin.ext hi0; rw [this]; exact h0
      · by_cases hik : i.val = k - 1
        · rw [ite_neg hi0, ite_pos hik]; have : i = ⟨k - 1, by omega⟩ := Fin.ext hik; rw [this]; exact hk1
        · rw [ite_neg hi0, ite_neg hik]; exact hmid i (by omega) (by omega)
    · have hdk : d = k := by rw [hd_eq_loss]; dsimp only [loss]; rw [ite_neg h93]; omega
      funext i; dsimp only [wFn]; rw [ite_neg h93]; dsimp only [wRaw]
      by_cases hi0 : i.val = 0
      · rw [dite_neg (by omega), dite_pos ⟨hi0, h93⟩, hwMid_val x (k - 1) (by omega)]
        exact congrArg (R0 hk false x) (Fin.ext (by
          dsimp [ix]; rw [show 1 + (k - 1) = k by omega, Nat.mod_self, hi0]))
      · rw [dite_pos ⟨by omega, by omega⟩, hwMid_val x (i.val - 1) (by omega)]
        exact congrArg (R0 hk false x) (Fin.ext (by
          dsimp [ix]; rw [show 1 + (i.val - 1) = i.val by omega, Nat.mod_eq_of_lt i.isLt]))

  by_cases h93 : 9 ≤ k ∧ 3 ∣ k
  · have hls : loss = 2 := by dsimp only [loss]; rw [ite_pos h93]
    have hd2 : d = k - 2 := by rw [hd_eq_loss]; dsimp only [loss]; rw [ite_pos h93]
    have hm3 : 3 ≤ m := by dsimp only [m]; omega

    rcases addAffineFn gs hgood baseW baseVals hbase (fun v => !(wFn v ⟨1, by omega⟩)) (isAffine_not (hwFn_aff _)) with
      ⟨gs1, wn1, hg1, hc1, hp1, hwn1⟩
    rcases addAffineFn gs1 hg1 baseW baseVals (fun p => hp1 _ _ (hbase p)) (fun v => wFn v ⟨2, by omega⟩) (hwFn_aff _) with
      ⟨gs2, ww2, hg2, hc2, hp2, hww2⟩
    rcases addAnd gs2 hg2 (hp2 _ _ hwn1) hww2 with ⟨gs3, wp0, hg3, hc3, hp3, hwp0⟩
    have hbase3 : ∀ p, WireSpec width gs3 (baseW p) (baseVals p) := fun p => hp3 _ _ (hp2 _ _ (hp1 _ _ (hbase p)))
    rcases addAffineFn gs3 hg3 baseW baseVals hbase3 (fun v => !(wFn v ⟨3, by omega⟩)) (isAffine_not (hwFn_aff _)) with
      ⟨gs4, wn3, hg4, hc4, hp4, hwn3⟩
    rcases addAffineFn gs4 hg4 baseW baseVals (fun p => hp4 _ _ (hbase3 p)) (fun v => wFn v ⟨4, by omega⟩) (hwFn_aff _) with
      ⟨gs5, ww4, hg5, hc5, hp5, hww4⟩
    rcases addAnd gs5 hg5 (hp5 _ _ hwn3) hww4 with ⟨gs6, wp2, hg6, hc6, hp6, hwp2⟩
    have hp_all : ∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width gs6 w0 f0 :=
      fun w0 f0 h0 => hp6 _ _ (hp5 _ _ (hp4 _ _ (hp3 _ _ (hp2 _ _ (hp1 _ _ h0)))))

    let extW : Fin (price + 2) → Nat := fun q =>
      if hq : q.val < price then baseW ⟨q.val, hq⟩
      else if q.val = price then wp0 else wp2
    let extVals : Fin (price + 2) → List Bool → Bool := fun q inp =>
      if hq : q.val < price then baseVals ⟨q.val, hq⟩ inp
      else if q.val = price then !(wFn (fun p => baseVals p inp) ⟨1, by omega⟩) && wFn (fun p => baseVals p inp) ⟨2, by omega⟩
      else !(wFn (fun p => baseVals p inp) ⟨3, by omega⟩) && wFn (fun p => baseVals p inp) ⟨4, by omega⟩
    have hext : ∀ q : Fin (price + 2), WireSpec width gs6 (extW q) (extVals q) := by
      intro q; unfold extW extVals
      by_cases hq : q.val < price
      · rw [dite_pos hq]
        have hs := hp_all _ _ (hbase ⟨q.val, hq⟩)
        refine ⟨hs.1, fun inp hlen => ?_⟩; dsimp only; rw [dite_pos hq]; exact hs.2 inp hlen
      · rw [dite_neg hq]
        by_cases hqp : q.val = price
        · rw [ite_pos hqp]
          have hs := hp6 _ _ (hp5 _ _ (hp4 _ _ hwp0))
          refine ⟨hs.1, fun inp hlen => ?_⟩; dsimp only; rw [dite_neg hq, ite_pos hqp]; exact hs.2 inp hlen
        · rw [ite_neg hqp]
          refine ⟨hwp2.1, fun inp hlen => ?_⟩; dsimp only; rw [dite_neg hq, ite_neg hqp]; exact hwp2.2 inp hlen

    let vOf : (Fin (price + 2) → Bool) → Fin price → Bool := fun ve p => ve ⟨p.val, by omega⟩
    let wExt : (Fin (price + 2) → Bool) → Fin k → Bool := fun ve => wFn (vOf ve)
    let y1Ext : (Fin (price + 2) → Bool) → Bool := fun ve =>
      xor (ve ⟨0, by omega⟩) (xor (wExt ve ⟨0, hk⟩) (ve ⟨price, by omega⟩))
    let y3Ext : (Fin (price + 2) → Bool) → Bool := fun ve =>
      xor (ve ⟨3, by omega⟩) (xor (wExt ve ⟨2, by omega⟩) (ve ⟨price + 1, by omega⟩))
    let y0Ext : (Fin (price + 2) → Bool) → Bool := fun ve =>
      xor (wExt ve ⟨1, by omega⟩) (xor (wExt ve ⟨2, by omega⟩) (y3Ext ve))
    let recExt : Fin k → (Fin (price + 2) → Bool) → Bool := fun i ve =>
      zOf hk (wExt ve) (y0Ext ve) (y1Ext ve) (ix hk (i.val + 1))
    have hwExt_aff : ∀ i : Fin k, IsAffine (fun ve => wExt ve i) := fun i =>
      isAffine_comp (f := fun v => wFn v i) (g := vOf) (hwFn_aff i) (fun p => isAffine_coord ⟨p.val, by omega⟩)
    have hy1_aff : IsAffine y1Ext :=
      isAffine_xor (isAffine_coord _) (isAffine_xor (hwExt_aff _) (isAffine_coord _))
    have hy3_aff : IsAffine y3Ext :=
      isAffine_xor (isAffine_coord _) (isAffine_xor (hwExt_aff _) (isAffine_coord _))
    have hy0_aff : IsAffine y0Ext :=
      isAffine_xor (hwExt_aff _) (isAffine_xor (hwExt_aff _) hy3_aff)
    have hrec_aff : ∀ i : Fin k, IsAffine (recExt i) := fun i =>
      isAffine_zOf hk wExt y0Ext y1Ext hwExt_aff hy0_aff hy1_aff (ix hk (i.val + 1))
    rcases addAffineVec gs6 hg6 extW extVals hext recExt hrec_aff with ⟨gs7, tapJ, hg7, hc7, hp7, htapJ⟩
    refine ⟨gs7, tapJ, hg7, by rw [hc7, hc6, hc5, hc4, hc3, hc2, hc1]; rw [← hloss_eq]; change gs.countP nonlinear + 1 + 1 = gs.countP nonlinear + loss; rw [hls],
      fun w0 f0 h0 => hp7 _ _ (hp_all _ _ h0), fun i => (htapJ i).1, fun inp x hlen hbase_eq0 i => ?_⟩
    have hbase_eq : ∀ p : Fin price, baseVals p inp = readBit hk (bank1 p) (name1 p) x (site1 p) := fun p => by rw [hbase_eq0 p, hnp_eq p]
    rw [(htapJ i).2 inp hlen]
    let v : Fin price → Bool := fun p => readBit hk (bank1 p) (name1 p) x (site1 p)
    let ve : Fin (price + 2) → Bool := fun q => extVals q inp
    have hv_eq : vOf ve = v := by
      funext p; unfold vOf ve extVals; dsimp only; rw [dite_pos p.isLt, hbase_eq p]
    have hw_eq : wExt ve = R0 hk false x := by unfold wExt; rw [hv_eq]; exact hwFn_val x
    have hve0 : ve ⟨0, by omega⟩ = readBit hk false u0 x ⟨0, hk⟩ := by
      have := congrFun hv_eq ⟨0, by omega⟩
      dsimp only [vOf, v, bank1, site1, name1] at this
      rw [dite_pos (by omega), dite_pos (by omega), ite_pos rfl] at this
      exact this
    have hve3 : ve ⟨3, by omega⟩ = readBit hk false u0 x ⟨2, by omega⟩ := by
      have := congrFun hv_eq ⟨3, by omega⟩
      dsimp only [vOf, v, bank1, site1, name1] at this
      rw [dite_pos (by omega), dite_pos (by omega), ite_pos (by omega)] at this
      exact this
    have hvp0 : ve ⟨price, by omega⟩ = (!(R0 hk false x ⟨1, by omega⟩) && R0 hk false x ⟨2, by omega⟩) := by
      unfold ve extVals; dsimp only; rw [dite_neg (by omega), ite_pos rfl]
      have hb_eq : (fun p => baseVals p inp) = v := funext hbase_eq
      rw [hb_eq, hwFn_val x]
    have hvp2 : ve ⟨price + 1, by omega⟩ = (!(R0 hk false x ⟨3, by omega⟩) && R0 hk false x ⟨4, by omega⟩) := by
      unfold ve extVals; dsimp only; rw [dite_neg (by omega), ite_neg (by omega)]
      have hb_eq : (fun p => baseVals p inp) = v := funext hbase_eq
      rw [hb_eq, hwFn_val x]
    let y := rot hk 1 x
    have hrot_x : ∀ q : Fin k, y (ix hk (q.val + 1)) = x q := fun q => by
      unfold y rot; exact congrArg x (Fin.ext (by
        dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_add_eq q.isLt (by omega)]
        split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega))
    have hrb0 : ∀ s : Fin k, readBit hk false u0 x s =
        xor (x s) (xor (R0 hk false x s) (!(R0 hk false x (ix hk (s.val + 1))) && R0 hk false x (ix hk (s.val + 2)))) := by
      intro s; unfold readBit R0; simp only [Bool.false_eq_true, ite_false]
      have ha0 : add u0 (rot hk 1 x) = rot hk 1 x := by funext q; exact Bool.false_xor _
      have hr0 : rot hk 0 x s = x s := by
        unfold rot; exact congrArg x (Fin.ext (by
          dsimp [ix]; rw [Nat.add_mod_right, Nat.mod_eq_of_lt s.isLt]))
      rw [ha0, hr0]
    have hy1_eq : y1Ext ve = y ⟨1, by omega⟩ := by
      unfold y1Ext; rw [hve0, hw_eq, hvp0, hrb0 ⟨0, hk⟩]
      have h1 : ix hk (0 + 1) = ⟨1, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
      have h2 : ix hk (0 + 2) = ⟨2, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
      have hx0 : x ⟨0, hk⟩ = y ⟨1, by omega⟩ := by rw [← hrot_x ⟨0, hk⟩, h1]
      rw [h1, h2, hx0]
      cases y ⟨1, by omega⟩ <;> cases R0 hk false x ⟨0, hk⟩ <;>
        cases (!(R0 hk false x ⟨1, by omega⟩) && R0 hk false x ⟨2, by omega⟩) <;> rfl
    have hy3_eq : y3Ext ve = y ⟨3, by omega⟩ := by
      unfold y3Ext; rw [hve3, hw_eq, hvp2, hrb0 ⟨2, by omega⟩]
      have h3 : ix hk (2 + 1) = ⟨3, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
      have h4 : ix hk (2 + 2) = ⟨4, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
      have hx2 : x ⟨2, by omega⟩ = y ⟨3, by omega⟩ := by rw [← hrot_x ⟨2, by omega⟩, h3]
      rw [h3, h4, hx2]
      cases y ⟨3, by omega⟩ <;> cases R0 hk false x ⟨2, by omega⟩ <;>
        cases (!(R0 hk false x ⟨3, by omega⟩) && R0 hk false x ⟨4, by omega⟩) <;> rfl
    have hy0_eq : y0Ext ve = y ⟨0, hk⟩ := by
      unfold y0Ext; rw [hw_eq, hy3_eq]
      have hw1 : R0 hk false x ⟨1, by omega⟩ = xor (y ⟨0, hk⟩) (xor (y ⟨1, by omega⟩) (y ⟨2, by omega⟩)) := by
        unfold R0 mix; simp only [Bool.false_eq_true, ite_false]
        have hm : ix hk (1 + k - 1 % k) = ⟨0, hk⟩ := Fin.ext (by
          dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k), show 1 + k - 1 = k by omega, Nat.mod_self])
        have hp : ix hk (1 + 1) = ⟨2, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
        rw [hm, hp]
      have hw2 : R0 hk false x ⟨2, by omega⟩ = xor (y ⟨1, by omega⟩) (xor (y ⟨2, by omega⟩) (y ⟨3, by omega⟩)) := by
        unfold R0 mix; simp only [Bool.false_eq_true, ite_false]
        have hm : ix hk (2 + k - 1 % k) = ⟨1, by omega⟩ := Fin.ext (by
          dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)])
        have hp : ix hk (2 + 1) = ⟨3, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
        rw [hm, hp]
      rw [hw1, hw2]
      cases y ⟨0, hk⟩ <;> cases y ⟨1, by omega⟩ <;> cases y ⟨2, by omega⟩ <;> cases y ⟨3, by omega⟩ <;> rfl
    change recExt i ve = x i
    unfold recExt
    rw [hw_eq, hy0_eq, hy1_eq]
    have hR0y : R0 hk false x = mix hk 1 y := rfl
    rw [hR0y, zOf_eq_of_mix1 hk (by omega) y (ix hk (i.val + 1)), hrot_x i]
  ·
    have hls : loss = 0 := by dsimp only [loss]; rw [ite_neg h93]
    have hndiv : ¬(3 ∣ k) := fun h3 => h93 (h93_iff.mpr h3)
    let recFn : Fin k → (Fin price → Bool) → Bool := fun i v =>
      invMix1 hk (by omega) (wFn v) (ix hk (i.val + 1))
    have hrec_aff : ∀ i : Fin k, IsAffine (recFn i) := fun i =>
      isAffine_invMix1 hk (by omega) wFn hwFn_aff (ix hk (i.val + 1))
    rcases addAffineVec gs hgood baseW baseVals hbase recFn hrec_aff with ⟨gs1, tapJ, hg1, hc1, hp1, htapJ⟩
    refine ⟨gs1, tapJ, hg1, by rw [hc1, ← hloss_eq]; change gs.countP nonlinear = gs.countP nonlinear + loss; rw [hls]; omega, hp1, fun i => (htapJ i).1, fun inp x hlen hbase_eq0 i => ?_⟩
    have hbase_eq : ∀ p : Fin price, baseVals p inp = readBit hk (bank1 p) (name1 p) x (site1 p) := fun p => by rw [hbase_eq0 p, hnp_eq p]
    rw [(htapJ i).2 inp hlen]
    have hb_eq : (fun p => baseVals p inp) = fun p => readBit hk (bank1 p) (name1 p) x (site1 p) := funext hbase_eq
    dsimp only [recFn]; rw [hb_eq, hwFn_val x]
    have hR0y : R0 hk false x = mix hk 1 (rot hk 1 x) := rfl
    rw [hR0y, invMix1_mix1 hk (by omega) hndiv (rot hk 1 x)]
    unfold rot; exact congrArg x (Fin.ext (by
      dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_add_eq i.isLt (by omega)]
      split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega))

def u1_h2 {k : Nat} (_hk : 0 < k) : Fin k → Bool := fun i =>
  if k % 3 = 1 then decide (i.val % 3 = 2)
  else if k % 3 = 2 then decide (i.val % 3 = 1)
  else decide (4 ≤ i.val ∧ i.val % 3 = 1)

lemma mix1_u1_h2_ndiv {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (hndiv : ¬(3 ∣ k)) (i : Fin k) :
    mix hk 1 (u1_h2 hk) i = decide (i.val ≠ 0) := by
  have hm12 : k % 3 = 1 ∨ k % 3 = 2 := by omega
  unfold mix
  have hm : (ix hk (i.val + k - 1 % k)).val = if 1 ≤ i.val then i.val - 1 else k - 1 := by
    dsimp only [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_sub_eq i.isLt (by omega)]
    split_ifs <;> omega
  have hp : (ix hk (i.val + 1)).val = if i.val + 1 < k then i.val + 1 else 0 := by
    dsimp only [ix]; rw [mod_add_eq i.isLt (by omega)]
    split_ifs <;> omega
  rcases hm12 with h1 | h2
  · have hu : ∀ q : Fin k, u1_h2 hk q = decide (q.val % 3 = 2) := fun q => by
      unfold u1_h2; rw [ite_pos h1]
    rw [hu, hu, hu, hm, hp]
    by_cases hi0 : i.val = 0
    · rw [ite_neg (by omega), ite_pos (by omega), hi0, decide_eq_false (by omega),
          decide_eq_false (by omega), decide_eq_false (by omega), decide_eq_false (by omega)]; rfl
    · rw [decide_eq_true hi0, ite_pos (by omega)]
      by_cases hik : i.val + 1 < k
      · rw [ite_pos hik]
        have h3 : (i.val - 1) % 3 = 2 ∨ i.val % 3 = 2 ∨ (i.val + 1) % 3 = 2 := by omega
        by_cases a : (i.val - 1) % 3 = 2
        · rw [decide_eq_true a, decide_eq_false (by omega), decide_eq_false (by omega)]; rfl
        · by_cases b : i.val % 3 = 2
          · rw [decide_eq_false a, decide_eq_true b, decide_eq_false (by omega)]; rfl
          · have c : (i.val + 1) % 3 = 2 := by omega
            rw [decide_eq_false a, decide_eq_false b, decide_eq_true c]; rfl
      · rw [ite_neg hik]
        have heq : i.val = k - 1 := by omega
        rw [decide_eq_true (by omega : (i.val - 1) % 3 = 2), decide_eq_false (by omega : i.val % 3 ≠ 2),
            decide_eq_false (by omega : 0 % 3 ≠ 2)]; rfl
  · have hu : ∀ q : Fin k, u1_h2 hk q = decide (q.val % 3 = 1) := fun q => by
      unfold u1_h2; rw [ite_neg (by omega), ite_pos h2]
    rw [hu, hu, hu, hm, hp]
    by_cases hi0 : i.val = 0
    · rw [ite_neg (by omega), ite_pos (by omega), hi0, decide_eq_true (by omega : (k - 1) % 3 = 1),
          decide_eq_false (by omega : 0 % 3 ≠ 1), decide_eq_true (by omega : (0 + 1) % 3 = 1),
          decide_eq_false (by omega)]; rfl
    · rw [decide_eq_true hi0, ite_pos (by omega)]
      by_cases hik : i.val + 1 < k
      · rw [ite_pos hik]
        by_cases a : (i.val - 1) % 3 = 1
        · rw [decide_eq_true a, decide_eq_false (by omega), decide_eq_false (by omega)]; rfl
        · by_cases b : i.val % 3 = 1
          · rw [decide_eq_false a, decide_eq_true b, decide_eq_false (by omega)]; rfl
          · have c : (i.val + 1) % 3 = 1 := by omega
            rw [decide_eq_false a, decide_eq_false b, decide_eq_true c]; rfl
      · rw [ite_neg hik]
        have heq : i.val = k - 1 := by omega
        rw [decide_eq_false (by omega : (i.val - 1) % 3 ≠ 1), decide_eq_true (by omega : i.val % 3 = 1),
            decide_eq_false (by omega : 0 % 3 ≠ 1)]; rfl

lemma mix1_u1_h2_div {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (h3 : 3 ∣ k) (i : Fin k) :
    mix hk 1 (u1_h2 hk) i = decide (3 ≤ i.val) := by
  rcases h3 with ⟨r, hr⟩
  have hu : ∀ q : Fin k, u1_h2 hk q = decide (4 ≤ q.val ∧ q.val % 3 = 1) := fun q => by
    unfold u1_h2; rw [ite_neg (by omega), ite_neg (by omega)]
  unfold mix
  have hm : (ix hk (i.val + k - 1 % k)).val = if 1 ≤ i.val then i.val - 1 else k - 1 := by
    dsimp only [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_sub_eq i.isLt (by omega)]
    split_ifs <;> omega
  have hp : (ix hk (i.val + 1)).val = if i.val + 1 < k then i.val + 1 else 0 := by
    dsimp only [ix]; rw [mod_add_eq i.isLt (by omega)]
    split_ifs <;> omega
  rw [hu, hu, hu, hm, hp]
  by_cases hi0 : i.val = 0
  · rw [ite_neg (by omega), ite_pos (by omega), hi0,
        decide_eq_false (by omega : ¬(4 ≤ k - 1 ∧ (k - 1) % 3 = 1)),
        decide_eq_false (by omega : ¬(4 ≤ 0 ∧ 0 % 3 = 1)),
        decide_eq_false (by omega : ¬(4 ≤ 0 + 1 ∧ (0 + 1) % 3 = 1)),
        decide_eq_false (by omega : ¬(3 ≤ 0))]; rfl
  · rw [ite_pos (by omega)]
    by_cases hi3 : i.val < 3
    · rw [ite_pos (by omega),
          decide_eq_false (by omega : ¬(4 ≤ i.val - 1 ∧ (i.val - 1) % 3 = 1)),
          decide_eq_false (by omega : ¬(4 ≤ i.val ∧ i.val % 3 = 1)),
          decide_eq_false (by omega : ¬(4 ≤ i.val + 1 ∧ (i.val + 1) % 3 = 1)),
          decide_eq_false (by omega : ¬(3 ≤ i.val))]; rfl
    · rw [decide_eq_true (by omega : 3 ≤ i.val)]
      by_cases hi3eq : i.val = 3
      · rw [ite_pos (by omega), hi3eq,
            decide_eq_false (by omega : ¬(4 ≤ 3 - 1 ∧ (3 - 1) % 3 = 1)),
            decide_eq_false (by omega : ¬(4 ≤ 3 ∧ 3 % 3 = 1)),
            decide_eq_true (by omega : 4 ≤ 3 + 1 ∧ (3 + 1) % 3 = 1)]; rfl
      · by_cases hi4eq : i.val = 4
        · rw [ite_pos (by omega), hi4eq,
              decide_eq_false (by omega : ¬(4 ≤ 4 - 1 ∧ (4 - 1) % 3 = 1)),
              decide_eq_true (by omega : 4 ≤ 4 ∧ 4 % 3 = 1),
              decide_eq_false (by omega : ¬(4 ≤ 4 + 1 ∧ (4 + 1) % 3 = 1))]; rfl
        · by_cases hik : i.val + 1 < k
          · rw [ite_pos hik]
            by_cases a : (i.val - 1) % 3 = 1
            · rw [decide_eq_true (by omega : 4 ≤ i.val - 1 ∧ (i.val - 1) % 3 = 1),
                  decide_eq_false (by omega : ¬(4 ≤ i.val ∧ i.val % 3 = 1)),
                  decide_eq_false (by omega : ¬(4 ≤ i.val + 1 ∧ (i.val + 1) % 3 = 1))]; rfl
            · by_cases b : i.val % 3 = 1
              · rw [decide_eq_false (by omega : ¬(4 ≤ i.val - 1 ∧ (i.val - 1) % 3 = 1)),
                    decide_eq_true (by omega : 4 ≤ i.val ∧ i.val % 3 = 1),
                    decide_eq_false (by omega : ¬(4 ≤ i.val + 1 ∧ (i.val + 1) % 3 = 1))]; rfl
              · rw [decide_eq_false (by omega : ¬(4 ≤ i.val - 1 ∧ (i.val - 1) % 3 = 1)),
                    decide_eq_false (by omega : ¬(4 ≤ i.val ∧ i.val % 3 = 1)),
                    decide_eq_true (by omega : 4 ≤ i.val + 1 ∧ (i.val + 1) % 3 = 1)]; rfl
          · rw [ite_neg hik]
            have heq : i.val = k - 1 := by omega
            rw [decide_eq_true (by omega : 4 ≤ i.val - 1 ∧ (i.val - 1) % 3 = 1),
                decide_eq_false (by omega : ¬(4 ≤ i.val ∧ i.val % 3 = 1)),
                decide_eq_false (by omega : ¬(4 ≤ 0 ∧ 0 % 3 = 1))]; rfl

lemma mix2_u1_h2_ndiv {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (hndiv : ¬(3 ∣ k)) :
    let V := mix hk 2 (u1_h2 hk)
    V ⟨3, by omega⟩ = true ∧ V ⟨4, by omega⟩ = true ∧ xor (V ⟨1, by omega⟩) (V ⟨2, by omega⟩) = true := by
  intro V
  have h1m : (ix hk (1 + k - 2 % k)).val = k - 1 := by
    dsimp only [ix]; rw [Nat.mod_eq_of_lt (by omega : 2 < k), mod_sub_eq (by omega) (by omega), ite_neg (by omega)]; omega
  have h1p : (ix hk (1 + 2)).val = 3 := Nat.mod_eq_of_lt (by omega)
  have h2m : (ix hk (2 + k - 2 % k)).val = 0 := by
    dsimp only [ix]; rw [Nat.mod_eq_of_lt (by omega : 2 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)]
  have h2p : (ix hk (2 + 2)).val = 4 := Nat.mod_eq_of_lt (by omega)
  have h3m : (ix hk (3 + k - 2 % k)).val = 1 := by
    dsimp only [ix]; rw [Nat.mod_eq_of_lt (by omega : 2 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)]
  have h3p : (ix hk (3 + 2)).val = 5 := Nat.mod_eq_of_lt (by omega)
  have h4m : (ix hk (4 + k - 2 % k)).val = 2 := by
    dsimp only [ix]; rw [Nat.mod_eq_of_lt (by omega : 2 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)]
  have h4p : (ix hk (4 + 2)).val = 6 := Nat.mod_eq_of_lt (by omega)
  have hm12 : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hm12 with h1 | h2
  · have hu : ∀ q : Fin k, u1_h2 hk q = decide (q.val % 3 = 2) := fun q => by unfold u1_h2; rw [ite_pos h1]
    dsimp only [V]; unfold mix; simp only [hu]
    rw [h1m, h1p, h2m, h2p, h3m, h3p, h4m, h4p]
    rw [decide_eq_false (by omega : (k - 1) % 3 ≠ 2)]
    simp
  · have hu : ∀ q : Fin k, u1_h2 hk q = decide (q.val % 3 = 1) := fun q => by unfold u1_h2; rw [ite_neg (by omega), ite_pos h2]
    dsimp only [V]; unfold mix; simp only [hu]
    rw [h1m, h1p, h2m, h2p, h3m, h3p, h4m, h4p]
    rw [decide_eq_true (by omega : (k - 1) % 3 = 1)]
    simp

lemma mix2_u1_h2_div {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (h3 : 3 ∣ k) :
    let V := mix hk 2 (u1_h2 hk)
    V ⟨4, by omega⟩ = true ∧ V ⟨5, by omega⟩ = true ∧ xor (V ⟨2, by omega⟩) (V ⟨3, by omega⟩) = true := by
  intro V
  rcases h3 with ⟨r, hr⟩
  have hk9 : 9 ≤ k := by omega
  have hu : ∀ q : Fin k, u1_h2 hk q = decide (4 ≤ q.val ∧ q.val % 3 = 1) := fun q => by
    unfold u1_h2; rw [ite_neg (by omega), ite_neg (by omega)]
  have h2m : (ix hk (2 + k - 2 % k)).val = 0 := by
    dsimp only [ix]; rw [Nat.mod_eq_of_lt (by omega : 2 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)]
  have h2p : (ix hk (2 + 2)).val = 4 := Nat.mod_eq_of_lt (by omega)
  have h3m : (ix hk (3 + k - 2 % k)).val = 1 := by
    dsimp only [ix]; rw [Nat.mod_eq_of_lt (by omega : 2 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)]
  have h3p : (ix hk (3 + 2)).val = 5 := Nat.mod_eq_of_lt (by omega)
  have h4m : (ix hk (4 + k - 2 % k)).val = 2 := by
    dsimp only [ix]; rw [Nat.mod_eq_of_lt (by omega : 2 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)]
  have h4p : (ix hk (4 + 2)).val = 6 := Nat.mod_eq_of_lt (by omega)
  have h5m : (ix hk (5 + k - 2 % k)).val = 3 := by
    dsimp only [ix]; rw [Nat.mod_eq_of_lt (by omega : 2 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)]
  have h5p : (ix hk (5 + 2)).val = 7 := Nat.mod_eq_of_lt (by omega)
  dsimp only [V]; unfold mix; simp only [hu]
  rw [h2m, h2p, h3m, h3p, h4m, h4p, h5m, h5p]
  simp

lemma rot_scale {k : Nat} (hk : 0 < k) (s : Nat) (b : Bool) (w : Fin k → Bool) :
    rot hk s (fun q => b && w q) = fun q => b && rot hk s w q := rfl

lemma mix_scale {k : Nat} (hk : 0 < k) (d : Nat) (b : Bool) (w : Fin k → Bool) :
    mix hk d (fun q => b && w q) = fun q => b && mix hk d w q := by
  funext q; unfold mix; cases b <;> simp

lemma rot2_rot1 {k : Nat} (hk : 0 < k) (hk4 : 4 ≤ k) (x : Fin k → Bool) :
    rot hk 2 (rot hk 1 x) = rot hk 3 x := by
  funext q; unfold rot; apply congrArg x; apply Fin.ext; dsimp [ix]
  rw [Nat.mod_eq_of_lt (by omega : 1 < k), Nat.mod_eq_of_lt (by omega : 2 < k),
      Nat.mod_eq_of_lt (by omega : 3 < k), mod_sub_eq q.isLt (by omega), mod_sub_eq q.isLt (by omega)]
  split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega

lemma mix2_rot2_comm {k : Nat} (hk : 0 < k) (hk5 : 5 ≤ k) (w : Fin k → Bool) :
    mix hk 2 (rot hk 2 w) = rot hk 2 (mix hk 2 w) := by
  funext q; unfold mix rot
  have h1 : ix hk ((ix hk (q.val + k - 2 % k)).val + k - 2 % k) =
      ix hk ((ix hk (q.val + k - 2 % k)).val + k - 2 % k) := rfl
  have h2 : ix hk ((ix hk (q.val + 2)).val + k - 2 % k) =
      ix hk ((ix hk (q.val + k - 2 % k)).val + 2) := by
    apply Fin.ext; dsimp [ix]
    rw [Nat.mod_eq_of_lt (by omega : 2 < k), mod_add_eq q.isLt (by omega), mod_sub_eq q.isLt (by omega)]
    split_ifs <;> rw [mod_sub_eq (by omega) (by omega), mod_add_eq (by omega) (by omega)] <;> split_ifs <;> omega
  rw [h2]

def per3 {k : Nat} (a b : Bool) (i : Fin k) : Bool :=
  if i.val % 3 = 0 then a else if i.val % 3 = 1 then b else xor a b

lemma mix2_per3 {k : Nat} (hk : 0 < k) (hk6 : 6 ≤ k) (h3 : 3 ∣ k) (a b : Bool) :
    mix hk 2 (per3 a b) = fun _ => false := by
  rcases h3 with ⟨r, hr⟩
  funext q; unfold mix per3
  have hm : (ix hk (q.val + k - 2 % k)).val % 3 = (q.val + 1) % 3 := by
    dsimp only [ix]; rw [Nat.mod_eq_of_lt (by omega : 2 < k), mod_sub_eq q.isLt (by omega)]; split_ifs <;> omega
  have hp : (ix hk (q.val + 2)).val % 3 = (q.val + 2) % 3 := by
    dsimp only [ix]; rw [mod_add_eq q.isLt (by omega)]; split_ifs <;> omega
  rw [hm, hp]
  have hq3 : q.val % 3 = 0 ∨ q.val % 3 = 1 ∨ q.val % 3 = 2 := by omega
  rcases hq3 with h0 | h1 | h2
  · rw [ite_neg (by omega), ite_pos (by omega), ite_pos h0, ite_neg (by omega), ite_neg (by omega)]
    cases a <;> cases b <;> rfl
  · rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_pos h1, ite_pos (by omega)]
    cases a <;> cases b <;> rfl
  · rw [ite_pos (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_pos (by omega)]
    cases a <;> cases b <;> rfl

lemma zOf_mix1_eq_add_per3 {k : Nat} (hk : 0 < k) (hk2 : 2 ≤ k) (v : Fin k → Bool) :
    zOf hk (mix hk 1 v) false false = add v (per3 (v ⟨0, hk⟩) (v ⟨1, by omega⟩)) := by
  funext i
  have hy : v i = xor (zOf hk (mix hk 1 v) false false i) (per3 (v ⟨0, hk⟩) (v ⟨1, by omega⟩) i) := by
    rw [← zOf_eq_of_mix1 hk hk2 v i]
    have hadd : mix hk 1 v = add (mix hk 1 v) (fun _ => false) := by funext p; unfold add; exact (Bool.xor_false _).symm
    unfold zOf per3
    conv_lhs => rw [hadd, show v ⟨0, hk⟩ = xor false (v ⟨0, hk⟩) from (Bool.false_xor _).symm,
      show v ⟨1, by omega⟩ = xor false (v ⟨1, by omega⟩) from (Bool.false_xor _).symm]
    rw [zPair_xor, zPair_zero]
  dsimp only [add]; rw [hy]
  cases zOf hk (mix hk 1 v) false false i <;> cases per3 (v ⟨0, hk⟩) (v ⟨1, by omega⟩) i <;> rfl

def chainXor (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | m + 1 => xor (chainXor f m) (f m)

lemma isAffine_chainXor {M : Nat} (f : Nat → (Fin M → Bool) → Bool)
    (hf : ∀ s, IsAffine (f s)) (m : Nat) :
    IsAffine (fun v => chainXor (fun s => f s v) m) := by
  induction m with
  | zero => exact isAffine_const false
  | succ m ih => exact isAffine_xor ih (hf m)

lemma chainXor_telescope (f g : Nat → Bool) (m : Nat)
    (h : ∀ s, s < m → f s = xor (g s) (g (s + 1))) :
    chainXor f m = xor (g 0) (g m) := by
  induction m with
  | zero => exact (Bool.xor_self (g 0)).symm
  | succ m ih =>
    unfold chainXor
    rw [ih (fun s hs => h s (by omega)), h m (by omega)]
    cases g 0 <;> cases g m <;> cases g (m + 1) <;> rfl

lemma isAffine_and_const_right {n : Nat} (b : Bool) {f : (Fin n → Bool) → Bool} (hf : IsAffine f) :
    IsAffine (fun x => f x && b) := by
  have heq : (fun x => f x && b) = (fun x => b && f x) := funext fun x => Bool.and_comm _ _
  rw [heq]; exact isAffine_and_const b hf

lemma h2_pair_df {k d : Nat} (hk : 0 < k) (hd_pos : 0 < d) (sitePair : Nat → Fin k)
    (x : Fin k → Bool) (t : Nat) (ht : t < d) :
    let u0 : Fin k → Bool := fun _ => false
    let u1 : Fin k → Bool := u1_h2 hk
    let names2 : Fin 2 → Fin k → Bool := fun r => if r.val = 0 then u0 else u1
    let pick1 : Fin (2 * d) → Fin 2 := fun l => if l.val % 2 = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩
    let bank1 : Fin (2 * d) → Bool := fun l => decide (2 * (d - 1) ≤ l.val)
    let site1 : Fin (2 * d) → Fin k := fun l => sitePair (l.val / 2)
    let v : Fin (2 * d) → Bool := fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)
    let col := decide (t = d - 1)
    xor (xor (v ⟨2 * t, by omega⟩) (v ⟨2 * t + 1, by omega⟩))
        (readBit hk col u1 u0 (sitePair t)) =
    xor (mix hk (if col then 2 else 1) u1 (ix hk ((sitePair t).val + 1)) && R0 hk col x (ix hk ((sitePair t).val + 2)))
        (mix hk (if col then 2 else 1) u1 (ix hk ((sitePair t).val + 2)) && R0 hk col x (ix hk ((sitePair t).val + 1))) := by
  intro u0 u1 names2 pick1 bank1 site1 v col
  have hb0 : bank1 ⟨2 * t, by omega⟩ = col := by
    dsimp only [bank1, col]; exact decide_eq_decide_of_iff (by omega)
  have hb1 : bank1 ⟨2 * t + 1, by omega⟩ = col := by
    dsimp only [bank1, col]; exact decide_eq_decide_of_iff (by omega)
  have hn0 : names2 (pick1 ⟨2 * t, by omega⟩) = u0 := by
    dsimp only [pick1, names2]
    rw [ite_pos (show (2 * t) % 2 = 0 by omega), ite_pos rfl]
  have hn1 : names2 (pick1 ⟨2 * t + 1, by omega⟩) = u1 := by
    dsimp only [pick1, names2]
    rw [ite_neg (show (2 * t + 1) % 2 ≠ 0 by omega)]
    dsimp only
    rw [ite_neg (by decide)]
  have hs0 : site1 ⟨2 * t, by omega⟩ = sitePair t := by
    dsimp only [site1]; congr 1; omega
  have hs1 : site1 ⟨2 * t + 1, by omega⟩ = sitePair t := by
    dsimp only [site1]; congr 1; omega
  dsimp only [v]
  rw [hb0, hb1, hn0, hn1, hs0, hs1]
  have hd := readBit_diff_zero hk col u1 x (sitePair t)
  dsimp only [u0]; rw [hd]
  cases readBit hk col u1 (fun _ => false) (sitePair t) <;>
    cases (mix hk (if col then 2 else 1) u1 (ix hk ((sitePair t).val + 1)) && R0 hk col x (ix hk ((sitePair t).val + 2))) <;>
    cases (mix hk (if col then 2 else 1) u1 (ix hk ((sitePair t).val + 2)) && R0 hk col x (ix hk ((sitePair t).val + 1))) <;> rfl

lemma single_key_spec_h2_div {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (h3 : 3 ∣ k) :
    let d := k - 2
    let names2 : Fin 2 → Fin k → Bool := fun r => if r.val = 0 then (fun _ => false) else u1_h2 hk
    ∃ (pick1 : Fin (2 * d) → Fin 2) (bank1 : Fin (2 * d) → Bool) (site1 : Fin (2 * d) → Fin k),
      (Finset.univ.filter (fun p : Fin (2 * d) => bank1 p = true)).card = 2 ∧
      ∀ (width : Nat) (gs : List Gate), Good width gs →
        ∀ (baseW : Fin (2 * d) → Nat) (baseVals : Fin (2 * d) → List Bool → Bool),
        (∀ p, WireSpec width gs (baseW p) (baseVals p)) →
        ∃ (gs' : List Gate) (tapJ : Fin k → Nat),
          Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear + 2 ∧
          (∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width gs' w0 f0) ∧
          (∀ i : Fin k, tapJ i < width + gs'.length) ∧
          ∀ (inp : List Bool) (x : Fin k → Bool),
            inp.length = width →
            (∀ p : Fin (2 * d), baseVals p inp = readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)) →
            ∀ i : Fin k, (Circuit.wires ⟨gs', 0⟩ inp).getD (tapJ i) false = x i := by
  intro d names2
  rcases h3 with ⟨r, hr⟩
  have hk9 : 9 ≤ k := by omega
  have hd_ge7 : 7 ≤ d := by dsimp only [d]; omega
  let u0 : Fin k → Bool := fun _ => false
  let u1 : Fin k → Bool := u1_h2 hk
  let pick1 : Fin (2 * d) → Fin 2 := fun l => if l.val % 2 = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩
  let bank1 : Fin (2 * d) → Bool := fun l => decide (2 * (d - 1) ≤ l.val)
  let sitePair : Nat → Fin k := fun t =>
    if t = 0 then ⟨k - 2, by omega⟩
    else if t = 1 then ⟨1, by omega⟩
    else if h : t < d - 1 then ⟨t, by dsimp only [d] at h; omega⟩
    else ⟨3, by omega⟩
  let site1 : Fin (2 * d) → Fin k := fun l => sitePair (l.val / 2)
  have hbank_card : (Finset.univ.filter (fun p : Fin (2 * d) => bank1 p = true)).card = 2 := by
    have heq : Finset.univ.filter (fun p : Fin (2 * d) => bank1 p = true) =
        {⟨2 * (d - 1), by omega⟩, ⟨2 * (d - 1) + 1, by omega⟩} := by
      ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, bank1, decide_eq_true_eq,
        Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [heq, Finset.card_pair]
    intro h; have := congrArg Fin.val h; dsimp only at this; omega
  let dfFn : Nat → (Fin (2 * d) → Bool) → Bool := fun t v =>
    if ht : t < d then
      xor (xor (v ⟨2 * t, by omega⟩) (v ⟨2 * t + 1, by omega⟩))
          (readBit hk (decide (t = d - 1)) u1 u0 (sitePair t))
    else false
  have hdf_aff : ∀ t : Nat, IsAffine (dfFn t) := fun t => by
    dsimp only [dfFn]
    by_cases ht : t < d
    · simp only [dite_pos ht]
      exact isAffine_xor (isAffine_xor (isAffine_coord _) (isAffine_coord _)) (isAffine_const _)
    · simp only [dite_neg ht]; exact isAffine_const false
  have hU : ∀ q : Fin k, mix hk 1 u1 q = decide (3 ≤ q.val) := fun q => mix1_u1_h2_div hk hk7 ⟨r, hr⟩ q
  have hV := mix2_u1_h2_div hk hk7 ⟨r, hr⟩
  have hdf0 : ∀ x : Fin k → Bool,
      dfFn 0 (fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)) = R0 hk false x ⟨0, hk⟩ := fun x => by
    dsimp only [dfFn]; rw [dite_pos (by omega)]
    have h := h2_pair_df hk (by omega : 0 < d) sitePair x 0 (by omega)
    have hcol : decide (0 = d - 1) = false := decide_eq_false (by omega)
    have hsp : sitePair 0 = ⟨k - 2, by omega⟩ := by dsimp only [sitePair]; rw [ite_pos rfl]
    refine Eq.trans h ?_
    rw [hcol, hsp]; simp only [Bool.false_eq_true, ite_false]
    rw [show u1_h2 hk = u1 from rfl, hU, hU]
    have h1 : ix hk (k - 2 + 1) = ⟨k - 1, by omega⟩ := Fin.ext (by dsimp [ix]; rw [show k - 2 + 1 = k - 1 by omega, Nat.mod_eq_of_lt (by omega)])
    have h2 : ix hk (k - 2 + 2) = ⟨0, hk⟩ := Fin.ext (by dsimp [ix]; rw [show k - 2 + 2 = k by omega, Nat.mod_self])
    rw [h1, h2, decide_eq_true (by omega : 3 ≤ k - 1), decide_eq_false (by omega : ¬(3 ≤ 0))]
    simp
  have hdf1 : ∀ x : Fin k → Bool,
      dfFn 1 (fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)) = R0 hk false x ⟨2, by omega⟩ := fun x => by
    dsimp only [dfFn]; rw [dite_pos (by omega)]
    have h := h2_pair_df hk (by omega : 0 < d) sitePair x 1 (by omega)
    have hcol : decide (1 = d - 1) = false := decide_eq_false (by omega)
    have hsp : sitePair 1 = ⟨1, by omega⟩ := by dsimp only [sitePair]; rw [ite_neg (by omega), ite_pos rfl]
    refine Eq.trans h ?_
    rw [hcol, hsp]; simp only [Bool.false_eq_true, ite_false]
    rw [show u1_h2 hk = u1 from rfl, hU, hU]
    have h1 : ix hk (1 + 1) = ⟨2, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have h2 : ix hk (1 + 2) = ⟨3, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [h1, h2, decide_eq_false (by omega : ¬(3 ≤ 2)), decide_eq_true (by omega : 3 ≤ 3)]
    simp
  have hdf_mid : ∀ (x : Fin k → Bool) (t : Nat) (ht2 : 2 ≤ t) (htd : t < k - 3),
      dfFn t (fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)) =
      xor (R0 hk false x ⟨t + 1, by omega⟩) (R0 hk false x ⟨t + 2, by omega⟩) := fun x t ht2 htd => by
    have htd' : t < d - 1 := by dsimp only [d]; omega
    dsimp only [dfFn]; rw [dite_pos (by omega)]
    have h := h2_pair_df hk (by omega : 0 < d) sitePair x t (by omega)
    have hcol : decide (t = d - 1) = false := decide_eq_false (by omega)
    have hsp : sitePair t = ⟨t, by omega⟩ := by
      dsimp only [sitePair]; rw [ite_neg (by omega), ite_neg (by omega), dite_pos htd']
    refine Eq.trans h ?_
    rw [hcol, hsp]; simp only [Bool.false_eq_true, ite_false]
    rw [show u1_h2 hk = u1 from rfl, hU, hU]
    have h1 : ix hk (t + 1) = ⟨t + 1, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have h2 : ix hk (t + 2) = ⟨t + 2, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [h1, h2, decide_eq_true (by omega : 3 ≤ t + 1), decide_eq_true (by omega : 3 ≤ t + 2)]
    simp [Bool.xor_comm]
  have hdt : ∀ x : Fin k → Bool,
      dfFn (d - 1) (fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)) =
      xor (R0 hk true x ⟨4, by omega⟩) (R0 hk true x ⟨5, by omega⟩) := fun x => by
    dsimp only [dfFn]; rw [dite_pos (by omega)]
    have h := h2_pair_df hk (by omega : 0 < d) sitePair x (d - 1) (by omega)
    have hcol : decide (d - 1 = d - 1) = true := decide_eq_true rfl
    have hsp : sitePair (d - 1) = ⟨3, by omega⟩ := by
      dsimp only [sitePair]; rw [ite_neg (by omega), ite_neg (by omega), dite_neg (by omega)]
    rw [hcol, hsp] at h ⊢; simp only [ite_true] at h
    have h1 : ix hk (3 + 1) = ⟨4, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have h2 : ix hk (3 + 2) = ⟨5, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [h1, h2, hV.1, hV.2.1, Bool.true_and, Bool.true_and] at h
    rw [h]; exact Bool.xor_comm _ _
  let wbRaw : (Fin (2 * d) → Bool) → Fin k → Bool := fun v i =>
    if i.val = 0 then dfFn 0 v
    else if i.val = 2 then dfFn 1 v
    else if 4 ≤ i.val ∧ i.val ≤ k - 2 then chainXor (fun s => dfFn (s + 2) v) (i.val - 3)
    else false
  let wbFn : (Fin (2 * d) → Bool) → Fin k → Bool := fun v i =>
    if i.val = 1 then xor (resSum (wbRaw v) 0) (resSum (wbRaw v) 1)
    else if i.val = k - 1 then xor (resSum (wbRaw v) 0) (resSum (wbRaw v) 2)
    else wbRaw v i
  let zbFn : (Fin (2 * d) → Bool) → Fin k → Bool := fun v => zOf hk (wbFn v) false false
  let rtbFn : (Fin (2 * d) → Bool) → Fin k → Bool := fun v => mix hk 2 (rot hk 2 (zbFn v))
  let bFn : (Fin (2 * d) → Bool) → Bool := fun v =>
    xor (dfFn (d - 1) v) (xor (rtbFn v ⟨4, by omega⟩) (rtbFn v ⟨5, by omega⟩))
  let wFn : (Fin (2 * d) → Bool) → Fin k → Bool := fun v i => xor (wbFn v i) (bFn v && mix hk 1 u1 i)
  have hwbRaw_aff : ∀ i : Fin k, IsAffine (fun v => wbRaw v i) := fun i => by
    dsimp only [wbRaw]
    by_cases h0 : i.val = 0
    · simp only [ite_pos h0]; exact hdf_aff 0
    · by_cases h2 : i.val = 2
      · simp only [ite_neg h0, ite_pos h2]; exact hdf_aff 1
      · by_cases h4 : 4 ≤ i.val ∧ i.val ≤ k - 2
        · simp only [ite_neg h0, ite_neg h2, ite_pos h4]
          exact isAffine_chainXor (fun s v => dfFn (s + 2) v) (fun s => hdf_aff (s + 2)) (i.val - 3)
        · simp only [ite_neg h0, ite_neg h2, ite_neg h4]; exact isAffine_const false
  have hwb_aff : ∀ i : Fin k, IsAffine (fun v => wbFn v i) := fun i => by
    have hres : ∀ c, IsAffine (fun v => resSum (wbRaw v) c) := fun c =>
      isAffine_xorFin _ (fun q => isAffine_and_const _ (hwbRaw_aff q))
    dsimp only [wbFn]
    by_cases h1 : i.val = 1
    · simp only [ite_pos h1]; exact isAffine_xor (hres 0) (hres 1)
    · by_cases hk1 : i.val = k - 1
      · simp only [ite_neg h1, ite_pos hk1]; exact isAffine_xor (hres 0) (hres 2)
      · simp only [ite_neg h1, ite_neg hk1]; exact hwbRaw_aff i
  have hzb_aff : ∀ i : Fin k, IsAffine (fun v => zbFn v i) := fun i =>
    isAffine_zOf hk wbFn (fun _ => false) (fun _ => false) hwb_aff (isAffine_const false) (isAffine_const false) i
  have hrtb_aff : ∀ i : Fin k, IsAffine (fun v => rtbFn v i) := fun i =>
    isAffine_xor (hzb_aff _) (isAffine_xor (hzb_aff _) (hzb_aff _))
  have hb_aff : IsAffine bFn :=
    isAffine_xor (hdf_aff (d - 1)) (isAffine_xor (hrtb_aff ⟨4, by omega⟩) (hrtb_aff ⟨5, by omega⟩))
  have hwFn_aff : ∀ i : Fin k, IsAffine (fun v => wFn v i) := fun i =>
    isAffine_xor (hwb_aff i) (isAffine_and_const_right (mix hk 1 u1 i) hb_aff)
  have hwFn_val : ∀ x : Fin k → Bool,
      wFn (fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)) = R0 hk false x := by
    intro x
    let v : Fin (2 * d) → Bool := fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)
    let bTrue : Bool := R0 hk false x ⟨3, by omega⟩
    let wTarg : Fin k → Bool := add (R0 hk false x) (fun q => bTrue && mix hk 1 u1 q)
    have hwb_mid : ∀ i : Fin k, i.val ≠ 1 → i.val ≠ k - 1 → wbRaw v i = wTarg i := fun i h1 hk1 => by
      dsimp only [wbRaw, wTarg, add]
      rw [hU i]
      by_cases h0 : i.val = 0
      · rw [ite_pos h0, hdf0 x, decide_eq_false (by omega), Bool.and_false, Bool.xor_false]
        exact congrArg (R0 hk false x) (Fin.ext h0.symm)
      · by_cases h2 : i.val = 2
        · rw [ite_neg h0, ite_pos h2, hdf1 x, decide_eq_false (by omega), Bool.and_false, Bool.xor_false]
          exact congrArg (R0 hk false x) (Fin.ext h2.symm)
        · by_cases h3i : i.val = 3
          · rw [ite_neg h0, ite_neg h2, ite_neg (by omega), decide_eq_true (by omega), Bool.and_true]
            have heq : i = ⟨3, by omega⟩ := Fin.ext h3i
            rw [heq]; exact (Bool.xor_self _).symm
          · have h4 : 4 ≤ i.val ∧ i.val ≤ k - 2 := by omega
            rw [ite_neg h0, ite_neg h2, ite_pos h4, decide_eq_true (by omega), Bool.and_true]
            have htel := chainXor_telescope (fun s => dfFn (s + 2) v)
              (fun s => if hs : s + 3 < k then R0 hk false x ⟨s + 3, hs⟩ else false) (i.val - 3)
              (fun s hs => by
                rw [dite_pos (by omega), dite_pos (by omega)]
                have hm := hdf_mid x (s + 2) (by omega) (by omega)
                have he1 : (⟨s + 2 + 1, by omega⟩ : Fin k) = ⟨s + 3, by omega⟩ := Fin.ext rfl
                have he2 : (⟨s + 2 + 2, by omega⟩ : Fin k) = ⟨s + 1 + 3, by omega⟩ := Fin.ext rfl
                rw [he1, he2] at hm; exact hm)
            rw [htel, dite_pos (by omega), dite_pos (by omega)]
            have hi_eq : (⟨i.val - 3 + 3, by omega⟩ : Fin k) = i := Fin.ext (by dsimp only; omega)
            rw [hi_eq]; exact Bool.xor_comm _ _
    have hraw1 : wbRaw v ⟨1, by omega⟩ = false := by
      dsimp only [wbRaw]; rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega)]
    have hrawk : wbRaw v ⟨k - 1, by omega⟩ = false := by
      dsimp only [wbRaw]; rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega)]
    have hwTarg_res : ∀ c, c < 3 → resSum wTarg c = xor (xorFin (rot hk 1 x)) (bTrue && xorFin u1) := fun c hc => by
      dsimp only [wTarg]; unfold add
      have hR0y : R0 hk false x = mix hk 1 (rot hk 1 x) := rfl
      rw [resSum_xor, hR0y, resSum_mix1 hk ⟨r, hr⟩ (by omega) (rot hk 1 x) c hc,
          resSum_and_const, resSum_mix1 hk ⟨r, hr⟩ (by omega) u1 c hc]
    have hres0 : resSum (wbRaw v) 0 = resSum wTarg 0 := by
      unfold resSum; apply xorFin_congr; intro i
      by_cases h1 : i.val = 1
      · rw [h1]; rfl
      · by_cases hk1 : i.val = k - 1
        · have hm : i.val % 3 ≠ 0 := by omega
          rw [decide_eq_false hm, Bool.false_and, Bool.false_and]
        · rw [hwb_mid i h1 hk1]
    have hwb_eq : wbFn v = wTarg := by
      have h1_eq : xor (resSum (wbRaw v) 0) (resSum (wbRaw v) 1) = wTarg ⟨1, by omega⟩ := by
        have hdiff : resSum (fun i => xor (wbRaw v i) (wTarg i)) 1 = wTarg ⟨1, by omega⟩ := by
          unfold resSum; rw [xorFin_single' ⟨1, by omega⟩]
          · dsimp only; rw [hraw1]; simp
          · intro i hi
            have hi1 : i.val ≠ 1 := fun h => hi (Fin.ext h)
            by_cases hik : i.val = k - 1
            · have hm : i.val % 3 ≠ 1 := by omega
              rw [decide_eq_false hm, Bool.false_and]
            · dsimp only; rw [hwb_mid i hi1 hik, Bool.xor_self, Bool.and_false]
        rw [resSum_xor, hwTarg_res 1 (by omega), ← hwTarg_res 0 (by omega), ← hres0, Bool.xor_comm] at hdiff
        exact hdiff
      have hk1_eq : xor (resSum (wbRaw v) 0) (resSum (wbRaw v) 2) = wTarg ⟨k - 1, by omega⟩ := by
        have hdiff : resSum (fun i => xor (wbRaw v i) (wTarg i)) 2 = wTarg ⟨k - 1, by omega⟩ := by
          unfold resSum; rw [xorFin_single' ⟨k - 1, by omega⟩]
          · have hm : (k - 1) % 3 = 2 := by omega
            dsimp only; rw [decide_eq_true hm, Bool.true_and, hrawk, Bool.false_xor]
          · intro i hi
            have hik : i.val ≠ k - 1 := fun h => hi (Fin.ext h)
            by_cases hi1 : i.val = 1
            · rw [hi1]; rfl
            · dsimp only; rw [hwb_mid i hi1 hik, Bool.xor_self, Bool.and_false]
        rw [resSum_xor, hwTarg_res 2 (by omega), ← hwTarg_res 0 (by omega), ← hres0, Bool.xor_comm] at hdiff
        exact hdiff
      funext i; dsimp only [wbFn]
      by_cases h1 : i.val = 1
      · rw [ite_pos h1]; have : i = ⟨1, by omega⟩ := Fin.ext h1; rw [this]; exact h1_eq
      · by_cases hk1 : i.val = k - 1
        · rw [ite_neg h1, ite_pos hk1]; have : i = ⟨k - 1, by omega⟩ := Fin.ext hk1; rw [this]; exact hk1_eq
        · rw [ite_neg h1, ite_neg hk1]; exact hwb_mid i h1 hk1
    have hrtb_eq : rtbFn v = add (R0 hk true x) (fun q => bTrue && rot hk 2 (mix hk 2 u1) q) := by
      dsimp only [rtbFn, zbFn]
      rw [hwb_eq]
      have hwTarg_mix : wTarg = mix hk 1 (add (rot hk 1 x) (fun q => bTrue && u1 q)) := by
        dsimp only [wTarg]; rw [mix_add, mix_scale]; rfl
      rw [hwTarg_mix, zOf_mix1_eq_add_per3 hk (by omega), rot_add, mix_add]
      have hp0 : mix hk 2 (rot hk 2 (per3 (add (rot hk 1 x) (fun q => bTrue && u1 q) ⟨0, hk⟩)
          (add (rot hk 1 x) (fun q => bTrue && u1 q) ⟨1, by omega⟩))) = fun _ => false := by
        rw [mix2_rot2_comm hk (by omega), mix2_per3 hk (by omega) ⟨r, hr⟩]; rfl
      rw [hp0, show ∀ g : Fin k → Bool, add g (fun _ => false) = g from fun g => funext fun q => Bool.xor_false _]
      rw [rot_add, mix_add, rot2_rot1 hk (by omega), rot_scale, mix_scale, mix2_rot2_comm hk (by omega)]
      rfl
    have hb_eq : bFn v = bTrue := by
      dsimp only [bFn]; rw [hdt x, hrtb_eq]; dsimp only [add]
      have hr4 : rot hk 2 (mix hk 2 u1) ⟨4, by omega⟩ = mix hk 2 u1 ⟨2, by omega⟩ := by
        unfold rot; apply congrArg (mix hk 2 u1); apply Fin.ext; dsimp [ix]
        rw [Nat.mod_eq_of_lt (by omega : 2 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)]
      have hr5 : rot hk 2 (mix hk 2 u1) ⟨5, by omega⟩ = mix hk 2 u1 ⟨3, by omega⟩ := by
        unfold rot; apply congrArg (mix hk 2 u1); apply Fin.ext; dsimp [ix]
        rw [Nat.mod_eq_of_lt (by omega : 2 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)]
      rw [hr4, hr5]
      have hv23 := hV.2.2
      revert hv23
      cases R0 hk true x ⟨4, by omega⟩ <;> cases R0 hk true x ⟨5, by omega⟩ <;>
        cases bTrue <;> cases mix hk 2 u1 ⟨2, by omega⟩ <;> cases mix hk 2 u1 ⟨3, by omega⟩ <;> simp
    funext i; dsimp only [wFn]; rw [hwb_eq, hb_eq]; dsimp only [wTarg, add]
    cases R0 hk false x i <;> cases (bTrue && mix hk 1 u1 i) <;> rfl

  suffices hgen : ∀ (wAbs : (Fin (2 * d) → Bool) → Fin k → Bool),
      (∀ i : Fin k, IsAffine (fun v => wAbs v i)) →
      (∀ x : Fin k → Bool, wAbs (fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)) = R0 hk false x) →
      ∀ (width : Nat) (gs : List Gate), Good width gs →
        ∀ (baseW : Fin (2 * d) → Nat) (baseVals : Fin (2 * d) → List Bool → Bool),
        (∀ p, WireSpec width gs (baseW p) (baseVals p)) →
        ∃ (gs' : List Gate) (tapJ : Fin k → Nat),
          Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear + 2 ∧
          (∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width gs' w0 f0) ∧
          (∀ i : Fin k, tapJ i < width + gs'.length) ∧
          ∀ (inp : List Bool) (x : Fin k → Bool),
            inp.length = width →
            (∀ p : Fin (2 * d), baseVals p inp = readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)) →
            ∀ i : Fin k, (Circuit.wires ⟨gs', 0⟩ inp).getD (tapJ i) false = x i by
    exact ⟨pick1, bank1, site1, hbank_card, hgen wFn hwFn_aff hwFn_val⟩
  intro wAbs hwAbs_aff hwAbs_val width gs hgood baseW baseVals hbase
  rcases addAffineFn gs hgood baseW baseVals hbase (fun v => !(wAbs v ⟨2, by omega⟩)) (isAffine_not (hwAbs_aff ⟨2, by omega⟩)) with
    ⟨gs1, wn2, hg1, hc1, hp1, hwn2⟩
  rcases addAffineFn gs1 hg1 baseW baseVals (fun p => hp1 _ _ (hbase p)) (fun v => wAbs v ⟨3, by omega⟩) (hwAbs_aff ⟨3, by omega⟩) with
    ⟨gs2, ww3, hg2, hc2, hp2, hww3⟩
  rcases addAnd gs2 hg2 (hp2 _ _ hwn2) hww3 with ⟨gs3, wp1, hg3, hc3, hp3, hwp1⟩
  have hbase3 : ∀ p, WireSpec width gs3 (baseW p) (baseVals p) := fun p => hp3 _ _ (hp2 _ _ (hp1 _ _ (hbase p)))
  rcases addAffineFn gs3 hg3 baseW baseVals hbase3 (fun v => !(wAbs v ⟨3, by omega⟩)) (isAffine_not (hwAbs_aff ⟨3, by omega⟩)) with
    ⟨gs4, wn3, hg4, hc4, hp4, hwn3⟩
  rcases addAffineFn gs4 hg4 baseW baseVals (fun p => hp4 _ _ (hbase3 p)) (fun v => wAbs v ⟨4, by omega⟩) (hwAbs_aff ⟨4, by omega⟩) with
    ⟨gs5, ww4, hg5, hc5, hp5, hww4⟩
  rcases addAnd gs5 hg5 (hp5 _ _ hwn3) hww4 with ⟨gs6, wp2, hg6, hc6, hp6, hwp2⟩
  have hp_all : ∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width gs6 w0 f0 :=
    fun w0 f0 h0 => hp6 _ _ (hp5 _ _ (hp4 _ _ (hp3 _ _ (hp2 _ _ (hp1 _ _ h0)))))
  let extW : Fin (2 * d + 2) → Nat := fun q =>
    if hq : q.val < 2 * d then baseW ⟨q.val, hq⟩
    else if q.val = 2 * d then wp1 else wp2
  let extVals : Fin (2 * d + 2) → List Bool → Bool := fun q inp =>
    if hq : q.val < 2 * d then baseVals ⟨q.val, hq⟩ inp
    else if q.val = 2 * d then !(wAbs (fun p => baseVals p inp) ⟨2, by omega⟩) && wAbs (fun p => baseVals p inp) ⟨3, by omega⟩
    else !(wAbs (fun p => baseVals p inp) ⟨3, by omega⟩) && wAbs (fun p => baseVals p inp) ⟨4, by omega⟩
  have hext : ∀ q : Fin (2 * d + 2), WireSpec width gs6 (extW q) (extVals q) := fun q => by
    dsimp only [extW, extVals]
    by_cases hq : q.val < 2 * d
    · simp only [dite_pos hq]; exact hp_all _ _ (hbase ⟨q.val, hq⟩)
    · by_cases hqp : q.val = 2 * d
      · simp only [dite_neg hq, ite_pos hqp]; exact hp6 _ _ (hp5 _ _ (hp4 _ _ hwp1))
      · simp only [dite_neg hq, ite_neg hqp]; exact hwp2
  let vOf : (Fin (2 * d + 2) → Bool) → Fin (2 * d) → Bool := fun ve p => ve ⟨p.val, by omega⟩
  let wExt : (Fin (2 * d + 2) → Bool) → Fin k → Bool := fun ve => wAbs (vOf ve)
  let y2Ext : (Fin (2 * d + 2) → Bool) → Bool := fun ve =>
    xor (ve ⟨2, by omega⟩) (xor (wExt ve ⟨1, by omega⟩) (ve ⟨2 * d, by omega⟩))
  let y3Ext : (Fin (2 * d + 2) → Bool) → Bool := fun ve =>
    xor (ve ⟨4, by omega⟩) (xor (wExt ve ⟨2, by omega⟩) (ve ⟨2 * d + 1, by omega⟩))
  let y1Ext : (Fin (2 * d + 2) → Bool) → Bool := fun ve =>
    xor (wExt ve ⟨2, by omega⟩) (xor (y2Ext ve) (y3Ext ve))
  let y0Ext : (Fin (2 * d + 2) → Bool) → Bool := fun ve =>
    xor (wExt ve ⟨1, by omega⟩) (xor (y1Ext ve) (y2Ext ve))
  let recExt : Fin k → (Fin (2 * d + 2) → Bool) → Bool := fun i ve =>
    zOf hk (wExt ve) (y0Ext ve) (y1Ext ve) (ix hk (i.val + 1))
  have hwExt_aff : ∀ i : Fin k, IsAffine (fun ve => wExt ve i) := fun i =>
    isAffine_comp (f := fun v => wAbs v i) (g := vOf) (hwAbs_aff i) (fun p => isAffine_coord ⟨p.val, by omega⟩)
  have hy2_aff : IsAffine y2Ext := isAffine_xor (isAffine_coord _) (isAffine_xor (hwExt_aff ⟨1, by omega⟩) (isAffine_coord _))
  have hy3_aff : IsAffine y3Ext := isAffine_xor (isAffine_coord _) (isAffine_xor (hwExt_aff ⟨2, by omega⟩) (isAffine_coord _))
  have hy1_aff : IsAffine y1Ext := isAffine_xor (hwExt_aff ⟨2, by omega⟩) (isAffine_xor hy2_aff hy3_aff)
  have hy0_aff : IsAffine y0Ext := isAffine_xor (hwExt_aff ⟨1, by omega⟩) (isAffine_xor hy1_aff hy2_aff)
  have hrec_aff : ∀ i : Fin k, IsAffine (recExt i) := fun i =>
    isAffine_zOf hk wExt y0Ext y1Ext hwExt_aff hy0_aff hy1_aff (ix hk (i.val + 1))
  rcases addAffineVec gs6 hg6 extW extVals hext recExt hrec_aff with ⟨gs7, tapJ, hg7, hc7, hp7, htapJ⟩
  refine ⟨gs7, tapJ, hg7, by rw [hc7, hc6, hc5, hc4, hc3, hc2, hc1],
    fun w0 f0 h0 => hp7 _ _ (hp_all _ _ h0), fun i => (htapJ i).1, fun inp x hlen hbase_eq i => ?_⟩
  rw [(htapJ i).2 inp hlen]
  let v : Fin (2 * d) → Bool := fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)
  let ve : Fin (2 * d + 2) → Bool := fun q => extVals q inp
  have hv_eq : vOf ve = v := by funext p; unfold vOf ve extVals; dsimp only; rw [dite_pos p.isLt, hbase_eq p]
  have hw_eq : wExt ve = R0 hk false x := by unfold wExt; rw [hv_eq]; exact hwAbs_val x
  have hve2 : ve ⟨2, by omega⟩ = readBit hk false u0 x ⟨1, by omega⟩ := by
    have := congrFun hv_eq ⟨2, by omega⟩
    dsimp only [vOf, v, bank1, pick1, names2, site1, sitePair] at this
    rw [decide_eq_false (by omega), ite_pos (show 2 % 2 = 0 by omega), ite_pos rfl,
        ite_neg (show 2 / 2 ≠ 0 by omega), ite_pos (show 2 / 2 = 1 by omega)] at this
    exact this
  have hve4 : ve ⟨4, by omega⟩ = readBit hk false u0 x ⟨2, by omega⟩ := by
    have := congrFun hv_eq ⟨4, by omega⟩
    dsimp only [vOf, v, bank1, pick1, names2, site1, sitePair] at this
    rw [decide_eq_false (by omega), ite_pos (show 4 % 2 = 0 by omega), ite_pos rfl,
        ite_neg (show 4 / 2 ≠ 0 by omega), ite_neg (show 4 / 2 ≠ 1 by omega), dite_pos (by omega)] at this
    exact this
  have hvp1 : ve ⟨2 * d, by omega⟩ = (!(R0 hk false x ⟨2, by omega⟩) && R0 hk false x ⟨3, by omega⟩) := by
    unfold ve extVals; dsimp only; rw [dite_neg (by omega), ite_pos rfl]
    have hb_eq : (fun p => baseVals p inp) = v := funext hbase_eq
    rw [hb_eq, hwAbs_val x]
  have hvp2 : ve ⟨2 * d + 1, by omega⟩ = (!(R0 hk false x ⟨3, by omega⟩) && R0 hk false x ⟨4, by omega⟩) := by
    unfold ve extVals; dsimp only; rw [dite_neg (by omega), ite_neg (by omega)]
    have hb_eq : (fun p => baseVals p inp) = v := funext hbase_eq
    rw [hb_eq, hwAbs_val x]
  let y := rot hk 1 x
  have hrot_x : ∀ q : Fin k, y (ix hk (q.val + 1)) = x q := fun q => by
    unfold y rot; exact congrArg x (Fin.ext (by
      dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_add_eq q.isLt (by omega)]
      split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega))
  have hrb0 : ∀ s : Fin k, readBit hk false u0 x s =
      xor (x s) (xor (R0 hk false x s) (!(R0 hk false x (ix hk (s.val + 1))) && R0 hk false x (ix hk (s.val + 2)))) := by
    intro s; unfold readBit R0; simp only [Bool.false_eq_true, ite_false]
    have ha0 : add u0 (rot hk 1 x) = rot hk 1 x := by funext q; exact Bool.false_xor _
    have hr0 : rot hk 0 x s = x s := by
      unfold rot; exact congrArg x (Fin.ext (by dsimp [ix]; rw [Nat.add_mod_right, Nat.mod_eq_of_lt s.isLt]))
    rw [ha0, hr0]
  have hy2_eq : y2Ext ve = y ⟨2, by omega⟩ := by
    unfold y2Ext; rw [hve2, hw_eq, hvp1, hrb0 ⟨1, by omega⟩]
    have h2 : ix hk (1 + 1) = ⟨2, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have h3 : ix hk (1 + 2) = ⟨3, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have hx1 : x ⟨1, by omega⟩ = y ⟨2, by omega⟩ := by rw [← hrot_x ⟨1, by omega⟩, h2]
    rw [h2, h3, hx1]
    cases y ⟨2, by omega⟩ <;> cases R0 hk false x ⟨1, by omega⟩ <;>
      cases (!(R0 hk false x ⟨2, by omega⟩) && R0 hk false x ⟨3, by omega⟩) <;> rfl
  have hy3_eq : y3Ext ve = y ⟨3, by omega⟩ := by
    unfold y3Ext; rw [hve4, hw_eq, hvp2, hrb0 ⟨2, by omega⟩]
    have h3 : ix hk (2 + 1) = ⟨3, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have h4 : ix hk (2 + 2) = ⟨4, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have hx2 : x ⟨2, by omega⟩ = y ⟨3, by omega⟩ := by rw [← hrot_x ⟨2, by omega⟩, h3]
    rw [h3, h4, hx2]
    cases y ⟨3, by omega⟩ <;> cases R0 hk false x ⟨2, by omega⟩ <;>
      cases (!(R0 hk false x ⟨3, by omega⟩) && R0 hk false x ⟨4, by omega⟩) <;> rfl
  have hw1 : R0 hk false x ⟨1, by omega⟩ = xor (y ⟨0, hk⟩) (xor (y ⟨1, by omega⟩) (y ⟨2, by omega⟩)) := by
    unfold R0 mix; simp only [Bool.false_eq_true, ite_false]
    have hm : ix hk (1 + k - 1 % k) = ⟨0, hk⟩ := Fin.ext (by
      dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k), show 1 + k - 1 = k by omega, Nat.mod_self])
    have hp : ix hk (1 + 1) = ⟨2, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [hm, hp]
  have hw2 : R0 hk false x ⟨2, by omega⟩ = xor (y ⟨1, by omega⟩) (xor (y ⟨2, by omega⟩) (y ⟨3, by omega⟩)) := by
    unfold R0 mix; simp only [Bool.false_eq_true, ite_false]
    have hm : ix hk (2 + k - 1 % k) = ⟨1, by omega⟩ := Fin.ext (by
      dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)])
    have hp : ix hk (2 + 1) = ⟨3, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [hm, hp]
  have hy1_eq : y1Ext ve = y ⟨1, by omega⟩ := by
    unfold y1Ext; rw [hw_eq, hy2_eq, hy3_eq, hw2]
    cases y ⟨1, by omega⟩ <;> cases y ⟨2, by omega⟩ <;> cases y ⟨3, by omega⟩ <;> rfl
  have hy0_eq : y0Ext ve = y ⟨0, hk⟩ := by
    unfold y0Ext; rw [hw_eq, hy1_eq, hy2_eq, hw1]
    cases y ⟨0, hk⟩ <;> cases y ⟨1, by omega⟩ <;> cases y ⟨2, by omega⟩ <;> rfl
  change recExt i ve = x i
  unfold recExt
  rw [hw_eq, hy0_eq, hy1_eq]
  have hR0y : R0 hk false x = mix hk 1 y := rfl
  rw [hR0y, zOf_eq_of_mix1 hk (by omega) y (ix hk (i.val + 1)), hrot_x i]

lemma single_key_spec_h2_ndiv {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (h3 : ¬(3 ∣ k)) :
    let names2 : Fin 2 → Fin k → Bool := fun r => if r.val = 0 then (fun _ => false) else u1_h2 hk
    ∃ (pick1 : Fin (2 * k) → Fin 2) (bank1 : Fin (2 * k) → Bool) (site1 : Fin (2 * k) → Fin k),
      (Finset.univ.filter (fun p : Fin (2 * k) => bank1 p = true)).card = 2 ∧
      ∀ (width : Nat) (gs : List Gate), Good width gs →
        ∀ (baseW : Fin (2 * k) → Nat) (baseVals : Fin (2 * k) → List Bool → Bool),
        (∀ p, WireSpec width gs (baseW p) (baseVals p)) →
        ∃ (gs' : List Gate) (tapJ : Fin k → Nat),
          Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
          (∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width gs' w0 f0) ∧
          (∀ i : Fin k, tapJ i < width + gs'.length) ∧
          ∀ (inp : List Bool) (x : Fin k → Bool),
            inp.length = width →
            (∀ p : Fin (2 * k), baseVals p inp = readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)) →
            ∀ i : Fin k, (Circuit.wires ⟨gs', 0⟩ inp).getD (tapJ i) false = x i := by
  intro names2
  let u0 : Fin k → Bool := fun _ => false
  let u1 : Fin k → Bool := u1_h2 hk
  let pick1 : Fin (2 * k) → Fin 2 := fun l => if l.val % 2 = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩
  let bank1 : Fin (2 * k) → Bool := fun l => decide (2 * (k - 1) ≤ l.val)
  let sitePair : Nat → Fin k := fun t =>
    if t = 0 then ⟨k - 1, by omega⟩
    else if h : t < k - 1 then ⟨t - 1, by omega⟩
    else ⟨2, by omega⟩
  let site1 : Fin (2 * k) → Fin k := fun l => sitePair (l.val / 2)
  have hbank_card : (Finset.univ.filter (fun p : Fin (2 * k) => bank1 p = true)).card = 2 := by
    have heq : Finset.univ.filter (fun p : Fin (2 * k) => bank1 p = true) =
        {⟨2 * (k - 1), by omega⟩, ⟨2 * (k - 1) + 1, by omega⟩} := by
      ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, bank1, decide_eq_true_eq,
        Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [heq, Finset.card_pair]
    intro h; have := congrArg Fin.val h; dsimp only at this; omega
  let dfFn : Nat → (Fin (2 * k) → Bool) → Bool := fun t v =>
    if ht : t < k then
      xor (xor (v ⟨2 * t, by omega⟩) (v ⟨2 * t + 1, by omega⟩))
          (readBit hk (decide (t = k - 1)) u1 u0 (sitePair t))
    else false
  have hdf_aff : ∀ t : Nat, IsAffine (dfFn t) := fun t => by
    dsimp only [dfFn]
    by_cases ht : t < k
    · simp only [dite_pos ht]
      exact isAffine_xor (isAffine_xor (isAffine_coord _) (isAffine_coord _)) (isAffine_const _)
    · simp only [dite_neg ht]; exact isAffine_const false
  have hU : ∀ q : Fin k, mix hk 1 u1 q = decide (q.val ≠ 0) := fun q => mix1_u1_h2_ndiv hk hk7 h3 q
  have hV := mix2_u1_h2_ndiv hk hk7 h3
  have hdf0 : ∀ x : Fin k → Bool,
      dfFn 0 (fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)) = R0 hk false x ⟨0, hk⟩ := fun x => by
    dsimp only [dfFn]; rw [dite_pos (by omega)]
    have h := h2_pair_df hk hk sitePair x 0 (by omega)
    have hcol : decide (0 = k - 1) = false := decide_eq_false (by omega)
    have hsp : sitePair 0 = ⟨k - 1, by omega⟩ := by dsimp only [sitePair]; rw [ite_pos rfl]
    refine Eq.trans h ?_
    rw [hcol, hsp]; simp only [Bool.false_eq_true, ite_false]
    rw [show u1_h2 hk = u1 from rfl, hU, hU]
    have h1 : ix hk (k - 1 + 1) = ⟨0, hk⟩ := Fin.ext (by dsimp [ix]; rw [show k - 1 + 1 = k by omega, Nat.mod_self])
    have h2 : ix hk (k - 1 + 2) = ⟨1, by omega⟩ := Fin.ext (by
      dsimp [ix]; rw [show k - 1 + 2 = 1 + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)])
    rw [h1, h2, decide_eq_false (by omega : ¬(0 ≠ 0)), decide_eq_true (by omega : 1 ≠ 0)]
    simp
  have hdf_mid : ∀ (x : Fin k → Bool) (t : Nat) (ht1 : 1 ≤ t) (htd : t < k - 1),
      dfFn t (fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)) =
      xor (R0 hk false x ⟨t, by omega⟩) (R0 hk false x ⟨t + 1, by omega⟩) := fun x t ht1 htd => by
    dsimp only [dfFn]; rw [dite_pos (by omega)]
    have h := h2_pair_df hk hk sitePair x t (by omega)
    have hcol : decide (t = k - 1) = false := decide_eq_false (by omega)
    have hsp : sitePair t = ⟨t - 1, by omega⟩ := by
      dsimp only [sitePair]; rw [ite_neg (by omega), dite_pos htd]
    refine Eq.trans h ?_
    rw [hcol, hsp]; simp only [Bool.false_eq_true, ite_false]
    rw [show u1_h2 hk = u1 from rfl, hU, hU]
    have h1 : ix hk (t - 1 + 1) = ⟨t, by omega⟩ := Fin.ext (by dsimp [ix]; rw [show t - 1 + 1 = t by omega, Nat.mod_eq_of_lt (by omega)])
    have h2 : ix hk (t - 1 + 2) = ⟨t + 1, by omega⟩ := Fin.ext (by dsimp [ix]; rw [show t - 1 + 2 = t + 1 by omega, Nat.mod_eq_of_lt (by omega)])
    rw [h1, h2, decide_eq_true (by omega : t ≠ 0), decide_eq_true (by omega : t + 1 ≠ 0)]
    simp [Bool.xor_comm]
  have hdt : ∀ x : Fin k → Bool,
      dfFn (k - 1) (fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)) =
      xor (R0 hk true x ⟨3, by omega⟩) (R0 hk true x ⟨4, by omega⟩) := fun x => by
    dsimp only [dfFn]; rw [dite_pos (by omega)]
    have h := h2_pair_df hk hk sitePair x (k - 1) (by omega)
    have hcol : decide (k - 1 = k - 1) = true := decide_eq_true rfl
    have hsp : sitePair (k - 1) = ⟨2, by omega⟩ := by
      dsimp only [sitePair]; rw [ite_neg (by omega), dite_neg (by omega)]
    rw [hcol, hsp] at h ⊢; simp only [ite_true] at h
    have h1 : ix hk (2 + 1) = ⟨3, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have h2 : ix hk (2 + 2) = ⟨4, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [h1, h2, hV.1, hV.2.1, Bool.true_and, Bool.true_and] at h
    rw [h]; exact Bool.xor_comm _ _
  let wbFn : (Fin (2 * k) → Bool) → Fin k → Bool := fun v i =>
    if i.val = 0 then dfFn 0 v
    else if i.val = 1 then false
    else chainXor (fun s => dfFn (s + 1) v) (i.val - 1)
  let ybFn : (Fin (2 * k) → Bool) → Fin k → Bool := fun v => invMix1 hk (by omega) (wbFn v)
  let rtbFn : (Fin (2 * k) → Bool) → Fin k → Bool := fun v => mix hk 2 (rot hk 2 (ybFn v))
  let bFn : (Fin (2 * k) → Bool) → Bool := fun v =>
    xor (dfFn (k - 1) v) (xor (rtbFn v ⟨3, by omega⟩) (rtbFn v ⟨4, by omega⟩))
  let yFn : (Fin (2 * k) → Bool) → Fin k → Bool := fun v i => xor (ybFn v i) (bFn v && u1 i)
  let recFn : Fin k → (Fin (2 * k) → Bool) → Bool := fun i v => yFn v (ix hk (i.val + 1))
  have hwb_aff : ∀ i : Fin k, IsAffine (fun v => wbFn v i) := fun i => by
    dsimp only [wbFn]
    by_cases h0 : i.val = 0
    · simp only [ite_pos h0]; exact hdf_aff 0
    · by_cases h1 : i.val = 1
      · simp only [ite_neg h0, ite_pos h1]; exact isAffine_const false
      · simp only [ite_neg h0, ite_neg h1]
        exact isAffine_chainXor (fun s v => dfFn (s + 1) v) (fun s => hdf_aff (s + 1)) (i.val - 1)
  have hyb_aff : ∀ i : Fin k, IsAffine (fun v => ybFn v i) := fun i =>
    isAffine_invMix1 hk (by omega) wbFn hwb_aff i
  have hrtb_aff : ∀ i : Fin k, IsAffine (fun v => rtbFn v i) := fun i =>
    isAffine_xor (hyb_aff _) (isAffine_xor (hyb_aff _) (hyb_aff _))
  have hb_aff : IsAffine bFn :=
    isAffine_xor (hdf_aff (k - 1)) (isAffine_xor (hrtb_aff ⟨3, by omega⟩) (hrtb_aff ⟨4, by omega⟩))
  have hy_aff : ∀ i : Fin k, IsAffine (fun v => yFn v i) := fun i =>
    isAffine_xor (hyb_aff i) (isAffine_and_const_right (u1 i) hb_aff)
  have hrec_aff : ∀ i : Fin k, IsAffine (recFn i) := fun i => hy_aff (ix hk (i.val + 1))
  have hrec_val : ∀ (x : Fin k → Bool) (i : Fin k),
      recFn i (fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)) = x i := by
    intro x i
    let v : Fin (2 * k) → Bool := fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)
    let bTrue : Bool := R0 hk false x ⟨1, by omega⟩
    have hwb_eq : wbFn v = add (R0 hk false x) (fun q => bTrue && mix hk 1 u1 q) := by
      funext q; dsimp only [wbFn, add]; rw [hU q]
      by_cases h0 : q.val = 0
      · rw [ite_pos h0, hdf0 x, decide_eq_false (by omega), Bool.and_false, Bool.xor_false]
        exact congrArg (R0 hk false x) (Fin.ext h0.symm)
      · rw [decide_eq_true h0, Bool.and_true]
        by_cases h1 : q.val = 1
        · rw [ite_neg h0, ite_pos h1]
          have : q = ⟨1, by omega⟩ := Fin.ext h1; rw [this]; exact (Bool.xor_self _).symm
        · rw [ite_neg h0, ite_neg h1]
          have htel := chainXor_telescope (fun s => dfFn (s + 1) v)
            (fun s => if hs : s + 1 < k then R0 hk false x ⟨s + 1, hs⟩ else false) (q.val - 1)
            (fun s hs => by
              rw [dite_pos (by omega), dite_pos (by omega)]
              exact hdf_mid x (s + 1) (by omega) (by omega))
          rw [htel, dite_pos (by omega), dite_pos (by omega)]
          have hq_eq : (⟨q.val - 1 + 1, by omega⟩ : Fin k) = q := Fin.ext (by dsimp only; omega)
          rw [hq_eq]; exact Bool.xor_comm _ _
    have hyb_eq : ybFn v = add (rot hk 1 x) (fun q => bTrue && u1 q) := by
      dsimp only [ybFn]; rw [hwb_eq]
      have hmix : add (R0 hk false x) (fun q => bTrue && mix hk 1 u1 q) =
          mix hk 1 (add (rot hk 1 x) (fun q => bTrue && u1 q)) := by
        rw [mix_add, mix_scale]; rfl
      rw [hmix, invMix1_mix1 hk (by omega) h3]
    have hrtb_eq : rtbFn v = add (R0 hk true x) (fun q => bTrue && rot hk 2 (mix hk 2 u1) q) := by
      dsimp only [rtbFn]; rw [hyb_eq, rot_add, mix_add, rot2_rot1 hk (by omega),
        rot_scale, mix_scale, mix2_rot2_comm hk (by omega)]
      rfl
    have hb_val : bFn v = bTrue := by
      dsimp only [bFn]; rw [hdt x, hrtb_eq]; dsimp only [add]
      have hr3 : rot hk 2 (mix hk 2 u1) ⟨3, by omega⟩ = mix hk 2 u1 ⟨1, by omega⟩ := by
        unfold rot; apply congrArg (mix hk 2 u1); apply Fin.ext; dsimp [ix]
        rw [Nat.mod_eq_of_lt (by omega : 2 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)]
      have hr4 : rot hk 2 (mix hk 2 u1) ⟨4, by omega⟩ = mix hk 2 u1 ⟨2, by omega⟩ := by
        unfold rot; apply congrArg (mix hk 2 u1); apply Fin.ext; dsimp [ix]
        rw [Nat.mod_eq_of_lt (by omega : 2 < k), mod_sub_eq (by omega) (by omega), ite_pos (by omega)]
      rw [hr3, hr4]
      have hv12 := hV.2.2
      revert hv12
      cases R0 hk true x ⟨3, by omega⟩ <;> cases R0 hk true x ⟨4, by omega⟩ <;>
        cases bTrue <;> cases mix hk 2 u1 ⟨1, by omega⟩ <;> cases mix hk 2 u1 ⟨2, by omega⟩ <;> simp
    have hy_val : yFn v = rot hk 1 x := by
      funext q; dsimp only [yFn]; rw [hyb_eq, hb_val]; dsimp only [add]
      cases rot hk 1 x q <;> cases (bTrue && u1 q) <;> rfl
    dsimp only [recFn]; rw [hy_val]; unfold rot; exact congrArg x (Fin.ext (by
      dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega : 1 < k), mod_add_eq i.isLt (by omega)]
      split_ifs <;> rw [mod_sub_eq (by omega) (by omega)] <;> split_ifs <;> omega))
  refine ⟨pick1, bank1, site1, hbank_card, fun width gs hgood baseW baseVals hbase => ?_⟩
  rcases addAffineVec gs hgood baseW baseVals hbase recFn hrec_aff with ⟨gs1, tapJ, hg1, hc1, hp1, htapJ⟩
  refine ⟨gs1, tapJ, hg1, hc1, hp1, fun i => (htapJ i).1, fun inp x hlen hbase_eq i => ?_⟩
  rw [(htapJ i).2 inp hlen]
  have hb_eq_v : (fun p => baseVals p inp) = fun p => readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p) := funext hbase_eq
  dsimp only
  rw [hb_eq_v]; exact hrec_val x i

lemma single_key_spec_h2 {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) :
    let e := if 3 ∣ k then 2 else 0
    let d := k - e
    let names2 : Fin 2 → Fin k → Bool := fun r => if r.val = 0 then (fun _ => false) else u1_h2 hk
    ∃ (pick1 : Fin (2 * d) → Fin 2) (bank1 : Fin (2 * d) → Bool) (site1 : Fin (2 * d) → Fin k),
      (Finset.univ.filter (fun p : Fin (2 * d) => bank1 p = true)).card = 2 ∧
      ∀ (width : Nat) (gs : List Gate), Good width gs →
        ∀ (baseW : Fin (2 * d) → Nat) (baseVals : Fin (2 * d) → List Bool → Bool),
        (∀ p, WireSpec width gs (baseW p) (baseVals p)) →
        ∃ (gs' : List Gate) (tapJ : Fin k → Nat),
          Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear + e ∧
          (∀ w0 f0, WireSpec width gs w0 f0 → WireSpec width gs' w0 f0) ∧
          (∀ i : Fin k, tapJ i < width + gs'.length) ∧
          ∀ (inp : List Bool) (x : Fin k → Bool),
            inp.length = width →
            (∀ p : Fin (2 * d), baseVals p inp = readBit hk (bank1 p) (names2 (pick1 p)) x (site1 p)) →
            ∀ i : Fin k, (Circuit.wires ⟨gs', 0⟩ inp).getD (tapJ i) false = x i := by
  intro e d names2
  by_cases h3 : 3 ∣ k
  · have he : e = 2 := by dsimp only [e]; rw [ite_pos h3]
    have hd : d = k - 2 := by dsimp only [d]; rw [he]
    rw [he, hd]; exact single_key_spec_h2_div hk hk7 h3
  · have he : e = 0 := by dsimp only [e]; rw [ite_neg h3]
    have hd : d = k := by dsimp only [d]; rw [he]; omega
    rw [he, hd]; simpa only [Nat.add_zero] using single_key_spec_h2_ndiv hk hk7 h3

theorem upper_bound_45025 {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (n h q c : Nat)
    (hcond : let e := if 3 ∣ k then 2 else 0
             let d := k - e
             n = 0 ∨ (h = 2 ∧ 2 * n * d ≤ q ∧ 2 * n ≤ c) ∨ (3 ≤ h ∧ n * (d + (d + 1) / 2) ≤ q)) :
    let e := if 3 ∣ k then 2 else 0
    ∃ (a : Nat) (names : Fin h → Fin k → Bool) (pick : Fin a → Fin h)
      (bank : Fin a → Bool) (key : Fin a → Fin n) (site : Fin a → Fin k)
      (C : Circuit) (tap : Fin n → Fin k → Nat),
      a ≤ q ∧ (Finset.univ.filter (fun j : Fin a => bank j = true)).card ≤ c ∧
      valid a C ∧ C.gates.countP nonlinear ≤ n * e ∧
      (∀ j i, tap j i < a + C.gates.length) ∧
      ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
        (C.wires (List.ofFn (fun l : Fin a => readBit hk (bank l) (names (pick l)) (x (key l)) (site l)))).getD (tap j i) false = x j i := by
  intro e
  dsimp only at hcond
  let d := k - e
  rcases hcond with hn0 | ⟨hh2, hq2, hc2⟩ | ⟨hh3, hq3⟩
  · subst hn0
    exact ⟨0, fun _ _ => false, fun l => l.elim0, fun l => l.elim0, fun l => l.elim0, fun l => l.elim0,
      ⟨[], 0⟩, fun j => j.elim0, Nat.zero_le q, by simp, good_nil 0, by simp, fun j => j.elim0, fun _ j => j.elim0⟩
  ·
    subst hh2
    let names2 : Fin 2 → Fin k → Bool := fun r => if r.val = 0 then (fun _ => false) else u1_h2 hk
    rcases single_key_spec_h2 hk hk7 with ⟨pick1, bank1, site1, hbank1_card, hspec⟩
    let blk := 2 * d
    have hblk_pos : 0 < blk := by dsimp only [blk, d, e]; by_cases h3 : 3 ∣ k <;> [rcases h3 with ⟨r, hr⟩; skip] <;> split_ifs <;> omega
    let a := n * blk
    have ha_le_q : a ≤ q := by
      dsimp only [a, blk]; rw [show n * (2 * d) = 2 * n * d by ring]; exact hq2
    let key : Fin a → Fin n := fun l => ⟨l.val / blk, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact l.isLt)⟩
    let idx : Fin a → Fin blk := fun l => ⟨l.val % blk, Nat.mod_lt _ hblk_pos⟩
    let pick : Fin a → Fin 2 := fun l => pick1 (idx l)
    let bank : Fin a → Bool := fun l => bank1 (idx l)
    let site : Fin a → Fin k := fun l => site1 (idx l)
    have hbank_le_c : (Finset.univ.filter (fun l : Fin a => bank l = true)).card ≤ c := by
      have hfib : (Finset.univ.filter (fun l : Fin a => bank l = true)).card =
          ∑ j : Fin n, (Finset.univ.filter (fun l : Fin a => bank l = true ∧ key l = j)).card := by
        have hp := Finset.card_eq_sum_card_fiberwise
          (s := Finset.univ.filter (fun l : Fin a => bank l = true))
          (f := key) (t := (Finset.univ : Finset (Fin n))) (fun _ _ => Finset.mem_univ _)
        rw [hp]; apply Finset.sum_congr rfl; intro j _
        congr 1; ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hper : ∀ j : Fin n, (Finset.univ.filter (fun l : Fin a => bank l = true ∧ key l = j)).card = 2 := fun j => by
        rw [← hbank1_card]
        refine Finset.card_bij (fun l _ => idx l)
          (fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2.1⟩)
          (fun l1 hl1 l2 hl2 heq => Fin.ext (by
            have hk1 : l1.val / blk = j.val := congrArg Fin.val (Finset.mem_filter.mp hl1).2.2
            have hk2 : l2.val / blk = j.val := congrArg Fin.val (Finset.mem_filter.mp hl2).2.2
            have hm : l1.val % blk = l2.val % blk := congrArg Fin.val heq
            have d1 := Nat.div_add_mod l1.val blk
            have d2 := Nat.div_add_mod l2.val blk
            rw [hk1] at d1; rw [hk2] at d2; omega))
          (fun p hp => by
            have hlt : j.val * blk + p.val < a := by
              dsimp only [a]
              have hj1 : j.val + 1 ≤ n := j.isLt
              calc j.val * blk + p.val < j.val * blk + blk := Nat.add_lt_add_left p.isLt _
                _ = (j.val + 1) * blk := by ring
                _ ≤ n * blk := Nat.mul_le_mul_right blk hj1
            refine ⟨⟨j.val * blk + p.val, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
            · dsimp only [bank, idx]
              have hmod : (j.val * blk + p.val) % blk = p.val := by
                rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]
              have heq : (⟨(j.val * blk + p.val) % blk, Nat.mod_lt _ hblk_pos⟩ : Fin blk) = p := Fin.ext hmod
              rw [heq]; exact (Finset.mem_filter.mp hp).2
            · apply Fin.ext; dsimp only [key]
              rw [Nat.mul_comm, Nat.mul_add_div hblk_pos, Nat.div_eq_of_lt p.isLt, Nat.add_zero]
            · apply Fin.ext; dsimp only [idx]
              rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt])
      rw [hfib]
      calc ∑ j : Fin n, (Finset.univ.filter (fun l : Fin a => bank l = true ∧ key l = j)).card
          = ∑ _j : Fin n, 2 := Finset.sum_congr rfl (fun j _ => hper j)
        _ = 2 * n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
        _ ≤ c := hc2
    have hbuild : ∀ (m : Nat) (hm : m ≤ n),
        ∃ (gs : List Gate) (taps : Fin m → Fin k → Nat),
          Good a gs ∧ gs.countP nonlinear = m * e ∧
          (∀ j i, taps j i < a + gs.length) ∧
          ∀ (x : Fin n → Fin k → Bool) (j : Fin m) (i : Fin k),
            (Circuit.wires ⟨gs, 0⟩ (List.ofFn (fun l : Fin a => readBit hk (bank l) (names2 (pick l)) (x (key l)) (site l)))).getD (taps j i) false =
            x ⟨j.val, Nat.lt_of_lt_of_le j.isLt hm⟩ i := by
      intro m hm
      induction m with
      | zero => exact ⟨[], fun j => j.elim0, good_nil a, by simp, fun j => j.elim0, fun _ j => j.elim0⟩
      | succ m ih =>
        rcases ih (by omega) with ⟨gs1, taps1, hg1, hc1, ht1, hcomp1⟩
        let jCur : Fin n := ⟨m, hm⟩
        let baseW : Fin blk → Nat := fun p => m * blk + p.val
        let baseVals : Fin blk → List Bool → Bool := fun p inp => inp.getD (baseW p) false
        have hbase_lt : ∀ p : Fin blk, baseW p < a := fun p => by
          dsimp only [baseW, a]
          calc m * blk + p.val < m * blk + blk := Nat.add_lt_add_left p.isLt _
            _ = (m + 1) * blk := by ring
            _ ≤ n * blk := Nat.mul_le_mul_right blk hm
        have hbase : ∀ p : Fin blk, WireSpec a gs1 (baseW p) (baseVals p) := fun p =>
          wireSpec_input_good gs1 hg1 (hbase_lt p)
        rcases hspec a gs1 hg1 baseW baseVals hbase with ⟨gs2, tapM, hg2, hc2, hp2, htapM_lt, htapM_val⟩
        let taps2 : Fin (m + 1) → Fin k → Nat := fun j i =>
          if hj : j.val < m then taps1 ⟨j.val, hj⟩ i else tapM i
        refine ⟨gs2, taps2, hg2, by rw [hc2, hc1]; ring, fun j i => ?_, fun x j i => ?_⟩
        · dsimp only [taps2]; by_cases hj : j.val < m
          · rw [dite_pos hj]
            have hws : WireSpec a gs1 (taps1 ⟨j.val, hj⟩ i) (fun inp => (Circuit.wires ⟨gs1, 0⟩ inp).getD (taps1 ⟨j.val, hj⟩ i) false) :=
              ⟨ht1 ⟨j.val, hj⟩ i, fun _ _ => rfl⟩
            exact (hp2 _ _ hws).1
          · rw [dite_neg hj]; exact htapM_lt i
        · dsimp only [taps2]; by_cases hj : j.val < m
          · rw [dite_pos hj]
            have hws : WireSpec a gs1 (taps1 ⟨j.val, hj⟩ i) (fun inp => (Circuit.wires ⟨gs1, 0⟩ inp).getD (taps1 ⟨j.val, hj⟩ i) false) :=
              ⟨ht1 ⟨j.val, hj⟩ i, fun _ _ => rfl⟩
            rw [(hp2 _ _ hws).2 _ (List.length_ofFn)]
            exact hcomp1 x ⟨j.val, hj⟩ i
          · rw [dite_neg hj]
            have hjm : j.val = m := by have := j.isLt; omega
            have hxj : (⟨j.val, by have := j.isLt; omega⟩ : Fin n) = jCur := Fin.ext hjm
            rw [hxj]
            refine htapM_val _ (x jCur) (List.length_ofFn) (fun p => ?_) i
            dsimp only [baseVals]
            have hlt := hbase_lt p
            rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_pos hlt]
            simp only [Option.getD_some]
            have hkey : key ⟨baseW p, hbase_lt p⟩ = jCur := by
              apply Fin.ext; dsimp only [key, baseW, jCur]
              rw [Nat.mul_comm, Nat.mul_add_div hblk_pos, Nat.div_eq_of_lt p.isLt, Nat.add_zero]
            have hidx : idx ⟨baseW p, hbase_lt p⟩ = p := by
              apply Fin.ext; dsimp only [idx, baseW]
              rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]
            dsimp only [bank, pick, site]; rw [hkey, hidx]
    rcases hbuild n (le_refl n) with ⟨gs, taps, hg, hc, ht, hcomp⟩
    exact ⟨a, names2, pick, bank, key, site, ⟨gs, 0⟩, taps, ha_le_q, hbank_le_c, hg, by rw [hc], ht,
      fun x j i => by have := hcomp x j i; exact this⟩
  ·
    rcases single_key_spec_h3 hk hk7 with ⟨names3, pick1, site1, hspec⟩
    let blk := d + (d + 1) / 2
    have hblk_pos : 0 < blk := by dsimp only [blk, d, e]; split_ifs <;> omega
    let a := n * blk
    let names : Fin h → Fin k → Bool := fun r =>
      if hr : r.val < 3 then names3 ⟨r.val, hr⟩ else fun _ => false
    let key : Fin a → Fin n := fun l => ⟨l.val / blk, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact l.isLt)⟩
    let idx : Fin a → Fin blk := fun l => ⟨l.val % blk, Nat.mod_lt _ hblk_pos⟩
    let pick : Fin a → Fin h := fun l => ⟨(pick1 (idx l)).val, by have := (pick1 (idx l)).isLt; omega⟩
    let bank : Fin a → Bool := fun _ => false
    let site : Fin a → Fin k := fun l => site1 (idx l)
    have hnames_eq : ∀ p : Fin blk, names ⟨(pick1 p).val, by have := (pick1 p).isLt; omega⟩ = names3 (pick1 p) := fun p => by
      dsimp only [names]; rw [dite_pos (pick1 p).isLt]
    have hbank_le_c : (Finset.univ.filter (fun l : Fin a => bank l = true)).card ≤ c := by
      have : Finset.univ.filter (fun l : Fin a => bank l = true) = ∅ := by
        ext l; simp [bank]
      rw [this, Finset.card_empty]; exact Nat.zero_le c
    have hbuild : ∀ (m : Nat) (hm : m ≤ n),
        ∃ (gs : List Gate) (taps : Fin m → Fin k → Nat),
          Good a gs ∧ gs.countP nonlinear = m * e ∧
          (∀ j i, taps j i < a + gs.length) ∧
          ∀ (x : Fin n → Fin k → Bool) (j : Fin m) (i : Fin k),
            (Circuit.wires ⟨gs, 0⟩ (List.ofFn (fun l : Fin a => readBit hk (bank l) (names (pick l)) (x (key l)) (site l)))).getD (taps j i) false =
            x ⟨j.val, Nat.lt_of_lt_of_le j.isLt hm⟩ i := by
      intro m hm
      induction m with
      | zero => exact ⟨[], fun j => j.elim0, good_nil a, by simp, fun j => j.elim0, fun _ j => j.elim0⟩
      | succ m ih =>
        rcases ih (by omega) with ⟨gs1, taps1, hg1, hc1, ht1, hcomp1⟩
        let jCur : Fin n := ⟨m, hm⟩
        let baseW : Fin blk → Nat := fun p => m * blk + p.val
        let baseVals : Fin blk → List Bool → Bool := fun p inp => inp.getD (baseW p) false
        have hbase_lt : ∀ p : Fin blk, baseW p < a := fun p => by
          dsimp only [baseW, a]
          calc m * blk + p.val < m * blk + blk := Nat.add_lt_add_left p.isLt _
            _ = (m + 1) * blk := by ring
            _ ≤ n * blk := Nat.mul_le_mul_right blk hm
        have hbase : ∀ p : Fin blk, WireSpec a gs1 (baseW p) (baseVals p) := fun p =>
          wireSpec_input_good gs1 hg1 (hbase_lt p)
        rcases hspec a gs1 hg1 baseW baseVals hbase with ⟨gs2, tapM, hg2, hc2, hp2, htapM_lt, htapM_val⟩
        let taps2 : Fin (m + 1) → Fin k → Nat := fun j i =>
          if hj : j.val < m then taps1 ⟨j.val, hj⟩ i else tapM i
        refine ⟨gs2, taps2, hg2, by rw [hc2, hc1]; ring, fun j i => ?_, fun x j i => ?_⟩
        · dsimp only [taps2]; by_cases hj : j.val < m
          · rw [dite_pos hj]
            have hws : WireSpec a gs1 (taps1 ⟨j.val, hj⟩ i) (fun inp => (Circuit.wires ⟨gs1, 0⟩ inp).getD (taps1 ⟨j.val, hj⟩ i) false) :=
              ⟨ht1 ⟨j.val, hj⟩ i, fun _ _ => rfl⟩
            exact (hp2 _ _ hws).1
          · rw [dite_neg hj]; exact htapM_lt i
        · dsimp only [taps2]; by_cases hj : j.val < m
          · rw [dite_pos hj]
            have hws : WireSpec a gs1 (taps1 ⟨j.val, hj⟩ i) (fun inp => (Circuit.wires ⟨gs1, 0⟩ inp).getD (taps1 ⟨j.val, hj⟩ i) false) :=
              ⟨ht1 ⟨j.val, hj⟩ i, fun _ _ => rfl⟩
            rw [(hp2 _ _ hws).2 _ (List.length_ofFn)]
            exact hcomp1 x ⟨j.val, hj⟩ i
          · rw [dite_neg hj]
            have hjm : j.val = m := by have := j.isLt; omega
            have hxj : (⟨j.val, by have := j.isLt; omega⟩ : Fin n) = jCur := Fin.ext hjm
            rw [hxj]
            refine htapM_val _ (x jCur) (List.length_ofFn) (fun p => ?_) i
            dsimp only [baseVals]
            have hlt := hbase_lt p
            rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_pos hlt]
            simp only [Option.getD_some]
            have hkey : key ⟨baseW p, hbase_lt p⟩ = jCur := by
              apply Fin.ext; dsimp only [key, baseW, jCur]
              rw [Nat.mul_comm, Nat.mul_add_div hblk_pos, Nat.div_eq_of_lt p.isLt, Nat.add_zero]
            have hidx : idx ⟨baseW p, hbase_lt p⟩ = p := by
              apply Fin.ext; dsimp only [idx, baseW]
              rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]
            have hpick : pick ⟨baseW p, hlt⟩ = ⟨(pick1 p).val, by have := (pick1 p).isLt; omega⟩ :=
              Fin.ext (by dsimp only [pick]; rw [hidx])
            dsimp only [bank, site]; rw [hkey, hpick, hidx, hnames_eq p]
    rcases hbuild n (le_refl n) with ⟨gs, taps, hg, hc, ht, hcomp⟩
    exact ⟨a, names, pick, bank, key, site, ⟨gs, 0⟩, taps, hq3, hbank_le_c, hg, by rw [hc], ht,
      fun x j i => by have := hcomp x j i; exact this⟩

end PEqualNP.Outside.L_meta_45025_aux

theorem PEqualNP.Outside.L_meta_45025 :
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
          (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
  let valid := fun (w : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack w C ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2
  ∀ (k : Nat) (hk : 0 < k), 7 ≤ k →
    let W := Fin k → Bool
    let ix := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
    let add := fun (u v : W) (i : Fin k) => xor (u i) (v i)
    let rot := fun (s : Nat) (w : W) (i : Fin k) => w (ix (i.val+k-s % k))
    let mix := fun (d : Nat) (w : W) (i : Fin k) =>
      xor (w (ix (i.val+k-d % k))) (xor (w i) (w (ix (i.val+d))))
    let readBit := fun (col : Bool) (u x : W) (i : Fin k) =>
      let d := if col then 2 else 1
      let R := mix d (add u (rot (if col then 3 else 1) x))
      xor (rot (if col then 4 else 0) x i)
        (xor (R i) (!(R (ix (i.val+1))) && R (ix (i.val+2))))
    let e := if 3 ∣ k then 2 else 0
    let d := k-e
    ∀ (n h q c : Nat),
      (∃ (a : Nat) (names : Fin h → W) (pick : Fin a → Fin h)
          (bank : Fin a → Bool) (key : Fin a → Fin n) (site : Fin a → Fin k)
          (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin n → Fin k → Nat),
        a ≤ q ∧ (Finset.univ.filter (fun j : Fin a => bank j = true)).card ≤ c ∧
        valid a C ∧ C.gates.countP nonlinear ≤ n*e ∧
        (∀ j i, tap j i < a+C.gates.length) ∧
        ∀ (x : Fin n → W) (j : Fin n) (i : Fin k),
          let data := List.ofFn (fun l : Fin a => readBit (bank l) (names (pick l)) (x (key l)) (site l))
          (C.wires data).getD (tap j i) false = x j i) ↔
        n = 0 ∨ (h = 2 ∧ 2*n*d ≤ q ∧ 2*n ≤ c) ∨
          (3 ≤ h ∧ n*(d+(d+1)/2) ≤ q) := by
  intro nonlinear valid k hk hk7 W ix add rot mix readBit e d n h q c
  constructor
  · rintro ⟨a, names, pick, bank, key, site, C, tap, haq, hbc, hval, hcnt, htap, hcomp⟩
    exact PEqualNP.Outside.L_meta_45025_aux.lower_bound_45025 hk hk7 n h q c a names pick bank key site C tap
      haq hbc hval hcnt htap hcomp
  · intro hcond
    exact PEqualNP.Outside.L_meta_45025_aux.upper_bound_45025 hk hk7 n h q c hcond
