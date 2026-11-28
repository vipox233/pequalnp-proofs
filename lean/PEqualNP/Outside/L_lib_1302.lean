import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1302

open scoped Classical
open PEqualNP.CircuitLowerBounds (Circuit Gate GateOp)
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

lemma bool_true_le_eq {b : Bool} (h : true ≤ b) : b = true := by
  cases b
  · exact absurd h (by decide)
  · rfl

def evalWires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

def notCountL (gs : List Gate) : ℕ :=
  (gs.filter fun g => isNotOp g.op).length

lemma notCountL_eq_notCount (C : Circuit) :
    notCountL C.gates = PEqualNP.NotBracket.notCount C := by
  unfold notCountL PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases g.op <;> simp [isNotOp]

def notCode : List Gate → List Bool → ℕ
  | [], _ => 0
  | g :: gs, w =>
    let val := g.op.eval (g.inputs.map fun i => w.getD i false)
    let rest := notCode gs (w ++ [val])
    if isNotOp g.op then
      (if val then 1 else 0) * 2 ^ (notCountL gs) + rest
    else
      rest

lemma notCountL_cons_not (g : Gate) (gs : List Gate) (h : isNotOp g.op = true) :
    notCountL (g :: gs) = notCountL gs + 1 := by
  simp [notCountL, h]

lemma notCountL_cons_ne (g : Gate) (gs : List Gate) (h : isNotOp g.op = false) :
    notCountL (g :: gs) = notCountL gs := by
  simp [notCountL, h]

lemma notCountL_append (gs1 gs2 : List Gate) :
    notCountL (gs1 ++ gs2) = notCountL gs1 + notCountL gs2 := by
  simp [notCountL, List.filter_append]

lemma notCode_lt : ∀ (gs : List Gate) (w : List Bool), notCode gs w < 2 ^ notCountL gs
  | [], _ => by simp [notCode, notCountL]
  | g :: gs, w => by
    have ih := notCode_lt gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    dsimp only [notCode]
    cases h : isNotOp g.op
    · simp only [Bool.false_eq_true, ↓reduceIte, notCountL_cons_ne g gs h]
      exact ih
    · simp only [↓reduceIte, notCountL_cons_not g gs h, pow_succ]
      generalize g.op.eval (g.inputs.map fun i => w.getD i false) = v at ih ⊢
      cases v <;> simp <;> omega

lemma getD_append_singleton {α : Type*} (w : List α) (a d : α) (i : ℕ) :
    (w ++ [a]).getD i d = if i < w.length then w.getD i d else if i = w.length then a else d := by
  by_cases h1 : i < w.length
  · rw [ite_eq_left h1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h1]
  · rw [ite_eq_right h1]
    have hge : w.length ≤ i := Nat.le_of_not_lt h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
    by_cases h2 : i = w.length
    · subst h2; simp
    · rw [ite_eq_right h2]
      have hgt : 1 ≤ i - w.length := by omega
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl

lemma getD_append_le {wa wb : List Bool} (hlen : wa.length = wb.length)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) {va vb : Bool} (hv : va ≤ vb) :
    ∀ i, (wa ++ [va]).getD i false ≤ (wb ++ [vb]).getD i false := by
  intro i
  rw [getD_append_singleton, getD_append_singleton, hlen]
  by_cases h1 : i < wb.length
  · rw [ite_eq_left h1, ite_eq_left h1]; exact hle i
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : i = wb.length
    · rw [ite_eq_left h2, ite_eq_left h2]; exact hv
    · rw [ite_eq_right h2, ite_eq_right h2]

lemma eval_and_mono (l : List ℕ) (wa wb : List Bool)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) :
    GateOp.and.eval (l.map fun i => wa.getD i false) ≤
    GateOp.and.eval (l.map fun i => wb.getD i false) := by
  dsimp only [GateOp.eval]
  cases ha : (l.map fun i => wa.getD i false).all id
  · exact Bool.false_le _
  · have hb : (l.map fun i => wb.getD i false).all id = true := by
      rw [List.all_eq_true] at ha ⊢
      intro x hx
      rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
      have h1 : wa.getD i false = true := ha (wa.getD i false) (List.mem_map.mpr ⟨i, hi, rfl⟩)
      exact bool_true_le_eq (h1 ▸ hle i)
    rw [hb]

lemma eval_or_mono (l : List ℕ) (wa wb : List Bool)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) :
    GateOp.or.eval (l.map fun i => wa.getD i false) ≤
    GateOp.or.eval (l.map fun i => wb.getD i false) := by
  dsimp only [GateOp.eval]
  cases ha : (l.map fun i => wa.getD i false).any id
  · exact Bool.false_le _
  · have hb : (l.map fun i => wb.getD i false).any id = true := by
      rw [List.any_eq_true] at ha ⊢
      rcases ha with ⟨x, hx, hxt⟩
      rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
      refine ⟨wb.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
      exact bool_true_le_eq (hxt ▸ hle i)
    rw [hb]

lemma eval_not_anti (l : List ℕ) (wa wb : List Bool)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) :
    GateOp.not.eval (l.map fun i => wb.getD i false) ≤
    GateOp.not.eval (l.map fun i => wa.getD i false) := by
  cases l with
  | nil => simp [GateOp.eval]
  | cons i _ =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons]
    have h := hle i
    generalize wa.getD i false = a at h ⊢
    generalize wb.getD i false = b at h ⊢
    revert h
    cases a <;> cases b <;> decide

lemma notCode_step : ∀ (gs : List Gate),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) →
    ∀ (wa wb : List Bool), wa.length = wb.length →
    (∀ i, wa.getD i false ≤ wb.getD i false) →
    (notCode gs wb < notCode gs wa) ∨
    (notCode gs wb = notCode gs wa ∧
      ∀ i, (evalWires gs wa).getD i false ≤ (evalWires gs wb).getD i false)
  | [], _, wa, wb, _, hle => Or.inr ⟨rfl, hle⟩
  | g :: gs, hfit, wa, wb, hlen, hle => by
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      have hm := hfit g (List.mem_cons_self ..)
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
    have hfit' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
      fun g' hg' => hfit g' (List.mem_cons_of_mem g hg')
    set va := g.op.eval (g.inputs.map fun i => wa.getD i false)
    set vb := g.op.eval (g.inputs.map fun i => wb.getD i false)
    have hlen' : (wa ++ [va]).length = (wb ++ [vb]).length := by simp [hlen]
    rcases hg with hand | hor | hnot
    · have hv : va ≤ vb := by
        dsimp only [va, vb]; rw [hand]; exact eval_and_mono g.inputs wa wb hle
      have hle' := getD_append_le hlen hle hv
      have hne : isNotOp g.op = false := by rw [hand]; rfl
      have ih := notCode_step gs hfit' (wa ++ [va]) (wb ++ [vb]) hlen' hle'
      simpa [notCode, evalWires, hne, va, vb] using ih
    · have hv : va ≤ vb := by
        dsimp only [va, vb]; rw [hor]; exact eval_or_mono g.inputs wa wb hle
      have hle' := getD_append_le hlen hle hv
      have hne : isNotOp g.op = false := by rw [hor]; rfl
      have ih := notCode_step gs hfit' (wa ++ [va]) (wb ++ [vb]) hlen' hle'
      simpa [notCode, evalWires, hne, va, vb] using ih
    · have hv_anti : vb ≤ va := by
        dsimp only [va, vb]; rw [hnot]; exact eval_not_anti g.inputs wa wb hle
      have hyes : isNotOp g.op = true := by rw [hnot]; rfl
      by_cases heq : va = vb
      · have hle' := getD_append_le hlen hle (le_of_eq heq)
        have ih := notCode_step gs hfit' (wa ++ [va]) (wb ++ [vb]) hlen' hle'
        dsimp only [notCode]
        rw [hyes]
        change (if vb then 1 else 0) * 2 ^ notCountL gs + notCode gs (wb ++ [vb]) <
            (if va then 1 else 0) * 2 ^ notCountL gs + notCode gs (wa ++ [va]) ∨
            ((if vb then 1 else 0) * 2 ^ notCountL gs + notCode gs (wb ++ [vb]) =
              (if va then 1 else 0) * 2 ^ notCountL gs + notCode gs (wa ++ [va]) ∧
              ∀ i, (evalWires gs (wa ++ [va])).getD i false ≤ (evalWires gs (wb ++ [vb])).getD i false)
        rw [heq] at ih ⊢
        rcases ih with hlt | ⟨heq', hw⟩
        · exact Or.inl (Nat.add_lt_add_left hlt _)
        · exact Or.inr ⟨by rw [heq'], hw⟩
      · have hva : va = true := by
          revert hv_anti heq; cases va <;> cases vb <;> decide
        have hvb : vb = false := by
          revert hv_anti heq; cases va <;> cases vb <;> decide
        left
        dsimp only [notCode]
        rw [hyes]
        change (if vb then 1 else 0) * 2 ^ notCountL gs + notCode gs (wb ++ [vb]) <
            (if va then 1 else 0) * 2 ^ notCountL gs + notCode gs (wa ++ [va])
        rw [hva, hvb]
        have hltb := notCode_lt gs (wb ++ [false])
        simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, zero_add, one_mul]
        omega

lemma eval_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    evalWires (g :: gs) w = evalWires gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma eval_append (gs hs : List Gate) (w : List Bool) :
    evalWires (gs ++ hs) w = evalWires hs (evalWires gs w) := List.foldl_append ..

lemma eval_len (gs : List Gate) (w : List Bool) :
    (evalWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalWires]
  | cons g gs ih => rw [eval_cons, ih]; simp; omega

lemma eval_old (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (evalWires gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [eval_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma eval_new (gs : List Gate) (g : Gate) (w : List Bool) :
    (evalWires (gs ++ [g]) w).getD (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (evalWires gs w).getD i false) := by
  rw [eval_append, ← eval_len gs w, eval_cons]
  simp [evalWires]

def Back (d : Nat) (gs : List Gate) : Prop :=
  ∀ j (h : j < gs.length), ∀ i ∈ gs[j].inputs, i < d + j

lemma back_iff (d : Nat) (C : Circuit) : Back d C.gates ↔ ReadsBack d C := by
  unfold Back ReadsBack gateAt
  simp only [List.getD_eq_getElem?_getD]
  constructor <;> intro h j hj <;> simpa [List.getElem?_eq_getElem hj] using h j hj

lemma back_cons (d : Nat) (g : Gate) (gs : List Gate) :
    Back d (g :: gs) ↔ (∀ i ∈ g.inputs, i < d) ∧ Back (d+1) gs := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      exact Nat.lt_of_lt_of_le (h 0 (by simp) i hi) (by omega)
    · intro j hj i hi
      have h' := h (j+1) (by simpa) i (by simpa using hi)
      omega
  · rintro ⟨hg, hgs⟩ (j | j) hj i hi
    · simpa using hg i hi
    · have h' := hgs j (by simpa using hj) i (by simpa using hi)
      omega

lemma back_append {d : Nat} {gs hs : List Gate} (hg : Back d gs)
    (hh : Back (d+gs.length) hs) : Back d (gs ++ hs) := by
  induction gs generalizing d with
  | nil => simpa using hh
  | cons g gs ih =>
    rw [List.cons_append, back_cons]
    rw [back_cons] at hg
    refine ⟨hg.1, ih hg.2 ?_⟩
    rw [show d + 1 + gs.length = d + (g :: gs).length by simp; omega]
    exact hh

def remap (f : Nat → Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def routing (d a : Nat) (f : Nat → Nat) (i : Nat) : Nat :=
  if i < d then f i else a + (i-d)

lemma routing_bound {d a : Nat} {f : Nat → Nat} (hf : ∀ i < d, f i < a)
    {j i : Nat} (hi : i < d+j) : routing d a f i < a+j := by
  unfold routing
  split
  · have := hf i (by assumption); omega
  · omega

lemma routing_gate (d a : Nat) (f : Nat → Nat) (j : Nat) :
    routing d a f (d+j) = a+j := by simp [routing]

lemma remap_back {d a : Nat} {gs : List Gate} (hg : Back d gs)
    {f : Nat → Nat} (hf : ∀ i < d, f i < a) :
    Back a (gs.map (remap (routing d a f))) := by
  intro j hj i hi
  simp only [List.getElem_map, remap, List.mem_map] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  exact routing_bound hf (hg j (by simpa using hj) k hk)

lemma remap_fan {C : Circuit} (hg : FanInTwo C) (f : Nat → Nat) (o : Nat) :
    FanInTwo ⟨C.gates.map (remap f), o⟩ := by
  intro g hg'
  obtain ⟨g', h, rfl⟩ := List.mem_map.mp hg'
  simpa [remap] using hg g' h

lemma remap_count (gs : List Gate) (f : Nat → Nat) :
    notCountL (gs.map (remap f)) = notCountL gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h : isNotOp g.op <;> simp [notCountL, remap, h, notCountL] at ih ⊢ <;> exact ih

lemma simulate {gs : List Gate} {f : Nat → Nat} {w v : List Bool}
    (hg : Back w.length gs)
    (hbound : ∀ i < w.length, f i < v.length)
    (hgate : ∀ j, f (w.length+j) = v.length+j)
    (hval : ∀ i < w.length, v.getD (f i) false = w.getD i false) :
    ∀ i < w.length + gs.length,
      (evalWires (gs.map (remap f)) v).getD (f i) false = (evalWires gs w).getD i false := by
  induction gs generalizing w v with
  | nil => simpa [evalWires] using hval
  | cons g gs ih =>
    obtain ⟨hg₁, hg₂⟩ := (back_cons ..).mp hg
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    have hb : (remap f g).op.eval ((remap f g).inputs.map fun i => v.getD i false) = b := by
      unfold remap b
      rw [List.map_map]
      congr 1
      exact List.map_congr_left (fun j hj => hval j (hg₁ j hj))
    have hw : (w ++ [b]).length = w.length + 1 := by simp
    have hv : (v ++ [b]).length = v.length + 1 := by simp
    simp only [List.map_cons, eval_cons, hb]
    intro i hi
    apply ih (w := w ++ [b]) (v := v ++ [b]) (by rwa [hw])
    · intro j hj
      by_cases h : j < w.length
      · have := hbound j h; omega
      · have hj' : j = w.length := by omega
        rw [hj', show w.length = w.length + 0 by omega, hgate]; omega
    · intro j
      rw [hw, hv, Nat.add_assoc, hgate, ← Nat.add_assoc]
    · intro j hj
      by_cases h : j < w.length
      · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hbound j h)]
        exact hval j h
      · have hj' : j = w.length := by omega
        have hf : f w.length = v.length := by simpa using hgate 0
        subst j
        simp [hf]
    · simp only [hw, List.length_cons] at *; omega

lemma simulate_routing {gs : List Gate} {d a : Nat} {f : Nat → Nat} {w v : List Bool}
    (hw : w.length = d) (hv : v.length = a) (hg : Back d gs)
    (hbound : ∀ i < d, f i < a)
    (hval : ∀ i < d, v.getD (f i) false = w.getD i false) :
    ∀ i < d + gs.length,
      (evalWires (gs.map (remap (routing d a f))) v).getD (routing d a f i) false =
      (evalWires gs w).getD i false := by
  subst d a
  exact simulate hg (fun i hi => routing_bound (j := 0) hbound (by simpa))
    (routing_gate _ _ _) (fun i hi => by simpa [routing, hi] using hval i hi)

noncomputable def maskBits {n : Nat} (s : Finset (Fin n)) : List Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  List.ofFn fun i : Fin n => decide (i ∈ s)

noncomputable def padBits (k l : Nat) : List Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  List.ofFn fun j : Fin k => decide (j.val < l)

lemma ofFn_getD {n : Nat} {f : Fin n → Bool} {i : Nat} (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i,h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa), List.getElem_ofFn]
  rfl

lemma mask_len {n : Nat} (s : Finset (Fin n)) : (maskBits s).length = n := by
  simp [maskBits]

lemma pad_len (k l : Nat) : (padBits k l).length = k := by simp [padBits]

lemma mask_bit {n : Nat} (s : Finset (Fin n)) (i : Fin n) :
    (maskBits s).getD i.val false = true ↔ i ∈ s := by
  rw [maskBits, ofFn_getD i.isLt]
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

lemma pad_bit {k l i : Nat} (hi : i < k) :
    (padBits k l).getD i false = true ↔ i < l := by
  rw [padBits, ofFn_getD hi]
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

lemma pad_order {k l l' : Nat} (h : l ≤ l') (i : Nat) :
    (padBits k l).getD i false ≤ (padBits k l').getD i false := by
  by_cases hi : i < k
  · cases hx : (padBits k l).getD i false
    · exact Bool.false_le _
    · rw [(pad_bit hi).mpr (lt_of_lt_of_le ((pad_bit hi).mp hx) h)]
  · have eq (a : Nat) : (padBits k a).getD i false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa [pad_len] using Nat.le_of_not_gt hi)]
      rfl
    rw [eq l, eq l']

lemma input_order {n k l l' : Nat} (s : Finset (Fin n)) (h : l ≤ l') :
    ∀ i, ((maskBits s ++ padBits k l) ++ [false,true]).getD i false ≤
      ((maskBits s ++ padBits k l') ++ [false,true]).getD i false := by
  intro i
  rw [List.append_assoc, List.append_assoc]
  by_cases hi : i < (maskBits s).length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi]
  · have hge := Nat.le_of_not_gt hi
    rw [List.getD_append_right (maskBits s) (padBits k l ++ _) false i hge,
      List.getD_append_right (maskBits s) (padBits k l' ++ _) false i hge]
    set j := i - (maskBits s).length
    by_cases hj : j < k
    · rw [List.getD_append (padBits k l) _ false j (by simpa [pad_len]),
        List.getD_append (padBits k l') _ false j (by simpa [pad_len])]
      exact pad_order h j
    · rw [List.getD_append_right (padBits k l) _ false j (by simpa [pad_len] using Nat.le_of_not_gt hj),
        List.getD_append_right (padBits k l') _ false j (by simpa [pad_len] using Nat.le_of_not_gt hj), pad_len, pad_len]

lemma stable_pair {q : Nat} {f : Nat → Nat} (hanti : Antitone f) (hbound : f 0 < q) :
    ∃ j : Fin q, f (2*j.val) = f (2*j.val+1) := by
  by_contra h
  have hs (j : Nat) (hj : j < q) : f (2*j+1) < f (2*j) := by
    refine lt_of_le_of_ne (hanti (by omega)) ?_
    exact fun he => h ⟨⟨j,hj⟩, he.symm⟩
  have grow (j : Nat) (hj : j ≤ q) : f (2*j) + j ≤ f 0 := by
    induction j with
    | zero => simp
    | succ j ih =>
      have ha : f (2*(j+1)) ≤ f (2*j+1) := hanti (by omega)
      have hb := hs j (by omega)
      have hc := ih (by omega)
      omega
  have := grow q le_rfl
  omega

lemma choose_pair {n k t r : Nat} (s : Finset (Fin n)) (base : Nat) (C : Circuit)
    (p : Fin t → Nat) (hf : FanInTwo C) (hc : PEqualNP.NotBracket.notCount C ≤ r) :
    ∃ j : Fin (2^r),
      ∀ a : Fin t,
        (C.wires ((maskBits s ++ padBits k (base+2*j.val)) ++ [false,true])).getD (p a) false ≤
        (C.wires ((maskBits s ++ padBits k (base+(2*j.val+1))) ++ [false,true])).getD (p a) false := by
  let w (i : Nat) := (maskBits s ++ padBits k (base+i)) ++ [false,true]
  let f (i : Nat) := notCode C.gates (w i)
  have step {i j : Nat} (h : i ≤ j) :=
    notCode_step C.gates (fun g hg => (hf g hg).1) (w i) (w j)
      (by simp [w, pad_len]) (input_order s (Nat.add_le_add_left h base))
  have hanti : Antitone f := by
    intro i j h
    rcases step h with hlt | ⟨heq, _⟩
    · exact le_of_lt hlt
    · exact le_of_eq heq
  have hbound : f 0 < 2^r := by
    have h := notCode_lt C.gates (w 0)
    rw [notCountL_eq_notCount] at h
    exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hc)
  obtain ⟨j, hj⟩ := stable_pair hanti hbound
  refine ⟨j, fun a => ?_⟩
  rcases step (show 2*j.val ≤ 2*j.val+1 by omega) with hlt | ⟨_, hout⟩
  · exact (not_lt_of_ge (le_of_eq hj) hlt).elim
  · exact hout (p a)

def andGates : Nat → Nat → List Nat → List Gate
  | _, _, [] => []
  | a, root, i :: is => ⟨.and, [root,i]⟩ :: andGates (a+1) a is

def andRoot (a root : Nat) (is : List Nat) : Nat :=
  if is.isEmpty then root else a + is.length - 1

lemma and_len (a root : Nat) (is : List Nat) :
    (andGates a root is).length = is.length := by
  induction is generalizing a root with
  | nil => rfl
  | cons i is ih => simp [andGates, ih]

lemma and_mem (a root : Nat) (is : List Nat) {g : Gate} (h : g ∈ andGates a root is) :
    g.op = .and ∧ g.inputs.length = 2 := by
  induction is generalizing a root with
  | nil => simp [andGates] at h
  | cons i is ih =>
    simp only [andGates, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨rfl,rfl⟩
    · exact ih _ _ h

lemma and_back {a root : Nat} {is : List Nat} (hr : root < a) (hi : ∀ i ∈ is, i < a) :
    Back a (andGates a root is) := by
  induction is generalizing a root with
  | nil => simp [andGates, Back]
  | cons i is ih =>
    rw [andGates, back_cons]
    refine ⟨?_, ih (by omega) (fun j hj => Nat.lt_succ_of_lt (hi j (List.mem_cons_of_mem _ hj)))⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact hr
    · exact hi _ (by simp)

lemma and_rt_bound {a root : Nat} (is : List Nat) (hr : root < a) :
    andRoot a root is < a + is.length := by
  cases is <;> simp [andRoot, hr]

lemma and_rt_cons (a root i : Nat) (is : List Nat) :
    andRoot a root (i :: is) = andRoot (a+1) a is := by
  cases is <;> simp [andRoot, Nat.add_assoc, Nat.add_comm 1]

lemma and_value (w : List Bool) (root : Nat) (is : List Nat)
    (hr : root < w.length) (hi : ∀ i ∈ is, i < w.length) :
    (evalWires (andGates w.length root is) w).getD (andRoot w.length root is) false = true ↔
      w.getD root false = true ∧ ∀ i ∈ is, w.getD i false = true := by
  induction is generalizing w root with
  | nil => simp [andRoot, andGates, evalWires]
  | cons i is ih =>
    let b := w.getD root false && w.getD i false
    have hb : GateOp.and.eval ([root,i].map fun j => w.getD j false) = b := by
      simp [GateOp.eval, b]
    let v := w ++ [b]
    have hv : v.length = w.length+1 := by simp [v]
    have hvb : v.getD w.length false = b := by simp [v]
    have hbnd : ∀ j ∈ is, j < v.length := fun j hj => by
      have := hi j (List.mem_cons_of_mem _ hj)
      omega
    have hvr (j : Nat) (hj : j ∈ is) : v.getD j false = w.getD j false :=
      List.getD_append _ _ _ _ (hi j (List.mem_cons_of_mem _ hj))
    have htail := ih v w.length (by omega) hbnd
    rw [hv, hvb] at htail
    simp only [andGates, eval_cons, hb, and_rt_cons]
    change (evalWires (andGates (w.length+1) w.length is) v).getD
      (andRoot (w.length+1) w.length is) false = true ↔ _
    rw [htail]
    simp only [b, Bool.and_eq_true, List.mem_cons]
    constructor
    · rintro ⟨⟨h₁,h₂⟩,ht⟩
      refine ⟨h₁, fun j hj => ?_⟩
      rcases hj with rfl | hj
      · exact h₂
      · exact (hvr j hj) ▸ ht j hj
    · rintro ⟨h₁,h₂⟩
      exact ⟨⟨h₁,h₂ i (Or.inl rfl)⟩, fun j hj => by rw [hvr j hj]; exact h₂ j (Or.inr hj)⟩

abbrev Item (n : Nat) := Finset (Fin n) × Nat

noncomputable def itemInputs {n : Nat} (s : Finset (Fin n)) : List Nat := s.toList.map Fin.val

def allRoot (n : Nat) (gs : List Gate) : Nat := if gs.isEmpty then n else n+2+gs.length-1

noncomputable def extendGates {n : Nat} : List (Item n) → List Gate
  | [] => []
  | (s, _) :: ls =>
    let gs := extendGates ls
    let a := n+2+gs.length
    let is := itemInputs s
    gs ++ andGates a (n+1) is ++ [⟨.or, [allRoot n gs, andRoot a (n+1) is]⟩]

noncomputable def extendTap {n : Nat} : List (Item n) → Nat → Nat
  | [], _ => n
  | item :: ls, b => if b < item.2 then allRoot n (extendGates (item :: ls)) else extendTap ls b

lemma item_length {n : Nat} (s : Finset (Fin n)) : (itemInputs s).length ≤ n := by
  simpa [itemInputs] using Finset.card_le_univ s

lemma item_bound {n : Nat} (s : Finset (Fin n)) {i : Nat} (h : i ∈ itemInputs s) : i < n := by
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
  exact j.isLt

lemma all_bound (n : Nat) (gs : List Gate) : allRoot n gs < n+2+gs.length := by
  cases gs <;> simp [allRoot]

lemma extend_len {n : Nat} (ls : List (Item n)) :
    (extendGates ls).length ≤ n*ls.length + ls.length := by
  induction ls with
  | nil => simp [extendGates]
  | cons item ls ih =>
    obtain ⟨s,b⟩ := item
    have h := item_length s
    simp [extendGates, and_len, Nat.mul_succ]
    omega

lemma extend_tap_bound {n : Nat} (ls : List (Item n)) (b : Nat) :
    extendTap ls b < n+2+(extendGates ls).length := by
  induction ls with
  | nil => simp [extendTap, extendGates]
  | cons item ls ih =>
    simp only [extendTap]
    split
    · exact all_bound _ _
    · obtain ⟨s,l⟩ := item
      simp [extendGates]
      omega

lemma extend_back {n : Nat} (ls : List (Item n)) : Back (n+2) (extendGates ls) := by
  induction ls with
  | nil => simp [extendGates, Back]
  | cons item ls ih =>
    obtain ⟨s,b⟩ := item
    dsimp only [extendGates]
    apply back_append (back_append ih (and_back (by omega) (fun i hi => by
      have := item_bound s hi; omega)))
    rw [back_cons]
    refine ⟨?_, by simp [Back]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.length_append, and_len]
    intro i hi
    rcases hi with rfl | rfl
    · have := all_bound n (extendGates ls); omega
    · have := and_rt_bound (itemInputs s) (a := n+2+(extendGates ls).length) (root := n+1) (by omega)
      omega

lemma extend_ops {n : Nat} (ls : List (Item n)) {g : Gate} (h : g ∈ extendGates ls) :
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
  induction ls with
  | nil => simp [extendGates] at h
  | cons item ls ih =>
    obtain ⟨s,b⟩ := item
    simp only [extendGates, List.mem_append, List.mem_singleton] at h
    rcases h with (h | h) | rfl
    · exact ih h
    · obtain ⟨ho, hl⟩ := and_mem _ _ _ h
      exact ⟨Or.inl ho,hl⟩
    · exact ⟨Or.inr rfl,rfl⟩

lemma extend_fan {n : Nat} (ls : List (Item n)) (o : Nat) : FanInTwo ⟨extendGates ls,o⟩ := by
  intro g hg
  obtain ⟨ho,hl⟩ := extend_ops ls hg
  exact ⟨by rcases ho with h | h <;> simp [h], by omega⟩

lemma extend_count {n : Nat} (ls : List (Item n)) : notCountL (extendGates ls) = 0 := by
  unfold notCountL
  suffices h : (extendGates ls).filter (fun g => isNotOp g.op) = [] by rw [h]; rfl
  apply List.filter_eq_nil_iff.mpr
  intro g hg
  rcases (extend_ops ls hg).1 with h | h <;> simp [h,isNotOp]

lemma mask_const_false {n : Nat} (x : Finset (Fin n)) :
    ((maskBits x) ++ [false,true]).getD n false = false := by
  rw [List.getD_append_right _ _ _ _ (by rw [mask_len]), mask_len, Nat.sub_self]
  rfl

lemma mask_const_true {n : Nat} (x : Finset (Fin n)) :
    ((maskBits x) ++ [false,true]).getD (n+1) false = true := by
  rw [List.getD_append_right _ _ _ _ (by rw [mask_len]; omega), mask_len, show n+1-n=1 by omega]
  rfl

lemma and_item {n : Nat} (s x : Finset (Fin n)) (gs : List Gate) :
    let w := maskBits x ++ [false,true]
    let a := n+2+gs.length
    (evalWires (gs ++ andGates a (n+1) (itemInputs s)) w).getD
      (andRoot a (n+1) (itemInputs s)) false = true ↔ s ⊆ x := by
  dsimp only
  rw [eval_append]
  let w := maskBits x ++ [false,true]
  let v := evalWires gs w
  have hw : w.length = n+2 := by simp [w,mask_len]
  have hv : v.length = n+2+gs.length := by rw [eval_len, hw]
  change (evalWires (andGates (n+2+gs.length) (n+1) (itemInputs s)) v).getD _ false = true ↔ _
  rw [← hv, and_value v _ _ (by omega) (fun i hi => by have := item_bound s hi; omega)]
  have hr : v.getD (n+1) false = true := by
    rw [eval_old _ _ _ (by omega)]
    exact mask_const_true x
  simp only [hr, true_and]
  constructor
  · intro h j hj
    have h' := h j.val (List.mem_map.mpr ⟨j, by simpa using hj, rfl⟩)
    rw [eval_old _ _ _ (by have := j.isLt; omega), List.getD_append _ _ _ _ (by rw [mask_len]; exact j.isLt)] at h'
    exact (mask_bit x j).mp h'
  · intro h i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    rw [eval_old _ _ _ (by have := j.isLt; omega), List.getD_append _ _ _ _ (by rw [mask_len]; exact j.isLt)]
    exact (mask_bit x j).mpr (h (by simpa using hj))

lemma extend_all {n : Nat} (ls : List (Item n)) (x : Finset (Fin n)) :
    (evalWires (extendGates ls) (maskBits x ++ [false,true])).getD
      (allRoot n (extendGates ls)) false = true ↔ ∃ item ∈ ls, item.1 ⊆ x := by
  induction ls with
  | nil =>
    change (maskBits x ++ [false,true]).getD n false = true ↔ _
    rw [mask_const_false x]
    simp
  | cons item ls ih =>
    obtain ⟨s,b⟩ := item
    let gs := extendGates ls
    let ag := andGates (n+2+gs.length) (n+1) (itemInputs s)
    let g : Gate := ⟨.or, [allRoot n gs, andRoot (n+2+gs.length) (n+1) (itemInputs s)]⟩
    let w := maskBits x ++ [false,true]
    have hw : w.length = n+2 := by simp [w,mask_len]
    change (evalWires ((gs ++ ag) ++ [g]) w).getD (allRoot n ((gs ++ ag) ++ [g])) false = true ↔ _
    have hroot : allRoot n ((gs ++ ag) ++ [g]) = w.length + (gs ++ ag).length := by
      simp [allRoot, hw]; omega
    rw [hroot, eval_new]
    have hpres : (evalWires (gs ++ ag) w).getD (allRoot n gs) false =
        (evalWires gs w).getD (allRoot n gs) false := by
      rw [eval_append, eval_old _ _ _ (by rw [eval_len,hw]; exact all_bound n gs)]
    change ([(evalWires (gs ++ ag) w).getD (allRoot n gs) false,
      (evalWires (gs ++ ag) w).getD (andRoot (n+2+gs.length) (n+1) (itemInputs s)) false].any id = true) ↔ _
    simp only [List.any_cons, List.any_nil, Bool.or_false, id_eq, Bool.or_eq_true, hpres]
    have ha := and_item s x gs
    dsimp only at ha
    rw [ha]
    change ((evalWires (extendGates ls) w).getD (allRoot n (extendGates ls)) false = true ∨ s ⊆ x) ↔ _
    rw [ih]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_comm

lemma extend_value {n : Nat} (ls : List (Item n)) (x : Finset (Fin n))
    (h : ls.Pairwise fun a b => a.2 ≤ b.2) (b : Nat) :
    (evalWires (extendGates ls) (maskBits x ++ [false,true])).getD (extendTap ls b) false = true ↔
      ∃ item ∈ ls, b < item.2 ∧ item.1 ⊆ x := by
  induction ls with
  | nil =>
    change (maskBits x ++ [false,true]).getD n false = true ↔ _
    rw [mask_const_false x]
    simp
  | cons item ls ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp h
    simp only [extendTap]
    split
    · rename_i hb
      rw [extend_all]
      constructor
      · rintro ⟨p,hp,hx⟩
        refine ⟨p,hp,?_,hx⟩
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact hb
        · exact lt_of_lt_of_le hb (hhead p hp')
      · rintro ⟨p,hp,_,hx⟩
        exact ⟨p,hp,hx⟩
    · rename_i hb
      obtain ⟨s,l⟩ := item
      dsimp only [extendGates]
      have ht := extend_tap_bound ls b
      rw [eval_append, eval_append]
      rw [eval_old _ _ _ (by
        rw [eval_len, eval_len]
        simp only [List.length_append, List.length_cons, List.length_nil, mask_len]
        omega)]
      rw [eval_old _ _ _ (by
        rw [eval_len]
        simp only [List.length_append, List.length_cons, List.length_nil, mask_len]
        omega), ih htail]
      constructor
      · rintro ⟨p,hp,hlt,hx⟩
        exact ⟨p,List.mem_cons_of_mem _ hp,hlt,hx⟩
      · rintro ⟨p,hp,hlt,hx⟩
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact (hb hlt).elim
        · exact ⟨p,hp',hlt,hx⟩

noncomputable def readMask {t : Nat} (C : Circuit) (p : Fin t → Nat) (v : List Bool) : Finset (Fin t) :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  Finset.univ.filter fun a => (C.wires (v ++ [false,true])).getD (p a) false = true

def ValidW {t : Nat} (d r : Nat) (C : Circuit) (p : Fin t → Nat) : Prop :=
  FanInTwo C ∧ ReadsBack d C ∧ C.output < d+C.size ∧ (∀ a, p a < d+C.size) ∧
    PEqualNP.NotBracket.notCount C ≤ r

lemma transfer {t d a r : Nat} {C : Circuit} {p : Fin t → Nat} (hc : ValidW d r C p)
    (B : List Gate) (hBfan : FanInTwo ⟨B,0⟩) (hBback : Back a B) (hBcount : notCountL B = 0)
    (f : Nat → Nat) (hf : ∀ i < d, f i < a+B.length) :
    ∃ E w, ValidW a r E w ∧ E.size = C.size+B.length ∧
      PEqualNP.NotBracket.notCount E = PEqualNP.NotBracket.notCount C ∧
      ∀ u v : List Bool, u.length+2 = a → v.length+2 = d →
        (∀ i < d, (evalWires B (u ++ [false,true])).getD (f i) false =
          (v ++ [false,true]).getD i false) → readMask E w u = readMask C p v := by
  obtain ⟨hfan,hback,hout,htap,hcnt⟩ := hc
  let route := routing d (a+B.length) f
  let gs := C.gates.map (remap route)
  let E : Circuit := ⟨B ++ gs, route C.output⟩
  have hlen : E.size = C.size+B.length := by simp [E, gs, Circuit.size, Nat.add_comm]
  have hn : PEqualNP.NotBracket.notCount E = PEqualNP.NotBracket.notCount C := by
    rw [← notCountL_eq_notCount, ← notCountL_eq_notCount]
    change notCountL (B ++ C.gates.map (remap route)) = notCountL C.gates
    rw [notCountL_append, remap_count, hBcount, zero_add]
  refine ⟨E, route ∘ p, ⟨?_, ?_, ?_, ?_, hn ▸ hcnt⟩, hlen, hn, ?_⟩
  · intro g hg
    change g ∈ B ++ gs at hg
    rcases List.mem_append.mp hg with h | h
    · exact hBfan g h
    · exact remap_fan hfan route 0 g h
  · apply (back_iff a E).mp
    exact back_append hBback (remap_back ((back_iff d C).mpr hback) hf)
  · have h : route C.output < a+B.length+C.size := routing_bound hf (j := C.size) hout
    change route C.output < a+E.size
    omega
  · intro i
    have h : route (p i) < a+B.length+C.size := routing_bound hf (j := C.size) (htap i)
    change route (p i) < a+E.size
    omega
  · intro u v hu hv hval
    ext i
    simp only [readMask, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    change (evalWires (B ++ gs) (u ++ [false,true])).getD (route (p i)) false = true ↔
      (evalWires C.gates (v ++ [false,true])).getD (p i) false = true
    rw [eval_append]
    rw [simulate_routing (w := v ++ [false,true]) (v := evalWires B (u ++ [false,true]))
      (by simpa using hv) (by rw [eval_len]; simp [hu]) ((back_iff d C).mpr hback) hf hval
      (p i) (htap i)]

lemma forward_transfer {n k t r : Nat} {C : Circuit} {p : Fin t → Nat}
    (hc : ValidW (n+2) r C p) :
    ∃ E w, ValidW (n+k+2) r E w ∧ E.size = C.size ∧
      PEqualNP.NotBracket.notCount E = PEqualNP.NotBracket.notCount C ∧
      ∀ u v : List Bool, u.length = n → v.length = k → readMask E w (u ++ v) = readMask C p u := by
  let f (i : Nat) := if i < n then i else i+k
  have hb : ∀ i < n+2, f i < n+k+2+([ ] : List Gate).length := by
    intro i hi; simp only [f,List.length_nil,Nat.add_zero]; split <;> omega
  obtain ⟨E,w,he,hs,hn,hr⟩ := transfer (a := n+k+2) hc [] (by simp [FanInTwo])
    (by simp [Back]) (by simp [notCountL]) f hb
  refine ⟨E,w,he,by simpa using hs,hn,?_⟩
  intro u v hu hv
  apply hr _ _ (by simp [hu,hv]) (by simp [hu])
  intro i hi
  change (((u ++ v) ++ [false,true]).getD (f i) false = (u ++ [false,true]).getD i false)
  by_cases h : i < n
  · have h₁ : i < u.length := by omega
    have h₂ : i < (u ++ v).length := by simp [hu,hv]; omega
    simp only [f, ite_eq_left h]
    rw [List.getD_append (u ++ v) _ false i h₂, List.getD_append u v false i h₁,
      List.getD_append u [false,true] false i h₁]
  · have h₁ : u.length ≤ i := by omega
    have h₂ : (u ++ v).length ≤ i+k := by simp [hu,hv]; omega
    simp only [f, ite_eq_right h]
    rw [List.getD_append_right (u ++ v) _ false (i+k) h₂,
      List.getD_append_right u [false,true] false i h₁]
    simp only [List.length_append, hu,hv]
    congr 1
    omega

lemma backward_transfer {n k m t r : Nat} {E : Circuit} {w : Fin t → Nat}
    (he : ValidW (n+k+2) r E w) (ls : List (Item n)) (x : Fin m → Finset (Fin n))
    (l : Fin m → Nat)
    (hpad : ∀ i : Fin m, ∀ b < k,
      (evalWires (extendGates ls) (maskBits (x i) ++ [false,true])).getD (extendTap ls b) false = true ↔ b < l i) :
    ∃ C p, ValidW (n+2) r C p ∧ C.size = E.size+(extendGates ls).length ∧
      PEqualNP.NotBracket.notCount C = PEqualNP.NotBracket.notCount E ∧
      ∀ i, readMask C p (maskBits (x i)) = readMask E w (maskBits (x i) ++ padBits k (l i)) := by
  let f (i : Nat) := if i < n then i else if i < n+k then extendTap ls (i-n) else i-k
  have hb : ∀ i < n+k+2, f i < n+2+(extendGates ls).length := by
    intro i hi
    unfold f
    split
    · omega
    · split
      · exact extend_tap_bound _ _
      · omega
  obtain ⟨C,p,hc,hs,hn,hr⟩ := transfer he (extendGates ls) (extend_fan ls 0)
    (extend_back ls) (extend_count ls) f hb
  refine ⟨C,p,hc,hs,hn,fun i => ?_⟩
  apply hr _ _ (by simp [mask_len]) (by simp [mask_len,pad_len])
  intro j hj
  let u := maskBits (x i)
  let v := padBits k (l i)
  have hu : u.length = n := mask_len _
  have hv : v.length = k := pad_len ..
  change (evalWires (extendGates ls) (u ++ [false,true])).getD (f j) false =
    ((u ++ v) ++ [false,true]).getD j false
  by_cases h₁ : j < n
  · have hsmall : j < u.length := by omega
    have hbig : j < (u ++ v).length := by simp [hu,hv]; omega
    simp only [f, ite_eq_left h₁]
    rw [eval_old _ _ _ (by simp [hu]; omega), List.getD_append u [false,true] false j hsmall,
      List.getD_append (u ++ v) _ false j hbig, List.getD_append u v false j hsmall]
  · by_cases h₂ : j < n+k
    · have hsub : j-n < k := by omega
      simp only [f, ite_eq_right h₁, ite_eq_left h₂]
      rw [List.getD_append (u ++ v) _ false j (by simp [hu,hv]; omega),
        List.getD_append_right u v false j (by omega), hu]
      apply Bool.eq_iff_iff.mpr
      exact (hpad i _ hsub).trans (pad_bit hsub).symm
    · have hsub : n ≤ j-k := by omega
      simp only [f, ite_eq_right h₁, ite_eq_right h₂]
      rw [eval_old _ _ _ (by simp [hu]; omega),
        List.getD_append_right u [false,true] false (j-k) (by omega),
        List.getD_append_right (u ++ v) _ false j (by simp [hu,hv]; omega)]
      simp only [List.length_append,hu,hv]
      congr 1
      omega

lemma readMask_subset_of_le {t : Nat} (C : Circuit) (p : Fin t → Nat) (u v : List Bool)
    (h : ∀ a, (C.wires (u ++ [false,true])).getD (p a) false ≤
              (C.wires (v ++ [false,true])).getD (p a) false) : readMask C p u ⊆ readMask C p v := by
  intro a ha
  simp only [readMask, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  have hh := h a
  rw [ha] at hh
  exact bool_true_le_eq hh

lemma forward_fit {n m t r q k : Nat} (x : Fin m → Finset (Fin n))
    (U D : Fin m → Finset (Fin t) → Prop) (C : Circuit) (p : Fin t → Nat)
    (hc : ValidW (n+2) r C p ∧ ∀ i, U i (readMask C p (maskBits (x i))) ∧
      D i (readMask C p (maskBits (x i)))) :
    ∃ E w, (ValidW (n+k+2) r E w ∧ ∀ i (j : Fin q),
      U i (readMask E w (maskBits (x i) ++ padBits k (2*q*(x i).card+2*j.val))) ∧
      D i (readMask E w (maskBits (x i) ++ padBits k (2*q*(x i).card+(2*j.val+1))))) ∧
      E.size = C.size ∧ PEqualNP.NotBracket.notCount E = PEqualNP.NotBracket.notCount C := by
  obtain ⟨E,w,he,hs,hn,hr⟩ := forward_transfer (k := k) hc.1
  refine ⟨E,w,⟨he,fun i j => ?_⟩,hs,hn⟩
  constructor
  · rw [hr _ _ (mask_len _) (pad_len ..)]
    exact (hc.2 i).1
  · rw [hr _ _ (mask_len _) (pad_len ..)]
    exact (hc.2 i).2

lemma sorted_items {n m : Nat} (x : Fin m → Finset (Fin n)) (l : Fin m → Nat) :
    ∃ ls : List (Item n), ls.length = m ∧ ls.Pairwise (fun a b => a.2 ≤ b.2) ∧
    ∀ a : Item n, a ∈ ls ↔ ∃ i, (x i,l i) = a := by
  let le (a b : Item n) := decide (a.2 ≤ b.2)
  let xs : List (Item n) := List.ofFn fun i => (x i,l i)
  refine ⟨xs.mergeSort le, by rw [List.length_mergeSort]; simp [xs], ?_, ?_⟩
  · apply List.Pairwise.imp (S := fun (a b : Item n) => a.2 ≤ b.2) (R := fun a b => le a b = true)
    · intros; simpa [le] using ‹le _ _ = true›
    · apply List.pairwise_mergeSort (le := le)
      · intro a b c
        simpa [le] using (Nat.le_trans : a.2 ≤ b.2 → b.2 ≤ c.2 → a.2 ≤ c.2)
      · intro a b
        simp [le, le_total]
  · intro a
    rw [List.mem_mergeSort, List.mem_ofFn]

noncomputable def rightStage (b : Bool) : Nat :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  if b then 1 else 0

lemma backward_fit {n m t r k : Nat} (x : Fin m → Finset (Fin n))
    (U D : Fin m → Finset (Fin t) → Prop) (right : Fin m → Bool)
    (hx : Function.Injective x)
    (hcl : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
      ∀ i a b, a ⊆ b → if right i then U i a → U i b else D i b → D i a)
    (E : Circuit) (w : Fin t → Nat)
    (he : ValidW (n+k+2) r E w ∧ ∀ i (j : Fin (2^r)),
      U i (readMask E w (maskBits (x i) ++ padBits k (2*2^r*(x i).card+2*j.val))) ∧
      D i (readMask E w (maskBits (x i) ++ padBits k (2*2^r*(x i).card+(2*j.val+1))))) :
    ∃ C p, ∃ choose : Fin m → Fin (2^r),
      (ValidW (n+2) r C p ∧ ∀ i, U i (readMask C p (maskBits (x i))) ∧
        D i (readMask C p (maskBits (x i)))) ∧
      C.size ≤ E.size+n*m+m+k ∧ PEqualNP.NotBracket.notCount C = PEqualNP.NotBracket.notCount E ∧
      ∀ i, readMask C p (maskBits (x i)) = readMask E w
        (maskBits (x i) ++ padBits k (2*2^r*(x i).card+(2*(choose i).val+rightStage (right i)))) := by
  have hpair (i : Fin m) := choose_pair (k := k) (x i) (2*2^r*(x i).card) E w he.1.1 he.1.2.2.2.2
  choose sel hsel using hpair
  let l (i : Fin m) := 2*2^r*(x i).card + (2*(sel i).val + rightStage (right i))
  have hfit (i : Fin m) : U i (readMask E w (maskBits (x i) ++ padBits k (l i))) ∧
      D i (readMask E w (maskBits (x i) ++ padBits k (l i))) := by
    have hab := readMask_subset_of_le E w _ _ (hsel i)
    have hclose := hcl i _ _ hab
    obtain ⟨hu,hd⟩ := he.2 i (sel i)
    cases hr : right i
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at hclose
      simpa [l,rightStage,hr] using And.intro hu (hclose hd)
    · simp only [hr, ↓reduceIte] at hclose
      simpa [l,rightStage,hr] using And.intro (hclose hu) hd
  have hl (i j : Fin m) (h : x i ⊆ x j) : l i ≤ l j := by
    by_cases hij : i = j
    · simp [hij]
    have hcard : (x i).card < (x j).card := by
      apply Finset.card_lt_card
      exact lt_of_le_of_ne h (fun hh => hij (hx hh))
    calc
      l i ≤ (2*2^r)*((x i).card+1) := by
        unfold l
        rw [Nat.mul_succ, Nat.mul_comm 2 (2^r)]
        have hsel := (sel i).isLt
        cases right i <;> simp [rightStage] <;> omega
      _ ≤ (2*2^r)*(x j).card := Nat.mul_le_mul_left _ (by omega)
      _ ≤ l j := Nat.le_add_right _ _
  obtain ⟨ls,hlsLen,hlsSort,hlsMem⟩ := sorted_items x l
  have hpad (i : Fin m) (b : Nat) (_ : b < k) :
      (evalWires (extendGates ls) (maskBits (x i) ++ [false,true])).getD (extendTap ls b) false = true ↔ b < l i := by
    rw [extend_value _ _ hlsSort]
    constructor
    · rintro ⟨a,ha,hb,hax⟩
      obtain ⟨j,rfl⟩ := (hlsMem a).mp ha
      exact lt_of_lt_of_le hb (hl j i hax)
    · intro hb
      exact ⟨(x i,l i),(hlsMem _).mpr ⟨i,rfl⟩,hb,Finset.Subset.refl _⟩
  obtain ⟨C,p,hc,hs,hn,hr⟩ := backward_transfer he.1 ls x l hpad
  refine ⟨C,p,sel,⟨hc,fun i => ?_⟩,?_,hn,hr⟩
  · rw [hr]
    exact hfit i
  · have hsize := extend_len ls
    rw [hlsLen] at hsize
    omega
end PEqualNP.Outside.L_lib_1302

theorem PEqualNP.Outside.L_lib_1302 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m t r : Nat) (x : Fin m → Finset (Fin n)) (U D : Fin m → Finset (Fin t) → Prop)
  (right : Fin m → Bool),
  Function.Injective x →
  (∀ i a b, a ⊆ b → if right i then U i a → U i b else D i b → D i a) →
  let q := 2^r
  let K := 2*q*(n+1)
  let src := fun (i : Fin m) => List.ofFn (fun a : Fin n => decide (a ∈ x i))
  let dst := fun (i : Fin m) (s : Nat) =>
    src i ++ List.ofFn (fun b : Fin K => decide (b.val < 2*q*(x i).card+s))
  let readW := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin t → Nat) (v : List Bool) =>
    Finset.univ.filter (fun a => (C.wires (v ++ [false,true])).getD (p a) false = true)
  let valid := fun (d : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin t → Nat) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
    C.output < d+2+C.size ∧ (∀ a, p a < d+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ r
  let original := fun C p => valid n C p ∧ ∀ i, U i (readW C p (src i)) ∧ D i (readW C p (src i))
  let splitFit := fun C p => valid (n+K) C p ∧ ∀ i (j : Fin q),
    U i (readW C p (dst i (2*j.val))) ∧ D i (readW C p (dst i (2*j.val+1)))
  (∀ C p, original C p → ∃ E w, splitFit E w ∧ E.size = C.size ∧
    PEqualNP.NotBracket.notCount E = PEqualNP.NotBracket.notCount C) ∧
  (∀ E w, splitFit E w → ∃ C p, ∃ choose : Fin m → Fin q, original C p ∧
    C.size ≤ E.size + n*m+m+K ∧ PEqualNP.NotBracket.notCount C = PEqualNP.NotBracket.notCount E ∧
    ∀ i, readW C p (src i) = readW E w (dst i (2*(choose i).val + (if right i then 1 else 0))))) := by
  intro n m t r x U D right hx hcl
  dsimp only
  constructor
  · exact PEqualNP.Outside.L_lib_1302.forward_fit x U D
  · exact PEqualNP.Outside.L_lib_1302.backward_fit x U D right hx hcl
