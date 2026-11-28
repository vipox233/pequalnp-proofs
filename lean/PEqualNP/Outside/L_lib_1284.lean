import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1284_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket
open PEqualNP.MetaComplexity.NestedCover
open scoped Classical

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_ge_length {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_mem {α : Type*} (l : List α) (k : ℕ) (d : α) (hk : k < l.length) :
    l.getD k d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma notCount_nil (o : ℕ) : notCount ⟨[], o⟩ = 0 := rfl

lemma notCount_append (gs1 gs2 : List Gate) (o : ℕ) :
    notCount ⟨gs1 ++ gs2, o⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp [notCount, List.filter_append]

lemma fanInTwo_nil (o : ℕ) : FanInTwo ⟨[], o⟩ := by
  intro g hg; cases hg

lemma fanInTwo_append {gs1 gs2 : List Gate} {o : ℕ}
    (h1 : FanInTwo ⟨gs1, 0⟩) (h2 : FanInTwo ⟨gs2, 0⟩) :
    FanInTwo ⟨gs1 ++ gs2, o⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with hg1 | hg2
  · exact h1 g hg1
  · exact h2 g hg2

lemma readsBack_nil (m o : ℕ) : ReadsBack m ⟨[], o⟩ := by
  intro j hj; cases hj

lemma readsBack_append {m : ℕ} {gs1 gs2 : List Gate} {o : ℕ}
    (h1 : ReadsBack m ⟨gs1, 0⟩) (h2 : ReadsBack (m + gs1.length) ⟨gs2, 0⟩) :
    ReadsBack m ⟨gs1 ++ gs2, o⟩ := by
  intro j hj i hi
  rw [gateAt_eq_getElem _ j hj] at hi
  by_cases hj1 : j < gs1.length
  · have hget : (gs1 ++ gs2)[j] = gs1[j] := List.getElem_append_left hj1
    rw [hget] at hi
    have h1' := h1 j hj1
    rw [gateAt_eq_getElem _ j hj1] at h1'
    exact h1' i hi
  · have hj1' : gs1.length ≤ j := Nat.le_of_not_lt hj1
    have hj2 : j - gs1.length < gs2.length := by
      simp only [List.length_append] at hj
      omega
    have hget : (gs1 ++ gs2)[j] = gs2[j - gs1.length] := List.getElem_append_right hj1'
    rw [hget] at hi
    have h2' := h2 (j - gs1.length) hj2
    rw [gateAt_eq_getElem _ (j - gs1.length) hj2] at h2'
    have hlt := h2' i hi
    omega

def inpVec {n : ℕ} (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]

lemma inpVec_length {n : ℕ} (x : Finset (Fin n)) : (inpVec x).length = n + 2 := by
  simp [inpVec]

lemma inpVec_getD_fin {n : ℕ} (x : Finset (Fin n)) (i : Fin n) :
    (inpVec x).getD i.val false = decide (i ∈ x) := by
  dsimp only [inpVec]
  rw [getD_append_left _ _ i.val false (by simp [i.isLt])]
  simp [List.getD_eq_getElem?_getD, i.isLt]

lemma inpVec_getD_false {n : ℕ} (x : Finset (Fin n)) :
    (inpVec x).getD n false = false := by
  dsimp only [inpVec]
  rw [getD_append_right _ _ n false (by simp)]
  simp

lemma inpVec_getD_true {n : ℕ} (x : Finset (Fin n)) :
    (inpVec x).getD (n + 1) false = true := by
  dsimp only [inpVec]
  rw [getD_append_right _ _ (n + 1) false (by simp)]
  have hsub : n + 1 - n = 1 := by omega
  simp [hsub]

lemma bool_le_iff (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

lemma not_true_le_false (h : (true : Bool) ≤ false) : False := by
  have := (bool_le_iff true false).mp h rfl
  cases this

lemma inpVec_mono {n : ℕ} {u v : Finset (Fin n)} (huv : u ⊆ v) (k : ℕ) :
    (inpVec u).getD k false ≤ (inpVec v).getD k false := by
  by_cases hk1 : k < n
  · have hu := inpVec_getD_fin u ⟨k, hk1⟩
    have hv := inpVec_getD_fin v ⟨k, hk1⟩
    dsimp only at hu hv
    rw [hu, hv, bool_le_iff]
    intro h
    exact decide_eq_true (huv (of_decide_eq_true h))
  · by_cases hk2 : k = n
    · subst hk2; rw [inpVec_getD_false, inpVec_getD_false]
    · by_cases hk3 : k = n + 1
      · subst hk3; rw [inpVec_getD_true, inpVec_getD_true]
      · rw [getD_ge_length _ k false (by rw [inpVec_length]; omega)]
        rw [getD_ge_length _ k false (by rw [inpVec_length]; omega)]

lemma all_map_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).all id ≤ (l.map g).all id := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.all_cons, id_eq]
    have ha := h a (List.mem_cons_self ..)
    have htl := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    cases hfa : f a <;> cases hga : g a <;>
      cases h1 : (tl.map f).all id <;> cases h2 : (tl.map g).all id <;> simp_all

lemma any_map_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).any id ≤ (l.map g).any id := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.any_cons, id_eq]
    have ha := h a (List.mem_cons_self ..)
    have htl := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    cases hfa : f a <;> cases hga : g a <;>
      cases h1 : (tl.map f).any id <;> cases h2 : (tl.map g).any id <;> simp_all

lemma not_headD_anti (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i ≤ g i) :
    (!((l.map g).headD false)) ≤ (!((l.map f).headD false)) := by
  cases l with
  | nil => simp
  | cons a tl =>
    simp only [List.map_cons, List.headD_cons]
    have ha := h a (List.mem_cons_self ..)
    cases hfa : f a <;> cases hga : g a <;> simp_all

def evalNotCode : List Gate → List Bool → ℕ
  | [], _ => 0
  | g :: gs, w =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    let rest := evalNotCode gs (w ++ [v])
    match g.op with
    | GateOp.not => (if v then 2 ^ (notCount ⟨gs, 0⟩) else 0) + rest
    | _ => rest

lemma evalNotCode_lt (gs : List Gate) (w : List Bool) :
    evalNotCode gs w < 2 ^ (notCount ⟨gs, 0⟩) := by
  induction gs generalizing w with
  | nil => simp [evalNotCode, notCount]
  | cons g gs ih =>
    dsimp only [evalNotCode]
    cases hg : g.op with
    | not =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ + 1 := by simp [notCount, hg]
      rw [hnc, pow_succ]
      cases hv : GateOp.not.eval (g.inputs.map fun i => w.getD i false) with
      | false =>
        have hrest := ih (w ++ [false])
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        omega
      | true =>
        have hrest := ih (w ++ [true])
        simp only [↓reduceIte]
        omega
    | and =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ := by simp [notCount, hg]
      rw [hnc]; exact ih _
    | or =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ := by simp [notCount, hg]
      rw [hnc]; exact ih _
    | mod k =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ := by simp [notCount, hg]
      rw [hnc]; exact ih _
    | maj =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ := by simp [notCount, hg]
      rw [hnc]; exact ih _

lemma append_singleton_getD_mono (w1 w2 : List Bool) (v1 v2 : Bool)
    (hlen : w1.length = w2.length)
    (hw : ∀ i, w1.getD i false ≤ w2.getD i false)
    (hv : v1 ≤ v2) (i : ℕ) :
    (w1 ++ [v1]).getD i false ≤ (w2 ++ [v2]).getD i false := by
  by_cases hi : i < w1.length
  · rw [getD_append_left w1 [v1] i false hi]
    rw [getD_append_left w2 [v2] i false (by omega)]
    exact hw i
  · rw [getD_append_right w1 [v1] i false (by omega)]
    rw [getD_append_right w2 [v2] i false (by omega)]
    rw [hlen]
    by_cases h0 : i - w2.length = 0
    · rw [h0]; simpa using hv
    · rw [getD_ge_length [v1] _ false (by simp; omega)]
      rw [getD_ge_length [v2] _ false (by simp; omega)]

lemma evalNotCode_dichotomy (gs : List Gate) (w1 w2 : List Bool)
    (hfit : FanInTwo ⟨gs, 0⟩)
    (hlen : w1.length = w2.length)
    (hw : ∀ i, w1.getD i false ≤ w2.getD i false) :
    evalNotCode gs w2 < evalNotCode gs w1 ∨
    (evalNotCode gs w2 = evalNotCode gs w1 ∧
      ∀ i, (wiresFrom gs w1).getD i false ≤ (wiresFrom gs w2).getD i false) := by
  induction gs generalizing w1 w2 with
  | nil => exact Or.inr ⟨rfl, hw⟩
  | cons g gs ih =>
    have hgfit := hfit g (List.mem_cons_self ..)
    have hgsfit : FanInTwo ⟨gs, 0⟩ := fun g' hg' => hfit g' (List.mem_cons_of_mem _ hg')
    dsimp only [evalNotCode, wiresFrom_cons]
    rcases hgfit.1 with h_and | h_or | h_not
    · rw [h_and]
      have hv : GateOp.and.eval (g.inputs.map fun i => w1.getD i false) ≤
          GateOp.and.eval (g.inputs.map fun i => w2.getD i false) :=
        all_map_mono g.inputs _ _ (fun i _ => hw i)
      exact ih _ _ hgsfit (by simp [hlen]) (append_singleton_getD_mono w1 w2 _ _ hlen hw hv)
    · rw [h_or]
      have hv : GateOp.or.eval (g.inputs.map fun i => w1.getD i false) ≤
          GateOp.or.eval (g.inputs.map fun i => w2.getD i false) :=
        any_map_mono g.inputs _ _ (fun i _ => hw i)
      exact ih _ _ hgsfit (by simp [hlen]) (append_singleton_getD_mono w1 w2 _ _ hlen hw hv)
    · rw [h_not]
      set v1 := GateOp.not.eval (g.inputs.map fun i => w1.getD i false)
      set v2 := GateOp.not.eval (g.inputs.map fun i => w2.getD i false)
      have hvanti : v2 ≤ v1 := not_headD_anti g.inputs _ _ (fun i _ => hw i)
      cases hv1 : v1 <;> cases hv2 : v2
      · have hw' := append_singleton_getD_mono w1 w2 false false hlen hw (le_refl false)
        rcases ih (w1 ++ [false]) (w2 ++ [false]) hgsfit (by simp [hlen]) hw' with hlt | ⟨heq, hle⟩
        · left; simpa using hlt
        · right; exact ⟨by simpa using heq, hle⟩
      · rw [hv1, hv2] at hvanti
        exact absurd hvanti not_true_le_false
      · left
        have hlt2 := evalNotCode_lt gs (w2 ++ [false])
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        omega
      · have hw' := append_singleton_getD_mono w1 w2 true true hlen hw (le_refl true)
        rcases ih (w1 ++ [true]) (w2 ++ [true]) hgsfit (by simp [hlen]) hw' with hlt | ⟨heq, hle⟩
        · left; simp only [↓reduceIte]; omega
        · right; exact ⟨by simp only [↓reduceIte, heq], hle⟩

abbrev F (A : Type) := A → Bool
def rd {A} (w : List (F A)) (i : Nat) : F A := w.getD i (fun _ => false)
def gate {A} (w : List (F A)) (g : Gate) : F A :=
  fun x => g.op.eval (g.inputs.map fun i => rd w i x)
def run {A} : List Gate → List (F A) → List (F A)
  | [], w => w
  | g :: gs, w => run gs (w ++ [gate w g])
noncomputable def cost {A} (p : Gate → Nat) : List Gate → List (F A) → Nat
  | [], _ => 0
  | g :: gs, w => (if gate w g ∈ w then 0 else p g) + cost p gs (w ++ [gate w g])
noncomputable def neg (g : Gate) : Nat := if g.op = .not then 1 else 0
def proj {A B} (h : B → A) (w : List (F A)) : List (F B) := w.map (fun f => f ∘ h)
def vals {A} (w : List (F A)) (x : A) := w.map (fun f => f x)

lemma rd_map {A B : Type} (f : A → B) (w : List A) (i : Nat) (d : A) :
    (w.map f).getD i (f d) = f (w.getD i d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

lemma rd_proj {A B} (h : B → A) (w : List (F A)) (i : Nat) : rd (proj h w) i = rd w i ∘ h := by
  exact rd_map (fun f : F A => f ∘ h) w i (fun _ => false)

lemma gate_proj {A B} (h : B → A) (w : List (F A)) (g : Gate) :
    gate (proj h w) g = gate w g ∘ h := by
  funext x
  simp [gate, rd_proj]

lemma proj_ext {A B} (h : B → A) (w : List (F A)) (g : Gate) :
    proj h (w ++ [gate w g]) = proj h w ++ [gate (proj h w) g] := by
  rw [gate_proj]
  simp [proj]

lemma rd_vals {A} (w : List (F A)) (x : A) (i : Nat) :
    (vals w x).getD i false = rd w i x := rd_map (fun f : F A => f x) w i (fun _ => false)

lemma run_vals {A} (gs : List Gate) (w : List (F A)) (x : A) :
    vals (run gs w) x = wiresFrom gs (vals w x) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run, ih, wiresFrom_cons]
    simp [vals, gate, ← rd_vals]

lemma cost_proj {A B} (h : B → A) (p : Gate → Nat) (gs : List Gate) (w : List (F A)) :
    cost p gs (proj h w) ≤ cost p gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [cost, ← proj_ext]
    apply Nat.add_le_add _ (ih _)
    by_cases hv : gate w g ∈ w
    · have hs : gate (proj h w) g ∈ proj h w := by
        rw [gate_proj]; exact List.mem_map_of_mem hv
      simp [hv, hs]
    · simp only [hv, ite_false]; split <;> omega

lemma cost_len {A} (gs : List Gate) (w : List (F A)) : cost (fun _ => 1) gs w ≤ gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have := ih (w ++ [gate w g])
    simp only [cost, List.length_cons]; split <;> omega

lemma neg_cons (g : Gate) (gs : List Gate) :
    notCount ⟨g :: gs,0⟩ = neg g + notCount ⟨gs,0⟩ := by
  by_cases h : g.op = .not <;> simp [notCount, neg, h, Nat.add_comm]

lemma cost_neg {A} (gs : List Gate) (w : List (F A)) : cost neg gs w ≤ notCount ⟨gs,0⟩ := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [cost, neg_cons]
    have := ih (w ++ [gate w g]); split <;> omega

lemma code_tail (g : Gate) (gs : List Gate) (w : List Bool) :
    evalNotCode gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ≤ evalNotCode (g :: gs) w := by
  cases g with | mk op ins =>
    cases op <;> simp [evalNotCode]

lemma cost_quota {A} (s : Nat) (gs : List Gate) (w : List (F A)) (hz : (fun _ => false) ∈ w)
    (h : ∀ x, evalNotCode gs (vals w x) < 2^s) : cost neg gs w ≤ s := by
  induction gs generalizing w with
  | nil => exact Nat.zero_le _
  | cons g gs ih =>
    let w' := w ++ [gate w g]
    have he (x : A) : vals w' x = vals w x ++ [g.op.eval (g.inputs.map fun i => (vals w x).getD i false)] := by
      simp [vals, w', gate, ← rd_vals]
    have tail := ih w' (List.mem_append_left _ hz) (fun x => (he x) ▸ lt_of_le_of_lt (code_tail g gs _) (h x))
    rw [cost]
    by_cases hn : g.op = .not
    · by_cases hc : notCount ⟨gs,0⟩ < s
      · have := cost_neg gs w'
        change (if gate w g ∈ w then 0 else neg g) + cost neg gs w' ≤ s
        simp only [neg, hn, ite_true]; split <;> omega
      · have hh : gate w g = fun _ => false := by
          funext x
          cases hx : gate w g x with
          | false => rfl
          | true =>
            have hi := h x
            have eq : g.op.eval (g.inputs.map fun i => (vals w x).getD i false) = true := by
              simpa only [gate, rd_vals] using hx
            simp only [evalNotCode, hn] at hi
            rw [hn] at eq
            simp only [eq, ite_true] at hi
            have pw : 2^s ≤ 2^(notCount ⟨gs,0⟩) := Nat.pow_le_pow_right (by decide) (by omega)
            omega
        simpa only [ite_eq_left (hh ▸ hz), Nat.zero_add] using tail
    · simp only [neg, hn, ite_false, ite_self, Nat.zero_add]
      exact tail

def simple {A} (h : A → A) (v f : F A) : Prop := f ∘ h = f ∨ f = v

lemma mp_mem {A B} {w : List (F A)} {f : F A} (h : B → A) (m : f ∈ w) :
    f ∘ h ∈ proj h w := List.mem_map_of_mem m

lemma rd_mem' {A} (w : List (F A)) (hz : (fun _ => false) ∈ w) (i : Nat) : rd w i ∈ w := by
  by_cases hi : i < w.length
  · exact getD_mem _ _ _ hi
  · unfold rd; rw [getD_ge_length _ _ _ (by omega)]; exact hz

def bop (k : Bool) (a b : Bool) := if k then a && b else a || b

lemma pair_case {A} (h : A → A) (v : F A) (hv : ∀ x, v (h x) = true)
    (w : List (F A)) (ht : (fun _ => true) ∈ w) (k : Bool)
    (f d : F A) (hf : f ∈ w) (hd : d ∈ w) (sf : simple h v f) (sd : simple h v d) :
    simple h v (fun x => bop k (f x) (d x)) ∨
      (fun x => bop k (f (h x)) (d (h x))) ∈ proj h w := by
  rcases sf with sf | rfl
  · rcases sd with sd | rfl
    · left; left; funext x
      change bop k (f (h x)) (d (h x)) = _
      rw [show f (h x) = f x from congrFun sf x, show d (h x) = d x from congrFun sd x]
    · right
      cases k
      · simpa [bop,hv,Function.comp_def] using mp_mem h ht
      · simpa [bop,hv,Function.comp_def] using mp_mem h hf
  · right
    cases k
    · simpa [bop,hv,Function.comp_def] using mp_mem h ht
    · simpa [bop,hv,Function.comp_def] using mp_mem h hd

lemma gate_case {A} (h : A → A) (v : F A) (hv : ∀ x, v (h x) = true)
    (w : List (F A)) (hz : (fun _ => false) ∈ w) (ht : (fun _ => true) ∈ w)
    (hw : ∀ f ∈ w, simple h v f) (g : Gate) (hg : FanInTwo ⟨[g],0⟩) :
    simple h v (gate w g) ∨ gate w g ∘ h ∈ proj h w := by
  obtain ⟨o,ins⟩ := g
  obtain ⟨ho, hl⟩ := hg ⟨o,ins⟩ (by simp)
  change (o = .and ∨ o = .or ∨ o = .not) at ho
  change ins.length ≤ 2 at hl
  have mem := rd_mem' w hz
  have one (i : Nat) := hw _ (mem i)
  rcases ho with rfl | rfl | rfl
  · match ins with
    | [] => exact Or.inl (Or.inl rfl)
    | [i] =>
      left
      convert one i using 1
      funext x; simp [gate,GateOp.eval]
    | [i,j] =>
      have e : gate w ⟨.and,[i,j]⟩ = fun x => bop true (rd w i x) (rd w j x) := by
        funext x; simp [gate,GateOp.eval,bop]
      rw [e]
      exact pair_case h v hv w ht true (rd w i) (rd w j) (mem i) (mem j) (one i) (one j)
    | a::b::c::ds => simp at hl
  · match ins with
    | [] => exact Or.inl (Or.inl rfl)
    | [i] =>
      left
      convert one i using 1
      funext x; simp [gate,GateOp.eval]
    | [i,j] =>
      have e : gate w ⟨.or,[i,j]⟩ = fun x => bop false (rd w i x) (rd w j x) := by
        funext x; simp [gate,GateOp.eval,bop]
      rw [e]
      exact pair_case h v hv w ht false (rd w i) (rd w j) (mem i) (mem j) (one i) (one j)
    | a::b::c::ds => simp at hl
  · cases ins with
    | nil => exact Or.inl (Or.inl rfl)
    | cons i rest =>
      rcases one i with s | s
      · left; left; funext x
        change (!(rd w i (h x))) = (!(rd w i x))
        rw [show rd w i (h x) = rd w i x from congrFun s x]
      · right
        simpa [gate,GateOp.eval,Function.comp_def,s,hv] using mp_mem h hz

lemma strict_cost {A} (h : A → A) (v : F A) (hv : ∀ x, v (h x) = true)
    (gs : List Gate) (w : List (F A)) (hz : (fun _ => false) ∈ w) (ht : (fun _ => true) ∈ w)
    (hw : ∀ f ∈ w, simple h v f) (hg : FanInTwo ⟨gs,0⟩)
    (bad : ∃ f ∈ run gs w, ¬ simple h v f) :
    cost (fun _ => 1) gs (proj h w) < cost (fun _ => 1) gs w := by
  induction gs generalizing w with
  | nil => obtain ⟨f, hm, hn⟩ := bad; exact (hn (hw f hm)).elim
  | cons g gs ih =>
    have hs : FanInTwo ⟨[g],0⟩ := by
      intro q hq; simp at hq; subst q; exact hg _ List.mem_cons_self
    have htgs : FanInTwo ⟨gs,0⟩ := fun q hq => hg q (List.mem_cons_of_mem _ hq)
    simp only [cost, ← proj_ext]
    by_cases hd : simple h v (gate w g)
    · have st := ih (w ++ [gate w g]) (List.mem_append_left _ hz) (List.mem_append_left _ ht) (by
        intro f hf; simp only [List.mem_append,List.mem_singleton] at hf
        rcases hf with hf | rfl
        · exact hw f hf
        · exact hd) htgs bad
      by_cases hm : gate w g ∈ w
      · have hm' : gate (proj h w) g ∈ proj h w := gate_proj h w g ▸ mp_mem h hm
        simpa only [ite_eq_left hm,ite_eq_left hm',Nat.zero_add] using st
      · simp only [hm, ite_false]; split <;> omega
    · have hm : gate w g ∉ w := fun hm => hd (hw _ hm)
      have hm' : gate (proj h w) g ∈ proj h w :=
        gate_proj h w g ▸ (gate_case h v hv w hz ht hw g hs).resolve_left hd
      have st := cost_proj h (fun _ => 1) gs (w ++ [gate w g])
      simp only [ite_eq_right hm,ite_eq_left hm',Nat.zero_add]
      omega

lemma run_add {A} (gs ds : List Gate) (w : List (F A)) : run (gs ++ ds) w = run ds (run gs w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => exact ih _
lemma run_length {A} (gs : List Gate) (w : List (F A)) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih => rw [run, ih]; simp; omega

def Avail {A} (b : List (F A)) (gs : List Gate) (f : F A) : Prop :=
  ∃ i < b.length + gs.length, rd (run gs b) i = f
def Well (n : Nat) (ds : List Gate) := FanInTwo ⟨ds,0⟩ ∧ ReadsBack n ⟨ds,0⟩

lemma avail_old {A} {b : List (F A)} {gs : List Gate} (g : Gate) {f : F A}
    (h : Avail b gs f) : Avail b (gs ++ [g]) f := by
  obtain ⟨i, hi, eq⟩ := h
  refine ⟨i,by simp; omega,?_⟩
  rw [run_add]; change (run gs b ++ [_]).getD i _ = f
  rw [getD_append_left _ _ _ _ (by rwa [run_length])]
  exact eq

lemma compile {A} (b : List (F A)) (gs : List Gate) (w : List (F A)) (pre : List Gate)
    (hz : (fun _ => false) ∈ w) (hg : FanInTwo ⟨gs,0⟩) (hp : Well b.length pre)
    (hw : ∀ f ∈ w, Avail b pre f) :
    ∃ ds, Well b.length ds ∧ ds.length = pre.length + cost (fun _ => 1) gs w ∧
      notCount ⟨ds,0⟩ = notCount ⟨pre,0⟩ + cost neg gs w ∧ ∀ f ∈ run gs w, Avail b ds f := by
  induction gs generalizing w pre with
  | nil => exact ⟨pre,hp,by simp [cost],by simp [cost],hw⟩
  | cons g gs ih =>
    let w' := w ++ [gate w g]
    have hgs : FanInTwo ⟨gs,0⟩ := fun q hq => hg q (List.mem_cons_of_mem _ hq)
    have hz' : (fun _ => false) ∈ w' := List.mem_append_left _ hz
    by_cases hv : gate w g ∈ w
    · obtain ⟨ds,hp',hl,hn,hw'⟩ := ih w' pre hz' hgs hp (by
        intro f hf
        rcases List.mem_append.mp hf with m | m
        · exact hw f m
        · rw [List.mem_singleton.mp m]; exact hw _ hv)
      exact ⟨ds,hp',by simpa [cost,hv,w'] using hl,by simpa [cost,hv,w'] using hn,hw'⟩
    · have mapex (i : Nat) := hw _ (rd_mem' w hz i)
      choose phi bound eq using mapex
      let q : Gate := ⟨g.op,g.inputs.map phi⟩
      have qleg : FanInTwo ⟨[q],0⟩ := by
        intro a ha; have e : a = q := List.mem_singleton.mp ha
        rw [e]; have H := hg g List.mem_cons_self
        exact ⟨H.1,by simpa [q] using H.2⟩
      have qback : ReadsBack (b.length + pre.length) ⟨[q],0⟩ := by
        intro j hj i hi
        have hj0 : j = 0 := by change j < 1 at hj; omega
        subst j
        change i ∈ g.inputs.map phi at hi
        obtain ⟨u,_,rfl⟩ := List.mem_map.mp hi
        simpa using bound u
      have qwell : Well b.length (pre ++ [q]) :=
        ⟨fanInTwo_append hp.1 qleg,readsBack_append hp.2 qback⟩
      have qvalue : gate (run pre b) q = gate w g := by
        funext x
        simp [q,gate,List.map_map,Function.comp_def,eq]
      have live : Avail b (pre ++ [q]) (gate w g) := by
        refine ⟨b.length + pre.length,by simp,?_⟩
        rw [run_add]
        change (run pre b ++ [_]).getD (b.length + pre.length) _ = gate w g
        rw [getD_append_right _ _ _ _ (by rw [run_length]),run_length,Nat.sub_self]
        exact qvalue
      obtain ⟨ds,hp',hl,hn,hw'⟩ := ih w' (pre ++ [q]) hz' hgs qwell (by
        intro f hf
        rcases List.mem_append.mp hf with m | m
        · exact avail_old q (hw _ m)
        · rwa [List.mem_singleton.mp m])
      have qn : notCount ⟨[q],0⟩ = neg g := by
        rw [neg_cons]; simp [q,neg,notCount]
      refine ⟨ds,hp',?_,?_,hw'⟩
      · simpa [cost,hv,w',Nat.add_assoc] using hl
      · rw [notCount_append,qn] at hn
        simpa [cost,hv,w',Nat.add_assoc] using hn

abbrev Mask (n : Nat) := Finset (Fin n)
abbrev Dom (n m : Nat) := Mask n × Mask m
noncomputable def bits {n} (x : Mask n) := List.ofFn (fun i : Fin n => decide (i ∈ x))
noncomputable def preSet (m k : Nat) : Mask m := Finset.univ.filter (fun i => i.val < k)
noncomputable def digit {n} (i : Fin n) : F (Mask n) := fun x => decide (i ∈ x)
noncomputable def pad {n m} (k : Nat) (i : Fin m) : F (Dom n m) := fun a => decide (i.val < k ∨ i ∈ a.2)
def constants (A : Type) : List (F A) := [fun _ => false, fun _ => true]
noncomputable def ws (n m k : Nat) : List (F (Dom n m)) :=
  (List.ofFn fun i : Fin n => digit i ∘ Prod.fst) ++ (List.ofFn fun i : Fin m => pad k i) ++ constants _
noncomputable def bs (n : Nat) : List (F (Mask n)) := List.ofFn digit ++ constants _
noncomputable def full (n m : Nat) : List (F (Mask n)) :=
  (List.ofFn digit) ++ (List.replicate m (fun _ => true)) ++ constants _
def pin {n m} (j : Fin m) (a : Dom n m) : Dom n m := (a.1,insert j a.2)
noncomputable def bitJ {n m} (j : Fin m) : F (Dom n m) := fun a => decide (j ∈ a.2)
noncomputable def input {n m} (x : Mask n) (z : Mask m) := bits x ++ bits z ++ [false,true]
noncomputable def atTop {n} (m : Nat) (x : Mask n) : Dom n m := (x,Finset.univ)

lemma inc_pad {n m} (j i : Fin m) :
    @pad n m j.val i ∘ pin j = pad (j.val + 1) i := by
  funext a
  have eq : (i.val < j.val ∨ i ∈ insert j a.2) ↔ (i.val < j.val+1 ∨ i ∈ a.2) := by
    by_cases e : i = j
    · subst i; simp
    · have v : i.val ≠ j.val := fun h => e (Fin.ext h)
      have lt : (i.val < j.val+1) ↔ (i.val < j.val) := by omega
      simp [Finset.mem_insert,e,lt]
  change decide (i.val < j.val ∨ i ∈ insert j a.2) = decide (i.val < j.val+1 ∨ i ∈ a.2)
  exact decide_eq_decide.mpr eq

lemma inc_ws (n m : Nat) (j : Fin m) :
    proj (pin j) (ws n m j.val) = ws n m (j.val + 1) := by
  simp only [ws,proj,List.map_append,List.map_ofFn,Function.comp_def,constants,List.map_cons,List.map_nil]
  congr 2
  exact congrArg List.ofFn (funext fun i => inc_pad j i)

lemma top_ws (n m k : Nat) : proj (atTop m) (ws n m k) = full n m := by
  simp [ws,proj,atTop,digit,pad,full,constants,List.map_ofFn,Function.comp_def,List.ofFn_const]
  rfl

lemma simple_in {n m} (j : Fin m) (f) (hf : f ∈ ws n m j.val) :
    simple (pin j) (bitJ j) f := by
  simp only [ws, List.mem_append,List.mem_ofFn,constants,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with (⟨i,rfl⟩ | ⟨i,rfl⟩) | rfl | rfl
  · exact Or.inl rfl
  · by_cases e : i = j
    · subst i; right; funext a; simp [pad,bitJ]
    · left; funext a; simp [pad,pin,e]
  · exact Or.inl rfl
  · exact Or.inl rfl

lemma vals_ws {n m} (k : Nat) (a : Dom n m) :
    vals (ws n m k) a = input a.1 (preSet m k ∪ a.2) := by
  simp [ws,vals,input,bits,digit,pad,preSet,constants,List.map_ofFn,Function.comp_def]
lemma vals_bs {n} (x : Mask n) : vals (bs n) x = bits x ++ [false,true] := by
  simp [bs,bits,vals,digit,constants,List.map_ofFn,Function.comp_def]
lemma vals_full {n} (m : Nat) (x : Mask n) : vals (full n m) x = input x (Finset.univ : Mask m) := by
  simp [full,bits,input,vals,digit,constants,List.map_ofFn,List.ofFn_const,Function.comp_def]
lemma pre_mem {m k} (i : Fin m) : i ∈ preSet m k ↔ i.val < k := by simp [preSet]
lemma pre_sub {m a b : Nat} (h : a ≤ b) : preSet m a ⊆ preSet m b := by
  intro i hi; exact (pre_mem i).2 (lt_of_lt_of_le ((pre_mem i).1 hi) h)
lemma pre_succ {m} (j : Fin m) : insert j (preSet m j.val) = preSet m (j.val+1) := by
  ext i; simp only [Finset.mem_insert,pre_mem,Fin.ext_iff]; omega
lemma read_run {A} (C : Circuit) (w : List (F A)) (a : A) :
    rd (run C.gates w) C.output a = C.eval (vals w a) := by
  rw [← rd_vals,run_vals]; rfl
lemma mem_run {A} (gs : List Gate) (w : List (F A)) {f} (hf : f ∈ w) : f ∈ run gs w := by
  induction gs generalizing w with
  | nil => exact hf
  | cons g gs ih => exact ih _ (List.mem_append_left _ hf)

def Alternates {n m : Nat} (C : Circuit) : Prop := ∀ (x : Mask n) (z : Mask m) (j : Fin m),
  (∀ i : Fin m, i < j → i ∈ z) → j ∉ z → C.eval (input x z) = decide (j.val % 2 = 0)

lemma parity_step (j : Nat) : decide (j % 2 = 0) ≠ decide ((j+1)%2 = 0) := by
  by_cases he : j%2 = 0
  · have ho : (j+1)%2 ≠ 0 := by omega
    simp [he,ho]
  · have ho : (j+1)%2 = 0 := by omega
    simp [he,ho]

lemma alt_pre {n m} {C : Circuit} (h : @Alternates n m C) (x : Mask n) (k : Nat) (hk : k < m) :
    C.eval (input x (preSet m k)) = decide (k%2=0) :=
  h x _ ⟨k,hk⟩ (fun i hi => (pre_mem i).2 hi) (by simp [pre_mem])

lemma scalar_bad {n m} {C : Circuit} (h : @Alternates n m C) (even : m%2 = 0)
    (j : Fin m) (hj : j.val < m-1) :
    ¬simple (pin j) (bitJ j) (rd (run C.gates (ws n m j.val)) C.output) := by
  let f := rd (run C.gates (ws n m j.val)) C.output
  have ep (k : Nat) (hjk : j.val ≤ k) (hk : k < m) :
      f (∅,preSet m k) = decide (k%2=0) := by
    rw [show f (∅,preSet m k) = C.eval (input (∅ : Mask n) (preSet m j.val ∪ preSet m k)) by
          dsimp only [f]; rw [read_run,vals_ws],Finset.union_eq_right.mpr (pre_sub hjk)]
    exact alt_pre h _ k hk
  rintro (hf | hf)
  · have e := congrFun hf (∅,preSet m j.val)
    change f (∅,insert j (preSet m j.val)) = f (∅,preSet m j.val) at e
    rw [pre_succ j,ep _ (by omega) (by omega),ep _ (by omega) j.isLt] at e
    exact parity_step j.val e.symm
  · have e := congrFun hf (∅,preSet m (m-1))
    change f (∅,preSet m (m-1)) = decide (j ∈ preSet m (m-1)) at e
    rw [ep _ (by omega) (by omega)] at e
    have odd : (m-1)%2 ≠ 0 := by omega
    simp [odd,(pre_mem j).2 hj] at e

lemma saving {n m} {C : Circuit} (fit : FanInTwo C) (h : @Alternates n m C) (even : m%2=0) :
    cost (fun _ => 1) C.gates (full n m) + (m-1) ≤ C.size := by
  have chain (k : Nat) (hk : k ≤ m-1) :
      cost (fun _ => 1) C.gates (ws n m k) + k ≤ C.size := by
    induction k with
    | zero => exact Nat.add_zero _ ▸ cost_len C.gates _
    | succ k ih =>
      have prev := ih (by omega)
      let j : Fin m := ⟨k,by omega⟩
      have z : (fun _ => false) ∈ ws n m k := by simp [ws,constants]
      have t : (fun _ => true) ∈ ws n m k := by simp [ws,constants]
      have v : ∀ a : Dom n m, bitJ j (pin j a) = true := by simp [bitJ,pin]
      have sc := strict_cost (pin j) (bitJ j) v C.gates (ws n m k) z t (simple_in j) fit
        ⟨_,rd_mem' _ (mem_run _ _ z) _,scalar_bad h even j (by change k < m-1; omega)⟩
      rw [show ws n m k = ws n m j.val from rfl,inc_ws] at sc
      change cost _ _ (ws n m (k+1)) < cost _ _ (ws n m k) at sc
      omega
  have hc := cost_proj (@atTop n m) (fun _ => 1) C.gates (ws n m (m-1))
  rw [top_ws] at hc
  exact le_trans (Nat.add_le_add_right hc _) (chain _ le_rfl)

lemma input_as {n m} (x : Mask n) (u : Mask m) : input x u = bits x ++ inpVec u := by
  simp [input,bits,inpVec,List.append_assoc]

lemma input_ord {n m} (x : Mask n) {u v : Mask m} (huv : u ⊆ v) (i : Nat) :
    (input x u).getD i false ≤ (input x v).getD i false := by
  rw [input_as,input_as]
  by_cases hi : i < (bits x).length
  · rw [getD_append_left _ _ _ _ hi,getD_append_left _ _ _ _ hi]
  · rw [getD_append_right _ _ _ _ (by omega),getD_append_right _ _ _ _ (by omega)]
    exact inpVec_mono huv _

lemma chain_code {n m d} {C : Circuit} (hm : m = 2*d) (fit : FanInTwo C) (h : @Alternates n m C)
    (x : Mask n) : d + evalNotCode C.gates (input x (Finset.univ : Mask m)) <
      2 ^ notCount C := by
  let r := fun z : Mask m => evalNotCode C.gates (input x z)
  have dich {u v : Mask m} (huv : u ⊆ v) :
      r v < r u ∨ (r v = r u ∧ C.eval (input x u) ≤ C.eval (input x v)) := by
    have he := evalNotCode_dichotomy C.gates (input x u) (input x v) fit
      (by simp [input,bits]) (input_ord x huv)
    rcases he with he | ⟨he,hw⟩
    · exact Or.inl he
    · exact Or.inr ⟨he,hw C.output⟩
  have mono {u v : Mask m} (huv : u ⊆ v) : r v ≤ r u :=
    (dich huv).elim Nat.le_of_lt (fun hh => Nat.le_of_eq hh.1)
  have cum (k : Nat) (hk : k ≤ d) : k + r (preSet m (2*k)) ≤ r (preSet m 0) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have prev := ih (by omega)
      have fall : r (preSet m (2*k+1)) < r (preSet m (2*k)) := by
        rcases dich (pre_sub (m := m) (a := 2*k) (b := 2*k+1) (by omega)) with hh | hh
        · exact hh
        · have a := hh.2
          rw [alt_pre h x _ (by omega),alt_pre h x _ (by omega)] at a
          have e0 : (2*k)%2=0 := by omega
          simp [e0] at a
          exact (not_true_le_false a).elim
      have rest := mono (pre_sub (m := m) (a := 2*k+1) (b := 2*(k+1)) (by omega))
      omega
  have e : preSet m (2*d) = Finset.univ := by
    ext i; simp only [pre_mem,Finset.mem_univ,iff_true]; omega
  have H := cum d le_rfl
  rw [e] at H
  exact lt_of_le_of_lt H (evalNotCode_lt _ _)

lemma power_gap {s b k : Nat} (sb : s < b) (h : 2^b - 2^s < 2^k) : b ≤ k := by
  by_contra! bad
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show b ≠ 0 by omega)
  have hs : 2^s ≤ 2^u := Nat.pow_le_pow_right (by decide) (by omega)
  have hk : 2^k ≤ 2^u := Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ] at h
  omega

lemma full_avail {n m} (f : F (Mask n)) (hf : f ∈ full n m) : Avail (bs n) [] f := by
  have mem : f ∈ bs n := by
    simp only [full,List.mem_append,List.mem_replicate] at hf
    rcases hf with (hf | ⟨_,rfl⟩) | hf
    · exact List.mem_append_left _ hf
    · simp [bs,constants]
    · exact List.mem_append_right _ hf
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp mem
  exact ⟨i,by simpa using hi,by simpa [rd,run,List.getD_eq_getElem?_getD,hi] using e⟩

lemma solve {n t s b : Nat} (sb : s < b) (m : Nat) (hm : m = 2*(2^b-2^s))
    (R : Mask n → Bool → (Fin t → Bool) → Prop) (C : Circuit) (fit : FanInTwo C)
    (p : Fin t → Nat) (alt : @Alternates n m C)
    (good : ∀ x : Mask n, let xs := input x (Finset.univ : Mask m)
      R x (C.eval xs) (fun i => (C.wires xs).getD (p i) false)) :
    b ≤ notCount C ∧ ∃ D : Circuit, (FanInTwo D ∧ ReadsBack (n+2) D ∧ D.output < n+2+D.size) ∧
      (∃ p' : Fin t → Fin (n+2+D.size), ∀ x : Mask n, let xs := bits x ++ [false,true]
        R x (D.eval xs) (fun i => (D.wires xs).getD (p' i).val false)) ∧
      D.size + (m-1) ≤ C.size ∧ notCount D ≤ notCount C ∧ (notCount C = b → notCount D ≤ s) := by
  have bound := chain_code hm fit alt
  have kbound : b ≤ notCount C := power_gap sb (by have := bound ∅; omega)
  have costS := saving fit alt (by omega)
  have z : (fun _ => false) ∈ full n m := by simp [full,constants]
  obtain ⟨ds,ok,sz,nc,live⟩ := compile (bs n) C.gates (full n m) [] z fit
    ⟨fanInTwo_nil _,readsBack_nil _ _⟩ full_avail
  have s0 : ds.length = cost (fun _ => 1) C.gates (full n m) := by simpa using sz
  have n0 : notCount ⟨ds,0⟩ = cost neg C.gates (full n m) := by simpa [notCount_nil] using nc
  have lw : (bs n).length = n+2 := by simp [bs,constants]
  have transfer (i : Nat) : ∃ a : Fin (n+2+ds.length), ∀ x : Mask n,
      (wiresFrom ds (bits x ++ [false,true])).getD a.val false =
      (C.wires (input x (Finset.univ : Mask m))).getD i false := by
    obtain ⟨j,hj,hf⟩ := live _ (rd_mem' _ (mem_run _ _ z) i)
    refine ⟨⟨j,by rwa [lw] at hj⟩,fun x => ?_⟩
    have e := congrFun hf x
    simpa only [← rd_vals,run_vals,vals_bs,vals_full,Circuit.wires,wiresFrom] using e
  choose w he using transfer
  let D : Circuit := ⟨ds,(w C.output).val⟩
  refine ⟨kbound,D,⟨ok.1,?_,(w C.output).isLt⟩,⟨fun i => w (p i),?_⟩,?_,?_,?_⟩
  · rw [←lw]; exact ok.2
  · intro x
    change R x ((wiresFrom ds (bits x ++ [false,true])).getD (w C.output).val false)
      (fun i => (wiresFrom ds (bits x ++ [false,true])).getD (w (p i)).val false)
    simp only [he]
    exact good x
  · change ds.length + _ ≤ _; rwa [s0]
  · change notCount ⟨ds,0⟩ ≤ _; rw [n0]; exact cost_neg _ _
  · intro quota
    change notCount ⟨ds,0⟩ ≤ _; rw [n0]
    apply cost_quota _ _ _ z
    intro x; rw [vals_full]
    have hx := bound x; rw [quota] at hx
    have hs : 2^s ≤ 2^b := Nat.pow_le_pow_right (by decide) (by omega)
    omega

end PEqualNP.Outside.L_lib_1284_aux

open PEqualNP.Outside.L_lib_1284_aux in
theorem PEqualNP.Outside.L_lib_1284 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n t s b : Nat), s < b →
  let m := 2*(2^b-2^s)
  let bits := fun (w : Nat) (x : Finset (Fin w)) => List.ofFn (fun i : Fin w => decide (i ∈ x))
  let valid := fun (w : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (w+2) C ∧
      C.output < w+2+C.size
  ∀ R : Finset (Fin n) → Bool → (Fin t → Bool) → Prop,
  let outputs := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (xs : List Bool) (p : Fin t → Nat) =>
    fun i => (C.wires xs).getD (p i) false
  let source := fun (D : PEqualNP.CircuitLowerBounds.Circuit) => valid n D ∧
    ∃ p : Fin t → Fin (n+2+D.size), ∀ x, let xs := bits n x ++ [false,true]
      R x (D.eval xs) (outputs D xs (fun i => (p i).val))
  ∀ C, valid (n+m) C →
    (∃ p : Fin t → Fin (n+m+2+C.size), ∀ x (z : Finset (Fin m)),
      let xs := bits n x ++ bits m z ++ [false,true]
      (z = Finset.univ → R x (C.eval xs) (outputs C xs (fun i => (p i).val))) ∧
      ∀ j : Fin m, (∀ i : Fin m, i < j → i ∈ z) → j ∉ z → C.eval xs = decide (j.val % 2 = 0)) →
    b ≤ PEqualNP.NotBracket.notCount C ∧
    ∃ D, source D ∧ D.size + (m-1) ≤ C.size ∧
      PEqualNP.NotBracket.notCount D ≤ PEqualNP.NotBracket.notCount C ∧
      (PEqualNP.NotBracket.notCount C = b → PEqualNP.NotBracket.notCount D ≤ s)) := by
  classical
  intro n t s b sb
  dsimp only
  intro R C hC hp
  have db (w : Nat) (u : Finset (Fin w)) :
      (List.ofFn fun i : Fin w => @decide (i ∈ u) (Classical.propDecidable _)) = bits u := by
    unfold bits
    apply congrArg List.ofFn
    funext i
    exact decide_eq_decide.mpr Iff.rfl
  simp only [db] at hp ⊢
  obtain ⟨p,hp⟩ := hp
  let m := 2*(2^b-2^s)
  have ha : @Alternates n m C := by
    intro x z j hj hz
    have ep := (hp x z).2 j hj hz
    exact ep.trans (decide_eq_decide.mpr Iff.rfl)
  have hb (x : Mask n) := (hp x (Finset.univ : Mask m)).1 rfl
  obtain ⟨lb,D,vd,⟨q,hq⟩,hs,hn,he⟩ :=
    solve sb m rfl R C hC.1 (fun i => (p i).val) ha hb
  exact ⟨lb,D,⟨vd,⟨q,hq⟩⟩,hs,hn,he⟩
