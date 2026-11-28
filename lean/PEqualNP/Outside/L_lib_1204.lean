import PEqualNP.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside.L_lib_1204_aux

open PEqualNP.CircuitLowerBounds

-- Part 0. Wires of a gate list on the input x followed by the constants false and true.

theorem wires_snoc (gs : List Gate) (g : Gate) (X : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires X = (Circuit.mk gs 0).wires X ++
      [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires X).getD i false)] := by
  simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem wires_length (gs : List Gate) (X : List Bool) :
    ((Circuit.mk gs 0).wires X).length = X.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    have h1 := congrArg List.length (wires_snoc gs g X)
    simp only [List.length_append, List.length_singleton] at h1 ⊢
    omega

def W (k : ℕ) (gs : List Gate) (x : Fin k → Bool) (w : ℕ) : Bool :=
  ((Circuit.mk gs 0).wires (List.ofFn x ++ [false, true])).getD w false

theorem W_len (k : ℕ) (gs : List Gate) (x : Fin k → Bool) :
    ((Circuit.mk gs 0).wires (List.ofFn x ++ [false, true])).length = k + 2 + gs.length := by
  rw [wires_length, List.length_append, List.length_ofFn]
  rfl

theorem W_snoc (k : ℕ) (gs : List Gate) (g : Gate) (x : Fin k → Bool) (w : ℕ) :
    W k (gs ++ [g]) x w = if w < k + 2 + gs.length then W k gs x w
      else if w = k + 2 + gs.length then g.op.eval (g.inputs.map (W k gs x)) else false := by
  have hl := W_len k gs x
  unfold W
  rw [wires_snoc]
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ (by omega)
  · subst h2
    rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
    rfl
  · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega)]

theorem W_prefix (k : ℕ) (gs : List Gate) (x : Fin k → Bool) (w : ℕ)
    (hw : w < k + 2 + gs.length) : ∀ e : List Gate, W k (gs ++ e) x w = W k gs x w := by
  intro e
  induction e using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton e g ih =>
    rw [← List.append_assoc, W_snoc, if_pos (by simp only [List.length_append]; omega), ih]

theorem W_nil_lt (k : ℕ) (x : Fin k → Bool) (i : ℕ) (hi : i < k) : W k [] x i = x ⟨i, hi⟩ := by
  show (List.ofFn x ++ [false, true]).getD i false = x ⟨i, hi⟩
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]
  rfl

theorem W_nil_k (k : ℕ) (x : Fin k → Bool) : W k [] x k = false := by
  show (List.ofFn x ++ [false, true]).getD k false = false
  rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self]
  rfl

theorem W_nil_k1 (k : ℕ) (x : Fin k → Bool) : W k [] x (k + 1) = true := by
  show (List.ofFn x ++ [false, true]).getD (k + 1) false = true
  rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.add_sub_cancel_left]
  rfl

theorem W_nil_ge (k : ℕ) (x : Fin k → Bool) (w : ℕ) (hw : k + 2 ≤ w) : W k [] x w = false := by
  show (List.ofFn x ++ [false, true]).getD w false = false
  rw [List.getD_eq_default _ _ (by simp; omega)]

theorem W_base (k : ℕ) (gs : List Gate) (x : Fin k → Bool) (w : ℕ) (hw : w < k + 2) :
    W k gs x w = W k [] x w := by
  have h := W_prefix k [] x w (by simp; omega) gs
  rw [List.nil_append] at h
  exact h

theorem W_out (k : ℕ) (gs : List Gate) (x : Fin k → Bool) (w : ℕ) (hw : k + 2 + gs.length ≤ w) :
    W k gs x w = false := by
  unfold W
  rw [List.getD_eq_default _ _ (by rw [W_len]; omega)]

-- NOT counts of gate lists (notCount uses a local DecidableEq instance, which reduces on constructors).

theorem nc_nil : PEqualNP.NotBracket.notCount (Circuit.mk [] 0) = 0 := rfl

theorem nc_snoc_not (gs : List Gate) (ins : List ℕ) :
    PEqualNP.NotBracket.notCount (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) 0) =
      PEqualNP.NotBracket.notCount (Circuit.mk gs 0) + 1 := by
  unfold PEqualNP.NotBracket.notCount
  rw [List.filter_append, List.length_append]
  rfl

theorem nc_snoc_and (gs : List Gate) (ins : List ℕ) :
    PEqualNP.NotBracket.notCount (Circuit.mk (gs ++ [⟨GateOp.and, ins⟩]) 0) =
      PEqualNP.NotBracket.notCount (Circuit.mk gs 0) := by
  unfold PEqualNP.NotBracket.notCount
  rw [List.filter_append, List.length_append]
  rfl

theorem nc_snoc_or (gs : List Gate) (ins : List ℕ) :
    PEqualNP.NotBracket.notCount (Circuit.mk (gs ++ [⟨GateOp.or, ins⟩]) 0) =
      PEqualNP.NotBracket.notCount (Circuit.mk gs 0) := by
  unfold PEqualNP.NotBracket.notCount
  rw [List.filter_append, List.length_append]
  rfl

theorem nc_append (gs e : List Gate) :
    PEqualNP.NotBracket.notCount (Circuit.mk (gs ++ e) 0) =
      PEqualNP.NotBracket.notCount (Circuit.mk gs 0) + PEqualNP.NotBracket.notCount (Circuit.mk e 0) := by
  unfold PEqualNP.NotBracket.notCount
  rw [List.filter_append, List.length_append]

theorem eval_and2 (a b : Bool) : GateOp.eval GateOp.and [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.eval GateOp.or [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.eval GateOp.and [a] = a := by
  cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.eval GateOp.or [a] = a := by
  cases a <;> rfl

theorem eval_not_cons (a : Bool) (l : List Bool) : GateOp.eval GateOp.not (a :: l) = !a := rfl

-- Part 1. Necessity: block labels of the raw inputs, and monotone wires.

abbrev Dep {k : ℕ} (lab : Fin k → Fin k) (c : Fin k) (f : (Fin k → Bool) → Bool) : Prop :=
  ∀ x y : Fin k → Bool, (∀ i, lab i = c → x i = y i) → f x = f y

abbrev Mono {k : ℕ} (f : (Fin k → Bool) → Bool) : Prop :=
  ∀ x y : Fin k → Bool, (∀ i, x i = true → y i = true) → f x = true → f y = true

abbrev Lab {k : ℕ} (lab : Fin k → Fin k) (N : Finset (Fin k)) (f : (Fin k → Bool) → Bool) : Prop :=
  ∃ c, Dep lab c f ∧ (c ∉ N → Mono f)

abbrev GOK (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem lab_const {k : ℕ} (lab : Fin k → Fin k) (N : Finset (Fin k)) (c0 : Fin k)
    (f : (Fin k → Bool) → Bool) (hf : ∀ x y, f x = f y) : Lab lab N f :=
  ⟨c0, fun x y _ => hf x y, fun _ x y _ h => (hf y x).trans h⟩

theorem lab_insert {k : ℕ} (lab : Fin k → Fin k) (N : Finset (Fin k)) (c : Fin k)
    (f : (Fin k → Bool) → Bool) (h : Lab lab N f) : Lab lab (insert c N) f := by
  obtain ⟨c', hd, hm⟩ := h
  exact ⟨c', hd, fun hn => hm (fun hc => hn (Finset.mem_insert_of_mem hc))⟩

theorem lab_relab {k : ℕ} (lab : Fin k → Fin k) (N : Finset (Fin k)) (φ : Fin k → Fin k)
    (f : (Fin k → Bool) → Bool) (h : Lab lab N f) : Lab (fun i => φ (lab i)) (N.image φ) f := by
  obtain ⟨c, hd, hm⟩ := h
  refine ⟨φ c, fun x y hxy => hd x y (fun i hi => hxy i ?_), fun hn => hm (fun hc => hn ?_)⟩
  · show φ (lab i) = φ c
    rw [hi]
  · exact Finset.mem_image_of_mem φ hc

theorem lab_not {k : ℕ} (lab : Fin k → Fin k) (N : Finset (Fin k)) (c : Fin k)
    (f : (Fin k → Bool) → Bool) (hd : Dep lab c f) : Lab lab (insert c N) (fun x => !f x) :=
  ⟨c, fun x y hxy => congrArg (fun b => !b) (hd x y hxy),
    fun hn => absurd (Finset.mem_insert_self c N) hn⟩

def mrg {k : ℕ} (cu cv : Fin k) (c : Fin k) : Fin k := if c = cv then cu else c

theorem mrg_v {k : ℕ} (cu cv : Fin k) : mrg cu cv cv = cu := if_pos rfl

theorem mrg_u {k : ℕ} (cu cv : Fin k) : mrg cu cv cu = cu := by
  unfold mrg
  split_ifs <;> rfl

theorem hop_and : ∀ a b a' b' : Bool, (a = true → a' = true) → (b = true → b' = true) →
    (a && b) = true → (a' && b') = true := by decide

theorem hop_or : ∀ a b a' b' : Bool, (a = true → a' = true) → (b = true → b' = true) →
    (a || b) = true → (a' || b') = true := by decide

theorem lab_merge {k : ℕ} (lab : Fin k → Fin k) (N : Finset (Fin k)) (cu cv : Fin k)
    (f f' : (Fin k → Bool) → Bool) (hd : Dep lab cu f) (hm : cu ∉ N → Mono f)
    (hd' : Dep lab cv f') (hm' : cv ∉ N → Mono f') (op : Bool → Bool → Bool)
    (hop : ∀ a b a' b' : Bool, (a = true → a' = true) → (b = true → b' = true) →
      op a b = true → op a' b' = true) :
    Lab (fun i => mrg cu cv (lab i)) (N.image (mrg cu cv)) (fun x => op (f x) (f' x)) := by
  refine ⟨cu, fun x y hxy => ?_, fun hn => ?_⟩
  · have e1 : f x = f y := hd x y (fun i hi => hxy i (by
      show mrg cu cv (lab i) = cu
      rw [hi]
      exact mrg_u cu cv))
    have e2 : f' x = f' y := hd' x y (fun i hi => hxy i (by
      show mrg cu cv (lab i) = cu
      rw [hi]
      exact mrg_v cu cv))
    show op (f x) (f' x) = op (f y) (f' y)
    rw [e1, e2]
  · have hu : cu ∉ N := fun h => hn (Finset.mem_image.2 ⟨cu, h, mrg_u cu cv⟩)
    have hv : cv ∉ N := fun h => hn (Finset.mem_image.2 ⟨cv, h, mrg_v cu cv⟩)
    intro x y hxy h
    exact hop _ _ _ _ (hm hu x y hxy) (hm' hv x y hxy) h

theorem card_mrg {k : ℕ} (lab : Fin k → Fin k) (cu cv : Fin k) :
    (Finset.univ.image lab).card ≤ (Finset.univ.image (fun i => mrg cu cv (lab i))).card + 1 := by
  have hsub : Finset.univ.image lab ⊆ insert cv (Finset.univ.image (fun i => mrg cu cv (lab i))) := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hc
    by_cases h : lab i = cv
    · rw [h]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      refine Finset.mem_image.2 ⟨i, Finset.mem_univ _, ?_⟩
      show (if lab i = cv then cu else lab i) = lab i
      rw [if_neg h]
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

theorem step_all {k : ℕ} (gs : List Gate) (g : Gate) (lab : Fin k → Fin k) (N : Finset (Fin k))
    (c0 : Fin k) (hold : ∀ w, Lab lab N (fun x => W k gs x w)) (f : (Fin k → Bool) → Bool)
    (hf : ∀ x, g.op.eval (g.inputs.map (W k gs x)) = f x) (hnew : Lab lab N f) :
    ∀ w, Lab lab N (fun x => W k (gs ++ [g]) x w) := by
  intro w
  by_cases h1 : w < k + 2 + gs.length
  · have e : (fun x => W k (gs ++ [g]) x w) = (fun x => W k gs x w) := by
      funext x
      rw [W_snoc, if_pos h1]
    rw [e]
    exact hold w
  · by_cases h2 : w = k + 2 + gs.length
    · have e : (fun x => W k (gs ++ [g]) x w) = f := by
        funext x
        rw [W_snoc, if_neg h1, if_pos h2, hf x]
      rw [e]
      exact hnew
    · have e : (fun x => W k (gs ++ [g]) x w) = (fun _ => false) := by
        funext x
        rw [W_snoc, if_neg h1, if_neg h2]
      rw [e]
      exact lab_const lab N c0 _ (fun _ _ => rfl)

theorem inv {k : ℕ} (hk : 0 < k) : ∀ gs : List Gate, (∀ g ∈ gs, GOK g) →
    ∃ (lab : Fin k → Fin k) (N : Finset (Fin k)),
      k + PEqualNP.NotBracket.notCount (Circuit.mk gs 0) ≤ (Finset.univ.image lab).card + gs.length ∧
      N.card ≤ PEqualNP.NotBracket.notCount (Circuit.mk gs 0) ∧
      ∀ w, Lab lab N (fun x => W k gs x w) := by
  have c0 : Fin k := ⟨0, hk⟩
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨id, ∅, ?_, ?_, ?_⟩
    · simp [nc_nil, Finset.card_image_of_injective _ Function.injective_id]
    · simp [nc_nil]
    · intro w
      by_cases hw : w < k
      · refine ⟨⟨w, hw⟩, fun x y hxy => ?_, fun _ x y hxy h => ?_⟩
        · show W k [] x w = W k [] y w
          rw [W_nil_lt k x w hw, W_nil_lt k y w hw]
          exact hxy ⟨w, hw⟩ rfl
        · have h' : W k [] x w = true := h
          show W k [] y w = true
          rw [W_nil_lt k x w hw] at h'
          rw [W_nil_lt k y w hw]
          exact hxy ⟨w, hw⟩ h'
      · apply lab_const id ∅ c0
        intro x y
        show W k [] x w = W k [] y w
        by_cases h1 : w = k
        · rw [h1, W_nil_k, W_nil_k]
        · by_cases h2 : w = k + 1
          · rw [h2, W_nil_k1, W_nil_k1]
          · rw [W_nil_ge k x w (by omega), W_nil_ge k y w (by omega)]
  | append_singleton gs g ih =>
    intro hg
    have hg' : ∀ g' ∈ gs, GOK g' := fun g' h' => hg g' (List.mem_append_left _ h')
    have hgg : GOK g := hg g (by simp)
    obtain ⟨lab, N, h1, h2, h3⟩ := ih hg'
    obtain ⟨op, ins⟩ := g
    obtain ⟨hop, hlen⟩ := hgg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨u, _ | ⟨v, _ | ⟨w3, rest⟩⟩⟩
      · refine ⟨lab, N, ?_, ?_, step_all gs _ lab N c0 h3 (fun _ => true) (fun x => rfl)
          (lab_const lab N c0 _ (fun _ _ => rfl))⟩
        · rw [nc_snoc_and, List.length_append, List.length_singleton]
          omega
        · rw [nc_snoc_and]
          exact h2
      · refine ⟨lab, N, ?_, ?_, step_all gs _ lab N c0 h3 (fun x => W k gs x u)
          (fun x => eval_and1 (W k gs x u)) (h3 u)⟩
        · rw [nc_snoc_and, List.length_append, List.length_singleton]
          omega
        · rw [nc_snoc_and]
          exact h2
      · obtain ⟨cu, hdu, hmu⟩ := h3 u
        obtain ⟨cv, hdv, hmv⟩ := h3 v
        refine ⟨fun i => mrg cu cv (lab i), N.image (mrg cu cv), ?_, ?_,
          step_all gs _ _ _ c0 (fun w => lab_relab lab N (mrg cu cv) _ (h3 w))
            (fun x => W k gs x u && W k gs x v) (fun x => eval_and2 (W k gs x u) (W k gs x v))
            (lab_merge lab N cu cv _ _ hdu hmu hdv hmv (fun a b => a && b) hop_and)⟩
        · have := card_mrg lab cu cv
          rw [nc_snoc_and, List.length_append, List.length_singleton]
          omega
        · rw [nc_snoc_and]
          exact Finset.card_image_le.trans h2
      · simp at hlen
    · rcases ins with _ | ⟨u, _ | ⟨v, _ | ⟨w3, rest⟩⟩⟩
      · refine ⟨lab, N, ?_, ?_, step_all gs _ lab N c0 h3 (fun _ => false) (fun x => rfl)
          (lab_const lab N c0 _ (fun _ _ => rfl))⟩
        · rw [nc_snoc_or, List.length_append, List.length_singleton]
          omega
        · rw [nc_snoc_or]
          exact h2
      · refine ⟨lab, N, ?_, ?_, step_all gs _ lab N c0 h3 (fun x => W k gs x u)
          (fun x => eval_or1 (W k gs x u)) (h3 u)⟩
        · rw [nc_snoc_or, List.length_append, List.length_singleton]
          omega
        · rw [nc_snoc_or]
          exact h2
      · obtain ⟨cu, hdu, hmu⟩ := h3 u
        obtain ⟨cv, hdv, hmv⟩ := h3 v
        refine ⟨fun i => mrg cu cv (lab i), N.image (mrg cu cv), ?_, ?_,
          step_all gs _ _ _ c0 (fun w => lab_relab lab N (mrg cu cv) _ (h3 w))
            (fun x => W k gs x u || W k gs x v) (fun x => eval_or2 (W k gs x u) (W k gs x v))
            (lab_merge lab N cu cv _ _ hdu hmu hdv hmv (fun a b => a || b) hop_or)⟩
        · have := card_mrg lab cu cv
          rw [nc_snoc_or, List.length_append, List.length_singleton]
          omega
        · rw [nc_snoc_or]
          exact Finset.card_image_le.trans h2
      · simp at hlen
    · rcases ins with _ | ⟨u, rest⟩
      · refine ⟨lab, N, ?_, ?_, step_all gs _ lab N c0 h3 (fun _ => true) (fun x => rfl)
          (lab_const lab N c0 _ (fun _ _ => rfl))⟩
        · rw [nc_snoc_not, List.length_append, List.length_singleton]
          omega
        · rw [nc_snoc_not]
          omega
      · obtain ⟨cu, hdu, hmu⟩ := h3 u
        refine ⟨lab, insert cu N, ?_, ?_,
          step_all gs _ lab _ c0 (fun w => lab_insert lab N cu _ (h3 w)) (fun x => !W k gs x u)
            (fun x => rfl) (lab_not lab N cu _ hdu)⟩
        · rw [nc_snoc_not, List.length_append, List.length_singleton]
          omega
        · rw [nc_snoc_not]
          exact (Finset.card_insert_le _ _).trans (by omega)

-- Part 2. From labels to the flip sets: lower one representative input per block.

def xF {k g : ℕ} (rep : Fin g → Fin k) (F : Finset (Fin g)) (i : Fin k) : Bool :=
  decide (∀ j ∈ F, rep j ≠ i)

theorem xF_agree {k g : ℕ} (lab : Fin k → Fin k) (e : Fin g → Fin k) (rep : Fin g → Fin k)
    (hrep : ∀ j, lab (rep j) = e j) (c : Fin k) (F F' : Finset (Fin g))
    (hFF : ∀ j, e j = c → (j ∈ F ↔ j ∈ F')) : ∀ i, lab i = c → xF rep F i = xF rep F' i := by
  intro i hi
  unfold xF
  apply decide_eq_decide.2
  constructor
  · intro h j hj hji
    have hej : e j = c := by rw [← hrep j, hji, hi]
    exact h j ((hFF j hej).2 hj) hji
  · intro h j hj hji
    have hej : e j = c := by rw [← hrep j, hji, hi]
    exact h j ((hFF j hej).1 hj) hji

theorem xF_empty {k g : ℕ} (rep : Fin g → Fin k) (i : Fin k) : xF rep ∅ i = true := by
  unfold xF
  simp

theorem xF_all {k g : ℕ} (rep : Fin g → Fin k) (F : Finset (Fin g)) :
    (∀ i, xF rep F i = true) ↔ F = ∅ := by
  constructor
  · intro h
    by_contra hF
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hF
    have h1 := h (rep j)
    unfold xF at h1
    rw [decide_eq_true_iff] at h1
    exact h1 j hj rfl
  · intro hF i
    rw [hF]
    exact xF_empty rep i

theorem tap_F1 {k g : ℕ} (lab : Fin k → Fin k) (e : Fin g → Fin k) (rep : Fin g → Fin k)
    (hrep : ∀ j, lab (rep j) = e j) (c : Fin k) (f : (Fin k → Bool) → Bool) (hd : Dep lab c f)
    (j : Fin g) (hj : f (xF rep {j}) ≠ f (xF rep ∅)) : e j = c := by
  by_contra hne
  apply hj
  apply hd
  apply xF_agree lab e rep hrep c
  intro j' hj'
  have hne' : j' ≠ j := fun h => hne (h ▸ hj')
  simp [hne']

theorem tap_F2a {k g : ℕ} (lab : Fin k → Fin k) (e : Fin g → Fin k) (he : Function.Injective e)
    (rep : Fin g → Fin k) (hrep : ∀ j, lab (rep j) = e j) (c : Fin k) (f : (Fin k → Bool) → Bool)
    (hd : Dep lab c f) (F : Finset (Fin g)) (j0 : Fin g) (hj0F : j0 ∈ F) (hj0c : e j0 = c) :
    f (xF rep F) = f (xF rep {j0}) := by
  apply hd
  apply xF_agree lab e rep hrep c
  intro j' hj'
  have h : j' = j0 := he (hj'.trans hj0c.symm)
  rw [h]
  simp [hj0F]

theorem tap_F2b {k g : ℕ} (lab : Fin k → Fin k) (e : Fin g → Fin k) (rep : Fin g → Fin k)
    (hrep : ∀ j, lab (rep j) = e j) (c : Fin k) (f : (Fin k → Bool) → Bool)
    (hd : Dep lab c f) (F : Finset (Fin g)) (hF : ∀ j ∈ F, e j ≠ c) :
    f (xF rep F) = f (xF rep ∅) := by
  apply hd
  apply xF_agree lab e rep hrep c
  intro j' hj'
  have h : j' ∉ F := fun h => hF j' h hj'
  simp [h]

theorem xor_dec (p q : Bool) : p = xor q (decide (p ≠ q)) := by
  cases p <;> cases q <;> decide

theorem tap_formula {k g : ℕ} (lab : Fin k → Fin k) (e : Fin g → Fin k) (he : Function.Injective e)
    (rep : Fin g → Fin k) (hrep : ∀ j, lab (rep j) = e j) (c : Fin k) (f : (Fin k → Bool) → Bool)
    (hd : Dep lab c f) (F : Finset (Fin g)) :
    f (xF rep F) = xor (f (xF rep ∅)) (decide (∃ j ∈ F, f (xF rep {j}) ≠ f (xF rep ∅))) := by
  by_cases h : ∃ j0 ∈ F, e j0 = c
  · obtain ⟨j0, hj0F, hj0c⟩ := h
    have e1 := tap_F2a lab e he rep hrep c f hd F j0 hj0F hj0c
    have e2 : (∃ j ∈ F, f (xF rep {j}) ≠ f (xF rep ∅)) ↔ f (xF rep {j0}) ≠ f (xF rep ∅) := by
      constructor
      · rintro ⟨j, _, hj⟩
        have hjc := tap_F1 lab e rep hrep c f hd j hj
        have hjj : j = j0 := he (hjc.trans hj0c.symm)
        rw [← hjj]
        exact hj
      · intro hj
        exact ⟨j0, hj0F, hj⟩
    rw [e1, decide_eq_decide.2 e2]
    exact xor_dec _ _
  · push_neg at h
    have e1 := tap_F2b lab e rep hrep c f hd F h
    have e2 : ¬ (∃ j ∈ F, f (xF rep {j}) ≠ f (xF rep ∅)) := by
      rintro ⟨j, hjF, hj⟩
      exact h j hjF (tap_F1 lab e rep hrep c f hd j hj)
    rw [e1, decide_eq_false e2]
    generalize f (xF rep ∅) = q
    cases q <;> rfl

theorem extract {k m g : ℕ} (R : Bool → (Fin m → Bool) → Prop) (lab : Fin k → Fin k)
    (N : Finset (Fin k)) (e : Fin g → Fin k) (he : Function.Injective e) (rep : Fin g → Fin k)
    (hrep : ∀ j, lab (rep j) = e j) (t : Fin m → (Fin k → Bool) → Bool)
    (ht : ∀ a, Lab lab N (t a)) (hR : ∀ x, R (decide (∀ i, x i = true)) (fun a => t a x)) :
    ∃ (v : Fin m → Bool) (S : Fin g → Finset (Fin m)),
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
      (∀ F : Finset (Fin g), R (decide (F = ∅)) (fun a => xor (v a) (decide (a ∈ F.biUnion S)))) ∧
      (Finset.univ.filter (fun j : Fin g => ∃ a ∈ S j, v a = false)).card ≤ N.card := by
  choose c hd hm using ht
  refine ⟨fun a => t a (xF rep ∅),
    fun j => Finset.univ.filter (fun a => t a (xF rep {j}) ≠ t a (xF rep ∅)), ?_, ?_, ?_⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro a hai haj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hai haj
    exact hij (he ((tap_F1 lab e rep hrep (c a) (t a) (hd a) i hai).trans
      (tap_F1 lab e rep hrep (c a) (t a) (hd a) j haj).symm))
  · intro F
    have hx := hR (xF rep F)
    have e1 : decide (∀ i, xF rep F i = true) = decide (F = ∅) := decide_eq_decide.2 (xF_all rep F)
    rw [e1] at hx
    refine (congrArg (R (decide (F = ∅))) (funext fun a => ?_)).mpr hx
    show xor (t a (xF rep ∅)) (decide (a ∈ F.biUnion
      (fun j => Finset.univ.filter (fun a => t a (xF rep {j}) ≠ t a (xF rep ∅))))) = t a (xF rep F)
    rw [tap_formula lab e he rep hrep (c a) (t a) (hd a) F]
    congr 1
    apply decide_eq_decide.2
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  · refine Finset.card_le_card_of_injOn e ?_ (fun a _ b _ h => he h)
    intro j hj
    simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hj
    obtain ⟨a, ha, hva⟩ := hj
    have hjc := tap_F1 lab e rep hrep (c a) (t a) (hd a) j ha
    have hva' : t a (xF rep ∅) = false := hva
    have hin : c a ∈ N := by
      by_contra hn
      have h1 : t a (xF rep {j}) = true := by
        rw [hva'] at ha
        simpa using ha
      have h2 := hm a hn (xF rep {j}) (xF rep ∅) (fun i _ => xF_empty rep i) h1
      rw [hva'] at h2
      exact Bool.false_ne_true h2
    rw [hjc]
    exact hin

theorem eT_exists {k : ℕ} (T : Finset (Fin k)) :
    ∃ e : Fin T.card → Fin k, Function.Injective e ∧ ∀ j, e j ∈ T :=
  ⟨fun j => (T.equivFin.symm j).val, fun i j h => T.equivFin.symm.injective (Subtype.ext h),
    fun j => (T.equivFin.symm j).2⟩

theorem necessity (k m : ℕ) (R : Bool → (Fin m → Bool) → Prop) (s b r : ℕ) (hk : 0 < k)
    (gs : List Gate) (hg : ∀ g ∈ gs, GOK g) (tap : Fin m → ℕ)
    (hs : gs.length ≤ s) (hb : gs.length - PEqualNP.NotBracket.notCount (Circuit.mk gs 0) ≤ b)
    (hr : PEqualNP.NotBracket.notCount (Circuit.mk gs 0) ≤ r)
    (hR : ∀ x : Fin k → Bool, R (decide (∀ i, x i = true)) (fun a => W k gs x (tap a))) :
    ∃ (g : ℕ) (v : Fin m → Bool) (S : Fin g → Finset (Fin m)),
      0 < g ∧ g ≤ k ∧ (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
      (∀ F : Finset (Fin g), R (decide (F = ∅))
        (fun a => xor (v a) (decide (a ∈ F.biUnion S)))) ∧
      (k - g ≤ b ∧ (Finset.univ.filter (fun j : Fin g => ∃ a ∈ S j, v a = false)).card ≤ r ∧
        k - g + (Finset.univ.filter (fun j : Fin g => ∃ a ∈ S j, v a = false)).card ≤ s) := by
  obtain ⟨lab, N, h1, h2, h3⟩ := inv hk gs hg
  obtain ⟨e, he, heT⟩ := eT_exists (Finset.univ.image lab)
  have hmem : ∀ j, ∃ i, lab i = e j := fun j => by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 (heT j)
    exact ⟨i, hi⟩
  choose rep hrep using hmem
  obtain ⟨v, S, hdisj, hRF, hq⟩ := extract R lab N e he rep hrep
    (fun a x => W k gs x (tap a)) (fun a => h3 (tap a)) hR
  have hTpos : 0 < (Finset.univ.image lab).card :=
    Finset.card_pos.2 ⟨lab ⟨0, hk⟩, Finset.mem_image_of_mem lab (Finset.mem_univ _)⟩
  have hTle : (Finset.univ.image lab).card ≤ k := by
    have h4 := Finset.card_le_univ (Finset.univ.image lab)
    simpa using h4
  refine ⟨(Finset.univ.image lab).card, v, S, hTpos, hTle, hdisj, hRF, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

-- Part 3. Sufficiency: group conjunctions, one shared NOT per needy group, constants.

abbrev Good (k : ℕ) (gs : List Gate) : Prop :=
  PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gs 0) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + 2) (Circuit.mk gs 0)

theorem good_nil (k : ℕ) : Good k [] :=
  ⟨fun g hg => by simp at hg, fun j hj => by simp at hj⟩

theorem good_snoc (k : ℕ) (gs : List Gate) (g : Gate) (h : Good k gs) (hg : GOK g)
    (hin : ∀ i ∈ g.inputs, i < k + 2 + gs.length) : Good k (gs ++ [g]) := by
  obtain ⟨hf, hr⟩ := h
  constructor
  · intro g' hg'
    have hg'' : g' ∈ gs ++ [g] := hg'
    rcases List.mem_append.1 hg'' with h' | h'
    · exact hf g' h'
    · rw [List.mem_singleton] at h'
      rw [h']
      exact hg
  · intro j hj i hi
    have hj' : j < gs.length + 1 := by simpa using hj
    by_cases hjl : j < gs.length
    · have e : PEqualNP.MetaComplexity.NestedCover.gateAt (Circuit.mk (gs ++ [g]) 0) j =
          PEqualNP.MetaComplexity.NestedCover.gateAt (Circuit.mk gs 0) j := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        show (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩
        exact List.getD_append _ _ _ _ hjl
      rw [e] at hi
      exact hr j hjl i hi
    · have hjeq : j = gs.length := by omega
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt (Circuit.mk (gs ++ [g]) 0) j = g := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        show (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = g
        rw [List.getD_append_right _ _ _ _ (by omega), hjeq, Nat.sub_self]
        rfl
      rw [e] at hi
      have := hin i hi
      omega

abbrev Avail (k : ℕ) (gs : List Gate) (f : (Fin k → Bool) → Bool) : Prop :=
  ∃ w, w < k + 2 + gs.length ∧ ∀ x, W k gs x w = f x

theorem avail_congr (k : ℕ) (gs : List Gate) (f f' : (Fin k → Bool) → Bool) (h : Avail k gs f)
    (e : ∀ x, f x = f' x) : Avail k gs f' := by
  obtain ⟨w, hw, hf⟩ := h
  exact ⟨w, hw, fun x => (hf x).trans (e x)⟩

theorem avail_mono (k : ℕ) (gs e : List Gate) (f : (Fin k → Bool) → Bool) (h : Avail k gs f) :
    Avail k (gs ++ e) f := by
  obtain ⟨w, hw, hf⟩ := h
  refine ⟨w, by simp only [List.length_append]; omega, fun x => ?_⟩
  rw [W_prefix k gs x w hw e]
  exact hf x

theorem avail_input (k : ℕ) (gs : List Gate) (i : Fin k) : Avail k gs (fun x => x i) := by
  have hi := i.isLt
  exact ⟨i.val, by omega, fun x => (W_base k gs x i.val (by omega)).trans (W_nil_lt k x i.val hi)⟩

theorem avail_const (k : ℕ) (gs : List Gate) (c : Bool) : Avail k gs (fun _ => c) := by
  cases c
  · exact ⟨k, by omega, fun x => (W_base k gs x k (by omega)).trans (W_nil_k k x)⟩
  · exact ⟨k + 1, by omega, fun x => (W_base k gs x (k + 1) (by omega)).trans (W_nil_k1 k x)⟩

theorem avail_and (k : ℕ) (gs : List Gate) (f f' : (Fin k → Bool) → Bool) (hgs : Good k gs)
    (h : Avail k gs f) (h' : Avail k gs f') :
    ∃ ins : List ℕ, Good k (gs ++ [⟨GateOp.and, ins⟩]) ∧
      Avail k (gs ++ [⟨GateOp.and, ins⟩]) (fun x => f x && f' x) := by
  obtain ⟨w, hw, hf⟩ := h
  obtain ⟨w', hw', hf'⟩ := h'
  refine ⟨[w, w'], good_snoc k gs _ hgs ⟨by simp, by simp⟩ ?_, k + 2 + gs.length, ?_, fun x => ?_⟩
  · intro i hi
    simp at hi
    rcases hi with h1 | h1
    · rw [h1]; exact hw
    · rw [h1]; exact hw'
  · simp only [List.length_append, List.length_singleton]
    omega
  · rw [W_snoc, if_neg (by omega), if_pos rfl]
    show GateOp.eval GateOp.and [W k gs x w, W k gs x w'] = (f x && f' x)
    rw [eval_and2, hf x, hf' x]

theorem avail_not (k : ℕ) (gs : List Gate) (f : (Fin k → Bool) → Bool) (hgs : Good k gs)
    (h : Avail k gs f) :
    ∃ ins : List ℕ, Good k (gs ++ [⟨GateOp.not, ins⟩]) ∧
      Avail k (gs ++ [⟨GateOp.not, ins⟩]) (fun x => !f x) := by
  obtain ⟨w, hw, hf⟩ := h
  refine ⟨[w], good_snoc k gs _ hgs ⟨by simp, by simp⟩ ?_, k + 2 + gs.length, ?_, fun x => ?_⟩
  · intro i hi
    simp at hi
    rw [hi]
    exact hw
  · simp only [List.length_append, List.length_singleton]
    omega
  · rw [W_snoc, if_neg (by omega), if_pos rfl]
    show (!W k gs x w) = !f x
    rw [hf x]

theorem chain (k g : ℕ) (hg0 : 0 < g) (hgk : g ≤ k) : ∀ t, t ≤ k - g →
    ∃ gs : List Gate, Good k gs ∧ gs.length = t ∧ PEqualNP.NotBracket.notCount (Circuit.mk gs 0) = 0 ∧
      Avail k gs (fun x => decide (∀ i : Fin k, g - 1 ≤ i.val → i.val ≤ g - 1 + t → x i = true)) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨[], good_nil k, rfl, nc_nil, g - 1, by omega, fun x => ?_⟩
    rw [W_nil_lt k x (g - 1) (by omega)]
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq]
    constructor
    · intro h i h1 h2
      have hi : i = ⟨g - 1, by omega⟩ := Fin.ext (show i.val = g - 1 by omega)
      rw [hi]
      exact h
    · intro h
      exact h ⟨g - 1, by omega⟩ (show g - 1 ≤ g - 1 from le_refl _) (show g - 1 ≤ g - 1 + 0 by omega)
  | succ t ih =>
    intro ht
    obtain ⟨gs, hgood, hlen, hnc, hav⟩ := ih (by omega)
    obtain ⟨ins, hgood', hav'⟩ := avail_and k gs _ _ hgood hav (avail_input k gs ⟨g + t, by omega⟩)
    refine ⟨gs ++ [⟨GateOp.and, ins⟩], hgood', by simp [hlen], by rw [nc_snoc_and, hnc], ?_⟩
    apply avail_congr k _ _ _ hav'
    intro x
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi1 hi2
      by_cases hit : i.val ≤ g - 1 + t
      · exact h1 i hi1 hit
      · have hi : i = ⟨g + t, by omega⟩ := Fin.ext (show i.val = g + t by omega)
        rw [hi]
        exact h2
    · intro h
      exact ⟨fun i hi1 hi2 => h i hi1 (by omega),
        h ⟨g + t, by omega⟩ (show g - 1 ≤ g + t by omega) (show g + t ≤ g - 1 + (t + 1) by omega)⟩

def cj {k g : ℕ} (j : Fin g) (x : Fin k → Bool) : Bool :=
  decide (∀ i : Fin k, min i.val (g - 1) = j.val → x i = true)

theorem conj_avail (k g : ℕ) (hg0 : 0 < g) (hgk : g ≤ k) :
    ∃ gs : List Gate, Good k gs ∧ gs.length = k - g ∧
      PEqualNP.NotBracket.notCount (Circuit.mk gs 0) = 0 ∧ ∀ j : Fin g, Avail k gs (cj j) := by
  obtain ⟨gs, hgood, hlen, hnc, hav⟩ := chain k g hg0 hgk (k - g) le_rfl
  refine ⟨gs, hgood, hlen, hnc, fun j => ?_⟩
  have hjlt := j.isLt
  by_cases hj : j.val < g - 1
  · apply avail_congr k gs _ _ (avail_input k gs ⟨j.val, by omega⟩)
    intro x
    apply Bool.eq_iff_iff.2
    simp only [cj, decide_eq_true_eq]
    constructor
    · intro h i hi
      have hii : i = ⟨j.val, by omega⟩ := Fin.ext (show i.val = j.val by omega)
      rw [hii]
      exact h
    · intro h
      exact h ⟨j.val, by omega⟩ (show min j.val (g - 1) = j.val by omega)
  · apply avail_congr k gs _ _ hav
    intro x
    apply Bool.eq_iff_iff.2
    simp only [cj, decide_eq_true_eq]
    constructor
    · intro h i hi
      have hil := i.isLt
      exact h i (by omega) (by omega)
    · intro h i h1 _
      exact h i (by omega)

theorem nots (k g : ℕ) (gs : List Gate) (hgood : Good k gs) (hav : ∀ j : Fin g, Avail k gs (cj j)) :
    ∀ T : Finset (Fin g), ∃ e : List Gate, Good k (gs ++ e) ∧ e.length = T.card ∧
      PEqualNP.NotBracket.notCount (Circuit.mk e 0) = T.card ∧
      ∀ j ∈ T, Avail k (gs ++ e) (fun x => !cj j x) := by
  intro T
  refine Finset.induction_on T ?_ ?_
  · refine ⟨[], by rw [List.append_nil]; exact hgood, by simp, by simp [nc_nil], fun j hj => by simp at hj⟩
  · intro j T hjT ih
    obtain ⟨e, hge, hle, hne, hae⟩ := ih
    have hcj : Avail k (gs ++ e) (cj j) := avail_mono k gs e _ (hav j)
    obtain ⟨ins, hgood', hav'⟩ := avail_not k (gs ++ e) _ hge hcj
    refine ⟨e ++ [⟨GateOp.not, ins⟩], ?_, ?_, ?_, ?_⟩
    · rw [← List.append_assoc]
      exact hgood'
    · rw [List.length_append, List.length_singleton, hle, Finset.card_insert_of_notMem hjT]
    · rw [nc_snoc_not, hne, Finset.card_insert_of_notMem hjT]
    · intro j' hj'
      rw [← List.append_assoc]
      rcases Finset.mem_insert.1 hj' with h | h
      · rw [h]
        exact hav'
      · exact avail_mono k (gs ++ e) _ _ (hae j' h)

theorem dec_iff_false (P : Prop) [Decidable P] (b : Bool) (h : P ↔ b = false) : decide P = !b := by
  cases b
  · show decide P = true
    exact decide_eq_true (h.2 rfl)
  · show decide P = false
    exact decide_eq_false (fun hp => absurd (h.1 hp) (by decide))

theorem sufficiency (k m : ℕ) (R : Bool → (Fin m → Bool) → Prop) (s b r : ℕ)
    (g : ℕ) (v : Fin m → Bool) (S : Fin g → Finset (Fin m)) (hg0 : 0 < g) (hgk : g ≤ k)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hRF : ∀ F : Finset (Fin g), R (decide (F = ∅)) (fun a => xor (v a) (decide (a ∈ F.biUnion S))))
    (hb : k - g ≤ b) (hr : (Finset.univ.filter (fun j : Fin g => ∃ a ∈ S j, v a = false)).card ≤ r)
    (hs : k - g + (Finset.univ.filter (fun j : Fin g => ∃ a ∈ S j, v a = false)).card ≤ s) :
    ∃ (C : Circuit) (tap : Fin m → Fin (k+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) C ∧
      C.output < k+2+C.size ∧ C.size ≤ s ∧ C.size - PEqualNP.NotBracket.notCount C ≤ b ∧
      PEqualNP.NotBracket.notCount C ≤ r ∧ ∀ x : Fin k → Bool,
        R (decide (∀ i, x i = true)) (fun a => W k C.gates x (tap a).val) := by
  obtain ⟨gs, hgood, hlen, hnc, hav⟩ := conj_avail k g hg0 hgk
  obtain ⟨e, hge, hle, hne, hae⟩ :=
    nots k g gs hgood hav (Finset.univ.filter (fun j : Fin g => ∃ a ∈ S j, v a = false))
  have htap : ∀ a : Fin m, Avail k (gs ++ e) (fun x => xor (v a)
      (decide (a ∈ (Finset.univ.filter (fun j : Fin g => cj j x = false)).biUnion S))) := by
    intro a
    by_cases ha : ∃ j0, a ∈ S j0
    · obtain ⟨j0, hj0⟩ := ha
      have hmem : ∀ x : Fin k → Bool,
          (a ∈ (Finset.univ.filter (fun j : Fin g => cj j x = false)).biUnion S) ↔ cj j0 x = false := by
        intro x
        rw [Finset.mem_biUnion]
        constructor
        · rintro ⟨j, hj, haj⟩
          have hjj : j = j0 := by
            by_contra hne'
            exact Finset.disjoint_left.1 (hdisj j j0 hne') haj hj0
          rw [hjj] at hj
          simpa using hj
        · intro h
          exact ⟨j0, by simpa using h, hj0⟩
      cases hva : v a
      · have hj0n : j0 ∈ Finset.univ.filter (fun j : Fin g => ∃ a ∈ S j, v a = false) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨a, hj0, hva⟩
        apply avail_congr k _ _ _ (hae j0 hj0n)
        intro x
        show (!cj j0 x) = xor false
          (decide (a ∈ (Finset.univ.filter (fun j : Fin g => cj j x = false)).biUnion S))
        rw [dec_iff_false _ _ (hmem x)]
        cases cj j0 x <;> rfl
      · apply avail_congr k _ _ _ (avail_mono k gs e _ (hav j0))
        intro x
        show cj j0 x = xor true
          (decide (a ∈ (Finset.univ.filter (fun j : Fin g => cj j x = false)).biUnion S))
        rw [dec_iff_false _ _ (hmem x)]
        cases cj j0 x <;> rfl
    · push_neg at ha
      apply avail_congr k _ _ _ (avail_const k (gs ++ e) (v a))
      intro x
      have hn : a ∉ (Finset.univ.filter (fun j : Fin g => cj j x = false)).biUnion S := by
        rw [Finset.mem_biUnion]
        rintro ⟨j, _, haj⟩
        exact ha j haj
      show v a = xor (v a)
        (decide (a ∈ (Finset.univ.filter (fun j : Fin g => cj j x = false)).biUnion S))
      rw [decide_eq_false hn]
      cases v a <;> rfl
  choose w hw hwv using htap
  refine ⟨Circuit.mk (gs ++ e) 0, fun a => ⟨w a, hw a⟩, hge.1, hge.2, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < k + 2 + (gs ++ e).length
    omega
  · show (gs ++ e).length ≤ s
    rw [List.length_append, hlen, hle]
    exact hs
  · show (gs ++ e).length - PEqualNP.NotBracket.notCount (Circuit.mk (gs ++ e) 0) ≤ b
    rw [nc_append, hnc, hne, List.length_append, hlen, hle]
    omega
  · show PEqualNP.NotBracket.notCount (Circuit.mk (gs ++ e) 0) ≤ r
    rw [nc_append, hnc, hne]
    omega
  · intro x
    have hx := hRF (Finset.univ.filter (fun j : Fin g => cj j x = false))
    have e1 : decide (∀ i, x i = true) =
        decide (Finset.univ.filter (fun j : Fin g => cj j x = false) = ∅) := by
      apply decide_eq_decide.2
      rw [Finset.filter_eq_empty_iff]
      constructor
      · intro h j _ hj
        unfold cj at hj
        rw [decide_eq_false_iff_not] at hj
        exact hj (fun i _ => h i)
      · intro h i
        by_contra hxi
        apply h (Finset.mem_univ (⟨min i.val (g - 1), by omega⟩ : Fin g))
        unfold cj
        rw [decide_eq_false_iff_not]
        intro hall
        exact hxi (hall i rfl)
    rw [e1]
    refine (congrArg (R _) (funext fun a => ?_)).mpr hx
    exact hwv a x

end PEqualNP.Outside.L_lib_1204_aux

theorem PEqualNP.Outside.L_lib_1204 : ∀ (k m : Nat) (R : Bool → (Fin m → Bool) → Prop) (s b r : Nat), 0 < k →
  ((∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (k+2+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) C ∧
    C.output < k+2+C.size ∧ C.size ≤ s ∧ C.size - PEqualNP.NotBracket.notCount C ≤ b ∧
    PEqualNP.NotBracket.notCount C ≤ r ∧ ∀ x : Fin k → Bool,
      let w := List.ofFn x ++ [false,true]
      R (decide (∀ i, x i = true)) (fun a => (C.wires w).getD (tap a).val false)) ↔
    ∃ (g : Nat) (v : Fin m → Bool) (S : Fin g → Finset (Fin m)),
      0 < g ∧ g ≤ k ∧ (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
      (∀ F : Finset (Fin g), R (decide (F = ∅))
        (fun a => xor (v a) (decide (a ∈ F.biUnion S)))) ∧
      let q := (Finset.univ.filter (fun j : Fin g => ∃ a ∈ S j, v a = false)).card
      k-g ≤ b ∧ q ≤ r ∧ k-g+q ≤ s) := by
  intro k m R s b r hk
  constructor
  · rintro ⟨C, tap, hFan, _, _, hs, hb, hr, hR⟩
    exact PEqualNP.Outside.L_lib_1204_aux.necessity k m R s b r hk C.gates hFan
      (fun a => (tap a).val) hs hb hr hR
  · rintro ⟨g, v, S, hg0, hgk, hdisj, hRF, hq⟩
    obtain ⟨hb, hr, hs⟩ := hq
    obtain ⟨C, tap, h1, h2, h3, h4, h5, h6, h7⟩ :=
      PEqualNP.Outside.L_lib_1204_aux.sufficiency k m R s b r g v S hg0 hgk hdisj hRF hb hr hs
    exact ⟨C, tap, h1, h2, h3, h4, h5, h6, h7⟩
