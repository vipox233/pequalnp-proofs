import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1188_aux

open scoped Classical
open PEqualNP.CircuitLowerBounds (Circuit Gate GateOp)

/-! ### Part 1: Wire evaluation and negation-count chain lemma -/

def evalWires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

lemma eq_not_of_isNotOp {op : GateOp} (h : isNotOp op = true) : op = GateOp.not := by
  cases op <;> simp [isNotOp] at h ⊢

def notCountL (gs : List Gate) : ℕ :=
  (gs.filter fun g => isNotOp g.op).length

def nonNotCountL (gs : List Gate) : ℕ :=
  (gs.filter fun g => !isNotOp g.op).length

lemma notCountL_eq_notCount (C : Circuit) :
    notCountL C.gates = PEqualNP.NotBracket.notCount C := by
  unfold notCountL PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases g.op <;> simp [isNotOp]

lemma nonNot_add_not (gs : List Gate) : nonNotCountL gs + notCountL gs = gs.length := by
  induction gs with
  | nil => simp [nonNotCountL, notCountL]
  | cons g gs ih =>
    cases h : isNotOp g.op <;> simp [nonNotCountL, notCountL, h] at ih ⊢ <;> omega

lemma notCountL_append (gs1 gs2 : List Gate) :
    notCountL (gs1 ++ gs2) = notCountL gs1 + notCountL gs2 := by
  simp [notCountL, List.filter_append]

lemma nonNotCountL_append (gs1 gs2 : List Gate) :
    nonNotCountL (gs1 ++ gs2) = nonNotCountL gs1 + nonNotCountL gs2 := by
  simp [nonNotCountL, List.filter_append]

lemma evalWires_length (gs : List Gate) (w : List Bool) :
    (evalWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalWires]
  | cons g gs ih =>
    simp only [evalWires, List.foldl_cons] at ih ⊢
    rw [ih, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma evalWires_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalWires (gs1 ++ gs2) w = evalWires gs2 (evalWires gs1 w) := by
  simp [evalWires, List.foldl_append]

lemma getD_append_singleton {α : Type*} (w : List α) (a d : α) (i : ℕ) :
    (w ++ [a]).getD i d = if i < w.length then w.getD i d else if i = w.length then a else d := by
  by_cases h1 : i < w.length
  · rw [if_pos h1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h1]
  · rw [if_neg h1]
    have hge : w.length ≤ i := Nat.le_of_not_lt h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
    by_cases h2 : i = w.length
    · subst h2; simp
    · rw [if_neg h2]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl

lemma evalWires_getD_prefix (gs1 gs2 : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + gs1.length) :
    (evalWires (gs1 ++ gs2) w).getD i false = (evalWires gs1 w).getD i false := by
  rw [evalWires_append]
  have hgen : ∀ (gs : List Gate) (u : List Bool), i < u.length →
      (evalWires gs u).getD i false = u.getD i false := by
    intro gs
    induction gs with
    | nil => intro u _; rfl
    | cons g gs ih =>
      intro u hu
      change (evalWires gs (u ++ [g.op.eval (g.inputs.map fun k => u.getD k false)])).getD i false = _
      rw [ih _ (by simp; omega), getD_append_singleton, if_pos hu]
  exact hgen gs2 (evalWires gs1 w) (by rw [evalWires_length]; exact hi)

lemma bool_true_le_eq {b : Bool} (h : true ≤ b) : b = true := by
  cases b
  · exact absurd h (by decide)
  · rfl

lemma getD_append_le {wa wb : List Bool} (hlen : wa.length = wb.length)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) {va vb : Bool} (hv : va ≤ vb) :
    ∀ i, (wa ++ [va]).getD i false ≤ (wb ++ [vb]).getD i false := by
  intro i
  rw [getD_append_singleton, getD_append_singleton, hlen]
  by_cases h1 : i < wb.length
  · rw [if_pos h1, if_pos h1]; exact hle i
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : i = wb.length
    · rw [if_pos h2, if_pos h2]; exact hv
    · rw [if_neg h2, if_neg h2]

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

def notCode : List Gate → List Bool → ℕ
  | [], _ => 0
  | g :: gs, w =>
    let val := g.op.eval (g.inputs.map fun i => w.getD i false)
    let rest := notCode gs (w ++ [val])
    if isNotOp g.op then
      (if val then 1 else 0) * 2 ^ (notCountL gs) + rest
    else
      rest

lemma notCode_lt : ∀ (gs : List Gate) (w : List Bool), notCode gs w < 2 ^ notCountL gs
  | [], _ => by simp [notCode, notCountL]
  | g :: gs, w => by
    have ih := notCode_lt gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    dsimp only [notCode]
    cases h : isNotOp g.op
    · simp only [Bool.false_eq_true, ↓reduceIte, notCountL, List.filter_cons, h]
      exact ih
    · have hnc : notCountL (g :: gs) = notCountL gs + 1 := by simp [notCountL, h]
      rw [hnc, pow_succ]
      simp only [↓reduceIte]
      generalize g.op.eval (g.inputs.map fun i => w.getD i false) = v at ih ⊢
      cases v <;> simp <;> omega

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

lemma evalWires_mono_of_zero_not (gs : List Gate)
    (hfit : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (h0 : notCountL gs = 0)
    (wa wb : List Bool) (hlen : wa.length = wb.length)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) :
    ∀ i, (evalWires gs wa).getD i false ≤ (evalWires gs wb).getD i false := by
  rcases notCode_step gs hfit wa wb hlen hle with hlt | ⟨_, hw⟩
  · exfalso
    have hlt1 := notCode_lt gs wa
    rw [h0, pow_zero] at hlt1
    omega
  · exact hw

/-! ### Part 2: Syntactic input support of wires -/

def gateDeps (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

def initSupp (n : ℕ) : List (Finset (Fin n)) :=
  (List.finRange n).map (fun u => {u}) ++ [∅, ∅]

def foldSupp {n : ℕ} (gs : List Gate) (S : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun S g => S ++ [(gateDeps g).foldl (fun acc i => acc ∪ S.getD i ∅) ∅]) S

lemma foldl_union_subset {α : Type*} [DecidableEq α] (l : List ℕ) (f : ℕ → Finset α)
    (acc : Finset α) :
    acc ⊆ l.foldl (fun a i => a ∪ f i) acc ∧
    ∀ i ∈ l, f i ⊆ l.foldl (fun a k => a ∪ f k) acc := by
  induction l generalizing acc with
  | nil => exact ⟨Finset.Subset.refl _, fun _ h => absurd h List.not_mem_nil⟩
  | cons k ks ih =>
    rcases ih (acc ∪ f k) with ⟨h1, h2⟩
    refine ⟨Finset.Subset.trans Finset.subset_union_left h1, fun i hi => ?_⟩
    rcases List.mem_cons.mp hi with rfl | hmem
    · exact Finset.Subset.trans Finset.subset_union_right h1
    · exact h2 i hmem

lemma foldl_union_card_le {α : Type*} [DecidableEq α] (l : List ℕ) (f : ℕ → Finset α)
    (acc : Finset α) (hf : ∀ i ∈ l, (f i).card ≤ 1) :
    (l.foldl (fun a i => a ∪ f i) acc).card ≤ acc.card + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons k ks ih =>
    have h1 := ih (acc ∪ f k) (fun i hi => hf i (List.mem_cons_of_mem k hi))
    have h2 : (acc ∪ f k).card ≤ acc.card + (f k).card := Finset.card_union_le acc (f k)
    have h3 : (f k).card ≤ 1 := hf k (List.mem_cons_self ..)
    simp only [List.foldl_cons, List.length_cons]
    omega

lemma agree_foldSupp {n : ℕ} (x y : Fin n → Bool) :
    ∀ (gs : List Gate) (wa wb : List Bool) (S : List (Finset (Fin n))),
      wa.length = S.length → wb.length = S.length →
      (∀ i, (∀ u ∈ S.getD i ∅, x u = y u) → wa.getD i false = wb.getD i false) →
      ∀ i, (∀ u ∈ (foldSupp gs S).getD i ∅, x u = y u) →
        (evalWires gs wa).getD i false = (evalWires gs wb).getD i false
  | [], wa, wb, S, _, _, hinv => hinv
  | g :: gs, wa, wb, S, hla, hlb, hinv => by
    let Unew := (gateDeps g).foldl (fun acc i => acc ∪ S.getD i ∅) ∅
    let va := g.op.eval (g.inputs.map fun i => wa.getD i false)
    let vb := g.op.eval (g.inputs.map fun i => wb.getD i false)
    apply agree_foldSupp x y gs (wa ++ [va]) (wb ++ [vb]) (S ++ [Unew])
      (by simp [hla]) (by simp [hlb])
    intro i hag
    rw [getD_append_singleton, getD_append_singleton, hla, hlb]
    rw [getD_append_singleton] at hag
    by_cases h1 : i < S.length
    · rw [if_pos h1, if_pos h1]; rw [if_pos h1] at hag; exact hinv i hag
    · rw [if_neg h1, if_neg h1]; rw [if_neg h1] at hag
      by_cases h2 : i = S.length
      · rw [if_pos h2, if_pos h2]; rw [if_pos h2] at hag
        have hdeps : ∀ k ∈ gateDeps g, wa.getD k false = wb.getD k false := by
          intro k hk
          apply hinv k
          intro u hu
          exact hag u ((foldl_union_subset (gateDeps g) (fun j => S.getD j ∅) ∅).2 k hk hu)
        dsimp only [va, vb]
        cases hop : g.op with
        | not =>
          cases hin : g.inputs with
          | nil => rfl
          | cons k ks =>
            simp only [GateOp.eval, List.map_cons, List.headD_cons]
            have hk : k ∈ gateDeps g := by simp [gateDeps, hop, hin]
            rw [hdeps k hk]
        | and | or | mod _ | maj =>
          congr 1
          apply List.map_congr_left
          intro k hk
          exact hdeps k (by simp [gateDeps, hop, hk])
      · rw [if_neg h2, if_neg h2]

lemma wire_agree_of_supp {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (i : ℕ)
    (hag : ∀ u ∈ (foldSupp C.gates (initSupp n)).getD i ∅, x u = y u) :
    (C.wires (List.ofFn x ++ [false, true])).getD i false =
    (C.wires (List.ofFn y ++ [false, true])).getD i false := by
  apply agree_foldSupp x y C.gates (List.ofFn x ++ [false, true]) (List.ofFn y ++ [false, true])
    (initSupp n) (by simp [initSupp]) (by simp [initSupp]) _ i hag
  intro k hk
  by_cases hkn : k < n
  · have hSk : (initSupp n).getD k ∅ = {⟨k, hkn⟩} := by
      dsimp only [initSupp]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hkn]),
          List.getElem?_map, List.getElem?_eq_getElem (by simp [hkn]), List.getElem_finRange]
      rfl
    rw [hSk] at hk
    have hxy : x ⟨k, hkn⟩ = y ⟨k, hkn⟩ := hk ⟨k, hkn⟩ (Finset.mem_singleton_self _)
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simp [hkn]), List.getElem?_append_left (by simp [hkn]),
        List.getElem?_ofFn, List.getElem?_ofFn, dif_pos hkn, dif_pos hkn]
    exact hxy
  · have hge1 : (List.ofFn x).length ≤ k := by simp; omega
    have hge2 : (List.ofFn y).length ≤ k := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right hge1, List.getElem?_append_right hge2]
    simp

lemma mem_getD_of_ne_empty {α : Type*} (S : List (Finset α)) (i : ℕ) :
    S.getD i ∅ = ∅ ∨ S.getD i ∅ ∈ S := by
  by_cases hi : i < S.length
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  · left
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]
    rfl

lemma foldSupp_zero_nonNot {n : ℕ} (Ustar : Finset (Fin n)) :
    ∀ (gs : List Gate) (S : List (Finset (Fin n))),
      nonNotCountL gs = 0 →
      (∀ U ∈ S, U.card ≤ 1 ∨ U = Ustar) →
      ∀ U ∈ foldSupp gs S, U.card ≤ 1 ∨ U = Ustar
  | [], S, _, hS => hS
  | g :: gs, S, h0, hS => by
    have hgnot : isNotOp g.op = true := by
      cases h : isNotOp g.op
      · simp [nonNotCountL, h] at h0
      · rfl
    have hgs0 : nonNotCountL gs = 0 := by simpa [nonNotCountL, hgnot] using h0
    have hop : g.op = GateOp.not := eq_not_of_isNotOp hgnot
    let Unew := (gateDeps g).foldl (fun acc i => acc ∪ S.getD i ∅) ∅
    apply foldSupp_zero_nonNot Ustar gs (S ++ [Unew]) hgs0
    intro U hU
    rcases List.mem_append.mp hU with h1 | h2
    · exact hS U h1
    · rw [List.mem_singleton.mp h2]
      dsimp only [Unew, gateDeps]
      rw [hop]
      cases hin : g.inputs with
      | nil => left; simp
      | cons k ks =>
        simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil,
          Finset.empty_union]
        rcases mem_getD_of_ne_empty S k with he | hm
        · left; rw [he]; simp
        · exact hS _ hm

lemma foldSupp_le_one_nonNot {n : ℕ} :
    ∀ (gs : List Gate) (S : List (Finset (Fin n))),
      (∀ g ∈ gs, g.inputs.length ≤ 2) →
      nonNotCountL gs ≤ 1 →
      (∀ U ∈ S, U.card ≤ 1) →
      ∃ Ustar : Finset (Fin n), Ustar.card ≤ 2 ∧ ∀ U ∈ foldSupp gs S, U.card ≤ 1 ∨ U = Ustar
  | [], S, _, _, hS => ⟨∅, by simp, fun U hU => Or.inl (hS U hU)⟩
  | g :: gs, S, hlen, h1, hS => by
    have hlen' : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' hg' => hlen g' (List.mem_cons_of_mem g hg')
    let Unew := (gateDeps g).foldl (fun acc i => acc ∪ S.getD i ∅) ∅
    cases hnot : isNotOp g.op
    · have hgs0 : nonNotCountL gs = 0 := by
        have hstep : nonNotCountL (g :: gs) = nonNotCountL gs + 1 := by simp [nonNotCountL, hnot]
        omega
      have hUcard : Unew.card ≤ 2 := by
        have hdeps_len : (gateDeps g).length ≤ 2 := by
          have hg2 := hlen g (List.mem_cons_self ..)
          cases h : g.op <;> simp [gateDeps, h] <;> omega
        have hle := foldl_union_card_le (gateDeps g) (fun i => S.getD i ∅) ∅ (fun i _ => by
          rcases mem_getD_of_ne_empty S i with he | hm
          · rw [he]; simp
          · exact hS _ hm)
        simp only [Finset.card_empty, zero_add] at hle
        dsimp only [Unew]
        omega
      refine ⟨Unew, hUcard, foldSupp_zero_nonNot Unew gs (S ++ [Unew]) hgs0 ?_⟩
      intro U hU
      rcases List.mem_append.mp hU with h1' | h2'
      · exact Or.inl (hS U h1')
      · exact Or.inr (List.mem_singleton.mp h2')
    · have hgs1 : nonNotCountL gs ≤ 1 := by simpa [nonNotCountL, hnot] using h1
      have hop : g.op = GateOp.not := eq_not_of_isNotOp hnot
      have hUcard : Unew.card ≤ 1 := by
        dsimp only [Unew, gateDeps]
        rw [hop]
        cases hin : g.inputs with
        | nil => simp
        | cons k ks =>
          simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil,
            Finset.empty_union]
          rcases mem_getD_of_ne_empty S k with he | hm
          · rw [he]; simp
          · exact hS _ hm
      apply foldSupp_le_one_nonNot gs (S ++ [Unew]) hlen' hgs1
      intro U hU
      rcases List.mem_append.mp hU with h1' | h2'
      · exact hS U h1'
      · rw [List.mem_singleton.mp h2']; exact hUcard

lemma initSupp_card_le_one (n : ℕ) : ∀ U ∈ initSupp n, U.card ≤ 1 := by
  intro U hU
  dsimp only [initSupp] at hU
  rcases List.mem_append.mp hU with h1 | h2
  · rcases List.mem_map.mp h1 with ⟨u, _, rfl⟩; simp
  · simp at h2; rcases h2 with rfl | rfl <;> simp

/-! ### Part 3: Lower bound proof -/

lemma cover_allExcept_singleton {n : ℕ} (G : Finset (Fin n × Fin n))
    (hltG : ∀ e ∈ G, e.1 < e.2) (v : Fin n) :
    ∀ e ∈ G, (fun u => decide (u ≠ v)) e.1 = true ∨ (fun u => decide (u ≠ v)) e.2 = true := by
  intro e he
  have hne : e.1 ≠ e.2 := ne_of_lt (hltG e he)
  by_cases h1 : e.1 = v
  · right; simp [h1 ▸ hne.symm]
  · left; simp [h1]

lemma cover_allTrue {n : ℕ} (G : Finset (Fin n × Fin n)) :
    ∀ e ∈ G, (fun _ : Fin n => true) e.1 = true ∨ (fun _ : Fin n => true) e.2 = true :=
  fun _ _ => Or.inl rfl

lemma allExcept_le_allTrue {n : ℕ} (S : Finset (Fin n)) (i : ℕ) :
    (List.ofFn (fun u : Fin n => decide (u ∉ S)) ++ [false, true]).getD i false ≤
    (List.ofFn (fun _ : Fin n => true) ++ [false, true]).getD i false := by
  by_cases hi : i < n
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simp [hi]), List.getElem?_append_left (by simp [hi]),
        List.getElem?_ofFn, List.getElem?_ofFn, dif_pos hi, dif_pos hi]
    exact Bool.le_true _
  · have h1 : (List.ofFn (fun u : Fin n => decide (u ∉ S))).length ≤ i := by simp; omega
    have h2 : (List.ofFn (fun _ : Fin n => true)).length ≤ i := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right h1, List.getElem?_append_right h2]
    simp

lemma lower_bound {n : ℕ} (G : Finset (Fin n × Fin n)) (a b c : Fin n)
    (hltG : ∀ e ∈ G, e.1 < e.2) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (s r : ℕ)
    (C : Circuit) (p q : Fin (n + 2 + C.size))
    (hfit : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (hsize : C.size ≤ s) (hnot : PEqualNP.NotBracket.notCount C ≤ r)
    (hspec : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
      let w := C.wires (List.ofFn x ++ [false, true])
      w.getD p.val false = xor (x a) (x b) ∧ w.getD q.val false = xor (x b) (x c)) :
    (4 ≤ s ∧ 2 ≤ r) ∨ (((a, c) ∈ G ∨ (c, a) ∈ G) ∧ 5 ≤ s ∧ 1 ≤ r) := by
  let xT : Fin n → Bool := fun _ => true
  let xA : Fin n → Bool := fun u => decide (u ≠ a)
  let xB : Fin n → Bool := fun u => decide (u ≠ b)
  let xC : Fin n → Bool := fun u => decide (u ≠ c)
  let inpT := List.ofFn xT ++ [false, true]
  let inpA := List.ofFn xA ++ [false, true]
  let inpB := List.ofFn xB ++ [false, true]
  let inpC := List.ofFn xC ++ [false, true]
  have hcovT := cover_allTrue G
  have hcovA := cover_allExcept_singleton G hltG a
  have hcovB := cover_allExcept_singleton G hltG b
  have hcovC := cover_allExcept_singleton G hltG c
  have hpT : (C.wires inpT).getD p.val false = false := by
    have := (hspec xT hcovT).1; simpa [xT, inpT] using this
  have hqT : (C.wires inpT).getD q.val false = false := by
    have := (hspec xT hcovT).2; simpa [xT, inpT] using this
  have hpA : (C.wires inpA).getD p.val false = true := by
    have := (hspec xA hcovA).1; simpa [xA, inpA, hab.symm] using this
  have hqA : (C.wires inpA).getD q.val false = false := by
    have := (hspec xA hcovA).2; simpa [xA, inpA, hab.symm, hac.symm] using this
  have hpB : (C.wires inpB).getD p.val false = true := by
    have := (hspec xB hcovB).1; simpa [xB, inpB, hab] using this
  have hqB : (C.wires inpB).getD q.val false = true := by
    have := (hspec xB hcovB).2; simpa [xB, inpB, hbc.symm] using this
  have hpC : (C.wires inpC).getD p.val false = false := by
    have := (hspec xC hcovC).1; simpa [xC, inpC, hac, hbc] using this
  have hqC : (C.wires inpC).getD q.val false = true := by
    have := (hspec xC hcovC).2; simpa [xC, inpC, hbc] using this
  have hfit_op : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
    fun g hg => (hfit g hg).1
  have hfit_len : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hfit g hg).2
  have hnc_eq := notCountL_eq_notCount C
  -- Fact 1: notCountL C.gates >= 1
  have hnc_pos : 1 ≤ notCountL C.gates := by
    by_contra h0
    have hzero : notCountL C.gates = 0 := by omega
    have hleA : ∀ i, inpA.getD i false ≤ inpT.getD i false := by
      intro i
      simpa [inpA, inpT, xA, xT] using allExcept_le_allTrue ({a} : Finset (Fin n)) i
    have hmono := evalWires_mono_of_zero_not C.gates hfit_op hzero inpA inpT (by simp [inpA, inpT]) hleA p.val
    change (C.wires inpA).getD p.val false ≤ (C.wires inpT).getD p.val false at hmono
    rw [hpA, hpT] at hmono
    exact absurd hmono (by decide)
  -- Split on whether notCountL C.gates >= 2 or = 1
  by_cases hnc2 : 2 ≤ notCountL C.gates
  · -- Case 2 <= notCount: prove 4 <= C.size
    left
    refine ⟨?_, by omega⟩
    have h4 : 4 ≤ C.gates.length := by
      by_contra hlt4
      have hnn1 : nonNotCountL C.gates ≤ 1 := by
        have hsum := nonNot_add_not C.gates; omega
      rcases foldSupp_le_one_nonNot C.gates (initSupp n) hfit_len hnn1 (initSupp_card_le_one n) with
        ⟨Ustar, hUcard, hUall⟩
      have hmem_supp : ∀ w (v : Fin n),
          (C.wires (List.ofFn (fun u => decide (u ≠ v)) ++ [false, true])).getD w false ≠
          (C.wires inpT).getD w false →
          v ∈ (foldSupp C.gates (initSupp n)).getD w ∅ := by
        intro w v hne
        by_contra hnotv
        apply hne
        apply wire_agree_of_supp C (fun u => decide (u ≠ v)) xT w
        intro u hu
        have huv : u ≠ v := fun h => hnotv (h ▸ hu)
        simp [xT, huv]
      let Sp := (foldSupp C.gates (initSupp n)).getD p.val ∅
      let Sq := (foldSupp C.gates (initSupp n)).getD q.val ∅
      have haSp : a ∈ Sp := hmem_supp p.val a (by rw [hpA, hpT]; decide)
      have hbSp : b ∈ Sp := hmem_supp p.val b (by rw [hpB, hpT]; decide)
      have hbSq : b ∈ Sq := hmem_supp q.val b (by rw [hqB, hqT]; decide)
      have hcSq : c ∈ Sq := hmem_supp q.val c (by rw [hqC, hqT]; decide)
      have hSp_ge2 : 2 ≤ Sp.card := by
        have hsub : ({a, b} : Finset (Fin n)) ⊆ Sp := by
          intro u hu; simp at hu; rcases hu with rfl | rfl <;> assumption
        have h2 : ({a, b} : Finset (Fin n)).card = 2 := Finset.card_pair hab
        exact h2 ▸ Finset.card_le_card hsub
      have hSq_ge2 : 2 ≤ Sq.card := by
        have hsub : ({b, c} : Finset (Fin n)) ⊆ Sq := by
          intro u hu; simp at hu; rcases hu with rfl | rfl <;> assumption
        have h2 : ({b, c} : Finset (Fin n)).card = 2 := Finset.card_pair hbc
        exact h2 ▸ Finset.card_le_card hsub
      have hSp_eq : Sp = Ustar := by
        rcases mem_getD_of_ne_empty (foldSupp C.gates (initSupp n)) p.val with he | hm
        · change Sp = ∅ at he; rw [he] at hSp_ge2; simp at hSp_ge2
        · rcases hUall Sp hm with hc1 | heq
          · omega
          · exact heq
      have hSq_eq : Sq = Ustar := by
        rcases mem_getD_of_ne_empty (foldSupp C.gates (initSupp n)) q.val with he | hm
        · change Sq = ∅ at he; rw [he] at hSq_ge2; simp at hSq_ge2
        · rcases hUall Sq hm with hc1 | heq
          · omega
          · exact heq
      have hsub3 : ({a, b, c} : Finset (Fin n)) ⊆ Ustar := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact hSp_eq ▸ haSp
        · exact hSp_eq ▸ hbSp
        · exact hSq_eq ▸ hcSq
      have hcard3 : ({a, b, c} : Finset (Fin n)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
      have := Finset.card_le_card hsub3
      omega
    change C.gates.length ≤ s at hsize
    omega
  · -- Case notCount = 1: prove adjacent a c ∧ 5 ≤ s ∧ 1 ≤ r
    have hnc1 : notCountL C.gates = 1 := by omega
    -- Subproof 1: adjacent a c
    have hadj : (a, c) ∈ G ∨ (c, a) ∈ G := by
      by_contra hnotadj
      let xAC : Fin n → Bool := fun u => decide (u ∉ ({a, c} : Finset (Fin n)))
      let inpAC := List.ofFn xAC ++ [false, true]
      have hcovAC : ∀ e ∈ G, xAC e.1 = true ∨ xAC e.2 = true := by
        intro e he
        have hne : e.1 ≠ e.2 := ne_of_lt (hltG e he)
        by_cases h1 : e.1 ∈ ({a, c} : Finset (Fin n))
        · by_cases h2 : e.2 ∈ ({a, c} : Finset (Fin n))
          · exfalso
            simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
            rcases h1 with h1a | h1c <;> rcases h2 with h2a | h2c
            · exact hne (h1a.trans h2a.symm)
            · exact hnotadj (Or.inl (by rwa [← h1a, ← h2c]))
            · exact hnotadj (Or.inr (by rwa [← h1c, ← h2a]))
            · exact hne (h1c.trans h2c.symm)
          · right; exact decide_eq_true h2
        · left; exact decide_eq_true h1
      have hpAC : (C.wires inpAC).getD p.val false = true := by
        have := (hspec xAC hcovAC).1
        simpa [xAC, inpAC, hab.symm, hbc] using this
      have hle1 : ∀ i, inpAC.getD i false ≤ inpC.getD i false := by
        intro i
        by_cases hi : i < n
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by simp [hi]), List.getElem?_append_left (by simp [hi]),
              List.getElem?_ofFn, List.getElem?_ofFn, dif_pos hi, dif_pos hi]
          dsimp only [Option.getD, xAC, xC]
          by_cases hca : (⟨i, hi⟩ : Fin n) = c
          · simp [hca]
          · simp [hca]
        · have h1 : (List.ofFn xAC).length ≤ i := by simp; omega
          have h2 : (List.ofFn xC).length ≤ i := by simp; omega
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_right h1, List.getElem?_append_right h2]
          simp
      have hle2 : ∀ i, inpC.getD i false ≤ inpT.getD i false := by
        intro i
        simpa [inpC, inpT, xC, xT] using allExcept_le_allTrue ({c} : Finset (Fin n)) i
      have hdrop1 : notCode C.gates inpC < notCode C.gates inpAC := by
        rcases notCode_step C.gates hfit_op inpAC inpC (by simp [inpAC, inpC]) hle1 with hlt | ⟨_, hw⟩
        · exact hlt
        · exfalso
          have h := hw p.val
          change (C.wires inpAC).getD p.val false ≤ (C.wires inpC).getD p.val false at h
          rw [hpAC, hpC] at h; exact absurd h (by decide)
      have hdrop2 : notCode C.gates inpT < notCode C.gates inpC := by
        rcases notCode_step C.gates hfit_op inpC inpT (by simp [inpC, inpT]) hle2 with hlt | ⟨_, hw⟩
        · exact hlt
        · exfalso
          have h := hw q.val
          change (C.wires inpC).getD q.val false ≤ (C.wires inpT).getD q.val false at h
          rw [hqC, hqT] at h; exact absurd h (by decide)
      have hlt_top := notCode_lt C.gates inpAC
      rw [hnc1] at hlt_top
      omega
    -- Subproof 2: 5 <= C.gates.length
    right
    refine ⟨hadj, ?_, by omega⟩
    -- Split C.gates = pre ++ [g0] ++ post around the unique NOT gate
    have hex_split : ∃ (pre post : List Gate) (g0 : Gate),
        C.gates = pre ++ [g0] ++ post ∧
        isNotOp g0.op = true ∧ notCountL pre = 0 ∧ notCountL post = 0 := by
      have hgen : ∀ gs : List Gate, notCountL gs = 1 →
          ∃ pre post g0, gs = pre ++ [g0] ++ post ∧
            isNotOp g0.op = true ∧ notCountL pre = 0 ∧ notCountL post = 0 := by
        intro gs
        induction gs with
        | nil => intro h; simp [notCountL] at h
        | cons g gs ih =>
          intro h
          cases hg : isNotOp g.op
          · have hgs : notCountL gs = 1 := by simpa [notCountL, hg] using h
            rcases ih hgs with ⟨pre, post, g0, heq, h0, hpre, hpost⟩
            have hpre' : notCountL (g :: pre) = 0 := by
              have hstep : notCountL (g :: pre) = notCountL pre := by simp [notCountL, hg]
              rw [hstep, hpre]
            refine ⟨g :: pre, post, g0, by simp [heq], h0, hpre', hpost⟩
          · have hgs : notCountL gs = 0 := by
              have hstep : notCountL (g :: gs) = notCountL gs + 1 := by simp [notCountL, hg]
              omega
            exact ⟨[], gs, g, rfl, hg, rfl, hgs⟩
      exact hgen C.gates hnc1
    rcases hex_split with ⟨pre, post, g0, hgs_eq, hg0_not, hpre0, hpost0⟩
    have hg0_op : g0.op = GateOp.not := eq_not_of_isNotOp hg0_not
    let j0 := pre.length
    have hfit_pre : ∀ g ∈ pre, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
      intro g hg; exact hfit_op g (by rw [hgs_eq]; simp [hg])
    have hfit_post : ∀ g ∈ post, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
      intro g hg; exact hfit_op g (by rw [hgs_eq]; simp [hg])
    have hlen_pre : ∀ g ∈ pre, g.inputs.length ≤ 2 := by
      intro g hg; exact hfit_len g (by rw [hgs_eq]; simp [hg])
    -- Value of the unique NOT gate at wire n + 2 + j0
    have hval_not_eq : ∀ (x : Fin n → Bool),
        let inp := List.ofFn x ++ [false, true]
        (C.wires inp).getD (n + 2 + j0) false =
        g0.op.eval (g0.inputs.map fun i => (evalWires pre inp).getD i false) := by
      intro x
      dsimp only
      change (evalWires C.gates (List.ofFn x ++ [false, true])).getD (n + 2 + j0) false = _
      rw [hgs_eq]
      have hlen1 : (List.ofFn x ++ [false, true]).length + (pre ++ [g0]).length = n + 2 + j0 + 1 := by
        simp [j0]; omega
      rw [evalWires_getD_prefix (pre ++ [g0]) post _ (n + 2 + j0) (by omega), evalWires_append]
      set ws := evalWires pre (List.ofFn x ++ [false, true])
      have hws_len : ws.length = n + 2 + j0 := by
        dsimp only [ws, j0]; rw [evalWires_length]; simp
      change (ws ++ [g0.op.eval (g0.inputs.map fun i => ws.getD i false)]).getD (n + 2 + j0) false = _
      rw [getD_append_singleton, if_neg (by omega), if_pos hws_len.symm]
    -- On x <= xT, if wire (n+2+j0) is equal on x and xT, then all wires of C are monotone
    have hmono_if_not_eq : ∀ (x : Fin n → Bool),
        let inp := List.ofFn x ++ [false, true]
        (∀ i, inp.getD i false ≤ inpT.getD i false) →
        (C.wires inp).getD (n + 2 + j0) false = (C.wires inpT).getD (n + 2 + j0) false →
        ∀ i, (C.wires inp).getD i false ≤ (C.wires inpT).getD i false := by
      intro x
      dsimp only
      intro hle hneq i
      change (evalWires C.gates (List.ofFn x ++ [false, true])).getD i false ≤
        (evalWires C.gates inpT).getD i false
      rw [hgs_eq, evalWires_append, evalWires_append, evalWires_append, evalWires_append]
      apply evalWires_mono_of_zero_not post hfit_post hpost0
      · simp [evalWires_length, inpT]
      · have hpre_m := evalWires_mono_of_zero_not pre hfit_pre hpre0
          (List.ofFn x ++ [false, true]) inpT (by simp [inpT]) hle
        have hlen_p : (evalWires pre (List.ofFn x ++ [false, true])).length =
            (evalWires pre inpT).length := by simp [evalWires_length, inpT]
        have hval_eq : g0.op.eval (g0.inputs.map fun k => (evalWires pre (List.ofFn x ++ [false, true])).getD k false) =
            g0.op.eval (g0.inputs.map fun k => (evalWires pre inpT).getD k false) := by
          rw [← hval_not_eq x, ← hval_not_eq xT]; exact hneq
        exact getD_append_le hlen_p hpre_m (le_of_eq hval_eq)
    -- Show wire (n+2+j0) is anti-monotone on x <= xT
    have hnot_anti : ∀ (x : Fin n → Bool),
        (∀ i, (List.ofFn x ++ [false, true]).getD i false ≤ inpT.getD i false) →
        (C.wires inpT).getD (n + 2 + j0) false ≤ (C.wires (List.ofFn x ++ [false, true])).getD (n + 2 + j0) false := by
      intro x hle
      rw [hval_not_eq x, hval_not_eq xT, hg0_op]
      apply eval_not_anti
      exact evalWires_mono_of_zero_not pre hfit_pre hpre0 _ _ (by simp [inpT]) hle
    have hleA : ∀ i, inpA.getD i false ≤ inpT.getD i false := fun i => by
      simpa [inpA, inpT, xA, xT] using allExcept_le_allTrue ({a} : Finset (Fin n)) i
    have hleB : ∀ i, inpB.getD i false ≤ inpT.getD i false := fun i => by
      simpa [inpB, inpT, xB, xT] using allExcept_le_allTrue ({b} : Finset (Fin n)) i
    have hleC : ∀ i, inpC.getD i false ≤ inpT.getD i false := fun i => by
      simpa [inpC, inpT, xC, xT] using allExcept_le_allTrue ({c} : Finset (Fin n)) i
    have hg0_AT : (C.wires inpA).getD (n + 2 + j0) false ≠ (C.wires inpT).getD (n + 2 + j0) false := by
      intro heq
      have hm := hmono_if_not_eq xA hleA heq p.val
      rw [hpA, hpT] at hm; exact absurd hm (by decide)
    have hg0_BT : (C.wires inpB).getD (n + 2 + j0) false ≠ (C.wires inpT).getD (n + 2 + j0) false := by
      intro heq
      have hm := hmono_if_not_eq xB hleB heq p.val
      rw [hpB, hpT] at hm; exact absurd hm (by decide)
    have hg0_CT : (C.wires inpC).getD (n + 2 + j0) false ≠ (C.wires inpT).getD (n + 2 + j0) false := by
      intro heq
      have hm := hmono_if_not_eq xC hleC heq q.val
      rw [hqC, hqT] at hm; exact absurd hm (by decide)
    have hg0_T_false : (C.wires inpT).getD (n + 2 + j0) false = false := by
      have ha := hnot_anti xA hleA
      revert ha hg0_AT
      cases (C.wires inpT).getD (n + 2 + j0) false <;>
        cases (C.wires inpA).getD (n + 2 + j0) false <;> decide
    have hg0_A_true : (C.wires inpA).getD (n + 2 + j0) false = true := by
      cases h : (C.wires inpA).getD (n + 2 + j0) false
      · exact absurd (h.trans hg0_T_false.symm) hg0_AT
      · rfl
    have hg0_B_true : (C.wires inpB).getD (n + 2 + j0) false = true := by
      cases h : (C.wires inpB).getD (n + 2 + j0) false
      · exact absurd (h.trans hg0_T_false.symm) hg0_BT
      · rfl
    have hg0_C_true : (C.wires inpC).getD (n + 2 + j0) false = true := by
      cases h : (C.wires inpC).getD (n + 2 + j0) false
      · exact absurd (h.trans hg0_T_false.symm) hg0_CT
      · rfl
    -- Fact A: 2 <= j0
    have hj0_ge2 : 2 ≤ j0 := by
      by_contra hlt2
      have hpre_len : pre.length ≤ 1 := by dsimp only [j0] at hlt2; omega
      have hpre_nn : nonNotCountL pre ≤ 1 := by
        have := nonNot_add_not pre; omega
      let Cpre : Circuit := ⟨pre ++ [g0], 0⟩
      have hCpre_nn : nonNotCountL Cpre.gates ≤ 1 := by
        dsimp only [Cpre]; rw [nonNotCountL_append]; simp [nonNotCountL, hg0_not]; exact hpre_nn
      have hCpre_len : ∀ g ∈ Cpre.gates, g.inputs.length ≤ 2 := by
        intro g hg
        dsimp only [Cpre] at hg
        exact hfit_len g (by rw [hgs_eq]; exact List.mem_append_left post hg)
      rcases foldSupp_le_one_nonNot Cpre.gates (initSupp n) hCpre_len hCpre_nn
        (initSupp_card_le_one n) with ⟨Ustar, hUcard, hUall⟩
      let S0 := (foldSupp Cpre.gates (initSupp n)).getD (n + 2 + j0) ∅
      have hCpre_val : ∀ x : Fin n → Bool,
          (Cpre.wires (List.ofFn x ++ [false, true])).getD (n + 2 + j0) false =
          (C.wires (List.ofFn x ++ [false, true])).getD (n + 2 + j0) false := by
        intro x
        change (evalWires (pre ++ [g0]) _).getD (n + 2 + j0) false =
          (evalWires C.gates _).getD (n + 2 + j0) false
        rw [hgs_eq, evalWires_getD_prefix (pre ++ [g0]) post _ (n + 2 + j0) (by simp [j0])]
      have hmem0 : ∀ v : Fin n,
          (C.wires (List.ofFn (fun u => decide (u ≠ v)) ++ [false, true])).getD (n + 2 + j0) false ≠
          (C.wires inpT).getD (n + 2 + j0) false → v ∈ S0 := by
        intro v hne
        by_contra hnotv
        apply hne
        rw [← hCpre_val (fun u => decide (u ≠ v)), ← hCpre_val xT]
        apply wire_agree_of_supp Cpre (fun u => decide (u ≠ v)) xT (n + 2 + j0)
        intro u hu
        have huv : u ≠ v := fun h => hnotv (h ▸ hu)
        simp [xT, huv]
      have ha0 : a ∈ S0 := hmem0 a hg0_AT
      have hb0 : b ∈ S0 := hmem0 b hg0_BT
      have hc0 : c ∈ S0 := hmem0 c hg0_CT
      have hsub3 : ({a, b, c} : Finset (Fin n)) ⊆ S0 := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl <;> assumption
      have hcard3 : ({a, b, c} : Finset (Fin n)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
      have hS0_ge3 : 3 ≤ S0.card := hcard3 ▸ Finset.card_le_card hsub3
      rcases mem_getD_of_ne_empty (foldSupp Cpre.gates (initSupp n)) (n + 2 + j0) with he | hm
      · change S0 = ∅ at he; rw [he] at hS0_ge3; simp at hS0_ge3
      · rcases hUall S0 hm with hc1 | heq
        · omega
        · rw [heq] at hS0_ge3; omega
    -- Fact B: n + 2 + j0 < p.val, n + 2 + j0 < q.val, p.val != q.val
    have hp_gt : n + 2 + j0 < p.val := by
      by_contra hle
      by_cases heq : p.val = n + 2 + j0
      · rw [heq, hg0_C_true] at hpC; exact Bool.false_ne_true hpC.symm
      · have hlt : p.val < n + 2 + j0 := by omega
        have hpreA : (C.wires inpA).getD p.val false = (evalWires pre inpA).getD p.val false := by
          change (evalWires C.gates inpA).getD p.val false = _
          rw [hgs_eq, List.append_assoc, evalWires_getD_prefix pre ([g0] ++ post) inpA p.val (by simp [inpA, j0]; omega)]
        have hpreT : (C.wires inpT).getD p.val false = (evalWires pre inpT).getD p.val false := by
          change (evalWires C.gates inpT).getD p.val false = _
          rw [hgs_eq, List.append_assoc, evalWires_getD_prefix pre ([g0] ++ post) inpT p.val (by simp [inpT, j0]; omega)]
        have hm := evalWires_mono_of_zero_not pre hfit_pre hpre0 inpA inpT (by simp [inpA, inpT]) hleA p.val
        rw [← hpreA, ← hpreT, hpA, hpT] at hm
        exact absurd hm (by decide)
    have hq_gt : n + 2 + j0 < q.val := by
      by_contra hle
      by_cases heq : q.val = n + 2 + j0
      · rw [heq, hg0_A_true] at hqA; exact Bool.false_ne_true hqA.symm
      · have hlt : q.val < n + 2 + j0 := by omega
        have hpreC : (C.wires inpC).getD q.val false = (evalWires pre inpC).getD q.val false := by
          change (evalWires C.gates inpC).getD q.val false = _
          rw [hgs_eq, List.append_assoc, evalWires_getD_prefix pre ([g0] ++ post) inpC q.val (by simp [inpC, j0]; omega)]
        have hpreT : (C.wires inpT).getD q.val false = (evalWires pre inpT).getD q.val false := by
          change (evalWires C.gates inpT).getD q.val false = _
          rw [hgs_eq, List.append_assoc, evalWires_getD_prefix pre ([g0] ++ post) inpT q.val (by simp [inpT, j0]; omega)]
        have hm := evalWires_mono_of_zero_not pre hfit_pre hpre0 inpC inpT (by simp [inpC, inpT]) hleC q.val
        rw [← hpreC, ← hpreT, hqC, hqT] at hm
        exact absurd hm (by decide)
    have hpq_ne : p.val ≠ q.val := by
      intro heq
      rw [heq, hqA] at hpA
      exact Bool.false_ne_true hpA
    have hp_lt := p.isLt
    have hq_lt := q.isLt
    have _ := hrb
    change C.gates.length ≤ s at hsize
    change p.val < n + 2 + C.gates.length at hp_lt
    change q.val < n + 2 + C.gates.length at hq_lt
    omega

/-! ### Part 4: Explicit upper bound circuits -/

lemma input_getD {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    (List.ofFn x ++ [false, true]).getD u.val false = x u := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [u.isLt]),
      List.getElem?_ofFn, dif_pos u.isLt]
  rfl

lemma upper_four_two {n : ℕ} (G : Finset (Fin n × Fin n)) (a b c : Fin n)
    (hadjAB : (a, b) ∈ G ∨ (b, a) ∈ G) (hadjBC : (b, c) ∈ G ∨ (c, b) ∈ G)
    {s r : ℕ} (hs : 4 ≤ s) (hr : 2 ≤ r) :
    ∃ (C : Circuit) (p q : Fin (n + 2 + C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
      C.output = p.val ∧ C.size ≤ s ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
        let w := C.wires (List.ofFn x ++ [false, true])
        w.getD p.val false = xor (x a) (x b) ∧ w.getD q.val false = xor (x b) (x c) := by
  let g0 : Gate := ⟨GateOp.and, [a.val, b.val]⟩
  let g1 : Gate := ⟨GateOp.not, [n + 2]⟩
  let g2 : Gate := ⟨GateOp.and, [b.val, c.val]⟩
  let g3 : Gate := ⟨GateOp.not, [n + 4]⟩
  let C : Circuit := ⟨[g0, g1, g2, g3], n + 3⟩
  have hCsize : C.size = 4 := rfl
  refine ⟨C, ⟨n + 3, by simp [hCsize]⟩, ⟨n + 5, by simp [hCsize]⟩, ?_, ?_, rfl, by omega, ?_, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp [g0, g1, g2, g3]
  · intro j hj i hi
    have hj4 : j < 4 := hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, C, g0] at hi
      rcases hi with rfl | rfl <;> [exact lt_trans a.isLt (by omega); exact lt_trans b.isLt (by omega)]
    · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, C, g1] at hi; omega
    · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, C, g2] at hi
      rcases hi with rfl | rfl <;> [exact lt_trans b.isLt (by omega); exact lt_trans c.isLt (by omega)]
    · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, C, g3] at hi; omega
  · have hnc : PEqualNP.NotBracket.notCount C = 2 := by
      rw [← notCountL_eq_notCount C]
      simp [notCountL, C, g0, g1, g2, g3, isNotOp]
    omega
  · intro x hcov
    have hAB : x a = true ∨ x b = true := by
      rcases hadjAB with h | h
      · exact hcov (a, b) h
      · exact (hcov (b, a) h).symm
    have hBC : x b = true ∨ x c = true := by
      rcases hadjBC with h | h
      · exact hcov (b, c) h
      · exact (hcov (c, b) h).symm
    set inp := List.ofFn x ++ [false, true]
    have hlen0 : inp.length = n + 2 := by simp [inp]
    have ha : inp.getD a.val false = x a := input_getD x a
    have hb : inp.getD b.val false = x b := input_getD x b
    have hc : inp.getD c.val false = x c := input_getD x c
    have hw : C.wires inp = inp ++ [x a && x b, !(x a && x b), x b && x c, !(x b && x c)] := by
      dsimp only [Circuit.wires, C, g0, g1, g2, g3]
      simp only [List.foldl_cons, List.foldl_nil, GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, List.headD_cons, id_eq, Bool.and_true]
      rw [ha, hb]
      have h1 : (inp ++ [x a && x b]).getD (n + 2) false = (x a && x b) := by
        rw [getD_append_singleton, hlen0]; simp
      have h2b : ((inp ++ [x a && x b]) ++ [!(x a && x b)]).getD b.val false = x b := by
        rw [getD_append_singleton, if_pos (by simp [hlen0]; have := b.isLt; omega),
            getD_append_singleton, if_pos (by rw [hlen0]; have := b.isLt; omega), hb]
      have h2c : ((inp ++ [x a && x b]) ++ [!(x a && x b)]).getD c.val false = x c := by
        rw [getD_append_singleton, if_pos (by simp [hlen0]; have := c.isLt; omega),
            getD_append_singleton, if_pos (by rw [hlen0]; have := c.isLt; omega), hc]
      have h3 : (((inp ++ [x a && x b]) ++ [!(x a && x b)]) ++ [x b && x c]).getD (n + 4) false =
          (x b && x c) := by
        rw [getD_append_singleton]; simp [hlen0]
      rw [h1, h2b, h2c, h3]
      simp [List.append_assoc]
    dsimp only
    rw [hw]
    have hget3 : (inp ++ [x a && x b, !(x a && x b), x b && x c, !(x b && x c)]).getD (n + 3) false =
        !(x a && x b) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen0]
      have : n + 3 - (n + 2) = 1 := by omega
      rw [this]; rfl
    have hget5 : (inp ++ [x a && x b, !(x a && x b), x b && x c, !(x b && x c)]).getD (n + 5) false =
        !(x b && x c) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen0]
      have : n + 5 - (n + 2) = 3 := by omega
      rw [this]; rfl
    rw [hget3, hget5]
    constructor
    · cases hxa : x a <;> cases hxb : x b <;> simp_all
    · cases hxb : x b <;> cases hxc : x c <;> simp_all

lemma upper_five_one {n : ℕ} (G : Finset (Fin n × Fin n)) (a b c : Fin n)
    (hadjAB : (a, b) ∈ G ∨ (b, a) ∈ G) (hadjBC : (b, c) ∈ G ∨ (c, b) ∈ G)
    (hadjAC : (a, c) ∈ G ∨ (c, a) ∈ G)
    {s r : ℕ} (hs : 5 ≤ s) (hr : 1 ≤ r) :
    ∃ (C : Circuit) (p q : Fin (n + 2 + C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
      C.output = p.val ∧ C.size ≤ s ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
        let w := C.wires (List.ofFn x ++ [false, true])
        w.getD p.val false = xor (x a) (x b) ∧ w.getD q.val false = xor (x b) (x c) := by
  let g0 : Gate := ⟨GateOp.and, [a.val, b.val]⟩
  let g1 : Gate := ⟨GateOp.and, [n + 2, c.val]⟩
  let g2 : Gate := ⟨GateOp.not, [n + 3]⟩
  let g3 : Gate := ⟨GateOp.and, [n + 4, c.val]⟩
  let g4 : Gate := ⟨GateOp.and, [n + 4, a.val]⟩
  let C : Circuit := ⟨[g0, g1, g2, g3, g4], n + 5⟩
  have hCsize : C.size = 5 := rfl
  refine ⟨C, ⟨n + 5, by simp [hCsize]⟩, ⟨n + 6, by simp [hCsize]⟩, ?_, ?_, rfl, by omega, ?_, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp [g0, g1, g2, g3, g4]
  · intro j hj i hi
    have hj5 : j < 5 := hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, C, g0] at hi
      rcases hi with rfl | rfl <;> [exact lt_trans a.isLt (by omega); exact lt_trans b.isLt (by omega)]
    · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, C, g1] at hi
      rcases hi with rfl | rfl <;> [omega; exact lt_trans c.isLt (by omega)]
    · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, C, g2] at hi; omega
    · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, C, g3] at hi
      rcases hi with rfl | rfl <;> [omega; exact lt_trans c.isLt (by omega)]
    · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, C, g4] at hi
      rcases hi with rfl | rfl <;> [omega; exact lt_trans a.isLt (by omega)]
  · have hnc : PEqualNP.NotBracket.notCount C = 1 := by
      rw [← notCountL_eq_notCount C]
      simp [notCountL, C, g0, g1, g2, g3, g4, isNotOp]
    omega
  · intro x hcov
    have hAB : x a = true ∨ x b = true := by
      rcases hadjAB with h | h
      · exact hcov (a, b) h
      · exact (hcov (b, a) h).symm
    have hBC : x b = true ∨ x c = true := by
      rcases hadjBC with h | h
      · exact hcov (b, c) h
      · exact (hcov (c, b) h).symm
    have hAC : x a = true ∨ x c = true := by
      rcases hadjAC with h | h
      · exact hcov (a, c) h
      · exact (hcov (c, a) h).symm
    set inp := List.ofFn x ++ [false, true]
    have hlen0 : inp.length = n + 2 := by simp [inp]
    have ha : inp.getD a.val false = x a := input_getD x a
    have hb : inp.getD b.val false = x b := input_getD x b
    have hc : inp.getD c.val false = x c := input_getD x c
    set v0 := x a && x b
    set v1 := v0 && x c
    set v2 := !v1
    set v3 := v2 && x c
    set v4 := v2 && x a
    have hw : C.wires inp = inp ++ [v0, v1, v2, v3, v4] := by
      dsimp only [Circuit.wires, C, g0, g1, g2, g3, g4]
      simp only [List.foldl_cons, List.foldl_nil, GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, List.headD_cons, id_eq, Bool.and_true]
      rw [ha, hb]
      change ((((inp ++ [v0]) ++ [((inp ++ [v0]).getD (n + 2) false && (inp ++ [v0]).getD c.val false)]) ++
        [!(((inp ++ [v0]) ++ [((inp ++ [v0]).getD (n + 2) false && (inp ++ [v0]).getD c.val false)]).getD (n + 3) false)]) ++
        [((((inp ++ [v0]) ++ [((inp ++ [v0]).getD (n + 2) false && (inp ++ [v0]).getD c.val false)]) ++
          [!(((inp ++ [v0]) ++ [((inp ++ [v0]).getD (n + 2) false && (inp ++ [v0]).getD c.val false)]).getD (n + 3) false)]).getD (n + 4) false &&
          (((inp ++ [v0]) ++ [((inp ++ [v0]).getD (n + 2) false && (inp ++ [v0]).getD c.val false)]) ++
          [!(((inp ++ [v0]) ++ [((inp ++ [v0]).getD (n + 2) false && (inp ++ [v0]).getD c.val false)]).getD (n + 3) false)]).getD c.val false)]) ++
        [_] = _
      have h1a : (inp ++ [v0]).getD (n + 2) false = v0 := by
        rw [getD_append_singleton, hlen0]; simp
      have h1c : (inp ++ [v0]).getD c.val false = x c := by
        rw [getD_append_singleton, if_pos (by rw [hlen0]; have := c.isLt; omega), hc]
      rw [h1a, h1c]
      have h2 : ((inp ++ [v0]) ++ [v1]).getD (n + 3) false = v1 := by
        rw [getD_append_singleton]; simp [hlen0]
      rw [h2]
      have h3a : (((inp ++ [v0]) ++ [v1]) ++ [v2]).getD (n + 4) false = v2 := by
        rw [getD_append_singleton]; simp [hlen0]
      have h3c : (((inp ++ [v0]) ++ [v1]) ++ [v2]).getD c.val false = x c := by
        rw [getD_append_singleton, if_pos (by simp [hlen0]; have := c.isLt; omega),
            getD_append_singleton, if_pos (by simp [hlen0]; have := c.isLt; omega),
            getD_append_singleton, if_pos (by rw [hlen0]; have := c.isLt; omega), hc]
      rw [h3a, h3c]
      have h4a : ((((inp ++ [v0]) ++ [v1]) ++ [v2]) ++ [v3]).getD (n + 4) false = v2 := by
        rw [getD_append_singleton, if_pos (by simp [hlen0]), h3a]
      have h4x : ((((inp ++ [v0]) ++ [v1]) ++ [v2]) ++ [v3]).getD a.val false = x a := by
        rw [getD_append_singleton, if_pos (by simp [hlen0]; have := a.isLt; omega),
            getD_append_singleton, if_pos (by simp [hlen0]; have := a.isLt; omega),
            getD_append_singleton, if_pos (by simp [hlen0]; have := a.isLt; omega),
            getD_append_singleton, if_pos (by rw [hlen0]; have := a.isLt; omega), ha]
      rw [h4a, h4x]
      simp [List.append_assoc, v4, v3, v2, v1]
    dsimp only
    rw [hw]
    have hget5 : (inp ++ [v0, v1, v2, v3, v4]).getD (n + 5) false = v3 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen0]
      have : n + 5 - (n + 2) = 3 := by omega
      rw [this]; rfl
    have hget6 : (inp ++ [v0, v1, v2, v3, v4]).getD (n + 6) false = v4 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen0]
      have : n + 6 - (n + 2) = 4 := by omega
      rw [this]; rfl
    rw [hget5, hget6]
    dsimp only [v3, v4, v2, v1, v0]
    constructor
    · cases hxa : x a <;> cases hxb : x b <;> cases hxc : x c <;> simp_all
    · cases hxa : x a <;> cases hxb : x b <;> cases hxc : x c <;> simp_all

theorem main :
    ∀ n : Nat, ∀ (G : Finset (Fin n × Fin n)) (a b c : Fin n),
      (∀ e ∈ G, e.1 < e.2) → a ≠ b → b ≠ c → a ≠ c →
      let adjacent := fun u v : Fin n => (u,v) ∈ G ∨ (v,u) ∈ G
      adjacent a b → adjacent b c → ∀ s r : Nat,
        (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (p q : Fin (n+2+C.size)),
          PEqualNP.MetaComplexity.FanInTwo C ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
          C.output = p.val ∧ C.size ≤ s ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
          ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1=true ∨ x e.2=true) →
            let w := C.wires (List.ofFn x ++ [false,true])
            w.getD p.val false = xor (x a) (x b) ∧ w.getD q.val false = xor (x b) (x c)) ↔
        (4 ≤ s ∧ 2 ≤ r) ∨ (adjacent a c ∧ 5 ≤ s ∧ 1 ≤ r) := by
  intro n G a b c hltG hab hbc hac
  dsimp only
  intro hadjAB hadjBC s r
  constructor
  · rintro ⟨C, p, q, hfit, hrb, _, hsize, hnot, hspec⟩
    exact lower_bound G a b c hltG hab hbc hac s r C p q hfit hrb hsize hnot hspec
  · rintro (⟨hs, hr⟩ | ⟨hadjAC, hs, hr⟩)
    · exact upper_four_two G a b c hadjAB hadjBC hs hr
    · exact upper_five_one G a b c hadjAB hadjBC hadjAC hs hr

end PEqualNP.Outside.L_lib_1188_aux

theorem PEqualNP.Outside.L_lib_1188 :
∀ n : Nat, ∀ (G : Finset (Fin n × Fin n)) (a b c : Fin n),
  (∀ e ∈ G, e.1 < e.2) → a ≠ b → b ≠ c → a ≠ c →
  let adjacent := fun u v : Fin n => (u,v) ∈ G ∨ (v,u) ∈ G
  adjacent a b → adjacent b c → ∀ s r : Nat,
    (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (p q : Fin (n+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output = p.val ∧ C.size ≤ s ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1=true ∨ x e.2=true) →
        let w := C.wires (List.ofFn x ++ [false,true])
        w.getD p.val false = xor (x a) (x b) ∧ w.getD q.val false = xor (x b) (x c)) ↔
    (4 ≤ s ∧ 2 ≤ r) ∨ (adjacent a c ∧ 5 ≤ s ∧ 1 ≤ r) :=
  PEqualNP.Outside.L_lib_1188_aux.main
