import Mathlib
import PEqualNP.Defs






namespace PEqualNP.Outside.L_meta_50718_aux

open PEqualNP.CircuitLowerBounds

/-! Kit of tools/taps_row.py for the three-ordered-outputs rows of the exceed kind.
A wire is the vector of its values on the `T` input words: a number below `2 ^ T`, bit `t` = its value at level `t`
(`F = 2 ^ T - 1`). A circuit adds one vector per gate to the set of the input vectors; `ok` is the exhaustive search
over such sets (a bit mask `S`: bit `v` = vector `v` is present), cut off when more targets are missing than gates
are left. `core`: a circuit that puts the three targets on wires makes `ok` true. -/

def vop (F : ℕ) : GateOp → List ℕ → ℕ
  | GateOp.and, l => l.foldr (fun a r => a &&& r) F
  | GateOp.or, l => l.foldr (fun a r => a ||| r) 0
  | GateOp.not, l => l.headD 0 ^^^ F
  | _, _ => 0

def step (F : ℕ) (w : List ℕ) (g : Gate) : List ℕ := w ++ [vop F g.op (g.inputs.map fun i => w.getD i 0)]

def sim (F : ℕ) (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (step F) w

def AON (o : GateOp) : Prop := o = GateOp.and ∨ o = GateOp.or ∨ o = GateOp.not

theorem all_bit (F t : ℕ) (hF : F.testBit t = true) (l : List ℕ) :
    (l.map fun v => v.testBit t).all id = (l.foldr (fun a r => a &&& r) F).testBit t := by
  induction l with
  | nil => simp [hF]
  | cons a l ih => simp only [List.map_cons, List.all_cons, List.foldr_cons, Nat.testBit_and, id]; rw [ih]

theorem any_bit (t : ℕ) (l : List ℕ) :
    (l.map fun v => v.testBit t).any id = (l.foldr (fun a r => a ||| r) 0).testBit t := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.any_cons, List.foldr_cons, Nat.testBit_or, id]; rw [ih]

theorem vop_bit (F t : ℕ) (hF : F.testBit t = true) (o : GateOp) (ho : AON o) (l : List ℕ) :
    o.eval (l.map fun v => v.testBit t) = (vop F o l).testBit t := by
  rcases ho with rfl | rfl | rfl
  · simp only [GateOp.eval, vop]; exact all_bit F t hF l
  · simp only [GateOp.eval, vop]; exact any_bit t l
  · cases l with
    | nil => simp [GateOp.eval, vop, hF]
    | cons a l => simp [GateOp.eval, vop, Nat.testBit_xor, hF]

theorem getD_bit (t : ℕ) (w : List ℕ) (i : ℕ) :
    (w.map fun v => v.testBit t).getD i false = (w.getD i 0).testBit t := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp

theorem wires_sim (F t : ℕ) (hF : F.testBit t = true) :
    ∀ (gs : List Gate) (w : List ℕ), (∀ g ∈ gs, AON g.op) →
      gs.foldl (fun (x : List Bool) g => x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
          (w.map fun v => v.testBit t)
        = (sim F gs w).map fun v => v.testBit t := by
  intro gs
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w h
    have hg := h g (List.mem_cons_self ..)
    have e : (w.map fun v => v.testBit t) ++
          [g.op.eval (g.inputs.map fun i => (w.map fun v => v.testBit t).getD i false)]
        = (step F w g).map fun v => v.testBit t := by
      have e2 : (g.inputs.map fun i => (w.map fun v => v.testBit t).getD i false)
          = (g.inputs.map fun i => w.getD i 0).map fun v => v.testBit t := by
        rw [List.map_map]; apply List.map_congr_left; intro i _; exact getD_bit t w i
      rw [e2, vop_bit F t hF g.op hg]; simp [step]
    simp only [List.foldl_cons, sim]
    rw [e]
    exact ih (step F w g) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

theorem sim_length (F : ℕ) : ∀ (gs : List Gate) (w : List ℕ), (sim F gs w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp [sim]
  | cons g gs ih => intro w; simp only [sim, List.foldl_cons] at ih ⊢; rw [ih]; simp [step]; omega

theorem and_lt (F T : ℕ) (hF : F < 2 ^ T) : ∀ l : List ℕ, l.foldr (fun a r => a &&& r) F < 2 ^ T := by
  intro l
  induction l with
  | nil => simpa using hF
  | cons a l ih => exact lt_of_le_of_lt Nat.and_le_right ih

theorem or_lt (T : ℕ) : ∀ l : List ℕ, (∀ v ∈ l, v < 2 ^ T) → l.foldr (fun a r => a ||| r) 0 < 2 ^ T := by
  intro l
  induction l with
  | nil => intro _; exact Nat.two_pow_pos T
  | cons a l ih =>
    intro h
    exact Nat.or_lt_two_pow (h a (List.mem_cons_self ..)) (ih fun v hv => h v (List.mem_cons_of_mem _ hv))

theorem vop_lt (F T : ℕ) (hF : F < 2 ^ T) (o : GateOp) (l : List ℕ) (hl : ∀ v ∈ l, v < 2 ^ T) :
    vop F o l < 2 ^ T := by
  cases o with
  | and => exact and_lt F T hF l
  | or => exact or_lt T l hl
  | not =>
    cases l with
    | nil => simpa [vop] using hF
    | cons a l => exact Nat.xor_lt_two_pow (hl a (List.mem_cons_self ..)) hF
  | mod m => exact Nat.two_pow_pos T
  | maj => exact Nat.two_pow_pos T

theorem sim_lt (F T : ℕ) (hF : F < 2 ^ T) :
    ∀ (gs : List Gate) (w : List ℕ), (∀ v ∈ w, v < 2 ^ T) → ∀ v ∈ sim F gs w, v < 2 ^ T := by
  intro gs
  induction gs with
  | nil => intro w hw v hv; exact hw v hv
  | cons g gs ih =>
    intro w hw v hv
    simp only [sim, List.foldl_cons] at hv
    refine ih (step F w g) ?_ v hv
    intro u hu
    simp only [step, List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact hw u hu
    · apply vop_lt F T hF
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨i, _, rfl⟩ := hx
      rw [List.getD_eq_getElem?_getD]
      cases hi : w[i]? with
      | none => exact Nat.two_pow_pos T
      | some y => exact hw y (List.mem_of_getElem? hi)

theorem bit_self (k : ℕ) : (1 <<< k).testBit k = true := by
  rw [Nat.one_shiftLeft]; exact Nat.testBit_two_pow_self

theorem bit_ins (S v x : ℕ) : (S ||| 1 <<< v).testBit x = (S.testBit x || decide (v = x)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem foldl_bit {α : Type} (g : ℕ → α → ℕ) (i : ℕ)
    (hm : ∀ acc x, acc.testBit i = true → (g acc x).testBit i = true) :
    ∀ (l : List α) (acc : ℕ), acc.testBit i = true → (l.foldl g acc).testBit i = true := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons x l ih => intro acc h; exact ih _ (hm acc x h)

theorem foldl_hit {α : Type} (g : ℕ → α → ℕ) (i : ℕ)
    (hm : ∀ acc x, acc.testBit i = true → (g acc x).testBit i = true)
    (x : α) (hx : ∀ acc, (g acc x).testBit i = true) :
    ∀ (l : List α) (acc : ℕ), x ∈ l → (l.foldl g acc).testBit i = true := by
  intro l
  induction l with
  | nil => intro acc h; cases h
  | cons y l ih =>
    intro acc h
    rcases List.mem_cons.1 h with rfl | h
    · exact foldl_bit g i hm l _ (hx acc)
    · exact ih _ h

/-- the vectors one AND or OR gate can make from the present ones -/
def cbIn (F S a : ℕ) (acc : ℕ) : ℕ :=
  (List.range (F + 1)).foldl (fun acc b => bif S.testBit b then
    acc ||| (1 <<< (a &&& (b &&& F))) ||| (1 <<< (a ||| (b ||| 0))) else acc) acc

def cb (F S : ℕ) : ℕ :=
  (List.range (F + 1)).foldl (fun acc a => bif S.testBit a then cbIn F S a acc else acc) 0

/-- the vectors one NOT gate can make -/
def cn (F S : ℕ) : ℕ :=
  (List.range (F + 1)).foldl (fun acc a => bif S.testBit a then acc ||| (1 <<< (a ^^^ F)) else acc) 0

theorem cbIn_mono (F S a i : ℕ) (acc : ℕ) (h : acc.testBit i = true) : (cbIn F S a acc).testBit i = true := by
  apply foldl_bit _ i _ _ _ h
  intro acc b hacc
  cases hb : S.testBit b <;> simp [Nat.testBit_or, hacc]

theorem cb_and (F S a b : ℕ) (ha : a ≤ F) (hb : b ≤ F) (hSa : S.testBit a = true) (hSb : S.testBit b = true) :
    (cb F S).testBit (a &&& (b &&& F)) = true := by
  apply foldl_hit _ _ _ a _ _ _ (List.mem_range.2 (by omega))
  · intro acc x hacc
    cases hx : S.testBit x
    · simpa using hacc
    · simpa using cbIn_mono F S x _ acc hacc
  · intro acc
    simp only [hSa, cond_true]
    apply foldl_hit _ _ _ b _ _ _ (List.mem_range.2 (by omega))
    · intro acc x hacc
      cases hx : S.testBit x
      · simp only [cond_false]; exact hacc
      · simp only [cond_true, Nat.testBit_or, hacc, Bool.true_or]
    · intro acc
      simp only [hSb, cond_true, Nat.testBit_or, bit_self, Bool.or_true, Bool.true_or]

theorem cb_or (F S a b : ℕ) (ha : a ≤ F) (hb : b ≤ F) (hSa : S.testBit a = true) (hSb : S.testBit b = true) :
    (cb F S).testBit (a ||| (b ||| 0)) = true := by
  apply foldl_hit _ _ _ a _ _ _ (List.mem_range.2 (by omega))
  · intro acc x hacc
    cases hx : S.testBit x
    · simpa using hacc
    · simpa using cbIn_mono F S x _ acc hacc
  · intro acc
    simp only [hSa, cond_true]
    apply foldl_hit _ _ _ b _ _ _ (List.mem_range.2 (by omega))
    · intro acc x hacc
      cases hx : S.testBit x
      · simp only [cond_false]; exact hacc
      · simp only [cond_true, Nat.testBit_or, hacc, Bool.true_or]
    · intro acc
      simp only [hSb, cond_true, Nat.testBit_or, bit_self, Bool.or_true, Bool.true_or]

theorem cn_not (F S a : ℕ) (ha : a ≤ F) (hSa : S.testBit a = true) : (cn F S).testBit (a ^^^ F) = true := by
  apply foldl_hit _ _ _ a _ _ _ (List.mem_range.2 (by omega))
  · intro acc x hacc
    cases hx : S.testBit x <;> simp [Nat.testBit_or, hacc]
  · intro acc
    simp [hSa, Nat.testBit_or, bit_self]

def tgs (A B C S : ℕ) : Bool := S.testBit A && S.testBit B && S.testBit C

def miss (A B C S : ℕ) : ℕ :=
  (bif S.testBit A then 0 else 1) + (bif S.testBit B then 0 else 1) + (bif S.testBit C then 0 else 1)

/-- can the three targets all be present after at most `g` more gates, at most `n` of them NOTs? -/
def ok (F A B C : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, S => tgs A B C S
  | g + 1, n, S => tgs A B C S || (Nat.ble (miss A B C S) (g + 1) &&
      (List.range (F + 1)).any (fun v => !S.testBit v &&
        (((cb F S).testBit v && ok F A B C g n (S ||| 1 <<< v)) ||
         (!Nat.beq n 0 && ((cn F S).testBit v && ok F A B C g (n - 1) (S ||| 1 <<< v))))))

theorem ok_tgs (F A B C g n S : ℕ) (h : tgs A B C S = true) : ok F A B C g n S = true := by
  cases g <;> simp [ok, h]

theorem tgs_miss (A B C S : ℕ) (h : tgs A B C S = true) : miss A B C S = 0 := by
  simp only [tgs, Bool.and_eq_true] at h
  simp [miss, h.1.1, h.1.2, h.2]

theorem ok_miss (F A B C g n S : ℕ) (h : ok F A B C g n S = true) : miss A B C S ≤ g := by
  cases g with
  | zero => simp only [ok] at h; rw [tgs_miss A B C S h]
  | succ g =>
    simp only [ok, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | h
    · rw [tgs_miss A B C S h]; omega
    · exact Nat.le_of_ble_eq_true h.1

theorem miss_ins (A B C S v : ℕ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    miss A B C S ≤ miss A B C (S ||| 1 <<< v) + 1 := by
  simp only [miss, bit_ins]
  by_cases h1 : v = A
  · subst h1
    have e2 : decide (v = B) = false := by simpa using hAB
    have e3 : decide (v = C) = false := by simpa using hAC
    simp only [e2, e3, Bool.or_false, decide_true, Bool.or_true, cond_true]
    cases S.testBit v <;> simp <;> omega
  · by_cases h2 : v = B
    · subst h2
      have e1 : decide (v = A) = false := by simpa using h1
      have e3 : decide (v = C) = false := by simpa using hBC
      simp only [e1, e3, Bool.or_false, decide_true, Bool.or_true, cond_true]
      cases S.testBit v <;> simp <;> omega
    · have e1 : decide (v = A) = false := by simpa using h1
      have e2 : decide (v = B) = false := by simpa using h2
      simp only [e1, e2, Bool.or_false]
      cases S.testBit A <;> cases S.testBit B <;> cases S.testBit C <;> cases decide (v = C) <;> simp

/-- the number of NOT gates of a gate list, as `PEqualNP.NotBracket.notCount` counts them -/
abbrev ncnt (gs : List Gate) : ℕ := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

theorem ncnt_cons (g : Gate) (gs : List Gate) : ncnt gs ≤ ncnt (g :: gs) ∧ (g.op = GateOp.not → ncnt gs + 1 ≤ ncnt (g :: gs)) := by
  simp only [ncnt, PEqualNP.NotBracket.notCount, List.filter_cons]
  by_cases h : g.op = GateOp.not <;> simp [h]

theorem core (F T A B C : ℕ) (hF : F + 1 = 2 ^ T) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    ∀ (gs : List Gate) (w : List ℕ) (S g n : ℕ),
      (∀ x ∈ gs, AON x.op ∧ x.inputs.length ≤ 2) →
      (∀ v ∈ w, v < 2 ^ T ∧ S.testBit v = true) → S.testBit 0 = true → S.testBit F = true →
      gs.length ≤ g → ncnt gs ≤ n →
      A ∈ sim F gs w → B ∈ sim F gs w → C ∈ sim F gs w → ok F A B C g n S = true := by
  have hFlt : F < 2 ^ T := by omega
  intro gs
  induction gs with
  | nil =>
    intro w S g n _ hw _ _ _ _ hA hB hC
    apply ok_tgs
    simp only [sim, List.foldl_nil] at hA hB hC
    simp [tgs, (hw A hA).2, (hw B hB).2, (hw C hC).2]
  | cons x gs ih =>
    intro w S g n hgs hw h0 hFS hlen hn hA hB hC
    obtain ⟨hop, hin⟩ := hgs x (List.mem_cons_self ..)
    have hgs' : ∀ y ∈ gs, AON y.op ∧ y.inputs.length ≤ 2 := fun y hy => hgs y (List.mem_cons_of_mem _ hy)
    -- the operands: present vectors below 2 ^ T
    have hop_mem : ∀ i, w.getD i 0 < 2 ^ T ∧ S.testBit (w.getD i 0) = true := by
      intro i
      rw [List.getD_eq_getElem?_getD]
      cases hi : w[i]? with
      | none => exact ⟨Nat.two_pow_pos T, h0⟩
      | some v => exact hw v (List.mem_of_getElem? hi)
    set l := x.inputs.map fun i => w.getD i 0 with hl
    have hl_mem : ∀ v ∈ l, v < 2 ^ T ∧ S.testBit v = true := by
      intro v hv
      simp only [hl, List.mem_map] at hv
      obtain ⟨i, _, rfl⟩ := hv
      exact hop_mem i
    set v := vop F x.op l with hv
    have hvlt : v < 2 ^ T := vop_lt F T hFlt x.op l (fun u hu => (hl_mem u hu).1)
    have hsim : sim F (x :: gs) w = sim F gs (w ++ [v]) := by simp [sim, step, hv, hl]
    rw [hsim] at hA hB hC
    have hnc := ncnt_cons x gs
    have hlen' : gs.length + 1 ≤ g := by simpa using hlen
    by_cases hSv : S.testBit v = true
    · -- nothing new: the same set, one gate fewer
      refine ih (w ++ [v]) S g n hgs' ?_ h0 hFS (by omega) (by omega) hA hB hC
      intro u hu
      rcases List.mem_append.1 hu with hu | hu
      · exact hw u hu
      · simp only [List.mem_singleton] at hu; subst hu; exact ⟨hvlt, hSv⟩
    · have hSv' : S.testBit v = false := by simpa using hSv
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      have hw' : ∀ u ∈ w ++ [v], u < 2 ^ T ∧ (S ||| 1 <<< v).testBit u = true := by
        intro u hu
        rcases List.mem_append.1 hu with hu | hu
        · exact ⟨(hw u hu).1, by rw [bit_ins]; simp [(hw u hu).2]⟩
        · simp only [List.mem_singleton] at hu; subst hu; exact ⟨hvlt, by rw [bit_ins]; simp⟩
      have h0' : (S ||| 1 <<< v).testBit 0 = true := by rw [bit_ins]; simp [h0]
      have hF' : (S ||| 1 <<< v).testBit F = true := by rw [bit_ins]; simp [hFS]
      have hvF : v ≤ F := by omega
      have hmissS : ∀ n', ok F A B C g' n' (S ||| 1 <<< v) = true → Nat.ble (miss A B C S) (g' + 1) = true := by
        intro n' hok
        apply Nat.ble_eq_true_of_le
        have := ok_miss F A B C g' n' _ hok
        have := miss_ins A B C S v hAB hAC hBC
        omega
      have hFF : F &&& F = F := Nat.and_self F
      -- which kind of gate made v
      rcases hop with hx | hx | hx
      · -- AND: v = a &&& (b &&& F) for present a, b
        have hok := ih (w ++ [v]) (S ||| 1 <<< v) g' n hgs' hw' h0' hF' (by omega) (by omega) hA hB hC
        have hcb : (cb F S).testBit v = true := by
          have e : v = l.foldr (fun a r => a &&& r) F := by rw [hv, hx]; rfl
          have hll : l.length ≤ 2 := by simpa [hl] using hin
          match l, hl_mem, e, hll with
          | [], _, e, _ => rw [e]; simpa [hFF] using cb_and F S F F le_rfl le_rfl hFS hFS
          | [a], hm, e, _ =>
            rw [e]
            have := cb_and F S a F (by have := (hm a (by simp)).1; omega) le_rfl (hm a (by simp)).2 hFS
            simpa [hFF] using this
          | [a, b], hm, e, _ =>
            rw [e]
            exact cb_and F S a b (by have := (hm a (by simp)).1; omega) (by have := (hm b (by simp)).1; omega)
              (hm a (by simp)).2 (hm b (by simp)).2
          | _ :: _ :: _ :: _, _, _, hll => simp at hll
        simp only [ok, Bool.or_eq_true, Bool.and_eq_true]
        right
        refine ⟨hmissS n hok, ?_⟩
        rw [List.any_eq_true]
        exact ⟨v, List.mem_range.2 (by omega), by simp [hSv', hcb, hok]⟩
      · -- OR
        have hok := ih (w ++ [v]) (S ||| 1 <<< v) g' n hgs' hw' h0' hF' (by omega) (by omega) hA hB hC
        have hcb : (cb F S).testBit v = true := by
          have e : v = l.foldr (fun a r => a ||| r) 0 := by rw [hv, hx]; rfl
          have hll : l.length ≤ 2 := by simpa [hl] using hin
          have h0F : (0 : ℕ) ≤ F := Nat.zero_le F
          match l, hl_mem, e, hll with
          | [], _, e, _ => rw [e]; simpa using cb_or F S 0 0 h0F h0F h0 h0
          | [a], hm, e, _ =>
            rw [e]
            have := cb_or F S a 0 (by have := (hm a (by simp)).1; omega) h0F (hm a (by simp)).2 h0
            simpa using this
          | [a, b], hm, e, _ =>
            rw [e]
            exact cb_or F S a b (by have := (hm a (by simp)).1; omega) (by have := (hm b (by simp)).1; omega)
              (hm a (by simp)).2 (hm b (by simp)).2
          | _ :: _ :: _ :: _, _, _, hll => simp at hll
        simp only [ok, Bool.or_eq_true, Bool.and_eq_true]
        right
        refine ⟨hmissS n hok, ?_⟩
        rw [List.any_eq_true]
        exact ⟨v, List.mem_range.2 (by omega), by simp [hSv', hcb, hok]⟩
      · -- NOT: one of the n allowed
        have hn1 : 1 ≤ n := by have := hnc.2 hx; omega
        have hok := ih (w ++ [v]) (S ||| 1 <<< v) g' (n - 1) hgs' hw' h0' hF' (by omega)
          (by have := hnc.2 hx; omega) hA hB hC
        have hcn : (cn F S).testBit v = true := by
          have e : v = l.headD 0 ^^^ F := by rw [hv, hx]; rfl
          rw [e]
          cases hl2 : l with
          | nil => simpa using cn_not F S 0 (Nat.zero_le F) h0
          | cons a l' =>
            have hm := hl_mem a (by rw [hl2]; simp)
            simpa using cn_not F S a (by have := hm.1; omega) hm.2
        have hnb : Nat.beq n 0 = false := by
          cases n with
          | zero => omega
          | succ k => rfl
        simp only [ok, Bool.or_eq_true, Bool.and_eq_true]
        right
        refine ⟨hmissS (n - 1) hok, ?_⟩
        rw [List.any_eq_true]
        exact ⟨v, List.mem_range.2 (by omega), by simp [hSv', hcn, hok, hnb]⟩

theorem ins_bits : ∀ t : Fin 6, (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    = ([62, 60, 56, 48, 32, 0, 63] : List ℕ).map (fun v => v.testBit t.val) := by decide

theorem eq_bits : ∀ u a : Fin 64, (∀ t : Fin 6, u.val.testBit t.val = a.val.testBit t.val) → u = a := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem search : ok 63 22 30 36 6 2 15060318633198616577 = false := by decide +kernel

end PEqualNP.Outside.L_meta_50718_aux

theorem PEqualNP.Outside.L_meta_50718 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (22 : Nat).testBit t.val ∧
    w.getD q.val false = (30 : Nat).testBit t.val ∧
    w.getD r.val false = (36 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hfan, -, hnc, hsz, hall⟩
  have hgs : ∀ x ∈ D.gates, PEqualNP.Outside.L_meta_50718_aux.AON x.op ∧ x.inputs.length ≤ 2 := by
    intro x hx
    obtain ⟨h1, h2⟩ := hfan x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  have hw : ∀ t : Fin 6, D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true])
      = (PEqualNP.Outside.L_meta_50718_aux.sim 63 D.gates [62, 60, 56, 48, 32, 0, 63]).map (fun v => v.testBit t.val) := by
    intro t
    rw [PEqualNP.Outside.L_meta_50718_aux.ins_bits t]
    exact PEqualNP.Outside.L_meta_50718_aux.wires_sim 63 t.val (by revert t; decide) D.gates _ (fun g hg => (hgs g hg).1)
  have hlen : (PEqualNP.Outside.L_meta_50718_aux.sim 63 D.gates [62, 60, 56, 48, 32, 0, 63]).length = 7 + D.size := by
    rw [PEqualNP.Outside.L_meta_50718_aux.sim_length]; rfl
  have hbd : ∀ v ∈ PEqualNP.Outside.L_meta_50718_aux.sim 63 D.gates [62, 60, 56, 48, 32, 0, 63], v < 2 ^ 6 :=
    PEqualNP.Outside.L_meta_50718_aux.sim_lt 63 6 (by norm_num) D.gates _ (by decide)
  have tap : ∀ (k : Fin (7 + D.size)) (a : ℕ), a < 64 →
      (∀ t : Fin 6, (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true])).getD k.val false = a.testBit t.val) →
      a ∈ PEqualNP.Outside.L_meta_50718_aux.sim 63 D.gates [62, 60, 56, 48, 32, 0, 63] := by
    intro k a ha h
    have hk : k.val < (PEqualNP.Outside.L_meta_50718_aux.sim 63 D.gates [62, 60, 56, 48, 32, 0, 63]).length := by rw [hlen]; exact k.isLt
    have hu := List.getElem_mem hk
    have hul : (PEqualNP.Outside.L_meta_50718_aux.sim 63 D.gates [62, 60, 56, 48, 32, 0, 63])[k.val] < 64 := by simpa using hbd _ hu
    have e := PEqualNP.Outside.L_meta_50718_aux.eq_bits ⟨_, hul⟩ ⟨a, ha⟩ (by
      intro t
      have h1 := h t
      rw [hw t, PEqualNP.Outside.L_meta_50718_aux.getD_bit, List.getD_eq_getElem _ _ hk] at h1
      exact h1)
    have e2 : (PEqualNP.Outside.L_meta_50718_aux.sim 63 D.gates [62, 60, 56, 48, 32, 0, 63])[k.val] = a := congrArg Fin.val e
    rw [← e2]; exact hu
  have hA := tap p 22 (by decide) (fun t => (hall t).1)
  have hB := tap q 30 (by decide) (fun t => (hall t).2.1)
  have hC := tap r 36 (by decide) (fun t => (hall t).2.2)
  have hok := PEqualNP.Outside.L_meta_50718_aux.core 63 6 22 30 36 (by norm_num) (by decide) (by decide) (by decide)
    D.gates [62, 60, 56, 48, 32, 0, 63] 15060318633198616577 6 2 hgs (by decide) (by decide) (by decide) hsz hnc hA hB hC
  rw [PEqualNP.Outside.L_meta_50718_aux.search] at hok
  exact absurd hok (by decide)
