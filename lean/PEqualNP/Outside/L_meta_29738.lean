import PEqualNP.Defs

/- Method and generic lemmas after upstream PEqualNP/Outside/L_meta_20800.lean (Maxime Wolf); mask and bound changed. -/
namespace PEqualNP.Outside.L_meta_29738_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev TT := BitVec 16

def zeroTT : TT := 0#16
def oneTT : TT := BitVec.allOnes 16

def isProper (w : TT) : Bool := (w != zeroTT) && (w != oneTT)

def inTTs : List TT :=
  [0x000F#16, 0x00F0#16, 0x0F00#16, 0xF000#16,
   0x1111#16, 0x2222#16, 0x4444#16, 0x8888#16]

def gateTT (g : Gate) (ws : List TT) : TT :=
  match g.op, g.inputs with
  | .and, [] => oneTT
  | .and, [a] => ws.getD a zeroTT
  | .and, [a, b] => ws.getD a zeroTT &&& ws.getD b zeroTT
  | .or, [] => zeroTT
  | .or, [a] => ws.getD a zeroTT
  | .or, [a, b] => ws.getD a zeroTT ||| ws.getD b zeroTT
  | .not, [] => oneTT
  | .not, a :: _ => ~~~(ws.getD a zeroTT)
  | _, _ => zeroTT

def evalTT (gs : List Gate) (ws : List TT) : List TT :=
  gs.foldl (fun acc g => acc ++ [gateTT g acc]) ws

lemma inTTs_bit (u v : Fin 4) (i : ℕ) :
    (inTTs.getD i zeroTT).getLsbD (4 * u.val + v.val) = (oneEach u v).getD i false := by
  have hi : i < 8 ∨ 8 ≤ i := Nat.lt_or_ge i 8
  rcases hi with hi | hi
  · revert u v
    have : ∀ (k : Fin 8) (u v : Fin 4),
        (inTTs.getD k.val zeroTT).getLsbD (4 * u.val + v.val) = (oneEach u v).getD k.val false := by
      decide
    exact this ⟨i, hi⟩
  · have h1 : inTTs.getD i zeroTT = zeroTT := by
      simp [List.getD, List.getElem?_eq_none (show inTTs.length ≤ i by simp [inTTs]; omega)]
    have h2 : (oneEach u v).getD i false = false := by
      have hlen : (oneEach u v).length = 8 := by simp [oneEach]
      simp [List.getD, List.getElem?_eq_none (show (oneEach u v).length ≤ i by omega)]
    rw [h1, h2]
    simp [zeroTT]

lemma gateTT_bit (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (ws : List TT) (bs : List Bool) (idx : ℕ) (hidx : idx < 16)
    (hmatch : ∀ i, (ws.getD i zeroTT).getLsbD idx = bs.getD i false) :
    (gateTT g ws).getLsbD idx = g.op.eval (g.inputs.map fun i => bs.getD i false) := by
  rcases hg with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · match hin : g.inputs with
    | [] => simp only [gateTT, h, hin, oneTT, BitVec.getLsbD_allOnes, GateOp.eval, List.map_nil, List.all_nil, hidx, decide_true]
    | [a] => simp only [gateTT, h, hin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]; exact hmatch a
    | [a, b] => simp only [gateTT, h, hin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq, BitVec.getLsbD_and, hmatch a, hmatch b]
    | _ :: _ :: _ :: _ => simp [hin] at hlen
  · match hin : g.inputs with
    | [] => simp [gateTT, h, hin, zeroTT, GateOp.eval]
    | [a] => simp only [gateTT, h, hin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]; exact hmatch a
    | [a, b] => simp only [gateTT, h, hin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq, BitVec.getLsbD_or, hmatch a, hmatch b]
    | _ :: _ :: _ :: _ => simp [hin] at hlen
  · match hin : g.inputs with
    | [] => simp only [gateTT, h, hin, oneTT, BitVec.getLsbD_allOnes, GateOp.eval, List.map_nil, List.headD_nil, Bool.not_false, hidx, decide_true]
    | a :: _ => simp only [gateTT, h, hin, GateOp.eval, List.map_cons, List.headD_cons, BitVec.getLsbD_not, hidx, decide_true, Bool.true_and, hmatch a]

lemma evalTT_bit (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (ws : List TT) (bs : List Bool) (hlen : ws.length = bs.length) (idx : ℕ) (hidx : idx < 16)
    (hmatch : ∀ i, (ws.getD i zeroTT).getLsbD idx = bs.getD i false) :
    ∀ i, ((evalTT gs ws).getD i zeroTT).getLsbD idx =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) bs).getD i false := by
  induction gs generalizing ws bs with
  | nil => exact hmatch
  | cons g rest ih =>
    simp only [evalTT, List.foldl_cons] at *
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
    · simp [hlen]
    · intro i
      have hg := hgs g (List.mem_cons_self ..)
      by_cases hi : i < ws.length
      · have hi' : i < bs.length := hlen ▸ hi
        simp only [List.getD, List.getElem?_append_left hi, List.getElem?_append_left hi']
        simpa [List.getD] using hmatch i
      · by_cases heq : i = ws.length
        · subst heq
          have h1 : (ws ++ [gateTT g ws]).getD ws.length zeroTT = gateTT g ws := by
            simp [List.getD]
          have h2 : (bs ++ [g.op.eval (g.inputs.map fun j => bs.getD j false)]).getD ws.length false =
              g.op.eval (g.inputs.map fun j => bs.getD j false) := by
            rw [hlen]; simp [List.getD]
          rw [h1, h2]
          exact gateTT_bit g hg ws bs idx hidx hmatch
        · have hgt : (ws ++ [gateTT g ws]).length ≤ i := by simp; omega
          have hgt' : (bs ++ [g.op.eval (g.inputs.map fun j => bs.getD j false)]).length ≤ i := by simp; omega
          have hl : (ws ++ [gateTT g ws]).getD i zeroTT = zeroTT := by
            rw [List.getD, List.getElem?_eq_none hgt]; rfl
          have hr : (bs ++ [g.op.eval (g.inputs.map fun j => bs.getD j false)]).getD i false = false := by
            rw [List.getD, List.getElem?_eq_none hgt']; rfl
          rw [hl, hr]; simp [zeroTT]

lemma circuit_target_mem (mask : ℕ) (C : Circuit) (hfit : FanInTwo C)
    (hrep : Represents (fun u v : Fin 4 => mask.testBit (4 * u.val + v.val)) C)
    (hprop : isProper (BitVec.ofNat 16 mask) = true) :
    BitVec.ofNat 16 mask ∈ evalTT C.gates inTTs := by
  have heq : (evalTT C.gates inTTs).getD C.output zeroTT = BitVec.ofNat 16 mask := by
    apply BitVec.eq_of_getLsbD_eq
    intro idx hidx
    let u : Fin 4 := ⟨idx / 4, by omega⟩
    let v : Fin 4 := ⟨idx % 4, by omega⟩
    have huv : 4 * u.val + v.val = idx := by dsimp [u, v]; omega
    rw [← huv]
    have hbit := evalTT_bit C.gates hfit inTTs (oneEach u v) (by simp [inTTs, oneEach])
      (4 * u.val + v.val) (by omega) (inTTs_bit u v) C.output
    rw [hbit]
    have hr := hrep u v
    simp only [Circuit.eval, Circuit.wires] at hr
    rw [hr, BitVec.getLsbD_ofNat]
    simp [show 4 * u.val + v.val < 16 by omega]
  by_cases hlt : C.output < (evalTT C.gates inTTs).length
  · rw [← heq]
    simp only [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_mem hlt
  · have hz : (evalTT C.gates inTTs).getD C.output zeroTT = zeroTT := by
      simp [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt)]
    rw [hz] at heq
    rw [← heq] at hprop
    simp [isProper, zeroTT] at hprop

def drop1 (d : Bool) (a : TT) (S : Finset TT) : Finset TT :=
  if d then S.erase a else S

def drop2 (da db : Bool) (a b : TT) (S : Finset TT) : Finset TT :=
  drop1 db b (drop1 da a S)

inductive Reach (target : TT) : ℕ → ℕ → Finset TT → Prop
  | done : Reach target 0 0 {target}
  | step_not {b u : ℕ} {S : Finset TT} {a : TT} (da : Bool) :
      a ∈ S → isProper (~~~a) = true → ~~~a ∉ S →
      Reach target b u (insert (~~~a) (drop1 da a S)) →
      Reach target b (u + 1) S
  | step_bin {b u : ℕ} {S : Finset TT} {a x : TT} (isOr da db : Bool) :
      a ∈ S → x ∈ S → a ≠ x →
      isProper (if isOr then a ||| x else a &&& x) = true →
      (if isOr then a ||| x else a &&& x) ∉ S →
      Reach target b u (insert (if isOr then a ||| x else a &&& x) (drop2 da db a x S)) →
      Reach target (b + 1) u S

lemma card_le_drop1_succ (d : Bool) (a : TT) (T : Finset TT) :
    T.card ≤ (drop1 d a T).card + 1 := by
  cases d
  · simp [drop1]
  · simp only [drop1, ↓reduceIte]
    by_cases ha : a ∈ T
    · rw [Finset.card_erase_of_mem ha]
      have : 1 ≤ T.card := Finset.card_pos.mpr ⟨a, ha⟩
      omega
    · rw [Finset.erase_eq_of_notMem ha]; omega

lemma reach_card_le {target : TT} {b u : ℕ} {S : Finset TT} (h : Reach target b u S) :
    S.card ≤ b + 1 := by
  induction h with
  | done => simp
  | @step_not b u S a da ha _ hna _ ih =>
    have h1 : (insert (~~~a) (drop1 da a S)).card = (drop1 da a S).card + 1 := by
      apply Finset.card_insert_of_notMem
      intro hm
      cases da
      · exact hna hm
      · exact hna (Finset.mem_erase.mp hm).2
    have h2 := card_le_drop1_succ da a S
    omega
  | @step_bin b u S a x isOr da db ha hx hax hpc hnc _ ih =>
    set c := if isOr then a ||| x else a &&& x
    have h1 : (insert c (drop2 da db a x S)).card = (drop2 da db a x S).card + 1 := by
      apply Finset.card_insert_of_notMem
      intro hm
      have : c ∈ S := by
        cases da <;> cases db <;> simp only [drop2, drop1, ↓reduceIte, Bool.false_eq_true, Finset.mem_erase] at hm
        · exact hm
        · exact hm.2
        · exact hm.2
        · exact hm.2.2
      exact hnc this
    have hd1 := card_le_drop1_succ da a S
    have hd2 := card_le_drop1_succ db x (drop1 da a S)
    dsimp only [drop2] at h1 ih
    omega

lemma extract_aux (target : TT) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (ws : List TT) (ht : target ∈ evalTT gs ws) (htp : isProper target = true) :
    ∃ b u S, b + u ≤ gs.length ∧ (∀ w ∈ S, w ∈ ws ∧ isProper w = true) ∧ Reach target b u S := by
  induction gs generalizing ws with
  | nil =>
    refine ⟨0, 0, {target}, by simp, ?_, Reach.done⟩
    intro w hw
    simp only [Finset.mem_singleton] at hw
    subst hw
    exact ⟨ht, htp⟩
  | cons g rest ih =>
    simp only [evalTT, List.foldl_cons] at ht
    obtain ⟨b, u, S', hbu, hS', hR'⟩ :=
      ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) (ws ++ [gateTT g ws]) ht
    set c := gateTT g ws
    by_cases hcS : c ∈ S'
    · by_cases hcws : c ∈ ws
      · refine ⟨b, u, S', by simp; omega, ?_, hR'⟩
        intro w hw
        obtain ⟨hm, hp⟩ := hS' w hw
        simp only [List.mem_append, List.mem_singleton] at hm
        exact ⟨hm.elim id (fun h => h ▸ hcws), hp⟩
      · have hcp : isProper c = true := (hS' c hcS).2
        have hsub : ∀ w ∈ S'.erase c, w ∈ ws ∧ isProper w = true := by
          intro w hw
          obtain ⟨hne, hmw⟩ := Finset.mem_erase.mp hw
          obtain ⟨hm, hp⟩ := hS' w hmw
          simp only [List.mem_append, List.mem_singleton] at hm
          exact ⟨hm.resolve_right hne, hp⟩
        have hg := hgs g (List.mem_cons_self ..)
        rcases hg with ⟨hop, hlen⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        have hnot_zero : c ≠ zeroTT := by
          simp only [isProper, Bool.and_eq_true, bne_iff_ne] at hcp; exact hcp.1
        have hnot_one : c ≠ oneTT := by
          simp only [isProper, Bool.and_eq_true, bne_iff_ne] at hcp; exact hcp.2
        have getD_mem_or_zero : ∀ i, ws.getD i zeroTT ∈ ws ∨ ws.getD i zeroTT = zeroTT := by
          intro i
          by_cases hlt : i < ws.length
          · left; simp only [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]; exact List.getElem_mem hlt
          · right; simp [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt)]
        have bin_case : ∀ (isOr : Bool) (i j : ℕ),
            c = (if isOr then ws.getD i zeroTT ||| ws.getD j zeroTT else ws.getD i zeroTT &&& ws.getD j zeroTT) →
            ∃ b' u' S, b' + u' ≤ (g :: rest).length ∧ (∀ w ∈ S, w ∈ ws ∧ isProper w = true) ∧ Reach target b' u' S := by
          intro isOr i j hceq
          set a := ws.getD i zeroTT
          set x := ws.getD j zeroTT
          have hap : isProper a = true := by
            by_contra hna
            simp only [isProper, Bool.and_eq_true, bne_iff_ne, not_and, not_not] at hna
            by_cases ha0 : a = zeroTT
            · cases isOr <;> simp only [Bool.false_eq_true, ↓reduceIte, ha0, zeroTT, BitVec.zero_and, BitVec.zero_or] at hceq
              · exact hnot_zero hceq
              · rcases getD_mem_or_zero j with hj | hj
                · exact hcws (hceq ▸ hj)
                · exact hnot_zero (hceq.trans hj)
            · have ha1 : a = oneTT := hna ha0
              cases isOr <;> simp only [Bool.false_eq_true, ↓reduceIte, ha1, oneTT, BitVec.allOnes_and, BitVec.allOnes_or] at hceq
              · rcases getD_mem_or_zero j with hj | hj
                · exact hcws (hceq ▸ hj)
                · exact hnot_zero (hceq.trans hj)
              · exact hnot_one hceq
          have hxp : isProper x = true := by
            by_contra hnx
            simp only [isProper, Bool.and_eq_true, bne_iff_ne, not_and, not_not] at hnx
            by_cases hx0 : x = zeroTT
            · cases isOr <;> simp only [Bool.false_eq_true, ↓reduceIte, hx0, zeroTT, BitVec.and_zero, BitVec.or_zero] at hceq
              · exact hnot_zero hceq
              · rcases getD_mem_or_zero i with hi | hi
                · exact hcws (hceq ▸ hi)
                · exact hnot_zero (hceq.trans hi)
            · have hx1 : x = oneTT := hnx hx0
              cases isOr <;> simp only [Bool.false_eq_true, ↓reduceIte, hx1, oneTT, BitVec.and_allOnes, BitVec.or_allOnes] at hceq
              · rcases getD_mem_or_zero i with hi | hi
                · exact hcws (hceq ▸ hi)
                · exact hnot_zero (hceq.trans hi)
              · exact hnot_one hceq
          have ha_ws : a ∈ ws := (getD_mem_or_zero i).resolve_right (by simp [isProper] at hap; exact hap.1)
          have hx_ws : x ∈ ws := (getD_mem_or_zero j).resolve_right (by simp [isProper] at hxp; exact hxp.1)
          have hax : a ≠ x := by
            intro heq
            cases isOr <;> simp [heq] at hceq <;> exact hcws (hceq ▸ hx_ws)
          let S := insert a (insert x (S'.erase c))
          have hc_not_S : c ∉ S := by
            intro hm
            simp only [S, Finset.mem_insert, Finset.mem_erase] at hm
            rcases hm with hca | hcx | ⟨hne, _⟩
            · exact hcws (hca ▸ ha_ws)
            · exact hcws (hcx ▸ hx_ws)
            · exact hne rfl
          let da : Bool := decide (a ∉ S'.erase c)
          let db : Bool := decide (x ∉ S'.erase c)
          have hS'_eq : insert c (drop2 da db a x S) = S' := by
            ext w
            simp only [Finset.mem_insert, drop2, drop1, S, da, db]
            by_cases hwc : w = c
            · subst hwc; simp [hcS]
            · simp only [hwc, false_or]
              by_cases ham : a ∈ S'.erase c <;> by_cases hxm : x ∈ S'.erase c <;>
                simp only [ham, hxm, not_true_eq_false, not_false_eq_true, decide_false, decide_true,
                  Bool.false_eq_true, ↓reduceIte, Finset.mem_erase, Finset.mem_insert]
              · constructor
                · rintro (rfl | rfl | ⟨_, hw⟩)
                  · exact (Finset.mem_erase.mp ham).2
                  · exact (Finset.mem_erase.mp hxm).2
                  · exact hw
                · intro hw; right; right; exact ⟨hwc, hw⟩
              · constructor
                · rintro ⟨hwx, (rfl | rfl | ⟨_, hw⟩)⟩
                  · exact (Finset.mem_erase.mp ham).2
                  · exact absurd rfl hwx
                  · exact hw
                · intro hw
                  refine ⟨fun hwx => hxm (Finset.mem_erase.mpr ⟨hwx ▸ hwc, hwx ▸ hw⟩), ?_⟩
                  right; right; exact ⟨hwc, hw⟩
              · constructor
                · rintro ⟨hwa, (rfl | rfl | ⟨_, hw⟩)⟩
                  · exact absurd rfl hwa
                  · exact (Finset.mem_erase.mp hxm).2
                  · exact hw
                · intro hw
                  refine ⟨fun hwa => ham (Finset.mem_erase.mpr ⟨hwa ▸ hwc, hwa ▸ hw⟩), ?_⟩
                  right; right; exact ⟨hwc, hw⟩
              · constructor
                · rintro ⟨hwx, hwa, (rfl | rfl | ⟨_, hw⟩)⟩
                  · exact absurd rfl hwa
                  · exact absurd rfl hwx
                  · exact hw
                · intro hw
                  refine ⟨fun hwx => hxm (Finset.mem_erase.mpr ⟨hwx ▸ hwc, hwx ▸ hw⟩),
                    fun hwa => ham (Finset.mem_erase.mpr ⟨hwa ▸ hwc, hwa ▸ hw⟩), ?_⟩
                  right; right; exact ⟨hwc, hw⟩
          refine ⟨b + 1, u, S, by simp; omega, ?_, ?_⟩
          · intro w hw
            simp only [S, Finset.mem_insert] at hw
            rcases hw with rfl | rfl | hm
            · exact ⟨ha_ws, hap⟩
            · exact ⟨hx_ws, hxp⟩
            · exact hsub w hm
          · apply Reach.step_bin (a := a) (x := x) isOr da db
            · simp [S]
            · simp [S]
            · exact hax
            · rw [← hceq]; exact hcp
            · rw [← hceq]; exact hc_not_S
            · rw [← hceq, hS'_eq]; exact hR'
        rcases hop with h | h | h
        · match hin : g.inputs with
          | [] => exfalso; exact hnot_one (by simp [c, gateTT, h, hin])
          | [i] =>
            exfalso
            have hci : c = ws.getD i zeroTT := by simp [c, gateTT, h, hin]
            rcases getD_mem_or_zero i with hi | hi
            · exact hcws (hci ▸ hi)
            · exact hnot_zero (hci.trans hi)
          | [i, j] => exact bin_case false i j (by simp [c, gateTT, h, hin])
          | _ :: _ :: _ :: _ => simp [hin] at hlen
        · match hin : g.inputs with
          | [] => exfalso; exact hnot_zero (by simp [c, gateTT, h, hin])
          | [i] =>
            exfalso
            have hci : c = ws.getD i zeroTT := by simp [c, gateTT, h, hin]
            rcases getD_mem_or_zero i with hi | hi
            · exact hcws (hci ▸ hi)
            · exact hnot_zero (hci.trans hi)
          | [i, j] => exact bin_case true i j (by simp [c, gateTT, h, hin])
          | _ :: _ :: _ :: _ => simp [hin] at hlen
        · match hin : g.inputs with
          | [] => exfalso; exact hnot_one (by simp [c, gateTT, h, hin])
          | i :: _ =>
            have hceq : c = ~~~(ws.getD i zeroTT) := by simp [c, gateTT, h, hin]
            set a := ws.getD i zeroTT
            have hap : isProper a = true := by
              by_contra hna
              simp only [isProper, Bool.and_eq_true, bne_iff_ne, not_and, not_not] at hna
              by_cases ha0 : a = zeroTT
              · exact hnot_one (by rw [hceq, ha0]; rfl)
              · exact hnot_zero (by rw [hceq, hna ha0]; rfl)
            have ha_ws : a ∈ ws := (getD_mem_or_zero i).resolve_right (by simp [isProper] at hap; exact hap.1)
            let S := insert a (S'.erase c)
            have hc_not_S : c ∉ S := by
              intro hm
              simp only [S, Finset.mem_insert, Finset.mem_erase] at hm
              rcases hm with hca | ⟨hne, _⟩
              · exact hcws (hca ▸ ha_ws)
              · exact hne rfl
            let da : Bool := decide (a ∉ S'.erase c)
            have hS'_eq : insert c (drop1 da a S) = S' := by
              ext w
              simp only [Finset.mem_insert, drop1, S, da]
              by_cases hwc : w = c
              · subst hwc; simp [hcS]
              · simp only [hwc, false_or]
                by_cases hwa : w = a
                · subst hwa
                  by_cases ham : a ∈ S'.erase c
                  · simp [ham, (Finset.mem_erase.mp ham).2]
                  · have : a ∉ S' := fun hm => ham (Finset.mem_erase.mpr ⟨hwc, hm⟩)
                    simp [ham, this]
                · by_cases ham : a ∈ S'.erase c <;> simp [ham, hwa, Finset.mem_erase, hwc]
            refine ⟨b, u + 1, S, by simp; omega, ?_, ?_⟩
            · intro w hw
              simp only [S, Finset.mem_insert] at hw
              rcases hw with rfl | hm
              · exact ⟨ha_ws, hap⟩
              · exact hsub w hm
            · apply Reach.step_not (a := a) da
              · simp [S]
              · rw [← hceq]; exact hcp
              · rw [← hceq]; exact hc_not_S
              · rw [← hceq, hS'_eq]; exact hR'
    · refine ⟨b, u, S', by simp; omega, ?_, hR'⟩
      intro w hw
      obtain ⟨hm, hp⟩ := hS' w hw
      simp only [List.mem_append, List.mem_singleton] at hm
      exact ⟨hm.resolve_right (fun h => hcS (h ▸ hw)), hp⟩

lemma reach_sep {target : TT} {b u : ℕ} {S : Finset TT} (h : Reach target b u S)
    (p q : ℕ) (hp16 : p < 16) (hq16 : q < 16)
    (hp : target.getLsbD p = true) (hq : target.getLsbD q = false) :
    if u = 0 then (∃ w ∈ S, w.getLsbD p = true ∧ w.getLsbD q = false)
    else (∃ w ∈ S, w.getLsbD p ≠ w.getLsbD q) := by
  induction h with
  | done =>
    simp only [↓reduceIte, Finset.mem_singleton]
    exact ⟨target, rfl, hp, hq⟩
  | @step_not b u S a da ha _ _ _ ih =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    have hdiff : ∃ w ∈ insert (~~~a) (drop1 da a S), w.getLsbD p ≠ w.getLsbD q := by
      by_cases hu : u = 0
      · simp only [hu, ↓reduceIte] at ih
        obtain ⟨w, hw, hwp, hwq⟩ := ih
        exact ⟨w, hw, by rw [hwp, hwq]; decide⟩
      · simp only [hu, ↓reduceIte] at ih
        exact ih
    obtain ⟨w, hw, hne⟩ := hdiff
    simp only [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · refine ⟨a, ha, ?_⟩
      intro heq
      apply hne
      simp only [BitVec.getLsbD_not, hp16, hq16, decide_true, Bool.true_and, heq]
    · have : w ∈ S := by
        cases da <;> simp [drop1] at hw
        · exact hw
        · exact hw.2
      exact ⟨w, this, hne⟩
  | @step_bin b u S a x isOr da db ha hx _ _ _ _ ih =>
    by_cases hu : u = 0
    · simp only [hu, ↓reduceIte] at ih ⊢
      obtain ⟨w, hw, hwp, hwq⟩ := ih
      simp only [Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · cases isOr
        · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_and, Bool.and_eq_true,
            Bool.and_eq_false_iff] at hwp hwq
          rcases hwq with hqa | hqx
          · exact ⟨a, ha, hwp.1, hqa⟩
          · exact ⟨x, hx, hwp.2, hqx⟩
        · simp only [↓reduceIte, BitVec.getLsbD_or, Bool.or_eq_true, Bool.or_eq_false_iff] at hwp hwq
          rcases hwp with hpa | hpx
          · exact ⟨a, ha, hpa, hwq.1⟩
          · exact ⟨x, hx, hpx, hwq.2⟩
      · have : w ∈ S := by
          cases da <;> cases db <;> simp [drop2, drop1] at hw
          · exact hw
          · exact hw.2
          · exact hw.2
          · exact hw.2.2
        exact ⟨w, this, hwp, hwq⟩
    · simp only [hu, ↓reduceIte] at ih ⊢
      obtain ⟨w, hw, hne⟩ := ih
      simp only [Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · by_cases hae : a.getLsbD p ≠ a.getLsbD q
        · exact ⟨a, ha, hae⟩
        · push Not at hae
          refine ⟨x, hx, ?_⟩
          intro hxe
          apply hne
          cases isOr <;> simp [BitVec.getLsbD_and, BitVec.getLsbD_or, hae, hxe]
      · have : w ∈ S := by
          cases da <;> cases db <;> simp [drop2, drop1] at hw
          · exact hw
          · exact hw.2
          · exact hw.2
          · exact hw.2.2
        exact ⟨w, this, hne⟩

def covPair (allowNot : Bool) (w : TT) (pq : ℕ × ℕ) : Bool :=
  if allowNot then (w.getLsbD pq.1 != w.getLsbD pq.2)
  else (w.getLsbD pq.1 && !w.getLsbD pq.2)

def allCovered (pairs : List (ℕ × ℕ)) (allowNot : Bool) (W : List TT) : Bool :=
  pairs.all (fun pq => W.any (fun w => covPair allowNot w pq))

def dropL (d : Bool) (a : TT) (W : List TT) : List TT :=
  if d then W.erase a else W

def dropL2 (da db : Bool) (a x : TT) (W : List TT) : List TT :=
  dropL db x (dropL da a W)

def tryPairsAux (f : TT → TT → Bool) : List TT → Bool
  | [] => false
  | a :: rest => rest.any (f a) || tryPairsAux f rest

lemma tryPairsAux_or (f : TT → TT → Bool) (W : List TT)
    (a x : TT) (ha : a ∈ W) (hx : x ∈ W) (hax : a ≠ x)
    (h1 : f a x = true) (h2 : f x a = true) :
    tryPairsAux f W = true := by
  induction W with
  | nil => cases ha
  | cons y ys ih =>
    simp only [tryPairsAux, Bool.or_eq_true, List.any_eq_true]
    simp only [List.mem_cons] at ha hx
    rcases ha with rfl | ha
    · rcases hx with rfl | hx
      · exact absurd rfl hax
      · left; exact ⟨x, hx, h1⟩
    · rcases hx with rfl | hx
      · left; exact ⟨a, ha, h2⟩
      · right; exact ih ha hx

def search (target : TT) (pairs : List (ℕ × ℕ)) : ℕ → ℕ → List TT → Bool
  | b, u, W =>
    if W.length > b + 1 then false
    else if W.contains target then true
    else if !allCovered pairs (decide (0 < u)) W then false
    else
      let tryNot :=
        match u with
        | 0 => false
        | u' + 1 =>
          W.any fun a =>
            let c := ~~~a
            isProper c && !W.contains c &&
            (search target pairs b u' (c :: dropL true a W) ||
             search target pairs b u' (c :: W))
      let tryBin :=
        match b with
        | 0 => false
        | b' + 1 =>
          tryPairsAux (fun a x =>
            let tryOp (c : TT) :=
              isProper c && !W.contains c &&
              (search target pairs b' u (c :: dropL2 true true a x W) ||
               search target pairs b' u (c :: dropL2 true false a x W) ||
               search target pairs b' u (c :: dropL2 false true a x W) ||
               search target pairs b' u (c :: W))
            tryOp (a &&& x) || tryOp (a ||| x)) W
      tryNot || tryBin
termination_by b u _ => b + u

lemma toFinset_dropL (d : Bool) (a : TT) (W : List TT) (hnd : W.Nodup) :
    (dropL d a W).toFinset = drop1 d a W.toFinset := by
  cases d
  · rfl
  · ext z
    simp only [dropL, drop1, ↓reduceIte, List.mem_toFinset, Finset.mem_erase,
      hnd.mem_erase_iff]

lemma nodup_dropL (d : Bool) (a : TT) (W : List TT) (hnd : W.Nodup) :
    (dropL d a W).Nodup := by
  cases d
  · exact hnd
  · exact hnd.erase a

lemma search_complete (target : TT) (pairs : List (ℕ × ℕ))
    (hpairs : ∀ pq ∈ pairs, pq.1 < 16 ∧ pq.2 < 16 ∧ target.getLsbD pq.1 = true ∧ target.getLsbD pq.2 = false)
    {b u : ℕ} {S : Finset TT} (hR : Reach target b u S) :
    ∀ W : List TT, W.Nodup → W.toFinset = S → search target pairs b u W = true := by
  induction hR with
  | done =>
    intro W hnd hW
    unfold search
    have hlen : W.length = 1 := by
      rw [← List.toFinset_card_of_nodup hnd, hW]; simp
    have hmem : target ∈ W := by
      rw [← List.mem_toFinset, hW]; simp
    simp [hlen, hmem]
  | @step_not b u S a da ha hpc hnc hnext ih =>
    intro W hnd hW
    have hcard : W.length ≤ b + 1 := by
      rw [← List.toFinset_card_of_nodup hnd, hW]
      exact reach_card_le (Reach.step_not da ha hpc hnc hnext)
    have hcov : allCovered pairs (decide (0 < u + 1)) W = true := by
      simp only [allCovered, List.all_eq_true, List.any_eq_true]
      intro pq hpq
      obtain ⟨hp16, hq16, hp, hq⟩ := hpairs pq hpq
      have hsep := reach_sep (Reach.step_not da ha hpc hnc hnext) pq.1 pq.2 hp16 hq16 hp hq
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte] at hsep
      obtain ⟨w, hw, hne⟩ := hsep
      refine ⟨w, by rwa [← List.mem_toFinset, hW], ?_⟩
      simp [covPair, hne]
    unfold search
    have hnotgt : ¬ W.length > b + 1 := by omega
    simp only [hnotgt, ↓reduceIte, hcov, Bool.not_true, Bool.false_eq_true]
    by_cases ht : W.contains target = true
    · rw [ht]; rfl
    · have htf : W.contains target = false := Bool.eq_false_iff.mpr ht
      simp only [htf, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
      left
      simp only [List.any_eq_true]
      refine ⟨a, by rwa [← List.mem_toFinset, hW], ?_⟩
      have hncW : W.contains (~~~a) = false :=
        Bool.eq_false_iff.mpr fun hm => hnc (hW ▸ List.mem_toFinset.mpr (List.contains_iff_mem.mp hm))
      simp only [hpc, hncW, Bool.not_false, Bool.and_self, Bool.true_and, Bool.or_eq_true]
      have hnd' : (~~~a :: dropL da a W).Nodup := by
        rw [List.nodup_cons]
        refine ⟨?_, nodup_dropL da a W hnd⟩
        intro hm
        have : ~~~a ∈ W := by
          cases da
          · exact hm
          · exact List.mem_of_mem_erase hm
        exact hnc (hW ▸ List.mem_toFinset.mpr this)
      have hW' : (~~~a :: dropL da a W).toFinset = insert (~~~a) (drop1 da a S) := by
        rw [List.toFinset_cons, toFinset_dropL da a W hnd, hW]
      have hrec := ih (~~~a :: dropL da a W) hnd' hW'
      cases da
      · right; exact hrec
      · left; exact hrec
  | @step_bin b u S a x isOr da db ha hx hax hpc hnc hnext ih =>
    intro W hnd hW
    have hcard : W.length ≤ b + 1 + 1 := by
      rw [← List.toFinset_card_of_nodup hnd, hW]
      exact reach_card_le (Reach.step_bin isOr da db ha hx hax hpc hnc hnext)
    have hcov : allCovered pairs (decide (0 < u)) W = true := by
      simp only [allCovered, List.all_eq_true, List.any_eq_true]
      intro pq hpq
      obtain ⟨hp16, hq16, hp, hq⟩ := hpairs pq hpq
      have hsep := reach_sep (Reach.step_bin isOr da db ha hx hax hpc hnc hnext) pq.1 pq.2 hp16 hq16 hp hq
      by_cases hu : u = 0
      · subst hu
        simp only [↓reduceIte] at hsep
        obtain ⟨w, hw, hwp, hwq⟩ := hsep
        refine ⟨w, by rwa [← List.mem_toFinset, hW], ?_⟩
        simp [covPair, hwp, hwq]
      · have hpos : 0 < u := Nat.pos_of_ne_zero hu
        simp only [hu, ↓reduceIte] at hsep
        obtain ⟨w, hw, hne⟩ := hsep
        refine ⟨w, by rwa [← List.mem_toFinset, hW], ?_⟩
        simp [covPair, hpos, hne]
    unfold search
    have hnotgt : ¬ W.length > b + 1 + 1 := by omega
    simp only [hnotgt, ↓reduceIte, hcov, Bool.not_true, Bool.false_eq_true]
    by_cases ht : W.contains target = true
    · rw [ht]; rfl
    · have htf : W.contains target = false := Bool.eq_false_iff.mpr ht
      simp only [htf, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
      right
      set c := if isOr then a ||| x else a &&& x
      have hncW : W.contains c = false :=
        Bool.eq_false_iff.mpr fun hm => hnc (hW ▸ List.mem_toFinset.mpr (List.contains_iff_mem.mp hm))
      have mk_branch : ∀ (u1 u2 : TT) (d1 d2 : Bool),
          (if isOr then u1 ||| u2 else u1 &&& u2) = c →
          drop2 d1 d2 u1 u2 S = drop2 da db a x S →
          ((isProper (u1 &&& u2) && !W.contains (u1 &&& u2) &&
              (search target pairs b u ((u1 &&& u2) :: dropL2 true true u1 u2 W) ||
               search target pairs b u ((u1 &&& u2) :: dropL2 true false u1 u2 W) ||
               search target pairs b u ((u1 &&& u2) :: dropL2 false true u1 u2 W) ||
               search target pairs b u ((u1 &&& u2) :: W))) ||
           (isProper (u1 ||| u2) && !W.contains (u1 ||| u2) &&
              (search target pairs b u ((u1 ||| u2) :: dropL2 true true u1 u2 W) ||
               search target pairs b u ((u1 ||| u2) :: dropL2 true false u1 u2 W) ||
               search target pairs b u ((u1 ||| u2) :: dropL2 false true u1 u2 W) ||
               search target pairs b u ((u1 ||| u2) :: W)))) = true := by
        intro u1 u2 d1 d2 hce hde
        have hnd' : (c :: dropL2 d1 d2 u1 u2 W).Nodup := by
          rw [List.nodup_cons]
          refine ⟨?_, nodup_dropL d2 u2 _ (nodup_dropL d1 u1 W hnd)⟩
          intro hm
          have h1 : c ∈ dropL d1 u1 W := by
            cases d2
            · exact hm
            · exact List.mem_of_mem_erase hm
          have h2 : c ∈ W := by
            cases d1
            · exact h1
            · exact List.mem_of_mem_erase h1
          exact hnc (hW ▸ List.mem_toFinset.mpr h2)
        have hW' : (c :: dropL2 d1 d2 u1 u2 W).toFinset = insert c (drop2 da db a x S) := by
          rw [List.toFinset_cons, dropL2, toFinset_dropL d2 u2 _ (nodup_dropL d1 u1 W hnd),
            toFinset_dropL d1 u1 W hnd, hW, ← hde]; rfl
        have hrec := ih (c :: dropL2 d1 d2 u1 u2 W) hnd' hW'
        cases isOr
        · simp only [Bool.false_eq_true, ↓reduceIte] at hce
          simp only [Bool.or_eq_true]; left
          rw [hce]
          simp only [hpc, hncW, Bool.not_false, Bool.and_self, Bool.true_and, Bool.or_eq_true]
          cases d1 <;> cases d2
          · right; exact hrec
          · left; right; exact hrec
          · left; left; right; exact hrec
          · left; left; left; exact hrec
        · simp only [↓reduceIte] at hce
          simp only [Bool.or_eq_true]; right
          rw [hce]
          simp only [hpc, hncW, Bool.not_false, Bool.and_self, Bool.true_and, Bool.or_eq_true]
          cases d1 <;> cases d2
          · right; exact hrec
          · left; right; exact hrec
          · left; left; right; exact hrec
          · left; left; left; exact hrec
      have hcomm_drop : drop2 db da x a S = drop2 da db a x S := by
        ext z
        cases da <;> cases db <;> simp [drop2, drop1, and_left_comm]
      exact tryPairsAux_or _ W a x (by rwa [← List.mem_toFinset, hW])
        (by rwa [← List.mem_toFinset, hW]) hax
        (mk_branch a x da db rfl rfl)
        (mk_branch x a db da (by cases isOr <;> simp [c, BitVec.and_comm, BitVec.or_comm]) hcomm_drop)

def mkPairs (mask : ℕ) : List (ℕ × ℕ) :=
  let t := BitVec.ofNat 16 mask
  (List.range 16).flatMap fun p =>
    if t.getLsbD p then
      (List.range 16).filterMap fun q => if !t.getLsbD q then some (p, q) else none
    else []

def validStarts (pairs : List (ℕ × ℕ)) (b u : ℕ) : List (List TT) :=
  inTTs.sublists.filter fun W => decide (W.length ≤ b + 1) && allCovered pairs (decide (0 < u)) W

lemma inTTs_nodup : inTTs.Nodup := by decide

lemma lb4x4_of_excl (mask K : ℕ)
    (hprop : isProper (BitVec.ofNat 16 mask) = true)
    (hexcl : ∀ b u, b + u ≤ K → (validStarts (mkPairs mask) b u).all (fun W => !search (BitVec.ofNat 16 mask) (mkPairs mask) b u W) = true) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ K ∧
      Represents (fun u v : Fin 4 => mask.testBit (4 * u.val + v.val)) C := by
  rintro ⟨C, hfit, hsz, hrep⟩
  have hmem := circuit_target_mem mask C hfit hrep hprop
  obtain ⟨b, u, S, hbu, hS, hR⟩ := extract_aux (BitVec.ofNat 16 mask) C.gates hfit inTTs hmem hprop
  let W := inTTs.filter (fun w => decide (w ∈ S))
  have hWnd : W.Nodup := inTTs_nodup.filter _
  have hWfs : W.toFinset = S := by
    ext w
    simp only [W, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨(hS w h).1, h⟩⟩
  have hpairs : ∀ pq ∈ mkPairs mask,
      pq.1 < 16 ∧ pq.2 < 16 ∧
      (BitVec.ofNat 16 mask).getLsbD pq.1 = true ∧ (BitVec.ofNat 16 mask).getLsbD pq.2 = false := by
    intro pq hpq
    simp only [mkPairs, List.mem_flatMap, List.mem_range] at hpq
    rcases hpq with ⟨p, hp16, hpq⟩
    split_ifs at hpq with hp
    · simp only [List.mem_filterMap, List.mem_range] at hpq
      rcases hpq with ⟨q, hq16, hq⟩
      split_ifs at hq with hnq
      · cases hq
        exact ⟨hp16, hq16, hp, Bool.eq_false_of_not_eq_true (by simpa using hnq)⟩
    · simp at hpq
  have hlen : W.length ≤ b + 1 := by
    rw [← List.toFinset_card_of_nodup hWnd, hWfs]
    exact reach_card_le hR
  have hcov : allCovered (mkPairs mask) (decide (0 < u)) W = true := by
    simp only [allCovered, List.all_eq_true, List.any_eq_true]
    intro pq hpq
    obtain ⟨hp16, hq16, hp, hq⟩ := hpairs pq hpq
    have hsep := reach_sep hR pq.1 pq.2 hp16 hq16 hp hq
    by_cases hu : u = 0
    · subst hu
      simp only [↓reduceIte] at hsep
      obtain ⟨w, hw, hwp, hwq⟩ := hsep
      refine ⟨w, by rwa [← List.mem_toFinset, hWfs], ?_⟩
      simp [covPair, hwp, hwq]
    · have hpos : 0 < u := Nat.pos_of_ne_zero hu
      simp only [hu, ↓reduceIte] at hsep
      obtain ⟨w, hw, hne⟩ := hsep
      refine ⟨w, by rwa [← List.mem_toFinset, hWfs], ?_⟩
      simp [covPair, hpos, hne]
  have hWmem : W ∈ validStarts (mkPairs mask) b u := by
    simp only [validStarts, List.mem_filter, List.mem_sublists, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.filter_sublist, hlen, hcov⟩
  have hfound := search_complete (BitVec.ofNat 16 mask) (mkPairs mask) hpairs hR W hWnd hWfs
  have hsz' : C.gates.length ≤ K := hsz
  have hbad := List.all_eq_true.mp (hexcl b u (by omega)) W hWmem
  rw [hfound] at hbad
  exact Bool.noConfusion hbad

set_option maxRecDepth 20000 in
theorem main_lb : ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧
    Represents (fun u v : Fin 4 => (14303 : ℕ).testBit (4 * u.val + v.val)) C := by
  apply lb4x4_of_excl 14303 6 (by decide)
  have hall : (List.range 7).all (fun u => (List.range (7 - u)).all (fun b =>
      (validStarts (mkPairs 14303) b u).all (fun W => !search (BitVec.ofNat 16 14303) (mkPairs 14303) b u W))) = true := by
    decide +kernel
  intro b u hbu
  have h1 := List.all_eq_true.mp hall u (List.mem_range.mpr (by omega))
  exact List.all_eq_true.mp h1 b (List.mem_range.mpr (by omega))

end PEqualNP.Outside.L_meta_29738_aux

theorem PEqualNP.Outside.L_meta_29738 :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (14303 : ℕ).testBit (4 * u.val + v.val)) C) :=
  PEqualNP.Outside.L_meta_29738_aux.main_lb
