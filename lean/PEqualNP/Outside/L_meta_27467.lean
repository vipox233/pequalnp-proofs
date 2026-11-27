import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27467_aux


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev TT := BitVec 240

def zeroTT : TT := 0#240
def oneTT : TT := BitVec.allOnes 240

def isProper (w : TT) : Bool := (w != zeroTT) && (w != oneTT)

def inTTs : List TT :=
  [0xdd44ad46261cc395899d77db38aaa5dd04a1420614c3948195575b18a885#240, 0xd39fe13d53e6ce9c8b4635f39e94ffc39fe03d0266cc9c094435f31e84bf#240, 0xa4b37ebeef73fceefc76cf0669c94984b36c3e6971d4e69c56cd0668c849#240, 0xbbd2823bfed9755d72fb9b350fe752b852820af699711d62fb1a340f6752#240, 0xe8743af66a7affba2d187ec6f475bf28543af66a4aff182d0836c2a455bf#240, 0x72b5dd8898cf2ebdcff205e871a0f072a5d988988f2ebdc7a201487120b#240, 0xa42f55c3952e9b32a43bdfe4ced30aa42515c1952e0b32a03bdbe4c89300#240, 0x36c5a6f88ea7647b75ad819a378e2532c5a6f08ea6247b75ad818a378e24#240, 0x7b5cf93571fd39d68f72b0adb9a5f07348593571fd38c28e32a08db1a160#240, 0x22bb52b9d9e33c6a76628824c7555a22fb5ebdf9eb3c6b7e6aa8a4e7577a#240, 0x178bc50995850045d2e781390b8a40d7abc50995b500e7d2f7c93d5baa40#240]


def baseTTs : List TT := [0xdd44ad46261cc395899d77db38aaa5dd04a1420614c3948195575b18a885#240, 0xd39fe13d53e6ce9c8b4635f39e94ffc39fe03d0266cc9c094435f31e84bf#240, 0xa4b37ebeef73fceefc76cf0669c94984b36c3e6971d4e69c56cd0668c849#240, 0xbbd2823bfed9755d72fb9b350fe752b852820af699711d62fb1a340f6752#240, 0xe8743af66a7affba2d187ec6f475bf28543af66a4aff182d0836c2a455bf#240, 0x72b5dd8898cf2ebdcff205e871a0f072a5d988988f2ebdc7a201487120b#240, 0xa42f55c3952e9b32a43bdfe4ced30aa42515c1952e0b32a03bdbe4c89300#240, 0x36c5a6f88ea7647b75ad819a378e2532c5a6f08ea6247b75ad818a378e24#240, 0x7b5cf93571fd39d68f72b0adb9a5f07348593571fd38c28e32a08db1a160#240]

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

lemma gateTT_bit (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (ws : List TT) (bs : List Bool) (idx : ℕ) (hidx : idx < 240)
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
    (ws : List TT) (bs : List Bool) (hlen : ws.length = bs.length) (idx : ℕ) (hidx : idx < 240)
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
    ∃ b u S, b + u ≤ gs.length ∧ (∀ w ∈ S, w ∈ ws ∧ isProper w = true) ∧ Reach target b u S ∧
      (u = 0 ∨ ∃ g ∈ gs, g.op = GateOp.not) := by
  induction gs generalizing ws with
  | nil =>
    refine ⟨0, 0, {target}, by simp, ?_, Reach.done, Or.inl rfl⟩
    intro w hw
    simp only [Finset.mem_singleton] at hw
    subst hw
    exact ⟨ht, htp⟩
  | cons g rest ih =>
    simp only [evalTT, List.foldl_cons] at ht
    obtain ⟨b, u, S', hbu, hS', hR', hu'⟩ :=
      ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) (ws ++ [gateTT g ws]) ht
    have hul : u = 0 ∨ ∃ g' ∈ g :: rest, g'.op = GateOp.not :=
      hu'.imp_right (fun ⟨g', hg', h⟩ => ⟨g', List.mem_cons_of_mem g hg', h⟩)
    set c := gateTT g ws
    by_cases hcS : c ∈ S'
    · by_cases hcws : c ∈ ws
      · refine ⟨b, u, S', by simp; omega, ?_, hR', hul⟩
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
            ∃ b' u' S, b' + u' ≤ (g :: rest).length ∧ (∀ w ∈ S, w ∈ ws ∧ isProper w = true) ∧ Reach target b' u' S ∧
              (u' = 0 ∨ ∃ g' ∈ g :: rest, g'.op = GateOp.not) := by
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
          refine ⟨b + 1, u, S, by simp; omega, ?_, ?_, hul⟩
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
            refine ⟨b, u + 1, S, by simp; omega, ?_, ?_, Or.inr ⟨g, List.mem_cons_self .., h⟩⟩
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
    · refine ⟨b, u, S', by simp; omega, ?_, hR', hul⟩
      intro w hw
      obtain ⟨hm, hp⟩ := hS' w hw
      simp only [List.mem_append, List.mem_singleton] at hm
      exact ⟨hm.resolve_right (fun h => hcS (h ▸ hw)), hp⟩

lemma reach_sep {target : TT} {b u : ℕ} {S : Finset TT} (h : Reach target b u S)
    (p q : ℕ) (hp16 : p < 240) (hq16 : q < 240)
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

def tryNotF (rec : List TT → Bool) (W : List TT) (a : TT) : Bool :=
  let c := ~~~a
  isProper c && !W.contains c && (rec (c :: dropL true a W) || rec (c :: W))

def tryOpF (prev : List TT → Bool) (W : List TT) (a x c : TT) : Bool :=
  isProper c && !W.contains c &&
  (prev (c :: dropL2 true true a x W) || prev (c :: dropL2 true false a x W) ||
   prev (c :: dropL2 false true a x W) || prev (c :: W))

def tryBinF (prev : List TT → Bool) (W : List TT) (a x : TT) : Bool :=
  tryOpF prev W a x (a &&& x) || tryOpF prev W a x (a ||| x)

def searchU (target : TT) (cov : Bool → List TT → Bool) (b : ℕ) (prev : ℕ → List TT → Bool) :
    ℕ → List TT → Bool
  | u, W =>
    if W.length > b + 1 then false
    else if W.contains target then true
    else if !cov (decide (0 < u)) W then false
    else
      let tryNot :=
        match u with
        | 0 => false
        | u' + 1 => W.any (tryNotF (searchU target cov b prev u') W)
      let tryBin :=
        match b with
        | 0 => false
        | _ + 1 => tryPairsAux (tryBinF (prev u) W) W
      tryNot || tryBin

def searchB (target : TT) (cov : Bool → List TT → Bool) : ℕ → ℕ → List TT → Bool
  | 0 => searchU target cov 0 (fun _ _ => false)
  | b' + 1 => searchU target cov (b' + 1) (searchB target cov b')

def search (target : TT) (cov : Bool → List TT → Bool) (b u : ℕ) (W : List TT) : Bool :=
  searchB target cov b u W

lemma search_unfold (target : TT) (cov : Bool → List TT → Bool) (b u : ℕ) (W : List TT) :
    search target cov b u W = (
      if W.length > b + 1 then false
      else if W.contains target then true
      else if !cov (decide (0 < u)) W then false
      else
        let tryNot :=
          match u with
          | 0 => false
          | u' + 1 =>
            W.any fun a =>
              let c := ~~~a
              isProper c && !W.contains c &&
              (search target cov b u' (c :: dropL true a W) ||
               search target cov b u' (c :: W))
        let tryBin :=
          match b with
          | 0 => false
          | b' + 1 =>
            tryPairsAux (fun a x =>
              let tryOp (c : TT) :=
                isProper c && !W.contains c &&
                (search target cov b' u (c :: dropL2 true true a x W) ||
                 search target cov b' u (c :: dropL2 true false a x W) ||
                 search target cov b' u (c :: dropL2 false true a x W) ||
                 search target cov b' u (c :: W))
              tryOp (a &&& x) || tryOp (a ||| x)) W
        tryNot || tryBin) := by
  cases b <;> cases u <;> rfl

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

lemma search_complete (target : TT) (pairs : List (ℕ × ℕ)) (cov : Bool → List TT → Bool)
    (hcovOK : ∀ an W, allCovered pairs an W = true → cov an W = true)
    (hpairs : ∀ pq ∈ pairs, pq.1 < 240 ∧ pq.2 < 240 ∧ target.getLsbD pq.1 = true ∧ target.getLsbD pq.2 = false)
    {b u : ℕ} {S : Finset TT} (hR : Reach target b u S) :
    ∀ W : List TT, W.Nodup → W.toFinset = S → search target cov b u W = true := by
  induction hR with
  | done =>
    intro W hnd hW
    rw [search_unfold]
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
    rw [search_unfold]
    have hnotgt : ¬ W.length > b + 1 := by omega
    have hcov2 := hcovOK _ W hcov
    simp only [hnotgt, ↓reduceIte, hcov2, Bool.not_true, Bool.false_eq_true]
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
    rw [search_unfold]
    have hnotgt : ¬ W.length > b + 1 + 1 := by omega
    have hcov2 := hcovOK _ W hcov
    simp only [hnotgt, ↓reduceIte, hcov2, Bool.not_true, Bool.false_eq_true]
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
              (search target cov b u ((u1 &&& u2) :: dropL2 true true u1 u2 W) ||
               search target cov b u ((u1 &&& u2) :: dropL2 true false u1 u2 W) ||
               search target cov b u ((u1 &&& u2) :: dropL2 false true u1 u2 W) ||
               search target cov b u ((u1 &&& u2) :: W))) ||
           (isProper (u1 ||| u2) && !W.contains (u1 ||| u2) &&
              (search target cov b u ((u1 ||| u2) :: dropL2 true true u1 u2 W) ||
               search target cov b u ((u1 ||| u2) :: dropL2 true false u1 u2 W) ||
               search target cov b u ((u1 ||| u2) :: dropL2 false true u1 u2 W) ||
               search target cov b u ((u1 ||| u2) :: W)))) = true := by
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

def lowM : TT := oneTT >>> 120

def goal : TT := ~~~lowM

def sepv (an : Bool) (w : TT) : TT :=
  if an then ((w >>> 120) ^^^ w) else ((w >>> 120) &&& ~~~w)

def fastCov (an : Bool) (W : List TT) : Bool :=
  ((W.foldr (fun w acc => sepv an w ||| acc) zeroTT) &&& lowM) == lowM

def mkPairs : List (ℕ × ℕ) := (List.range 120).map fun k => (120 + k, k)

lemma fold_bit (an : Bool) (W : List TT) (j : ℕ) :
    (W.foldr (fun w acc => sepv an w ||| acc) zeroTT).getLsbD j = W.any (fun w => (sepv an w).getLsbD j) := by
  induction W with
  | nil => simp [zeroTT]
  | cons w W ih => simp [BitVec.getLsbD_or, ih]

lemma sepv_bit (an : Bool) (w : TT) (k : ℕ) (hk : k < 120) :
    (sepv an w).getLsbD k = covPair an w (120 + k, k) := by
  have hk2 : k < 240 := by omega
  cases an <;> simp [sepv, covPair, hk2]

lemma lowM_bit (j : ℕ) : lowM.getLsbD j = decide (120 + j < 240) := by
  unfold lowM
  rw [BitVec.getLsbD_ushiftRight]
  unfold oneTT
  rw [BitVec.getLsbD_allOnes]

lemma fastCov_of_all (an : Bool) (W : List TT) (h : allCovered mkPairs an W = true) : fastCov an W = true := by
  simp only [fastCov, beq_iff_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_and, lowM_bit]
  by_cases hjP : j < 120
  · have h1 : 120 + j < 240 := by omega
    rw [decide_eq_true h1, Bool.and_true, fold_bit]
    simp only [allCovered, List.all_eq_true] at h
    have hm : (120 + j, j) ∈ mkPairs := by
      simp only [mkPairs, List.mem_map, List.mem_range]
      exact ⟨j, hjP, rfl⟩
    have h2 := h _ hm
    simp only [List.any_eq_true] at h2 ⊢
    obtain ⟨w, hw, hc⟩ := h2
    exact ⟨w, hw, by rw [sepv_bit an w j hjP]; exact hc⟩
  · have h1 : ¬ (120 + j < 240) := by omega
    rw [decide_eq_false h1, Bool.and_false]

lemma goal_bit (i : ℕ) : goal.getLsbD i = (decide (i < 240) && !decide (120 + i < 240)) := by
  unfold goal
  rw [BitVec.getLsbD_not, lowM_bit]

lemma hpairs_ok : ∀ pq ∈ mkPairs,
    pq.1 < 240 ∧ pq.2 < 240 ∧ goal.getLsbD pq.1 = true ∧ goal.getLsbD pq.2 = false := by
  intro pq hpq
  simp only [mkPairs, List.mem_map, List.mem_range] at hpq
  obtain ⟨k, hk, rfl⟩ := hpq
  refine ⟨by simp; omega, by simp; omega, ?_, ?_⟩
  · rw [goal_bit]; simp; omega
  · rw [goal_bit]; simp; omega

lemma goal_proper : isProper goal = true := by decide +kernel

def goodStarts : List (List TT) :=
  [[0xdd44ad46261cc395899d77db38aaa5dd04a1420614c3948195575b18a885#240, 0xd39fe13d53e6ce9c8b4635f39e94ffc39fe03d0266cc9c094435f31e84bf#240, 0xa4b37ebeef73fceefc76cf0669c94984b36c3e6971d4e69c56cd0668c849#240, 0xbbd2823bfed9755d72fb9b350fe752b852820af699711d62fb1a340f6752#240, 0xe8743af66a7affba2d187ec6f475bf28543af66a4aff182d0836c2a455bf#240, 0x72b5dd8898cf2ebdcff205e871a0f072a5d988988f2ebdc7a201487120b#240, 0xa42f55c3952e9b32a43bdfe4ced30aa42515c1952e0b32a03bdbe4c89300#240, 0x36c5a6f88ea7647b75ad819a378e2532c5a6f08ea6247b75ad818a378e24#240, 0x7b5cf93571fd39d68f72b0adb9a5f07348593571fd38c28e32a08db1a160#240],
  [0xd39fe13d53e6ce9c8b4635f39e94ffc39fe03d0266cc9c094435f31e84bf#240, 0xa4b37ebeef73fceefc76cf0669c94984b36c3e6971d4e69c56cd0668c849#240, 0xbbd2823bfed9755d72fb9b350fe752b852820af699711d62fb1a340f6752#240, 0xe8743af66a7affba2d187ec6f475bf28543af66a4aff182d0836c2a455bf#240, 0x72b5dd8898cf2ebdcff205e871a0f072a5d988988f2ebdc7a201487120b#240, 0xa42f55c3952e9b32a43bdfe4ced30aa42515c1952e0b32a03bdbe4c89300#240, 0x36c5a6f88ea7647b75ad819a378e2532c5a6f08ea6247b75ad818a378e24#240, 0x7b5cf93571fd39d68f72b0adb9a5f07348593571fd38c28e32a08db1a160#240, 0x22bb52b9d9e33c6a76628824c7555a22fb5ebdf9eb3c6b7e6aa8a4e7577a#240],
  [0xdd44ad46261cc395899d77db38aaa5dd04a1420614c3948195575b18a885#240, 0xd39fe13d53e6ce9c8b4635f39e94ffc39fe03d0266cc9c094435f31e84bf#240, 0xa4b37ebeef73fceefc76cf0669c94984b36c3e6971d4e69c56cd0668c849#240, 0xbbd2823bfed9755d72fb9b350fe752b852820af699711d62fb1a340f6752#240, 0xe8743af66a7affba2d187ec6f475bf28543af66a4aff182d0836c2a455bf#240, 0x72b5dd8898cf2ebdcff205e871a0f072a5d988988f2ebdc7a201487120b#240, 0xa42f55c3952e9b32a43bdfe4ced30aa42515c1952e0b32a03bdbe4c89300#240, 0x36c5a6f88ea7647b75ad819a378e2532c5a6f08ea6247b75ad818a378e24#240, 0x7b5cf93571fd39d68f72b0adb9a5f07348593571fd38c28e32a08db1a160#240, 0x22bb52b9d9e33c6a76628824c7555a22fb5ebdf9eb3c6b7e6aa8a4e7577a#240],
  [0xdd44ad46261cc395899d77db38aaa5dd04a1420614c3948195575b18a885#240, 0xd39fe13d53e6ce9c8b4635f39e94ffc39fe03d0266cc9c094435f31e84bf#240, 0xa4b37ebeef73fceefc76cf0669c94984b36c3e6971d4e69c56cd0668c849#240, 0xbbd2823bfed9755d72fb9b350fe752b852820af699711d62fb1a340f6752#240, 0x72b5dd8898cf2ebdcff205e871a0f072a5d988988f2ebdc7a201487120b#240, 0xa42f55c3952e9b32a43bdfe4ced30aa42515c1952e0b32a03bdbe4c89300#240, 0x36c5a6f88ea7647b75ad819a378e2532c5a6f08ea6247b75ad818a378e24#240, 0x7b5cf93571fd39d68f72b0adb9a5f07348593571fd38c28e32a08db1a160#240, 0x178bc50995850045d2e781390b8a40d7abc50995b500e7d2f7c93d5baa40#240],
  [0xdd44ad46261cc395899d77db38aaa5dd04a1420614c3948195575b18a885#240, 0xd39fe13d53e6ce9c8b4635f39e94ffc39fe03d0266cc9c094435f31e84bf#240, 0xa4b37ebeef73fceefc76cf0669c94984b36c3e6971d4e69c56cd0668c849#240, 0xbbd2823bfed9755d72fb9b350fe752b852820af699711d62fb1a340f6752#240, 0xe8743af66a7affba2d187ec6f475bf28543af66a4aff182d0836c2a455bf#240, 0x72b5dd8898cf2ebdcff205e871a0f072a5d988988f2ebdc7a201487120b#240, 0xa42f55c3952e9b32a43bdfe4ced30aa42515c1952e0b32a03bdbe4c89300#240, 0x36c5a6f88ea7647b75ad819a378e2532c5a6f08ea6247b75ad818a378e24#240, 0x7b5cf93571fd39d68f72b0adb9a5f07348593571fd38c28e32a08db1a160#240, 0x178bc50995850045d2e781390b8a40d7abc50995b500e7d2f7c93d5baa40#240],
  [0xd39fe13d53e6ce9c8b4635f39e94ffc39fe03d0266cc9c094435f31e84bf#240, 0xa4b37ebeef73fceefc76cf0669c94984b36c3e6971d4e69c56cd0668c849#240, 0xbbd2823bfed9755d72fb9b350fe752b852820af699711d62fb1a340f6752#240, 0x72b5dd8898cf2ebdcff205e871a0f072a5d988988f2ebdc7a201487120b#240, 0xa42f55c3952e9b32a43bdfe4ced30aa42515c1952e0b32a03bdbe4c89300#240, 0x36c5a6f88ea7647b75ad819a378e2532c5a6f08ea6247b75ad818a378e24#240, 0x7b5cf93571fd39d68f72b0adb9a5f07348593571fd38c28e32a08db1a160#240, 0x22bb52b9d9e33c6a76628824c7555a22fb5ebdf9eb3c6b7e6aa8a4e7577a#240, 0x178bc50995850045d2e781390b8a40d7abc50995b500e7d2f7c93d5baa40#240],
  [0xdd44ad46261cc395899d77db38aaa5dd04a1420614c3948195575b18a885#240, 0xd39fe13d53e6ce9c8b4635f39e94ffc39fe03d0266cc9c094435f31e84bf#240, 0xa4b37ebeef73fceefc76cf0669c94984b36c3e6971d4e69c56cd0668c849#240, 0xbbd2823bfed9755d72fb9b350fe752b852820af699711d62fb1a340f6752#240, 0x72b5dd8898cf2ebdcff205e871a0f072a5d988988f2ebdc7a201487120b#240, 0xa42f55c3952e9b32a43bdfe4ced30aa42515c1952e0b32a03bdbe4c89300#240, 0x36c5a6f88ea7647b75ad819a378e2532c5a6f08ea6247b75ad818a378e24#240, 0x7b5cf93571fd39d68f72b0adb9a5f07348593571fd38c28e32a08db1a160#240, 0x22bb52b9d9e33c6a76628824c7555a22fb5ebdf9eb3c6b7e6aa8a4e7577a#240, 0x178bc50995850045d2e781390b8a40d7abc50995b500e7d2f7c93d5baa40#240],
  [0xd39fe13d53e6ce9c8b4635f39e94ffc39fe03d0266cc9c094435f31e84bf#240, 0xa4b37ebeef73fceefc76cf0669c94984b36c3e6971d4e69c56cd0668c849#240, 0xbbd2823bfed9755d72fb9b350fe752b852820af699711d62fb1a340f6752#240, 0xe8743af66a7affba2d187ec6f475bf28543af66a4aff182d0836c2a455bf#240, 0x72b5dd8898cf2ebdcff205e871a0f072a5d988988f2ebdc7a201487120b#240, 0xa42f55c3952e9b32a43bdfe4ced30aa42515c1952e0b32a03bdbe4c89300#240, 0x36c5a6f88ea7647b75ad819a378e2532c5a6f08ea6247b75ad818a378e24#240, 0x7b5cf93571fd39d68f72b0adb9a5f07348593571fd38c28e32a08db1a160#240, 0x22bb52b9d9e33c6a76628824c7555a22fb5ebdf9eb3c6b7e6aa8a4e7577a#240, 0x178bc50995850045d2e781390b8a40d7abc50995b500e7d2f7c93d5baa40#240],
  [0xdd44ad46261cc395899d77db38aaa5dd04a1420614c3948195575b18a885#240, 0xd39fe13d53e6ce9c8b4635f39e94ffc39fe03d0266cc9c094435f31e84bf#240, 0xa4b37ebeef73fceefc76cf0669c94984b36c3e6971d4e69c56cd0668c849#240, 0xbbd2823bfed9755d72fb9b350fe752b852820af699711d62fb1a340f6752#240, 0xe8743af66a7affba2d187ec6f475bf28543af66a4aff182d0836c2a455bf#240, 0x72b5dd8898cf2ebdcff205e871a0f072a5d988988f2ebdc7a201487120b#240, 0xa42f55c3952e9b32a43bdfe4ced30aa42515c1952e0b32a03bdbe4c89300#240, 0x36c5a6f88ea7647b75ad819a378e2532c5a6f08ea6247b75ad818a378e24#240, 0x7b5cf93571fd39d68f72b0adb9a5f07348593571fd38c28e32a08db1a160#240, 0x22bb52b9d9e33c6a76628824c7555a22fb5ebdf9eb3c6b7e6aa8a4e7577a#240, 0x178bc50995850045d2e781390b8a40d7abc50995b500e7d2f7c93d5baa40#240]]

lemma good_mem : ∀ W ∈ inTTs.sublists, fastCov true W = true → W ∈ goodStarts := by
  decide +kernel

lemma covPair_weak (an : Bool) (w : TT) (pq : ℕ × ℕ) (h : covPair an w pq = true) :
    covPair true w pq = true := by
  cases an <;> simp_all [covPair]

lemma allCovered_weak (an : Bool) (W : List TT) (h : allCovered mkPairs an W = true) :
    allCovered mkPairs true W = true := by
  simp only [allCovered, List.all_eq_true, List.any_eq_true] at h ⊢
  intro pq hpq
  obtain ⟨w, hw, hc⟩ := h pq hpq
  exact ⟨w, hw, covPair_weak an w pq hc⟩

def validStarts (b u : ℕ) : List (List TT) :=
  goodStarts.filter fun W => decide (W.length ≤ b + 1) && fastCov (decide (0 < u)) W

lemma inP_nodup : (inTTs.filter (fun w => isProper w)).Nodup := by decide +kernel

def MONO : Bool := false

lemma core_lb (gs : List Gate) (K : ℕ) (hlen : gs.length ≤ K)
    (hfit : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hmono : MONO = true → ∀ g ∈ gs, g.op ≠ GateOp.not)
    (hmem : goal ∈ evalTT gs inTTs)
    (hexcl : ∀ b u, b + u ≤ K → (MONO = true → u = 0) →
      (validStarts b u).all (fun W => !search goal fastCov b u W) = true) : False := by
  obtain ⟨b, u, S, hbu, hS, hR, hu⟩ := extract_aux goal gs hfit inTTs hmem goal_proper
  have hu0 : MONO = true → u = 0 := by
    intro hM
    rcases hu with hu | ⟨g, hg, hn⟩
    · exact hu
    · exact absurd hn (hmono hM g hg)
  let W := (inTTs.filter (fun w => isProper w)).filter (fun w => decide (w ∈ S))
  have hWnd : W.Nodup := inP_nodup.filter _
  have hWfs : W.toFinset = S := by
    ext w
    simp only [W, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨⟨(hS w h).1, (hS w h).2⟩, h⟩⟩
  have hlenW : W.length ≤ b + 1 := by
    rw [← List.toFinset_card_of_nodup hWnd, hWfs]
    exact reach_card_le hR
  have hcov : allCovered mkPairs (decide (0 < u)) W = true := by
    simp only [allCovered, List.all_eq_true, List.any_eq_true]
    intro pq hpq
    obtain ⟨hp16, hq16, hp, hq⟩ := hpairs_ok pq hpq
    have hsep := reach_sep hR pq.1 pq.2 hp16 hq16 hp hq
    by_cases hu' : u = 0
    · subst hu'
      simp only [↓reduceIte] at hsep
      obtain ⟨w, hw, hwp, hwq⟩ := hsep
      refine ⟨w, by rwa [← List.mem_toFinset, hWfs], ?_⟩
      simp [covPair, hwp, hwq]
    · have hpos : 0 < u := Nat.pos_of_ne_zero hu'
      simp only [hu', ↓reduceIte] at hsep
      obtain ⟨w, hw, hne⟩ := hsep
      refine ⟨w, by rwa [← List.mem_toFinset, hWfs], ?_⟩
      simp [covPair, hpos, hne]
  have hWmem : W ∈ validStarts b u := by
    simp only [validStarts, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨good_mem W (List.mem_sublists.mpr (List.filter_sublist.trans List.filter_sublist))
      (fastCov_of_all _ W (allCovered_weak _ W hcov)), hlenW, fastCov_of_all _ W hcov⟩
  have hfound := search_complete goal mkPairs fastCov fastCov_of_all hpairs_ok hR W hWnd hWfs
  have hbad := List.all_eq_true.mp (hexcl b u (by omega) hu0) W hWmem
  rw [hfound] at hbad
  exact Bool.noConfusion hbad

lemma target_mem (C : Circuit) (hfit : FanInTwo C) (rowIn : ℕ → List Bool)
    (hlen : ∀ idx < 240, (rowIn idx).length = 9)
    (hbits : ∀ idx < 240, ∀ i < 9, (baseTTs.getD i zeroTT).getLsbD idx = (rowIn idx).getD i false)
    (hev : ∀ idx < 240, C.eval (rowIn idx) = goal.getLsbD idx) :
    goal ∈ evalTT C.gates baseTTs := by
  have hinlen : baseTTs.length = 9 := by decide
  have heq : (evalTT C.gates baseTTs).getD C.output zeroTT = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro idx hidx
    have hmatch : ∀ i, (baseTTs.getD i zeroTT).getLsbD idx = (rowIn idx).getD i false := by
      intro i
      by_cases hi : i < 9
      · exact hbits idx hidx i hi
      · have h1 : baseTTs.getD i zeroTT = zeroTT := by
          simp [List.getD, List.getElem?_eq_none (show baseTTs.length ≤ i by omega)]
        have h2 : (rowIn idx).getD i false = false := by
          simp [List.getD, List.getElem?_eq_none (show (rowIn idx).length ≤ i by rw [hlen idx hidx]; omega)]
        rw [h1, h2]
        simp [zeroTT]
    have hbit := evalTT_bit C.gates hfit baseTTs (rowIn idx) (by rw [hinlen, hlen idx hidx]) idx hidx hmatch C.output
    rw [hbit]
    have hr := hev idx hidx
    simp only [Circuit.eval, Circuit.wires] at hr
    exact hr
  by_cases hlt : C.output < (evalTT C.gates baseTTs).length
  · rw [← heq]
    simp only [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_mem hlt
  · have hz : (evalTT C.gates baseTTs).getD C.output zeroTT = zeroTT := by
      simp [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt)]
    rw [hz] at heq
    have hp := goal_proper
    rw [← heq] at hp
    simp [isProper, zeroTT] at hp


def notKids (b u' : ℕ) (W : List TT) : List (ℕ × ℕ × List TT) :=
  W.flatMap fun a => if isProper (~~~a) && !W.contains (~~~a) then
    [(b, u', ~~~a :: dropL true a W), (b, u', ~~~a :: W)] else []

def opKids (b' u : ℕ) (W : List TT) (a x c : TT) : List (ℕ × ℕ × List TT) :=
  if isProper c && !W.contains c then
    [(b', u, c :: dropL2 true true a x W), (b', u, c :: dropL2 true false a x W),
     (b', u, c :: dropL2 false true a x W), (b', u, c :: W)] else []

def pairKids (b' u : ℕ) (W : List TT) : List TT → List (ℕ × ℕ × List TT)
  | [] => []
  | a :: rest => rest.flatMap (fun x => opKids b' u W a x (a &&& x) ++ opKids b' u W a x (a ||| x)) ++
      pairKids b' u W rest

def kids (b u : ℕ) (W : List TT) : List (ℕ × ℕ × List TT) :=
  (match u with
   | 0 => []
   | u' + 1 => notKids b u' W) ++
  (match b with
   | 0 => []
   | b' + 1 => pairKids b' u W W)

lemma tpa_false (f : TT → TT → Bool) (g : TT → TT → List (ℕ × ℕ × List TT)) (p : ℕ × ℕ × List TT → Bool)
    (hfg : ∀ a x, (g a x).all p = true → f a x = false) :
    ∀ L : List TT, (L.rec [] (fun a rest ih => rest.flatMap (g a) ++ ih) : List (ℕ × ℕ × List TT)).all p = true →
      tryPairsAux f L = false := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons a rest ih =>
    intro h
    simp only [List.all_append, Bool.and_eq_true] at h
    simp only [tryPairsAux, Bool.or_eq_false_iff]
    refine ⟨?_, ih h.2⟩
    rw [List.any_eq_false]
    intro x hx
    have := h.1
    rw [List.all_eq_true] at this
    intro hf
    have h2 : (g a x).all p = true := by
      rw [List.all_eq_true]
      intro k hk
      exact this k (List.mem_flatMap.mpr ⟨x, hx, hk⟩)
    rw [hfg a x h2] at hf
    exact Bool.noConfusion hf

lemma pairKids_eq (b' u : ℕ) (W L : List TT) :
    pairKids b' u W L = (L.rec [] (fun a rest ih =>
      rest.flatMap (fun x => opKids b' u W a x (a &&& x) ++ opKids b' u W a x (a ||| x)) ++ ih)) := by
  induction L with
  | nil => rfl
  | cons a rest ih => simp only [pairKids, ih]

lemma search_false_of_kids (target : TT) (cov : Bool → List TT → Bool) (b u : ℕ) (W : List TT)
    (hc : W.contains target = false)
    (hk : (kids b u W).all (fun k => !search target cov k.1 k.2.1 k.2.2) = true) :
    search target cov b u W = false := by
  rw [search_unfold]
  simp only [kids, List.all_append, Bool.and_eq_true] at hk
  obtain ⟨hn, hb⟩ := hk
  by_cases h1 : W.length > b + 1
  · simp [h1]
  simp only [h1, ↓reduceIte, hc, Bool.false_eq_true]
  by_cases h2 : cov (decide (0 < u)) W = true
  swap
  · simp [h2]
  simp only [h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_false_iff]
  constructor
  · cases u with
    | zero => rfl
    | succ u' =>
      simp only [notKids, List.all_eq_true, List.mem_flatMap] at hn
      rw [List.any_eq_false]
      intro a ha
      intro hT
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hT
      obtain ⟨⟨hp, hnc⟩, hs⟩ := hT
      have hcond : (isProper (~~~a) && !W.contains (~~~a)) = true := by rw [hp, hnc]; rfl
      rcases hs with hs | hs
      · have := hn (b, u', ~~~a :: dropL true a W) ⟨a, ha, by rw [if_pos hcond]; simp⟩
        simp [hs] at this
      · have := hn (b, u', ~~~a :: W) ⟨a, ha, by rw [if_pos hcond]; simp⟩
        simp [hs] at this
  · cases b with
    | zero => rfl
    | succ b' =>
      dsimp only at hb
      rw [pairKids_eq] at hb
      refine tpa_false _ (fun a x => opKids b' u W a x (a &&& x) ++ opKids b' u W a x (a ||| x)) _ ?_ W hb
      intro a x hax
      simp only [List.all_append, Bool.and_eq_true] at hax
      have hop : ∀ c, (opKids b' u W a x c).all (fun k => !search target cov k.1 k.2.1 k.2.2) = true →
          (isProper c && !W.contains c &&
            (search target cov b' u (c :: dropL2 true true a x W) ||
             search target cov b' u (c :: dropL2 true false a x W) ||
             search target cov b' u (c :: dropL2 false true a x W) ||
             search target cov b' u (c :: W))) = false := by
        intro c hc'
        unfold opKids at hc'
        by_cases hcond : (isProper c && !W.contains c) = true
        · rw [if_pos hcond] at hc'
          simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true'] at hc'
          obtain ⟨e1, e2, e3, e4⟩ := hc'
          simp [e1, e2, e3, e4]
        · simp only [Bool.not_eq_true] at hcond
          rw [hcond]
          rfl
      simp only [Bool.or_eq_false_iff]
      exact ⟨hop _ hax.1, hop _ hax.2⟩


lemma all_split {α : Type} (l : List α) (p : α → Bool) (s m : ℕ)
    (h1 : ((l.drop s).take m).all p = true) (h2 : (l.drop (s + m)).all p = true) :
    (l.drop s).all p = true := by
  rw [← List.take_append_drop m (l.drop s), List.all_append, h1, List.drop_drop]
  simpa [Nat.add_comm] using h2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_0_0_0 : ((validStarts 0 0).drop 0).all (fun W => !search goal fastCov 0 0 W) = true := by
  decide +kernel

lemma ex_0_0 : (validStarts 0 0).all (fun W => !search goal fastCov 0 0 W) = true := by
  have h := ex_0_0_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_0_1_0 : ((validStarts 0 1).drop 0).all (fun W => !search goal fastCov 0 1 W) = true := by
  decide +kernel

lemma ex_0_1 : (validStarts 0 1).all (fun W => !search goal fastCov 0 1 W) = true := by
  have h := ex_0_1_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_0_2_0 : ((validStarts 0 2).drop 0).all (fun W => !search goal fastCov 0 2 W) = true := by
  decide +kernel

lemma ex_0_2 : (validStarts 0 2).all (fun W => !search goal fastCov 0 2 W) = true := by
  have h := ex_0_2_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_0_3_0 : ((validStarts 0 3).drop 0).all (fun W => !search goal fastCov 0 3 W) = true := by
  decide +kernel

lemma ex_0_3 : (validStarts 0 3).all (fun W => !search goal fastCov 0 3 W) = true := by
  have h := ex_0_3_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_0_4_0 : ((validStarts 0 4).drop 0).all (fun W => !search goal fastCov 0 4 W) = true := by
  decide +kernel

lemma ex_0_4 : (validStarts 0 4).all (fun W => !search goal fastCov 0 4 W) = true := by
  have h := ex_0_4_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_0_5_0 : ((validStarts 0 5).drop 0).all (fun W => !search goal fastCov 0 5 W) = true := by
  decide +kernel

lemma ex_0_5 : (validStarts 0 5).all (fun W => !search goal fastCov 0 5 W) = true := by
  have h := ex_0_5_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_0_6_0 : ((validStarts 0 6).drop 0).all (fun W => !search goal fastCov 0 6 W) = true := by
  decide +kernel

lemma ex_0_6 : (validStarts 0 6).all (fun W => !search goal fastCov 0 6 W) = true := by
  have h := ex_0_6_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_0_7_0 : ((validStarts 0 7).drop 0).all (fun W => !search goal fastCov 0 7 W) = true := by
  decide +kernel

lemma ex_0_7 : (validStarts 0 7).all (fun W => !search goal fastCov 0 7 W) = true := by
  have h := ex_0_7_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_0_8_0 : ((validStarts 0 8).drop 0).all (fun W => !search goal fastCov 0 8 W) = true := by
  decide +kernel

lemma ex_0_8 : (validStarts 0 8).all (fun W => !search goal fastCov 0 8 W) = true := by
  have h := ex_0_8_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_0_9_0 : ((validStarts 0 9).drop 0).all (fun W => !search goal fastCov 0 9 W) = true := by
  decide +kernel

lemma ex_0_9 : (validStarts 0 9).all (fun W => !search goal fastCov 0 9 W) = true := by
  have h := ex_0_9_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_1_0_0 : ((validStarts 1 0).drop 0).all (fun W => !search goal fastCov 1 0 W) = true := by
  decide +kernel

lemma ex_1_0 : (validStarts 1 0).all (fun W => !search goal fastCov 1 0 W) = true := by
  have h := ex_1_0_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_1_1_0 : ((validStarts 1 1).drop 0).all (fun W => !search goal fastCov 1 1 W) = true := by
  decide +kernel

lemma ex_1_1 : (validStarts 1 1).all (fun W => !search goal fastCov 1 1 W) = true := by
  have h := ex_1_1_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_1_2_0 : ((validStarts 1 2).drop 0).all (fun W => !search goal fastCov 1 2 W) = true := by
  decide +kernel

lemma ex_1_2 : (validStarts 1 2).all (fun W => !search goal fastCov 1 2 W) = true := by
  have h := ex_1_2_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_1_3_0 : ((validStarts 1 3).drop 0).all (fun W => !search goal fastCov 1 3 W) = true := by
  decide +kernel

lemma ex_1_3 : (validStarts 1 3).all (fun W => !search goal fastCov 1 3 W) = true := by
  have h := ex_1_3_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_1_4_0 : ((validStarts 1 4).drop 0).all (fun W => !search goal fastCov 1 4 W) = true := by
  decide +kernel

lemma ex_1_4 : (validStarts 1 4).all (fun W => !search goal fastCov 1 4 W) = true := by
  have h := ex_1_4_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_1_5_0 : ((validStarts 1 5).drop 0).all (fun W => !search goal fastCov 1 5 W) = true := by
  decide +kernel

lemma ex_1_5 : (validStarts 1 5).all (fun W => !search goal fastCov 1 5 W) = true := by
  have h := ex_1_5_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_1_6_0 : ((validStarts 1 6).drop 0).all (fun W => !search goal fastCov 1 6 W) = true := by
  decide +kernel

lemma ex_1_6 : (validStarts 1 6).all (fun W => !search goal fastCov 1 6 W) = true := by
  have h := ex_1_6_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_1_7_0 : ((validStarts 1 7).drop 0).all (fun W => !search goal fastCov 1 7 W) = true := by
  decide +kernel

lemma ex_1_7 : (validStarts 1 7).all (fun W => !search goal fastCov 1 7 W) = true := by
  have h := ex_1_7_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_1_8_0 : ((validStarts 1 8).drop 0).all (fun W => !search goal fastCov 1 8 W) = true := by
  decide +kernel

lemma ex_1_8 : (validStarts 1 8).all (fun W => !search goal fastCov 1 8 W) = true := by
  have h := ex_1_8_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_2_0_0 : ((validStarts 2 0).drop 0).all (fun W => !search goal fastCov 2 0 W) = true := by
  decide +kernel

lemma ex_2_0 : (validStarts 2 0).all (fun W => !search goal fastCov 2 0 W) = true := by
  have h := ex_2_0_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_2_1_0 : ((validStarts 2 1).drop 0).all (fun W => !search goal fastCov 2 1 W) = true := by
  decide +kernel

lemma ex_2_1 : (validStarts 2 1).all (fun W => !search goal fastCov 2 1 W) = true := by
  have h := ex_2_1_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_2_2_0 : ((validStarts 2 2).drop 0).all (fun W => !search goal fastCov 2 2 W) = true := by
  decide +kernel

lemma ex_2_2 : (validStarts 2 2).all (fun W => !search goal fastCov 2 2 W) = true := by
  have h := ex_2_2_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_2_3_0 : ((validStarts 2 3).drop 0).all (fun W => !search goal fastCov 2 3 W) = true := by
  decide +kernel

lemma ex_2_3 : (validStarts 2 3).all (fun W => !search goal fastCov 2 3 W) = true := by
  have h := ex_2_3_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_2_4_0 : ((validStarts 2 4).drop 0).all (fun W => !search goal fastCov 2 4 W) = true := by
  decide +kernel

lemma ex_2_4 : (validStarts 2 4).all (fun W => !search goal fastCov 2 4 W) = true := by
  have h := ex_2_4_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_2_5_0 : ((validStarts 2 5).drop 0).all (fun W => !search goal fastCov 2 5 W) = true := by
  decide +kernel

lemma ex_2_5 : (validStarts 2 5).all (fun W => !search goal fastCov 2 5 W) = true := by
  have h := ex_2_5_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_2_6_0 : ((validStarts 2 6).drop 0).all (fun W => !search goal fastCov 2 6 W) = true := by
  decide +kernel

lemma ex_2_6 : (validStarts 2 6).all (fun W => !search goal fastCov 2 6 W) = true := by
  have h := ex_2_6_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_2_7_0 : ((validStarts 2 7).drop 0).all (fun W => !search goal fastCov 2 7 W) = true := by
  decide +kernel

lemma ex_2_7 : (validStarts 2 7).all (fun W => !search goal fastCov 2 7 W) = true := by
  have h := ex_2_7_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_3_0_0 : ((validStarts 3 0).drop 0).all (fun W => !search goal fastCov 3 0 W) = true := by
  decide +kernel

lemma ex_3_0 : (validStarts 3 0).all (fun W => !search goal fastCov 3 0 W) = true := by
  have h := ex_3_0_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_3_1_0 : ((validStarts 3 1).drop 0).all (fun W => !search goal fastCov 3 1 W) = true := by
  decide +kernel

lemma ex_3_1 : (validStarts 3 1).all (fun W => !search goal fastCov 3 1 W) = true := by
  have h := ex_3_1_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_3_2_0 : ((validStarts 3 2).drop 0).all (fun W => !search goal fastCov 3 2 W) = true := by
  decide +kernel

lemma ex_3_2 : (validStarts 3 2).all (fun W => !search goal fastCov 3 2 W) = true := by
  have h := ex_3_2_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_3_3_0 : ((validStarts 3 3).drop 0).all (fun W => !search goal fastCov 3 3 W) = true := by
  decide +kernel

lemma ex_3_3 : (validStarts 3 3).all (fun W => !search goal fastCov 3 3 W) = true := by
  have h := ex_3_3_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_3_4_0 : ((validStarts 3 4).drop 0).all (fun W => !search goal fastCov 3 4 W) = true := by
  decide +kernel

lemma ex_3_4 : (validStarts 3 4).all (fun W => !search goal fastCov 3 4 W) = true := by
  have h := ex_3_4_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_3_5_0 : ((validStarts 3 5).drop 0).all (fun W => !search goal fastCov 3 5 W) = true := by
  decide +kernel

lemma ex_3_5 : (validStarts 3 5).all (fun W => !search goal fastCov 3 5 W) = true := by
  have h := ex_3_5_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_3_6_0 : ((validStarts 3 6).drop 0).all (fun W => !search goal fastCov 3 6 W) = true := by
  decide +kernel

lemma ex_3_6 : (validStarts 3 6).all (fun W => !search goal fastCov 3 6 W) = true := by
  have h := ex_3_6_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_4_0_0 : ((validStarts 4 0).drop 0).all (fun W => !search goal fastCov 4 0 W) = true := by
  decide +kernel

lemma ex_4_0 : (validStarts 4 0).all (fun W => !search goal fastCov 4 0 W) = true := by
  have h := ex_4_0_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_4_1_0 : ((validStarts 4 1).drop 0).all (fun W => !search goal fastCov 4 1 W) = true := by
  decide +kernel

lemma ex_4_1 : (validStarts 4 1).all (fun W => !search goal fastCov 4 1 W) = true := by
  have h := ex_4_1_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_4_2_0 : ((validStarts 4 2).drop 0).all (fun W => !search goal fastCov 4 2 W) = true := by
  decide +kernel

lemma ex_4_2 : (validStarts 4 2).all (fun W => !search goal fastCov 4 2 W) = true := by
  have h := ex_4_2_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_4_3_0 : ((validStarts 4 3).drop 0).all (fun W => !search goal fastCov 4 3 W) = true := by
  decide +kernel

lemma ex_4_3 : (validStarts 4 3).all (fun W => !search goal fastCov 4 3 W) = true := by
  have h := ex_4_3_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_4_4_0 : ((validStarts 4 4).drop 0).all (fun W => !search goal fastCov 4 4 W) = true := by
  decide +kernel

lemma ex_4_4 : (validStarts 4 4).all (fun W => !search goal fastCov 4 4 W) = true := by
  have h := ex_4_4_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_4_5_0 : ((validStarts 4 5).drop 0).all (fun W => !search goal fastCov 4 5 W) = true := by
  decide +kernel

lemma ex_4_5 : (validStarts 4 5).all (fun W => !search goal fastCov 4 5 W) = true := by
  have h := ex_4_5_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_5_0_0 : ((validStarts 5 0).drop 0).all (fun W => !search goal fastCov 5 0 W) = true := by
  decide +kernel

lemma ex_5_0 : (validStarts 5 0).all (fun W => !search goal fastCov 5 0 W) = true := by
  have h := ex_5_0_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_5_1_0 : ((validStarts 5 1).drop 0).all (fun W => !search goal fastCov 5 1 W) = true := by
  decide +kernel

lemma ex_5_1 : (validStarts 5 1).all (fun W => !search goal fastCov 5 1 W) = true := by
  have h := ex_5_1_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_5_2_0 : ((validStarts 5 2).drop 0).all (fun W => !search goal fastCov 5 2 W) = true := by
  decide +kernel

lemma ex_5_2 : (validStarts 5 2).all (fun W => !search goal fastCov 5 2 W) = true := by
  have h := ex_5_2_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_5_3_0 : ((validStarts 5 3).drop 0).all (fun W => !search goal fastCov 5 3 W) = true := by
  decide +kernel

lemma ex_5_3 : (validStarts 5 3).all (fun W => !search goal fastCov 5 3 W) = true := by
  have h := ex_5_3_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_5_4_0 : ((validStarts 5 4).drop 0).all (fun W => !search goal fastCov 5 4 W) = true := by
  decide +kernel

lemma ex_5_4 : (validStarts 5 4).all (fun W => !search goal fastCov 5 4 W) = true := by
  have h := ex_5_4_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_6_0_0 : ((validStarts 6 0).drop 0).all (fun W => !search goal fastCov 6 0 W) = true := by
  decide +kernel

lemma ex_6_0 : (validStarts 6 0).all (fun W => !search goal fastCov 6 0 W) = true := by
  have h := ex_6_0_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_6_1_0 : ((validStarts 6 1).drop 0).all (fun W => !search goal fastCov 6 1 W) = true := by
  decide +kernel

lemma ex_6_1 : (validStarts 6 1).all (fun W => !search goal fastCov 6 1 W) = true := by
  have h := ex_6_1_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_6_2_0 : ((validStarts 6 2).drop 0).all (fun W => !search goal fastCov 6 2 W) = true := by
  decide +kernel

lemma ex_6_2 : (validStarts 6 2).all (fun W => !search goal fastCov 6 2 W) = true := by
  have h := ex_6_2_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_6_3_0 : ((validStarts 6 3).drop 0).all (fun W => !search goal fastCov 6 3 W) = true := by
  decide +kernel

lemma ex_6_3 : (validStarts 6 3).all (fun W => !search goal fastCov 6 3 W) = true := by
  have h := ex_6_3_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_7_0_0 : ((validStarts 7 0).drop 0).all (fun W => !search goal fastCov 7 0 W) = true := by
  decide +kernel

lemma ex_7_0 : (validStarts 7 0).all (fun W => !search goal fastCov 7 0 W) = true := by
  have h := ex_7_0_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_7_1_0 : ((validStarts 7 1).drop 0).all (fun W => !search goal fastCov 7 1 W) = true := by
  decide +kernel

lemma ex_7_1 : (validStarts 7 1).all (fun W => !search goal fastCov 7 1 W) = true := by
  have h := ex_7_1_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_7_2_0 : ((validStarts 7 2).drop 0).all (fun W => !search goal fastCov 7 2 W) = true := by
  decide +kernel

lemma ex_7_2 : (validStarts 7 2).all (fun W => !search goal fastCov 7 2 W) = true := by
  have h := ex_7_2_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_8_0_0 : ((validStarts 8 0).drop 0).all (fun W => !search goal fastCov 8 0 W) = true := by
  decide +kernel

lemma ex_8_0 : (validStarts 8 0).all (fun W => !search goal fastCov 8 0 W) = true := by
  have h := ex_8_0_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_8_1_0 : ((validStarts 8 1).drop 0).all (fun W => !search goal fastCov 8 1 W) = true := by
  decide +kernel

lemma ex_8_1 : (validStarts 8 1).all (fun W => !search goal fastCov 8 1 W) = true := by
  have h := ex_8_1_0
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex_9_0_0 : ((validStarts 9 0).drop 0).all (fun W => !search goal fastCov 9 0 W) = true := by
  decide +kernel

lemma ex_9_0 : (validStarts 9 0).all (fun W => !search goal fastCov 9 0 W) = true := by
  have h := ex_9_0_0
  simpa using h

def exTable : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 0), (6, 1), (6, 2), (6, 3), (7, 0), (7, 1), (7, 2), (8, 0), (8, 1), (9, 0)]

lemma exTable_all : exTable.all (fun bu => (validStarts bu.1 bu.2).all
    (fun W => !search goal fastCov bu.1 bu.2 W)) = true := by
  simp only [exTable, List.all_cons, List.all_nil, Bool.and_true, ex_0_0, ex_0_1, ex_0_2, ex_0_3, ex_0_4, ex_0_5, ex_0_6, ex_0_7, ex_0_8, ex_0_9, ex_1_0, ex_1_1, ex_1_2, ex_1_3, ex_1_4, ex_1_5, ex_1_6, ex_1_7, ex_1_8, ex_2_0, ex_2_1, ex_2_2, ex_2_3, ex_2_4, ex_2_5, ex_2_6, ex_2_7, ex_3_0, ex_3_1, ex_3_2, ex_3_3, ex_3_4, ex_3_5, ex_3_6, ex_4_0, ex_4_1, ex_4_2, ex_4_3, ex_4_4, ex_4_5, ex_5_0, ex_5_1, ex_5_2, ex_5_3, ex_5_4, ex_6_0, ex_6_1, ex_6_2, ex_6_3, ex_7_0, ex_7_1, ex_7_2, ex_8_0, ex_8_1, ex_9_0]

lemma exTable_mem : ∀ b < 9 + 1, ∀ u < 9 + 1, b + u ≤ 9 → (MONO = true → u = 0) →
    exTable.contains (b, u) = true := by
  decide

lemma excl : ∀ b u, b + u ≤ 9 → (MONO = true → u = 0) →
    (validStarts b u).all (fun W => !search goal fastCov b u W) = true := by
  intro b u hbu hm
  have hmem : (b, u) ∈ exTable := List.contains_iff_mem.mp (exTable_mem b (by omega) u (by omega) hbu hm)
  exact List.all_eq_true.mp exTable_all (b, u) hmem


def RW : List ℕ := [55, 58, 147, 54, 26, 402, 268, 19, 344, 232, 154, 133, 112, 265, 28, 455, 424, 170, 186, 79, 387, 404, 68, 368, 259, 151, 364, 385, 43, 74, 83, 466, 199, 89, 23, 76, 91, 306, 69, 452, 201, 364, 135, 248, 365, 488, 46, 137, 147, 264, 436, 310, 164, 216, 168, 357, 168, 484, 15, 186, 219, 228, 420, 295, 89, 113, 150, 338, 316, 440, 63, 55, 268, 210, 451, 376, 269, 454, 278, 424, 356, 155, 201, 180, 328, 284, 284, 232, 322, 29, 278, 46, 438, 406, 209, 240, 353, 152, 228, 308, 368, 151, 294, 139, 198, 46, 211, 290, 30, 100, 408, 134, 291, 418, 101, 25, 393, 472, 259, 79, 183, 122, 179, 118, 282, 403, 270, 275, 348, 233, 410, 165, 114, 281, 92, 463, 428, 234, 250, 335, 403, 405, 84, 370, 267, 183, 380, 417, 171, 330, 115, 467, 207, 93, 87, 92, 347, 307, 85, 460, 233, 366, 167, 249, 381, 492, 302, 169, 403, 266, 500, 311, 172, 220, 172, 359, 169, 500, 271, 190, 475, 244, 428, 311, 345, 115, 158, 342, 380, 444, 191, 119, 396, 214, 483, 377, 285, 470, 286, 426, 358, 159, 205, 188, 330, 285, 286, 236, 330, 93, 279, 174, 446, 414, 241, 244, 355, 156, 229, 309, 372, 407, 358, 395, 230, 110, 467, 354, 286, 116, 409, 142, 299, 426, 229, 281, 395, 476, 275, 95]

def rowIn (idx : ℕ) : List Bool := List.ofFn fun k : Fin 9 => (RW.getD idx 0).testBit k.val

lemma rowIn_len : ∀ idx < 240, (rowIn idx).length = 9 := by
  intro idx _
  simp [rowIn]

lemma rowIn_bits : ∀ idx < 240, ∀ i < 9,
    (baseTTs.getD i zeroTT).getLsbD idx = (rowIn idx).getD i false := by
  decide +kernel

def tgt (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

lemma rowIn_tgt : ∀ idx < 240, tgt (fun k : Fin 9 => (RW.getD idx 0).testBit k.val) = goal.getLsbD idx := by
  decide +kernel

def gpre : List Gate := [⟨GateOp.not, [0]⟩, ⟨GateOp.not, [4]⟩]

lemma ins_eq : evalTT gpre baseTTs = inTTs := by
  decide +kernel

lemma main_pm (C : Circuit) (hf : FanInTwo C) (hsz : C.size ≤ 11)
    (hev : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = tgt x)
    (hpre : C.gates.take 2 = gpre) : False := by
  obtain ⟨gl, out⟩ := C
  have hsplit : gl = gpre ++ gl.drop 2 := by
    rw [← hpre]
    exact (List.take_append_drop _ _).symm
  have hev' : ∀ idx < 240, (Circuit.mk gl out).eval (rowIn idx) = goal.getLsbD idx := by
    intro idx hidx
    rw [← rowIn_tgt idx hidx]
    exact hev _
  have hm := target_mem _ hf rowIn rowIn_len rowIn_bits hev'
  have hm2 : goal ∈ evalTT (gl.drop 2) inTTs := by
    rw [← ins_eq]
    have he : evalTT gl baseTTs = evalTT (gl.drop 2) (evalTT gpre baseTTs) := by
      conv_lhs => rw [hsplit]
      simp only [evalTT, List.foldl_append]
    rw [← he]
    exact hm
  have hlen : (gl.drop 2).length ≤ 9 := by
    simp only [Circuit.size] at hsz
    simp only [List.length_drop]
    omega
  exact core_lb (gl.drop 2) 9 hlen (fun g hg => hf g (List.mem_of_mem_drop hg))
    (fun h => absurd h (by decide)) hm2 excl

end PEqualNP.Outside.L_meta_27467_aux

theorem PEqualNP.Outside.L_meta_27467 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4]⟩) := by
  rintro ⟨C, hfan, hsize, hf, -, -, -, -, h0, h1⟩
  refine PEqualNP.Outside.L_meta_27467_aux.main_pm C hfan hsize hf ?_
  obtain ⟨gl, out⟩ := C
  match gl, h0, h1 with
    | g0 :: g1 :: rest, h0, h1 =>
      have e0 : g0 = ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ := Option.some.inj h0
      have e1 : g1 = ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4]⟩ := Option.some.inj h1
      subst e0 e1
      rfl
    | [], h0, h1 => simp at h0
    | _ :: [], h0, h1 => simp at h1
