import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_51356

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

def isNotOp : GateOp → Bool
  | .not => true
  | _ => false

private lemma notCount_eq (C : Circuit) :
    notCount C = (C.gates.filter fun g => isNotOp g.op).length := by
  simp only [notCount]
  congr 1
  refine List.filter_congr (fun g _ => ?_)
  cases g.op <;> rfl

def initW : List Nat := [62, 60, 56, 48, 32, 0, 63]
def initMask : Nat := (1 <<< 62) ||| (1 <<< 60) ||| (1 <<< 56) ||| (1 <<< 48) ||| (1 <<< 32) ||| (1 <<< 0) ||| (1 <<< 63)

def evalGateW (ws : List Nat) (g : Gate) : Nat :=
  match g.op, g.inputs with
  | .and, [] => 63
  | .and, [i] => ws.getD i 0
  | .and, i :: j :: _ => ws.getD i 0 &&& ws.getD j 0
  | .or, [] => 0
  | .or, [i] => ws.getD i 0
  | .or, i :: j :: _ => ws.getD i 0 ||| ws.getD j 0
  | .not, [] => 63
  | .not, i :: _ => ws.getD i 0 ^^^ 63
  | _, _ => 0

def runW (gs : List Gate) (ws : List Nat) : List Nat :=
  gs.foldl (fun w g => w ++ [evalGateW w g]) ws

private lemma getD_map_bit (ws : List Nat) (t : Nat) (i : Nat) :
    (ws.map (fun v => v.testBit t)).getD i false = (ws.getD i 0).testBit t := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · have hi2 : ¬ i < (ws.map (fun v => v.testBit t)).length := by simpa using hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi),
      List.getElem?_eq_none (Nat.le_of_not_lt hi2)]

private lemma evalGateW_lt (ws : List Nat) (hws : ∀ v ∈ ws, v < 64) (g : Gate) :
    evalGateW ws g < 64 := by
  have hget : ∀ i, ws.getD i 0 < 64 := fun i => by
    by_cases hi : i < ws.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact hws _ (List.getElem_mem hi)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi), Option.getD_none]
      decide
  have hand : ∀ x y, x < 64 → y < 64 → x &&& y < 64 := fun _ _ hx _ => Nat.lt_of_le_of_lt Nat.and_le_left hx
  have hor : ∀ x y, x < 64 → y < 64 → x ||| y < 64 := fun _ _ hx hy => Nat.or_lt_two_pow (n := 6) hx hy
  have hxor : ∀ x, x < 64 → x ^^^ 63 < 64 := fun _ hx => Nat.xor_lt_two_pow (n := 6) hx (by decide)
  cases h : g.op <;> cases hi : g.inputs with
  | nil => simp [evalGateW, h, hi]
  | cons i r =>
    cases r with
    | nil =>
      simp only [evalGateW, h, hi]
      first | decide | exact hget i | exact hxor _ (hget i)
    | cons j r2 =>
      simp only [evalGateW, h, hi]
      first | decide | exact hand _ _ (hget i) (hget j) | exact hor _ _ (hget i) (hget j) | exact hxor _ (hget i)

private lemma evalGateW_bit (ws : List Nat) (t : Fin 6) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (evalGateW ws g).testBit t.val = g.op.eval (g.inputs.map fun i => (ws.map (fun v => v.testBit t.val)).getD i false) := by
  have ht : (63 : Nat).testBit t.val = true := by
    fin_cases t <;> decide
  rcases hg with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop | hop
  · match hi : g.inputs with
    | [] => simp only [evalGateW, hop, hi, GateOp.eval, List.map_nil, ht]; rfl
    | [i] => simp only [evalGateW, hop, hi, GateOp.eval, List.map_cons, List.map_nil, getD_map_bit, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    | [i, j] => simp only [evalGateW, hop, hi, GateOp.eval, List.map_cons, List.map_nil, getD_map_bit, Nat.testBit_and, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    | _ :: _ :: _ :: _ => simp [hi] at hlen
  · match hi : g.inputs with
    | [] => simp only [evalGateW, hop, hi, GateOp.eval, List.map_nil, Nat.zero_testBit]; rfl
    | [i] => simp only [evalGateW, hop, hi, GateOp.eval, List.map_cons, List.map_nil, getD_map_bit, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    | [i, j] => simp only [evalGateW, hop, hi, GateOp.eval, List.map_cons, List.map_nil, getD_map_bit, Nat.testBit_or, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    | _ :: _ :: _ :: _ => simp [hi] at hlen
  · match hi : g.inputs with
    | [] => simp only [evalGateW, hop, hi, GateOp.eval, List.map_nil, ht]; rfl
    | [i] => simp only [evalGateW, hop, hi, GateOp.eval, List.map_cons, List.map_nil, getD_map_bit, Nat.testBit_xor, ht, Bool.xor_true, List.headD_cons]
    | [i, j] => simp only [evalGateW, hop, hi, GateOp.eval, List.map_cons, List.map_nil, getD_map_bit, Nat.testBit_xor, ht, Bool.xor_true, List.headD_cons]
    | _ :: _ :: _ :: _ => simp [hi] at hlen

private lemma runW_bit (gs : List Gate) (ws : List Nat) (t : Fin 6)
    (hfit : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (runW gs ws).map (fun v => v.testBit t.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws.map (fun v => v.testBit t.val)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [runW, List.foldl_cons] at ih ⊢
    rw [ih (ws ++ [evalGateW ws g]) (fun g' hg' => hfit g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    rw [List.map_append, List.map_singleton, evalGateW_bit ws t g (hfit g (List.mem_cons_self ..))]

private lemma runW_lt (gs : List Gate) (ws : List Nat) (hws : ∀ v ∈ ws, v < 64) :
    ∀ v ∈ runW gs ws, v < 64 := by
  induction gs generalizing ws with
  | nil => exact hws
  | cons g gs ih =>
    simp only [runW, List.foldl_cons]
    refine ih (ws ++ [evalGateW ws g]) (fun v hv => ?_)
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hws v hv
    · exact evalGateW_lt ws hws g

private lemma runW_length (gs : List Gate) (ws : List Nat) :
    (runW gs ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp [runW]
  | cons g gs ih =>
    rw [runW, List.foldl_cons]
    change (runW gs (ws ++ [evalGateW ws g])).length = ws.length + (gs.length + 1)
    rw [ih]
    simp
    omega

private lemma eq_of_testBit6 (x y : Nat) (hx : x < 64) (hy : y < 64)
    (h : ∀ t : Fin 6, x.testBit t.val = y.testBit t.val) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 6
  · exact h ⟨k, hk⟩
  · have hpow : 64 ≤ 2 ^ k := by
      have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hx hpow),
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hy hpow)]

private lemma initW_bit : ∀ t : Fin 6,
    initW.map (fun v => v.testBit t.val) = (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true] := by
  decide

private lemma initW_lt : ∀ v ∈ initW, v < 64 := by decide

def hasBit (S v : Nat) : Bool := ((S >>> v) &&& 1) == 1

def monoPair (S : List Nat) (i : Nat) : Nat :=
  S.foldl (fun acc x => if x.testBit i then acc &&& x else acc) 63

def monoOk (tgts S : List Nat) : Bool :=
  ([0, 1, 2, 3, 4, 5] : List Nat).all (fun i =>
    let m := monoPair S i
    tgts.all (fun t => !(t.testBit i) || ((t &&& m) == m)))

def candNotMask (S : Nat) (extra : List Nat) : Nat :=
  let m1 := initW.foldl (fun acc x => let v := x ^^^ 63; if hasBit S v then acc else acc ||| (1 <<< v)) 0
  extra.foldl (fun acc x => let v := x ^^^ 63; if hasBit S v then acc else acc ||| (1 <<< v)) m1

def candBinMask (S : Nat) (extra : List Nat) : Nat :=
  let allS := initW ++ extra
  extra.foldl (fun acc e =>
    allS.foldl (fun acc2 x =>
      let v1 := e &&& x
      let acc3 := if hasBit S v1 then acc2 else acc2 ||| (1 <<< v1)
      let v2 := e ||| x
      if hasBit S v2 then acc3 else acc3 ||| (1 <<< v2)) acc) 0

def anyBitIn (mask : Nat) (f : Nat → Bool) : Bool :=
  (List.range 64).any (fun v => hasBit mask v && f v)

def countMiss (a b c S : Nat) : Nat :=
  (if hasBit S a then 0 else 1) +
  (if b == a || hasBit S b then 0 else 1) +
  (if c == a || c == b || hasBit S c then 0 else 1)

def tgtMask (a b c : Nat) : Nat := (1 <<< a) ||| (1 <<< b) ||| (1 <<< c)

def mask64 : Nat := 2 ^ 64 - 1

def canReach (a b c : Nat) : Nat → Nat → Nat → List Nat → Bool
  | 0, _, S, _ => hasBit S a && hasBit S b && hasBit S c
  | remG + 1, remN, S, extra =>
    if hasBit S a && hasBit S b && hasBit S c then true
    else
      let miss := countMiss a b c S
      if remG + 1 < miss then false
      else if remN == 0 && !monoOk [a, b, c] (initW ++ extra) then false
      else
        let cb := candBinMask S extra
        let cn := if remN == 0 then 0 else candNotMask S extra
        let tm := tgtMask a b c
        let cb' := if miss == remG + 1 then cb &&& tm else cb
        let cn' := if miss == remG + 1 then cn &&& tm else cn
        let cn'' := cn' &&& (cb' ^^^ mask64)
        if remG == 0 then
          ((cb' ||| cn'') &&& (tm &&& (S ^^^ mask64))) != 0
        else
          anyBitIn cb' (fun v => canReach a b c remG remN (S ||| (1 <<< v)) (v :: extra)) ||
          (if remN == 0 then false
           else anyBitIn cn'' (fun v => canReach a b c remG (remN - 1) (S ||| (1 <<< v)) (v :: extra)))

private lemma testBit_mask64 (v : Nat) (hv : v < 64) : mask64.testBit v = true := by
  rw [mask64, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hv

private lemma hasBit_iff (S v : Nat) : hasBit S v = true ↔ S.testBit v = true := by
  simp only [hasBit, beq_iff_eq, Nat.testBit, Nat.and_comm 1 (S >>> v), bne_iff_ne, ne_eq]
  have hlt : ((S >>> v) &&& 1) < 2 := by rw [Nat.and_one_is_mod]; exact Nat.mod_lt _ (by decide)
  omega

private lemma testBit_one_iff (k : Nat) : (1 : Nat).testBit k = true ↔ k = 0 := by
  cases k with
  | zero => simp
  | succ k =>
    have hlt : 1 < 2 ^ (k + 1) := by
      have : 2 ^ 1 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (Nat.succ_pos k)
      omega
    simp [Nat.testBit_eq_false_of_lt hlt]

private lemma hasBit_or (S v u : Nat) :
    hasBit (S ||| (1 <<< v)) u = (hasBit S u || decide (u = v)) := by
  by_cases h : u = v
  · subst h
    have h1 : (1 <<< u).testBit u = true := by simp [Nat.testBit_shiftLeft]
    have h2 : (S ||| (1 <<< u)).testBit u = true := by rw [Nat.testBit_or, h1]; simp
    have h3 : hasBit (S ||| (1 <<< u)) u = true := (hasBit_iff _ _).mpr h2
    simp [h3]
  · have h1 : (1 <<< v).testBit u = false := by
      rw [Nat.testBit_shiftLeft]
      by_cases hle : v ≤ u
      · have hne : u - v ≠ 0 := by omega
        have htb : (1 : Nat).testBit (u - v) = false := by
          cases ht : (1 : Nat).testBit (u - v) with
          | false => rfl
          | true => exact absurd ((testBit_one_iff _).mp ht) hne
        simp [hle, htb]
      · simp [hle]
    have h2 : (S ||| (1 <<< v)).testBit u = S.testBit u := by rw [Nat.testBit_or, h1]; simp
    have h3 : hasBit (S ||| (1 <<< v)) u = hasBit S u :=
      Bool.eq_iff_iff.mpr (by rw [hasBit_iff, hasBit_iff, h2])
    simp [h3, h]

private lemma initW_closed : ∀ u ∈ initW, ∀ w ∈ initW,
    hasBit initMask (u &&& w) = true ∧ hasBit initMask (u ||| w) = true := by decide

private lemma initW_in_mask : ∀ u ∈ initW, hasBit initMask u = true := by decide

private lemma monoPair_fold (L : List Nat) (acc i : Nat) (j : Fin 6) :
    (L.foldl (fun a x => if x.testBit i then a &&& x else a) acc).testBit j.val = true ↔
      acc.testBit j.val = true ∧ ∀ x ∈ L, x.testBit i = true → x.testBit j.val = true := by
  induction L generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    by_cases hx : x.testBit i = true
    · simp only [hx, ↓reduceIte, Nat.testBit_and, Bool.and_eq_true]
      constructor
      · rintro ⟨⟨ha, hxj⟩, hrest⟩
        exact ⟨ha, fun y hy hxi => hy.elim (fun e => e ▸ hxj) (fun hm => hrest y hm hxi)⟩
      · rintro ⟨ha, hall⟩
        exact ⟨⟨ha, hall x (Or.inl rfl) hx⟩, fun y hm hxi => hall y (Or.inr hm) hxi⟩
    · simp only [hx, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨ha, hrest⟩
        exact ⟨ha, fun y hy hxi => hy.elim (fun e => absurd (e ▸ hxi) hx) (fun hm => hrest y hm hxi)⟩
      · rintro ⟨ha, hall⟩
        exact ⟨ha, fun y hm hxi => hall y (Or.inr hm) hxi⟩

private lemma monoPair_bit (L : List Nat) (i : Nat) (j : Fin 6) :
    (monoPair L i).testBit j.val = true ↔ ∀ x ∈ L, x.testBit i = true → x.testBit j.val = true := by
  have h63 : (63 : Nat).testBit j.val = true := by fin_cases j <;> decide
  simp [monoPair, monoPair_fold, h63]

private lemma runW_mono_preserve (gs : List Gate) (ws : List Nat) (i : Nat) (j : Fin 6)
    (hfit : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnoNot : (gs.filter fun g => isNotOp g.op).length = 0)
    (hws : ∀ x ∈ ws, x.testBit i = true → x.testBit j.val = true) :
    ∀ x ∈ runW gs ws, x.testBit i = true → x.testBit j.val = true := by
  induction gs generalizing ws with
  | nil => exact hws
  | cons g gs ih =>
    simp only [runW, List.foldl_cons]
    have hgn : g.op ≠ GateOp.not := by
      intro heq; simp [isNotOp, heq] at hnoNot
    have hgnB : isNotOp g.op = false := by
      cases h : g.op <;> first | rfl | exact absurd h hgn
    have hnoNot' : (gs.filter fun g => isNotOp g.op).length = 0 := by
      simpa [List.filter_cons, hgnB] using hnoNot
    refine ih (ws ++ [evalGateW ws g]) (fun g' hg' => hfit g' (List.mem_cons_of_mem _ hg')) hnoNot' (fun x hx hxi => ?_)
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hws x hx hxi
    · have hget : ∀ k, (ws.getD k 0).testBit i = true → (ws.getD k 0).testBit j.val = true := fun k hk => by
        by_cases hlt : k < ws.length
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at hk ⊢
          exact hws _ (List.getElem_mem hlt) hk
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none] at hk
          simp at hk
      have h63 : (63 : Nat).testBit j.val = true := by fin_cases j <;> decide
      have hop := (hfit g (List.mem_cons_self ..)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop | hop
      · match hi : g.inputs with
        | [] => simp [evalGateW, hop, hi, h63]
        | [u] => simp [evalGateW, hop, hi] at hxi ⊢; exact hget u hxi
        | u :: v :: _ =>
          simp only [evalGateW, hop, hi, Nat.testBit_and, Bool.and_eq_true] at hxi ⊢
          exact ⟨hget u hxi.1, hget v hxi.2⟩
      · match hi : g.inputs with
        | [] => simp [evalGateW, hop, hi] at hxi
        | [u] => simp [evalGateW, hop, hi] at hxi ⊢; exact hget u hxi
        | u :: v :: _ =>
          simp only [evalGateW, hop, hi, Nat.testBit_or, Bool.or_eq_true] at hxi ⊢
          exact hxi.elim (fun h => Or.inl (hget u h)) (fun h => Or.inr (hget v h))
      · exact absurd hop hgn

private lemma monoOk_of_reach (a b c : Nat) (ha64 : a < 64) (hb64 : b < 64) (hc64 : c < 64)
    (gs : List Gate) (ws : List Nat) (extra : List Nat)
    (hfit : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnoNot : (gs.filter fun g => isNotOp g.op).length = 0)
    (hsub : ∀ x ∈ ws, x ∈ initW ++ extra)
    (ha : a ∈ runW gs ws) (hb : b ∈ runW gs ws) (hc : c ∈ runW gs ws) :
    monoOk [a, b, c] (initW ++ extra) = true := by
  simp only [monoOk, List.all_eq_true]
  intro i _
  have hpres : ∀ x ∈ runW gs ws, ∀ j : Fin 6, (monoPair (initW ++ extra) i).testBit j.val = true →
      x.testBit i = true → x.testBit j.val = true := fun x hx j hmj hxi =>
    runW_mono_preserve gs ws i j hfit hnoNot (fun w hw => (monoPair_bit (initW ++ extra) i j).mp hmj w (hsub w hw)) x hx hxi
  have h1 : ∀ t, t < 64 → t ∈ runW gs ws → ((!(t.testBit i) || ((t &&& monoPair (initW ++ extra) i) == monoPair (initW ++ extra) i)) = true) := by
    intro t ht64 htmem
    by_cases hti : t.testBit i = true
    · simp only [hti, Bool.not_true, Bool.false_or, beq_iff_eq]
      apply Nat.eq_of_testBit_eq
      intro k
      by_cases hk : k < 6
      · rw [Nat.testBit_and]
        cases hmk : (monoPair (initW ++ extra) i).testBit k with
        | false => simp
        | true => simp [hpres t htmem ⟨k, hk⟩ hmk hti]
      · have hmp_lt : monoPair (initW ++ extra) i < 64 := by
          have hfold_lt : ∀ (L : List Nat) (acc : Nat), acc < 64 →
              L.foldl (fun a x => if x.testBit i then a &&& x else a) acc < 64 := by
            intro L; induction L with
            | nil => intro acc h; exact h
            | cons x xs ih =>
              intro acc hacc
              simp only [List.foldl_cons]
              apply ih
              by_cases h : x.testBit i = true
              · simp only [h, ↓reduceIte]; exact Nat.lt_of_le_of_lt Nat.and_le_left hacc
              · simp [h, hacc]
          exact hfold_lt _ 63 (by decide)
        have hpow : 64 ≤ 2 ^ k := by
          have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
          omega
        have h1' : (monoPair (initW ++ extra) i).testBit k = false := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hmp_lt hpow)
        rw [Nat.testBit_and, h1']; simp
    · simp [hti]
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact h1 _ ha64 ha
  · exact h1 _ hb64 hb
  · exact h1 _ hc64 hc

private lemma foldl_or_bit (L : List α) (f : α → Nat) (init : Nat) (v : Nat) :
    hasBit (L.foldl (fun acc x => acc ||| f x) init) v = true ↔
      hasBit init v = true ∨ ∃ x ∈ L, hasBit (f x) v = true := by
  induction L generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    have hor : hasBit (init ||| f x) v = true ↔ hasBit init v = true ∨ hasBit (f x) v = true := by
      simp [hasBit_iff, Nat.testBit_or, Bool.or_eq_true]
    rw [hor]
    constructor
    · rintro ((h | h) | ⟨y, hy, hp⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, Or.inl rfl, h⟩
      · exact Or.inr ⟨y, Or.inr hy, hp⟩
    · rintro (h | ⟨y, rfl | hy, hp⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr hp)
      · exact Or.inr ⟨y, hy, hp⟩

private lemma candNotMask_mem (S : Nat) (extra : List Nat) (x : Nat)
    (hx : x ∈ initW ∨ x ∈ extra) (hnew : hasBit S (x ^^^ 63) = false) :
    hasBit (candNotMask S extra) (x ^^^ 63) = true := by
  have step_eq : ∀ (L : List Nat) (acc : Nat),
      L.foldl (fun a y => let v := y ^^^ 63; if hasBit S v then a else a ||| (1 <<< v)) acc =
      L.foldl (fun a y => a ||| (if hasBit S (y ^^^ 63) then 0 else 1 <<< (y ^^^ 63))) acc := by
    intro L; induction L with
    | nil => intro acc; rfl
    | cons y ys ih =>
      intro acc; simp only [List.foldl_cons]
      by_cases h : hasBit S (y ^^^ 63) = true
      · simp [h, ih]
      · simp [h, ih]
  unfold candNotMask
  rw [step_eq, step_eq, foldl_or_bit, foldl_or_bit]
  rcases hx with hx | hx
  · left; right; refine ⟨x, hx, ?_⟩
    simp only [hnew, Bool.false_eq_true, ↓reduceIte, hasBit_iff, Nat.testBit_shiftLeft]; simp
  · right; refine ⟨x, hx, ?_⟩
    simp only [hnew, Bool.false_eq_true, ↓reduceIte, hasBit_iff, Nat.testBit_shiftLeft]; simp

private lemma candBinMask_mem (S : Nat) (extra : List Nat) (e x : Nat)
    (he : e ∈ extra) (hx : x ∈ initW ++ extra) :
    (hasBit S (e &&& x) = false → hasBit (candBinMask S extra) (e &&& x) = true) ∧
    (hasBit S (e ||| x) = false → hasBit (candBinMask S extra) (e ||| x) = true) := by
  have inner_eq : ∀ (L : List Nat) (acc : Nat) (e : Nat),
      L.foldl (fun acc2 y =>
        let v1 := e &&& y
        let acc3 := if hasBit S v1 then acc2 else acc2 ||| (1 <<< v1)
        let v2 := e ||| y
        if hasBit S v2 then acc3 else acc3 ||| (1 <<< v2)) acc =
      L.foldl (fun acc2 y => acc2 ||| ((if hasBit S (e &&& y) then 0 else 1 <<< (e &&& y)) |||
        (if hasBit S (e ||| y) then 0 else 1 <<< (e ||| y)))) acc := by
    intro L; induction L with
    | nil => intro acc e; rfl
    | cons y ys ih =>
      intro acc e; simp only [List.foldl_cons]
      by_cases h1 : hasBit S (e &&& y) = true <;> by_cases h2 : hasBit S (e ||| y) = true
      · simp [h1, h2, ih]
      · simp [h1, h2, ih]
      · simp [h1, h2, ih]
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Nat.or_assoc]; exact ih _ e
  have outer_eq : ∀ (E : List Nat) (acc : Nat),
      E.foldl (fun a e' => (initW ++ extra).foldl (fun acc2 y =>
        let v1 := e' &&& y
        let acc3 := if hasBit S v1 then acc2 else acc2 ||| (1 <<< v1)
        let v2 := e' ||| y
        if hasBit S v2 then acc3 else acc3 ||| (1 <<< v2)) a) acc =
      E.foldl (fun a e' => a ||| (initW ++ extra).foldl (fun acc2 y =>
        acc2 ||| ((if hasBit S (e' &&& y) then 0 else 1 <<< (e' &&& y)) |||
          (if hasBit S (e' ||| y) then 0 else 1 <<< (e' ||| y)))) 0) acc := by
    intro E; induction E with
    | nil => intro acc; rfl
    | cons e' es ih =>
      intro acc; simp only [List.foldl_cons]
      rw [inner_eq]
      have hshift : ∀ (L : List Nat) (f : Nat → Nat) (a : Nat),
          L.foldl (fun u y => u ||| f y) a = a ||| L.foldl (fun u y => u ||| f y) 0 := by
        intro L f; induction L with
        | nil => intro a; simp
        | cons y ys ihl =>
          intro a; simp only [List.foldl_cons, Nat.zero_or]
          rw [ihl, ihl (f y), Nat.or_assoc]
      rw [hshift]
      exact ih _
  unfold candBinMask
  rw [outer_eq]
  constructor
  · intro hnew
    rw [foldl_or_bit]; right; refine ⟨e, he, ?_⟩
    rw [foldl_or_bit]; right; refine ⟨x, hx, ?_⟩
    simp only [hnew, Bool.false_eq_true, ↓reduceIte, hasBit_iff, Nat.testBit_or, Bool.or_eq_true]
    left; simp [Nat.testBit_shiftLeft]
  · intro hnew
    rw [foldl_or_bit]; right; refine ⟨e, he, ?_⟩
    rw [foldl_or_bit]; right; refine ⟨x, hx, ?_⟩
    simp only [hnew, Bool.false_eq_true, ↓reduceIte, hasBit_iff, Nat.testBit_or, Bool.or_eq_true]
    right; simp [Nat.testBit_shiftLeft]

private lemma countMiss_le_len (a b c S : Nat) (gs : List Gate) (ws : List Nat)
    (hws : ∀ x ∈ ws, hasBit S x = true)
    (ha : a ∈ runW gs ws) (hb : b ∈ runW gs ws) (hc : c ∈ runW gs ws) :
    countMiss a b c S ≤ gs.length := by
  have hmem : ∀ x ∈ runW gs ws, hasBit S x = true ∨ x ∈ (runW gs ws).drop ws.length := by
    intro x hx
    have hsplit : runW gs ws = ws ++ (runW gs ws).drop ws.length := by
      have hpre : ∀ gs' ws', ∃ tail, runW gs' ws' = ws' ++ tail := by
        intro gs'; induction gs' with
        | nil => intro ws'; exact ⟨[], by simp [runW]⟩
        | cons g gs' ih =>
          intro ws'
          rw [runW, List.foldl_cons]
          change ∃ tail, runW gs' (ws' ++ [evalGateW ws' g]) = ws' ++ tail
          obtain ⟨t, ht⟩ := ih (ws' ++ [evalGateW ws' g])
          exact ⟨evalGateW ws' g :: t, by rw [ht, List.append_assoc]; rfl⟩
      obtain ⟨tail, htail⟩ := hpre gs ws
      rw [htail, List.drop_left]
    rw [hsplit, List.mem_append] at hx
    exact hx.elim (fun h => Or.inl (hws x h)) Or.inr
  have hdrop_len : ((runW gs ws).drop ws.length).length = gs.length := by
    rw [List.length_drop, runW_length]; omega
  set T := (runW gs ws).drop ws.length
  have ha' := hmem a ha; have hb' := hmem b hb; have hc' := hmem c hc
  unfold countMiss
  by_cases hSa : hasBit S a = true <;> by_cases hSb : (b == a || hasBit S b) = true <;> by_cases hSc : (c == a || c == b || hasBit S c) = true
  · simp [hSa, hSb, hSc]
  · simp only [hSa, hSb, hSc, ↓reduceIte, Bool.false_eq_true, Nat.zero_add]
    have hcT : c ∈ T := hc'.resolve_left (by simp only [Bool.or_eq_true] at hSc; intro h; exact hSc (Or.inr h))
    have : 0 < T.length := List.length_pos_of_mem hcT
    omega
  · simp only [hSa, hSb, hSc, ↓reduceIte, Bool.false_eq_true, Nat.add_zero, Nat.zero_add]
    have hbT : b ∈ T := hb'.resolve_left (by simp only [Bool.or_eq_true] at hSb; intro h; exact hSb (Or.inr h))
    have : 0 < T.length := List.length_pos_of_mem hbT
    omega
  · simp only [hSa, hSb, hSc, ↓reduceIte, Bool.false_eq_true, Nat.zero_add]
    have hbT : b ∈ T := hb'.resolve_left (by simp only [Bool.or_eq_true] at hSb; intro h; exact hSb (Or.inr h))
    have hcT : c ∈ T := hc'.resolve_left (by simp only [Bool.or_eq_true] at hSc; intro h; exact hSc (Or.inr h))
    have hbc : c ≠ b := by intro h; apply hSc; simp [h]
    have h2 : 2 ≤ T.length := by
      have : ({b, c} : Finset Nat) ⊆ T.toFinset := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
      have hc2 : ({b, c} : Finset Nat).card = 2 := Finset.card_pair (Ne.symm hbc)
      have := Finset.card_le_card this
      have := List.toFinset_card_le T
      omega
    omega
  · simp only [hSa, hSb, hSc, ↓reduceIte, Bool.false_eq_true, Nat.add_zero]
    have haT : a ∈ T := ha'.resolve_left hSa
    have : 0 < T.length := List.length_pos_of_mem haT
    omega
  · simp only [hSa, hSb, hSc, ↓reduceIte, Bool.false_eq_true, Nat.add_zero]
    have haT : a ∈ T := ha'.resolve_left hSa
    have hcT : c ∈ T := hc'.resolve_left (by simp only [Bool.or_eq_true] at hSc; intro h; exact hSc (Or.inr h))
    have hca : c ≠ a := by intro h; apply hSc; simp [h]
    have h2 : 2 ≤ T.length := by
      have : ({a, c} : Finset Nat) ⊆ T.toFinset := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
      have hc2 : ({a, c} : Finset Nat).card = 2 := Finset.card_pair (Ne.symm hca)
      have := Finset.card_le_card this
      have := List.toFinset_card_le T
      omega
    omega
  · simp only [hSa, hSb, hSc, ↓reduceIte, Bool.false_eq_true, Nat.add_zero]
    have haT : a ∈ T := ha'.resolve_left hSa
    have hbT : b ∈ T := hb'.resolve_left (by simp only [Bool.or_eq_true] at hSb; intro h; exact hSb (Or.inr h))
    have hba : b ≠ a := by intro h; apply hSb; simp [h]
    have h2 : 2 ≤ T.length := by
      have : ({a, b} : Finset Nat) ⊆ T.toFinset := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
      have hc2 : ({a, b} : Finset Nat).card = 2 := Finset.card_pair (Ne.symm hba)
      have := Finset.card_le_card this
      have := List.toFinset_card_le T
      omega
    omega
  · simp only [hSa, hSb, hSc, ↓reduceIte, Bool.false_eq_true]
    have haT : a ∈ T := ha'.resolve_left hSa
    have hbT : b ∈ T := hb'.resolve_left (by simp only [Bool.or_eq_true] at hSb; intro h; exact hSb (Or.inr h))
    have hcT : c ∈ T := hc'.resolve_left (by simp only [Bool.or_eq_true] at hSc; intro h; exact hSc (Or.inr h))
    have hba : b ≠ a := by intro h; apply hSb; simp [h]
    have hca : c ≠ a := by intro h; apply hSc; simp [h]
    have hcb : c ≠ b := by intro h; apply hSc; simp [h]
    have h3 : 3 ≤ T.length := by
      have : ({a, b, c} : Finset Nat) ⊆ T.toFinset := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
      have hc3 : ({a, b, c} : Finset Nat).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hcb)]
        simp [Ne.symm hba, Ne.symm hca]
      have := Finset.card_le_card this
      have := List.toFinset_card_le T
      omega
    omega

private lemma countMiss_pos (a b c S : Nat) (h : ¬ (hasBit S a && hasBit S b && hasBit S c) = true) :
    0 < countMiss a b c S := by
  unfold countMiss
  by_cases ha : hasBit S a = true
  · by_cases hb : hasBit S b = true
    · by_cases hc : hasBit S c = true
      · simp [ha, hb, hc] at h
      · have hca : (c == a) = false := by cases h1 : (c == a) with | false => rfl | true => rw [beq_iff_eq] at h1; subst h1; exact absurd ha hc
        have hcb : (c == b) = false := by cases h1 : (c == b) with | false => rfl | true => rw [beq_iff_eq] at h1; subst h1; exact absurd hb hc
        simp [ha, hb, hc, hca, hcb]
    · have hba : (b == a) = false := by cases h1 : (b == a) with | false => rfl | true => rw [beq_iff_eq] at h1; subst h1; exact absurd ha hb
      simp [ha, hb, hba]
  · simp [ha]

private lemma countMiss_add_one (a b c S v : Nat) :
    countMiss a b c S ≤ countMiss a b c (S ||| (1 <<< v)) + (if hasBit (tgtMask a b c) v then 1 else 0) := by
  have htm : hasBit (tgtMask a b c) v = true ↔ v = a ∨ v = b ∨ v = c := by
    have hb1 : ∀ u, (1 <<< u).testBit v = true ↔ v = u := fun u => by
      rw [Nat.testBit_shiftLeft]
      by_cases h : u ≤ v
      · simp [h, testBit_one_iff]; omega
      · simp [h]; omega
    simp only [tgtMask, hasBit_iff, Nat.testBit_or, Bool.or_eq_true, hb1, or_assoc]
  have h01 : ∀ p q : Bool, (if p = true then (0 : Nat) else 1) ≤ (if q = true then 0 else 1) + 1 := by decide
  by_cases hva : v = a
  · subst v
    have ht : hasBit (tgtMask a b c) a = true := htm.mpr (Or.inl rfl)
    have h2 : (b == a || hasBit (S ||| (1 <<< a)) b) = (b == a || hasBit S b) := by
      rw [hasBit_or]; by_cases h : b = a <;> simp [h]
    have h3 : (c == a || c == b || hasBit (S ||| (1 <<< a)) c) = (c == a || c == b || hasBit S c) := by
      rw [hasBit_or]; by_cases h : c = a <;> simp [h]
    simp only [ht, ↓reduceIte, countMiss, h2, h3]
    have := h01 (hasBit S a) (hasBit (S ||| (1 <<< a)) a)
    omega
  · by_cases hvb : v = b
    · subst v
      have ht : hasBit (tgtMask a b c) b = true := htm.mpr (Or.inr (Or.inl rfl))
      have h1 : hasBit (S ||| (1 <<< b)) a = hasBit S a := by rw [hasBit_or]; simp [Ne.symm hva]
      have h3 : (c == a || c == b || hasBit (S ||| (1 <<< b)) c) = (c == a || c == b || hasBit S c) := by
        rw [hasBit_or]; by_cases h : c = b <;> simp [h]
      simp only [ht, ↓reduceIte, countMiss, h1, h3]
      have := h01 (b == a || hasBit S b) (b == a || hasBit (S ||| (1 <<< b)) b)
      omega
    · by_cases hvc : v = c
      · subst v
        have ht : hasBit (tgtMask a b c) c = true := htm.mpr (Or.inr (Or.inr rfl))
        have h1 : hasBit (S ||| (1 <<< c)) a = hasBit S a := by rw [hasBit_or]; simp [Ne.symm hva]
        have h2 : hasBit (S ||| (1 <<< c)) b = hasBit S b := by rw [hasBit_or]; simp [Ne.symm hvb]
        simp only [ht, ↓reduceIte, countMiss, h1, h2]
        have := h01 (c == a || c == b || hasBit S c) (c == a || c == b || hasBit (S ||| (1 <<< c)) c)
        omega
      · have ht : hasBit (tgtMask a b c) v = false := by
          cases h : hasBit (tgtMask a b c) v with
          | false => rfl
          | true => rcases htm.mp h with rfl | rfl | rfl <;> contradiction
        have h1 : hasBit (S ||| (1 <<< v)) a = hasBit S a := by rw [hasBit_or]; simp [Ne.symm hva]
        have h2 : hasBit (S ||| (1 <<< v)) b = hasBit S b := by rw [hasBit_or]; simp [Ne.symm hvb]
        have h3 : hasBit (S ||| (1 <<< v)) c = hasBit S c := by rw [hasBit_or]; simp [Ne.symm hvc]
        simp [ht, countMiss, h1, h2, h3]

private lemma anyBitIn_of_mem (mask : Nat) (f : Nat → Bool) (v : Nat) (hv64 : v < 64)
    (hm : hasBit mask v = true) (hf : f v = true) : anyBitIn mask f = true := by
  simp only [anyBitIn, List.any_eq_true, List.mem_range, Bool.and_eq_true]
  exact ⟨v, hv64, hm, hf⟩

private lemma getD_in_ws (ws extra : List Nat) (h0 : 0 ∈ initW) (hsub : ∀ x ∈ ws, x ∈ initW ++ extra) (i : Nat) :
    ws.getD i 0 ∈ initW ++ extra := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hsub _ (List.getElem_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi), Option.getD_none]
    exact List.mem_append_left _ h0

private lemma canReach_complete (a b c : Nat) (ha64 : a < 64) (hb64 : b < 64) (hc64 : c < 64)
    (gs : List Gate) (ws : List Nat) (S : Nat) (extra : List Nat) (remG remN : Nat)
    (hinit : ∀ u ∈ initW, hasBit S u = true)
    (hSE : ∀ x, hasBit S x = true → x ∈ initW ++ extra)
    (hwsS : ∀ x ∈ ws, hasBit S x = true)
    (hws64 : ∀ x ∈ ws, x < 64)
    (hfit : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hlen : gs.length ≤ remG)
    (hnot : (gs.filter fun g => isNotOp g.op).length ≤ remN)
    (ha : a ∈ runW gs ws) (hb : b ∈ runW gs ws) (hc : c ∈ runW gs ws) :
    canReach a b c remG remN S extra = true := by
  induction gs generalizing ws S extra remG remN with
  | nil =>
    simp only [runW, List.foldl_nil] at ha hb hc
    have hdone : (hasBit S a && hasBit S b && hasBit S c) = true := by
      simp [hwsS a ha, hwsS b hb, hwsS c hc]
    cases remG with
    | zero => exact hdone
    | succ r => simp [canReach, hdone]
  | cons g gs ih =>
    have hrem_pos : 1 ≤ remG := by simp at hlen; omega
    obtain ⟨rG, rfl⟩ := Nat.exists_eq_add_of_le' hrem_pos
    have hwsL : ∀ x ∈ ws, x ∈ initW ++ extra := fun x hx => hSE x (hwsS x hx)
    by_cases hdone : (hasBit S a && hasBit S b && hasBit S c) = true
    · simp [canReach, hdone]
    · set v := evalGateW ws g
      have hv64 : v < 64 := evalGateW_lt ws hws64 g
      by_cases hSv : hasBit S v = true
      · have hgn : (gs.filter fun g => isNotOp g.op).length ≤ remN := by
          have : (gs.filter fun g => isNotOp g.op).length ≤ ((g :: gs).filter fun g => isNotOp g.op).length := by
            simp only [List.filter_cons]; split <;> simp
          omega
        have hgs_len : gs.length ≤ rG + 1 := by simp at hlen; omega
        have hwsS' : ∀ x ∈ ws ++ [v], hasBit S x = true := fun x hx => by
          simp only [List.mem_append, List.mem_singleton] at hx
          exact hx.elim (hwsS x) (fun e => e ▸ hSv)
        have hws64' : ∀ x ∈ ws ++ [v], x < 64 := fun x hx => by
          simp only [List.mem_append, List.mem_singleton] at hx
          exact hx.elim (hws64 x) (fun e => e ▸ hv64)
        exact ih (ws ++ [v]) S extra (rG + 1) remN hinit hSE hwsS' hws64'
          (fun g' hg' => hfit g' (List.mem_cons_of_mem _ hg')) hgs_len hgn ha hb hc
      · have hSv_f : hasBit S v = false := Bool.eq_false_iff.mpr hSv
        have hmiss_le : countMiss a b c S ≤ rG + 1 :=
          Nat.le_trans (countMiss_le_len a b c S (g :: gs) ws hwsS ha hb hc) hlen
        have hnot_lt : ¬ (rG + 1 < countMiss a b c S) := by omega
        have hmono_not_false : ¬ (remN == 0 && !monoOk [a, b, c] (initW ++ extra)) = true := by
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
          rintro ⟨rfl, hm⟩
          have h0 : ((g :: gs).filter fun g => isNotOp g.op).length = 0 := by omega
          have hok := monoOk_of_reach a b c ha64 hb64 hc64 (g :: gs) ws extra hfit h0 hwsL ha hb hc
          rw [hok] at hm; exact Bool.noConfusion hm
        have h0in : (0 : Nat) ∈ initW := by decide
        have h63in : (63 : Nat) ∈ initW := by decide
        have hv_cls : hasBit (candBinMask S extra) v = true ∨
            (remN ≠ 0 ∧ hasBit (candNotMask S extra) v = true ∧
              (gs.filter fun g => isNotOp g.op).length ≤ remN - 1) := by
          have hop := (hfit g (List.mem_cons_self ..)).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with hop | hop | hop
          · match hi : g.inputs with
            | [] =>
              have : v = 63 := by simp [v, evalGateW, hop, hi]
              exact absurd (this ▸ hinit 63 h63in) hSv
            | [i] =>
              have : v = ws.getD i 0 := by simp [v, evalGateW, hop, hi]
              by_cases hlt : i < ws.length
              · have h1 : ws.getD i 0 ∈ ws := by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
                  exact List.getElem_mem hlt
                exact absurd (this ▸ hwsS _ h1) hSv
              · have h1 : ws.getD i 0 = 0 := by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none]
                have hv0 : v = 0 := this.trans h1
                exact absurd (hv0 ▸ hinit 0 h0in) hSv
            | i :: j :: _ =>
              have hv_eq : v = ws.getD i 0 &&& ws.getD j 0 := by simp [v, evalGateW, hop, hi]
              have hiM := getD_in_ws ws extra h0in hwsL i
              have hjM := getD_in_ws ws extra h0in hwsL j
              rcases List.mem_append.mp hiM with hiI | hiE
              · rcases List.mem_append.mp hjM with hjI | hjE
                · have hc := (initW_closed _ hiI _ hjI).1
                  have hsub : ∀ u, hasBit initMask u = true → hasBit S u = true := fun u hu => by
                    have huI : u ∈ initW := by
                      have : ∀ w < 64, hasBit initMask w = true → w ∈ initW := by decide
                      by_cases hw : u < 64
                      · exact this u hw hu
                      · exfalso
                        have hlt : initMask < 2 ^ u := by
                          have h1 : initMask < 2 ^ 64 := by decide
                          have h2 : 2 ^ 64 ≤ 2 ^ u := Nat.pow_le_pow_right (by decide) (by omega)
                          omega
                        have hbf : initMask.testBit u = false := Nat.testBit_eq_false_of_lt hlt
                        rw [hasBit_iff] at hu; rw [hbf] at hu; exact Bool.noConfusion hu
                    exact hinit u huI
                  exact absurd (hv_eq ▸ hsub _ hc) hSv
                · left
                  have hcomm : ws.getD i 0 &&& ws.getD j 0 = ws.getD j 0 &&& ws.getD i 0 := Nat.and_comm _ _
                  rw [hv_eq, hcomm]
                  exact (candBinMask_mem S extra _ _ hjE hiM).1 (by rwa [← hcomm, ← hv_eq])
              · left; rw [hv_eq]; exact (candBinMask_mem S extra _ _ hiE hjM).1 (by rwa [← hv_eq])
          · match hi : g.inputs with
            | [] =>
              have : v = 0 := by simp [v, evalGateW, hop, hi]
              exact absurd (this ▸ hinit 0 h0in) hSv
            | [i] =>
              have : v = ws.getD i 0 := by simp [v, evalGateW, hop, hi]
              by_cases hlt : i < ws.length
              · have h1 : ws.getD i 0 ∈ ws := by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
                  exact List.getElem_mem hlt
                exact absurd (this ▸ hwsS _ h1) hSv
              · have h1 : ws.getD i 0 = 0 := by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none]
                have hv0 : v = 0 := this.trans h1
                exact absurd (hv0 ▸ hinit 0 h0in) hSv
            | i :: j :: _ =>
              have hv_eq : v = ws.getD i 0 ||| ws.getD j 0 := by simp [v, evalGateW, hop, hi]
              have hiM := getD_in_ws ws extra h0in hwsL i
              have hjM := getD_in_ws ws extra h0in hwsL j
              rcases List.mem_append.mp hiM with hiI | hiE
              · rcases List.mem_append.mp hjM with hjI | hjE
                · have hc := (initW_closed _ hiI _ hjI).2
                  have hsub : ∀ u, hasBit initMask u = true → hasBit S u = true := fun u hu => by
                    have huI : u ∈ initW := by
                      have : ∀ w < 64, hasBit initMask w = true → w ∈ initW := by decide
                      by_cases hw : u < 64
                      · exact this u hw hu
                      · exfalso
                        have hlt : initMask < 2 ^ u := by
                          have h1 : initMask < 2 ^ 64 := by decide
                          have h2 : 2 ^ 64 ≤ 2 ^ u := Nat.pow_le_pow_right (by decide) (by omega)
                          omega
                        have hbf : initMask.testBit u = false := Nat.testBit_eq_false_of_lt hlt
                        rw [hasBit_iff] at hu; rw [hbf] at hu; exact Bool.noConfusion hu
                    exact hinit u huI
                  exact absurd (hv_eq ▸ hsub _ hc) hSv
                · left
                  have hcomm : ws.getD i 0 ||| ws.getD j 0 = ws.getD j 0 ||| ws.getD i 0 := Nat.or_comm _ _
                  rw [hv_eq, hcomm]
                  exact (candBinMask_mem S extra _ _ hjE hiM).2 (by rwa [← hcomm, ← hv_eq])
              · left; rw [hv_eq]; exact (candBinMask_mem S extra _ _ hiE hjM).2 (by rwa [← hv_eq])
          · right
            have hnot1 : (gs.filter fun g => isNotOp g.op).length + 1 ≤ remN := by
              simpa [List.filter_cons, isNotOp, hop] using hnot
            match hi : g.inputs with
            | [] =>
              have : v = 63 := by simp [v, evalGateW, hop, hi]
              exact absurd (this ▸ hinit 63 h63in) hSv
            | i :: _ =>
              have hv_eq : v = ws.getD i 0 ^^^ 63 := by simp [v, evalGateW, hop, hi]
              have hiM := List.mem_append.mp (getD_in_ws ws extra h0in hwsL i)
              refine ⟨by omega, ?_, by omega⟩
              rw [hv_eq]
              exact candNotMask_mem S extra _ hiM (by rwa [← hv_eq])
        set S' := S ||| (1 <<< v)
        have hinit' : ∀ u ∈ initW, hasBit S' u = true := fun u hu => by
          simp [S', hasBit_or, hinit u hu]
        have hSE' : ∀ x, hasBit S' x = true → x ∈ initW ++ (v :: extra) := fun x hx => by
          simp only [S', hasBit_or, Bool.or_eq_true, decide_eq_true_eq] at hx
          rcases hx with hx | rfl
          · rcases List.mem_append.mp (hSE x hx) with h1 | h2
            · exact List.mem_append_left _ h1
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
          · exact List.mem_append_right _ (List.mem_cons_self ..)
        have hwsS' : ∀ x ∈ ws ++ [v], hasBit S' x = true := fun x hx => by
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · simp [S', hasBit_or, hwsS x hx]
          · simp [S', hasBit_or]
        have hws64' : ∀ x ∈ ws ++ [v], x < 64 := fun x hx => by
          simp only [List.mem_append, List.mem_singleton] at hx
          exact hx.elim (hws64 x) (fun e => e ▸ hv64)
        have hgs_len : gs.length ≤ rG := by simp at hlen; omega
        have hgs_not_le : (gs.filter fun g => isNotOp g.op).length ≤ remN := by
          have : (gs.filter fun g => isNotOp g.op).length ≤ ((g :: gs).filter fun g => isNotOp g.op).length := by
            simp only [List.filter_cons]; split <;> simp
          omega
        have hv_tm : countMiss a b c S = rG + 1 → hasBit (tgtMask a b c) v = true := by
          intro heq
          have h1 := countMiss_add_one a b c S v
          have h2 : countMiss a b c (S ||| (1 <<< v)) ≤ gs.length := countMiss_le_len a b c S' gs (ws ++ [v]) hwsS' ha hb hc
          cases ht : hasBit (tgtMask a b c) v with
          | true => rfl
          | false => simp [ht] at h1; omega
        simp only [canReach, hdone, Bool.false_eq_true, ↓reduceIte, hnot_lt, hmono_not_false]
        set cb := candBinMask S extra
        set cn := if remN == 0 then 0 else candNotMask S extra
        set tm := tgtMask a b c
        set cb' := if countMiss a b c S == rG + 1 then cb &&& tm else cb
        set cn' := if countMiss a b c S == rG + 1 then cn &&& tm else cn
        set cn'' := cn' &&& (cb' ^^^ mask64)
        have hv_cb_or_cn : hasBit cb' v = true ∨ (remN ≠ 0 ∧ hasBit cn'' v = true ∧
            (gs.filter fun g => isNotOp g.op).length ≤ remN - 1) := by
          have hcb_keep : hasBit cb v = true → hasBit cb' v = true := fun h => by
            by_cases hm : countMiss a b c S = rG + 1
            · simp only [cb', hm, beq_self_eq_true, ↓reduceIte, hasBit_iff, Nat.testBit_and, Bool.and_eq_true]
              exact ⟨(hasBit_iff _ _).mp h, (hasBit_iff _ _).mp (hv_tm hm)⟩
            · simp [cb', hm, h]
          rcases hv_cls with hcb | ⟨hne, hcn, hnot'⟩
          · exact Or.inl (hcb_keep hcb)
          · by_cases hcb' : hasBit cb' v = true
            · exact Or.inl hcb'
            · right
              have hcn_nz : hasBit cn v = true := by simp [cn, hne, hcn]
              have hcn'_t : hasBit cn' v = true := by
                by_cases hm : countMiss a b c S = rG + 1
                · simp only [cn', hm, beq_self_eq_true, ↓reduceIte, hasBit_iff, Nat.testBit_and, Bool.and_eq_true]
                  exact ⟨(hasBit_iff _ _).mp hcn_nz, (hasBit_iff _ _).mp (hv_tm hm)⟩
                · simp [cn', hm, hcn_nz]
              have hmask64 : mask64.testBit v = true := testBit_mask64 v hv64
              have hcb'_f : cb'.testBit v = false := by
                rw [← Bool.not_eq_true]; intro h; exact hcb' ((hasBit_iff _ _).mpr h)
              have hcn''_t : hasBit cn'' v = true := by
                simp only [cn'', hasBit_iff, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true]
                exact ⟨(hasBit_iff _ _).mp hcn'_t, by rw [hcb'_f, hmask64]; rfl⟩
              exact ⟨hne, hcn''_t, hnot'⟩
        cases hr : rG with
        | zero =>
          simp only [beq_self_eq_true, ↓reduceIte, bne_iff_ne, ne_eq]
          intro hzero
          have hbit_zero := congrArg (fun x => x.testBit v) hzero
          simp only [Nat.zero_testBit, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at hbit_zero
          have hmask64 : mask64.testBit v = true := testBit_mask64 v hv64
          have hSv0 : S.testBit v = false := by
            rw [← Bool.not_eq_true]; intro h; exact hSv ((hasBit_iff _ _).mpr h)
          have htm_v : tm.testBit v = true := by
            have hgt0 : 0 < countMiss a b c S := countMiss_pos a b c S hdone
            exact (hasBit_iff _ _).mp (hv_tm (by omega))
          have hcb_or_cn_bit : (cb'.testBit v || cn''.testBit v) = true := by
            rcases hv_cb_or_cn with h | ⟨_, h, _⟩
            · simp [(hasBit_iff _ _).mp h]
            · simp [(hasBit_iff _ _).mp h]
          rw [hcb_or_cn_bit, htm_v, hSv0, hmask64] at hbit_zero
          exact Bool.noConfusion hbit_zero
        | succ rG' =>
          simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte, Bool.or_eq_true]
          rcases hv_cb_or_cn with hcb' | ⟨hne, hcn'', hnot'⟩
          · left
            refine anyBitIn_of_mem cb' _ v hv64 hcb' ?_
            exact ih (ws ++ [v]) S' (v :: extra) (rG' + 1) remN hinit' hSE' hwsS' hws64'
              (fun g' hg' => hfit g' (List.mem_cons_of_mem _ hg')) (by omega) hgs_not_le ha hb hc
          · right
            simp only [hne, ↓reduceIte]
            refine anyBitIn_of_mem cn'' _ v hv64 hcn'' ?_
            exact ih (ws ++ [v]) S' (v :: extra) (rG' + 1) (remN - 1) hinit' hSE' hwsS' hws64'
              (fun g' hg' => hfit g' (List.mem_cons_of_mem _ hg')) (by omega) hnot' ha hb hc

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem check_unsat : canReach 40 42 50 6 2 initMask [] = false := by
  decide +kernel

theorem final :
    ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (40 : Nat).testBit t.val ∧
    w.getD q.val false = (42 : Nat).testBit t.val ∧
    w.getD r.val false = (50 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hfit, _hrb, hnc, hsz, hev⟩
  have hlen : (runW D.gates initW).length = 7 + D.size := by
    simpa [Circuit.size, initW] using runW_length D.gates initW
  have hmem_of : ∀ (idx : Fin (7 + D.size)) (tgt : Nat), tgt < 64 →
      (∀ t : Fin 6, (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD idx.val false = tgt.testBit t.val) →
      tgt ∈ runW D.gates initW := by
    intro idx tgt htgt hbit
    have hlt : idx.val < (runW D.gates initW).length := by omega
    have hv_lt : (runW D.gates initW).getD idx.val 0 < 64 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      exact runW_lt D.gates initW initW_lt _ (List.getElem_mem hlt)
    have heq : (runW D.gates initW).getD idx.val 0 = tgt := by
      apply eq_of_testBit6 _ _ hv_lt htgt
      intro t
      have h1 := hbit t
      rw [Circuit.wires, ← initW_bit t, ← runW_bit D.gates initW t hfit, getD_map_bit] at h1
      exact h1
    rw [← heq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_mem hlt
  have ha : 40 ∈ runW D.gates initW := hmem_of p 40 (by decide) (fun t => (hev t).1)
  have hb : 42 ∈ runW D.gates initW := hmem_of q 42 (by decide) (fun t => (hev t).2.1)
  have hc : 50 ∈ runW D.gates initW := hmem_of r 50 (by decide) (fun t => (hev t).2.2)
  have hSE0 : ∀ x, hasBit initMask x = true → x ∈ initW ++ [] := by
    intro x hx
    by_cases h64 : x < 64
    · have : ∀ w < 64, hasBit initMask w = true → w ∈ initW := by decide
      simpa using this x h64 hx
    · exfalso
      have hlt : initMask < 2 ^ x := by
        have h1 : initMask < 2 ^ 64 := by decide
        have h2 : 2 ^ 64 ≤ 2 ^ x := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      rw [hasBit_iff, Nat.testBit_eq_false_of_lt hlt] at hx
      exact Bool.noConfusion hx
  have hnc' : (D.gates.filter fun g => isNotOp g.op).length ≤ 2 := by
    rwa [← notCount_eq D]
  have hreach := canReach_complete 40 42 50 (by decide) (by decide) (by decide)
    D.gates initW initMask [] 6 2
    initW_in_mask hSE0 initW_in_mask initW_lt hfit hsz hnc' ha hb hc
  rw [check_unsat] at hreach
  exact Bool.noConfusion hreach

end PEqualNP.Outside.L_meta_51356

theorem PEqualNP.Outside.L_meta_51356 :
    ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (40 : Nat).testBit t.val ∧
    w.getD q.val false = (42 : Nat).testBit t.val ∧
    w.getD r.val false = (50 : Nat).testBit t.val) :=
  PEqualNP.Outside.L_meta_51356.final
