import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52854
namespace Wide
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 256
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
lemma testBit_bin (d a b r : Nat) :
    (bin d a b).testBit r =
      match d with
      | 0 => a.testBit r && b.testBit r
      | 1 => a.testBit r || b.testBit r
      | 2 => a.testBit r && !b.testBit r
      | _ => !a.testBit r && b.testBit r := by
  rcases d with _ | _ | _ | d <;>
    simp [bin, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit r <;> cases b.testBit r <;> rfl
lemma bin_lt (d a b : Nat) (ha : a < 2^256) (hb : b < 2^256) : bin d a b < 2^256 := by
  have h1 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x &&& y) < 2^256 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ||| y) < 2^256 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ^^^ y) < 2^256 := fun x y hx hy =>
    Nat.xor_lt_two_pow hx hy
  rcases d with _ | _ | _ | d
  · exact h1 a b ha hb
  · exact h2 a b ha hb
  · exact h3 a (a &&& b) ha (h1 a b ha hb)
  · exact h3 b (a &&& b) hb (h1 a b ha hb)
lemma bin_bit0 (d a b : Nat) (ha : a.testBit 0 = false) (hb : b.testBit 0 = false) :
    (bin d a b).testBit 0 = false := by
  rw [testBit_bin]
  rcases d with _ | _ | _ | d <;> simp [ha, hb]
def Live (T : Nat) : Nat → Finset Nat → Prop
  | 0, S => S = {T} ∧ T ≠ 0
  | k + 1, S => ∃ (U : Finset Nat) (a b d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k (insert (bin d a b) U)
lemma live_nonzero {T k S} (h : Live T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hT⟩ := h; simpa using hT
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma live_sep {T k S} (h : Live T k S) {r s : Nat} (hd : T.testBit r ≠ T.testBit s) :
    ∃ a ∈ S, a.testBit r ≠ a.testBit s := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; exact ⟨T, by simp, hd⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, _, tail⟩ := h
    obtain ⟨v, hv, hvd⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : a.testBit r = a.testBit s
      · refine ⟨b, by simp, fun hb => hvd ?_⟩
        rw [testBit_bin, testBit_bin, ha, hb]
      · exact ⟨a, by simp, ha⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv), hvd⟩
abbrev SWire := Bool × Nat
def swZero : SWire := (false, 0)
def swFlip (a : SWire) : SWire := (!a.1, a.2)
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def swMeet (a b : SWire) : SWire := (a.1 && b.1, bin (opIdx a.1 b.1) a.2 b.2)
def swJoin (a b : SWire) : SWire := swFlip (swMeet (swFlip a) (swFlip b))
def swRead (j : Nat) (a : SWire) : Bool := a.1 != a.2.testBit j
lemma swRead_zero (j : Nat) : swRead j swZero = false := by simp [swRead, swZero]
lemma swRead_flip (j : Nat) (a : SWire) : swRead j (swFlip a) = !(swRead j a) := by
  cases a with | mk s v => cases s <;> cases h : v.testBit j <;> simp [swRead, swFlip, h]
lemma swRead_meet (j : Nat) (a b : SWire) : swRead j (swMeet a b) = (swRead j a && swRead j b) := by
  obtain ⟨s, u⟩ := a; obtain ⟨t, v⟩ := b
  cases s <;> cases t <;> cases hu : u.testBit j <;> cases hv : v.testBit j <;>
    simp [swRead, swMeet, opIdx, testBit_bin, hu, hv]
lemma swRead_join (j : Nat) (a b : SWire) : swRead j (swJoin a b) = (swRead j a || swRead j b) := by
  simp only [swJoin, swRead_flip, swRead_meet]
  cases swRead j a <;> cases swRead j b <;> rfl
def swGate (w : List SWire) (g : Gate) : SWire :=
  let arg := fun i => w.getD i swZero
  match g.op, g.inputs with
  | .not, xs => swFlip (arg (xs.headD w.length))
  | .and, [] => swFlip swZero
  | .or, [] => swZero
  | .and, [i] | .or, [i] => arg i
  | .and, i :: j :: _ => swMeet (arg i) (arg j)
  | .or, i :: j :: _ => swJoin (arg i) (arg j)
  | _, _ => swZero
def swExec (gs : List Gate) (w : List SWire) : List SWire :=
  gs.foldl (fun w g => w ++ [swGate w g]) w
def isBin (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma get_simple (w : List SWire) (i : Nat) : simple w (w.getD i swZero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a, List.mem_of_getElem? eq, rfl⟩)
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
lemma swGate_priced (w : List SWire) (g : Gate) : priced w (isBin g) (swGate w g).2 := by
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | not => exact Or.inl (get_simple w _)
  | _ => exact Or.inl (Or.inl rfl)
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^256 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^256 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^256 ∧ (w.getD i swZero).2.testBit 0 = false := by
    simp only [List.getD_eq_getElem?_getD]
    cases eq : w[i]? with
    | none => exact hz
    | some a => exact hw a (List.mem_of_getElem? eq)
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | not => exact hg (xs.headD w.length)
  | _ => exact hz
lemma swExec_lt (gs : List Gate) (w : List SWire)
    (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hw u hu
    · rw [List.mem_singleton.mp hu]; exact swGate_lt w hw g
lemma swRead_get (j : Nat) (w : List SWire) (i : Nat) :
    (w.map (swRead j)).getD i false = swRead j (w.getD i swZero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [swRead_zero]
lemma swGate_read (w : List SWire) (g : Gate)
    (legal : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (j : Nat) :
    swRead j (swGate w g) = g.op.eval (g.inputs.map fun i => (w.map (swRead j)).getD i false) := by
  simp_rw [swRead_get]
  obtain ⟨op, xs⟩ := g
  obtain ⟨hop, hlen⟩ := legal
  rcases hop with rfl | rfl | rfl <;>
    rcases xs with _ | ⟨i, _ | ⟨k, _ | ⟨h, rest⟩⟩⟩ <;>
    simp_all [swGate, GateOp.eval, swRead_flip, swRead_meet, swRead_join, swRead_zero]
lemma swExec_read (j : Nat) (gs : List Gate) (w : List SWire)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (swExec gs w).map (swRead j) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (swRead j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (swExec gs (w ++ [swGate w g])).map (swRead j) = _
    rw [ih _ (fun v hv => legal v (List.mem_cons_of_mem _ hv))]
    simp [swGate_read w g (legal g List.mem_cons_self) j]
lemma pull_live {T k S w z p} (h : Live T k S) (op : priced w p z)
    (sub : ∀ a ∈ S, a ∈ reps w ++ [z]) :
    ∃ l V, l ≤ k + p.toNat ∧ Live T l V ∧ ∀ a ∈ V, a ∈ reps w := by
  by_cases needed : z ∈ S
  · by_cases avail : z ∈ reps w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha : a ∈ reps w ∨ a = z) with old | rfl
      · exact old
      · exact avail
    · rcases op with easy | ⟨rfl, d, hd, a, ha, b, hb, na, nb, ab, rfl⟩
      · rcases easy with rfl | hm
        · exact (live_nonzero h 0 needed rfl).elim
        · exact (avail hm).elim
      · let U := S.erase (bin d a b)
        have tail : Live T k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase needed] using h
        have old (x : Nat) (hx : x ∈ U) : x ∈ reps w := by
          obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hx
          exact (by simpa using sub x mem : x ∈ reps w ∨ x = bin d a b).resolve_right ne
        have fresh : bin d a b ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e | h'
          · exact avail (e.symm ▸ ha)
          rcases Finset.mem_insert.mp h' with e | u
          · exact avail (e.symm ▸ hb)
          · exact avail (old _ u)
        exact ⟨k + 1, insert a (insert b U), by simp,
          ⟨U, a, b, d, hd, rfl, na, nb, ab, fresh, tail⟩, by simpa using And.intro ha (And.intro hb old)⟩
  · exact ⟨k, S, by omega, h, fun a ha => (by simpa [show a ≠ z from fun e => needed (e ▸ ha)] using sub a ha)⟩
lemma extract_live {T} (hT : T ≠ 0) (gs : List Gate) (w : List SWire)
    (found : T ∈ reps (swExec gs w)) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0, {T}, by simp, ⟨rfl, hT⟩, by simpa [swExec] using found⟩
  | cons g gs ih =>
    obtain ⟨k, S, lim, h, sub⟩ := ih (w ++ [swGate w g]) found
    have sub' : ∀ a ∈ S, a ∈ reps w ++ [(swGate w g).2] := by simpa [reps] using sub
    obtain ⟨l, V, cost, hl, raw⟩ := pull_live h (swGate_priced w g) sub'
    refine ⟨l, V, ?_, hl, raw⟩
    rw [List.countP_cons]
    cases e : isBin g <;> simp [e] at cost ⊢ <;> omega
def invW (a : Wire) : Wire := fun r => !(a r)
def comb2 (isOr : Bool) (a b : Wire) : Wire :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb4 (d : Nat) (a b : Wire) : Wire :=
  match d with
  | 0 => comb2 false a b
  | 1 => comb2 true a b
  | 2 => comb2 false a (invW b)
  | _ => comb2 false (invW a) b
def Constant (a : Wire) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def wcost (a : Wire) : Nat := by classical exact if Constant a then 1 else 0
noncomputable def wmass (xs : List Wire) : Nat := (xs.map wcost).sum
def Avail (pool : List Wire) (v : Wire) : Prop := v ∈ pool ∨ Constant v ∨ invW v ∈ pool
def Supply (pool xs : List Wire) : Prop := ∀ a ∈ xs, Avail pool a
def Reach (roots : List Wire) : Nat → List Wire → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List Wire) (a b : Wire),
      Reach roots p bank ∧ Avail bank a ∧ Avail bank b ∧ c = comb2 op a b :: bank
def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs
def Run (goal : Wire) : Nat → List Wire → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire) (rest : List Wire),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb4 op a b :: kept ka a (kept kb b rest))
lemma invW_inv (a : Wire) : invW (invW a) = a := by funext r; simp [invW]
lemma invW_const {a : Wire} (h : Constant a) : Constant (invW a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
lemma wcost_inv (a : Wire) : wcost (invW a) = wcost a := by
  have h : Constant (invW a) ↔ Constant a := ⟨fun hc => invW_inv a ▸ invW_const hc, invW_const⟩
  by_cases hc : Constant a
  · simp [wcost, hc, h.mpr hc]
  · simp [wcost, hc, mt h.mp hc]
lemma avail_inv {bank : List Wire} {a : Wire} (h : Avail bank a) : Avail bank (invW a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by rwa [invW_inv]))
  · exact Or.inr (Or.inl (invW_const h))
  · exact Or.inl h
lemma avail_cons {bank : List Wire} {v : Wire} (w : Wire) (h : Avail bank v) : Avail (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
lemma from_const (op : Bool) {a b : Wire} {bank : List Wire} (h : Constant a ∨ Constant b)
    (ha : Avail bank a) (hb : Avail bank b) : Avail bank (comb2 op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using hb
  · simpa [comb2] using hb
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using ha
  · simpa [comb2] using ha
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
lemma both_const (op : Bool) {a b : Wire} (ha : Constant a) (hb : Constant b) :
    Constant (comb2 op a b) := by
  obtain ⟨v, rfl⟩ := ha; obtain ⟨w, rfl⟩ := hb; cases op <;> exact ⟨_, rfl⟩
lemma extend_comb (roots : List Wire) {p bank a b} (d : Nat) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Avail bank a) (hb : Avail bank b) :
    ∃ q next, Reach roots q next ∧ Avail next (comb4 d a b) ∧
      (∀ v, Avail bank v → Avail next v) ∧ q + wcost a + wcost b ≤ p + 1 + wcost (comb4 d a b) := by
  have hprep : ∃ op x y, comb4 d a b = comb2 op x y ∧ Avail bank x ∧ Avail bank y ∧
      wcost x = wcost a ∧ wcost y = wcost b := by
    interval_cases d
    · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨false, a, invW b, rfl, ha, avail_inv hb, rfl, wcost_inv b⟩
    · exact ⟨false, invW a, b, rfl, avail_inv ha, hb, wcost_inv a, rfl⟩
  obtain ⟨op, x, y, eq, hx, hy, cx, cy⟩ := hprep
  rw [eq, ← cx, ← cy]
  classical
  by_cases c : Constant x ∨ Constant y
  · refine ⟨p, bank, hp, from_const op c hx hy, fun _ h => h, ?_⟩
    by_cases hcx : Constant x <;> by_cases hcy : Constant y
    · simp [wcost, hcx, hcy, both_const op hcx hcy]
    · simp [wcost, hcx, hcy]
    · simp [wcost, hcx, hcy]
    · exact (c.elim hcx hcy).elim
  · have hcx : ¬Constant x := fun h => c (Or.inl h)
    have hcy : ¬Constant y := fun h => c (Or.inr h)
    exact ⟨p + 1, _, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, Or.inl (by simp),
      fun _ h => avail_cons _ h, by simp [wcost, hcx, hcy]⟩
lemma wmass_kept (a : Wire) (xs : List Wire) (k : Bool) : wmass xs ≤ wmass (kept k a xs) := by
  cases k <;> simp [kept, wmass]
lemma contraction {goal : Wire} (nc : ¬Constant goal) {s ws} (h : Run goal s ws)
    (roots : List Wire) {p bank} (hp : Reach roots p bank) (hs : Supply bank ws) :
    ∃ q next, Reach roots q next ∧ Avail next goal ∧ q + wmass ws ≤ p + s := by
  classical
  induction s generalizing ws p bank with
  | zero =>
    have hmem : goal ∈ ws := h.mem_iff.mp (by simp)
    have hlen : wmass ws = wcost goal := by
      have := (h.map wcost).sum_eq
      simpa [wmass] using this.symm
    exact ⟨p, bank, hp, hs goal hmem, by simp [hlen, wcost, nc]⟩
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have hsa : Avail bank a := hs a (perm.mem_iff.mp (by simp))
    have hsb : Avail bank b := hs b (perm.mem_iff.mp (by simp))
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp hsa hsb
    have ht : Supply T (comb4 op a b :: kept ka a (kept kb b rest)) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hz
      · apply inc; apply hs; apply perm.mem_iff.mp
        cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto
    obtain ⟨q, W, hW, hv, hl⟩ := ih tail hT ht
    have hm1 := wmass_kept a (kept kb b rest) ka
    have hm2 := wmass_kept b rest kb
    have hp_eq : wmass ws = wcost a + wcost b + wmass rest := by
      have := (perm.map wcost).sum_eq
      simpa [wmass, Nat.add_assoc] using this.symm
    have hcons : wmass (comb4 op a b :: kept ka a (kept kb b rest)) =
        wcost (comb4 op a b) + wmass (kept ka a (kept kb b rest)) := rfl
    rw [hcons] at hl
    exact ⟨q, W, hW, hv, by omega⟩
def restrictW (f : Row → Row) (a : Wire) : Wire := fun r => a (f r)
lemma restrict_run (f : Row → Row) {goal s ws} (h : Run goal s ws) :
    Run (restrictW f goal) s (ws.map (restrictW f)) := by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have htail := ih tail
    have hk : ∀ (k : Bool) (x : Wire) (l : List Wire),
        (kept k x l).map (restrictW f) = kept k (restrictW f x) (l.map (restrictW f)) := by
      intro k x l; cases k <;> rfl
    have hc : restrictW f (comb4 op a b) = comb4 op (restrictW f a) (restrictW f b) := by
      funext r; rcases op with _ | _ | _ | op <;> rfl
    simp only [List.map_cons, hk, hc] at htail
    exact ⟨op, ka, kb, restrictW f a, restrictW f b, rest.map (restrictW f), hd,
      by simpa using perm.map (restrictW f), htail⟩
def obs (a : Nat) : Wire := fun r => a.testBit r.val
lemma obs_bin (d a b : Nat) : obs (bin d a b) = comb4 d (obs a) (obs b) := by
  funext r
  simp only [obs, testBit_bin, comb4, comb2, invW]
  rcases d with _ | _ | _ | d <;> rfl
lemma kept_nodup {α : Type} (c : Bool) (x : α) (l : List α) (hl : l.Nodup) (hx : x ∉ l) :
    (kept c x l).Nodup := by
  cases c <;> simp [kept, hl, hx]
lemma live_to_run {T k S} (h : Live T k S) (v : List Nat) (nd : v.Nodup) (eqv : v.toFinset = S) :
    Run (obs T) k (v.map obs) := by
  classical
  induction k generalizing S v with
  | zero =>
    obtain ⟨rfl, _⟩ := h
    have hp : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) nd (by simp [eqv])
    exact hp.map obs
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, fresh, tail⟩ := h
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tl := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm : mid.Nodup := kept_nodup kb b rest hr br
    have am : a ∉ mid := by cases hkb : kb <;> simp [mid, kept, hkb, hab, ar]
    have ntl : tl.Nodup := kept_nodup ka a mid bm am
    have htl : tl.toFinset = U := by
      have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
        cases c <;> simp [kept]
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kf, kf, er]
      ext j
      by_cases ha' : a ∈ U <;> by_cases hb' : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;>
        simp_all [ka, kb]
    have hf : bin d a b ∉ tl := fun hm =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (htl ▸ List.mem_toFinset.mpr hm)))
    have prog := ih tail (bin d a b :: tl) (List.nodup_cons.mpr ⟨hf, ntl⟩) (by simp [htl])
    have hk : ∀ (c : Bool) (x : Nat) (l : List Nat), (kept c x l).map obs = kept c (obs x) (l.map obs) := by
      intro c x l; cases c <;> rfl
    change Run (obs T) k ((bin d a b :: kept ka a (kept kb b rest)).map obs) at prog
    rw [List.map_cons, hk, hk, obs_bin] at prog
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) nd
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all
    exact ⟨d, ka, kb, obs a, obs b, rest.map obs, hd, by simpa using perm.map obs, prog⟩
def normPack (f : Wire) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).toNat
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 256 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 256 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^256) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
  · simp only [hr, dite_true]
    cases op <;> cases ha0 : a 0 <;> cases hb0 : b 0 <;>
      cases har : a ⟨r, hr⟩ <;> cases hbr : b ⟨r, hr⟩ <;>
      simp [comb2, opIdx, ha0, hb0, har, hbr]
  · simp only [hr, dite_false]
    rcases opIdx _ _ with _ | _ | _ | d <;> rfl
lemma avail_normPack {bank : List Wire} {v : Wire} (h : Avail bank v) :
    normPack v = 0 ∨ normPack v ∈ bank.map normPack := by
  rcases h with hm | hc | hi
  · exact Or.inr (List.mem_map_of_mem hm)
  · exact Or.inl (normPack_const hc)
  · exact Or.inr (by rw [← normPack_inv v]; exact List.mem_map_of_mem hi)
set_option maxRecDepth 16000 in
lemma reach_to_live_sub {roots : List Wire} {p bank} (h : Reach roots p bank)
    {T k S} (run : Live T k S) (sub : ∀ a ∈ S, a ∈ bank.map normPack) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ roots.map normPack := by
  induction p generalizing bank k S with
  | zero =>
    rcases h with rfl
    exact ⟨k, S, by omega, run, sub⟩
  | succ p ih =>
    obtain ⟨op, prev, a, b, hr, ha, hb, rfl⟩ := h
    obtain ⟨d, hd, eq⟩ := normPack_comb2 op a b
    let w := prev.map (fun f => (false, normPack f))
    have hreps : reps w = prev.map normPack := by simp [w, reps, List.map_map, Function.comp_def]
    have hp : priced w true (normPack (comb2 op a b)) := by
      rw [eq]
      exact made_priced w d (false, normPack a) (false, normPack b) hd
        (by simpa [simple, hreps] using avail_normPack ha)
        (by simpa [simple, hreps] using avail_normPack hb)
    have hsub' : ∀ x ∈ S, x ∈ reps w ++ [normPack (comb2 op a b)] := by
      intro x hx
      rcases List.mem_cons.mp (sub x hx) with rfl | hm
      · simp
      · simp [hreps, hm]
    obtain ⟨k', S', hk', run', sub'⟩ := pull_live run hp hsub'
    obtain ⟨l, V, hl, run'', sub''⟩ := ih hr run' (by simpa [hreps] using sub')
    simp only [Bool.toNat_true] at hk'
    exact ⟨l, V, by omega, run'', sub''⟩
def Lower (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map obs) p bank → Avail bank (obs T) → L ≤ p
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (255 ^^^ z)) ||| o) % 256, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^256 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma wmass_append (a b : List Wire) : wmass (a ++ b) = wmass a + wmass b := by simp [wmass]
lemma wmass_consts (xs : List Wire) (hc : ∀ x ∈ xs, Constant x) : wmass xs = xs.length := by
  classical
  induction xs with
  | nil => simp [wmass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [wmass, List.map_cons, List.sum_cons, List.length_cons, wcost, ha, ite_true]
    have := ih (fun x hx => hc x (by simp [hx]))
    simp only [wmass] at this
    omega
lemma lower_slice {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^256) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have subS : singles ⊆ S := fun a hs => raw_required run roots a sub (necessary a hs)
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have gc : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs eq)
  have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
    intro v hv
    obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
    exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
  obtain ⟨q, next, hq, hav, hbound⟩ :=
    contraction (gc ▸ obs_not_const hG0 hGlt hGb0) (restrict_run f (live_to_run run front nd fe))
      (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
  have hlo := prior q next hq (gc ▸ hav)
  have hmass : singles.card ≤ wmass ((front.map obs).map (restrictW f)) := by
    simp only [front, List.map_append, wmass_append]
    let xs := (singles.toList.map obs).map (restrictW f)
    have hc : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact constant a (Finset.mem_toList.mp ha')
    have hlen := wmass_consts xs hc
    simp only [xs, List.length_map, Finset.length_toList] at hlen
    change singles.card ≤ wmass xs + _
    rw [← hlen]
    exact Nat.le_add_right _ _
  have := hbound
  omega
def VAR (i : Nat) : Nat :=
  match i with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | 7 => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
  | _ => 0
def ALL256 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def varsOf (m : Nat) : List Nat :=
  (List.range 8).filterMap fun i => if m.testBit i then some (VAR i) else none
def fixWord (z o w : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    let fr := ((r &&& (255 ^^^ z)) ||| o) % 256
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma testBit_foldr_bits (p : Nat → Bool) (l : List Nat) (r : Nat) :
    (l.foldr (fun i acc => if p i then acc ||| (1 <<< i) else acc) 0).testBit r =
      (decide (r ∈ l) && p r) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hpa : p a = true
    · simp only [hpa, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases hra : r = a
      · subst hra; simp [hpa]
      · have h1 : (decide (a ≤ r) && (1 : Nat).testBit (r - a)) = false := by
          by_cases hle : a ≤ r
          · have hpos : r - a ≠ 0 := by omega
            simp only [hle, decide_true, Bool.true_and]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r - a)))
          · simp [hle]
        simp [h1, hra]
    · have hpf : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpf, Bool.false_eq_true, ite_false, ih]
      by_cases hra : r = a
      · subst hra; simp [hpf]
      · simp [hra]
lemma fixWord_eq_renameW (z o w : Nat) : fixWord z o w = renameW (fixRow z o) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fixWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 256
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 256) && decide (s < 256) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL256 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL256]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 256 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^256) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^256 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^256) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^256 ∧ a.testBit 0 = false := by
  simp only [checkRoots, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h
def liftCheck (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL256))
lemma lift_of {z o roots T other G essPairs L} (ok : liftCheck z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G := (fixWord_eq_renameW z o T).symm.trans heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [Bool.or_eq_true, beq_iff_eq, fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL256]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 256 r'.val |> fun e => by simpa [this] using e⟩
def evalInput (r : Row) : Fin 8 → Bool := fun i => r.val.testBit i.val
def packInput (x : Fin 8 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat + 128 * (x 7).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    have h6 := Bool.toNat_le (x 6); have h7 := Bool.toNat_le (x 7); omega⟩
lemma evalInput_packInput (x : Fin 8 → Bool) : evalInput (packInput x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (j : Fin 8),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat + 64 * b6.toNat + 128 * b7.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5, b6, b7].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) i
  fin_cases i <;> simpa [evalInput, packInput] using hi
lemma var_testBit (i : Fin 8) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
lemma sw_extract_full (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 255 := by
  let seeds : List SWire := (varsOf 255).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 255).all (fun a => decide (a < 2^256) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^256 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi7 : i < 8 := by simpa using hi2
      have hv : (varsOf 255)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget : (varsOf 255)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit ⟨i, hi7⟩ r
  have hev (r : Row) : swRead r.val out = T.testBit r.val := by
    have h1 := (swRead_get r.val final o).symm
    rw [show final = swExec gs seeds from rfl, swExec_read r.val gs seeds legal, hread_seeds r] at h1
    exact h1.trans (he r)
  have hout0 : out.1 = false := by
    have h0 := hev 0
    simp only [swRead, Fin.val_zero, hfinal_lt.2, hTb0, Bool.bne_false] at h0
    exact h0
  have hout2 : out.2 = T := by
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
    · have h := hev ⟨r, hr⟩
      simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]
    exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma replace_of_lower (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 255) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : ∀ g ∈ wit, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (edgeFn : (Fin 8 → Bool) → Bool)
    (hEdgeT : ∀ r : Row, edgeFn (evalInput r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput r)) = T.testBit r.val)
    (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (spec : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFn x) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFn x := by
  have hwEval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = edgeFn x := by
    intro x
    have hx := evalInput_packInput x
    rw [← hx]
    exact (hwEvalR (packInput x)).trans (hEdgeT (packInput x)).symm
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hlt : gates.countP isBin < gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full T hT0 hTlt hTb0 gates o legal (fun r => (spec (evalInput r)).trans (hEdgeT r))
    have hnd : S.toList.Nodup := Finset.nodup_toList S
    have hrun := live_to_run hlive S.toList hnd (by simp)
    have hsup : Supply ((varsOf 255).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 255).map obs)
        (show Reach ((varsOf 255).map obs) 0 ((varsOf 255).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    refine ⟨wit, wo, hwMono, by omega, hwEval⟩
  · refine ⟨gates, o, ?_, le_rfl, spec⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim

end Wide
namespace Small
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 128
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def flipOp (d : Nat) : Nat :=
  match d with
  | 2 => 3
  | 3 => 2
  | _ => d
lemma bin_comm_flip (d : Nat) (hd : d < 4) (a b : Nat) : bin d a b = bin (flipOp d) b a := by
  interval_cases d <;> simp [bin, flipOp, Nat.and_comm, Nat.or_comm]
lemma flipOp_lt {d : Nat} (hd : d < 4) : flipOp d < 4 := by
  interval_cases d <;> decide
lemma testBit_bin (d a b r : Nat) :
    (bin d a b).testBit r =
      match d with
      | 0 => a.testBit r && b.testBit r
      | 1 => a.testBit r || b.testBit r
      | 2 => a.testBit r && !b.testBit r
      | _ => !a.testBit r && b.testBit r := by
  rcases d with _ | _ | _ | d <;>
    simp [bin, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit r <;> cases b.testBit r <;> rfl
lemma bin_lt (d a b : Nat) (ha : a < 2^128) (hb : b < 2^128) : bin d a b < 2^128 := by
  have h1 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x &&& y) < 2^128 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ||| y) < 2^128 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ^^^ y) < 2^128 := fun x y hx hy =>
    Nat.xor_lt_two_pow hx hy
  rcases d with _ | _ | _ | d
  · exact h1 a b ha hb
  · exact h2 a b ha hb
  · exact h3 a (a &&& b) ha (h1 a b ha hb)
  · exact h3 b (a &&& b) hb (h1 a b ha hb)
def Live (T : Nat) : Nat → Finset Nat → Prop
  | 0, S => S = {T} ∧ T ≠ 0
  | k + 1, S => ∃ (U : Finset Nat) (a b d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k (insert (bin d a b) U)
lemma live_nonzero {T k S} (h : Live T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hT⟩ := h; simpa using hT
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma live_size {T k S} (h : Live T k S) : S.card ≤ k + 1 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; simp
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, hf, tail⟩ := h
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have ht := ih tail
    rw [Finset.card_insert_of_notMem hu] at ht
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega
lemma live_sep {T k S} (h : Live T k S) {r s : Nat} (hd : T.testBit r ≠ T.testBit s) :
    ∃ a ∈ S, a.testBit r ≠ a.testBit s := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; exact ⟨T, by simp, hd⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, _, tail⟩ := h
    obtain ⟨v, hv, hvd⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : a.testBit r = a.testBit s
      · refine ⟨b, by simp, fun hb => hvd ?_⟩
        rw [testBit_bin, testBit_bin, ha, hb]
      · exact ⟨a, by simp, ha⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv), hvd⟩
abbrev SWire := Bool × Nat
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
lemma pull_live {T k S w z p} (h : Live T k S) (op : priced w p z)
    (sub : ∀ a ∈ S, a ∈ reps w ++ [z]) :
    ∃ l V, l ≤ k + p.toNat ∧ Live T l V ∧ ∀ a ∈ V, a ∈ reps w := by
  by_cases needed : z ∈ S
  · by_cases avail : z ∈ reps w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha : a ∈ reps w ∨ a = z) with old | rfl
      · exact old
      · exact avail
    · rcases op with easy | ⟨rfl, d, hd, a, ha, b, hb, na, nb, ab, rfl⟩
      · rcases easy with rfl | hm
        · exact (live_nonzero h 0 needed rfl).elim
        · exact (avail hm).elim
      · let U := S.erase (bin d a b)
        have tail : Live T k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase needed] using h
        have old (x : Nat) (hx : x ∈ U) : x ∈ reps w := by
          obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hx
          exact (by simpa using sub x mem : x ∈ reps w ∨ x = bin d a b).resolve_right ne
        have fresh : bin d a b ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e | h'
          · exact avail (e.symm ▸ ha)
          rcases Finset.mem_insert.mp h' with e | u
          · exact avail (e.symm ▸ hb)
          · exact avail (old _ u)
        exact ⟨k + 1, insert a (insert b U), by simp,
          ⟨U, a, b, d, hd, rfl, na, nb, ab, fresh, tail⟩, by simpa using And.intro ha (And.intro hb old)⟩
  · exact ⟨k, S, by omega, h, fun a ha => (by simpa [show a ≠ z from fun e => needed (e ▸ ha)] using sub a ha)⟩
def invW (a : Wire) : Wire := fun r => !(a r)
def comb2 (isOr : Bool) (a b : Wire) : Wire :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb4 (d : Nat) (a b : Wire) : Wire :=
  match d with
  | 0 => comb2 false a b
  | 1 => comb2 true a b
  | 2 => comb2 false a (invW b)
  | _ => comb2 false (invW a) b
def Constant (a : Wire) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def wcost (a : Wire) : Nat := by classical exact if Constant a then 1 else 0
noncomputable def wmass (xs : List Wire) : Nat := (xs.map wcost).sum
def Avail (pool : List Wire) (v : Wire) : Prop := v ∈ pool ∨ Constant v ∨ invW v ∈ pool
def Supply (pool xs : List Wire) : Prop := ∀ a ∈ xs, Avail pool a
def Reach (roots : List Wire) : Nat → List Wire → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List Wire) (a b : Wire),
      Reach roots p bank ∧ Avail bank a ∧ Avail bank b ∧ c = comb2 op a b :: bank
def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs
def Run (goal : Wire) : Nat → List Wire → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire) (rest : List Wire),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb4 op a b :: kept ka a (kept kb b rest))
lemma invW_inv (a : Wire) : invW (invW a) = a := by funext r; simp [invW]
lemma invW_const {a : Wire} (h : Constant a) : Constant (invW a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
lemma wcost_inv (a : Wire) : wcost (invW a) = wcost a := by
  have h : Constant (invW a) ↔ Constant a := ⟨fun hc => invW_inv a ▸ invW_const hc, invW_const⟩
  by_cases hc : Constant a
  · simp [wcost, hc, h.mpr hc]
  · simp [wcost, hc, mt h.mp hc]
lemma avail_inv {bank : List Wire} {a : Wire} (h : Avail bank a) : Avail bank (invW a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by rwa [invW_inv]))
  · exact Or.inr (Or.inl (invW_const h))
  · exact Or.inl h
lemma avail_cons {bank : List Wire} {v : Wire} (w : Wire) (h : Avail bank v) : Avail (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
lemma from_const (op : Bool) {a b : Wire} {bank : List Wire} (h : Constant a ∨ Constant b)
    (ha : Avail bank a) (hb : Avail bank b) : Avail bank (comb2 op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using hb
  · simpa [comb2] using hb
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using ha
  · simpa [comb2] using ha
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
lemma both_const (op : Bool) {a b : Wire} (ha : Constant a) (hb : Constant b) :
    Constant (comb2 op a b) := by
  obtain ⟨v, rfl⟩ := ha; obtain ⟨w, rfl⟩ := hb; cases op <;> exact ⟨_, rfl⟩
lemma extend_comb (roots : List Wire) {p bank a b} (d : Nat) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Avail bank a) (hb : Avail bank b) :
    ∃ q next, Reach roots q next ∧ Avail next (comb4 d a b) ∧
      (∀ v, Avail bank v → Avail next v) ∧ q + wcost a + wcost b ≤ p + 1 + wcost (comb4 d a b) := by
  have hprep : ∃ op x y, comb4 d a b = comb2 op x y ∧ Avail bank x ∧ Avail bank y ∧
      wcost x = wcost a ∧ wcost y = wcost b := by
    interval_cases d
    · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨false, a, invW b, rfl, ha, avail_inv hb, rfl, wcost_inv b⟩
    · exact ⟨false, invW a, b, rfl, avail_inv ha, hb, wcost_inv a, rfl⟩
  obtain ⟨op, x, y, eq, hx, hy, cx, cy⟩ := hprep
  rw [eq, ← cx, ← cy]
  classical
  by_cases c : Constant x ∨ Constant y
  · refine ⟨p, bank, hp, from_const op c hx hy, fun _ h => h, ?_⟩
    by_cases hcx : Constant x <;> by_cases hcy : Constant y
    · simp [wcost, hcx, hcy, both_const op hcx hcy]
    · simp [wcost, hcx, hcy]
    · simp [wcost, hcx, hcy]
    · exact (c.elim hcx hcy).elim
  · have hcx : ¬Constant x := fun h => c (Or.inl h)
    have hcy : ¬Constant y := fun h => c (Or.inr h)
    exact ⟨p + 1, _, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, Or.inl (by simp),
      fun _ h => avail_cons _ h, by simp [wcost, hcx, hcy]⟩
lemma wmass_kept (a : Wire) (xs : List Wire) (k : Bool) : wmass xs ≤ wmass (kept k a xs) := by
  cases k <;> simp [kept, wmass]
lemma contraction {goal : Wire} (nc : ¬Constant goal) {s ws} (h : Run goal s ws)
    (roots : List Wire) {p bank} (hp : Reach roots p bank) (hs : Supply bank ws) :
    ∃ q next, Reach roots q next ∧ Avail next goal ∧ q + wmass ws ≤ p + s := by
  classical
  induction s generalizing ws p bank with
  | zero =>
    have hmem : goal ∈ ws := h.mem_iff.mp (by simp)
    have hlen : wmass ws = wcost goal := by
      have := (h.map wcost).sum_eq
      simpa [wmass] using this.symm
    exact ⟨p, bank, hp, hs goal hmem, by simp [hlen, wcost, nc]⟩
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have hsa : Avail bank a := hs a (perm.mem_iff.mp (by simp))
    have hsb : Avail bank b := hs b (perm.mem_iff.mp (by simp))
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp hsa hsb
    have ht : Supply T (comb4 op a b :: kept ka a (kept kb b rest)) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hz
      · apply inc; apply hs; apply perm.mem_iff.mp
        cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto
    obtain ⟨q, W, hW, hv, hl⟩ := ih tail hT ht
    have hm1 := wmass_kept a (kept kb b rest) ka
    have hm2 := wmass_kept b rest kb
    have hp_eq : wmass ws = wcost a + wcost b + wmass rest := by
      have := (perm.map wcost).sum_eq
      simpa [wmass, Nat.add_assoc] using this.symm
    have hcons : wmass (comb4 op a b :: kept ka a (kept kb b rest)) =
        wcost (comb4 op a b) + wmass (kept ka a (kept kb b rest)) := rfl
    rw [hcons] at hl
    exact ⟨q, W, hW, hv, by omega⟩
def restrictW (f : Row → Row) (a : Wire) : Wire := fun r => a (f r)
lemma restrict_run (f : Row → Row) {goal s ws} (h : Run goal s ws) :
    Run (restrictW f goal) s (ws.map (restrictW f)) := by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have htail := ih tail
    have hk : ∀ (k : Bool) (x : Wire) (l : List Wire),
        (kept k x l).map (restrictW f) = kept k (restrictW f x) (l.map (restrictW f)) := by
      intro k x l; cases k <;> rfl
    have hc : restrictW f (comb4 op a b) = comb4 op (restrictW f a) (restrictW f b) := by
      funext r; rcases op with _ | _ | _ | op <;> rfl
    simp only [List.map_cons, hk, hc] at htail
    exact ⟨op, ka, kb, restrictW f a, restrictW f b, rest.map (restrictW f), hd,
      by simpa using perm.map (restrictW f), htail⟩
def obs (a : Nat) : Wire := fun r => a.testBit r.val
lemma obs_bin (d a b : Nat) : obs (bin d a b) = comb4 d (obs a) (obs b) := by
  funext r
  simp only [obs, testBit_bin, comb4, comb2, invW]
  rcases d with _ | _ | _ | d <;> rfl
lemma kept_nodup {α : Type} (c : Bool) (x : α) (l : List α) (hl : l.Nodup) (hx : x ∉ l) :
    (kept c x l).Nodup := by
  cases c <;> simp [kept, hl, hx]
lemma live_to_run {T k S} (h : Live T k S) (v : List Nat) (nd : v.Nodup) (eqv : v.toFinset = S) :
    Run (obs T) k (v.map obs) := by
  classical
  induction k generalizing S v with
  | zero =>
    obtain ⟨rfl, _⟩ := h
    have hp : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) nd (by simp [eqv])
    exact hp.map obs
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, fresh, tail⟩ := h
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tl := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm : mid.Nodup := kept_nodup kb b rest hr br
    have am : a ∉ mid := by cases hkb : kb <;> simp [mid, kept, hkb, hab, ar]
    have ntl : tl.Nodup := kept_nodup ka a mid bm am
    have htl : tl.toFinset = U := by
      have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
        cases c <;> simp [kept]
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kf, kf, er]
      ext j
      by_cases ha' : a ∈ U <;> by_cases hb' : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;>
        simp_all [ka, kb]
    have hf : bin d a b ∉ tl := fun hm =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (htl ▸ List.mem_toFinset.mpr hm)))
    have prog := ih tail (bin d a b :: tl) (List.nodup_cons.mpr ⟨hf, ntl⟩) (by simp [htl])
    have hk : ∀ (c : Bool) (x : Nat) (l : List Nat), (kept c x l).map obs = kept c (obs x) (l.map obs) := by
      intro c x l; cases c <;> rfl
    change Run (obs T) k ((bin d a b :: kept ka a (kept kb b rest)).map obs) at prog
    rw [List.map_cons, hk, hk, obs_bin] at prog
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) nd
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all
    exact ⟨d, ka, kb, obs a, obs b, rest.map obs, hd, by simpa using perm.map obs, prog⟩
def normPack (f : Wire) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).toNat
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 128 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 128 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^128) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true]
    cases op <;> cases ha0 : a 0 <;> cases hb0 : b 0 <;>
      cases har : a ⟨r, hr⟩ <;> cases hbr : b ⟨r, hr⟩ <;>
      simp [comb2, opIdx, ha0, hb0, har, hbr]
  · simp only [hr, dite_false]
    rcases opIdx _ _ with _ | _ | _ | d <;> rfl
lemma avail_normPack {bank : List Wire} {v : Wire} (h : Avail bank v) :
    normPack v = 0 ∨ normPack v ∈ bank.map normPack := by
  rcases h with hm | hc | hi
  · exact Or.inr (List.mem_map_of_mem hm)
  · exact Or.inl (normPack_const hc)
  · exact Or.inr (by rw [← normPack_inv v]; exact List.mem_map_of_mem hi)
lemma reach_to_live_sub {roots : List Wire} {p bank} (h : Reach roots p bank)
    {T k S} (run : Live T k S) (sub : ∀ a ∈ S, a ∈ bank.map normPack) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ roots.map normPack := by
  induction p generalizing bank k S with
  | zero =>
    rcases h with rfl
    exact ⟨k, S, by omega, run, sub⟩
  | succ p ih =>
    obtain ⟨op, prev, a, b, hr, ha, hb, rfl⟩ := h
    obtain ⟨d, hd, eq⟩ := normPack_comb2 op a b
    let w := prev.map (fun f => (false, normPack f))
    have hreps : reps w = prev.map normPack := by simp [w, reps, List.map_map, Function.comp_def]
    have hp : priced w true (normPack (comb2 op a b)) := by
      rw [eq]
      exact made_priced w d (false, normPack a) (false, normPack b) hd
        (by simpa [simple, hreps] using avail_normPack ha)
        (by simpa [simple, hreps] using avail_normPack hb)
    have hsub' : ∀ x ∈ S, x ∈ reps w ++ [normPack (comb2 op a b)] := by
      intro x hx
      rcases List.mem_cons.mp (sub x hx) with rfl | hm
      · simp
      · simp [hreps, hm]
    obtain ⟨k', S', hk', run', sub'⟩ := pull_live run hp hsub'
    obtain ⟨l, V, hl, run'', sub''⟩ := ih hr run' (by simpa [hreps] using sub')
    simp only [Bool.toNat_true] at hk'
    exact ⟨l, V, by omega, run'', sub''⟩
def Lower (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map obs) p bank → Avail bank (obs T) → L ≤ p
def Impossible (T : Nat) (cap : Nat) (S : Finset Nat) : Prop :=
  ∀ k ≤ cap, ¬Live T k S
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
lemma lower_of_impossible {roots : List Nat} {T L : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (ess : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L + 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hnz : normPack (obs T) ≠ 0 := by rwa [hnormT]
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left hnz
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id roots]
    apply List.map_congr_left
    intro a ha'
    exact normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have heq : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    exact ⟨fun ha' => raw_required run roots a sub (ess a ha'), sub a⟩
  by_contra! small
  exact noRun k (by omega) (heq.symm ▸ run)
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
def Slice (raw : List Nat) (T d : Nat) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Nat),
    (∀ r : Row, d.testBit (f r).val = true) ∧
    (∀ a ∈ raw, Avail (roots.map obs) (restrictW f (obs a))) ∧
    ¬Constant (restrictW f (obs T)) ∧
    ∀ p bank, Reach (roots.map obs) p bank → Avail bank (restrictW f (obs T)) → L ≤ p
def isConstM (d a : Nat) : Bool := (a &&& d == 0) || (a &&& d == d)
def availM (d : Nat) (pm : List Nat) (a : Nat) : Bool :=
  let m := a &&& d
  m == 0 || m == d || pm.contains m || pm.contains (d ^^^ m)
lemma masked_eq_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (b &&& d)) : restrictW f (obs a) = restrictW f (obs b) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_zero_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = 0) : restrictW f (obs a) = fun _ => false := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_one_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = d) : restrictW f (obs a) = fun _ => true := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_comp_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (d ^^^ (b &&& d))) : restrictW f (obs a) = invW (restrictW f (obs b)) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simp only [Nat.testBit_and, Nat.testBit_xor, dom r, Bool.and_true] at h
  simp only [restrictW, obs, invW, h]
  cases b.testBit (f r).val <;> rfl
def poolSupply (f : Row → Row) (bank : List Wire) (pool : List Nat) : Prop :=
  ∀ a ∈ pool, Avail bank (restrictW f (obs a))
lemma availM_sound {f : Row → Row} {d a : Nat} {bank : List Wire} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hs : poolSupply f bank pool)
    (ok : availM d (pool.map (· &&& d)) a = true) :
    Avail bank (restrictW f (obs a)) := by
  simp only [availM, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq, List.mem_map] at ok
  rcases ok with ((h0 | h1) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero_obs dom h0⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one_obs dom h1⟩)
  · exact (masked_eq_obs dom he.symm) ▸ hs v hv
  · have hinv := avail_inv (hs v hv)
    have hcomp : restrictW f (obs a) = invW (restrictW f (obs v)) := by
      have hx : (a &&& d) = d ^^^ (v &&& d) := by
        have := congrArg (d ^^^ ·) he
        simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_self] using this.symm
      exact masked_comp_obs dom hx
    exact hcomp ▸ hinv
abbrev Choice := Nat × Nat × Nat
def choiceVal (c : Choice) : Nat := bin c.1 c.2.1 c.2.2
def choiceOK (d : Nat) (pm : List Nat) (c : Choice) : Bool :=
  decide (c.1 < 4) && availM d pm c.2.1 && availM d pm c.2.2
def makePool (d : Nat) (pool : List Nat) : List Choice → Option (List Nat)
  | [] => some pool
  | c :: cs => if choiceOK d (pool.map (· &&& d)) c then makePool d (choiceVal c :: pool) cs else none
lemma pay_choice {f : Row → Row} {d : Nat} {roots bank q} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d (pool.map (· &&& d)) c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  have ha := availM_sound dom hs valid.1.2
  have hb := availM_sound dom hs valid.2
  have hprep : ∃ op x y, comb4 c.1 (restrictW f (obs c.2.1)) (restrictW f (obs c.2.2)) = comb2 op x y ∧
      Avail bank x ∧ Avail bank y := by
    have hd := valid.1.1
    interval_cases c.1
    · exact ⟨false, _, _, rfl, ha, hb⟩
    · exact ⟨true, _, _, rfl, ha, hb⟩
    · exact ⟨false, _, _, rfl, ha, avail_inv hb⟩
    · exact ⟨false, _, _, rfl, avail_inv ha, hb⟩
  obtain ⟨op, x, y, eq, hx, hy⟩ := hprep
  refine ⟨comb2 op x y :: bank, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv
  · have hcv : restrictW f (obs (choiceVal c)) = comb2 op x y := by
      rw [← eq]; funext r; simp only [choiceVal, restrictW, obs, testBit_bin, comb4, comb2, invW]
      rcases c.1 with _ | _ | _ | d' <;> rfl
    exact hcv ▸ Or.inl (by simp)
  · exact avail_cons _ (hs v hv)
lemma makePool_sound {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {res} (ok : makePool d pool cs = some res) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next res := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨bank, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction
lemma count_constM {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (ws : List Nat) : ws.countP (isConstM d) ≤ wmass ((ws.map obs).map (restrictW f)) := by
  classical
  induction ws with
  | nil => simp [wmass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, wmass, List.sum_cons] at ih ⊢
    cases h : isConstM d a
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih.trans (Nat.le_add_left _ _)
    · have hc : Constant (restrictW f (obs a)) := by
        simp only [isConstM, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h0 | h1
        · exact ⟨false, masked_zero_obs dom h0⟩
        · exact ⟨true, masked_one_obs dom h1⟩
      simp only [ite_true, wcost, hc]
      omega
structure BoundPool where
  dom : Nat
  lb : Nat
  paid : Nat
  wires : List Nat
  pm : List Nat
def ValidPool (_raw : List Nat) (T : Nat) (c : BoundPool) : Prop :=
  c.pm = c.wires.map (· &&& c.dom) ∧
  ∃ (f : Row → Row) (roots : List Nat) (bank : List Wire),
    (∀ r : Row, c.dom.testBit (f r).val = true) ∧ ¬Constant (restrictW f (obs T)) ∧
    (∀ q ws, Reach (roots.map obs) q ws → Avail ws (restrictW f (obs T)) → c.lb ≤ q) ∧
    Reach (roots.map obs) c.paid bank ∧ poolSupply f bank c.wires
def materialize (raw : List Nat) (cs : List Choice) (d lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map fun pool => ⟨d, lb, cs.length, pool, pool.map (· &&& d)⟩
lemma materialize_sound {raw T d L cs c} (sl : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, base, nc, lo⟩ := sl
    obtain ⟨bank, hr, hs⟩ := makePool_sound dom (show Reach (roots.map obs) 0 (roots.map obs) from rfl) base cs he
    exact ⟨rfl, f, roots, bank, dom, nc, lo, by simpa using hr, hs⟩
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let z := choiceVal op
  let extra := !(availM c.dom c.pm z)
  decide (k + c.paid + extra.toNat < c.lb + (z :: rest).countP (isConstM c.dom)) &&
    rest.all (availM c.dom c.pm) && (!extra || choiceOK c.dom c.pm op)
lemma scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op :: rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  obtain ⟨hpm, f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  simp only [scalarPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at cut
  intro t ht run
  have finish (n : Nat) (out : List Wire) (hr : Reach (roots.map obs) n out)
      (hsup : poolSupply f out (choiceVal op :: rest))
      (hle : n = c.paid + (!(availM c.dom c.pm (choiceVal op))).toNat) : False := by
    have hcov : Supply out (((choiceVal op :: rest).map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact hsup a ha
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction nc (restrict_run f (live_to_run run (choiceVal op :: rest) nd rfl)) (roots.map obs) hr hcov
    have hlo := lo q next hq hav
    have hcm := count_constM dom (choiceVal op :: rest)
    have hineq := cut.1.1
    omega
  cases hav : availM c.dom c.pm (choiceVal op) with
  | true =>
    apply finish c.paid bank hp _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact availM_sound dom hs (hpm ▸ hav)
    · exact availM_sound dom hs (hpm ▸ cut.1.2 a ha)
  | false =>
    have hok : choiceOK c.dom (c.wires.map (· &&& c.dom)) op = true := by
      have h2 := cut.2
      simp only [hav, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_or] at h2
      exact hpm ▸ h2
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs op hok
    apply finish (c.paid + 1) out hr _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc (choiceVal op) (by simp)
    · have hpt : poolSupply f out c.wires := fun v hv => hc v (List.mem_cons_of_mem _ hv)
      exact availM_sound dom hpt (hpm ▸ cut.1.2 a ha)
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (127 ^^^ z)) ||| o) % 128, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 128
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 128 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^128) (hb : b < 2^128) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 128 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^128) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^128 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^128 := hS a (by simp)
    have hblt : b < 2^128 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^128 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^128 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^128 := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exact hzlt; exact hUlt x hx
    have nr := ih tail htail_lt
    simp only [Finset.image_insert, renameW_bin] at nr ⊢
    refine ⟨U.image (renameW f), renameW f a, renameW f b, d, hd, rfl,
      fun hz => ha (renameW_inj f onto halt (by decide) (hz.trans (renameW_zero f).symm)),
      fun hz => hb (renameW_inj f onto hblt (by decide) (hz.trans (renameW_zero f).symm)),
      fun heq => hab (renameW_inj f onto halt hblt heq), ?_, nr⟩
    intro hm
    rw [← renameW_bin] at hm
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt halt heq]; simp)
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt hblt heq]; simp)
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
    exact fresh (by rw [renameW_inj f onto hzlt (hUlt x hx) heq.symm]; simp [hx])
lemma wmass_append (a b : List Wire) : wmass (a ++ b) = wmass a + wmass b := by simp [wmass]
lemma wmass_consts (xs : List Wire) (hc : ∀ x ∈ xs, Constant x) : wmass xs = xs.length := by
  classical
  induction xs with
  | nil => simp [wmass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [wmass, List.map_cons, List.sum_cons, List.length_cons, wcost, ha, ite_true]
    have := ih (fun x hx => hc x (by simp [hx]))
    simp only [wmass] at this
    omega
lemma lower_slice {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^128) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have subS : singles ⊆ S := fun a hs => raw_required run roots a sub (necessary a hs)
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have gc : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs eq)
  have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
    intro v hv
    obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
    exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
  obtain ⟨q, next, hq, hav, hbound⟩ :=
    contraction (gc ▸ obs_not_const hG0 hGlt hGb0) (restrict_run f (live_to_run run front nd fe))
      (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
  have hlo := prior q next hq (gc ▸ hav)
  have hmass : singles.card ≤ wmass ((front.map obs).map (restrictW f)) := by
    simp only [front, List.map_append, wmass_append]
    let xs := (singles.toList.map obs).map (restrictW f)
    have hc : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact constant a (Finset.mem_toList.mp ha')
    have hlen := wmass_consts xs hc
    simp only [xs, List.length_map, Finset.length_toList] at hlen
    change singles.card ≤ wmass xs + _
    rw [← hlen]
    exact Nat.le_add_right _ _
  have := hbound
  omega
def VAR (i : Nat) : Nat :=
  match i with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000
  | _ => 0
def ALL128 : Nat := 0xffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 128, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL128 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 7) (hj : j < 7) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 7 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL128 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
  | true =>
    obtain ⟨heq, h10, h01⟩ := hr.1 hms
    rw [heq]
    by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
    · simp [hd, h10 hd, h01]
    · simp [hd, h01]
  | false =>
    rcases hr.2 hms with ⟨hd, h10, heq, h01⟩ | ⟨h10, h01, heq⟩
    · simp [hd, h10, heq, h01]
    · by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
      · simp [hd, h10 hd, h01, heq]
      · simp [hd, h01, heq]
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) : swapWord i j w < 2^128 := by
  have hi : i < 7 := by omega
  have h1 : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^128 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^128 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^128 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 7)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^128) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^128 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hr⟩, testBit_renameW _ _ (swapRow p.1 p.2 ⟨r, hr⟩), testBit_renameW _ _ ⟨r, hr⟩]
      rfl
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega)))]
lemma permRow_surj (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) :
    Function.Surjective (permRow swaps) := by
  induction swaps with
  | nil => intro r; exact ⟨r, rfl⟩
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    intro r
    obtain ⟨q, hq⟩ := ih hv.2 r
    refine ⟨swapRow p.1 p.2 q, ?_⟩
    change permRow ps (swapRow p.1 p.2 (swapRow p.1 p.2 q)) = r
    rw [swapRow_invol p.1 p.2 (by omega) hv.1.2, hq]
lemma permRow_rev_cancel (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) (r : Row) :
    permRow swaps.reverse (permRow swaps r) = r := by
  induction swaps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
        swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
      simp [permRow, List.reverse_cons, List.foldl_append]
    rw [h1, ih hv.2, swapRow_invol p.1 p.2 (by omega) hv.1.2]
lemma rotate_impossible {T n : Nat} {ws : List Nat} (hi : Impossible T n ws.toFinset)
    (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (hT : T < 2^128) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^128) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^128 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^128 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
  have run' := live_renameW run hr (permRow swaps.reverse) (permRow_surj swaps.reverse hvr)
  have hT' : renameW (permRow swaps.reverse) T = T := by
    conv_lhs => rw [← hfix]
    exact hinv_word T hT
  have hS' : (ws.map (permWord swaps)).toFinset.image (renameW (permRow swaps.reverse)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hinv_word x (hw x hx)]
    · intro ha
      exact ⟨permWord swaps a, ⟨a, ha, rfl⟩, hinv_word a (hw a ha)⟩
  rw [hT', hS'] at run'
  exact hi k hk run'
abbrev Decor := Nat × Nat × Nat
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1, bin d x.2.1 y.2.1, bin d x.2.2 y.2.2)
def dsep (x : Decor) : Nat := x.2.1 ^^^ x.2.2
def projBits (rows : List Nat) (w : Nat) : Nat :=
  rows.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0
lemma testBit_projBits (rows : List Nat) (w i : Nat) :
    (projBits rows w).testBit i = match rows[i]? with | none => false | some r => w.testBit r := by
  induction rows generalizing i with
  | nil => simp [projBits]
  | cons r rs ih =>
    simp only [projBits, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.not_le.mpr (by decide : 0 < 1)]
      cases w.testBit r <;> rfl
    | succ i =>
      simp only [List.getElem?_cons_succ, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
      have h0 : (if w.testBit r then (1 : Nat) else 0).testBit (i + 1) = false := by
        cases w.testBit r
        · simp
        · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ i + 1)))
      rw [h0, Bool.or_false]
      exact ih i
lemma projBits_bin (rows : List Nat) (d a b : Nat) :
    projBits rows (bin d a b) = bin d (projBits rows a) (projBits rows b) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_projBits, testBit_bin, testBit_projBits, testBit_projBits]
  cases rows[i]? with
  | none => rcases d with _ | _ | _ | d <;> rfl
  | some r => exact testBit_bin d a b r
def faithful (pos neg : List Nat) (x : Decor) : Prop :=
  x.2.1 = projBits pos x.1 ∧ x.2.2 = projBits neg x.1
lemma faithful_bin {pos neg x y} (d : Nat) (hx : faithful pos neg x) (hy : faithful pos neg y) :
    faithful pos neg (dbin d x y) :=
  ⟨by rw [dbin, hx.1, hy.1, projBits_bin], by rw [dbin, hx.2, hy.2, projBits_bin]⟩
def goodPairs (T : Nat) (pos neg : List Nat) : Prop :=
  pos.length = neg.length ∧ ∀ i < pos.length,
    T.testBit (pos.getD i 0) = true ∧ T.testBit (neg.getD i 0) = false
def fullMask (n : Nat) : Nat := (1 <<< n) - 1
abbrev Cov := Nat × Nat × Nat
def addCov (z : Nat) (c : Cov) : Cov :=
  (z ||| c.1, (z ^^^ (z &&& c.1)) ||| (c.2.1 ^^^ (c.2.1 &&& z)),
   (z &&& c.2.1) ||| (c.2.2 ^^^ (c.2.2 &&& z)))
def coverage (v : List Decor) : Cov := v.foldr (fun a c => addCov (dsep a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := c.1 ^^^ (c.1 &&& (c.2.1 &&& a))
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
lemma cov_one (c : Cov) (a : Nat) : takeOne (addCov a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOne, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
lemma cov_two (c : Cov) (a b : Nat) : takeTwo (addCov a (addCov b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwo, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma addCov_swap (c : Cov) (a b : Nat) : addCov a (addCov b c) = addCov b (addCov a c) := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [addCov, Nat.testBit_or]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
      simp only [addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor] <;>
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma cov_perm {l r : List Decor} (h : l.Perm r) : coverage l = coverage r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (dsep a)) ih
  | swap _ _ _ => exact addCov_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
def delOne (ws : List Decor) (a : Decor) (k : Bool) : List Decor := if k then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) : List Decor := delOne (delOne ws a ka) b kb
def restCov (c : Cov) (a b : Nat) (ka kb : Bool) : Nat :=
  if ka then (if kb then c.1 else takeOne c b) else if kb then takeOne c a else takeTwo c a b
lemma cov_delOne {ws : List Decor} (a : Decor) (ha : a ∈ ws) (k : Bool) :
    (coverage (delOne ws a k)).1 = if k then (coverage ws).1 else takeOne (coverage ws) (dsep a) := by
  cases k
  · change (coverage (ws.erase a)).1 = _
    rw [cov_perm (List.perm_cons_erase ha)]
    exact (cov_one _ _).symm
  · rfl
lemma cov_delTwo {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    (coverage (delTwo ws a b ka kb)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb := by
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
    have hp : ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hbm))
    change (coverage ((ws.erase a).erase b)).1 = takeTwo (coverage ws) _ _
    rw [cov_perm hp]
    exact (cov_two _ _ _).symm
  · exact cov_delOne a ha false
  · exact cov_delOne b hb false
  · rfl
lemma cov_testBit (ws : List Decor) (i : Nat) :
    (coverage ws).1.testBit i = true ↔ ∃ x ∈ ws, (dsep x).testBit i = true := by
  induction ws with
  | nil => simp [coverage]
  | cons a ws ih =>
    change (dsep a ||| (coverage ws).1).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp
lemma cov_required {T k pos neg} {ws : List Decor}
    (gp : goodPairs T pos neg) (hf : ∀ x ∈ ws, faithful pos neg x)
    (h : Live T k (ws.map Prod.fst).toFinset) :
    ((coverage ws).1 &&& fullMask pos.length) = fullMask pos.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  have hfm : (fullMask pos.length).testBit i = decide (i < pos.length) := by
    simp [fullMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pos.length
  · have ⟨hp, hn⟩ := gp.2 i hi
    have hsep : T.testBit (pos.getD i 0) ≠ T.testBit (neg.getD i 0) := by rw [hp, hn]; decide
    obtain ⟨v, hv, hvd⟩ := live_sep h hsep
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have hfx := hf x hx
    have hpi : pos[i]? = some (pos.getD i 0) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hni : neg[i]? = some (neg.getD i 0) := by
      have hi' : i < neg.length := gp.1 ▸ hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    have hbit : (dsep x).testBit i = true := by
      simp only [dsep, Nat.testBit_xor, hfx.1, hfx.2, testBit_projBits, hpi, hni]
      have h12 : x.1.testBit (pos.getD i 0) ≠ x.1.testBit (neg.getD i 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        exact hvd
      cases h1 : x.1.testBit (pos.getD i 0) <;> cases h2 : x.1.testBit (neg.getD i 0)
      · exact absurd (h1.trans h2.symm) h12
      · rfl
      · rfl
      · exact absurd (h1.trans h2.symm) h12
    have hc := (cov_testBit ws i).mpr ⟨x, hx, hbit⟩
    simp [hfm, hi, hc]
  · simp [hfm, hi]
def insertNat (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertNat a bs
def sortNats : List Nat → List Nat
  | [] => []
  | a :: bs => insertNat a (sortNats bs)
lemma insertNat_perm (a : Nat) (l : List Nat) : (insertNat a l).Perm (a :: l) := by
  induction l with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : a ≤ b
    · simp [insertNat, h]
    · exact by simpa [insertNat, h] using (List.Perm.cons b ih).trans (.swap a b bs)
lemma sortNats_perm (l : List Nat) : (sortNats l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertNat_perm a (sortNats bs)).trans (.cons a ih)
lemma sortNats_toFinset (l : List Nat) : (sortNats l).toFinset = l.toFinset := by
  ext x; simpa only [List.mem_toFinset] using (sortNats_perm l).mem_iff
def childTwo (ws : List Nat) (a b d : Nat) (ka kb : Bool) : List Nat :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
lemma erase_toFinset {l : List Nat} (nd : l.Nodup) (a : Nat) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [nd.mem_erase_iff]
lemma enum_step {T cap : Nat} {ws : List Nat} (nd : ws.Nodup) (out : T ∉ ws)
    (stepOK : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d < 4, ∀ ka kb : Bool,
      a ≠ b → bin d a b ≠ 0 → bin d a b ∉ ws → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k hk h
  cases k with
  | zero =>
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  | succ k =>
    obtain ⟨U, a, b, d, hd, he, _, _, hab, hf, tail⟩ := h
    have am : a ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_self a _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
    have fresh : bin d a b ∉ ws := fun hm => hf (he ▸ List.mem_toFinset.mpr hm)
    have hnz : bin d a b ≠ 0 := live_nonzero tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b from rfl, erase_toFinset (nd.erase _) b, erase_toFinset nd a]
    have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
      cases c <;> simp [kept]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kf, kf, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (nd.erase _).erase _
    have ar : a ∉ rest := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (nd.erase a).not_mem_erase
    have nk := kept_nodup kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have ndc : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr hm))),
        kept_nodup ka a _ nk ax⟩
    have eqc : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := live_size tail
    have hlen : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup ndc, eqc]; omega
    exact stepOK a am b bm d hd ka kb hab hnz fresh hlen k (by omega) (eqc.symm ▸ tail)
lemma delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k; exact List.erase_sublist; exact List.Sublist.refl _
lemma delTwo_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) : (delTwo ws a b ka kb).Sublist ws :=
  (delOne_sub _ _ _).trans (delOne_sub _ _ _)
lemma delTwo_len (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
  cases ka <;> cases kb <;> simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]
lemma unique_fst {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (hn (eq ▸ List.mem_map_of_mem hb')).elim
    · exact (hn (eq.symm ▸ List.mem_map_of_mem ha')).elim
    · exact ih ht ha' hb'
lemma delTwo_map_toFinset {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  have wn : ws.Nodup := nd.of_map
  have dn : (delOne ws a ka).Nodup := wn.sublist (delOne_sub ws a ka)
  have m1 (l : List Decor) (hl : l.Nodup) (x y : Decor) (c : Bool) :
      y ∈ delOne l x c ↔ y ∈ l ∧ (y ≠ x ∨ c = true) := by
    cases c <;> simp [delOne, hl.mem_erase_iff, and_comm]
  have km (v : Nat) : v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
      v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
    simp only [delTwo, List.mem_map, m1 _ wn, m1 _ dn]
    constructor
    · rintro ⟨w, ⟨⟨hw, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, h1.imp (fun h e => h (unique_fst nd hw ha e)) id,
        h2.imp (fun h e => h (unique_fst nd hw hb e)) id⟩
    · rintro ⟨⟨w, hw, rfl⟩, h1, h2⟩
      exact ⟨w, ⟨⟨hw, h1.imp (fun h e => h (congrArg Prod.fst e)) id⟩,
        h2.imp (fun h e => h (congrArg Prod.fst e)) id⟩, rfl⟩
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv := List.mem_map_of_mem (f := Prod.fst) hb
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (v : Nat) : v ∈ kept c x l ↔ (v = x ∧ c = true) ∨ v ∈ l := by
    cases c <;> simp [kept]
  ext v
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, km, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, dbin]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all
lemma childTwo_swap (v : List Nat) (nd : v.Nodup) (a b : Nat) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (y : Nat) : y ∈ kept c x l ↔ (y = x ∧ c = true) ∨ y ∈ l := by
    cases c <;> simp [kept]
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_comm_flip d hd a b]
  tauto
def varsOf (m : Nat) : List Nat :=
  (List.range 7).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    let fr := ((r &&& (127 ^^^ z)) ||| o) % 128
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma testBit_foldr_bits (p : Nat → Bool) (l : List Nat) (r : Nat) :
    (l.foldr (fun i acc => if p i then acc ||| (1 <<< i) else acc) 0).testBit r =
      (decide (r ∈ l) && p r) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hpa : p a = true
    · simp only [hpa, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases hra : r = a
      · subst hra; simp [hpa]
      · have h1 : (decide (a ≤ r) && (1 : Nat).testBit (r - a)) = false := by
          by_cases hle : a ≤ r
          · have hpos : r - a ≠ 0 := by omega
            simp only [hle, decide_true, Bool.true_and]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r - a)))
          · simp [hle]
        simp [h1, hra]
    · have hpf : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpf, Bool.false_eq_true, ite_false, ih]
      by_cases hra : r = a
      · subst hra; simp [hpf]
      · simp [hra]
lemma fixWord_eq_renameW (z o w : Nat) : fixWord z o w = renameW (fixRow z o) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fixWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 128
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 128 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h127 : ((r.val &&& (127 ^^^ z)) ||| o) < 128 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (127 ^^^ z)) < 128 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 7) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (127 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h127
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 7
    · have h7 : (127 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 128) && decide (s < 128) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL128 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL128]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 128 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^128) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^128 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^128) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^128 ∧ a.testBit 0 = false := by
  simp only [checkRoots, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h
def carryOK (swaps : List (Nat × Nat)) (roots1 : List Nat) (T1 : Nat) (roots2 : List Nat) (T2 : Nat) : Bool :=
  swapsValid swaps && checkProper T1 && checkRoots roots1 && checkProper T2 &&
    (permWord swaps T1 == T2) && roots1.all (fun a => freeIn roots2 (permWord swaps a))
lemma carry_of {swaps roots1 T1 roots2 T2 L} (ok : carryOK swaps roots1 T1 roots2 T2 = true)
    (hL : Lower roots2 T2 L) : Lower roots1 T1 L := by
  simp only [carryOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hsv, hT1⟩, hR1⟩, hT2⟩, heq⟩, hcov⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT1
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hT2
  have hR1' := checkRoots_sound hR1
  have heq' : renameW (permRow swaps) T1 = T2 := (permWord_eq_renameW swaps hsv T1 p1b).symm.trans heq
  have hcov' : ∀ a ∈ roots1, Avail (roots2.map obs) (restrictW (permRow swaps) (obs a)) := fun a ha =>
    freeIn_sound (permWord_eq_renameW swaps hsv a (hR1' a ha).1 ▸ hcov a ha)
  simpa using lower_slice p1a p1b p1c hR1' p2a p2b p2c (permRow swaps) heq' hcov' ∅ (by simp) (by simp) L hL
def liftCheck (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL128))
lemma lift_of {z o roots T other G essPairs L} (ok : liftCheck z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G := (fixWord_eq_renameW z o T).symm.trans heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [Bool.or_eq_true, beq_iff_eq, fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL128]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 128 r'.val |> fun e => by simpa [this] using e⟩
def goodPairsCheck (T : Nat) (pos neg : List Nat) : Bool :=
  (pos.length == neg.length) &&
    (List.range pos.length).all fun i => T.testBit (pos.getD i 0) && !(T.testBit (neg.getD i 0))
lemma goodPairs_of {T pos neg} (ok : goodPairsCheck T pos neg = true) : goodPairs T pos neg := by
  simp only [goodPairsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at ok
  exact ok
def autosCheck (T : Nat) (autos : List (List (Nat × Nat))) : Bool :=
  autos.all fun sw => swapsValid sw && (permWord sw T == T)
lemma autos_of {T autos} (ok : autosCheck T autos = true) :
    ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T := by
  simp only [autosCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at ok
  exact ok
def baseCheck (pos neg : List Nat) (base : List Decor) : Bool :=
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^128)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := by
  simp only [baseCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  intro x hx
  have h := ok x hx
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩
def forestRootCheck (roots : List Nat) (T : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    roots.all fun a => essPairs.any fun e => (e.1 == a) && checkEss1 T roots e.1 e.2.1 e.2.2
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)
abbrev NodeSpec := List Nat × List Nat × List Nat
lemma var_testBit (i : Fin 7) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
def sliceDirectCheck (z o zDead : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
    decide (zDead < 128) && (((z ||| zDead) &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord (z ||| zDead) o T == qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord (z ||| zDead) o a))
lemma subcube_fixRow_sup (z o zDead : Nat) (hz : z < 128) (hd : zDead < 128) (ho : o < 128)
    (hzo : ((z ||| zDead) &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow (z ||| zDead) o r).val = true := by
  have hsub := subcube_fixRow (z ||| zDead) o (Nat.or_lt_two_pow (n := 7) hz hd) ho hzo r
  unfold subcube at hsub ⊢
  rw [testBit_foldr_bits] at hsub ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsub ⊢
  refine ⟨hsub.1, ?_, hsub.2.2⟩
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun x => x.testBit i) hsub.2.1
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
  cases hfa : (fixRow (z ||| zDead) o r).val.testBit i <;> cases hzb : z.testBit i <;> simp_all
lemma slice_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) qL := by
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz, ho⟩, _hzo0⟩, hd⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  refine ⟨fixRow (z ||| zDead) o, qRoots, subcube_fixRow_sup z o zDead hz hd ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW (z ||| zDead) o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW, heq]
  exact hPrior
inductive BT (α : Type) where
  | empty : BT α
  | leaf : α → BT α
  | node : BT α → BT α → BT α
def btGet {α : Type} (d : α) : BT α → Nat → α
  | .empty, _ => d
  | .leaf x, _ => x
  | .node l r, i => if i &&& 1 == 0 then btGet d l (i >>> 1) else btGet d r (i >>> 1)
def btSet {α : Type} : Nat → BT α → Nat → α → BT α
  | 0, _, _, v => .leaf v
  | d + 1, .empty, i, v =>
    if i &&& 1 == 0 then .node (btSet d .empty (i >>> 1) v) .empty
    else .node .empty (btSet d .empty (i >>> 1) v)
  | d + 1, .leaf x, i, v =>
    if i &&& 1 == 0 then .node (btSet d (.leaf x) (i >>> 1) v) .empty
    else .node .empty (btSet d (.leaf x) (i >>> 1) v)
  | d + 1, .node l r, i, v =>
    if i &&& 1 == 0 then .node (btSet d l (i >>> 1) v) r
    else .node l (btSet d r (i >>> 1) v)
def btUpdate {α : Type} (d0 : α) : Nat → BT α → Nat → (α → α) → BT α
  | 0, .leaf x, _, f => .leaf (f x)
  | 0, _, _, f => .leaf (f d0)
  | d + 1, .empty, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d .empty (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d .empty (i >>> 1) f)
  | d + 1, .leaf x, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d (.leaf x) (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d (.leaf x) (i >>> 1) f)
  | d + 1, .node l r, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d l (i >>> 1) f) r
    else .node l (btUpdate d0 d r (i >>> 1) f)
def btAll {α : Type} (P : α → Prop) : BT α → Prop
  | .empty => True
  | .leaf x => P x
  | .node l r => btAll P l ∧ btAll P r
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction t generalizing i with
  | empty => exact hd
  | leaf x => exact ht
  | node l r ihl ihr =>
    unfold btGet
    split
    · exact ihl ht.1 _
    · exact ihr ht.2 _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact hv
  | succ d ih =>
    cases t with
    | empty =>
      unfold btSet; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btSet; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btSet; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases t with
    | leaf x => exact hf x ht
    | empty => exact hf d0 hd0
    | node _ _ => exact hf d0 hd0
  | succ d ih =>
    cases t with
    | empty =>
      unfold btUpdate; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btUpdate; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btUpdate; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
def btOfList {α : Type} (depth : Nat) (l : List α) : BT α :=
  (l.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) (0, BT.empty)).2
lemma btAll_ofList {α : Type} {P : α → Prop} {depth : Nat} {l : List α}
    (h : ∀ x ∈ l, P x) : btAll P (btOfList depth l) := by
  unfold btOfList
  have hgo : ∀ (xs : List α) (acc : Nat × BT α),
      (∀ x ∈ xs, P x) → btAll P acc.2 →
      btAll P (xs.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) acc).2 := by
    intro xs
    induction xs with
    | nil => intro acc _ hacc; exact hacc
    | cons x xs ih =>
      intro acc hx hacc
      exact ih (acc.1 + 1, btSet depth acc.2 acc.1 x)
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        (btAll_set hacc (hx x (List.mem_cons_self ..)))
  exact hgo l (0, BT.empty) h trivial
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL128 ^^^ VAR i else if o.testBit i then VAR i else ALL128
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&& fastBitMask z o 6
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 7) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL128.testBit r.val = true := by
    simp only [ALL128]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 128 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · have hsub : (subcube z o).testBit r = ((r &&& z == 0) && (r &&& o == o)) := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and,
      fastBitMask_testBit z o 0 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 1 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 2 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 3 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 4 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 5 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 7) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 7, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 7
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 7
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 128 ≤ r := by omega
      have ha : ALL128 < 2^128 := by decide
      have hv : VAR i < 2^128 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^128; decide
      have hlt_m : fastBitMask z o i < 2^128 := by
        unfold fastBitMask; split
        · exact Nat.xor_lt_two_pow ha hv
        · split; exact hv; exact ha
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by decide : 0 < 2) hle))
    have hsub : (subcube z o).testBit r = false := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and, hlt_f]
    rfl
lemma slice_fast_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL := by
  have ok2 := ok
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1.1.1 ok2.1.1.1.1.1.1.1.2 ok2.1.1.1.1.1.1.2]
  exact slice_direct ok hPrior
def hashWs64 (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) &&& 63
def bucketContainsBT (bks : BT (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (btGet [] bks (hashWs64 s)).contains s
def closeChildBT (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContainsBT prevBks (ws.map (permWord sw)))
lemma closeChildBT_sound {raw T pools autos prevBks k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChildBT pools autos prevBks k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChildBT, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContainsBT at hhit
    have hmem := List.contains_iff_mem.mp hhit
    have hb : ∀ xs ∈ btGet [] prevBks (hashWs64 (sortNats ((choiceVal op :: rest).map (permWord sw)))),
        Impossible T k xs.toFinset :=
      btAll_get hPrev (fun _ hx => (List.not_mem_nil hx).elim) _
    have himp := hb _ hmem
    rw [sortNats_toFinset] at himp
    have ⟨hsv, hfix⟩ := hAutos sw hsw
    have hvr : swapsValid sw.reverse = true := by simp only [swapsValid, List.all_reverse]; exact hsv
    have hinv_row_gen : ∀ (l : List (Nat × Nat)), swapsValid l = true →
        ∀ r : Row, permRow l.reverse (permRow l r) = r := by
      intro l hl
      induction l with
      | nil => intro r; rfl
      | cons p ps ih =>
        simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
        intro r
        have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
            swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
          simp [permRow, List.reverse_cons, List.foldl_append]
        rw [h1, ih hl.2, swapRow_invol p.1 p.2 (by omega) hl.1.2]
    have hinv_row2 : ∀ r : Row, permRow sw (permRow sw.reverse r) = r := by
      simpa using hinv_row_gen sw.reverse hvr
    have hinv_w : ∀ x : Nat, x < 2^128 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 128
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      rw [permWord_eq_renameW sw hsv x (hlt x hx)]
      exact renameW_lt _ x
    have hrot := rotate_impossible himp sw.reverse hvr hT hfixr hmap_lt
    have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
      exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
    rwa [hback] at hrot
abbrev FastPool := BoundPool × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else some (c, miss, vals.countP (isConstM c.dom))
def fastPoolCut (fp : FastPool) (k : Nat) (a b d : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let totC := fp.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && isConstM c.dom a then 1 else 0
    let dropB := if !kb && isConstM c.dom b then 1 else 0
    let z := bin d a b
    let cRest := totC - dropA - dropB + (if isConstM c.dom z then 1 else 0)
    let zIn := availM c.dom c.pm z
    let extra := if zIn then 0 else 1
    decide (k + c.paid + extra < c.lb + cRest) && (zIn || choiceOK c.dom c.pm (d, a, b))
lemma countP_erase {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {x : α} (hx : x ∈ l) :
    (l.erase x).countP p + (if p x then 1 else 0) = l.countP p := by
  have hp := List.perm_cons_erase hx
  have h1 := List.Perm.countP_eq p hp
  simp only [List.countP_cons] at h1
  omega
lemma countP_delTwo_fst (p : Nat → Bool) {ws : List Decor} {a b : Decor}
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map Prod.fst).countP p =
      (ws.map Prod.fst).countP p - (if !ka && p a.1 then 1 else 0) - (if !kb && p b.1 then 1 else 0) := by
  have hne : a ≠ b := fun e => hab (congrArg Prod.fst e)
  have hmap_erase : ∀ (l : List Decor) (x : Decor), (l.map Prod.fst).Nodup → x ∈ l →
      (l.erase x).map Prod.fst = (l.map Prod.fst).erase x.1 := by
    intro l x hnd hx
    induction l with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hyx : y = x
      · subst hyx; simp
      · have hne1 : y.1 ≠ x.1 := by
          intro eq; apply hnd.1; rw [eq]
          exact List.mem_map_of_mem ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx))
        have h1 : (y == x) = false := beq_false_of_ne hyx
        have h2 : (y.1 == x.1) = false := beq_false_of_ne hne1
        simp only [List.erase_cons, h1, h2, List.map_cons]
        exact congrArg (y.1 :: ·) (ih hnd.2 ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx)))
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne hne.symm).mpr hb
    have hnd1 : ((ws.erase a).map Prod.fst).Nodup := ((List.erase_sublist).map Prod.fst).nodup nd
    change (((ws.erase a).erase b).map Prod.fst).countP p = _
    rw [hmap_erase _ b hnd1 hbm, hmap_erase ws a nd ha]
    have ha1 : a.1 ∈ ws.map Prod.fst := List.mem_map_of_mem ha
    have hb1 : b.1 ∈ (ws.map Prod.fst).erase a.1 := (List.mem_erase_of_ne hab.symm).mpr (List.mem_map_of_mem hb)
    have c1 := countP_erase p ha1
    have c2 := countP_erase p hb1
    cases hpa : p a.1 <;> cases hpb : p b.1 <;> simp [hpa, hpb] at c1 c2 ⊢ <;> omega
  · change ((ws.erase a).map Prod.fst).countP p = _
    rw [hmap_erase ws a nd ha]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) ha)
    cases hpa : p a.1 <;> simp [hpa] at c1 ⊢ <;> omega
  · change ((ws.erase b).map Prod.fst).countP p = _
    rw [hmap_erase ws b nd hb]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) hb)
    cases hpb : p b.1 <;> simp [hpb] at c1 ⊢ <;> omega
  · simp [delTwo, delOne]
lemma fastPoolCut_sound {raw T ws a b d ka kb k c fp}
    (hP : ValidPool raw T c) (hprep : prepPool (ws.map Prod.fst) c = some fp)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 d ka kb = true) :
    Impossible T k (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  unfold prepPool at hprep
  dsimp only at hprep
  split at hprep
  · simp at hprep
  · simp only [Option.some.injEq] at hprep
    subst hprep
    unfold fastPoolCut at hcut
    dsimp only at hcut
    split at hcut
    · simp at hcut
    · next hmiss =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_filter, Bool.not_eq_true'] at hmiss
      have hsub := (delTwo_sub ws a b ka kb).map Prod.fst
      have h_all_avail : ((delTwo ws a b ka kb).map Prod.fst).all (availM c.dom c.pm) = true := by
        rw [List.all_eq_true]; intro w hw
        by_contra hna
        have hnf : availM c.dom c.pm w = false := Bool.eq_false_iff.mpr hna
        have hmem_ws : w ∈ ws.map Prod.fst := hsub.subset hw
        have hm := hmiss w ⟨hmem_ws, hnf⟩
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
        have hne_ab : a ≠ b := fun e => hab (congrArg Prod.fst e)
        have hnot_in : ∀ (x : Decor) (kx : Bool), kx = false → x ∈ ws → x.1 ∉ (delTwo ws a b ka kb).map Prod.fst → True := fun _ _ _ _ _ => trivial
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            exact List.Nodup.not_mem_erase hnd_ws hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · have hu_eq : u = a := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa)
          exact hna' hka hu_eq
        · have hu_eq : u = b := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb)
          exact hnb' hkb hu_eq
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut
      simp only [choiceVal, h_all_avail, Bool.true_and, Bool.and_true, List.countP_cons,
        Bool.and_eq_true, decide_eq_true_eq] at hcut ⊢
      rw [hcnt]
      rcases hcut with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          cases hcz : isConstM c.dom (bin d a.1 b.1) <;>
          simp only [hz, hcz, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
            Bool.and_eq_true, Bool.false_eq_true, ite_true, ite_false] at h1 ⊢ <;> omega
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          simp only [hz, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or] at h2 ⊢ <;>
          exact h2
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
  go false false && go true false && go false true && go true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^128) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (_hd : d < 4)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (hnz : bin d a.1 b.1 ≠ 0) (hfr : bin d a.1 b.1 ∉ ws.map Prod.fst)
    (test : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b :: delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := (z :: rest).map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := by
    simp only [child, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => hfr ((sub.map Prod.fst).subset hm), (sub.map Prod.fst).nodup nd⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hlt w (sub.subset hw)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hfr_b : (ws.any (fun v => v.1 == z.1)) = false := by
    rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
    have hvz : v.1 = bin d a.1 b.1 := beq_iff_eq.mp heq
    exact hfr (hvz ▸ List.mem_map_of_mem hv)
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    have hdl := delTwo_len ws a b ka kb ha hb ne
    simp only [child, rest, List.length_map, List.length_cons]
    omega
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have hlen : child.length ≤ cap := by omega
  have hcov := cov_required gp (ws := z :: rest)
    (fun w hw => by rcases List.mem_cons.mp hw with rfl | hw; exact faithful_bin d (hf a ha) (hf b hb); exact hf w (sub.subset hw)) h
  have hcov_eq : (coverage (z :: rest)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z := by
    change dsep z ||| (coverage rest).1 = _
    rw [cov_delTwo a b ha hb ne ka kb, Nat.or_comm]
  rw [hcov_eq] at hcov
  have hcov_b : (((restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z) &&& fullMask pos.length) != fullMask pos.length) = false := by
    simp [hcov]
  unfold evalMoveBT at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = false := Bool.eq_false_iff.mpr hfp
    simp only [hfp_f, Bool.false_eq_true, ↓reduceIte] at test
    exact closeChildBT_sound (raw := raw) (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT (fun _ hm => (List.not_mem_nil hm).elim) hAutos hPrev ndc hltc test k hk h
lemma testAllBT_pair {cap n fmask ws cov fpools autos prevBks l}
    (h : testAllBT cap n fmask ws cov fpools autos prevBks l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks a b d = true) ∨
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAllBT, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma nodeBT_sound {raw T pos neg ws fpools autos prevBks cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (checks : cap = 0 ∨ testAllBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0
    intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  have hcap : 0 < cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne hnz hfr _
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (x y : Decor) (d' : Nat) (hd' : d' < 4) (hx : x ∈ ws) (hy : y ∈ ws) (nxy : x.1 ≠ y.1)
      (k1 k2 : Bool) (hnz' : bin d' x.1 y.1 ≠ 0) (hfr' : bin d' x.1 y.1 ∉ ws.map Prod.fst)
      (ht : testPairBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPairBT, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMoveBT_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAllBT_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
def buildWiresBT (depth : Nat) (base : List Decor) (steps : List (Nat × Nat × Nat)) : BT Decor :=
  let init := (base.length, btOfList depth base)
  (steps.foldl (fun p s =>
    let a := btGet (0, 0, 0) p.2 s.2.1
    let b := btGet (0, 0, 0) p.2 s.2.2
    (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 a b))) init).2
lemma buildWiresBT_faithful {depth pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128)
        (ss.foldl (fun p s => (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 (btGet (0, 0, 0) p.2 s.2.1) (btGet (0, 0, 0) p.2 s.2.2)))) acc).2 := by
    intro ss
    induction ss with
    | nil => intro acc hacc; exact hacc
    | cons s ss ih =>
      intro acc hacc
      have ha := btAll_get hacc hdef s.2.1
      have hb := btAll_get hacc hdef s.2.2
      exact ih _ (btAll_set hacc ⟨faithful_bin s.1 ha.1 hb.1, bin_lt s.1 _ _ ha.2 hb.2⟩)
  exact hgo steps (base.length, btOfList depth base) h0
def buildPoolsBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : List PoolSpec) : BT (Option BoundPool) :=
  btOfList pdepth (pspecs.map fun (slIdx, chIdxs) =>
    match btGet none slices slIdx with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
      materialize raw cs dom lb)
lemma buildPoolsBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))} {pspecs : List PoolSpec}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsBT pdepth W raw slices pspecs) := by
  apply btAll_ofList
  intro o ho c hc
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp ho
  dsimp only at hmat
  have hsl := btAll_get (d := none) hSlices (fun _ h => by simp at h) slIdx
  cases heq : btGet none slices slIdx with
  | none => rw [heq] at hmat; exact absurd (hmat.trans hc) (by simp)
  | some sl =>
    rw [heq] at hmat
    exact materialize_sound (hsl sl heq) (hmat.trans hc)
def checkNodeBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  let vals := ws.map Prod.fst
  let fpools := ns.2.1.filterMap fun pIdx =>
    match btGet none poolTable pIdx with
    | none => none
    | some c => prepPool vals c
  let nodeAutos := ns.2.2.map fun aIdx => btGet [] autosTable aIdx
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^128 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun fp hfp => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hfp
      cases heq : btGet none poolTable pIdx with
      | none => simp [heq] at hmat
      | some c =>
        simp only [heq] at hmat
        have hvc := btAll_get hPoolTable (fun _ h => by simp at h) pIdx c heq
        have hfp_eq : fp.1 = c := by
          unfold prepPool at hmat
          dsimp only at hmat
          split at hmat
          · simp at hmat
          · simp only [Option.some.injEq] at hmat; rw [← hmat]
        rw [hfp_eq]
        exact ⟨hvc, hmat⟩)
    (fun sw hsw => by
      obtain ⟨aIdx, _, rfl⟩ := List.mem_map.mp hsw
      exact btAll_get hAutos ⟨rfl, rfl⟩ aIdx)
    hPrev ok.2
def nodeValsBT (W : BT Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (btGet (0, 0, 0) W idx).1)
def buildBucketsBT (W : BT Decor) (nodes : List NodeSpec) : BT (List (List Nat)) :=
  nodes.foldl (fun acc ns =>
    let xs := nodeValsBT W ns
    btUpdate [] 6 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := fun ns hns => by
    unfold nodeValsBT; rw [sortNats_toFinset]
    exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := trivial
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
lemma lower_of_forestBT {roots T cap} {topBks : BT (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : btAll (fun bk => ∀ xs ∈ bk, Impossible T cap xs.toFinset) topBks)
    (hRoot : bucketContainsBT topBks roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContainsBT at hRoot
    exact btAll_get hTop (fun _ h => (List.not_mem_nil h).elim) _ _ (List.contains_iff_mem.mp hRoot)
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def hashWs (nb : Nat) (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) % nb
def bucketContains (buckets : Array (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (buckets.getD (hashWs buckets.size s) []).contains s
def closeChild (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContains prevBuckets (ws.map (permWord sw)))
lemma closeChild_sound {raw T pools autos prevBuckets k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T k xs.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChild pools autos prevBuckets k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContains at hhit
    simp only [Array.getD, List.contains_eq_mem, decide_eq_true_eq] at hhit
    split at hhit
    next hlt_b =>
      have himp := hPrev _ hlt_b _ hhit
      rw [sortNats_toFinset] at himp
      have ⟨hsv, hfix⟩ := hAutos sw hsw
      have hvr : swapsValid sw.reverse = true := by simp only [swapsValid, List.all_reverse]; exact hsv
      have hinv_row_gen : ∀ (l : List (Nat × Nat)), swapsValid l = true →
          ∀ r : Row, permRow l.reverse (permRow l r) = r := by
        intro l hl
        induction l with
        | nil => intro r; rfl
        | cons p ps ih =>
          simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
          intro r
          have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
              swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
            simp [permRow, List.reverse_cons, List.foldl_append]
          rw [h1, ih hl.2, swapRow_invol p.1 p.2 (by omega) hl.1.2]
      have hinv_row2 : ∀ r : Row, permRow sw (permRow sw.reverse r) = r := by
        simpa using hinv_row_gen sw.reverse hvr
      have hinv_w : ∀ x : Nat, x < 2^128 → permWord sw.reverse (permWord sw x) = x := by
        intro x hx
        have h1 := permWord_eq_renameW sw hsv x hx
        have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
        rw [h2, h1]
        apply Nat.eq_of_testBit_eq; intro r
        by_cases hrr : r < 128
        · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
        · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
              Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
      have hfix_r : permWord sw.reverse T = T := by
        conv_lhs => rw [← hfix]
        exact hinv_w T hT
      have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
        intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [permWord_eq_renameW sw hsv x (hlt x hx)]
        exact renameW_lt _ x
      have hrot := rotate_impossible himp sw.reverse hvr hT hfix_r hmap_lt
      have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
        exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
      rwa [hback] at hrot
    next => simp at hhit
def evalMove (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild pools autos prevBuckets (cap - 1) rest (d, a.1, b.1)
def testPair (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMove cap n fmask ws cov pools autos prevBuckets d a b z
  go false false && go true false && go false true && go true true
def testAll (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPair cap n fmask ws cov pools autos prevBuckets a b)) &&
      testAll cap n fmask ws cov pools autos prevBuckets bs
lemma evalMove_sound {raw T pos neg ws pools autos prevBuckets cap a b d ka kb}
    (hT : T < 2^128)
    (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (hd : d < 4)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (hnz : (dbin d a b).1 ≠ 0) (hfr : (dbin d a b).1 ∉ ws.map Prod.fst)
    (test : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets
      d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => hfr ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      exact hlt w (sub.subset hw)
  have hfr_b : ws.any (fun v => v.1 == z.1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hh
    exact hfr (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    change _ = (z.1 :: rest.map Prod.fst).length
    rw [List.length_cons, List.length_map, delTwo_len ws a b ka kb ha hb ne, Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have hlen : child.length ≤ cap := by omega
  have hcov := cov_required gp (ws := z :: rest)
    (fun w hw => by rcases List.mem_cons.mp hw with rfl | hw; exact faithful_bin d (hf a ha) (hf b hb); exact hf w (sub.subset hw)) h
  have hcov_eq : (coverage (z :: rest)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z := by
    change dsep z ||| (coverage rest).1 = _
    rw [cov_delTwo a b ha hb ne ka kb, Nat.or_comm]
  rw [hcov_eq] at hcov
  have hcov_b : (((restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z) &&& fullMask pos.length) != fullMask pos.length) = false := by
    simp [hcov]
  unfold evalMove at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  exact closeChild_sound (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT hPools hAutos hPrev ndc hltc test k hk h
lemma testAll_pair {cap n fmask ws cov pools autos prevBuckets l}
    (h : testAll cap n fmask ws cov pools autos prevBuckets l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets a b d = true) ∨
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAll, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma node_sound {raw T pos neg ws pools autos prevBuckets cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (checks : cap = 0 ∨ testAll cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0; intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  have hcap : 0 < cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne hnz hfr _
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (x y : Decor) (d' : Nat) (hd' : d' < 4) (hx : x ∈ ws) (hy : y ∈ ws) (nxy : x.1 ≠ y.1)
      (k1 k2 : Bool) (hnz' : bin d' x.1 y.1 ≠ 0) (hfr' : bin d' x.1 y.1 ∉ ws.map Prod.fst)
      (ht : testPair cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPair, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMove_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAll_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
lemma lower_of_forest {roots T cap} {topBuckets : Array (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : ∀ i (hi : i < topBuckets.size), ∀ xs ∈ topBuckets[i], Impossible T cap xs.toFinset)
    (hRoot : bucketContains topBuckets roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContains Array.getD at hRoot
    dsimp only at hRoot
    split at hRoot
    next hi => exact hTop _ hi _ (List.contains_iff_mem.mp hRoot)
    next => simp at hRoot
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def buildWires (base : List Decor) (steps : List (Nat × Nat × Nat)) : Array Decor :=
  steps.foldl (fun arr s =>
    let a := arr.getD s.2.1 (0, 0, 0)
    let b := arr.getD s.2.2 (0, 0, 0)
    arr.push (dbin s.1 a b)) base.toArray
lemma buildWires_faithful {pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    ∀ x ∈ (buildWires base steps).toList, faithful pos neg x ∧ x.1 < 2^128 := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hstep : ∀ (arr : Array Decor) (s : Nat × Nat × Nat),
      (∀ x ∈ arr.toList, faithful pos neg x ∧ x.1 < 2^128) →
      ∀ x ∈ (arr.push (dbin s.1 (arr.getD s.2.1 (0, 0, 0)) (arr.getD s.2.2 (0, 0, 0)))).toList,
        faithful pos neg x ∧ x.1 < 2^128 := by
    intro arr s harr x hx
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact harr x hx
    · have hget (i : Nat) : faithful pos neg (arr.getD i (0, 0, 0)) ∧ (arr.getD i (0, 0, 0)).1 < 2^128 := by
        unfold Array.getD
        split
        next hi => exact harr arr[i] (Array.getElem_mem_toList hi)
        next => exact hdef
      exact ⟨faithful_bin s.1 (hget s.2.1).1 (hget s.2.2).1, bin_lt s.1 _ _ (hget s.2.1).2 (hget s.2.2).2⟩
  unfold buildWires
  have hinit : ∀ x ∈ base.toArray.toList, faithful pos neg x ∧ x.1 < 2^128 := by simpa using hbase
  clear hbase
  generalize base.toArray = acc at hinit ⊢
  induction steps generalizing acc with
  | nil => exact hinit
  | cons s ss ih => exact ih _ (hstep acc s hinit)
lemma array_forall_of_list {α : Type} {P : α → Prop} {l : List α} (h : ∀ x ∈ l, P x) :
    ∀ i (hi : i < l.toArray.size), P l.toArray[i] :=
  fun i hi => h l.toArray[i] (Array.getElem_mem_toList hi)
def buildPools (W : Array Decor) (raw : List Nat) (slices : Array (Nat × Nat))
    (pspecs : List PoolSpec) : Array (Option BoundPool) :=
  (pspecs.map fun (slIdx, chIdxs) =>
    match slices[slIdx]? with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
      materialize raw cs dom lb).toArray
lemma buildPools_sound {W : Array Decor} {raw T} {slices : Array (Nat × Nat)} {pspecs : List PoolSpec}
    (hSlices : ∀ i (hi : i < slices.size), Slice raw T slices[i].1 slices[i].2) :
    ∀ i (hi : i < (buildPools W raw slices pspecs).size),
      ∀ c, (buildPools W raw slices pspecs)[i] = some c → ValidPool raw T c := by
  intro i hi c hc
  unfold buildPools at hi hc
  have hmem : some c ∈ pspecs.map (fun (slIdx, chIdxs) =>
      match slices[slIdx]? with
      | none => none
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
        materialize raw cs dom lb) := by
    rw [← hc]
    exact Array.getElem_mem_toList hi
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp hmem
  cases hget_sl : slices[slIdx]? with
  | none => simp [hget_sl] at hmat
  | some sl =>
    simp only [hget_sl] at hmat
    have ⟨hsi, hval⟩ := Array.getElem?_eq_some_iff.mp hget_sl
    exact materialize_sound (hval ▸ hSlices slIdx hsi) hmat
def checkNode (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  let vals := ws.map Prod.fst
  let pools := ns.2.1.filterMap fun pIdx => poolTable.getD pIdx none
  let nodeAutos := ns.2.2.filterMap fun aIdx => autosTable[aIdx]?
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAll k ws.length fmask ws (coverage ws) pools nodeAutos prevBuckets ws)
def checkNodes (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNode W T fmask poolTable autosTable prevBuckets k)
lemma checkNode_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (ok : checkNode W T (fullMask pos.length) poolTable autosTable prevBuckets k ns = true) :
    Impossible T k ((ns.1.map fun idx => (W.getD idx (0, 0, 0)).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (W.getD idx (0, 0, 0)) ∧ (W.getD idx (0, 0, 0)).1 < 2^128 := by
    unfold Array.getD; split
    next hi => exact hW W[idx] (Array.getElem_mem_toList hi)
    next => exact hdef
  unfold checkNode at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (W.getD idx (0, 0, 0)).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply node_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun c hc => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hc
      unfold Array.getD at hmat
      split at hmat
      next hi => exact hPoolTable pIdx hi c hmat
      next => simp at hmat)
    (fun sw hsw => by
      obtain ⟨aIdx, _, ha⟩ := List.mem_filterMap.mp hsw
      have ⟨hi, hval⟩ := Array.getElem?_eq_some_iff.mp ha
      exact hAutos sw (hval ▸ Array.getElem_mem_toList hi))
    hPrev ok.2
def nodeVals (W : Array Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (W.getD idx (0, 0, 0)).1)
def insertBucket (buckets : Array (List (List Nat))) (xs : List Nat) : Array (List (List Nat)) :=
  let idx := hashWs buckets.size xs
  if h : idx < buckets.size then
    let b := buckets[idx]
    if b.contains xs then buckets else buckets.set idx (xs :: b) h
  else buckets
def buildBuckets (nb : Nat) (W : Array Decor) (nodes : List NodeSpec) : Array (List (List Nat)) :=
  nodes.foldl (fun acc ns => insertBucket acc (nodeVals W ns)) (Array.replicate nb [])
lemma insertBucket_mem {bks : Array (List (List Nat))} {P : List Nat → Prop} {xs : List Nat}
    (hb : ∀ i (hi : i < bks.size), ∀ ys ∈ bks[i], P ys) (hxs : P xs) :
    ∀ i (hi : i < (insertBucket bks xs).size), ∀ ys ∈ (insertBucket bks xs)[i], P ys := by
  unfold insertBucket
  dsimp only
  split
  next hidx =>
    split
    · exact hb
    · intro i hi ys hys
      rw [Array.size_set] at hi
      rw [Array.getElem_set] at hys
      split at hys
      next =>
        rcases List.mem_cons.mp hys with rfl | hys'
        · exact hxs
        · exact hb _ hidx ys hys'
      next => exact hb i hi ys hys
  next => exact hb
lemma buildBuckets_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k nb}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (hNodes : checkNodes W T (fullMask pos.length) poolTable autosTable prevBuckets k nodes = true) :
    ∀ i (hi : i < (buildBuckets nb W nodes).size), ∀ xs ∈ (buildBuckets nb W nodes)[i], Impossible T k xs.toFinset := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeVals W ns).toFinset := fun ns hns => by
    unfold nodeVals
    rw [sortNats_toFinset]
    exact checkNode_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBuckets
  have hinit : ∀ i (hi : i < (Array.replicate nb ([] : List (List Nat))).size),
      ∀ xs ∈ (Array.replicate nb ([] : List (List Nat)))[i], Impossible T k xs.toFinset := by
    intro i hi xs hxs; simp at hxs
  generalize Array.replicate nb ([] : List (List Nat)) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    exact ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      (insertBucket acc (nodeVals W ns)) (insertBucket_mem hinit (hmem ns (List.mem_cons_self ..)))
lemma checkNodesBT_mem {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k nodes}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := by
  intro ns hns
  unfold nodeValsBT; rw [sortNats_toFinset]
  exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
lemma forall_append {α : Type} {P : α → Prop} {l1 l2 : List α}
    (h1 : ∀ x ∈ l1, P x) (h2 : ∀ x ∈ l2, P x) : ∀ x ∈ l1 ++ l2, P x := by
  intro x hx; rcases List.mem_append.mp hx with h | h; exact h1 x h; exact h2 x h
lemma buildBucketsBT_of_mem {W : BT Decor} {T k nodes}
    (hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := trivial
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
def buildPoolsSubBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : BT (Option PoolSpec)) (used : List Nat) : BT (Option BoundPool) :=
  used.foldl (fun acc pIdx =>
    match btGet none pspecs pIdx with
    | none => acc
    | some (slIdx, chIdxs) =>
      match btGet none slices slIdx with
      | none => acc
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
        btSet pdepth acc pIdx (materialize raw cs dom lb)) BT.empty
lemma buildPoolsSubBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))}
    {pspecs : BT (Option PoolSpec)} {used : List Nat}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsSubBT pdepth W raw slices pspecs used) := by
  unfold buildPoolsSubBT
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := trivial
  generalize (BT.empty : BT (Option BoundPool)) = acc at hinit ⊢
  induction used generalizing acc with
  | nil => exact hinit
  | cons pIdx rest ih =>
    apply ih
    dsimp only
    cases hps : btGet none pspecs pIdx with
    | none => simp only [hps]; exact hinit
    | some spec =>
      cases hsl : btGet none slices spec.1 with
      | none => simp only [hps, hsl]; exact hinit
      | some sl =>
        simp only [hps, hsl]
        apply btAll_set hinit
        intro c hc
        exact materialize_sound (btAll_get (d := none) hSlices (fun _ h => by simp at h) spec.1 sl hsl) hc

def dualRow (r : Row) : Row := ⟨(r.val ^^^ 127) % 128, Nat.mod_lt _ (by decide)⟩

lemma map_available (f : Row → Row) {b c : List Wire}
    (cover : ∀ w ∈ b, Avail c (restrictW f w)) {w : Wire} (hw : Avail b w) :
    Avail c (restrictW f w) := by
  rcases hw with hb | ⟨bit,rfl⟩ | hi
  · exact cover _ hb
  · exact Or.inr (Or.inl ⟨bit,rfl⟩)
  · have h : Avail c (invW (restrictW f w)) := cover _ hi
    simpa only [invW_inv] using avail_inv h

lemma map_reach (f : Row → Row) {R S : List Wire}
    (cover : ∀ w ∈ R, Avail S (restrictW f w)) {p b} (hr : Reach R p b) :
    ∃ c, Reach S p c ∧ ∀ w ∈ b, Avail c (restrictW f w) := by
  induction p generalizing b with
  | zero =>
    have hb : b = R := hr
    exact ⟨S,rfl,hb.symm ▸ cover⟩
  | succ p ih =>
    obtain ⟨op,b,a,d,prev,ha,hd,rfl⟩ := hr
    obtain ⟨c,hc,hmap⟩ := ih prev
    let w := comb2 op (restrictW f a) (restrictW f d)
    have eq : restrictW f (comb2 op a d) = w := by cases op <;> rfl
    refine ⟨w :: c,⟨op,c,_,_,hc,map_available f hmap ha,map_available f hmap hd,rfl⟩,?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with rfl | hold
    · rw [eq]
      exact Or.inl List.mem_cons_self
    · exact avail_cons w (hmap t hold)

lemma dualLower {roots : List Nat} {T G L : Nat}
    (hvars : ∀ r : Row, roots.all (fun a => decide (obs a (dualRow r) = !(obs a r))) = true)
    (hgoal : ∀ r : Row, (!(obs T (dualRow r))) = obs G r)
    (prior : Lower roots G L) : Lower roots T L := by
  intro p bank hr hav
  have maps (w : Wire) (hw : w ∈ roots.map obs) : Avail (roots.map obs) (restrictW dualRow w) := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    have eq : restrictW dualRow (obs a) = invW (obs a) :=
      funext fun r => of_decide_eq_true (List.all_eq_true.mp (hvars r) a ha)
    rw [eq]
    exact avail_inv (Or.inl (List.mem_map.mpr ⟨a,ha,rfl⟩))
  obtain ⟨c,hc,hmap⟩ := map_reach dualRow maps hr
  have eq : invW (restrictW dualRow (obs T)) = obs G := funext hgoal
  exact prior p c hc (eq ▸ avail_inv (map_available dualRow hmap hav))

def identifyRow (z o i j : Nat) (r : Row) : Row :=
  let mask := if r.val.testBit i then 1 <<< j else 0
  ⟨((fixRow z o r).val &&& (127 ^^^ (1 <<< j)) ||| mask) % 128, Nat.mod_lt _ (by decide)⟩
lemma mappedSlice {f : Row → Row} {raw R : List Nat} {T G D L : Nat}
    (proper : checkProper G = true) (inDomain : ∀ r : Row, D.testBit (f r).val = true)
    (covered : raw.all (fun v => freeIn R (renameW f v)) = true)
    (mapped : renameW f T = G) (bound : Lower R G L) : Slice raw T D L := by
  have ⟨g0,glt,gb0⟩ := checkProper_sound proper
  refine ⟨f, R, inDomain, fun a ha => freeIn_sound (List.all_eq_true.mp covered a ha), ?_, ?_⟩
  · rw [← obs_renameW, mapped]
    exact obs_not_const g0 glt gb0
  · rw [← obs_renameW, mapped]
    exact bound

def lb0 : Nat := 0xffffff00ff000000ffffff00ff000000
def lb20 : List Nat := varsOf 56
def lb166 : List Nat := [24,24,40,40,48,48,24,40,48]
def lb150 : List Nat := [16,8,32,8,32,16,32,16,8]
def lb113 : Nat := fullMask 9
def lb46 : List Decor := [(0xff00ff00ff00ff00ff00ff00ff00ff00,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def lb215 : List (Nat × Nat × Nat) := []
def lb34 : Array Decor := buildWires lb46 lb215
def lb40 : Array (List (Nat × Nat)) := #[]
def lb206 : List (Nat × Nat) := []
def lb209 : Array (Nat × Nat) := lb206.toArray
def lb169 : List PoolSpec := []
def lb14 : Array (Option BoundPool) := buildPools lb34 lb20 lb209 lb169
lemma lb122 : goodPairs lb0 lb166 lb150 := goodPairs_of (by decide +kernel)
lemma lb47 : ∀ x ∈ lb46, faithful lb166 lb150 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb35 : ∀ x ∈ lb34.toList, faithful lb166 lb150 x ∧ x.1 < 2^128 := buildWires_faithful lb47
lemma lb41 : ∀ sw ∈ lb40.toList, swapsValid sw = true ∧ permWord sw lb0 = lb0 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma lb210 : ∀ i (hi : i < lb209.size), Slice lb20 lb0 lb209[i].1 lb209[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb20 lb0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb15 : ∀ i (hi : i < lb14.size), ∀ c, lb14[i] = some c → ValidPool lb20 lb0 c := buildPools_sound lb210
def lb58 : Array (List (List Nat)) := #[]
lemma lb59 : ∀ i (hi : i < lb58.size), ∀ xs ∈ lb58[i], Impossible lb0 (0 - 1) xs.toFinset := by intro i hi; simp [lb58] at hi
def lb153 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb92 : checkNodes lb34 lb0 lb113 lb14 lb40 lb58 0 lb153 = true := by decide +kernel
def lb52 : Array (List (List Nat)) := buildBuckets 1 lb34 lb153
lemma lb53 : ∀ i (hi : i < lb52.size), ∀ xs ∈ lb52[i], Impossible lb0 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb122 lb35 lb15 lb41 lb59 lb92
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb93 : checkNodes lb34 lb0 lb113 lb14 lb40 lb52 1 lb153 = true := by decide +kernel
lemma lb54 : ∀ i (hi : i < lb52.size), ∀ xs ∈ lb52[i], Impossible lb0 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb122 lb35 lb15 lb41 lb53 lb93
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb94 : checkNodes lb34 lb0 lb113 lb14 lb40 lb52 2 lb153 = true := by decide +kernel
lemma lb55 : ∀ i (hi : i < lb52.size), ∀ xs ∈ lb52[i], Impossible lb0 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb122 lb35 lb15 lb41 lb54 lb94
def lb154 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb95 : checkNodes lb34 lb0 lb113 lb14 lb40 lb52 3 lb154 = true := by decide +kernel
def lb56 : Array (List (List Nat)) := buildBuckets 1 lb34 lb154
lemma lb57 : ∀ i (hi : i < lb56.size), ∀ xs ∈ lb56[i], Impossible lb0 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb122 lb35 lb15 lb41 lb55 lb95
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb117 : forestRootCheck lb20 lb0 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb116 : bucketContains lb56 lb20 = true := by decide +kernel
lemma lb125 : Lower lb20 lb0 4 := lower_of_forest lb117 lb57 lb116
def lb12 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def lb32 : List Nat := varsOf 14
lemma lb147 : carryOK [(1,2),(1,5),(2,4),(1,3)] lb32 lb12 lb20 lb0 = true := by decide +kernel
lemma lb146 : Lower lb32 lb12 4 := carry_of lb147 lb125
def lb13 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def lb33 : List Nat := varsOf 38
lemma lb149 : carryOK [(2,4),(1,3)] lb33 lb13 lb20 lb0 = true := by decide +kernel
lemma lb148 : Lower lb33 lb13 4 := carry_of lb149 lb125
def lb1 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def lb21 : List Nat := varsOf 42
lemma lb127 : carryOK [(2,4),(1,2),(1,3)] lb21 lb1 lb20 lb0 = true := by decide +kernel
lemma lb126 : Lower lb21 lb1 4 := carry_of lb127 lb125
def lb2 : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def lb22 : List Nat := varsOf 28
lemma lb129 : carryOK [(2,5),(2,4),(2,3)] lb22 lb2 lb20 lb0 = true := by decide +kernel
lemma lb128 : Lower lb22 lb2 4 := carry_of lb129 lb125
def lb3 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def lb23 : List Nat := varsOf 44
lemma lb131 : carryOK [(2,4),(2,3)] lb23 lb3 lb20 lb0 = true := by decide +kernel
lemma lb130 : Lower lb23 lb3 4 := carry_of lb131 lb125
def lb4 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def lb24 : List Nat := varsOf 50
lemma lb133 : carryOK [(1,2),(1,3)] lb24 lb4 lb20 lb0 = true := by decide +kernel
lemma lb132 : Lower lb24 lb4 4 := carry_of lb133 lb125
def lb5 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def lb25 : List Nat := varsOf 52
lemma lb135 : carryOK [(2,3)] lb25 lb5 lb20 lb0 = true := by decide +kernel
lemma lb134 : Lower lb25 lb5 4 := carry_of lb135 lb125
def lb6 : Nat := 0xfff0f000f0000000fff0f000f0000000
def lb26 : List Nat := varsOf 60
def lb167 : List Nat := [28,28,28,44,44,44,52,52,52,56,56,56,28,28,28,44,44,44,52,52,52,56,56,56]
def lb151 : List Nat := [24,20,12,40,36,12,48,36,20,48,40,24,36,40,48,20,24,48,12,24,40,12,20,36]
def lb114 : Nat := fullMask 24
def lb48 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1ff1ff,0xe491b6),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def lb216 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def lb36 : Array Decor := buildWires lb48 lb216
def lb42 : Array (List (Nat × Nat)) := #[[],[(4,5)],[(2,3)],[(4,5),(2,3)],[(3,4)],[(3,5),(3,4)],[(2,3),(2,4)],[(3,5),(2,3),(2,4)],[(3,5),(2,4)]]
def lb207 : List (Nat × Nat) := [(subcube 0 16,4),(subcube 0 4,4),(subcube 0 8,4),(subcube 0 32,4)]
def lb211 : Array (Nat × Nat) := lb207.toArray
def lb170 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def lb16 : Array (Option BoundPool) := buildPools lb36 lb26 lb211 lb170
lemma lb123 : goodPairs lb6 lb167 lb151 := goodPairs_of (by decide +kernel)
lemma lb49 : ∀ x ∈ lb48, faithful lb167 lb151 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb37 : ∀ x ∈ lb36.toList, faithful lb167 lb151 x ∧ x.1 < 2^128 := buildWires_faithful lb49
lemma lb43 : ∀ sw ∈ lb42.toList, swapsValid sw = true ∧ permWord sw lb6 = lb6 := autos_of (by decide +kernel)
lemma lb173 : sliceDirectCheck 0 16 0 lb26 lb6 lb23 lb3 = true := by decide +kernel
lemma lb172 : Slice lb26 lb6 (subcube 0 16) 4 := slice_direct lb173 lb130
lemma lb175 : sliceDirectCheck 0 4 0 lb26 lb6 lb20 lb0 = true := by decide +kernel
lemma lb174 : Slice lb26 lb6 (subcube 0 4) 4 := slice_direct lb175 lb125
lemma lb177 : sliceDirectCheck 0 8 0 lb26 lb6 lb25 lb5 = true := by decide +kernel
lemma lb176 : Slice lb26 lb6 (subcube 0 8) 4 := slice_direct lb177 lb134
lemma lb179 : sliceDirectCheck 0 32 0 lb26 lb6 lb22 lb2 = true := by decide +kernel
lemma lb178 : Slice lb26 lb6 (subcube 0 32) 4 := slice_direct lb179 lb128
set_option maxRecDepth 200000 in
lemma lb212 : ∀ i (hi : i < lb211.size), Slice lb26 lb6 lb211[i].1 lb211[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb26 lb6 p.1 p.2) (forall_cons lb172 (forall_cons lb174 (forall_cons lb176 (forall_cons lb178 (fun _ h => (List.not_mem_nil h).elim)))))
lemma lb17 : ∀ i (hi : i < lb16.size), ∀ c, lb16[i] = some c → ValidPool lb26 lb6 c := buildPools_sound lb212
lemma lb72 : ∀ i (hi : i < lb58.size), ∀ xs ∈ lb58[i], Impossible lb6 (0 - 1) xs.toFinset := by intro i hi; simp [lb58] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb96 : checkNodes lb36 lb6 lb114 lb16 lb42 lb58 0 lb153 = true := by decide +kernel
def lb60 : Array (List (List Nat)) := buildBuckets 1 lb36 lb153
lemma lb61 : ∀ i (hi : i < lb60.size), ∀ xs ∈ lb60[i], Impossible lb6 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb123 lb37 lb17 lb43 lb72 lb96
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb97 : checkNodes lb36 lb6 lb114 lb16 lb42 lb60 1 lb153 = true := by decide +kernel
lemma lb62 : ∀ i (hi : i < lb60.size), ∀ xs ∈ lb60[i], Impossible lb6 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb123 lb37 lb17 lb43 lb61 lb97
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb98 : checkNodes lb36 lb6 lb114 lb16 lb42 lb60 2 lb153 = true := by decide +kernel
lemma lb63 : ∀ i (hi : i < lb60.size), ∀ xs ∈ lb60[i], Impossible lb6 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb123 lb37 lb17 lb43 lb62 lb98
def lb155 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb99 : checkNodes lb36 lb6 lb114 lb16 lb42 lb60 3 lb155 = true := by decide +kernel
def lb64 : Array (List (List Nat)) := buildBuckets 1 lb36 lb155
lemma lb65 : ∀ i (hi : i < lb64.size), ∀ xs ∈ lb64[i], Impossible lb6 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb123 lb37 lb17 lb43 lb63 lb99
def lb156 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb100 : checkNodes lb36 lb6 lb114 lb16 lb42 lb64 4 lb156 = true := by decide +kernel
def lb66 : Array (List (List Nat)) := buildBuckets 2 lb36 lb156
lemma lb67 : ∀ i (hi : i < lb66.size), ∀ xs ∈ lb66[i], Impossible lb6 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb123 lb37 lb17 lb43 lb65 lb100
def lb157 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb101 : checkNodes lb36 lb6 lb114 lb16 lb42 lb66 5 lb157 = true := by decide +kernel
def lb68 : Array (List (List Nat)) := buildBuckets 1 lb36 lb157
lemma lb69 : ∀ i (hi : i < lb68.size), ∀ xs ∈ lb68[i], Impossible lb6 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb123 lb37 lb17 lb43 lb67 lb101
def lb158 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb102 : checkNodes lb36 lb6 lb114 lb16 lb42 lb68 6 lb158 = true := by decide +kernel
def lb70 : Array (List (List Nat)) := buildBuckets 1 lb36 lb158
lemma lb71 : ∀ i (hi : i < lb70.size), ∀ xs ∈ lb70[i], Impossible lb6 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb123 lb37 lb17 lb43 lb69 lb102
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb119 : forestRootCheck lb26 lb6 [(VAR 2,28,24),(VAR 3,28,20),(VAR 4,28,12),(VAR 5,44,12)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb118 : bucketContains lb70 lb26 = true := by decide +kernel
lemma lb136 : Lower lb26 lb6 7 := lower_of_forest lb119 lb71 lb118
def lb7 : Nat := 0xfcc0c000fcc0c000fcc0c000fcc0c000
def lb27 : List Nat := varsOf 30
lemma lb138 : carryOK [(1,5),(1,4),(1,3),(1,2)] lb27 lb7 lb26 lb6 = true := by decide +kernel
lemma lb137 : Lower lb27 lb7 7 := carry_of lb138 lb136
def lb8 : Nat := 0xfcc0fcc0c000c000fcc0fcc0c000c000
def lb28 : List Nat := varsOf 46
lemma lb140 : carryOK [(1,4),(1,3),(1,2)] lb28 lb8 lb26 lb6 = true := by decide +kernel
lemma lb139 : Lower lb28 lb8 7 := carry_of lb140 lb136
def lb9 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
def lb29 : List Nat := varsOf 54
lemma lb142 : carryOK [(1,3),(1,2)] lb29 lb9 lb26 lb6 = true := by decide +kernel
lemma lb141 : Lower lb29 lb9 7 := carry_of lb142 lb136
def lb10 : Nat := 0xffcccc00cc000000ffcccc00cc000000
def lb30 : List Nat := varsOf 58
lemma lb144 : carryOK [(1,2)] lb30 lb10 lb26 lb6 = true := by decide +kernel
lemma lb143 : Lower lb30 lb10 7 := carry_of lb144 lb136
def lb11 : Nat := 0xfcc0c000c0000000fcc0c000c0000000
def lb31 : List Nat := varsOf 62
def lb168 : List Nat := [30,30,30,30,46,46,46,46,54,54,54,54,58,58,58,58,60,60,60,60,30,30,30,30,30,30,46,46,46,46,46,46,54,54,54,54,54,54,58,58,58,58,58,58,60,60,60,60,60,60]
def lb152 : List Nat := [28,26,22,14,44,42,38,14,52,50,38,22,56,50,42,26,56,52,44,28,38,42,44,50,52,56,22,26,28,50,52,56,14,26,28,42,44,56,14,22,28,38,44,52,14,22,26,38,42,50]
def lb115 : Nat := fullMask 50
def lb50 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xffffff0ffff,0x3f2cb2cb0eeee),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3f03fffff0fff,0xbfd5555e0ddd),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffc0fffff0ff,0x1557f9a6dd0bb),(0xffff0000ffff0000ffff0000ffff0000,0x3ffff03ffff0f,0x269a6ff8bbb07),(0xffffffff00000000ffffffff00000000,0x3fffffc0ffff0,0x38e38e3f77770)]
def lb217 : List (Nat × Nat × Nat) := [(0,0,1),(0,2,3),(0,0,2),(3,5,2),(0,5,2),(0,1,3),(0,3,4),(3,8,3),(2,5,6),(0,9,3),(0,1,2),(0,0,3),(3,9,3),(0,5,3),(3,13,0),(0,1,4),(0,2,4),(3,12,4),(3,16,4),(3,14,4),(0,0,4),(3,14,0),(0,12,4),(1,14,4),(2,2,11),(0,17,4),(0,14,4),(0,16,4),(3,17,4),(3,14,1),(3,31,0)]
def lb38 : Array Decor := buildWires lb50 lb217
def lb44 : Array (List (Nat × Nat)) := #[[],[(1,2)],[(1,3),(1,2)],[(1,2),(2,4),(1,5)],[(4,5)],[(1,5),(1,4),(1,3),(1,2)],[(3,5),(3,4)],[(3,5),(2,3),(2,4)],[(3,5),(1,2),(1,4)],[(2,3),(1,3),(2,5),(1,4)],[(2,3),(3,5),(2,4)],[(3,4),(3,5)],[(3,4)],[(3,4),(2,3),(2,5)],[(2,3),(2,4)],[(3,4),(2,3),(1,2),(1,5)],[(2,3),(1,2),(1,4)],[(3,5),(2,3),(1,2),(1,4)],[(3,5),(2,4)],[(2,5),(2,4),(2,3)],[(2,4)],[(2,3),(3,5),(1,2),(1,4)],[(2,3)],[(1,4),(1,3),(1,2)],[(2,4),(2,3)],[(4,5),(1,2),(1,3)],[(2,5),(1,4)],[(4,5),(1,2)],[(4,5),(2,3)],[(1,2),(1,4)],[(3,4),(1,2)],[(4,5),(1,3),(1,2)],[(2,5),(2,4)],[(3,5),(3,4),(1,2)],[(1,3),(1,4),(1,2)],[(3,5),(1,3),(1,4),(1,2)],[(2,4),(1,3)],[(1,2),(2,3),(1,4)],[(1,2),(1,3)],[(2,4),(1,2),(1,3)],[(2,3),(2,5),(1,4)],[(2,5),(2,4),(1,2),(1,3)],[(2,5),(2,4),(1,3)],[(1,2),(1,5),(2,4),(1,3)]]
def lb208 : List (Nat × Nat) := [(subcube 0 12,4),(subcube 0 6,4),(subcube 0 32,7),(subcube 0 48,4),(subcube 0 2,7),(subcube 0 24,4),(subcube 0 20,4),(subcube 0 10,4),(subcube 0 8,7),(subcube 0 16,7),(subcube 0 4,7),(subcube 0 34,4),(subcube 0 18,4)]
def lb213 : Array (Nat × Nat) := lb208.toArray
def lb171 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(2,[(0,0,1),(0,0,2),(0,1,2)]),(8,[(0,0,1),(0,0,3),(0,1,3)]),(9,[]),(4,[(0,5,2),(0,9,3),(3,14,4)]),(2,[(0,0,1),(0,5,2),(3,9,3)]),(4,[(0,5,2),(0,5,3),(0,2,3)]),(10,[]),(9,[(0,0,1),(0,0,2)]),(8,[(0,0,1),(0,1,3)]),(2,[(0,0,1),(3,5,2)]),(8,[(0,0,1),(3,8,3)]),(9,[(0,0,1),(3,5,2)]),(4,[(0,2,3),(2,5,6)]),(8,[]),(9,[(0,0,1),(0,5,2)]),(4,[(0,5,2),(0,2,3)]),(2,[(0,0,1),(0,5,2)]),(4,[(0,1,2)]),(9,[(0,0,1),(0,0,2),(0,1,2)]),(10,[(0,5,2),(0,0,3)]),(8,[(0,0,1),(0,0,3)]),(11,[]),(4,[(0,5,2),(0,9,3)]),(4,[(0,5,2),(3,9,3)]),(10,[(0,5,2),(3,9,3)]),(8,[(0,0,1),(3,9,3)]),(2,[(0,0,1),(0,0,2)]),(10,[(0,5,2),(0,9,3)]),(8,[(0,0,1),(0,9,3)]),(4,[(0,5,2),(0,5,3)]),(12,[]),(8,[(0,0,1)]),(9,[(0,0,1)]),(4,[(0,2,3)]),(10,[(0,2,3)]),(10,[(0,0,2)]),(4,[(0,5,2)]),(10,[(0,5,2)]),(2,[(0,0,1)])]
def lb18 : Array (Option BoundPool) := buildPools lb38 lb31 lb213 lb171
lemma lb124 : goodPairs lb11 lb168 lb152 := goodPairs_of (by decide +kernel)
lemma lb51 : ∀ x ∈ lb50, faithful lb168 lb152 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb39 : ∀ x ∈ lb38.toList, faithful lb168 lb152 x ∧ x.1 < 2^128 := buildWires_faithful lb51
lemma lb45 : ∀ sw ∈ lb44.toList, swapsValid sw = true ∧ permWord sw lb11 = lb11 := autos_of (by decide +kernel)
lemma lb181 : sliceDirectCheck 0 12 0 lb31 lb11 lb24 lb4 = true := by decide +kernel
lemma lb180 : Slice lb31 lb11 (subcube 0 12) 4 := slice_direct lb181 lb132
lemma lb189 : sliceDirectCheck 0 6 0 lb31 lb11 lb20 lb0 = true := by decide +kernel
lemma lb182 : Slice lb31 lb11 (subcube 0 6) 4 := slice_direct lb189 lb125
lemma lb191 : sliceDirectCheck 0 32 0 lb31 lb11 lb27 lb7 = true := by decide +kernel
lemma lb190 : Slice lb31 lb11 (subcube 0 32) 7 := slice_direct lb191 lb137
lemma lb193 : sliceDirectCheck 0 48 0 lb31 lb11 lb32 lb12 = true := by decide +kernel
lemma lb192 : Slice lb31 lb11 (subcube 0 48) 4 := slice_direct lb193 lb146
lemma lb195 : sliceDirectCheck 0 2 0 lb31 lb11 lb26 lb6 = true := by decide +kernel
lemma lb194 : Slice lb31 lb11 (subcube 0 2) 7 := slice_direct lb195 lb136
lemma lb197 : sliceDirectCheck 0 24 0 lb31 lb11 lb33 lb13 = true := by decide +kernel
lemma lb196 : Slice lb31 lb11 (subcube 0 24) 4 := slice_direct lb197 lb148
lemma lb199 : sliceDirectCheck 0 20 0 lb31 lb11 lb21 lb1 = true := by decide +kernel
lemma lb198 : Slice lb31 lb11 (subcube 0 20) 4 := slice_direct lb199 lb126
lemma lb201 : sliceDirectCheck 0 10 0 lb31 lb11 lb25 lb5 = true := by decide +kernel
lemma lb200 : Slice lb31 lb11 (subcube 0 10) 4 := slice_direct lb201 lb134
lemma lb203 : sliceDirectCheck 0 8 0 lb31 lb11 lb29 lb9 = true := by decide +kernel
lemma lb202 : Slice lb31 lb11 (subcube 0 8) 7 := slice_direct lb203 lb141
lemma lb205 : sliceDirectCheck 0 16 0 lb31 lb11 lb28 lb8 = true := by decide +kernel
lemma lb204 : Slice lb31 lb11 (subcube 0 16) 7 := slice_direct lb205 lb139
lemma lb184 : sliceDirectCheck 0 4 0 lb31 lb11 lb30 lb10 = true := by decide +kernel
lemma lb183 : Slice lb31 lb11 (subcube 0 4) 7 := slice_direct lb184 lb143
lemma lb186 : sliceDirectCheck 0 34 0 lb31 lb11 lb22 lb2 = true := by decide +kernel
lemma lb185 : Slice lb31 lb11 (subcube 0 34) 4 := slice_direct lb186 lb128
lemma lb188 : sliceDirectCheck 0 18 0 lb31 lb11 lb23 lb3 = true := by decide +kernel
lemma lb187 : Slice lb31 lb11 (subcube 0 18) 4 := slice_direct lb188 lb130
set_option maxRecDepth 200000 in
lemma lb214 : ∀ i (hi : i < lb213.size), Slice lb31 lb11 lb213[i].1 lb213[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb31 lb11 p.1 p.2) (forall_cons lb180 (forall_cons lb182 (forall_cons lb190 (forall_cons lb192 (forall_cons lb194 (forall_cons lb196 (forall_cons lb198 (forall_cons lb200 (forall_cons lb202 (forall_cons lb204 (forall_cons lb183 (forall_cons lb185 (forall_cons lb187 (fun _ h => (List.not_mem_nil h).elim))))))))))))))
lemma lb19 : ∀ i (hi : i < lb18.size), ∀ c, lb18[i] = some c → ValidPool lb31 lb11 c := buildPools_sound lb214
lemma lb91 : ∀ i (hi : i < lb58.size), ∀ xs ∈ lb58[i], Impossible lb11 (0 - 1) xs.toFinset := by intro i hi; simp [lb58] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb103 : checkNodes lb38 lb11 lb115 lb18 lb44 lb58 0 lb153 = true := by decide +kernel
def lb73 : Array (List (List Nat)) := buildBuckets 1 lb38 lb153
lemma lb74 : ∀ i (hi : i < lb73.size), ∀ xs ∈ lb73[i], Impossible lb11 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb124 lb39 lb19 lb45 lb91 lb103
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb104 : checkNodes lb38 lb11 lb115 lb18 lb44 lb73 1 lb153 = true := by decide +kernel
lemma lb75 : ∀ i (hi : i < lb73.size), ∀ xs ∈ lb73[i], Impossible lb11 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb124 lb39 lb19 lb45 lb74 lb104
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb105 : checkNodes lb38 lb11 lb115 lb18 lb44 lb73 2 lb153 = true := by decide +kernel
lemma lb76 : ∀ i (hi : i < lb73.size), ∀ xs ∈ lb73[i], Impossible lb11 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb124 lb39 lb19 lb45 lb75 lb105
def lb159 : List NodeSpec := [([29,8,16,20],[],[]),([29,12,25,1],[],[]),([9,32,10,21],[0],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb106 : checkNodes lb38 lb11 lb115 lb18 lb44 lb73 3 lb159 = true := by decide +kernel
def lb77 : Array (List (List Nat)) := buildBuckets 2 lb38 lb159
lemma lb78 : ∀ i (hi : i < lb77.size), ∀ xs ∈ lb77[i], Impossible lb11 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb124 lb39 lb19 lb45 lb76 lb106
def lb160 : List NodeSpec := [([8,16,20,2,11],[1],[0]),([23,8,10,2,4],[],[]),([29,12,0,1,4],[],[0,1]),([12,25,1,2,11],[2],[0]),([12,25,20,2,3],[],[]),([26,34,2,3,4],[],[]),([26,1,2,3,28],[],[]),([9,16,20,2,11],[3],[2]),([23,9,10,2,4],[],[]),([17,25,20,2,3],[],[]),([35,1,2,3,4],[],[]),([9,32,10,2,4],[0],[0]),([9,16,10,21,4],[],[0,1]),([5,7,10,21,11],[],[]),([29,8,16,1,4],[],[3,4,0]),([14,25,20,2,3],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb107 : checkNodes lb38 lb11 lb115 lb18 lb44 lb77 4 lb160 = true := by decide +kernel
def lb79 : Array (List (List Nat)) := buildBuckets 6 lb38 lb160
lemma lb80 : ∀ i (hi : i < lb79.size), ∀ xs ∈ lb79[i], Impossible lb11 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb124 lb39 lb19 lb45 lb78 lb107
def lb161 : List NodeSpec := [([5,19,1,2,3,4],[4],[]),([14,0,1,2,3,4],[2],[5]),([5,7,10,6,4],[5,1,6,7],[6,7,8,9]),([8,16,1,2,11,4],[1],[4,8,0]),([8,16,20,2,3,4],[],[10,8,0]),([5,7,15,11,3,4],[5,1,6,7,0,8],[11,12,6,13,14,7,15,16,17]),([8,16,10,2,4],[5,1,9],[4,18,8]),([5,7,10,21,3,4],[],[19,20,15,21,9,0]),([12,0,1,2,11,4],[2],[0,1]),([22,0,1,2,3,4],[],[]),([23,8,1,2,3,4],[],[0]),([9,16,10,2,4],[10,0,7,1,9],[4,0,1]),([9,5,16,10,2,4],[0,6,7,1],[]),([24,5,0,1,2,3],[11],[]),([9,5,16,1,6,4],[0,7,6,1],[]),([17,25,1,2,3,4],[2,12],[0,22]),([17,5,16,1,2,4],[10,7],[]),([26,5,1,2,3,4],[4],[]),([12,25,1,2,3,4],[2],[0]),([27,0,1,2,3,4],[],[2]),([24,0,1,2,3,4],[],[]),([14,0,1,2,3,28],[],[0,1,2,23,5]),([9,16,1,2,11,4],[3],[19,1,0,2,22]),([26,9,1,2,3,4],[4],[24]),([14,25,1,2,3,4],[2],[0,22,24]),([9,16,20,2,3,4],[],[4,1,22,25,0]),([26,14,1,2,3,4],[4],[0,22,24]),([29,8,0,1,3,4],[],[2,26,3,0,4,27]),([30,0,1,2,3,4],[12],[]),([17,9,16,1,2,4],[10,7,1],[]),([24,14,0,1,2,3],[2],[]),([9,18,0,1,6,4],[0,6,13],[]),([24,9,0,1,2,3],[],[]),([23,9,1,2,3,4],[],[0,22]),([24,0,1,2,3],[],[]),([31,0,1,2,3,4],[],[0,1,2,23,5]),([9,32,1,2,3,4],[0],[0,4,22,28]),([33,0,1,2,3,4],[12],[23])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb108 : checkNodes lb38 lb11 lb115 lb18 lb44 lb79 5 lb161 = true := by decide +kernel
def lb81 : Array (List (List Nat)) := buildBuckets 13 lb38 lb161
lemma lb82 : ∀ i (hi : i < lb81.size), ∀ xs ∈ lb81[i], Impossible lb11 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb124 lb39 lb19 lb45 lb80 lb108
def lb162 : List NodeSpec := [([5,7,10,2,3,4],[14,4,1,6,7,15,16],[6,20,14,7,16,29,8,0,30]),([8,0,1,2,11,3,4],[1,3,0,17],[0,4,18,8,1,27]),([12,0,1,2,3,4],[6,4,1,18,2,19],[0,1]),([13,5,0,1,2,3,4],[20],[0,1]),([9,5,0,1,6,3,4],[21,0,7,6,1,22,23],[0,1]),([14,9,0,1,2,3,4],[10,24,22],[0,1,2,23]),([9,0,1,2,11,3,4],[3,1,0,24],[0,23,5,4,1,27,2,31]),([5,7,15,3,4],[25,14,21,1,0,26,8,7],[12,6,14,7,16,17,0]),([9,16,1,2,3,4],[10,0,7,1,22,27,28],[0,4,22]),([17,9,0,1,2,3,4],[10,0,1,7,22],[23,0,1,2]),([14,5,0,1,2,3,4],[5,29,30],[0,1]),([17,5,0,1,2,3,4],[21,10,6,0,7,22,31],[23,0,1]),([8,16,1,2,3,4],[5,4,1,28,19],[4,18,0]),([17,0,1,2,3,4],[0,4,7,1,22,2,31,32,33,12],[23,0,1,2]),([5,7,1,2,11,3,4],[5,1,6,7,34],[11,24,19,13,20,32,0,8,30,33,9,34,35]),([14,0,1,2,3,4],[30,35,36,22,2],[0,1,2,23]),([9,5,16,1,2,3,4],[0,7,6,1],[0]),([9,18,0,1,2,3,4],[22,21,0,37],[23,2,0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb109 : checkNodes lb38 lb11 lb115 lb18 lb44 lb81 6 lb162 = true := by decide +kernel
def lb83 : Array (List (List Nat)) := buildBuckets 7 lb38 lb162
lemma lb84 : ∀ i (hi : i < lb83.size), ∀ xs ∈ lb83[i], Impossible lb11 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb124 lb39 lb19 lb45 lb82 lb109
def lb163 : List NodeSpec := [([5,0,1,6,2,3,4],[0,38,5,1,39,40,3,41,42,29],[0,36,2,23,12,6,14,22,24,16,37,38,39,33,9,40]),([5,7,1,2,3,4],[43,21,0,4,1,15,34,7,39],[12,6,14,7,0,4,22,28]),([8,0,1,2,3,4],[14,0,4,1,39,10,2,17,19],[0,4,1,27]),([9,5,0,1,2,3,4],[21,0,7,1,6,29,22,24,44,45,39],[0,4,1,27]),([9,0,1,2,3,4],[0,7,1,10,22,2,24,44,45,39],[0,4,1,27,2,31])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb110 : checkNodes lb38 lb11 lb115 lb18 lb44 lb83 7 lb163 = true := by decide +kernel
def lb85 : Array (List (List Nat)) := buildBuckets 2 lb38 lb163
lemma lb86 : ∀ i (hi : i < lb85.size), ∀ xs ∈ lb85[i], Impossible lb11 7 xs.toFinset :=
  buildBuckets_sound (by decide) lb124 lb39 lb19 lb45 lb84 lb110
def lb164 : List NodeSpec := [([5,0,1,2,3,4],[14,4,21,1,39,10,40,2,46],[0,12,6,1,30,33,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb111 : checkNodes lb38 lb11 lb115 lb18 lb44 lb85 8 lb164 = true := by decide +kernel
def lb87 : Array (List (List Nat)) := buildBuckets 1 lb38 lb164
lemma lb88 : ∀ i (hi : i < lb87.size), ∀ xs ∈ lb87[i], Impossible lb11 8 xs.toFinset :=
  buildBuckets_sound (by decide) lb124 lb39 lb19 lb45 lb86 lb111
def lb165 : List NodeSpec := [([0,1,2,3,4],[4,14,21,10,2],[0,22,24,19,38,39,41,36,42,43])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb112 : checkNodes lb38 lb11 lb115 lb18 lb44 lb87 9 lb165 = true := by decide +kernel
def lb89 : Array (List (List Nat)) := buildBuckets 1 lb38 lb165
lemma lb90 : ∀ i (hi : i < lb89.size), ∀ xs ∈ lb89[i], Impossible lb11 9 xs.toFinset :=
  buildBuckets_sound (by decide) lb124 lb39 lb19 lb45 lb88 lb112
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb121 : forestRootCheck lb31 lb11 [(VAR 1,30,28),(VAR 2,30,26),(VAR 3,30,22),(VAR 4,30,14),(VAR 5,46,14)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb120 : bucketContains lb89 lb31 = true := by decide +kernel
lemma lb145 : Lower lb31 lb11 10 := lower_of_forest lb121 lb90 lb120
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q1d : Lower (varsOf 109) 0xfaa0faa0a000a000a000a00000000000 10 := by
  apply carry_of (swaps := [(5, 6), (4, 5), (0, 1)]) (roots2 := lb31) (T2 := lb11) _ lb145
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q1 : Lower (varsOf 109) 0xfffffffffffafffafffafffafaa0faa0 10 := dualLower (by decide +kernel) (by decide +kernel) q1d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q0 : Lower (varsOf 111) 0xfffffffffffefffefffafffafaa0faa0 11 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,64,66)]) (by decide +kernel) q1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q3d : Lower (varsOf 117) 0xfafaa0a0a0a00000a0a0000000000000 10 := by
  apply carry_of (swaps := [(5, 6), (4, 5), (3, 4), (0, 1)]) (roots2 := lb31) (T2 := lb11) _ lb145
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q3 : Lower (varsOf 117) 0xfffffffffffffafafffffafafafaa0a0 10 := dualLower (by decide +kernel) (by decide +kernel) q3d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q2 : Lower (varsOf 119) 0xfffffffffffffefefffffafafefea0a0 11 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,16,18)]) (by decide +kernel) q3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q4 : Lower (varsOf 125) 0xfffffffffffffffafffffffafafafaa0 11 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,1,9)]) (by decide +kernel) q3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q6d : Lower (varsOf 31) 0xe8808000e8808000e8808000e8808000 10 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]) (roots2 := lb31) (T2 := lb11) _ lb145
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q6 : Lower (varsOf 31) 0xfffefee8fffefee8fffefee8fffefee8 10 := dualLower (by decide +kernel) (by decide +kernel) q6d
def s0NR : List Nat := varsOf 63
def s0NG : Nat := 0xfffefeeafffcfee8fffefeeafffcfee8
def s0NPos : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12,18,18,20,20,24,24,33,38,38,42,49,49,50]
def s0NNeg : List Nat := [1,2,1,4,2,4,1,8,2,8,4,8,2,16,4,16,8,16,1,34,36,34,17,48,34]
def s0NMask : Nat := fullMask 25
def s0NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc400cf,0x440045),(0xcccccccccccccccccccccccccccccccc,0x1383333,0x1281112),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x18cc3c,0x104428),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x230fc0,0x10a80),(0xffff0000ffff0000ffff0000ffff0000,0x1c3f000,0xc2a000),(0xffffffff00000000ffffffff00000000,0x1fc0000,0x1b80000)]
def s0NSteps : List (Nat × Nat × Nat) := []
def s0NW : BT Decor := buildWiresBT 3 s0NBase s0NSteps
def s0NAutoList : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,2),(2,3)],[(1,3),(2,3)],[(1,3)]]
def s0NAutos : BT (List (Nat × Nat)) := btOfList 3 s0NAutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NPairs : goodPairs s0NG s0NPos s0NNeg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBaseOk : ∀ x ∈ s0NBase, faithful s0NPos s0NNeg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NWOk : btAll (fun x => faithful s0NPos s0NNeg x ∧ x.1 < 2^128) s0NW := buildWiresBT_faithful s0NBaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NAutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw s0NG = s0NG) s0NAutos := btAll_ofList (autos_of (by decide +kernel))
def s0NSliceList : List (Option (Nat × Nat)) := [some (0xffff00000000ffffffff00000000ffff,10)]
def s0NSlices : BT (Option (Nat × Nat)) := btOfList 1 s0NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice0 : Slice s0NR s0NG 0xffff00000000ffffffff00000000ffff 10 := mappedSlice (f := identifyRow 0 0 4 5) (R := varsOf 31) (G := 0xfffefee8fffefee8fffefee8fffefee8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s0NR s0NG p.1 p.2) s0NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s0NR s0NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s0NSlice0) (fun _ h => (List.not_mem_nil h).elim))
def s0NEmpty : BT (List (List Nat)) := BT.empty
lemma s0NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG (9 - 1) xs.toFinset) s0NEmpty := trivial
def s0NBlock9_0Specs : List PoolSpec := [(0,[])]
def s0NBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 1 s0NW s0NR s0NSlices s0NBlock9_0Specs
def s0NBlock9_0 : List NodeSpec := [([0,1,2,3,4,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock9_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock9_0Pools s0NAutos s0NEmpty 9 s0NBlock9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock9_0Mem : ∀ ns ∈ s0NBlock9_0, Impossible s0NG 9 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NEmptyOk s0NBlock9_0Ok
def s0NNodes9 : List NodeSpec := s0NBlock9_0
def s0NBucket9 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 9 xs.toFinset) s0NBucket9 := buildBucketsBT_of_mem s0NBlock9_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBound : Lower s0NR s0NG 10 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,2,18),(VAR 5,1,33)]) (by decide +kernel) s0NBucket9Ok (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q5 : Lower (varsOf 63) 0xfffffffafefefaa0fffffffafefefaa0 10 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (2, 3), (1, 2)]) (roots2 := s0NR) (T2 := s0NG) _ s0NBound
  decide +kernel
def s1NR : List Nat := varsOf 63
def s1NG : Nat := 0xfffefeeefffafee8fffefeeefffafee8
def s1NPos : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12,17,17,20,20,24,24,33,33,34,44,44,50,50,52]
def s1NNeg : List Nat := [1,2,1,4,2,4,1,8,2,8,4,8,1,16,4,16,8,16,1,32,2,36,40,18,48,36]
def s1NMask : Nat := fullMask 26
def s1NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc30cf,0x41045),(0xcccccccccccccccccccccccccccccccc,0x1900333,0x900112),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x260cc3c,0x2204428),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x630fc0,0x410a80),(0xffff0000ffff0000ffff0000ffff0000,0x383f000,0x182a000),(0xffffffff00000000ffffffff00000000,0x3fc0000,0x3680000)]
def s1NSteps : List (Nat × Nat × Nat) := []
def s1NW : BT Decor := buildWiresBT 3 s1NBase s1NSteps
def s1NAutoList : List (List (Nat × Nat)) := [[],[(2,3)]]
def s1NAutos : BT (List (Nat × Nat)) := btOfList 1 s1NAutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NPairs : goodPairs s1NG s1NPos s1NNeg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBaseOk : ∀ x ∈ s1NBase, faithful s1NPos s1NNeg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NWOk : btAll (fun x => faithful s1NPos s1NNeg x ∧ x.1 < 2^128) s1NW := buildWiresBT_faithful s1NBaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NAutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw s1NG = s1NG) s1NAutos := btAll_ofList (autos_of (by decide +kernel))
def s1NSliceList : List (Option (Nat × Nat)) := [some (0xffff00000000ffffffff00000000ffff,10)]
def s1NSlices : BT (Option (Nat × Nat)) := btOfList 1 s1NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice0 : Slice s1NR s1NG 0xffff00000000ffffffff00000000ffff 10 := mappedSlice (f := identifyRow 0 0 4 5) (R := varsOf 31) (G := 0xfffefee8fffefee8fffefee8fffefee8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s1NR s1NG p.1 p.2) s1NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s1NR s1NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s1NSlice0) (fun _ h => (List.not_mem_nil h).elim))
def s1NEmpty : BT (List (List Nat)) := BT.empty
lemma s1NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG (9 - 1) xs.toFinset) s1NEmpty := trivial
def s1NBlock9_0Specs : List PoolSpec := [(0,[])]
def s1NBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock9_0Specs
def s1NBlock9_0 : List NodeSpec := [([0,1,2,3,4,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock9_0Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock9_0Pools s1NAutos s1NEmpty 9 s1NBlock9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock9_0Mem : ∀ ns ∈ s1NBlock9_0, Impossible s1NG 9 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NEmptyOk s1NBlock9_0Ok
def s1NNodes9 : List NodeSpec := s1NBlock9_0
def s1NBucket9 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 9 xs.toFinset) s1NBucket9 := buildBucketsBT_of_mem s1NBlock9_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBound : Lower s1NR s1NG 10 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) s1NBucket9Ok (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q7 : Lower (varsOf 95) 0xfffffffefffffffefefefaa0fefefaa0 10 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (0, 1), (1, 2), (2, 3), (3, 4), (2, 3), (1, 2)]) (roots2 := s1NR) (T2 := s1NG) _ s1NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q8 : Lower (varsOf 123) 0xffffffffffffffeeffffffaaeeeeaa00 10 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (1, 2), (2, 3)]) (roots2 := s1NR) (T2 := s1NG) _ s1NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q9 : Lower (varsOf 126) 0xfffffffffffffffcfffffff0fcfcf000 10 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := s1NR) (T2 := s1NG) _ s1NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q10d : Lower (varsOf 118) 0xfcfcc0c0c0c00000c0c0000000000000 10 := by
  apply carry_of (swaps := [(5, 6), (4, 5), (3, 4)]) (roots2 := lb31) (T2 := lb11) _ lb145
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q10 : Lower (varsOf 118) 0xfffffffffffffcfcfffffcfcfcfcc0c0 10 := dualLower (by decide +kernel) (by decide +kernel) q10d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q11d : Lower (varsOf 115) 0xeeee8888888800008888000000000000 10 := by
  apply carry_of (swaps := [(5, 6), (4, 5), (3, 4), (0, 1), (1, 2)]) (roots2 := lb31) (T2 := lb11) _ lb145
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q11 : Lower (varsOf 115) 0xffffffffffffeeeeffffeeeeeeee8888 10 := dualLower (by decide +kernel) (by decide +kernel) q11d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q12d : Lower (varsOf 87) 0xe8e88080e8e880808080000080800000 10 := by
  apply carry_of (swaps := [(5, 6), (0, 1), (1, 2), (2, 3)]) (roots2 := lb31) (T2 := lb11) _ lb145
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q12 : Lower (varsOf 87) 0xfffffefefffffefefefee8e8fefee8e8 10 := dualLower (by decide +kernel) (by decide +kernel) q12d
def lb218 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def lb224 : List Nat := varsOf 7
lemma lb258 : carryOK [(2,5),(1,4),(0,3)] lb224 lb218 lb20 lb0 = true := by decide +kernel
lemma lb257 : Lower lb224 lb218 4 := carry_of lb258 lb125
def lb220 : Nat := 0xeeeeeeee88888888eeeeeeee88888888
def lb226 : List Nat := varsOf 35
lemma lb261 : carryOK [(1,2),(0,2),(1,4),(0,3)] lb226 lb220 lb20 lb0 = true := by decide +kernel
lemma lb260 : Lower lb226 lb220 4 := carry_of lb261 lb125
def lb221 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def lb227 : List Nat := varsOf 37
lemma lb263 : carryOK [(2,4),(0,1),(0,3)] lb227 lb221 lb20 lb0 = true := by decide +kernel
lemma lb262 : Lower lb227 lb221 4 := carry_of lb263 lb125
def lb219 : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
def lb225 : List Nat := varsOf 39
def lb269 : List Nat := [3,3,5,5,6,6,33,33,34,34,36,36,3,3,5,5,6,6,33,33,34,34,36,36]
def lb264 : List Nat := [2,1,4,1,4,2,32,1,32,2,32,4,4,32,2,32,1,32,2,4,1,4,1,2]
def lb232 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def lb281 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def lb228 : Array Decor := buildWires lb232 lb281
def lb230 : Array (List (Nat × Nat)) := #[[],[(2,5)],[(0,1)],[(2,5),(0,1)],[(1,2)],[(1,5),(1,2)],[(0,1),(0,2)],[(1,5),(0,1),(0,2)],[(1,5),(0,2)]]
def lb278 : List (Nat × Nat) := [(subcube 2 0,4),(subcube 1 0,4),(subcube 32 0,4),(subcube 4 0,4)]
def lb279 : Array (Nat × Nat) := lb278.toArray
def lb222 : Array (Option BoundPool) := buildPools lb228 lb225 lb279 lb170
lemma lb256 : goodPairs lb219 lb269 lb264 := goodPairs_of (by decide +kernel)
lemma lb233 : ∀ x ∈ lb232, faithful lb269 lb264 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb229 : ∀ x ∈ lb228.toList, faithful lb269 lb264 x ∧ x.1 < 2^128 := buildWires_faithful lb233
lemma lb231 : ∀ sw ∈ lb230.toList, swapsValid sw = true ∧ permWord sw lb219 = lb219 := autos_of (by decide +kernel)
lemma lb271 : sliceDirectCheck 2 0 0 lb225 lb219 lb227 lb221 = true := by decide +kernel
lemma lb270 : Slice lb225 lb219 (subcube 2 0) 4 := slice_direct lb271 lb262
lemma lb273 : sliceDirectCheck 1 0 0 lb225 lb219 lb33 lb13 = true := by decide +kernel
lemma lb272 : Slice lb225 lb219 (subcube 1 0) 4 := slice_direct lb273 lb148
lemma lb275 : sliceDirectCheck 32 0 0 lb225 lb219 lb224 lb218 = true := by decide +kernel
lemma lb274 : Slice lb225 lb219 (subcube 32 0) 4 := slice_direct lb275 lb257
lemma lb277 : sliceDirectCheck 4 0 0 lb225 lb219 lb226 lb220 = true := by decide +kernel
lemma lb276 : Slice lb225 lb219 (subcube 4 0) 4 := slice_direct lb277 lb260
set_option maxRecDepth 200000 in
lemma lb280 : ∀ i (hi : i < lb279.size), Slice lb225 lb219 lb279[i].1 lb279[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb225 lb219 p.1 p.2) (forall_cons lb270 (forall_cons lb272 (forall_cons lb274 (forall_cons lb276 (fun _ h => (List.not_mem_nil h).elim)))))
lemma lb223 : ∀ i (hi : i < lb222.size), ∀ c, lb222[i] = some c → ValidPool lb225 lb219 c := buildPools_sound lb280
lemma lb246 : ∀ i (hi : i < lb58.size), ∀ xs ∈ lb58[i], Impossible lb219 (0 - 1) xs.toFinset := by intro i hi; simp [lb58] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb247 : checkNodes lb228 lb219 lb114 lb222 lb230 lb58 0 lb153 = true := by decide +kernel
def lb234 : Array (List (List Nat)) := buildBuckets 1 lb228 lb153
lemma lb235 : ∀ i (hi : i < lb234.size), ∀ xs ∈ lb234[i], Impossible lb219 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb256 lb229 lb223 lb231 lb246 lb247
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb248 : checkNodes lb228 lb219 lb114 lb222 lb230 lb234 1 lb153 = true := by decide +kernel
lemma lb236 : ∀ i (hi : i < lb234.size), ∀ xs ∈ lb234[i], Impossible lb219 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb256 lb229 lb223 lb231 lb235 lb248
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb249 : checkNodes lb228 lb219 lb114 lb222 lb230 lb234 2 lb153 = true := by decide +kernel
lemma lb237 : ∀ i (hi : i < lb234.size), ∀ xs ∈ lb234[i], Impossible lb219 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb256 lb229 lb223 lb231 lb236 lb249
def lb265 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb250 : checkNodes lb228 lb219 lb114 lb222 lb230 lb234 3 lb265 = true := by decide +kernel
def lb238 : Array (List (List Nat)) := buildBuckets 1 lb228 lb265
lemma lb239 : ∀ i (hi : i < lb238.size), ∀ xs ∈ lb238[i], Impossible lb219 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb256 lb229 lb223 lb231 lb237 lb250
def lb266 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb251 : checkNodes lb228 lb219 lb114 lb222 lb230 lb238 4 lb266 = true := by decide +kernel
def lb240 : Array (List (List Nat)) := buildBuckets 2 lb228 lb266
lemma lb241 : ∀ i (hi : i < lb240.size), ∀ xs ∈ lb240[i], Impossible lb219 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb256 lb229 lb223 lb231 lb239 lb251
def lb267 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb252 : checkNodes lb228 lb219 lb114 lb222 lb230 lb240 5 lb267 = true := by decide +kernel
def lb242 : Array (List (List Nat)) := buildBuckets 1 lb228 lb267
lemma lb243 : ∀ i (hi : i < lb242.size), ∀ xs ∈ lb242[i], Impossible lb219 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb256 lb229 lb223 lb231 lb241 lb252
def lb268 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb253 : checkNodes lb228 lb219 lb114 lb222 lb230 lb242 6 lb268 = true := by decide +kernel
def lb244 : Array (List (List Nat)) := buildBuckets 1 lb228 lb268
lemma lb245 : ∀ i (hi : i < lb244.size), ∀ xs ∈ lb244[i], Impossible lb219 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb256 lb229 lb223 lb231 lb243 lb253
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb255 : forestRootCheck lb225 lb219 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb254 : bucketContains lb244 lb225 = true := by decide +kernel
lemma lb259 : Lower lb225 lb219 7 := lower_of_forest lb255 lb245 lb254
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q14 : Lower (varsOf 45) 0xfffafffafaa0faa0fffafffafaa0faa0 7 := by
  apply carry_of (swaps := [(2, 3), (1, 2)]) (roots2 := lb225) (T2 := lb219) _ lb259
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q13 : Lower (varsOf 61) 0xfffffffafffffaa0fffffffafffffaa0 8 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,0,16)]) (by decide +kernel) q14
def lb324 : List Nat := [6,6,34,34,36,36,6,34,36]
def lb323 : List Nat := [4,2,32,2,32,4,32,4,2]
def lb290 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def lb287 : Array Decor := buildWires lb290 lb215
def lb283 : Array (Option BoundPool) := buildPools lb287 lb33 lb209 lb169
lemma lb312 : goodPairs lb13 lb324 lb323 := goodPairs_of (by decide +kernel)
lemma lb291 : ∀ x ∈ lb290, faithful lb324 lb323 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb288 : ∀ x ∈ lb287.toList, faithful lb324 lb323 x ∧ x.1 < 2^128 := buildWires_faithful lb291
lemma lb289 : ∀ sw ∈ lb40.toList, swapsValid sw = true ∧ permWord sw lb13 = lb13 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma lb329 : ∀ i (hi : i < lb209.size), Slice lb33 lb13 lb209[i].1 lb209[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb33 lb13 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb284 : ∀ i (hi : i < lb283.size), ∀ c, lb283[i] = some c → ValidPool lb33 lb13 c := buildPools_sound lb329
lemma lb298 : ∀ i (hi : i < lb58.size), ∀ xs ∈ lb58[i], Impossible lb13 (0 - 1) xs.toFinset := by intro i hi; simp [lb58] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb306 : checkNodes lb287 lb13 lb113 lb283 lb40 lb58 0 lb153 = true := by decide +kernel
def lb292 : Array (List (List Nat)) := buildBuckets 1 lb287 lb153
lemma lb293 : ∀ i (hi : i < lb292.size), ∀ xs ∈ lb292[i], Impossible lb13 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb312 lb288 lb284 lb289 lb298 lb306
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb307 : checkNodes lb287 lb13 lb113 lb283 lb40 lb292 1 lb153 = true := by decide +kernel
lemma lb294 : ∀ i (hi : i < lb292.size), ∀ xs ∈ lb292[i], Impossible lb13 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb312 lb288 lb284 lb289 lb293 lb307
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb308 : checkNodes lb287 lb13 lb113 lb283 lb40 lb292 2 lb153 = true := by decide +kernel
lemma lb295 : ∀ i (hi : i < lb292.size), ∀ xs ∈ lb292[i], Impossible lb13 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb312 lb288 lb284 lb289 lb294 lb308
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb309 : checkNodes lb287 lb13 lb113 lb283 lb40 lb292 3 lb154 = true := by decide +kernel
def lb296 : Array (List (List Nat)) := buildBuckets 1 lb287 lb154
lemma lb297 : ∀ i (hi : i < lb296.size), ∀ xs ∈ lb296[i], Impossible lb13 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb312 lb288 lb284 lb289 lb295 lb309
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb311 : forestRootCheck lb33 lb13 [(VAR 1,6,4),(VAR 2,6,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb310 : bucketContains lb296 lb33 = true := by decide +kernel
lemma lb313 : Lower lb33 lb13 4 := lower_of_forest lb311 lb297 lb310
lemma lb316 : carryOK [(3,4),(0,3),(0,5),(0,2),(0,1)] lb224 lb218 lb33 lb13 = true := by decide +kernel
lemma lb314 : Lower lb224 lb218 4 := carry_of lb316 lb313
lemma lb320 : carryOK [(0,2),(0,1)] lb226 lb220 lb33 lb13 = true := by decide +kernel
lemma lb319 : Lower lb226 lb220 4 := carry_of lb320 lb313
lemma lb322 : carryOK [(0,1)] lb227 lb221 lb33 lb13 = true := by decide +kernel
lemma lb321 : Lower lb227 lb221 4 := carry_of lb322 lb313
lemma lb325 : Slice lb225 lb219 (subcube 2 0) 4 := slice_direct lb271 lb321
lemma lb326 : Slice lb225 lb219 (subcube 1 0) 4 := slice_direct lb273 lb313
lemma lb327 : Slice lb225 lb219 (subcube 32 0) 4 := slice_direct lb275 lb314
lemma lb328 : Slice lb225 lb219 (subcube 4 0) 4 := slice_direct lb277 lb319
set_option maxRecDepth 200000 in
lemma lb330 : ∀ i (hi : i < lb279.size), Slice lb225 lb219 lb279[i].1 lb279[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb225 lb219 p.1 p.2) (forall_cons lb325 (forall_cons lb326 (forall_cons lb327 (forall_cons lb328 (fun _ h => (List.not_mem_nil h).elim)))))
lemma lb285 : ∀ i (hi : i < lb222.size), ∀ c, lb222[i] = some c → ValidPool lb225 lb219 c := buildPools_sound lb330
lemma lb299 : ∀ i (hi : i < lb234.size), ∀ xs ∈ lb234[i], Impossible lb219 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb256 lb229 lb285 lb231 lb246 lb247
lemma lb300 : ∀ i (hi : i < lb234.size), ∀ xs ∈ lb234[i], Impossible lb219 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb256 lb229 lb285 lb231 lb299 lb248
lemma lb301 : ∀ i (hi : i < lb234.size), ∀ xs ∈ lb234[i], Impossible lb219 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb256 lb229 lb285 lb231 lb300 lb249
lemma lb302 : ∀ i (hi : i < lb238.size), ∀ xs ∈ lb238[i], Impossible lb219 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb256 lb229 lb285 lb231 lb301 lb250
lemma lb303 : ∀ i (hi : i < lb240.size), ∀ xs ∈ lb240[i], Impossible lb219 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb256 lb229 lb285 lb231 lb302 lb251
lemma lb304 : ∀ i (hi : i < lb242.size), ∀ xs ∈ lb242[i], Impossible lb219 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb256 lb229 lb285 lb231 lb303 lb252
lemma lb305 : ∀ i (hi : i < lb244.size), ∀ xs ∈ lb244[i], Impossible lb219 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb256 lb229 lb285 lb231 lb304 lb253
lemma lb315 : Lower lb225 lb219 7 := lower_of_forest lb255 lb305 lb254
def lb282 : Nat := 0xfefefefefefee8e8fefefefefefee8e8
def lb286 : List Nat := varsOf 55
lemma lb318 : liftCheck 16 0 lb286 lb282 lb225 lb219 [(VAR 4,17,1)] = true := by decide +kernel
lemma lb317 : Lower lb286 lb282 8 := lift_of lb318 lb315
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q15 : Lower (varsOf 121) 0xffffffffffffffaaffffffaaaaaaaa00 8 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (4, 5), (3, 4), (2, 3)]) (roots2 := lb286) (T2 := lb282) _ lb317
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q16 : Lower (varsOf 124) 0xfffffffffffffff0fffffff0f0f0f000 8 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (4, 5), (3, 4), (2, 3), (0, 1), (1, 2)]) (roots2 := lb286) (T2 := lb282) _ lb317
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q17 : Lower (varsOf 108) 0xfffffffffff0fff0fff0fff0f000f000 7 := by
  apply carry_of (swaps := [(5, 6), (2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := lb225) (T2 := lb219) _ lb259
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q18 : Lower (varsOf 116) 0xfffffffffffff0f0fffff0f0f0f00000 7 := by
  apply carry_of (swaps := [(5, 6), (2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2)]) (roots2 := lb225) (T2 := lb219) _ lb259
  decide +kernel
def lb415 : List Nat := [6,6,10,10,12,12,6,10,12]
def lb408 : List Nat := [4,2,8,2,8,4,8,4,2]
def lb359 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1bc,0x54)]
def lb346 : BT Decor := buildWiresBT 2 lb359 lb215
def lb352 : List (List (Nat × Nat)) := []
def lb354 : BT (List (Nat × Nat)) := btOfList 1 lb352
def lb432 : List (Option (Nat × Nat)) := []
def lb434 : BT (Option (Nat × Nat)) := btOfList 1 lb432
def lb418 : BT (Option PoolSpec) := btOfList 1 []
lemma lb392 : goodPairs lb12 lb415 lb408 := goodPairs_of (by decide +kernel)
lemma lb360 : ∀ x ∈ lb359, faithful lb415 lb408 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb347 : btAll (fun x => faithful lb415 lb408 x ∧ x.1 < 2^128) lb346 := buildWiresBT_faithful lb360
set_option maxRecDepth 500000 in
lemma lb355 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb12 = lb12) lb354 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb435 : btAll (fun o => ∀ p, o = some p → Slice lb32 lb12 p.1 p.2) lb434 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb32 lb12 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
def lb368 : BT (List (List Nat)) := BT.empty
lemma lb365 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb12 2 xs.toFinset) lb368 := trivial
def lb337 : BT (Option BoundPool) := buildPoolsSubBT 1 lb346 lb32 lb434 lb418 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb379 : checkNodesBT lb346 lb12 lb113 lb337 lb354 lb368 3 lb154 = true := by decide +kernel
def lb366 : BT (List (List Nat)) := buildBucketsBT lb346 lb154
set_option maxRecDepth 500000 in
lemma lb367 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb12 3 xs.toFinset) lb366 :=
  buildBucketsBT_sound (by decide) lb392 lb347 (buildPoolsSubBT_sound lb435) lb355 lb365 lb379
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb387 : forestRootCheck lb32 lb12 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb386 : bucketContainsBT lb366 lb32 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb395 : Lower lb32 lb12 4 := lower_of_forestBT lb387 lb367 lb386
lemma lb400 : carryOK [(0,3),(0,2),(0,1)] lb224 lb218 lb32 lb12 = true := by decide +kernel
lemma lb396 : Lower lb224 lb218 4 := carry_of lb400 lb395
def lb333 : Nat := 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8
lemma lb402 : liftCheck 32 0 lb225 lb333 lb224 lb218 [(VAR 5,33,1)] = true := by decide +kernel
lemma lb401 : Lower lb225 lb333 5 := lift_of lb402 lb396
def lb334 : Nat := 0xfaaafaaaf0a0f0a0faaafaaaf0a0f0a0
def lb344 : List Nat := varsOf 45
def lb417 : List Nat := [5,5,12,12,13,33,33,37,41,41,44,44,5,5,5,12,12,12,33,33,33]
def lb410 : List Nat := [4,1,8,4,9,32,1,36,40,9,40,36,9,36,40,9,36,40,9,36,40]
def lb385 : Nat := fullMask 21
def lb363 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1c73f3,0x49252),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3fc9f,0x92889),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x38f1c,0x16d714),(0xffffffff00000000ffffffff00000000,0x1c0fe0,0x1b6da0)]
def lb350 : BT Decor := buildWiresBT 2 lb363 lb215
lemma lb394 : goodPairs lb334 lb417 lb410 := goodPairs_of (by decide +kernel)
lemma lb364 : ∀ x ∈ lb363, faithful lb417 lb410 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb351 : btAll (fun x => faithful lb417 lb410 x ∧ x.1 < 2^128) lb350 := buildWiresBT_faithful lb364
set_option maxRecDepth 500000 in
lemma lb358 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb334 = lb334) lb354 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb438 : btAll (fun o => ∀ p, o = some p → Slice lb344 lb334 p.1 p.2) lb434 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb344 lb334 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb376 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb334 2 xs.toFinset) lb368 := trivial
def lb414 : List NodeSpec := [([0,1,2,3],[],[])]
def lb341 : BT (Option BoundPool) := buildPoolsSubBT 1 lb350 lb344 lb434 lb418 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb383 : checkNodesBT lb350 lb334 lb385 lb341 lb354 lb368 3 lb414 = true := by decide +kernel
def lb377 : BT (List (List Nat)) := buildBucketsBT lb350 lb414
set_option maxRecDepth 500000 in
lemma lb378 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb334 3 xs.toFinset) lb377 :=
  buildBucketsBT_sound (by decide) lb394 lb351 (buildPoolsSubBT_sound lb438) lb358 lb376 lb383
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb391 : forestRootCheck lb344 lb334 [(VAR 0,5,4),(VAR 2,5,1),(VAR 3,12,4),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb390 : bucketContainsBT lb377 lb344 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb403 : Lower lb344 lb334 4 := lower_of_forestBT lb391 lb378 lb390
def lb335 : Nat := 0xfce8fce8fce8fce8fce8fce8fce8fce8
def lb345 : List Nat := varsOf 15
lemma lb405 : liftCheck 1 0 lb345 lb335 lb32 lb12 [(VAR 0,3,2)] = true := by decide +kernel
lemma lb404 : Lower lb345 lb335 5 := lift_of lb405 lb395
def lb336 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
lemma lb407 : liftCheck 1 0 lb345 lb336 lb32 lb12 [(VAR 0,1,0)] = true := by decide +kernel
lemma lb406 : Lower lb345 lb336 5 := lift_of lb407 lb395
def lb331 : Nat := 0xeeaaeeaacc88cc88eeaaeeaacc88cc88
def lb342 : List Nat := varsOf 43
lemma lb398 : carryOK [(1,2)] lb342 lb331 lb344 lb334 = true := by decide +kernel
lemma lb397 : Lower lb342 lb331 4 := carry_of lb398 lb403
def lb332 : Nat := 0xfeeafeeafce8fce8feeafeeafce8fce8
def lb343 : List Nat := varsOf 47
def lb416 : List Nat := [3,3,5,5,6,6,10,10,11,12,12,13,33,33,35,37,38,38,41,41,42,42,44,44,3,3,3,3,5,5,5,5,6,6,6,6,10,10,10,10,12,12,12,12,33,33,33,33]
def lb409 : List Nat := [2,1,4,1,4,2,8,2,9,8,4,9,32,1,34,36,36,34,40,9,40,34,40,36,9,34,36,40,9,34,36,40,9,34,36,40,9,34,36,40,9,34,36,40,9,34,36,40]
def lb384 : Nat := fullMask 48
def lb361 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf000ff0cf90f,0x11111108290a),(0xcccccccccccccccccccccccccccccccc,0xff0f3341f3,0x2222222240a1),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0ff0c38e3c,0x444444818414),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xff000fc0fc0,0x9999995c0b40),(0xffffffff00000000ffffffff00000000,0xf00000fff000,0xeeeeeef7d000)]
def lb439 : List (Nat × Nat × Nat) := [(1,1,2),(2,5,3)]
def lb348 : BT Decor := buildWiresBT 3 lb361 lb439
def lb353 : List (List (Nat × Nat)) := [[]]
def lb356 : BT (List (Nat × Nat)) := btOfList 1 lb353
def lb433 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,4),some (subcubeFast 8 0,5),some (subcubeFast 0 32,5),some (subcubeFast 32 0,5),some (subcubeFast 1 32,4),some (subcubeFast 4 0,4)]
def lb436 : BT (Option (Nat × Nat)) := btOfList 3 lb433
def lb419 : BT (Option PoolSpec) := btOfList 3 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (5,[])]
lemma lb393 : goodPairs lb332 lb416 lb409 := goodPairs_of (by decide +kernel)
lemma lb362 : ∀ x ∈ lb361, faithful lb416 lb409 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb349 : btAll (fun x => faithful lb416 lb409 x ∧ x.1 < 2^128) lb348 := buildWiresBT_faithful lb362
set_option maxRecDepth 500000 in
lemma lb357 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb332 = lb332) lb356 := btAll_ofList (autos_of (by decide +kernel))
lemma lb421 : sliceDirectCheck 2 0 0 lb343 lb332 lb344 lb334 = true := by decide +kernel
lemma lb420 : Slice lb343 lb332 (subcubeFast 2 0) 4 := slice_fast_direct lb421 lb403
lemma lb423 : sliceDirectCheck 8 0 0 lb343 lb332 lb225 lb333 = true := by decide +kernel
lemma lb422 : Slice lb343 lb332 (subcubeFast 8 0) 5 := slice_fast_direct lb423 lb401
lemma lb425 : sliceDirectCheck 0 32 0 lb343 lb332 lb345 lb336 = true := by decide +kernel
lemma lb424 : Slice lb343 lb332 (subcubeFast 0 32) 5 := slice_fast_direct lb425 lb406
lemma lb427 : sliceDirectCheck 32 0 0 lb343 lb332 lb345 lb335 = true := by decide +kernel
lemma lb426 : Slice lb343 lb332 (subcubeFast 32 0) 5 := slice_fast_direct lb427 lb404
lemma lb429 : sliceDirectCheck 1 32 0 lb343 lb332 lb32 lb12 = true := by decide +kernel
lemma lb428 : Slice lb343 lb332 (subcubeFast 1 32) 4 := slice_fast_direct lb429 lb395
lemma lb431 : sliceDirectCheck 4 0 0 lb343 lb332 lb342 lb331 = true := by decide +kernel
lemma lb430 : Slice lb343 lb332 (subcubeFast 4 0) 4 := slice_fast_direct lb431 lb397
set_option maxRecDepth 500000 in
lemma lb437 : btAll (fun o => ∀ p, o = some p → Slice lb343 lb332 p.1 p.2) lb436 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb343 lb332 p.1 p.2) (forall_cons (fun _ h => by cases h; exact lb420) (forall_cons (fun _ h => by cases h; exact lb422) (forall_cons (fun _ h => by cases h; exact lb424) (forall_cons (fun _ h => by cases h; exact lb426) (forall_cons (fun _ h => by cases h; exact lb428) (forall_cons (fun _ h => by cases h; exact lb430) (fun _ h => (List.not_mem_nil h).elim)))))))
lemma lb369 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb332 3 xs.toFinset) lb368 := trivial
def lb411 : List NodeSpec := [([6,0,1,2,4],[],[])]
def lb338 : BT (Option BoundPool) := buildPoolsSubBT 3 lb348 lb343 lb436 lb419 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb380 : checkNodesBT lb348 lb332 lb384 lb338 lb356 lb368 4 lb411 = true := by decide +kernel
def lb370 : BT (List (List Nat)) := buildBucketsBT lb348 lb411
set_option maxRecDepth 500000 in
lemma lb371 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb332 4 xs.toFinset) lb370 :=
  buildBucketsBT_sound (by decide) lb393 lb349 (buildPoolsSubBT_sound lb437) lb357 lb369 lb380
def lb412 : List NodeSpec := [([0,1,2,5,3,4],[0,1,2,3],[0])]
def lb339 : BT (Option BoundPool) := buildPoolsSubBT 3 lb348 lb343 lb436 lb419 [0,1,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb381 : checkNodesBT lb348 lb332 lb384 lb339 lb356 lb370 5 lb412 = true := by decide +kernel
def lb372 : BT (List (List Nat)) := buildBucketsBT lb348 lb412
set_option maxRecDepth 500000 in
lemma lb373 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb332 5 xs.toFinset) lb372 :=
  buildBucketsBT_sound (by decide) lb393 lb349 (buildPoolsSubBT_sound lb437) lb357 lb371 lb381
def lb413 : List NodeSpec := [([0,1,2,3,4],[4,1,3,0,5],[0])]
def lb340 : BT (Option BoundPool) := buildPoolsSubBT 3 lb348 lb343 lb436 lb419 [0,1,3,4,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb382 : checkNodesBT lb348 lb332 lb384 lb340 lb356 lb372 6 lb413 = true := by decide +kernel
def lb374 : BT (List (List Nat)) := buildBucketsBT lb348 lb413
set_option maxRecDepth 500000 in
lemma lb375 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb332 6 xs.toFinset) lb374 :=
  buildBucketsBT_sound (by decide) lb393 lb349 (buildPoolsSubBT_sound lb437) lb357 lb373 lb382
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb389 : forestRootCheck lb343 lb332 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 3,10,2),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb388 : bucketContainsBT lb374 lb343 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb399 : Lower lb343 lb332 7 := lower_of_forestBT lb389 lb375 lb388
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q19 : Lower (varsOf 31) 0xfefefaa0fefefaa0fefefaa0fefefaa0 7 := by
  apply carry_of (swaps := [(4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (2, 3), (1, 2)]) (roots2 := lb343) (T2 := lb332) _ lb399
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q20 : Lower (varsOf 59) 0xffffffaaeeeeaa00ffffffaaeeeeaa00 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (1, 2), (2, 3), (1, 2)]) (roots2 := lb343) (T2 := lb332) _ lb399
  decide +kernel
def lb511 (entries : List (List Nat × List Nat)) : List NodeSpec :=
  entries.map (fun entry => (entry.1, entry.2, [0]))

def lb464 : List Nat := varsOf 21
def lb456 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def lb463 : List Nat := [17,20,5,5,20,17]
def lb458 : List Nat := [16,16,1,4,4,1]
def lb457 : Nat := fullMask 6
def lb448 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def lb467 : BT Decor := buildWiresBT 2 lb448 lb215
def lb445 : List (List (Nat × Nat)) := [[],[(2,4)],[(0,2)],[(0,4)],[(2,4),(0,2)],[(2,4),(0,4)]]
def lb446 : BT (List (Nat × Nat)) := btOfList 3 lb445
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb460 : goodPairs lb456 lb463 lb458 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb449 : ∀ x ∈ lb448, faithful lb463 lb458 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb468 : btAll (fun x => faithful lb463 lb458 x ∧ x.1 < 2^128) lb467 := buildWiresBT_faithful lb449
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb447 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb456 = lb456) lb446 := btAll_ofList (autos_of (by decide +kernel))
def lb461 : BT (Option BoundPool) := buildPoolsBT 1 lb467 lb464 lb434 lb169
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb465 : btAll (fun o => ∀ p, o = some p → Slice lb464 lb456 p.1 p.2) lb434 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb464 lb456 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb462 : btAll (fun o => ∀ c, o = some c → ValidPool lb464 lb456 c) lb461 := buildPoolsBT_sound lb465
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb455 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb456 (3 - 1) xs.toFinset) lb368 := trivial
def lb450 : List NodeSpec := lb511 [([0,1,2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb466 : checkNodesBT lb467 lb456 lb457 lb461 lb446 lb368 3 lb450 = true := by decide +kernel
def lb459 : List NodeSpec := lb450
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb454 : checkNodesBT lb467 lb456 lb457 lb461 lb446 lb368 3 lb459 = true := lb466
def lb452 : BT (List (List Nat)) := buildBucketsBT lb467 lb459
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb453 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb456 3 xs.toFinset) lb452 := buildBucketsBT_sound (by decide) lb460 lb468 lb462 lb447 lb455 lb454
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb451 : Lower lb464 lb456 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 4,1,17)]) (by decide +kernel) lb453 (by decide +kernel)
def lb442 : List Nat := varsOf 13
def lb441 : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb440 : Lower lb442 lb441 4 := carry_of (swaps := [(3,4)]) (roots2 := lb464) (T2 := lb456) (by decide +kernel) lb451
def lb444 : Nat := 0xfae8fae8fae8fae8fae8fae8fae8fae8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb443 : Lower lb345 lb444 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,1,3)]) (by decide +kernel) lb440
def lb471 : List Nat := varsOf 19
def lb470 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb469 : Lower lb471 lb470 4 := carry_of (swaps := [(1,2)]) (roots2 := lb464) (T2 := lb456) (by decide +kernel) lb451
def lb474 : List Nat := varsOf 27
def lb473 : Nat := 0xeeeeaa88eeeeaa88eeeeaa88eeeeaa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb472 : Lower lb474 lb473 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,1,9)]) (by decide +kernel) lb469
def lb477 : List Nat := varsOf 29
def lb476 : Nat := 0xfaaafaa0faaafaa0faaafaa0faaafaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb475 : Lower lb477 lb476 5 := carry_of (swaps := [(3,4),(1,2)]) (roots2 := lb474) (T2 := lb473) (by decide +kernel) lb472
def lb510 : List Nat := varsOf 23
def lb509 : Nat := 0xeeeee8e8eeeee8e8eeeee8e8eeeee8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb508 : Lower lb510 lb509 5 := carry_of (swaps := [(3,4),(1,2)]) (roots2 := lb345) (T2 := lb444) (by decide +kernel) lb443
def lb497 : List Nat := varsOf 31
def lb489 : Nat := 0xfeeefae8feeefae8feeefae8feeefae8
def lb496 : List Nat := [5,6,3,3,6,5,12,9,9,18,17,17,26,12,28,26,28]
def lb491 : List Nat := [4,4,1,2,2,1,4,1,8,2,1,16,24,8,24,10,20]
def lb490 : Nat := fullMask 17
def lb481 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,3501,1188),(0xcccccccccccccccccccccccccccccccc,0x921e,0x8218),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x16073,0x10043),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f1c0,0xf100),(0xffff0000ffff0000ffff0000ffff0000,0x1de00,0x15800)]
def lb506 : BT Decor := buildWiresBT 3 lb481 lb215
def lb478 : List (List (Nat × Nat)) := [[],[(3,4),(1,2)]]
def lb479 : BT (List (Nat × Nat)) := btOfList 1 lb478
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb493 : goodPairs lb489 lb496 lb491 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb482 : ∀ x ∈ lb481, faithful lb496 lb491 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb507 : btAll (fun x => faithful lb496 lb491 x ∧ x.1 < 2^128) lb506 := buildWiresBT_faithful lb482
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb480 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb489 = lb489) lb479 := btAll_ofList (autos_of (by decide +kernel))
def lb502 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5)]
def lb503 : BT (Option (Nat × Nat)) := btOfList 2 lb502
def lb494 : BT (Option BoundPool) := buildPoolsBT 2 lb506 lb497 lb503 lb170
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb501 : Slice lb497 lb489 (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) lb443
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb500 : Slice lb497 lb489 (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) lb508
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb499 : Slice lb497 lb489 (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) lb472
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb498 : Slice lb497 lb489 (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) lb475
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb504 : btAll (fun o => ∀ p, o = some p → Slice lb497 lb489 p.1 p.2) lb503 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb497 lb489 p.1 p.2) (forall_cons (fun _ h => by cases h; exact lb498) (forall_cons (fun _ h => by cases h; exact lb499) (forall_cons (fun _ h => by cases h; exact lb500) (forall_cons (fun _ h => by cases h; exact lb501) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb495 : btAll (fun o => ∀ c, o = some c → ValidPool lb497 lb489 c) lb494 := buildPoolsBT_sound lb504
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb488 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb489 (6 - 1) xs.toFinset) lb368 := trivial
def lb483 : List NodeSpec := lb511 [([0,1,2,3,4],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb505 : checkNodesBT lb506 lb489 lb490 lb494 lb479 lb368 6 lb483 = true := by decide +kernel
def lb492 : List NodeSpec := lb483
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb487 : checkNodesBT lb506 lb489 lb490 lb494 lb479 lb368 6 lb492 = true := lb505
def lb485 : BT (List (List Nat)) := buildBucketsBT lb506 lb492
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb486 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb489 6 xs.toFinset) lb485 := buildBucketsBT_sound (by decide) lb493 lb507 lb495 lb480 lb488 lb487
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb484 : Lower lb497 lb489 7 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) lb486 (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q21 : Lower (varsOf 91) 0xffffffeeffffffeeeeeeaa00eeeeaa00 7 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (2, 3)]) (roots2 := lb497) (T2 := lb489) _ lb484
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q22 : Lower (varsOf 62) 0xfffffff0fcfcf000fffffff0fcfcf000 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := lb343) (T2 := lb332) _ lb399
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q23 : Lower (varsOf 94) 0xfffffffcfffffffcfcfcf000fcfcf000 7 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := lb497) (T2 := lb489) _ lb484
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q24 : Lower (varsOf 122) 0xffffffffffffffccffffff00cccc0000 7 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3), (0, 1)]) (roots2 := lb497) (T2 := lb489) _ lb484
  decide +kernel
def lb530 : List Nat := [12,12,20,20,24,24,12,20,24]
def lb529 : List Nat := [8,4,16,4,16,8,16,8,4]
def lb517 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def lb514 : BT Decor := buildWiresBT 2 lb517 lb215
lemma lb525 : goodPairs lb2 lb530 lb529 := goodPairs_of (by decide +kernel)
lemma lb518 : ∀ x ∈ lb517, faithful lb530 lb529 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb515 : btAll (fun x => faithful lb530 lb529 x ∧ x.1 < 2^128) lb514 := buildWiresBT_faithful lb518
set_option maxRecDepth 500000 in
lemma lb516 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb2 = lb2) lb354 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb531 : btAll (fun o => ∀ p, o = some p → Slice lb22 lb2 p.1 p.2) lb434 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb22 lb2 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb519 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb2 2 xs.toFinset) lb368 := trivial
def lb513 : BT (Option BoundPool) := buildPoolsSubBT 1 lb514 lb22 lb434 lb418 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb522 : checkNodesBT lb514 lb2 lb113 lb513 lb354 lb368 3 lb154 = true := by decide +kernel
def lb520 : BT (List (List Nat)) := buildBucketsBT lb514 lb154
set_option maxRecDepth 500000 in
lemma lb521 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb2 3 xs.toFinset) lb520 :=
  buildBucketsBT_sound (by decide) lb525 lb515 (buildPoolsSubBT_sound lb531) lb516 lb519 lb522
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb524 : forestRootCheck lb22 lb2 [(VAR 2,12,8),(VAR 3,12,4),(VAR 4,20,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb523 : bucketContainsBT lb520 lb22 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb526 : Lower lb22 lb2 4 := lower_of_forestBT lb524 lb521 lb523
def lb512 : Nat := 0xfffffffffff0f000fffffffffff0f000
lemma lb528 : liftCheck 32 0 lb26 lb512 lb22 lb2 [(VAR 5,32,0)] = true := by decide +kernel
lemma lb527 : Lower lb26 lb512 5 := lift_of lb528 lb526
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q25 : Lower (varsOf 29) 0xfffffaa0fffffaa0fffffaa0fffffaa0 5 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (0, 1)]) (roots2 := lb26) (T2 := lb512) _ lb527
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q26 : Lower (varsOf 60) 0xfffffff0fffff000fffffff0fffff000 5 := by
  apply carry_of (swaps := [(4, 5)]) (roots2 := lb26) (T2 := lb512) _ lb527
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q27 : Lower (varsOf 120) 0xffffffffffffff00ffffff0000000000 5 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3)]) (roots2 := lb345) (T2 := lb335) _ lb404
  decide +kernel
def lb546 : List Nat := [5,6,3,3,6,5]
def lb541 : List Nat := [4,4,1,2,2,1]
def lb533 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,51,3)]
def lb549 : BT Decor := buildWiresBT 2 lb533 lb215
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb543 : goodPairs lb218 lb546 lb541 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb534 : ∀ x ∈ lb533, faithful lb546 lb541 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb550 : btAll (fun x => faithful lb546 lb541 x ∧ x.1 < 2^128) lb549 := buildWiresBT_faithful lb534
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb532 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb218 = lb218) lb356 := btAll_ofList (autos_of (by decide +kernel))
def lb544 : BT (Option BoundPool) := buildPoolsBT 1 lb549 lb224 lb434 lb169
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb547 : btAll (fun o => ∀ p, o = some p → Slice lb224 lb218 p.1 p.2) lb434 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb224 lb218 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb545 : btAll (fun o => ∀ c, o = some c → ValidPool lb224 lb218 c) lb544 := buildPoolsBT_sound lb547
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb540 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb218 (3 - 1) xs.toFinset) lb368 := trivial
def lb535 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb548 : checkNodesBT lb549 lb218 lb457 lb544 lb356 lb368 3 lb535 = true := by decide +kernel
def lb542 : List NodeSpec := lb535
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb539 : checkNodesBT lb549 lb218 lb457 lb544 lb356 lb368 3 lb542 = true := lb548
def lb537 : BT (List (List Nat)) := buildBucketsBT lb549 lb542
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb538 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb218 3 xs.toFinset) lb537 := buildBucketsBT_sound (by decide) lb543 lb550 lb545 lb532 lb540 lb539
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb536 : Lower lb224 lb218 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)]) (by decide +kernel) lb538 (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q28 : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0 4 := by
  apply carry_of (swaps := [(2, 3), (1, 2)]) (roots2 := lb224) (T2 := lb218) _ lb536
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q29 : Lower (varsOf 41) 0xffaaffaaaa00aa00ffaaffaaaa00aa00 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3)]) (roots2 := lb224) (T2 := lb218) _ lb536
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q30 : Lower (varsOf 82) 0xffffccccffffcccccccc0000cccc0000 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (0, 1)]) (roots2 := lb224) (T2 := lb218) _ lb536
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q31 : Lower (varsOf 44) 0xfff0fff0f000f000fff0fff0f000f000 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := lb224) (T2 := lb218) _ lb536
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q32 : Lower (varsOf 76) 0xfff0fff0fff0fff0f000f000f000f000 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := lb224) (T2 := lb218) _ lb536
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q33 : Lower (varsOf 52) 0xfffff0f0f0f00000fffff0f0f0f00000 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2)]) (roots2 := lb224) (T2 := lb218) _ lb536
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q34 : Lower (varsOf 84) 0xfffff0f0fffff0f0f0f00000f0f00000 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2)]) (roots2 := lb224) (T2 := lb218) _ lb536
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q35 : Lower (varsOf 104) 0xffffffffff00ff00ff00ff0000000000 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3)]) (roots2 := lb224) (T2 := lb218) _ lb536
  decide +kernel
def lb562 : Nat := 0xeea0eea0eea0eea0eea0eea0eea0eea0
def lb569 : List Nat := [5,7,9,5,7,9,10,14]
def lb564 : List Nat := [4,6,8,1,3,1,2,6]
def lb563 : Nat := fullMask 8
def lb554 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,63,56),(0xcccccccccccccccccccccccccccccccc,210,210),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,155,131),(0xff00ff00ff00ff00ff00ff00ff00ff00,228,4)]
def lb572 : BT Decor := buildWiresBT 2 lb554 lb215
def lb551 : List (List (Nat × Nat)) := [[],[(1,2),(0,3)]]
def lb552 : BT (List (Nat × Nat)) := btOfList 1 lb551
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb566 : goodPairs lb562 lb569 lb564 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb555 : ∀ x ∈ lb554, faithful lb569 lb564 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb573 : btAll (fun x => faithful lb569 lb564 x ∧ x.1 < 2^128) lb572 := buildWiresBT_faithful lb555
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb553 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb562 = lb562) lb552 := btAll_ofList (autos_of (by decide +kernel))
def lb567 : BT (Option BoundPool) := buildPoolsBT 1 lb572 lb345 lb434 lb169
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb570 : btAll (fun o => ∀ p, o = some p → Slice lb345 lb562 p.1 p.2) lb434 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb345 lb562 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb568 : btAll (fun o => ∀ c, o = some c → ValidPool lb345 lb562 c) lb567 := buildPoolsBT_sound lb570
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb561 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb562 (3 - 1) xs.toFinset) lb368 := trivial
def lb556 : List NodeSpec := lb511 [([0,1,2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb571 : checkNodesBT lb572 lb562 lb563 lb567 lb552 lb368 3 lb556 = true := by decide +kernel
def lb565 : List NodeSpec := lb556
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb560 : checkNodesBT lb572 lb562 lb563 lb567 lb552 lb368 3 lb565 = true := lb571
def lb558 : BT (List (List Nat)) := buildBucketsBT lb572 lb565
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb559 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb562 3 xs.toFinset) lb558 := buildBucketsBT_sound (by decide) lb566 lb573 lb568 lb553 lb561 lb560
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb557 : Lower lb345 lb562 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) lb559 (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q36 : Lower (varsOf 27) 0xeeeeaa00eeeeaa00eeeeaa00eeeeaa00 4 := by
  apply carry_of (swaps := [(3, 4), (2, 3)]) (roots2 := lb345) (T2 := lb562) _ lb557
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q37 : Lower (varsOf 30) 0xfcfcf000fcfcf000fcfcf000fcfcf000 4 := by
  apply carry_of (swaps := [(3, 4), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := lb345) (T2 := lb562) _ lb557
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q38 : Lower (varsOf 58) 0xffffff00cccc0000ffffff00cccc0000 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3), (0, 1)]) (roots2 := lb345) (T2 := lb562) _ lb557
  decide +kernel
def rootNR : List Nat := varsOf 127
def rootNG : Nat := 0xfffffffffffffffefffffffafefefaa0
def rootNPos : List Nat := [5,5,5,5,7,7,7,7,9,9,11,11,12,12,13,14,17,17,18,18,20,20,21,25,26,26,28,33,33,33,35,35,35,36,36,36,37,38,38,40,41,42,48,48,56,65,65,66,66,66,66,66,67,67,68,68,68,69,69,70,72,72,73,80,80,88,96,96,96,96,97,98]
def rootNNeg : List Nat := [0,1,4,64,2,3,6,34,1,8,3,10,4,8,8,10,1,16,2,16,4,16,16,24,10,24,24,1,4,32,2,3,34,4,32,64,0,6,34,32,8,10,16,32,24,1,64,2,3,6,34,64,2,3,1,4,64,0,64,6,8,64,8,16,64,24,0,1,32,64,64,34]
def rootNMask : Nat := fullMask 72
def rootNBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x4046306111f8c34fff,0x80061200088010522),(0xcccccccccccccccccccccccccccccccc,0x80083f8261c30c8cf0,0x8008378261c1048cf0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfc0007e0470f0ff,0x882002210101044),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x2700013800780ff00,0x2500013000780ea00),(0xffff0000ffff0000ffff0000ffff0000,0x380001c0007ff0000,0x28000140006ea0000),(0xffffffff00000000ffffffff00000000,0xfc00001ffff8000000,0x90000408c520000080),(0xffffffffffffffff0000000000000000,0xffffffe00000000000,0x612508400800000008)]
def rootNSteps : List (Nat × Nat × Nat) := [(1,0,1),(1,0,6),(2,7,2),(1,9,5),(1,5,6),(1,5,8),(2,7,5),(1,2,5),(2,7,14),(1,2,6),(1,2,8),(1,14,6),(1,14,8),(3,3,19),(2,14,8),(1,21,6),(3,2,12),(3,5,16),(3,5,17),(1,7,2),(2,26,5),(1,7,5),(1,7,14),(3,2,29),(1,15,2),(2,14,6),(1,0,2),(1,0,5),(1,1,14),(2,33,6),(2,34,6),(1,33,5),(3,5,8),(1,1,5),(2,33,5),(3,0,19),(2,20,0),(2,20,2),(3,0,29),(2,20,5),(2,38,6),(1,41,6),(1,36,5),(2,33,11),(3,33,11),(1,51,0),(1,51,2),(1,1,2),(3,2,8),(1,55,5)]
def rootNW : BT Decor := buildWiresBT 6 rootNBase rootNSteps
def rootNAutoList : List (List (Nat × Nat)) := [[],[(2,5)],[(0,2)],[(0,2),(2,5)],[(0,5),(2,5)],[(0,5)]]
def rootNAutos : BT (List (Nat × Nat)) := btOfList 3 rootNAutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNPairs : goodPairs rootNG rootNPos rootNNeg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBaseOk : ∀ x ∈ rootNBase, faithful rootNPos rootNNeg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNWOk : btAll (fun x => faithful rootNPos rootNNeg x ∧ x.1 < 2^128) rootNW := buildWiresBT_faithful rootNBaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNAutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw rootNG = rootNG) rootNAutos := btAll_ofList (autos_of (by decide +kernel))
def rootNSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 16 0,11),some (subcubeFast 8 0,11),some (subcubeFast 2 0,11),some (subcubeFast 18 0,10),some (subcubeFast 10 0,10),some (subcubeFast 64 0,10),some (subcubeFast 32 0,10),some (subcubeFast 4 0,10),some (subcubeFast 1 0,10),some (0x44114411441144114411441144114411,10),some (0xc030c030c030c030c030c030c030c03,10),some (0xcc33cc3300000000cc33cc33,10),some (subcubeFast 64 2,8),some (subcubeFast 6 0,8),some (subcubeFast 3 0,8),some (subcubeFast 80 2,7),some (subcubeFast 19 0,7),some (subcubeFast 11 0,7),some (subcubeFast 96 0,7),some (subcubeFast 68 0,7),some (subcubeFast 36 0,7),some (subcubeFast 65 0,7),some (subcubeFast 33 0,7),some (subcubeFast 5 0,7),some (subcubeFast 96 2,5),some (subcubeFast 65 2,5),some (subcubeFast 7 0,5),some (subcubeFast 112 2,4),some (subcubeFast 84 2,4),some (subcubeFast 45 0,4),some (subcubeFast 81 2,4),some (subcubeFast 83 0,4),some (subcubeFast 51 0,4),some (subcubeFast 75 0,4),some (subcubeFast 43 0,4),some (subcubeFast 23 0,4),some (subcubeFast 100 0,4),some (subcubeFast 97 0,4),some (subcubeFast 69 0,4)]
def rootNSlices : BT (Option (Nat × Nat)) := btOfList 6 rootNSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice0 : Slice rootNR rootNG (subcubeFast 16 0) 11 := slice_fast_direct (zDead := 0) (qRoots := varsOf 111) (qGoal := 0xfffffffffffefffefffafffafaa0faa0) (by decide +kernel) q0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice1 : Slice rootNR rootNG (subcubeFast 8 0) 11 := slice_fast_direct (zDead := 0) (qRoots := varsOf 119) (qGoal := 0xfffffffffffffefefffffafafefea0a0) (by decide +kernel) q2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice2 : Slice rootNR rootNG (subcubeFast 2 0) 11 := slice_fast_direct (zDead := 0) (qRoots := varsOf 125) (qGoal := 0xfffffffffffffffafffffffafafafaa0) (by decide +kernel) q4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice3 : Slice rootNR rootNG (subcubeFast 18 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 109) (qGoal := 0xfffffffffffafffafffafffafaa0faa0) (by decide +kernel) q1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice4 : Slice rootNR rootNG (subcubeFast 10 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 117) (qGoal := 0xfffffffffffffafafffffafafafaa0a0) (by decide +kernel) q3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice5 : Slice rootNR rootNG (subcubeFast 64 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 63) (qGoal := 0xfffffffafefefaa0fffffffafefefaa0) (by decide +kernel) q5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice6 : Slice rootNR rootNG (subcubeFast 32 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 95) (qGoal := 0xfffffffefffffffefefefaa0fefefaa0) (by decide +kernel) q7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice7 : Slice rootNR rootNG (subcubeFast 4 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 123) (qGoal := 0xffffffffffffffeeffffffaaeeeeaa00) (by decide +kernel) q8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice8 : Slice rootNR rootNG (subcubeFast 1 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 126) (qGoal := 0xfffffffffffffffcfffffff0fcfcf000) (by decide +kernel) q9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice9 : Slice rootNR rootNG 0x44114411441144114411441144114411 10 := mappedSlice (f := identifyRow 1 0 1 3) (R := varsOf 118) (G := 0xfffffffffffffcfcfffffcfcfcfcc0c0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice10 : Slice rootNR rootNG 0xc030c030c030c030c030c030c030c03 10 := mappedSlice (f := identifyRow 4 0 1 3) (R := varsOf 115) (G := 0xffffffffffffeeeeffffeeeeeeee8888) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice11 : Slice rootNR rootNG 0xcc33cc3300000000cc33cc33 10 := mappedSlice (f := identifyRow 32 0 1 3) (R := varsOf 87) (G := 0xfffffefefffffefefefee8e8fefee8e8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice12 : Slice rootNR rootNG (subcubeFast 64 2) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffffffafffffaa0fffffffafffffaa0) (by decide +kernel) q13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice13 : Slice rootNR rootNG (subcubeFast 6 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 121) (qGoal := 0xffffffffffffffaaffffffaaaaaaaa00) (by decide +kernel) q15
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice14 : Slice rootNR rootNG (subcubeFast 3 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 124) (qGoal := 0xfffffffffffffff0fffffff0f0f0f000) (by decide +kernel) q16
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice15 : Slice rootNR rootNG (subcubeFast 80 2) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 45) (qGoal := 0xfffafffafaa0faa0fffafffafaa0faa0) (by decide +kernel) q14
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice16 : Slice rootNR rootNG (subcubeFast 19 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 108) (qGoal := 0xfffffffffff0fff0fff0fff0f000f000) (by decide +kernel) q17
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice17 : Slice rootNR rootNG (subcubeFast 11 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 116) (qGoal := 0xfffffffffffff0f0fffff0f0f0f00000) (by decide +kernel) q18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice18 : Slice rootNR rootNG (subcubeFast 96 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfefefaa0fefefaa0fefefaa0fefefaa0) (by decide +kernel) q19
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice19 : Slice rootNR rootNG (subcubeFast 68 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffffffaaeeeeaa00ffffffaaeeeeaa00) (by decide +kernel) q20
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice20 : Slice rootNR rootNG (subcubeFast 36 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 91) (qGoal := 0xffffffeeffffffeeeeeeaa00eeeeaa00) (by decide +kernel) q21
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice21 : Slice rootNR rootNG (subcubeFast 65 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffffff0fcfcf000fffffff0fcfcf000) (by decide +kernel) q22
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice22 : Slice rootNR rootNG (subcubeFast 33 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 94) (qGoal := 0xfffffffcfffffffcfcfcf000fcfcf000) (by decide +kernel) q23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice23 : Slice rootNR rootNG (subcubeFast 5 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 122) (qGoal := 0xffffffffffffffccffffff00cccc0000) (by decide +kernel) q24
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice24 : Slice rootNR rootNG (subcubeFast 96 2) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 29) (qGoal := 0xfffffaa0fffffaa0fffffaa0fffffaa0) (by decide +kernel) q25
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice25 : Slice rootNR rootNG (subcubeFast 65 2) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 60) (qGoal := 0xfffffff0fffff000fffffff0fffff000) (by decide +kernel) q26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice26 : Slice rootNR rootNG (subcubeFast 7 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 120) (qGoal := 0xffffffffffffff00ffffff0000000000) (by decide +kernel) q27
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice27 : Slice rootNR rootNG (subcubeFast 112 2) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 13) (qGoal := 0xfaa0faa0faa0faa0faa0faa0faa0faa0) (by decide +kernel) q28
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice28 : Slice rootNR rootNG (subcubeFast 84 2) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 41) (qGoal := 0xffaaffaaaa00aa00ffaaffaaaa00aa00) (by decide +kernel) q29
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice29 : Slice rootNR rootNG (subcubeFast 45 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 82) (qGoal := 0xffffccccffffcccccccc0000cccc0000) (by decide +kernel) q30
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice30 : Slice rootNR rootNG (subcubeFast 81 2) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 44) (qGoal := 0xfff0fff0f000f000fff0fff0f000f000) (by decide +kernel) q31
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice31 : Slice rootNR rootNG (subcubeFast 83 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 44) (qGoal := 0xfff0fff0f000f000fff0fff0f000f000) (by decide +kernel) q31
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice32 : Slice rootNR rootNG (subcubeFast 51 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 76) (qGoal := 0xfff0fff0fff0fff0f000f000f000f000) (by decide +kernel) q32
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice33 : Slice rootNR rootNG (subcubeFast 75 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 52) (qGoal := 0xfffff0f0f0f00000fffff0f0f0f00000) (by decide +kernel) q33
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice34 : Slice rootNR rootNG (subcubeFast 43 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 84) (qGoal := 0xfffff0f0fffff0f0f0f00000f0f00000) (by decide +kernel) q34
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice35 : Slice rootNR rootNG (subcubeFast 23 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 104) (qGoal := 0xffffffffff00ff00ff00ff0000000000) (by decide +kernel) q35
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice36 : Slice rootNR rootNG (subcubeFast 100 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 27) (qGoal := 0xeeeeaa00eeeeaa00eeeeaa00eeeeaa00) (by decide +kernel) q36
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice37 : Slice rootNR rootNG (subcubeFast 97 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 30) (qGoal := 0xfcfcf000fcfcf000fcfcf000fcfcf000) (by decide +kernel) q37
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice38 : Slice rootNR rootNG (subcubeFast 69 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffffff00cccc0000ffffff00cccc0000) (by decide +kernel) q38
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlicesOk : btAll (fun o => ∀ p, o = some p → Slice rootNR rootNG p.1 p.2) rootNSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice rootNR rootNG p.1 p.2) (forall_cons (fun _ h => by cases h; exact rootNSlice0) (forall_cons (fun _ h => by cases h; exact rootNSlice1) (forall_cons (fun _ h => by cases h; exact rootNSlice2) (forall_cons (fun _ h => by cases h; exact rootNSlice3) (forall_cons (fun _ h => by cases h; exact rootNSlice4) (forall_cons (fun _ h => by cases h; exact rootNSlice5) (forall_cons (fun _ h => by cases h; exact rootNSlice6) (forall_cons (fun _ h => by cases h; exact rootNSlice7) (forall_cons (fun _ h => by cases h; exact rootNSlice8) (forall_cons (fun _ h => by cases h; exact rootNSlice9) (forall_cons (fun _ h => by cases h; exact rootNSlice10) (forall_cons (fun _ h => by cases h; exact rootNSlice11) (forall_cons (fun _ h => by cases h; exact rootNSlice12) (forall_cons (fun _ h => by cases h; exact rootNSlice13) (forall_cons (fun _ h => by cases h; exact rootNSlice14) (forall_cons (fun _ h => by cases h; exact rootNSlice15) (forall_cons (fun _ h => by cases h; exact rootNSlice16) (forall_cons (fun _ h => by cases h; exact rootNSlice17) (forall_cons (fun _ h => by cases h; exact rootNSlice18) (forall_cons (fun _ h => by cases h; exact rootNSlice19) (forall_cons (fun _ h => by cases h; exact rootNSlice20) (forall_cons (fun _ h => by cases h; exact rootNSlice21) (forall_cons (fun _ h => by cases h; exact rootNSlice22) (forall_cons (fun _ h => by cases h; exact rootNSlice23) (forall_cons (fun _ h => by cases h; exact rootNSlice24) (forall_cons (fun _ h => by cases h; exact rootNSlice25) (forall_cons (fun _ h => by cases h; exact rootNSlice26) (forall_cons (fun _ h => by cases h; exact rootNSlice27) (forall_cons (fun _ h => by cases h; exact rootNSlice28) (forall_cons (fun _ h => by cases h; exact rootNSlice29) (forall_cons (fun _ h => by cases h; exact rootNSlice30) (forall_cons (fun _ h => by cases h; exact rootNSlice31) (forall_cons (fun _ h => by cases h; exact rootNSlice32) (forall_cons (fun _ h => by cases h; exact rootNSlice33) (forall_cons (fun _ h => by cases h; exact rootNSlice34) (forall_cons (fun _ h => by cases h; exact rootNSlice35) (forall_cons (fun _ h => by cases h; exact rootNSlice36) (forall_cons (fun _ h => by cases h; exact rootNSlice37) (forall_cons (fun _ h => by cases h; exact rootNSlice38) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))))))
def rootNEmpty : BT (List (List Nat)) := BT.empty
lemma rootNEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG (5 - 1) xs.toFinset) rootNEmpty := trivial
def rootNBlock5_0Specs : List PoolSpec := [(29,[])]
def rootNBlock5_0Pools : BT (Option BoundPool) := buildPoolsBT 1 rootNW rootNR rootNSlices rootNBlock5_0Specs
def rootNBlock5_0 : List NodeSpec := [([3,4,29,17,12,18],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock5_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock5_0Pools rootNAutos rootNEmpty 5 rootNBlock5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock5_0Mem : ∀ ns ∈ rootNBlock5_0, Impossible rootNG 5 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNEmptyOk rootNBlock5_0Ok
def rootNNodes5 : List NodeSpec := rootNBlock5_0
def rootNBucket5 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 5 xs.toFinset) rootNBucket5 := buildBucketsBT_of_mem rootNBlock5_0Mem
def rootNBlock6_0Specs : List PoolSpec := [(28,[]),(29,[]),(31,[]),(12,[(1,2,5),(1,14,8),(3,3,19)]),(12,[(1,2,5),(1,2,8),(1,5,8)]),(35,[]),(25,[]),(12,[(1,0,2),(1,33,11),(3,3,19)]),(12,[(1,0,2),(1,0,11),(1,2,11)])]
def rootNBlock6_0Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock6_0Specs
def rootNBlock6_0 : List NodeSpec := [([15,20,2,4,5,6,8],[],[]),([15,3,4,14,6,17,12],[1,2],[]),([15,3,4,14,8,16,12],[0],[]),([27,3,4,38,8,16],[1,5],[]),([44,43,1,33,4,5,6],[1],[]),([44,43,1,4,5,38,6],[],[]),([44,43,1,4,5,6,17],[],[]),([44,43,1,4,5,6,19],[],[]),([20,1,33,4,34,16,11],[],[]),([20,7,4,5,14,8,16],[3],[]),([20,2,26,4,5,8,11],[7],[]),([30,33,3,4,6,11,12],[1],[]),([1,3,4,38,17,12,18],[1],[0]),([7,3,4,14,17,12,18],[1,4],[]),([2,3,4,29,17,11,12],[1],[0]),([33,3,4,29,6,12,18],[1],[0]),([33,3,4,29,8,11,18],[1],[]),([26,3,4,5,17,12,18],[1,8],[]),([26,3,4,34,17,11,18],[6],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock6_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock6_0Pools rootNAutos rootNBucket5 6 rootNBlock6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock6_0Mem : ∀ ns ∈ rootNBlock6_0, Impossible rootNG 6 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket5Ok rootNBlock6_0Ok
def rootNNodes6 : List NodeSpec := rootNBlock6_0
def rootNBucket6 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 6 xs.toFinset) rootNBucket6 := buildBucketsBT_of_mem rootNBlock6_0Mem
def rootNBlock7_0Specs : List PoolSpec := [(28,[]),(24,[]),(17,[]),(29,[]),(31,[]),(15,[(1,2,5)]),(16,[(1,2,5),(1,14,6)]),(12,[(1,2,5),(1,14,8),(3,3,19)]),(8,[(1,2,5),(1,14,8),(3,3,19)]),(6,[(1,0,1),(1,0,6),(1,14,8),(3,3,19)]),(37,[]),(15,[(1,2,5),(1,14,8),(3,3,19)]),(7,[(1,0,1),(1,0,6),(1,14,8),(3,3,19)]),(15,[(1,5,8),(3,2,12)]),(4,[(1,0,6),(1,2,6),(1,5,8),(3,2,12)]),(21,[(1,5,17),(3,3,19)]),(23,[]),(32,[]),(14,[(1,2,5),(1,2,6),(1,5,6)]),(4,[]),(35,[]),(12,[(1,0,2),(1,0,5)]),(25,[]),(36,[]),(7,[(1,0,5),(1,34,16),(3,3,19)]),(8,[(1,2,6),(1,34,16),(3,3,19)]),(15,[(1,0,2),(1,33,5)]),(12,[(1,0,2)]),(30,[]),(12,[(1,0,2),(1,33,11),(3,3,19)]),(5,[(1,0,2),(1,33,11),(3,3,19)]),(8,[(1,5,6),(1,33,11),(3,3,19)]),(15,[(1,0,2),(1,33,5),(3,3,19)]),(7,[(1,1,33),(1,33,6),(1,5,17),(3,3,19)]),(0,[(1,0,2),(1,5,6),(2,33,11),(1,50,11),(3,3,19)])]
def rootNBlock7_0Pools : BT (Option BoundPool) := buildPoolsBT 6 rootNW rootNR rootNSlices rootNBlock7_0Specs
def rootNBlock7_0 : List NodeSpec := [([46,20,0,1,2,4,6,11],[3],[]),([15,0,3,4,14,16,11],[3,5,18],[]),([15,2,3,4,5,6,8,19],[3],[0]),([15,2,3,4,5,8,18],[0,1,3,6],[]),([15,3,4,5,14,6,8,17],[0,3,4],[0,1]),([15,3,4,5,14,8,16],[0,3,4,5],[0]),([27,2,3,4,34,6,17],[3,20,21,22],[]),([27,2,3,4,38,6,8],[3,20,26],[0]),([27,33,3,4,5,8,16],[1,3,20,27],[0]),([27,33,3,4,34,6,16],[3,20,21],[]),([39,33,26,3,4,5,16],[3,28],[]),([25,20,0,1,2,4,6,11],[3],[]),([43,20,1,2,33,4,5,6],[3],[0]),([43,20,1,2,4,5,38,6],[3],[0,1]),([43,20,1,2,4,5,6,17],[3],[0]),([43,20,1,2,4,5,6,19],[3],[0,1]),([20,42,1,2,33,4,5,6],[3],[]),([20,42,1,2,4,5,38,6],[3],[]),([20,42,1,2,4,5,6,17],[3],[]),([20,42,1,2,4,5,6,19],[3],[]),([20,0,1,2,4,5,6],[3,34],[]),([20,0,1,2,4,5,6,19],[19],[]),([20,0,2,26,4,5,6],[3,32],[]),([20,0,2,26,4,5,6,17],[33],[]),([20,0,2,26,4,5,6,11],[29],[0,2]),([20,0,2,26,4,5,6,19],[2],[]),([20,0,2,4,5,29,6],[3,32],[]),([20,0,2,4,5,29,6,19],[3],[]),([20,1,2,33,4,5,8,11],[30,31],[0,2,3]),([20,1,33,4,5,34,6,16],[3,24,25],[0]),([20,7,2,4,5,14,6,8],[7,8,9],[0,1]),([20,7,2,4,5,6,8],[3,9,11,12],[]),([20,7,2,4,5,6,8,17],[3,15],[]),([20,7,2,4,5,6,8,19],[3],[]),([30,45,3,4,5,38,6],[3,17,26],[]),([23,42,1,33,3,4,5,6],[3],[]),([23,42,1,3,4,5,38,6],[],[]),([23,42,1,3,4,5,6,17],[],[]),([23,42,1,3,4,5,6,19],[],[]),([23,7,3,4,5,8,16],[10,13,14],[]),([23,33,26,3,4,5,6,8],[3],[]),([23,33,26,3,4,5,6,12],[3,22],[]),([42,2,26,3,4,5,6,17],[16],[]),([42,2,26,3,4,5,6,19],[3],[]),([42,2,3,4,5,29,6,19],[3],[]),([1,2,3,4,38,17,11,12],[3],[0]),([1,33,3,4,5,17,12,18],[3],[0,3]),([1,33,3,4,34,16,11,19],[3,23],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock7_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock7_0Pools rootNAutos rootNBucket6 7 rootNBlock7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock7_0Mem : ∀ ns ∈ rootNBlock7_0, Impossible rootNG 7 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket6Ok rootNBlock7_0Ok
def rootNBlock7_1Specs : List PoolSpec := [(28,[]),(17,[(1,5,6)]),(24,[]),(29,[]),(31,[]),(7,[(1,0,1),(1,0,6),(1,5,8)]),(15,[(1,2,5),(1,5,8)]),(21,[(1,2,5)]),(4,[(1,0,6),(1,2,5),(1,2,6),(1,5,8)]),(38,[]),(12,[(1,2,5),(1,14,8)]),(15,[(1,2,5),(1,2,8),(1,5,8)]),(4,[(1,0,6),(1,2,5),(1,2,8),(1,5,8)]),(12,[(1,2,5),(1,2,8)]),(15,[(1,2,5),(2,14,8)]),(27,[]),(15,[(1,0,2),(1,0,5),(1,2,5)]),(15,[(1,0,2),(1,0,5)]),(8,[(1,1,33),(1,2,6),(1,5,16)]),(25,[]),(15,[(1,0,2),(1,33,5)]),(7,[(1,0,6),(1,1,33),(1,5,8)]),(12,[(1,0,2),(1,2,11)]),(12,[(1,0,2),(1,33,11)]),(4,[(1,0,2),(1,0,6),(1,2,6),(1,5,8)]),(7,[(1,0,6),(1,5,8),(1,1,33)]),(12,[(1,0,2),(1,0,11),(1,2,11)]),(12,[(1,0,2),(1,0,11)])]
def rootNBlock7_1Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock7_1Specs
def rootNBlock7_1 : List NodeSpec := [([1,33,3,4,34,16,12,18],[3],[1]),([1,33,3,4,38,6,12,18],[3],[0]),([1,33,3,4,38,8,11,18],[3],[0]),([7,2,3,4,5,22,8],[3,14],[]),([7,3,4,5,14,8,16,19],[3,9,10],[0]),([7,3,4,5,14,8,17,18],[0,3,13],[0]),([7,3,4,14,6,17,12],[3,4,5,11,12],[0]),([7,3,4,14,8,16,12],[3,5,6,7,8],[0]),([2,33,3,4,29,6,11,12],[3],[0,2]),([2,26,3,4,5,8,11,19],[3,9,23],[0]),([2,26,3,4,5,17,11,12],[3,19,27],[0,2]),([2,26,3,4,34,17,11],[0,3,17,19],[0]),([2,26,3,4,38,8,11],[3,20],[]),([2,3,4,10,8,11],[0,1,2],[]),([33,26,3,4,5,6,12,18],[2,19,26],[0]),([33,26,3,4,5,8,16,12],[2,3,19,21],[]),([33,26,3,4,5,8,11,18],[0,2,19,22],[]),([33,26,3,4,5,16,12],[2,3,9,17],[]),([33,26,3,4,34,6,16,18],[0,3,18],[]),([33,26,3,4,34,6,11,18],[2,3],[0]),([33,26,3,4,34,16,11],[0,2,3,17],[]),([33,26,3,4,14,6,12],[2,3,4,16],[]),([26,3,4,5,38,8,16],[3,20],[0]),([26,3,4,5,8,16,12],[3,9,15,24,25],[]),([26,3,4,34,14,6,17],[0,3,4,16],[]),([3,4,5,38,29,8,16],[3,20],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock7_1Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock7_1Pools rootNAutos rootNBucket6 7 rootNBlock7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock7_1Mem : ∀ ns ∈ rootNBlock7_1, Impossible rootNG 7 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket6Ok rootNBlock7_1Ok
def rootNNodes7 : List NodeSpec := rootNBlock7_0 ++ rootNBlock7_1
def rootNBucket7 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 7 xs.toFinset) rootNBucket7 := buildBucketsBT_of_mem (forall_append rootNBlock7_0Mem rootNBlock7_1Mem)
def rootNBlock8_0Specs : List PoolSpec := [(28,[]),(17,[(1,5,6)]),(24,[]),(17,[]),(6,[(1,0,1),(1,0,6),(2,7,2)]),(16,[(1,5,6)]),(29,[]),(33,[]),(7,[(1,0,1),(1,0,6),(1,5,6)]),(31,[]),(17,[(1,5,8)]),(7,[(1,0,1),(1,0,6),(1,5,8)]),(15,[]),(15,[(1,2,5)]),(16,[(1,2,5),(1,14,6)]),(14,[(1,2,5)]),(6,[(1,0,1),(1,0,6),(2,7,14)]),(21,[(1,2,5)]),(38,[]),(6,[(1,0,1),(1,0,6),(1,2,6)]),(6,[(1,0,1),(1,0,6),(1,2,8)]),(37,[]),(15,[(1,2,5),(2,14,8)]),(4,[(1,0,6),(1,2,6),(1,5,8),(3,2,12)]),(21,[]),(4,[(1,0,6),(1,2,6),(3,5,16)]),(21,[(1,5,17),(3,3,19)]),(21,[(1,5,17)]),(15,[(1,2,8),(3,5,17)]),(4,[(1,0,6),(1,2,8),(3,5,17)]),(23,[]),(16,[]),(32,[]),(14,[(1,2,5),(1,2,6)]),(35,[]),(25,[]),(5,[(1,0,2),(1,0,5),(1,2,5)]),(3,[(1,0,2),(1,0,5),(1,2,5),(2,33,6)]),(36,[]),(19,[]),(0,[(1,0,2),(1,0,5),(1,33,6),(3,5,17)]),(3,[(1,0,2),(1,0,5),(1,33,6),(3,5,17)]),(1,[(1,0,2),(1,0,5),(1,33,6),(3,5,17)]),(15,[(1,0,2),(1,33,5)]),(12,[(1,0,2)]),(30,[]),(6,[(1,0,2),(1,0,6),(1,2,6)]),(3,[(1,0,2),(1,0,6),(1,2,6),(2,33,5)]),(1,[(1,0,2),(1,0,6),(1,2,6),(2,33,5)]),(3,[(1,0,2),(1,0,6),(1,2,6),(3,5,8)]),(1,[(1,0,2),(1,0,6),(1,2,6),(3,5,8)]),(5,[(1,0,2),(1,33,11),(3,3,19)]),(8,[(1,5,6),(1,33,11),(3,3,19)]),(3,[(1,0,2),(1,0,6),(1,5,8),(3,2,12)]),(1,[(1,0,2),(1,0,6),(1,5,8),(3,2,12)]),(7,[(1,1,33),(1,33,6),(2,26,5)]),(15,[(1,0,2),(3,5,17)]),(0,[(1,0,2),(1,33,5),(1,33,6),(3,5,17)]),(2,[(1,0,2),(1,33,5),(1,38,6),(3,0,19)]),(0,[(1,0,2),(1,33,5),(1,38,6),(3,0,19)]),(4,[(1,0,2),(1,33,5),(1,38,6)]),(18,[(1,0,2),(3,3,19)]),(7,[(1,33,5),(1,38,6),(3,3,19)]),(3,[(1,0,2),(1,33,5),(1,38,6),(3,3,19)]),(5,[(1,0,2),(1,33,5),(3,3,19)]),(1,[(1,0,2),(1,33,5),(1,38,6),(3,0,19)]),(6,[(1,0,2),(1,38,6),(3,3,19)]),(8,[(1,33,5),(1,38,6),(3,3,19)]),(2,[(1,0,2),(1,33,6),(1,5,17),(3,0,19)]),(19,[(1,5,17),(3,3,19)]),(4,[(1,0,2),(1,33,6),(1,5,17)]),(7,[(1,33,6),(1,5,17),(3,3,19)]),(3,[(1,0,2),(1,33,6),(1,5,6),(3,5,17)]),(1,[(1,0,2),(1,33,6),(1,5,6),(3,5,17)]),(1,[(1,0,2),(1,33,6),(1,5,17),(3,0,19)]),(0,[(1,0,2),(1,33,6),(1,5,17),(3,0,19)]),(6,[(1,0,2),(1,33,6),(3,3,19)]),(3,[(1,0,2),(1,33,6),(1,5,17),(3,3,19)]),(8,[(1,33,6),(1,5,17),(3,3,19)]),(4,[(1,0,2),(1,5,6),(1,33,11)]),(6,[(1,0,2),(1,33,11),(3,3,19)]),(7,[(1,5,6),(1,33,11),(3,3,19)]),(3,[(1,0,2),(1,5,6),(1,33,11),(3,3,19)]),(1,[(1,0,2),(1,5,6),(1,33,11),(3,5,19)]),(3,[(1,0,2),(1,5,6),(1,33,11),(3,5,19)]),(18,[]),(3,[(1,0,6),(1,2,6),(1,5,8),(3,2,12)]),(19,[(1,5,8)])]
def rootNBlock8_0Pools : BT (Option BoundPool) := buildPoolsBT 7 rootNW rootNR rootNSlices rootNBlock8_0Specs
def rootNBlock8_0 : List NodeSpec := [([21,7,2,3,4,5,6,8],[3,6,17,22],[0]),([36,1,3,4,34,14,6],[6,36,37],[]),([15,0,2,3,4,5,6,18],[0,2,6,13,14],[0]),([15,0,3,4,5,14,6,16],[0,6,13,33],[0]),([15,2,3,4,5,14,6,8],[0,2,6,9,13,15,16],[0,1]),([41,1,3,4,5,8,16],[2,6,12,30,46,47,48],[]),([27,0,2,3,4,5,6,17],[0,6,34,35,44,55],[0,2]),([27,0,2,3,4,38,6],[6,34],[0,2]),([27,2,33,3,4,5,6,8],[6,31,34,35,44],[0,2]),([27,2,33,3,4,34,6],[6,31,34],[0]),([39,1,33,3,4,5,16],[6,24,46,49,50],[0]),([39,2,33,26,3,4,5,6],[6,9,45],[0]),([24,7,2,3,4,5,8],[0,19,24,25],[]),([25,0,1,2,3,4,38,6],[6,18,57],[]),([25,0,1,2,3,4,6,11],[6,18,83,84],[]),([25,0,1,2,3,4,6,11,19],[6,21,38,83],[0]),([25,0,1,2,3,4,17,11],[6,18,24,39,72,73],[]),([25,0,2,26,3,4,5,6],[6,18,56],[]),([25,1,2,33,3,4,34,6],[6,18,24,40],[]),([25,1,2,3,4,34,6,17],[6,18,24,41,42],[1]),([25,7,2,3,4,5,6,8],[6,18,20,28,29],[1]),([20,0,1,2,33,4,5,6],[6,60,61,62,63,64],[0,2]),([20,0,1,2,33,4,5,6,17],[6,26,69,70,71],[0]),([20,0,1,2,33,4,5,6,11],[6,51,52,61,79,80,81],[0,1,2,3,4]),([20,0,1,2,33,4,5,6,19],[60,61,62],[0,2]),([20,0,1,2,4,5,38,6],[6,63,64],[0,2,3]),([20,0,1,2,4,5,38,6,19],[6,60,61],[0,2,3]),([20,0,1,2,4,5,6],[6,60,62,63,64,66,67],[]),([20,0,1,2,4,5,6,8,17],[6,26,69],[0]),([20,0,1,2,4,5,6,17],[6,26,69,70,71,76,77,78],[0,2]),([20,0,1,2,4,5,6,17,19],[6,76],[0,2,3]),([20,0,1,2,4,5,6,11],[6,52,61,79,81,82],[0,3]),([20,0,1,2,4,5,6,11,19],[6],[0,3]),([20,0,1,2,4,5,6,19],[6,60,62,63,66,67],[0,2,3]),([9,2,3,4,5,6,8,12],[4,6,9,10,11],[]),([9,2,3,4,5,8,11],[1,4,5,6,7,8],[0]),([30,0,3,4,5,14,6],[6,13,32],[]),([23,0,1,3,4,5,8,16],[21,23,85,86,87],[0]),([23,1,33,3,4,5,6,8],[6,21,53,54],[0]),([45,2,3,4,5,38,29,6],[6,43],[0,1]),([42,1,2,33,3,4,5,6],[6,38,59],[]),([42,1,2,33,3,4,5,6,17],[6,18,27,68],[0]),([42,1,2,33,3,4,5,6,19],[6,18,58],[0]),([42,1,2,3,4,5,38,6,19],[6,58],[0,1]),([42,1,2,3,4,5,6,8,17],[6,18,27],[]),([42,1,2,3,4,5,6,17],[6,18,27,38,74,75],[]),([42,1,2,3,4,5,6,17,19],[6,18,38,74],[0,1]),([42,1,2,3,4,5,6,19],[6,38,59,65],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_0Pools rootNAutos rootNBucket7 8 rootNBlock8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_0Mem : ∀ ns ∈ rootNBlock8_0, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_0Ok
def rootNBlock8_1Specs : List PoolSpec := [(28,[]),(17,[(1,5,6)]),(24,[]),(16,[(1,5,6)]),(29,[]),(33,[]),(31,[]),(7,[(1,0,1),(1,0,6),(1,5,8)]),(15,[]),(7,[(1,0,1),(1,0,6)]),(15,[(1,2,5)]),(21,[(1,2,5)]),(38,[]),(12,[(1,2,5),(1,14,8)]),(4,[(1,0,6),(1,2,5),(1,2,6)]),(6,[(1,0,1),(1,0,6),(1,2,6)]),(15,[(1,2,5),(1,2,8)]),(6,[(1,0,1),(1,0,6),(1,2,8)]),(4,[(1,0,6),(1,2,5),(1,2,8)]),(8,[(1,2,5),(1,14,6)]),(6,[(1,0,1),(1,0,6),(1,14,6)]),(4,[(1,0,6),(1,2,5),(1,14,6)]),(7,[(1,0,1),(1,0,6),(1,14,6)]),(37,[]),(8,[(1,2,5),(1,14,8)]),(6,[(1,0,1),(1,0,6),(1,14,8)]),(15,[(1,2,5),(1,14,8)]),(4,[(1,0,6),(1,2,5),(1,14,8)]),(7,[(1,0,1),(1,0,6),(1,14,8)]),(15,[(1,5,8)]),(4,[(1,0,6),(1,2,6),(1,5,8)]),(21,[]),(4,[(1,0,6),(1,2,6),(1,5,16)]),(8,[(1,2,6),(1,5,16)]),(12,[(1,5,16)]),(21,[(1,5,16)]),(15,[(1,2,8),(1,5,8)]),(4,[(1,0,6),(1,2,8),(1,5,8)]),(21,[(1,5,17)]),(23,[]),(7,[(1,0,1),(1,5,6)]),(27,[]),(4,[(1,2,5),(1,2,6),(1,5,6)]),(8,[(1,2,5),(1,2,6),(1,5,6)]),(8,[(1,2,6),(1,5,6)]),(15,[(1,0,2),(1,0,5)]),(25,[]),(14,[(1,34,6)]),(3,[(1,0,2),(1,0,5),(1,2,5),(1,33,6)]),(19,[(1,0,5)]),(5,[(1,0,2),(1,0,5),(1,2,5)]),(1,[(1,0,2),(1,0,5),(1,2,5),(1,33,6)]),(6,[(1,0,2),(1,33,6)]),(36,[]),(3,[(1,0,2),(1,0,5),(1,2,6),(1,5,6)]),(1,[(1,0,2),(1,0,5),(1,2,6),(1,5,6)]),(18,[(1,0,2)]),(6,[(1,0,2),(1,2,6)]),(3,[(1,0,2),(1,0,5),(1,2,6),(1,5,16)]),(1,[(1,0,2),(1,0,5),(1,2,6),(1,5,16)]),(3,[(1,0,2),(1,0,5),(1,2,6),(1,34,6)]),(7,[(1,0,5),(1,34,6)]),(1,[(1,0,2),(1,0,5),(1,2,6),(1,34,6)]),(6,[(1,0,2),(1,2,6),(1,34,6)]),(5,[(1,0,2),(1,0,5)]),(7,[(1,0,5),(1,34,16)]),(8,[(1,2,6),(1,34,16)]),(19,[]),(22,[]),(15,[(1,0,2),(1,33,5)]),(12,[(1,0,2)]),(7,[(1,0,6),(1,1,33),(1,5,8)]),(15,[(1,0,2)]),(12,[(1,0,2),(1,33,11)]),(3,[(1,0,2),(1,0,6),(1,2,6),(1,33,5)]),(5,[(1,0,2),(1,33,5)]),(1,[(1,0,2),(1,0,6),(1,2,6),(1,33,5)]),(6,[(1,0,2),(1,0,6),(1,2,6)]),(19,[(1,33,5)]),(4,[(1,0,2),(1,0,6),(1,2,6),(1,5,8)]),(7,[(1,0,6),(1,5,8),(1,1,33)]),(3,[(1,0,2),(1,0,6),(1,2,6),(1,5,8)]),(7,[(1,0,6),(1,5,8)]),(3,[(1,0,2),(1,0,6),(1,33,5),(1,5,6)]),(21,[(1,33,5)]),(3,[(1,0,2),(1,0,6),(1,5,6),(1,2,11)]),(1,[(1,0,2),(1,0,6),(1,5,6),(1,2,11)]),(8,[(1,5,6),(1,2,11)]),(21,[(1,2,11)]),(5,[(1,0,2),(1,33,11)]),(8,[(1,5,6),(1,33,11)]),(4,[(1,0,2),(1,0,6),(1,5,8)]),(12,[(1,0,2),(1,0,11)]),(7,[(1,1,33),(1,33,6),(1,5,6)]),(7,[(1,1,33),(1,33,6),(1,5,17)]),(3,[(1,0,2),(1,33,5),(1,33,6),(1,5,6)]),(7,[(1,33,5),(1,33,6),(1,5,6)]),(3,[(1,0,2),(1,5,6),(1,0,11),(1,2,11)]),(1,[(1,0,2),(1,5,6),(1,0,11),(1,2,11)]),(19,[(1,0,11)]),(3,[(1,0,2),(1,5,6),(2,33,11),(1,50,5)]),(3,[(1,0,2),(1,5,6),(2,33,11),(1,50,6)]),(3,[(1,0,2),(1,5,6),(2,33,11),(1,50,11)]),(0,[(1,0,2),(1,5,6),(3,33,11),(1,51,0)])]
def rootNBlock8_1Pools : BT (Option BoundPool) := buildPoolsBT 7 rootNW rootNR rootNSlices rootNBlock8_1Specs
def rootNBlock8_1 : List NodeSpec := [([0,1,2,3,4,5,6,19],[4,12,23,53,102],[0]),([0,1,2,3,4,5,48,11],[4,12,101],[3]),([0,1,2,3,4,49,6,11],[4,8,100],[]),([0,1,2,3,4,38,17,11],[4,70,78,84,95,96],[0,2]),([0,7,3,4,14,16,11],[4,10,40,42,43],[0]),([0,2,26,3,4,5,6,17,19],[4,12,94],[0,2]),([0,2,26,3,4,5,6,11,19],[4,12,73],[0,2]),([0,2,26,3,4,5,6,19],[4,12,69],[0,2]),([0,2,26,3,4,5,17,11],[0,4,12,46,72,93],[0,2]),([0,2,26,3,4,38,6,11],[4,69],[0,2]),([0,2,3,4,5,29,6,19],[4,69],[0,2,3]),([0,2,3,4,10,6,11],[0,1,4],[0]),([0,31,3,4,5,14,6],[4,41],[]),([52,1,2,33,3,4,5,6],[4,23,56,103],[]),([1,2,33,3,4,5,8,11,19],[4,12,23,89,90],[0,2,3]),([1,2,33,3,4,5,17,11,12],[4,31],[0,3,4]),([1,2,33,3,4,38,6,11,12],[4,68],[0,2]),([1,2,33,3,4,38,8,11],[4,56,68,70,75,83,84],[0]),([1,33,3,4,5,34,6,16,19],[4,12,53,65,66],[0]),([1,33,3,4,5,34,16,12],[2,4,31,49,60,61],[0,1]),([1,33,3,4,5,38,8,16],[4,39,70,74,75],[0]),([1,33,3,4,5,6,12,18],[4,56,87,88,97,98,99],[0,3]),([1,33,3,4,5,8,16,12],[4,31,56,77,79,81,82],[0]),([1,33,3,4,5,8,11,18],[4,56,67,85,86,87,88],[0,3]),([1,33,3,4,5,16,12],[4,31,56,60,61,62,63,64],[0]),([1,33,3,4,34,14,6,17],[4,31,39,48,49,50],[0]),([1,33,3,4,34,6,16,18],[2,4,33,49,58,59],[0,1]),([1,33,3,4,34,16,11],[4,44,49,54,55,56,57],[0,1]),([1,3,4,5,38,8,16],[4,8,39,74,75,76,77,78],[0]),([1,3,4,34,14,6,17],[4,11,48,49,50,51,52],[1,4]),([7,2,3,4,5,14,6,8,19],[4,12,13,23,24,25],[0,1]),([7,2,3,4,5,14,8,18],[0,2,4,10,11,19,20],[0,1]),([7,2,3,4,5,6,8,17,19],[4,5,12,23,38],[0]),([7,2,3,4,5,6,8,19],[4,12,23,25,26,27,28],[0]),([7,2,3,4,5,6,17,12],[4,7,12,17,23,31,36,37],[0]),([7,2,3,4,5,8,16,12],[4,7,15,23,29,30,31],[0]),([7,2,3,4,5,8,16,18],[0,2,4,15,32,33,34,35],[]),([7,2,3,4,5,8,18],[0,2,4,10,19,20,21,22],[]),([7,3,4,5,14,6,8,17],[4,11,12,16,17,18],[0,1]),([7,3,4,5,14,8,16],[0,4,9,10,11,14,15],[0]),([2,33,26,3,4,5,6,8,12],[2,4,6,46,71],[0,2]),([2,33,26,3,4,5,6,11,12],[2,3,4,46,92],[0,2]),([2,33,26,3,4,5,6,12],[2,4,45,46,47],[0]),([2,33,26,3,4,5,8,11],[2,3,4,46,72],[0,2]),([2,33,26,3,4,34,6,11],[2,3,4,45],[0,2]),([2,26,3,4,5,34,6,17],[0,4,12,45,46],[0]),([2,26,3,4,5,38,6,8],[4,69],[0]),([2,26,3,4,5,6,8,12],[4,41,46,80,91],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_1Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_1Pools rootNAutos rootNBucket7 8 rootNBlock8_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_1Mem : ∀ ns ∈ rootNBlock8_1, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_1Ok
def rootNBlock8_2Specs : List PoolSpec := [(28,[]),(24,[]),(17,[]),(6,[(1,0,1),(1,0,6),(2,7,2)]),(29,[]),(38,[]),(23,[]),(16,[]),(15,[(1,0,2),(1,0,5),(1,2,5)]),(3,[(1,0,2),(1,0,5),(1,2,5)]),(13,[]),(15,[(1,0,2),(1,0,5)]),(15,[(1,0,2),(1,33,5)]),(15,[(1,0,2)]),(4,[(1,0,2),(1,0,6),(1,2,6)])]
def rootNBlock8_2Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock8_2Specs
def rootNBlock8_2 : List NodeSpec := [([2,3,4,5,10,6,8],[0,2,3],[0]),([2,3,4,5,38,29,6,8],[4,12],[0,1]),([33,26,3,4,5,34,6,16],[0,4,6,10,11],[0,2]),([33,26,3,4,5,8,16],[1,4,5,6,13,14],[0,2]),([33,26,3,4,34,14,6],[4,7,8,9,10],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_2Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_2Pools rootNAutos rootNBucket7 8 rootNBlock8_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_2Mem : ∀ ns ∈ rootNBlock8_2, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_2Ok
def rootNNodes8 : List NodeSpec := rootNBlock8_0 ++ rootNBlock8_1 ++ rootNBlock8_2
def rootNBucket8 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 8 xs.toFinset) rootNBucket8 := buildBucketsBT_of_mem (forall_append (forall_append rootNBlock8_0Mem rootNBlock8_1Mem) rootNBlock8_2Mem)
def rootNBlock9_0Specs : List PoolSpec := [(28,[]),(17,[(1,5,6)]),(24,[]),(17,[]),(6,[(1,0,1),(1,0,6),(2,7,2)]),(16,[(1,5,6)]),(29,[]),(33,[]),(31,[]),(15,[]),(7,[(1,0,1),(1,0,6)]),(15,[(1,2,5)]),(38,[]),(8,[(1,2,5),(1,14,6)]),(37,[]),(4,[(1,0,6),(1,2,6),(1,5,8)]),(21,[]),(8,[(1,2,6),(1,5,16)]),(12,[(1,5,16)]),(4,[(1,0,6),(1,2,8),(1,5,8)]),(21,[(1,5,17)]),(4,[(1,0,6),(1,2,8),(3,5,17)]),(23,[]),(11,[(1,0,1),(1,7,2)]),(26,[]),(7,[(1,0,1),(2,26,5)]),(8,[(1,7,2),(2,26,5)]),(16,[]),(10,[(1,0,1),(1,9,5)]),(34,[]),(6,[(1,0,1),(2,7,2)]),(7,[(1,0,1),(1,5,6)]),(6,[(1,0,1),(1,7,14)]),(16,[(1,2,5)]),(6,[(1,0,1),(2,7,14)]),(4,[(1,2,5),(1,2,6)]),(8,[(1,2,5),(1,2,6)]),(6,[(1,0,1),(1,2,6)]),(6,[(1,0,1),(1,14,6)]),(4,[(1,2,5),(1,14,6)]),(7,[(1,0,1),(1,14,6)]),(4,[(1,2,6),(1,5,6)]),(8,[(1,2,6),(1,5,6)]),(4,[(1,2,6),(1,5,16)]),(4,[(1,2,6),(3,5,16)]),(8,[(1,2,6),(3,5,16)]),(13,[]),(35,[]),(25,[]),(6,[(1,0,2),(1,33,6)]),(36,[]),(18,[(1,0,2)]),(5,[(1,0,2),(1,0,5)]),(19,[]),(3,[(1,0,2),(1,0,5),(1,33,6)]),(3,[(1,0,2),(1,0,5),(2,33,6)]),(22,[]),(15,[(1,0,2),(1,33,5)]),(12,[(1,0,2)]),(15,[(1,0,2)]),(5,[(1,0,2),(1,33,5)]),(19,[(1,33,5)]),(7,[(1,0,6),(1,5,8)]),(21,[(1,33,5)]),(3,[(1,0,2),(1,0,6),(1,33,5)]),(6,[(1,0,2),(1,0,6)]),(3,[(1,0,2),(1,0,6),(2,33,5)]),(1,[(1,0,2),(1,0,6),(2,33,5)]),(5,[(1,0,2),(2,33,5)]),(5,[(1,0,2),(1,33,11)]),(8,[(1,5,6),(1,33,11)]),(3,[(1,0,2),(1,0,6),(3,5,8)]),(1,[(1,0,2),(1,0,6),(3,5,8)]),(7,[(1,0,6),(3,5,8)]),(3,[(1,0,2),(1,33,5)]),(13,[(1,33,5)]),(14,[(1,33,5)]),(4,[(1,0,2),(1,33,6)]),(7,[(1,1,33),(1,33,6)]),(6,[(1,0,2),(1,1,33)]),(7,[(1,1,33),(2,26,5)]),(13,[(1,5,6)]),(7,[(1,1,33),(1,5,6)]),(3,[(1,0,2),(1,33,5),(1,33,6)]),(7,[(1,33,5),(1,33,6)]),(3,[(1,0,2),(1,33,5),(1,5,6)]),(20,[]),(7,[(1,33,5),(1,5,6)]),(4,[(1,0,2),(1,33,5),(1,38,6)]),(3,[(1,0,2),(1,33,5),(1,38,6)]),(7,[(1,33,5),(1,38,6)]),(6,[(1,0,2),(1,38,6)]),(8,[(1,33,5),(1,38,6)]),(3,[(1,0,2),(1,33,5),(2,38,6)]),(3,[(1,0,2),(2,33,5),(1,41,6)]),(1,[(1,0,2),(2,33,5),(1,41,6)]),(6,[(1,0,2),(1,41,6)]),(3,[(1,0,2),(1,33,6),(1,5,6)]),(7,[(1,33,6),(1,5,6)]),(4,[(1,0,2),(1,33,6),(1,5,17)]),(19,[(1,5,17)]),(7,[(1,33,6),(1,5,17)]),(3,[(1,0,2),(1,33,6),(3,5,17)]),(7,[(1,33,6),(3,5,17)]),(1,[(1,0,2),(1,33,6),(1,5,6)]),(8,[(1,33,6),(1,5,6)]),(0,[(1,0,2),(1,33,6),(1,5,17)]),(8,[(1,33,6),(1,5,17)]),(1,[(1,0,2),(1,33,6),(3,5,17)]),(8,[(1,33,6),(3,5,17)]),(5,[(1,0,2),(3,5,17)]),(3,[(1,0,2),(2,33,6),(1,36,5)]),(5,[(1,0,2),(1,36,5)]),(4,[(1,0,2),(1,5,6),(1,33,11)]),(6,[(1,0,2),(1,33,11)]),(7,[(1,5,6),(1,33,11)]),(0,[(1,0,2),(1,5,6),(1,33,11)]),(3,[(1,0,2),(1,5,6),(2,33,11)]),(3,[(1,0,2),(1,5,6),(3,33,11)]),(7,[(1,5,6),(3,33,11)]),(18,[]),(19,[(1,5,8)]),(3,[(1,0,6),(1,2,6),(1,5,8)]),(6,[(1,0,6),(1,2,6)]),(3,[(1,0,6),(1,2,6),(3,5,8)]),(1,[(1,0,6),(1,2,6),(3,5,8)]),(3,[(1,0,6),(1,2,8),(1,5,8)]),(6,[(1,0,6),(1,2,8)]),(18,[(1,2,8)]),(3,[(1,0,6),(1,2,8),(3,5,17)]),(3,[(1,0,6),(3,2,8),(1,55,5)]),(1,[(1,0,6),(3,2,8),(1,55,5)]),(7,[(1,0,6),(1,55,5)]),(6,[(1,0,6),(3,2,8)])]
def rootNBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 8 rootNW rootNR rootNSlices rootNBlock9_0Specs
def rootNBlock9_0 : List NodeSpec := [([50,0,1,2,3,4,5,6,11],[6,9,51,117],[0,3]),([36,1,2,3,4,5,34,6],[6,22,52,55],[0]),([32,0,7,2,3,4,5,6],[6,11,27],[]),([47,0,1,2,3,4,5,6],[6,9,60,93],[]),([15,0,2,3,4,5,14,6],[6,11,33,34],[0,1]),([41,1,2,3,4,5,6,8],[9,16,22,65,66,67,68],[0]),([27,0,2,33,3,4,5,6],[6,9,27,46,47,79,80],[0,2]),([27,0,2,3,4,5,6],[6,9,23,24,25,26],[]),([39,0,1,2,3,4,5,16],[6,16,73,123,124,125],[0,2]),([39,1,2,33,3,4,5,6],[6,16,65,71,72,73],[0]),([24,0,7,2,3,4,5,6],[0,6,37,44,45],[0]),([25,0,1,2,33,3,4,5,6],[6,12,16,49,53,102,103],[0,2]),([25,0,1,2,3,4,5,6],[6,49,102,103,108,109,110],[3]),([25,0,1,2,3,4,5,6,8],[12,21,22,53,127,129],[0,1,3]),([25,0,1,2,3,4,5,6,17],[12,16,22,49,53,102,108],[0,2,3]),([51,0,1,2,33,3,4,5,6],[2,6,51,118,119],[0,2]),([9,0,2,3,4,5,6,11],[1,5,6,9,30,31],[0]),([9,2,3,4,5,6,8],[3,4,8,9,10],[0]),([0,1,2,33,3,4,5,6,17,19],[6,12,20,51,99,100,101],[0,2]),([0,1,2,33,3,4,5,6,11,19],[6,12,14,50,51,69,70,113,114,115],[0,1,2,3,4]),([0,1,2,33,3,4,5,6,19],[6,12,51,60,89,90],[0,2]),([0,1,2,33,3,4,5,17,11],[6,12,16,49,51,53,97,98],[0,1,2,3,4]),([0,1,2,33,3,4,38,6,11],[6,51,56,58,60,85,86,87],[0,2]),([0,1,2,3,4,5,49,6],[6,9,111,112],[]),([0,1,2,3,4,5,56,6],[6,16,130,131,132,133],[]),([0,1,2,3,4,5,38,6,17],[6,12,58,60,61,63,83,84],[0]),([0,1,2,3,4,5,38,6,19],[6,60,89],[0,1,2,3,4]),([0,1,2,3,4,5,6,48],[22,94,95,96],[]),([0,1,2,3,4,5,6,8,17,19],[6,7,12,14,20,100],[0]),([0,1,2,3,4,5,6,17,12],[6,12,14,16,19,62,121,126,127,128],[0,2,3,4]),([0,1,2,3,4,5,6,17,19],[6,12,20,49,99,100,101,106,107],[0,2,3]),([0,1,2,3,4,5,6,11,19],[6,14,50,51,70,113,115,116],[0,3]),([0,1,2,3,4,5,6,19],[6,60,88,89,90,91,92],[0,2,3]),([0,1,2,3,4,5,8,16,12],[6,14,15,16,62,120,121,122,123],[0,2,4]),([0,1,2,3,4,5,17,11],[6,16,49,53,97,98,104,105],[0,1,3,4]),([0,7,2,3,4,5,14,6,18],[0,2,6,11,38],[0]),([0,7,2,3,4,5,6,16,18],[0,2,6,17,18,37,43],[0]),([0,7,2,3,4,5,6,18],[0,2,6,11,13,38,39,40],[0]),([0,7,2,3,4,5,16,11],[0,2,6,9,31,37,41,42],[0]),([0,7,3,4,5,14,6,16],[0,6,11,35,36,37],[0]),([0,2,33,26,3,4,5,6,11],[2,5,6,59,81,82],[0,2]),([0,2,26,3,4,5,38,6],[6,24,57,74,75,76],[0,2]),([0,2,26,3,4,5,6,17],[0,6,12,22,48,59,77,78],[0,2]),([0,2,3,4,5,10,6],[0,3,27,28,29,30],[0]),([0,2,3,4,5,14,29,6],[6,11,27,32],[0,1]),([0,2,3,4,5,38,29,6],[6,57,74],[0,1,2,3,4]),([1,2,33,3,4,5,34,6,17],[6,12,16,22,52,53,54],[0,1]),([1,2,33,3,4,5,38,6,8],[6,22,56,58,60,63,64],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_0Pools rootNAutos rootNBucket8 9 rootNBlock9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_0Mem : ∀ ns ∈ rootNBlock9_0, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_0Ok
def rootNBlock9_1Specs : List PoolSpec := [(28,[]),(17,[]),(29,[]),(15,[]),(7,[(1,0,1),(1,0,6)]),(15,[(1,2,5)]),(21,[(1,2,5)]),(38,[]),(6,[(1,0,1),(1,0,6),(1,2,6)]),(6,[(1,0,1),(1,0,6),(1,2,8)]),(37,[]),(4,[(1,0,6),(1,2,5)]),(6,[(1,0,1),(1,0,6)]),(21,[]),(4,[(1,0,6),(1,2,6)]),(15,[(1,2,8)]),(4,[(1,0,6),(1,2,8)]),(23,[]),(26,[]),(16,[]),(9,[(1,2,5)]),(8,[(1,2,6)]),(3,[(1,0,2),(1,0,5),(1,2,5)]),(13,[]),(12,[(1,0,2),(1,0,5)]),(25,[]),(3,[(1,0,2),(1,0,5)]),(19,[(1,0,5)]),(5,[(1,0,2),(1,0,5),(1,2,5)]),(6,[(1,0,2),(1,33,6)]),(1,[(1,0,2),(1,0,5),(1,2,5)]),(6,[(1,0,2)]),(18,[(1,0,2)]),(6,[(1,0,2),(1,2,6)]),(5,[(1,0,2),(1,0,5)]),(3,[(1,0,2),(1,0,5),(1,2,6)]),(1,[(1,0,2),(1,0,5),(1,2,6)]),(19,[]),(3,[(1,0,2),(1,0,5),(1,33,6)]),(1,[(1,0,2),(1,0,5),(1,33,6)]),(7,[(1,0,5),(1,33,6)]),(22,[]),(15,[(1,0,2)]),(4,[(1,0,2),(1,0,6),(1,2,6)]),(4,[(1,0,2),(1,0,6)]),(6,[(1,0,2),(1,0,6),(1,1,33)]),(5,[(1,0,2),(1,33,5)]),(6,[(1,0,2),(1,0,6),(1,2,6)]),(7,[(1,0,6),(1,5,8)]),(3,[(1,0,2),(1,0,6),(1,2,6)]),(3,[(1,0,2),(1,0,6),(1,33,5)]),(1,[(1,0,2),(1,0,6),(1,33,5)]),(6,[(1,0,2),(1,0,6)]),(7,[(1,0,6),(1,33,5)]),(3,[(1,0,2),(1,0,6),(1,5,6)]),(1,[(1,0,2),(1,0,6),(1,5,6)]),(7,[(1,0,6),(1,5,6)]),(4,[(1,0,2),(1,0,6),(1,5,8)]),(3,[(1,0,2),(1,0,6),(1,5,8)]),(3,[(1,0,2),(1,5,6),(1,0,11)]),(7,[(1,5,6),(1,0,11)]),(1,[(1,0,2),(1,5,6),(1,0,11)])]
def rootNBlock9_1Pools : BT (Option BoundPool) := buildPoolsBT 6 rootNW rootNR rootNSlices rootNBlock9_1Specs
def rootNBlock9_1 : List NodeSpec := [([1,2,33,3,4,5,6,8,12],[2,10,13,32,48,52,57,58],[0,2]),([1,2,33,3,4,5,6,11,12],[2,10,13,32,59,60,61],[0,2,3,4]),([1,2,33,3,4,5,8,11],[2,3,13,32,52,54,55,56],[0,1,2,3]),([1,2,3,4,5,34,6,17],[2,13,27,29,34,38,39,40],[0,1]),([1,2,3,4,5,38,6,8],[2,3,17,41,46,50,51,52,53],[0,1]),([1,33,3,4,5,34,6,16],[2,17,27,33,34,35,36,37],[0,1,4]),([1,33,3,4,5,8,16],[3,13,17,21,37,43,47,49],[0,2,3]),([1,33,3,4,34,14,6],[2,20,22,23,28,30,31],[0,1,4]),([7,2,3,4,5,14,6,8],[1,2,4,5,6,11,12],[0,1]),([7,2,3,4,5,6,8,17],[4,7,9,13,15,16,17],[0,1]),([7,2,3,4,5,8,16],[0,3,4,8,13,14],[0,1]),([2,33,26,3,4,5,34,6],[2,17,18,19,23,24,26],[0]),([2,33,26,3,4,5,6,8],[17,19,25,42,44,45],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_1Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_1Pools rootNAutos rootNBucket8 9 rootNBlock9_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_1Mem : ∀ ns ∈ rootNBlock9_1, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_1Ok
def rootNNodes9 : List NodeSpec := rootNBlock9_0 ++ rootNBlock9_1
def rootNBucket9 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 9 xs.toFinset) rootNBucket9 := buildBucketsBT_of_mem (forall_append rootNBlock9_0Mem rootNBlock9_1Mem)
def rootNBlock10_0Specs : List PoolSpec := [(28,[]),(17,[]),(29,[]),(15,[]),(7,[(1,0,1),(1,0,6)]),(15,[(1,2,5)]),(14,[(1,2,5)]),(38,[]),(6,[(1,0,1),(1,0,6)]),(21,[]),(4,[(1,0,6),(1,2,6)]),(4,[(1,0,6),(1,2,8)]),(23,[]),(4,[(1,0,6)]),(26,[]),(9,[(1,7,2)]),(7,[(1,0,1)]),(4,[(1,7,2)]),(16,[]),(6,[(1,0,1),(2,7,2)]),(6,[(1,0,1),(1,2,6)]),(3,[(1,2,5)]),(9,[(1,2,5)]),(4,[(1,2,5)]),(6,[(1,0,1)]),(4,[(1,2,6)]),(8,[(1,2,6)]),(8,[]),(13,[]),(3,[(1,0,2),(1,0,5)]),(6,[(1,0,2),(1,33,6)]),(6,[(1,0,2)]),(18,[(1,0,2)]),(5,[(1,0,2),(1,0,5)]),(19,[]),(7,[(1,0,5)]),(1,[(1,0,2),(1,0,5)]),(22,[]),(15,[(1,0,2)]),(4,[(1,0,2),(1,0,6)]),(5,[(1,0,2),(1,33,5)]),(6,[(1,0,2),(1,0,6)]),(3,[(1,0,2),(1,0,6)]),(7,[(1,0,6)]),(5,[(1,0,2)]),(3,[(1,0,2),(1,33,5)]),(4,[(1,0,2),(1,33,6)]),(6,[(1,0,2),(1,1,33)]),(4,[(1,0,2)]),(3,[(1,0,2)]),(7,[(1,1,33)]),(20,[]),(7,[(1,33,5)]),(1,[(1,0,2),(1,33,5)]),(8,[(1,33,5)]),(3,[(1,0,2),(2,33,5)]),(1,[(1,0,2),(2,33,5)]),(3,[(1,0,2),(1,33,6)]),(7,[(1,33,6)]),(8,[(1,33,6)]),(3,[(1,0,2),(2,33,6)]),(1,[(1,0,2),(2,33,6)]),(3,[(1,0,2),(1,5,6)]),(7,[(1,5,6)]),(8,[(1,5,6)]),(1,[(1,0,2),(1,5,6)]),(18,[]),(6,[(1,0,6),(1,2,6)]),(3,[(1,0,6),(1,2,6)]),(6,[(1,0,6),(1,2,8)]),(3,[(1,0,6),(1,2,8)]),(3,[(1,0,6),(3,2,8)]),(1,[(1,0,6),(3,2,8)])]
def rootNBlock10_0Pools : BT (Option BoundPool) := buildPoolsBT 7 rootNW rootNR rootNSlices rootNBlock10_0Specs
def rootNBlock10_0 : List NodeSpec := [([36,0,1,2,3,4,5,6],[3,12,44,51,60,61],[0,2,3]),([41,0,1,2,3,4,5,6],[3,12,31,55,56],[0,2]),([9,0,2,3,4,5,6],[1,3,16,18,19],[0]),([55,0,1,2,3,4,5,6],[9,43,66,71,72],[0,1,3]),([0,1,2,33,3,4,5,38,6],[2,12,37,40,45,51,52],[0,2,3]),([0,1,2,33,3,4,5,6,17],[7,9,12,30,34,44,46,57,58],[0,2,3]),([0,1,2,33,3,4,5,6,11],[2,3,12,31,32,44,62,63,64,65,66],[0,1,2,3,4]),([0,1,2,3,4,5,38,6],[2,3,12,31,37,40,45,51,52,53,54],[0,2,3]),([0,1,2,3,4,5,6,8,17],[7,9,11,12,34,43,69,70],[0,1,3,4]),([0,1,2,3,4,5,6,17],[9,12,30,34,44,46,57,58,59],[0,2,3]),([0,1,2,3,4,5,8,16],[9,10,26,34,43,67,68],[0,1,2,3,4]),([0,7,2,3,4,5,14,6],[2,3,5,6,16,18,21,22,23,24],[0,1]),([0,7,2,3,4,5,6,16],[0,3,16,20,25,26],[0,1]),([0,2,33,26,3,4,5,6],[12,14,18,28,38,47,48,49,50],[0,2,3]),([0,2,26,3,4,5,6],[3,15,16,17],[0]),([1,2,33,3,4,5,34,6],[2,12,27,29,31,33,35,36,37],[0,1]),([1,2,33,3,4,5,6,8],[3,9,12,39,41,42,43,44],[0,1,2,3]),([7,2,3,4,5,6,8],[1,3,4,8,9,13],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock10_0Pools rootNAutos rootNBucket9 10 rootNBlock10_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_0Mem : ∀ ns ∈ rootNBlock10_0, Impossible rootNG 10 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket9Ok rootNBlock10_0Ok
def rootNNodes10 : List NodeSpec := rootNBlock10_0
def rootNBucket10 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 10 xs.toFinset) rootNBucket10 := buildBucketsBT_of_mem rootNBlock10_0Mem
def rootNBlock11_0Specs : List PoolSpec := [(17,[]),(15,[]),(21,[]),(23,[]),(4,[(1,0,6)]),(7,[(1,0,1)]),(6,[(1,0,1)]),(3,[]),(8,[]),(4,[]),(6,[(1,0,2)]),(7,[(1,0,6)]),(5,[(1,0,2)]),(4,[(1,0,2)]),(3,[(1,0,2)]),(7,[]),(3,[(1,0,6)]),(5,[]),(6,[(1,0,6)])]
def rootNBlock11_0Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock11_0Specs
def rootNBlock11_0 : List NodeSpec := [([0,1,2,33,3,4,5,6],[3,8,10,12,13,14,15],[0,2,3]),([0,1,2,3,4,5,6,8],[2,4,8,11,16,17,18],[0,1,2,3,4]),([0,7,2,3,4,5,6],[0,1,5,6,7,8,9],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock11_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock11_0Pools rootNAutos rootNBucket10 11 rootNBlock11_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock11_0Mem : ∀ ns ∈ rootNBlock11_0, Impossible rootNG 11 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket10Ok rootNBlock11_0Ok
def rootNNodes11 : List NodeSpec := rootNBlock11_0
def rootNBucket11 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket11Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 11 xs.toFinset) rootNBucket11 := buildBucketsBT_of_mem rootNBlock11_0Mem
def rootNBlock12_0Specs : List PoolSpec := [(3,[]),(8,[]),(4,[]),(7,[]),(5,[]),(6,[])]
def rootNBlock12_0Pools : BT (Option BoundPool) := buildPoolsBT 3 rootNW rootNR rootNSlices rootNBlock12_0Specs
def rootNBlock12_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,3,4,5],[0,1,2,3,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock12_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock12_0Pools rootNAutos rootNBucket11 12 rootNBlock12_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock12_0Mem : ∀ ns ∈ rootNBlock12_0, Impossible rootNG 12 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket11Ok rootNBlock12_0Ok
def rootNNodes12 : List NodeSpec := rootNBlock12_0
def rootNBucket12 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket12Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 12 xs.toFinset) rootNBucket12 := buildBucketsBT_of_mem rootNBlock12_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBound : Lower rootNR rootNG 13 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,16,18),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,1,33),(VAR 6,1,65)]) (by decide +kernel) rootNBucket12Ok (by decide +kernel)

end Small
namespace Relate
def insertRow (r : Small.Row) : Wide.Row :=
  ⟨(0 + ((r.val / 1) % 2) * 1 + ((r.val / 2) % 2) * 4 + ((r.val / 4) % 2) * 8 + ((r.val / 8) % 2) * 16 + ((r.val / 16) % 2) * 32 + ((r.val / 32) % 2) * 64 + ((r.val / 64) % 2) * 128) % 256, Nat.mod_lt _ (by decide)⟩
def project (w : Wide.Wire) : Small.Wire := fun r => w (insertRow r)
lemma avail {b : List Wide.Wire} {v : Wide.Wire} (h : Wide.Avail b v) :
    Small.Avail (b.map project) (project v) := by
  rcases h with h | ⟨k, rfl⟩ | h
  · exact Or.inl (List.mem_map_of_mem h)
  · exact Or.inr (Or.inl ⟨k,rfl⟩)
  · exact Or.inr (Or.inr (List.mem_map_of_mem (f := project) h))
lemma reach {roots b : List Wide.Wire} {n : Nat} (h : Wide.Reach roots n b) :
    Small.Reach (roots.map project) n (b.map project) := by
  induction n generalizing b with
  | zero => change b = roots at h; rw [h]; rfl
  | succ n ih =>
    obtain ⟨op,bank,a,b,hr,ha,hb,rfl⟩ := h
    refine ⟨op, bank.map project, project a, project b, ih hr, avail ha, avail hb, ?_⟩
    cases op <;> rfl
lemma liftPins : Wide.Lower (Wide.varsOf 255) 0xfffffffffffffffffffffffffffffffeffffffffffffffeefffefffeffaaaa00 14 := by
  have bound : Wide.Lower (Wide.varsOf 253) 0xfffffffffffffffffffffffffffffffaffffffffffffffaafffafffaffaaaa00 13 := by
    intro n bank hr ha
    have proots : (((Wide.varsOf 253).map Wide.obs).map project) = (Small.varsOf 127).map Small.obs := by
      change [_,_,_,_,_,_,_] = [_,_,_,_,_,_,_]
      repeat' apply congrArg₂ List.cons
      all_goals first | rfl | funext r; revert r; decide +kernel
    have target : project (Wide.obs 0xfffffffffffffffffffffffffffffffaffffffffffffffaafffafffaffaaaa00) = Small.obs 0xfffffffffffffffefffffffafefefaa0 := by funext r; revert r; decide +kernel
    have r := reach hr
    have a := avail ha
    rw [proots] at r
    rw [target] at a
    exact Small.rootNBound n _ r a
  exact Wide.lift_of (z := 2) (o := 0) (essPairs := [(Wide.VAR 1,32,34)]) (by decide +kernel) bound
end Relate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
def onWit : List Gate := [⟨.or, [5, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [7, 5]⟩, ⟨.or, [11, 8]⟩, ⟨.and, [6, 10]⟩, ⟨.and, [8, 11]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [19, 21]⟩]

theorem onWitBasis : ∀ g ∈ onWit,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [onWit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem onWitCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨onWit, 22⟩ (List.ofFn x) = f x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem onGraphCorrect : ∀ x : Fin 8 → Bool, f x = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

theorem onFinal :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfit _hone hev
  have hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y := fun y => (hev y).trans (onGraphCorrect y).symm
  have hrow : ∀ r : Wide.Row, f (Wide.evalInput r) = (0xfffffffffffffffffffffffffffffffeffffffffffffffeefffefffeffaaaa00 : Nat).testBit r.val := by decide +kernel
  have hw : ∀ r : Wide.Row, Circuit.eval ⟨onWit, 22⟩ (List.ofFn (Wide.evalInput r)) = (0xfffffffffffffffffffffffffffffffeffffffffffffffeefffefffeffaaaa00 : Nat).testBit r.val :=
    fun r => (onWitCorrect (Wide.evalInput r)).trans (hrow r)
  obtain ⟨gs, out, hg, hlen, hev⟩ := Wide.replace_of_lower (0xfffffffffffffffffffffffffffffffeffffffffffffffeefffefffeffaaaa00 : Nat) (by decide) (by decide) (by decide)
    14 Relate.liftPins onWit 22 (by decide) onWitBasis f hrow hw gates o hfit hf
  exact ⟨gs, out, hg, hlen, fun x => (hev x).trans (onGraphCorrect x)⟩
end PEqualNP.Outside.L_meta_52854

theorem PEqualNP.Outside.L_meta_52854 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_52854.onFinal
