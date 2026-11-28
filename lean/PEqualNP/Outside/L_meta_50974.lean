import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50974_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

def inp (t : Fin 6) : List Bool :=
  (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]

def initMasks : List Nat := [62, 60, 56, 48, 32, 0, 63]

lemma initMasks_spec (t : Fin 6) :
    initMasks.map (fun m => m.testBit t.val) = inp t := by
  fin_cases t <;> decide

lemma initMasks_lt64 : ∀ m ∈ initMasks, m < 64 := by
  intro m hm
  simp only [initMasks, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

def gateMask (ws : List Nat) (g : Gate) : Nat :=
  match g.op with
  | .and => match g.inputs with
    | [] => 63
    | [i] => ws.getD i 0
    | i :: j :: _ => (ws.getD i 0) &&& (ws.getD j 0)
  | .or => match g.inputs with
    | [] => 0
    | [i] => ws.getD i 0
    | i :: j :: _ => (ws.getD i 0) ||| (ws.getD j 0)
  | .not => match g.inputs with
    | [] => 63
    | i :: _ => 63 ^^^ (ws.getD i 0)
  | _ => 0

def runMasks (gs : List Gate) (ws : List Nat) : List Nat :=
  gs.foldl (fun w g => w ++ [gateMask w g]) ws

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

lemma readBit (ws : List Nat) (i k : Nat) :
    (ws.map (fun m => m.testBit k)).getD i false = (ws.getD i 0).testBit k := by
  by_cases h : i < ws.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h)]

lemma testBit_63 (t : Fin 6) : (63 : Nat).testBit t.val = true := by
  fin_cases t <;> decide

lemma gateMask_bit (ws : List Nat) (g : Gate) (hg : legal g) (t : Fin 6) :
    (gateMask ws g).testBit t.val =
      g.op.eval (g.inputs.map fun i => (ws.map (fun m => m.testBit t.val)).getD i false) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  have h63 := testBit_63 t
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tl⟩⟩⟩ <;> simp at hlen
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [gateMask, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      List.any_cons, List.any_nil, List.headD_cons, List.headD_nil, id_eq, readBit,
      Bool.and_true, Bool.or_false, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      Nat.zero_testBit, h63, Bool.true_xor, Bool.not_false]

lemma runMasks_map (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (ws : List Nat) (t : Fin 6) :
    (runMasks gs ws).map (fun m => m.testBit t.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws.map (fun m => m.testBit t.val)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [runMasks, List.foldl_cons]
    have h1 := gateMask_bit ws g (hg g List.mem_cons_self) t
    have h2 := ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (ws ++ [gateMask ws g])
    simp only [runMasks, List.map_append, List.map_cons, List.map_nil, h1] at h2 ⊢
    exact h2

lemma runMasks_len (gs : List Gate) (ws : List Nat) :
    (runMasks gs ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp [runMasks]
  | cons g gs ih =>
    simp only [runMasks, List.foldl_cons, List.length_cons]
    have := ih (ws ++ [gateMask ws g])
    simp only [runMasks, List.length_append, List.length_singleton] at this
    omega

lemma nat_lt64_of_testBit {a : Nat} (ha : ∀ k ≥ 6, a.testBit k = false) : a < 64 := by
  by_contra h
  have hge : 64 ≤ a := Nat.le_of_not_lt h
  have hne : a >>> 6 ≠ 0 := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero hne
  rw [Nat.testBit_shiftRight] at hj
  have := ha (6 + j) (by omega)
  rw [this] at hj; exact Bool.noConfusion hj

lemma testBit_ge6_of_lt64 {a : Nat} (ha : a < 64) {k : Nat} (hk : 6 ≤ k) : a.testBit k = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (show a < 2 ^ 6 by omega) (Nat.pow_le_pow_right (by omega) hk))

lemma lt64_and {a b : Nat} (ha : a < 64) : a &&& b < 64 := by
  apply nat_lt64_of_testBit; intro k hk
  simp [Nat.testBit_and, testBit_ge6_of_lt64 ha hk]

lemma lt64_or {a b : Nat} (ha : a < 64) (hb : b < 64) : a ||| b < 64 := by
  apply nat_lt64_of_testBit; intro k hk
  simp [Nat.testBit_or, testBit_ge6_of_lt64 ha hk, testBit_ge6_of_lt64 hb hk]

lemma lt64_xor63 {a : Nat} (ha : a < 64) : 63 ^^^ a < 64 := by
  apply nat_lt64_of_testBit; intro k hk
  simp [Nat.testBit_xor, testBit_ge6_of_lt64 (by omega : 63 < 64) hk, testBit_ge6_of_lt64 ha hk]

lemma getD_mem_or_zero {ws : List Nat} {i : Nat} : ws.getD i 0 = 0 ∨ ws.getD i 0 ∈ ws := by
  by_cases h : i < ws.length
  · right; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · left; exact List.getD_eq_default _ _ (Nat.le_of_not_gt h)

lemma gateMask_lt64 {ws : List Nat} (hws : ∀ m ∈ ws, m < 64) (g : Gate) : gateMask ws g < 64 := by
  have hget : ∀ i, ws.getD i 0 < 64 := fun i => by
    rcases getD_mem_or_zero (ws := ws) (i := i) with h | h
    · rw [h]; omega
    · exact hws _ h
  obtain ⟨op, args⟩ := g
  cases op
  · rcases args with _ | ⟨i, _ | ⟨j, _⟩⟩
    · simp [gateMask]
    · exact hget i
    · exact lt64_and (hget i)
  · rcases args with _ | ⟨i, _ | ⟨j, _⟩⟩
    · simp [gateMask]
    · exact hget i
    · exact lt64_or (hget i) (hget j)
  · rcases args with _ | ⟨i, _⟩
    · simp [gateMask]
    · exact lt64_xor63 (hget i)
  all_goals simp [gateMask]

lemma runMasks_lt64 (gs : List Gate) {ws : List Nat} (hws : ∀ m ∈ ws, m < 64) :
    ∀ m ∈ runMasks gs ws, m < 64 := by
  induction gs generalizing ws with
  | nil => exact hws
  | cons g gs ih =>
    simp only [runMasks, List.foldl_cons]
    apply ih
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hws m hm
    · rw [List.mem_singleton.mp hm]; exact gateMask_lt64 hws g

lemma eq_of_testBit6 {a b : Nat} (ha : a < 64) (hb : b < 64)
    (h : ∀ t : Fin 6, a.testBit t.val = b.testBit t.val) : a = b := by
  apply Nat.eq_of_testBit_eq; intro k
  by_cases hk : k < 6
  · exact h ⟨k, hk⟩
  · rw [testBit_ge6_of_lt64 ha (by omega), testBit_ge6_of_lt64 hb (by omega)]

def memF (z : Nat) (l : List Nat) : Bool :=
  List.rec false (fun w _ ih => Bool.rec ih true (Nat.beq z w)) l

lemma memF_eq (z : Nat) (l : List Nat) : memF z l = true ↔ z ∈ l := by
  induction l with
  | nil => simp [memF]
  | cons w ws ih =>
    change Bool.rec (memF z ws) true (Nat.beq z w) = true ↔ z ∈ w :: ws
    cases h : Nat.beq z w
    · have hne : z ≠ w := fun e => by subst e; rw [Nat.beq_refl] at h; exact Bool.noConfusion h
      simp [ih, hne]
    · have heq : z = w := Nat.eq_of_beq_eq_true h
      simp [heq]

def allF (p : Nat → Bool) (l : List Nat) : Bool :=
  List.rec true (fun w _ ih => Bool.rec false ih (p w)) l

lemma allF_spec {p : Nat → Bool} {l : List Nat} (h : allF p l = true) : ∀ w ∈ l, p w = true := by
  induction l with
  | nil => intro w hw; nomatch hw
  | cons x xs ih =>
    change Bool.rec false (allF p xs) (p x) = true at h
    cases hx : p x <;> rw [hx] at h
    · exact Bool.noConfusion h
    · intro w hw; rcases List.mem_cons.mp hw with rfl | hw
      · exact hx
      · exact ih h w hw

def pairsF (f : Nat → Nat → Bool) (l : List Nat) : Bool :=
  List.rec true (fun a rest ih => Bool.rec false ih (allF (fun b => f a b) rest)) l

lemma pairsF_spec {f : Nat → Nat → Bool} {l : List Nat}
    (hsym : ∀ a b, f a b = f b a) (h : pairsF f l = true) :
    ∀ a ∈ l, ∀ b ∈ l, a ≠ b → f a b = true := by
  induction l with
  | nil => intro a ha; nomatch ha
  | cons x xs ih =>
    change Bool.rec false (pairsF f xs) (allF (fun b => f x b) xs) = true at h
    cases hx : allF (fun b => f x b) xs <;> rw [hx] at h
    · exact Bool.noConfusion h
    · intro a ha b hb hab
      rcases List.mem_cons.mp ha with ha0 | ha' <;> rcases List.mem_cons.mp hb with hb0 | hb'
      · exact absurd (ha0.trans hb0.symm) hab
      · rw [ha0]; exact allF_spec hx b hb'
      · rw [hb0, hsym]; exact allF_spec hx a ha'
      · exact ih h a ha' b hb' hab

def b10 (c : Bool) : Nat := Bool.rec 1 0 c

def missF (bank : List Nat) : Nat :=
  Nat.add (Nat.add (b10 (memF 16 bank)) (b10 (memF 18 bank))) (b10 (memF 58 bank))

lemma missF_cons_le (v : Nat) (bank : List Nat) : missF bank ≤ missF (v :: bank) + 1 := by
  unfold missF
  change Nat.add (Nat.add (b10 (memF 16 bank)) (b10 (memF 18 bank))) (b10 (memF 58 bank)) ≤
    Nat.add (Nat.add (b10 (Bool.rec (memF 16 bank) true (Nat.beq 16 v)))
      (b10 (Bool.rec (memF 18 bank) true (Nat.beq 18 v))))
      (b10 (Bool.rec (memF 58 bank) true (Nat.beq 58 v))) + 1
  cases b16 : Nat.beq 16 v <;> cases b18 : Nat.beq 18 v <;> cases b58 : Nat.beq 58 v
  all_goals try (have h1 := Nat.eq_of_beq_eq_true b16; have h2 := Nat.eq_of_beq_eq_true b18; omega)
  all_goals try (have h1 := Nat.eq_of_beq_eq_true b16; have h2 := Nat.eq_of_beq_eq_true b58; omega)
  all_goals try (have h1 := Nat.eq_of_beq_eq_true b18; have h2 := Nat.eq_of_beq_eq_true b58; omega)
  all_goals cases memF 16 bank <;> cases memF 18 bank <;> cases memF 58 bank <;> decide

lemma missF_subset {a b : List Nat} (h : ∀ x ∈ a, x ∈ b) : missF b ≤ missF a := by
  have hc (t : Nat) : memF t a = true → memF t b = true := fun ht =>
    (memF_eq t b).mpr (h t ((memF_eq t a).mp ht))
  have hb (t : Nat) : b10 (memF t b) ≤ b10 (memF t a) := by
    cases ha : memF t a <;> cases hb' : memF t b
    · decide
    · decide
    · exact absurd (hc t ha) (by rw [hb']; decide)
    · decide
  have h1 := hb 16; have h2 := hb 18; have h3 := hb 58
  unfold missF
  change (b10 (memF 16 b) + b10 (memF 18 b)) + b10 (memF 58 b) ≤
    (b10 (memF 16 a) + b10 (memF 18 a)) + b10 (memF 58 a)
  omega

lemma missF_runMasks (gs : List Gate) (ws bank : List Nat) (hcov : ∀ m ∈ ws, m ∈ bank) :
    missF bank ≤ missF (runMasks gs ws) + gs.length := by
  induction gs generalizing ws bank with
  | nil =>
    simp only [runMasks, List.foldl_nil, List.length_nil, Nat.add_zero]
    exact missF_subset hcov
  | cons g gs ih =>
    change missF bank ≤ missF (runMasks gs (ws ++ [gateMask ws g])) + (gs.length + 1)
    have hcov' : ∀ m ∈ ws ++ [gateMask ws g], m ∈ gateMask ws g :: bank := by
      intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · exact List.mem_cons_of_mem _ (hcov m hm)
      · rw [List.mem_singleton.mp hm]; exact List.mem_cons_self
    have h1 := ih (ws ++ [gateMask ws g]) (gateMask ws g :: bank) hcov'
    have h2 := missF_cons_le (gateMask ws g) bank
    omega

def noHitF : Nat → Nat → List Nat → Bool
  | 0, _, bank => Bool.rec true false (Nat.beq (missF bank) 0)
  | r + 1, nots, bank =>
    let m := missF bank
    Bool.rec
      (Bool.rec
        (Bool.rec false
          (pairsF (fun a b =>
            let v1 := Nat.land a b
            let v2 := Nat.lor a b
            Bool.rec false
              (Bool.rec (noHitF r nots (v2 :: bank)) true (memF v2 bank))
              (Bool.rec (noHitF r nots (v1 :: bank)) true (memF v1 bank))) bank)
          (Nat.rec true (fun n _ =>
            allF (fun a =>
              let v := Nat.xor 63 a
              Bool.rec (noHitF r n (v :: bank)) true (memF v bank)) bank) nots))
        true (Nat.blt (Nat.add r 1) m))
      false (Nat.beq m 0)

lemma noHitF_miss_pos {rem nots : Nat} {bank : List Nat} (h : noHitF rem nots bank = true) :
    0 < missF bank := by
  cases rem with
  | zero =>
    unfold noHitF at h
    cases hb : Nat.beq (missF bank) 0 <;> rw [hb] at h
    · have hne : missF bank ≠ 0 := fun e => by rw [e, Nat.beq_refl] at hb; exact Bool.noConfusion hb
      omega
    · exact Bool.noConfusion h
  | succ r =>
    unfold noHitF at h; dsimp only at h
    cases hb : Nat.beq (missF bank) 0 <;> rw [hb] at h
    · have hne : missF bank ≠ 0 := fun e => by rw [e, Nat.beq_refl] at hb; exact Bool.noConfusion hb
      omega
    · exact Bool.noConfusion h

def isNotG (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

def notCountL (gs : List Gate) : Nat :=
  (gs.filter isNotG).length

lemma notCountL_eq (D : Circuit) : notCountL D.gates = notCount D := by
  unfold notCountL notCount
  congr 1; apply List.filter_congr; intro g _
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp [isNotG]

lemma gateMask_cases {ws bank : List Nat} (hcov : ∀ m ∈ ws, m ∈ bank)
    (h0 : 0 ∈ bank) (h63 : 63 ∈ bank) {g : Gate} (hg : legal g) :
    gateMask ws g ∈ bank ∨
    (g.op = .not ∧ ∃ a ∈ bank, gateMask ws g = 63 ^^^ a) ∨
    (∃ a ∈ bank, ∃ b ∈ bank, a ≠ b ∧ (gateMask ws g = a &&& b ∨ gateMask ws g = a ||| b)) := by
  have hget : ∀ i, ws.getD i 0 ∈ bank := fun i => by
    rcases getD_mem_or_zero (ws := ws) (i := i) with h | h
    · rw [h]; exact h0
    · exact hcov _ h
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tl⟩⟩⟩ <;> simp at hlen
  · rcases hop with rfl | rfl | rfl
    · left; exact h63
    · left; exact h0
    · left; exact h63
  · rcases hop with rfl | rfl | rfl
    · left; exact hget i
    · left; exact hget i
    · right; left; exact ⟨rfl, ws.getD i 0, hget i, rfl⟩
  · rcases hop with rfl | rfl | rfl
    · by_cases heq : ws.getD i 0 = ws.getD j 0
      · left; change (ws.getD i 0) &&& (ws.getD j 0) ∈ bank; rw [heq, Nat.and_self]; exact hget j
      · right; right; exact ⟨ws.getD i 0, hget i, ws.getD j 0, hget j, heq, Or.inl rfl⟩
    · by_cases heq : ws.getD i 0 = ws.getD j 0
      · left; change (ws.getD i 0) ||| (ws.getD j 0) ∈ bank; rw [heq, Nat.or_self]; exact hget j
      · right; right; exact ⟨ws.getD i 0, hget i, ws.getD j 0, hget j, heq, Or.inr rfl⟩
    · right; left; exact ⟨rfl, ws.getD i 0, hget i, rfl⟩

lemma noHitF_sound : ∀ (gs : List Gate) (rem nots : Nat) (bank ws : List Nat),
    noHitF rem nots bank = true →
    gs.length ≤ rem →
    notCountL gs ≤ nots →
    (∀ g ∈ gs, legal g) →
    0 ∈ bank → 63 ∈ bank →
    (∀ m ∈ ws, m ∈ bank) →
    ¬ (16 ∈ runMasks gs ws ∧ 18 ∈ runMasks gs ws ∧ 58 ∈ runMasks gs ws) := by
  intro gs
  induction gs with
  | nil =>
    intro rem nots bank ws hnh _ _ _ _ _ hcov ⟨h16, h18, h58⟩
    have hmpos := noHitF_miss_pos hnh
    have h16' : memF 16 bank = true := (memF_eq 16 bank).mpr (hcov 16 h16)
    have h18' : memF 18 bank = true := (memF_eq 18 bank).mpr (hcov 18 h18)
    have h58' : memF 58 bank = true := (memF_eq 58 bank).mpr (hcov 58 h58)
    unfold missF at hmpos; rw [h16', h18', h58'] at hmpos; simp [b10] at hmpos
  | cons g gs ih =>
    intro rem nots bank ws hnh hlen hnot hleg h0 h63 hcov ⟨h16, h18, h58⟩
    have hg := hleg g List.mem_cons_self
    have hgs := fun x hx => hleg x (List.mem_cons_of_mem _ hx)
    have hnot_tail : notCountL gs ≤ notCountL (g :: gs) := by
      unfold notCountL; simp only [List.filter_cons]; split <;> simp
    have hhit_tail : 16 ∈ runMasks gs (ws ++ [gateMask ws g]) ∧
        18 ∈ runMasks gs (ws ++ [gateMask ws g]) ∧
        58 ∈ runMasks gs (ws ++ [gateMask ws g]) := ⟨h16, h18, h58⟩
    have hz_hit : missF (runMasks (g :: gs) ws) = 0 := by
      unfold missF
      rw [(memF_eq 16 _).mpr h16, (memF_eq 18 _).mpr h18, (memF_eq 58 _).mpr h58]
      rfl
    rcases gateMask_cases hcov h0 h63 hg with hstay | ⟨hgn, a, ha, hveq⟩ | ⟨a, ha, b, hb, hab, hveq⟩
    · have hcov' : ∀ m ∈ ws ++ [gateMask ws g], m ∈ bank := by
        intro m hm; rcases List.mem_append.mp hm with hm | hm
        · exact hcov m hm
        · rw [List.mem_singleton.mp hm]; exact hstay
      exact ih rem nots bank (ws ++ [gateMask ws g]) hnh (by simp at hlen; omega)
        (le_trans hnot_tail hnot) hgs h0 h63 hcov' hhit_tail
    · by_cases hmem : gateMask ws g ∈ bank
      · have hcov' : ∀ m ∈ ws ++ [gateMask ws g], m ∈ bank := by
          intro m hm; rcases List.mem_append.mp hm with hm | hm
          · exact hcov m hm
          · rw [List.mem_singleton.mp hm]; exact hmem
        exact ih rem nots bank (ws ++ [gateMask ws g]) hnh (by simp at hlen; omega)
          (le_trans hnot_tail hnot) hgs h0 h63 hcov' hhit_tail
      · cases rem with
        | zero => simp at hlen
        | succ r =>
          have hnot_eq : notCountL (g :: gs) = notCountL gs + 1 := by
            unfold notCountL isNotG; simp [hgn]
          cases nots with
          | zero => omega
          | succ n =>
            unfold noHitF at hnh; dsimp only at hnh
            cases hm0 : Nat.beq (missF bank) 0 <;> rw [hm0] at hnh; swap; · exact Bool.noConfusion hnh
            cases hlt : Nat.blt (Nat.add r 1) (missF bank) <;> rw [hlt] at hnh
            · dsimp only at hnh
              cases hnotAll : allF (fun a => let v := Nat.xor 63 a; Bool.rec (noHitF r n (v :: bank)) true (memF v bank)) bank <;> rw [hnotAll] at hnh
              · exact Bool.noConfusion hnh
              · have hstep := allF_spec hnotAll a ha
                dsimp only at hstep
                have hnc : memF (Nat.xor 63 a) bank = false := by
                  cases hc : memF (Nat.xor 63 a) bank
                  · rfl
                  · exact absurd (hveq ▸ (memF_eq _ bank).mp hc) hmem
                rw [hnc] at hstep
                have hcov' : ∀ m ∈ ws ++ [gateMask ws g], m ∈ (Nat.xor 63 a) :: bank := by
                  intro m hm; rcases List.mem_append.mp hm with hm | hm
                  · exact List.mem_cons_of_mem _ (hcov m hm)
                  · rw [List.mem_singleton.mp hm, hveq]; exact List.mem_cons_self
                exact ih r n ((Nat.xor 63 a) :: bank) (ws ++ [gateMask ws g]) hstep (by simp at hlen; omega)
                  (by omega) hgs (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h63) hcov' hhit_tail
            · have hlt' : r + 1 < missF bank := Nat.blt_eq.mp hlt
              have hm := missF_runMasks (g :: gs) ws bank hcov
              rw [hz_hit] at hm; omega
    · by_cases hmem : gateMask ws g ∈ bank
      · have hcov' : ∀ m ∈ ws ++ [gateMask ws g], m ∈ bank := by
          intro m hm; rcases List.mem_append.mp hm with hm | hm
          · exact hcov m hm
          · rw [List.mem_singleton.mp hm]; exact hmem
        exact ih rem nots bank (ws ++ [gateMask ws g]) hnh (by simp at hlen; omega)
          (le_trans hnot_tail hnot) hgs h0 h63 hcov' hhit_tail
      · cases rem with
        | zero => simp at hlen
        | succ r =>
          unfold noHitF at hnh; dsimp only at hnh
          cases hm0 : Nat.beq (missF bank) 0 <;> rw [hm0] at hnh; swap; · exact Bool.noConfusion hnh
          cases hlt : Nat.blt (Nat.add r 1) (missF bank) <;> rw [hlt] at hnh
          · dsimp only at hnh
            have hpa : pairsF (fun a b =>
                let v1 := Nat.land a b
                let v2 := Nat.lor a b
                Bool.rec false
                  (Bool.rec (noHitF r nots (v2 :: bank)) true (memF v2 bank))
                  (Bool.rec (noHitF r nots (v1 :: bank)) true (memF v1 bank))) bank = true := by
              cases nots with
              | zero => exact hnh
              | succ n =>
                dsimp only at hnh
                cases hc : allF (fun a => let v := Nat.xor 63 a; Bool.rec (noHitF r n (v :: bank)) true (memF v bank)) bank <;> rw [hc] at hnh
                · exact Bool.noConfusion hnh
                · exact hnh
            have hsym : ∀ x y,
                Bool.rec (motive := fun _ => Bool) false
                  (Bool.rec (motive := fun _ => Bool) (noHitF r nots (Nat.lor x y :: bank)) true (memF (Nat.lor x y) bank))
                  (Bool.rec (motive := fun _ => Bool) (noHitF r nots (Nat.land x y :: bank)) true (memF (Nat.land x y) bank)) =
                Bool.rec (motive := fun _ => Bool) false
                  (Bool.rec (motive := fun _ => Bool) (noHitF r nots (Nat.lor y x :: bank)) true (memF (Nat.lor y x) bank))
                  (Bool.rec (motive := fun _ => Bool) (noHitF r nots (Nat.land y x :: bank)) true (memF (Nat.land y x) bank)) := by
              intro x y
              have h1 : Nat.land x y = Nat.land y x := Nat.and_comm x y
              have h2 : Nat.lor x y = Nat.lor y x := Nat.or_comm x y
              rw [h1, h2]
            have hpair := pairsF_spec hsym hpa a ha b hb hab
            rcases hveq with hveq | hveq
            · have hnc : memF (Nat.land a b) bank = false := by
                cases hc : memF (Nat.land a b) bank
                · rfl
                · exact absurd (hveq ▸ (memF_eq _ bank).mp hc) hmem
              rw [hnc] at hpair
              cases hs1 : noHitF r nots (Nat.land a b :: bank) <;> rw [hs1] at hpair
              · exact Bool.noConfusion hpair
              · have hcov' : ∀ m ∈ ws ++ [gateMask ws g], m ∈ (Nat.land a b) :: bank := by
                  intro m hm; rcases List.mem_append.mp hm with hm | hm
                  · exact List.mem_cons_of_mem _ (hcov m hm)
                  · rw [List.mem_singleton.mp hm, hveq]; exact List.mem_cons_self
                exact ih r nots ((Nat.land a b) :: bank) (ws ++ [gateMask ws g]) hs1 (by simp at hlen; omega)
                  (le_trans hnot_tail hnot) hgs (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h63) hcov' hhit_tail
            · have hnc : memF (Nat.lor a b) bank = false := by
                cases hc : memF (Nat.lor a b) bank
                · rfl
                · exact absurd (hveq ▸ (memF_eq _ bank).mp hc) hmem
              rw [hnc] at hpair
              cases hs1 : Bool.rec (motive := fun _ => Bool) (noHitF r nots (Nat.land a b :: bank)) true (memF (Nat.land a b) bank) <;> rw [hs1] at hpair
              · exact Bool.noConfusion hpair
              · have hcov' : ∀ m ∈ ws ++ [gateMask ws g], m ∈ (Nat.lor a b) :: bank := by
                  intro m hm; rcases List.mem_append.mp hm with hm | hm
                  · exact List.mem_cons_of_mem _ (hcov m hm)
                  · rw [List.mem_singleton.mp hm, hveq]; exact List.mem_cons_self
                exact ih r nots ((Nat.lor a b) :: bank) (ws ++ [gateMask ws g]) hpair (by simp at hlen; omega)
                  (le_trans hnot_tail hnot) hgs (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h63) hcov' hhit_tail
          · have hlt' : r + 1 < missF bank := Nat.blt_eq.mp hlt
            have hm := missF_runMasks (g :: gs) ws bank hcov
            rw [hz_hit] at hm; omega

set_option maxHeartbeats 0 in
theorem check_noHitF : noHitF 5 2 initMasks = true := by
  decide +kernel

theorem main :
    ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7 + D.size)),
      PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
      PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
      ∀ t : Fin 6,
        let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]
        let w := D.wires xs
        w.getD p.val false = (16 : Nat).testBit t.val ∧
        w.getD q.val false = (18 : Nat).testBit t.val ∧
        w.getD r.val false = (58 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hfan, _, hnot, hsz, hval⟩
  have hleg : ∀ g ∈ D.gates, legal g := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact ⟨hop, hlen⟩
  set ms := runMasks D.gates initMasks
  have hmlen : ms.length = 7 + D.size := runMasks_len D.gates initMasks
  have hmlt : ∀ m ∈ ms, m < 64 := runMasks_lt64 D.gates initMasks_lt64
  have hbit (idx : Fin (7 + D.size)) (tgt : Nat) (htgt : tgt < 64)
      (heq : ∀ t : Fin 6, (D.wires (inp t)).getD idx.val false = tgt.testBit t.val) :
      tgt ∈ ms := by
    have hlt : idx.val < ms.length := by omega
    have hmem : ms.getD idx.val 0 ∈ ms := by
      rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
    have heqm : ms.getD idx.val 0 = tgt := by
      apply eq_of_testBit6 (hmlt _ hmem) htgt
      intro t
      have hmap := runMasks_map D.gates hleg initMasks t
      rw [initMasks_spec t] at hmap
      have h1 := heq t
      change (D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (inp t)).getD idx.val false = tgt.testBit t.val at h1
      rw [← hmap, readBit] at h1
      exact h1
    exact heqm ▸ hmem
  have h16 : 16 ∈ ms := hbit p 16 (by omega) (fun t => (hval t).1)
  have h18 : 18 ∈ ms := hbit q 18 (by omega) (fun t => (hval t).2.1)
  have h58 : 58 ∈ ms := hbit r 58 (by omega) (fun t => (hval t).2.2)
  have hnotL : notCountL D.gates ≤ 2 := (notCountL_eq D).symm ▸ hnot
  exact noHitF_sound D.gates 5 2 initMasks initMasks check_noHitF hsz hnotL hleg
    (by decide) (by decide) (fun m hm => hm) ⟨h16, h18, h58⟩

end PEqualNP.Outside.L_meta_50974_aux

theorem PEqualNP.Outside.L_meta_50974 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (16 : Nat).testBit t.val ∧
    w.getD q.val false = (18 : Nat).testBit t.val ∧
    w.getD r.val false = (58 : Nat).testBit t.val)) :=
  PEqualNP.Outside.L_meta_50974_aux.main
