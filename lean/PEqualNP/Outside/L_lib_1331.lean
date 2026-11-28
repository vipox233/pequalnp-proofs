import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1331

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

private def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

private lemma isNotOp_eq_true_iff (o : GateOp) : isNotOp o = true ↔ o = GateOp.not := by
  cases o <;> simp [isNotOp]

private lemma decide_eq_isNotOp (o : GateOp) (d : Decidable (o = GateOp.not)) :
    @decide (o = GateOp.not) d = isNotOp o := by
  cases o <;> simp [isNotOp]

private def cstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def evalW (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl cstep x

private lemma evalW_nil (x : List Bool) : evalW [] x = x := rfl

private lemma evalW_append (gs1 gs2 : List Gate) (x : List Bool) :
    evalW (gs1 ++ gs2) x = evalW gs2 (evalW gs1 x) := by
  simp [evalW, List.foldl_append]

private lemma evalW_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    evalW (gs ++ [g]) x = cstep (evalW gs x) g := by
  rw [evalW_append]; rfl

private lemma evalW_len (gs : List Gate) :
    ∀ x : List Bool, (evalW gs x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; simp [evalW]
  | cons g gs ih =>
    intro x
    change (evalW gs (cstep x g)).length = x.length + (g :: gs).length
    rw [ih, cstep]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private lemma getD_append_left (l1 l2 : List Bool) (i : Nat) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma evalW_pre (gs : List Gate) :
    ∀ (x : List Bool) (i : Nat), i < x.length → (evalW gs x).getD i false = x.getD i false := by
  induction gs with
  | nil => intro x i _; rfl
  | cons g gs ih =>
    intro x i hi
    have h1 : i < (cstep x g).length := by simp [cstep]; omega
    change (evalW gs (cstep x g)).getD i false = _
    rw [ih (cstep x g) i h1]
    exact getD_append_left x _ i hi

private lemma evalW_append_pre (gs1 gs2 : List Gate) (x : List Bool) (i : Nat)
    (hi : i < x.length + gs1.length) :
    (evalW (gs1 ++ gs2) x).getD i false = (evalW gs1 x).getD i false := by
  rw [evalW_append]
  exact evalW_pre gs2 (evalW gs1 x) i (by rw [evalW_len]; exact hi)

private lemma evalW_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (evalW (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (evalW gs x).getD i false) := by
  rw [evalW_snoc]
  dsimp only [cstep]
  have hlen : (evalW gs x).length = x.length + gs.length := evalW_len gs x
  rw [← hlen]
  simp [List.getD_eq_getElem?_getD]

private lemma wires_getD_pre (C : Circuit) (x : List Bool) (i : Nat) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  evalW_pre C.gates x i hi

private lemma wires_getD_gate (C : Circuit) (x : List Bool) (u : Nat) (hu : u < C.size)
    (hrb : ReadsBack x.length C) :
    (C.wires x).getD (x.length + u) false =
      (gateAt C u).op.eval ((gateAt C u).inputs.map fun i => (C.wires x).getD i false) := by
  have hu' : u < C.gates.length := hu
  have hsplit : C.gates = C.gates.take u ++ [C.gates[u]] ++ C.gates.drop (u + 1) := by
    have := List.take_append_drop u C.gates
    rw [List.drop_eq_getElem_cons hu'] at this
    simpa [List.append_assoc] using this.symm
  have hga : gateAt C u = C.gates[u] := by
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu']
  rw [hga]
  change (evalW C.gates x).getD (x.length + u) false = _
  let pre := C.gates.take u
  let post := C.gates.drop (u + 1)
  have hpre_len : pre.length = u := List.length_take_of_le (Nat.le_of_lt hu')
  have h1 : (evalW C.gates x).getD (x.length + u) false =
      C.gates[u].op.eval (C.gates[u].inputs.map fun i => (evalW pre x).getD i false) := by
    conv_lhs => rw [hsplit]
    rw [evalW_append_pre (pre ++ [C.gates[u]]) post x (x.length + u) (by simp [hpre_len])]
    have := evalW_snoc_last pre C.gates[u] x
    rw [hpre_len] at this
    exact this
  rw [h1]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hilt : i < x.length + u := by
    have := hrb u hu' i; rw [hga] at this; exact this hi
  change (evalW pre x).getD i false = (evalW C.gates x).getD i false
  conv_rhs => rw [hsplit, List.append_assoc]
  exact (evalW_append_pre pre ([C.gates[u]] ++ post) x i (by rw [hpre_len]; exact hilt)).symm

private def posCount (gs : List Gate) : Nat :=
  (gs.filter (fun g => !isNotOp g.op)).length

private def notCountL (gs : List Gate) : Nat :=
  (gs.filter (fun g => isNotOp g.op)).length

private lemma notCount_eq_notCountL (C : Circuit) : notCount C = notCountL C.gates := by
  unfold notCount notCountL
  congr 1
  refine List.filter_congr fun g _ => decide_eq_isNotOp g.op _

private lemma posCount_add_notCountL (gs : List Gate) :
    posCount gs + notCountL gs = gs.length := by
  induction gs with
  | nil => simp [posCount, notCountL]
  | cons g gs ih =>
    simp only [posCount, notCountL, List.filter_cons, List.length_cons] at ih ⊢
    cases isNotOp g.op <;> simp <;> omega

private lemma posCount_append (gs1 gs2 : List Gate) :
    posCount (gs1 ++ gs2) = posCount gs1 + posCount gs2 := by
  simp [posCount, List.filter_append]

private lemma notCountL_append (gs1 gs2 : List Gate) :
    notCountL (gs1 ++ gs2) = notCountL gs1 + notCountL gs2 := by
  simp [notCountL, List.filter_append]

private lemma map_range_getD (L : List Gate) (d : Gate) :
    (List.range L.length).map (fun u => L.getD u d) = L := by
  refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]

private lemma range_filter_not_len (C : Circuit) :
    ((List.range C.size).filter (fun u => isNotOp (gateAt C u).op)).length = notCount C := by
  rw [notCount_eq_notCountL]
  have h := congrArg (fun L => (L.filter (fun g => isNotOp g.op)).length)
    (map_range_getD C.gates ⟨GateOp.or, []⟩)
  rw [List.filter_map, List.length_map] at h
  exact h

private def ValidGates (N : Nat) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < N + 2 + j)

private lemma validGates_nil (N : Nat) : ValidGates N [] := ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩

private lemma validGates_to_valid (N : Nat) (gs : List Gate) (h : ValidGates N gs) :
    FanInTwo ⟨gs, 0⟩ ∧ ReadsBack (N + 2) ⟨gs, 0⟩ ∧ (⟨gs, 0⟩ : Circuit).output < N + 2 + (⟨gs, 0⟩ : Circuit).size := by
  refine ⟨fun g hg => ?_, h.2, by simp [Circuit.size]⟩
  rcases h.1 g hg with ⟨hop, hlen⟩
  refine ⟨?_, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact hop

private lemma validGates_snoc (N : Nat) (gs : List Gate) (g : Gate)
    (hgs : ValidGates N gs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < N + 2 + gs.length) :
    ValidGates N (gs ++ [g]) := by
  refine ⟨fun g' hg' => ?_, fun j hj i hi => ?_⟩
  · rcases List.mem_append.mp hg' with h1 | h2
    · exact hgs.1 g' h1
    · rw [List.mem_singleton.mp h2]; exact ⟨hop, hlen⟩
  · simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hgs.2 j hlt i hi
    · have heq : j = gs.length := by omega
      subst heq
      have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hin i hi

private lemma le_two_pow_sub_one (k : Nat) : k ≤ 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
    omega

private def bitsRank (f : Nat → Bool) (L : List Nat) (acc : Nat) : Nat :=
  L.foldl (fun v u => 2 * v + (if f u then 0 else 1)) acc

private lemma bitsRank_cons (f : Nat → Bool) (a : Nat) (L : List Nat) (acc : Nat) :
    bitsRank f (a :: L) acc = bitsRank f L (2 * acc + (if f a then 0 else 1)) := rfl

private lemma bitsRank_shift (f : Nat → Bool) (L : List Nat) :
    ∀ acc : Nat, bitsRank f L acc = acc * 2 ^ L.length + bitsRank f L 0 := by
  induction L with
  | nil => intro acc; simp [bitsRank]
  | cons a L ih =>
    intro acc
    rw [bitsRank_cons, bitsRank_cons, Nat.mul_zero, Nat.zero_add]
    rw [ih (2 * acc + (if f a then 0 else 1)), ih (if f a then 0 else 1)]
    have hp : 2 ^ (a :: L).length = 2 * 2 ^ L.length := by rw [List.length_cons, pow_succ, Nat.mul_comm]
    rw [hp]; ring

private lemma bitsRank_lt (f : Nat → Bool) (L : List Nat) :
    bitsRank f L 0 < 2 ^ L.length := by
  induction L with
  | nil => simp [bitsRank]
  | cons a L ih =>
    rw [bitsRank_cons, Nat.mul_zero, Nat.zero_add, bitsRank_shift]
    have hbit : (if f a then 0 else 1) ≤ 1 := by cases f a <;> decide
    have hp : 2 ^ (a :: L).length = 2 * 2 ^ L.length := by rw [List.length_cons, pow_succ, Nat.mul_comm]
    rw [hp]
    have := Nat.mul_le_mul_right (2 ^ L.length) hbit
    omega

private lemma bitsRank_testBit (f : Nat → Bool) (L : List Nat) :
    ∀ (s : Nat) (hs : s < L.length),
      (bitsRank f L 0).testBit (L.length - 1 - s) = !(f L[s]) := by
  induction L with
  | nil => intro s hs; simp at hs
  | cons a L ih =>
    intro s hs
    have hval : bitsRank f (a :: L) 0 = (if f a then 0 else 1) * 2 ^ L.length + bitsRank f L 0 := by
      rw [bitsRank_cons, Nat.mul_zero, Nat.zero_add]
      exact bitsRank_shift f L _
    have hrem : bitsRank f L 0 < 2 ^ L.length := bitsRank_lt f L
    rw [hval]
    cases s with
    | zero =>
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero]
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : ((if f a then 0 else 1) * 2 ^ L.length + bitsRank f L 0) / 2 ^ L.length =
          (if f a then 0 else 1) := by
        rw [Nat.mul_comm (if f a then 0 else 1) (2 ^ L.length),
          Nat.mul_add_div (Nat.two_pow_pos L.length), Nat.div_eq_of_lt hrem, Nat.add_zero]
      rw [hdiv]
      cases f a <;> decide
    | succ s =>
      simp only [List.length_cons, List.getElem_cons_succ]
      have hs' : s < L.length := Nat.lt_of_succ_lt_succ hs
      have hidx : L.length + 1 - 1 - (s + 1) = L.length - 1 - s := by omega
      rw [hidx, ← ih s hs']
      set r := L.length - 1 - s
      have hr : r < L.length := by omega
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 2 ^ L.length = 2 ^ r * (2 * 2 ^ (L.length - r - 1)) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      have hdiv : ((if f a then 0 else 1) * 2 ^ L.length + bitsRank f L 0) / 2 ^ r =
          (if f a then 0 else 1) * (2 * 2 ^ (L.length - r - 1)) + bitsRank f L 0 / 2 ^ r := by
        rw [hpow, ← Nat.mul_assoc, Nat.mul_comm (if f a then 0 else 1) (2 ^ r), Nat.mul_assoc,
          Nat.mul_add_div (Nat.two_pow_pos r)]
      rw [hdiv]
      have hmod : ((if f a then 0 else 1) * (2 * 2 ^ (L.length - r - 1)) + bitsRank f L 0 / 2 ^ r) % 2 =
          (bitsRank f L 0 / 2 ^ r) % 2 := by
        have hmul : (if f a then 0 else 1) * (2 * 2 ^ (L.length - r - 1)) =
            2 * ((if f a then 0 else 1) * 2 ^ (L.length - r - 1)) := by ring
        rw [hmul, Nat.mul_add_mod]
      rw [hmod]

private lemma nat_lt_two_iff (a : Nat) (h : a < 2) : a = 0 ∨ a = 1 := by omega

private lemma lt_iff_exists_msb_diff (b x y : Nat) (hx : x < 2 ^ b) (hy : y < 2 ^ b) :
    x < y ↔ ∃ s < b, (∀ j < s, x.testBit (b - 1 - j) = y.testBit (b - 1 - j)) ∧
      x.testBit (b - 1 - s) = false ∧ y.testBit (b - 1 - s) = true := by
  induction b generalizing x y with
  | zero =>
    simp at hx hy
    omega
  | succ b ih =>
    set P := 2 ^ b
    have hP : 0 < P := Nat.two_pow_pos b
    have hp : 2 ^ (b + 1) = 2 * P := by dsimp only [P]; rw [pow_succ, Nat.mul_comm]
    set qx := x / P
    set qy := y / P
    set rx := x % P
    set ry := y % P
    have hxhi : qx < 2 := (Nat.div_lt_iff_lt_mul hP).mpr (by omega)
    have hyhi : qy < 2 := (Nat.div_lt_iff_lt_mul hP).mpr (by omega)
    have hxlo : rx < P := Nat.mod_lt x hP
    have hylo : ry < P := Nat.mod_lt y hP
    have hx_bit_top : x.testBit b = decide (qx = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      change decide (qx % 2 = 1) = decide (qx = 1)
      rw [Nat.mod_eq_of_lt hxhi]
    have hy_bit_top : y.testBit b = decide (qy = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      change decide (qy % 2 = 1) = decide (qy = 1)
      rw [Nat.mod_eq_of_lt hyhi]
    have hx_bit_lo : ∀ r < b, rx.testBit r = x.testBit r := fun r hr => by
      dsimp only [rx, P]; rw [Nat.testBit_mod_two_pow, decide_eq_true hr, Bool.true_and]
    have hy_bit_lo : ∀ r < b, ry.testBit r = y.testBit r := fun r hr => by
      dsimp only [ry, P]; rw [Nat.testBit_mod_two_pow, decide_eq_true hr, Bool.true_and]
    have hx_dm : x = qx * P + rx := by
      have := Nat.div_add_mod x P; rw [Nat.mul_comm] at this; exact this.symm
    have hy_dm : y = qy * P + ry := by
      have := Nat.div_add_mod y P; rw [Nat.mul_comm] at this; exact this.symm
    constructor
    · intro hxy
      by_cases htop : qx = qy
      · have hmodlt : rx < ry := by rw [hx_dm, hy_dm, htop] at hxy; omega
        rcases (ih rx ry hxlo hylo).mp hmodlt with ⟨s, hs, hpre, hxf, hyt⟩
        refine ⟨s + 1, by omega, ?_, ?_, ?_⟩
        · intro j hj
          cases j with
          | zero =>
            simp only [Nat.add_sub_cancel, Nat.sub_zero, hx_bit_top, hy_bit_top, htop]
          | succ j =>
            have hidx : b + 1 - 1 - (j + 1) = b - 1 - j := by omega
            rw [hidx, ← hx_bit_lo (b - 1 - j) (by omega), ← hy_bit_lo (b - 1 - j) (by omega)]
            exact hpre j (by omega)
        · have hidx : b + 1 - 1 - (s + 1) = b - 1 - s := by omega
          rw [hidx, ← hx_bit_lo (b - 1 - s) (by omega)]; exact hxf
        · have hidx : b + 1 - 1 - (s + 1) = b - 1 - s := by omega
          rw [hidx, ← hy_bit_lo (b - 1 - s) (by omega)]; exact hyt
      · have hqx_qy : qx = 0 ∧ qy = 1 := by
          rcases nat_lt_two_iff qx hxhi with hqx0 | hqx1 <;>
          rcases nat_lt_two_iff qy hyhi with hqy0 | hqy1
          · exact absurd (hqx0.trans hqy0.symm) htop
          · exact ⟨hqx0, hqy1⟩
          · rw [hx_dm, hy_dm, hqx1, hqy0, Nat.one_mul, Nat.zero_mul, Nat.zero_add] at hxy; omega
          · exact absurd (hqx1.trans hqy1.symm) htop
        refine ⟨0, by omega, fun j hj => by omega, ?_, ?_⟩
        · simp [hx_bit_top, hqx_qy.1]
        · simp [hy_bit_top, hqx_qy.2]
    · rintro ⟨s, hs, hpre, hxf, hyt⟩
      cases s with
      | zero =>
        simp only [Nat.add_sub_cancel, Nat.sub_zero, hx_bit_top, hy_bit_top] at hxf hyt
        have hx0 : qx = 0 := by
          have hne1 : qx ≠ 1 := of_decide_eq_false hxf
          exact (nat_lt_two_iff qx hxhi).resolve_right hne1
        have hy1 : qy = 1 := of_decide_eq_true hyt
        rw [hx_dm, hy_dm, hx0, hy1, Nat.zero_mul, Nat.zero_add, Nat.one_mul]; omega
      | succ s =>
        have htop_bit := hpre 0 (by omega)
        simp only [Nat.add_sub_cancel, Nat.sub_zero, hx_bit_top, hy_bit_top] at htop_bit
        have htop : qx = qy := by
          by_cases h1 : qx = 1
          · rw [decide_eq_true h1] at htop_bit
            have hy1 := of_decide_eq_true htop_bit.symm
            exact h1.trans hy1.symm
          · rw [decide_eq_false h1] at htop_bit
            have hyne1 := of_decide_eq_false htop_bit.symm
            have hqx0 : qx = 0 := (nat_lt_two_iff qx hxhi).resolve_right h1
            have hqy0 : qy = 0 := (nat_lt_two_iff qy hyhi).resolve_right hyne1
            exact hqx0.trans hqy0.symm
        have hmodlt : rx < ry := by
          apply (ih rx ry hxlo hylo).mpr
          refine ⟨s, by omega, ?_, ?_, ?_⟩
          · intro j hj
            rw [hx_bit_lo (b - 1 - j) (by omega), hy_bit_lo (b - 1 - j) (by omega)]
            have hidx : b - 1 - j = b + 1 - 1 - (j + 1) := by omega
            rw [hidx]
            exact hpre (j + 1) (by omega)
          · rw [hx_bit_lo (b - 1 - s) (by omega)]
            have hidx : b - 1 - s = b + 1 - 1 - (s + 1) := by omega
            rw [hidx]; exact hxf
          · rw [hy_bit_lo (b - 1 - s) (by omega)]
            have hidx : b - 1 - s = b + 1 - 1 - (s + 1) := by omega
            rw [hidx]; exact hyt
        rw [hx_dm, hy_dm, htop]; omega

private lemma flatten_fixed_getD {α : Type} (L : List (List α)) (len : Nat) (dflt : α)
    (hlen : ∀ l ∈ L, l.length = len) (j c : Nat) (hj : j < L.length) (hc : c < len) :
    L.flatten.getD (j * len + c) dflt = (L[j]).getD c dflt := by
  induction L generalizing j with
  | nil => simp at hj
  | cons a rest ih =>
    have ha : a.length = len := hlen a List.mem_cons_self
    cases j with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.flatten_cons, List.getElem_cons_zero]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : c < a.length)]
    | succ j =>
      simp only [List.flatten_cons, List.getElem_cons_succ]
      have hidx : (j + 1) * len + c = a.length + (j * len + c) := by rw [ha]; ring
      rw [hidx]
      have hge : a.length ≤ a.length + (j * len + c) := Nat.le_add_right _ _
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, Nat.add_sub_cancel_left]
      exact ih (fun l hl => hlen l (List.mem_cons_of_mem a hl)) j (by simp at hj; omega)

private def rawVec (d k : Nat) (s : Fin k) (x : Fin d → Bool) : List Bool :=
  (List.ofFn (fun i : Fin k => decide (i ≤ s) :: List.ofFn (fun z : Fin d =>
    decide (i < s) || (decide (i = s) && x z)))).flatten ++ [false, true]

private lemma rawVec_len (d k : Nat) (s : Fin k) (x : Fin d → Bool) :
    (rawVec d k s x).length = k * (d + 1) + 2 := by
  unfold rawVec
  rw [List.length_append, List.length_flatten]
  have hmap : (List.ofFn (fun i : Fin k => decide (i ≤ s) :: List.ofFn (fun z : Fin d =>
      decide (i < s) || (decide (i = s) && x z)))).map List.length =
      List.replicate k (d + 1) := by
    refine List.ext_getElem (by simp) fun j hj1 hj2 => ?_
    simp
  rw [hmap, List.sum_replicate, smul_eq_mul]
  simp

private lemma rawVec_flag (d k : Nat) (s i : Fin k) (x : Fin d → Bool) :
    (rawVec d k s x).getD (i.val * (d + 1)) false = decide (i ≤ s) := by
  unfold rawVec
  let blocks := List.ofFn (fun i : Fin k => decide (i ≤ s) :: List.ofFn (fun z : Fin d =>
    decide (i < s) || (decide (i = s) && x z)))
  have hblen : ∀ l ∈ blocks, l.length = d + 1 := by
    intro l hl
    rcases List.mem_ofFn.mp hl with ⟨i', rfl⟩
    simp
  have hflat_len : blocks.flatten.length = k * (d + 1) := by
    rw [List.length_flatten]
    have hm : blocks.map List.length = List.replicate k (d + 1) := by
      refine List.ext_getElem (by simp [blocks]) fun r hr1 hr2 => ?_
      simp [blocks]
    rw [hm, List.sum_replicate, smul_eq_mul]
  have hlt : i.val * (d + 1) < blocks.flatten.length := by
    rw [hflat_len]
    have h1 : (i.val + 1) * (d + 1) ≤ k * (d + 1) := Nat.mul_le_mul_right _ i.isLt
    have h2 : (i.val + 1) * (d + 1) = i.val * (d + 1) + (d + 1) := by ring
    omega
  rw [getD_append_left blocks.flatten [false, true] _ hlt]
  have hf := flatten_fixed_getD blocks (d + 1) false hblen i.val 0 (by simp [blocks]) (by omega)
  rw [Nat.add_zero] at hf
  rw [hf]
  simp [blocks]

private lemma rawVec_data (d k : Nat) (s i : Fin k) (z : Fin d) (x : Fin d → Bool) :
    (rawVec d k s x).getD (i.val * (d + 1) + (z.val + 1)) false =
      (decide (i < s) || (decide (i = s) && x z)) := by
  unfold rawVec
  let blocks := List.ofFn (fun i : Fin k => decide (i ≤ s) :: List.ofFn (fun z : Fin d =>
    decide (i < s) || (decide (i = s) && x z)))
  have hblen : ∀ l ∈ blocks, l.length = d + 1 := by
    intro l hl
    rcases List.mem_ofFn.mp hl with ⟨i', rfl⟩
    simp
  have hflat_len : blocks.flatten.length = k * (d + 1) := by
    rw [List.length_flatten]
    have hm : blocks.map List.length = List.replicate k (d + 1) := by
      refine List.ext_getElem (by simp [blocks]) fun r hr1 hr2 => ?_
      simp [blocks]
    rw [hm, List.sum_replicate, smul_eq_mul]
  have hlt : i.val * (d + 1) + (z.val + 1) < blocks.flatten.length := by
    rw [hflat_len]
    have h1 : (i.val + 1) * (d + 1) ≤ k * (d + 1) := Nat.mul_le_mul_right _ i.isLt
    have h2 : (i.val + 1) * (d + 1) = i.val * (d + 1) + (d + 1) := by ring
    have := z.isLt
    omega
  rw [getD_append_left blocks.flatten [false, true] _ hlt]
  have hf := flatten_fixed_getD blocks (d + 1) false hblen i.val (z.val + 1) (by simp [blocks]) (by have := z.isLt; omega)
  rw [hf]
  simp [blocks, List.getD_eq_getElem?_getD, z.isLt]

private lemma rawVec_c0 (d k : Nat) (s : Fin k) (x : Fin d → Bool) :
    (rawVec d k s x).getD (k * (d + 1)) false = false := by
  unfold rawVec
  let blocks := List.ofFn (fun i : Fin k => decide (i ≤ s) :: List.ofFn (fun z : Fin d =>
    decide (i < s) || (decide (i = s) && x z)))
  have hflat_len : blocks.flatten.length = k * (d + 1) := by
    rw [List.length_flatten]
    have hm : blocks.map List.length = List.replicate k (d + 1) := by
      refine List.ext_getElem (by simp [blocks]) fun r hr1 hr2 => ?_
      simp [blocks]
    rw [hm, List.sum_replicate, smul_eq_mul]
  change (blocks.flatten ++ [false, true]).getD (k * (d + 1)) false = false
  rw [← hflat_len]
  simp [List.getD_eq_getElem?_getD]

private lemma rawVec_c1 (d k : Nat) (s : Fin k) (x : Fin d → Bool) :
    (rawVec d k s x).getD (k * (d + 1) + 1) false = true := by
  unfold rawVec
  let blocks := List.ofFn (fun i : Fin k => decide (i ≤ s) :: List.ofFn (fun z : Fin d =>
    decide (i < s) || (decide (i = s) && x z)))
  have hflat_len : blocks.flatten.length = k * (d + 1) := by
    rw [List.length_flatten]
    have hm : blocks.map List.length = List.replicate k (d + 1) := by
      refine List.ext_getElem (by simp [blocks]) fun r hr1 hr2 => ?_
      simp [blocks]
    rw [hm, List.sum_replicate, smul_eq_mul]
  change (blocks.flatten ++ [false, true]).getD (k * (d + 1) + 1) false = true
  rw [← hflat_len]
  simp [List.getD_eq_getElem?_getD]

private lemma rawVec_mono_lt (d k : Nat) (s1 s2 : Fin k) (hlt : s1 < s2)
    (x1 x2 : Fin d → Bool) :
    ∀ u < k * (d + 1) + 2, (rawVec d k s1 x1).getD u false = true →
      (rawVec d k s2 x2).getD u false = true := by
  intro u hu h1
  by_cases hltN : u < k * (d + 1)
  · have hq : u / (d + 1) < k := (Nat.div_lt_iff_lt_mul (by omega : 0 < d + 1)).mpr hltN
    have hr : u % (d + 1) < d + 1 := Nat.mod_lt u (by omega)
    have hdm : u = (u / (d + 1)) * (d + 1) + u % (d + 1) := by
      have := Nat.div_add_mod u (d + 1); rw [Nat.mul_comm] at this; exact this.symm
    let i : Fin k := ⟨u / (d + 1), hq⟩
    by_cases hr0 : u % (d + 1) = 0
    · have hueq : u = i.val * (d + 1) := by rw [hdm, hr0, Nat.add_zero]
      rw [hueq, rawVec_flag] at h1 ⊢
      have hle : i ≤ s1 := of_decide_eq_true h1
      exact decide_eq_true (le_trans hle (le_of_lt hlt))
    · let z : Fin d := ⟨u % (d + 1) - 1, by omega⟩
      have hueq : u = i.val * (d + 1) + (z.val + 1) := by
        show u = (u / (d + 1)) * (d + 1) + ((u % (d + 1) - 1) + 1); omega
      rw [hueq, rawVec_data] at h1 ⊢
      have hle : i ≤ s1 := by
        by_contra hnot
        have hgt : s1 < i := lt_of_not_ge hnot
        have h1f : decide (i < s1) = false := decide_eq_false (not_lt.mpr (le_of_lt hgt))
        have h2f : decide (i = s1) = false := decide_eq_false (ne_of_gt hgt)
        rw [h1f, h2f] at h1; simp at h1
      have hilts2 : i < s2 := lt_of_le_of_lt hle hlt
      rw [decide_eq_true hilts2, Bool.true_or]
  · by_cases hu0 : u = k * (d + 1)
    · subst hu0; rw [rawVec_c0] at h1; exact absurd h1 Bool.false_ne_true
    · have hu1 : u = k * (d + 1) + 1 := by omega
      subst hu1; rw [rawVec_c1]

private lemma rawVec_mono_le (d k : Nat) (s : Fin k) (x1 x2 : Fin d → Bool)
    (hle : ∀ z, x1 z = true → x2 z = true) :
    ∀ u < k * (d + 1) + 2, (rawVec d k s x1).getD u false = true →
      (rawVec d k s x2).getD u false = true := by
  intro u hu h1
  by_cases hltN : u < k * (d + 1)
  · have hq : u / (d + 1) < k := (Nat.div_lt_iff_lt_mul (by omega : 0 < d + 1)).mpr hltN
    have hr : u % (d + 1) < d + 1 := Nat.mod_lt u (by omega)
    have hdm : u = (u / (d + 1)) * (d + 1) + u % (d + 1) := by
      have := Nat.div_add_mod u (d + 1); rw [Nat.mul_comm] at this; exact this.symm
    let i : Fin k := ⟨u / (d + 1), hq⟩
    by_cases hr0 : u % (d + 1) = 0
    · have hueq : u = i.val * (d + 1) := by rw [hdm, hr0, Nat.add_zero]
      rw [hueq, rawVec_flag] at h1 ⊢; exact h1
    · let z : Fin d := ⟨u % (d + 1) - 1, by omega⟩
      have hueq : u = i.val * (d + 1) + (z.val + 1) := by
        show u = (u / (d + 1)) * (d + 1) + ((u % (d + 1) - 1) + 1); omega
      rw [hueq, rawVec_data] at h1 ⊢
      by_cases hilt : i < s
      · rw [decide_eq_true hilt, Bool.true_or]
      · by_cases hieq : i = s
        · rw [decide_eq_false hilt, decide_eq_true hieq, Bool.false_or, Bool.true_and] at h1 ⊢
          exact hle z h1
        · rw [decide_eq_false hilt, decide_eq_false hieq] at h1; simp at h1
  · by_cases hu0 : u = k * (d + 1)
    · subst hu0; rw [rawVec_c0] at h1; exact absurd h1 Bool.false_ne_true
    · have hu1 : u = k * (d + 1) + 1 := by omega
      subst hu1; rw [rawVec_c1]

private lemma mono_pre_wires (L : Nat) (C : Circuit) (hfan : FanInTwo C) (hrb : ReadsBack L C)
    (v1 v2 : List Bool) (hv1 : v1.length = L) (hv2 : v2.length = L)
    (hin : ∀ u < L, v1.getD u false = true → v2.getD u false = true)
    (lim : Nat) (hlim : lim ≤ C.size)
    (hnot_eq : ∀ u < lim, isNotOp (gateAt C u).op = true →
      (C.wires v1).getD (L + u) false = (C.wires v2).getD (L + u) false) :
    ∀ w < L + lim, (C.wires v1).getD w false = true → (C.wires v2).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw h1
    by_cases hwL : w < L
    · rw [wires_getD_pre C v1 w (by rw [hv1]; exact hwL)] at h1
      rw [wires_getD_pre C v2 w (by rw [hv2]; exact hwL)]
      exact hin w hwL h1
    · set u := w - L
      have hweq : w = L + u := by omega
      have hult : u < lim := by omega
      have husz : u < C.size := lt_of_lt_of_le hult hlim
      rw [hweq] at h1 ⊢
      by_cases hnotu : isNotOp (gateAt C u).op = true
      · rw [← hnot_eq u hult hnotu]; exact h1
      · have hgmem : gateAt C u ∈ C.gates := by
          have hu' : u < C.gates.length := husz
          have hga : gateAt C u = C.gates[u] := by
            simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu']
          rw [hga]; exact List.getElem_mem hu'
        have hop_ao : (gateAt C u).op = GateOp.and ∨ (gateAt C u).op = GateOp.or := by
          have := (hfan (gateAt C u) hgmem).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
          rcases this with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd ((isNotOp_eq_true_iff _).mpr h) hnotu
        have hrb1 : ReadsBack v1.length C := by rw [hv1]; exact hrb
        have hrb2 : ReadsBack v2.length C := by rw [hv2]; exact hrb
        have hg1 := wires_getD_gate C v1 u husz hrb1
        have hg2 := wires_getD_gate C v2 u husz hrb2
        rw [hv1] at hg1; rw [hv2] at hg2
        rw [hg1] at h1; rw [hg2]
        rcases hop_ao with hand | hor
        · rw [hand] at h1 ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at h1 ⊢
          rintro _ ⟨a, ha, rfl⟩
          have halt : a < L + u := hrb u husz a ha
          exact ih a (by omega) (by omega) (h1 _ ⟨a, ha, rfl⟩)
        · rw [hor] at h1 ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at h1 ⊢
          rcases h1 with ⟨_, ⟨a, ha, rfl⟩, ha1⟩
          have halt : a < L + u := hrb u husz a ha
          exact ⟨_, ⟨a, ha, rfl⟩, ih a (by omega) (by omega) ha1⟩

private lemma rank_mono (L : Nat) (C : Circuit) (hfan : FanInTwo C) (hrb : ReadsBack L C)
    (v1 v2 : List Bool) (hv1 : v1.length = L) (hv2 : v2.length = L)
    (hin : ∀ u < L, v1.getD u false = true → v2.getD u false = true) :
    let gates := (List.range C.size).filter (fun u => isNotOp (gateAt C u).op)
    bitsRank (fun u => (C.wires v1).getD (L + u) false) gates 0 ≤
      bitsRank (fun u => (C.wires v2).getD (L + u) false) gates 0 := by
  intro gates
  by_contra hnot
  have hlt : bitsRank (fun u => (C.wires v2).getD (L + u) false) gates 0 <
      bitsRank (fun u => (C.wires v1).getD (L + u) false) gates 0 := by omega
  have hr1_lt := bitsRank_lt (fun u => (C.wires v1).getD (L + u) false) gates
  have hr2_lt := bitsRank_lt (fun u => (C.wires v2).getD (L + u) false) gates
  rcases (lt_iff_exists_msb_diff gates.length _ _ hr2_lt hr1_lt).mp hlt with ⟨s, hs, hpre, h2f, h1t⟩
  have hgates_sorted : gates.Pairwise (· < ·) := List.pairwise_lt_range.filter _
  set u0 := gates[s]
  have hu0_mem : u0 ∈ gates := List.getElem_mem hs
  have hu0_spec : u0 < C.size ∧ isNotOp (gateAt C u0).op = true := by
    have := List.mem_filter.mp hu0_mem
    exact ⟨List.mem_range.mp this.1, this.2⟩
  have hnot_pre : ∀ u' < u0, isNotOp (gateAt C u').op = true →
      (C.wires v1).getD (L + u') false = (C.wires v2).getD (L + u') false := by
    intro u' hu'lt hu'not
    have hu'mem : u' ∈ gates := List.mem_filter.mpr ⟨List.mem_range.mpr (lt_trans hu'lt hu0_spec.1), hu'not⟩
    have hidx_lt : gates.idxOf u' < gates.length := List.idxOf_lt_length_iff.mpr hu'mem
    have hidx_eq : gates[gates.idxOf u'] = u' := List.getElem_idxOf hidx_lt
    have hidx_lt_s : gates.idxOf u' < s := by
      by_contra hge
      have hsle : s ≤ gates.idxOf u' := by omega
      rcases eq_or_lt_of_le hsle with heq | hlt'
      · have : u0 = u' := by dsimp only [u0]; rw [← hidx_eq]; congr 1
        omega
      · have := List.pairwise_iff_getElem.mp hgates_sorted s (gates.idxOf u') hs hidx_lt hlt'
        rw [hidx_eq] at this; omega
    have hbit := hpre (gates.idxOf u') hidx_lt_s
    rw [bitsRank_testBit _ gates _ hidx_lt, bitsRank_testBit _ gates _ hidx_lt, hidx_eq] at hbit
    have h1 := congrArg Bool.not hbit
    simp only [Bool.not_not] at h1
    exact h1.symm
  have hmp := mono_pre_wires L C hfan hrb v1 v2 hv1 hv2 hin u0 (Nat.le_of_lt hu0_spec.1) hnot_pre
  rw [bitsRank_testBit _ gates s hs] at h2f h1t
  have hw2 : (C.wires v2).getD (L + u0) false = true := by
    cases h : (C.wires v2).getD (L + u0) false
    · rw [h] at h2f; simp at h2f
    · rfl
  have hw1 : (C.wires v1).getD (L + u0) false = false := by
    cases h : (C.wires v1).getD (L + u0) false
    · rfl
    · rw [h] at h1t; simp at h1t
  have hrb1 : ReadsBack v1.length C := by rw [hv1]; exact hrb
  have hrb2 : ReadsBack v2.length C := by rw [hv2]; exact hrb
  have hg1 := wires_getD_gate C v1 u0 hu0_spec.1 hrb1
  have hg2 := wires_getD_gate C v2 u0 hu0_spec.1 hrb2
  rw [hv1] at hg1; rw [hv2] at hg2
  have hu0_op : (gateAt C u0).op = GateOp.not := (isNotOp_eq_true_iff _).mp hu0_spec.2
  rw [hg1, hu0_op] at hw1
  rw [hg2, hu0_op] at hw2
  cases hlist : (gateAt C u0).inputs with
  | nil =>
    rw [hlist] at hw1; simp [GateOp.eval] at hw1
  | cons a rest =>
    rw [hlist] at hw1 hw2
    simp only [List.map_cons, GateOp.eval, List.headD_cons, Bool.not_eq_false', Bool.not_eq_true'] at hw1 hw2
    have halt : a < L + u0 := hrb u0 hu0_spec.1 a (by simp [hlist])
    have ha2 := hmp a halt hw1
    rw [ha2] at hw2
    exact Bool.noConfusion hw2

private lemma strict_steps_le (k M : Nat) (lo hi : Fin k → Nat)
    (hbd : ∀ s, lo s ≤ hi s ∧ hi s < M)
    (hstep : ∀ s1 s2, s1 < s2 → hi s1 ≤ lo s2) :
    (Finset.univ.filter (fun s : Fin k => lo s < hi s)).card ≤ M - 1 := by
  have haux : ∀ c (hc : c ≤ k),
      (Finset.univ.filter (fun s : Fin k => s.val < c ∧ lo s < hi s)).card ≤
        if h0 : c = 0 then 0 else hi ⟨c - 1, by omega⟩ := by
    intro c
    induction c with
    | zero =>
      intro _
      simp
    | succ c ih =>
      intro hc
      have hdecomp : Finset.univ.filter (fun s : Fin k => s.val < c + 1 ∧ lo s < hi s) =
          Finset.univ.filter (fun s : Fin k => s.val < c ∧ lo s < hi s) ∪
          (if lo ⟨c, hc⟩ < hi ⟨c, hc⟩ then {⟨c, hc⟩} else ∅) := by
        by_cases hltc : lo ⟨c, hc⟩ < hi ⟨c, hc⟩
        · rw [if_pos hltc]
          ext s
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨hs1, hs2⟩
            by_cases heq : s.val = c
            · exact Or.inr (Fin.ext heq)
            · exact Or.inl ⟨by omega, hs2⟩
          · rintro (⟨hs1, hs2⟩ | rfl)
            · exact ⟨by omega, hs2⟩
            · exact ⟨Nat.lt_succ_self c, hltc⟩
        · rw [if_neg hltc, Finset.union_empty]
          ext s
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hs1, hs2⟩
            have hne : s.val ≠ c := fun h => hltc (by have : (⟨c, hc⟩ : Fin k) = s := Fin.ext h.symm; rw [this]; exact hs2)
            exact ⟨by omega, hs2⟩
          · rintro ⟨hs1, hs2⟩; exact ⟨by omega, hs2⟩
      rw [hdecomp]
      have hne0 : ¬ (c + 1 = 0) := by omega
      rw [dif_neg hne0]
      have hprev := ih (by omega)
      cases c with
      | zero =>
        have hempty : Finset.univ.filter (fun s : Fin k => s.val < 0 ∧ lo s < hi s) = ∅ := by
          ext s; simp
        rw [hempty, Finset.empty_union]
        by_cases hlt0 : lo ⟨0, hc⟩ < hi ⟨0, hc⟩
        · rw [if_pos hlt0, Finset.card_singleton]; change 1 ≤ hi ⟨0, hc⟩; omega
        · rw [if_neg hlt0, Finset.card_empty]; exact Nat.zero_le _
      | succ c' =>
        have hne' : ¬ (c' + 1 = 0) := by omega
        rw [dif_neg hne'] at hprev
        have hord := hstep ⟨c', by omega⟩ ⟨c' + 1, hc⟩ (by show c' < c' + 1; omega)
        have hle' := (hbd ⟨c' + 1, hc⟩).1
        have hcard_le : (Finset.univ.filter (fun s : Fin k => s.val < c' + 1 ∧ lo s < hi s) ∪
            (if lo ⟨c' + 1, hc⟩ < hi ⟨c' + 1, hc⟩ then {⟨c' + 1, hc⟩} else ∅)).card ≤
            (Finset.univ.filter (fun s : Fin k => s.val < c' + 1 ∧ lo s < hi s)).card +
            (if lo ⟨c' + 1, hc⟩ < hi ⟨c' + 1, hc⟩ then 1 else 0) := by
          refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
          split <;> simp
        by_cases hltc : lo ⟨c' + 1, hc⟩ < hi ⟨c' + 1, hc⟩
        · rw [if_pos hltc, if_pos hltc] at hcard_le
          rw [if_pos hltc]
          have : (⟨c' + 1 + 1 - 1, by omega⟩ : Fin k) = ⟨c' + 1, hc⟩ := Fin.ext (by simp)
          rw [this]
          have : (⟨c' + 1 - 1, by omega⟩ : Fin k) = ⟨c', by omega⟩ := Fin.ext (by simp)
          rw [this] at hprev
          omega
        · rw [if_neg hltc, if_neg hltc] at hcard_le
          rw [if_neg hltc]
          have : (⟨c' + 1 + 1 - 1, by omega⟩ : Fin k) = ⟨c' + 1, hc⟩ := Fin.ext (by simp)
          rw [this]
          have : (⟨c' + 1 - 1, by omega⟩ : Fin k) = ⟨c', by omega⟩ := Fin.ext (by simp)
          rw [this] at hprev
          omega
  have hfull := haux k (le_refl k)
  have hfilt : Finset.univ.filter (fun s : Fin k => s.val < k ∧ lo s < hi s) =
      Finset.univ.filter (fun s : Fin k => lo s < hi s) := by
    ext s; simp [s.isLt]
  rw [hfilt] at hfull
  by_cases hk0 : k = 0
  · rw [dif_pos hk0] at hfull; omega
  · rw [dif_neg hk0] at hfull
    have := (hbd ⟨k - 1, by omega⟩).2
    omega

private lemma lower_bound_proof (B m n e : Nat) (hm : 0 < m) (hn : 0 < n) (he : e ≤ B) :
    let k := 2 ^ B * m
    let d := n + n
    let N := k * (d + 1)
    let q := 2 ^ e
    let h := k / q
    ∀ (C : Circuit) (tap : Fin k → Fin n → Fin n → Nat),
      FanInTwo C → ReadsBack (N + 2) C → C.output < N + 2 + C.size →
      (∀ s i j, tap s i j < N + 2 + C.size) →
      (∀ s x i j, (C.wires (rawVec d k s x)).getD (tap s i j) false =
        (x (Fin.castAdd n i) && x (Fin.natAdd n j))) →
      notCount C ≤ e → h * n ^ 2 ≤ C.size - notCount C := by
  intro k d N q h C tap hfan hrb _ htap hfit hnot
  have hqh : q * h = k := by
    dsimp only [q, h, k]
    have hpow : 2 ^ B = 2 ^ e * 2 ^ (B - e) := by rw [← pow_add]; congr 1; omega
    have hkmul : 2 ^ B * m = 2 ^ e * (2 ^ (B - e) * m) := by rw [hpow]; ring
    rw [hkmul, Nat.mul_div_cancel_left _ (Nat.two_pow_pos e)]
  have hh_pos : 1 ≤ h := by
    have hk_pos : 1 ≤ k := Nat.mul_pos (Nat.two_pow_pos B) hm
    exact Nat.pos_of_ne_zero fun hh0 => by rw [hh0, Nat.mul_zero] at hqh; omega
  let b := notCount C
  let bPow := 2 ^ b
  have hbPow_pos : 1 ≤ bPow := Nat.one_le_two_pow
  have hbPow_le_q : bPow ≤ q := Nat.pow_le_pow_right (by omega) hnot
  let gates := (List.range C.size).filter (fun u => isNotOp (gateAt C u).op)
  have hgates_len : gates.length = b := range_filter_not_len C
  let rankV : List Bool → Nat := fun v =>
    bitsRank (fun u => (C.wires v).getD (N + 2 + u) false) gates 0
  have hrank_lt : ∀ v, rankV v < bPow := by
    intro v; dsimp only [rankV, bPow]; rw [← hgates_len]; exact bitsRank_lt _ _
  let bot : Fin k → List Bool := fun s => rawVec d k s (fun _ => false)
  let top : Fin k → List Bool := fun s => rawVec d k s (fun _ => true)
  let lo : Fin k → Nat := fun s => rankV (bot s)
  let hi : Fin k → Nat := fun s => rankV (top s)
  have hlo_le_rank : ∀ s x, lo s ≤ rankV (rawVec d k s x) := fun s x =>
    rank_mono (N + 2) C hfan hrb (bot s) (rawVec d k s x) (rawVec_len d k s _) (rawVec_len d k s _)
      (rawVec_mono_le d k s _ x (fun _ h => absurd h Bool.false_ne_true))
  have hrank_le_hi : ∀ s x, rankV (rawVec d k s x) ≤ hi s := fun s x =>
    rank_mono (N + 2) C hfan hrb (rawVec d k s x) (top s) (rawVec_len d k s _) (rawVec_len d k s _)
      (rawVec_mono_le d k s x _ (fun _ _ => rfl))
  have hlo_le_hi : ∀ s, lo s ≤ hi s := fun s => (hlo_le_rank s (fun _ => false)).trans (hrank_le_hi s _)
  have hhi_le_lo : ∀ s1 s2, s1 < s2 → hi s1 ≤ lo s2 := fun s1 s2 hlt =>
    rank_mono (N + 2) C hfan hrb (top s1) (bot s2) (rawVec_len d k s1 _) (rawVec_len d k s2 _)
      (rawVec_mono_lt d k s1 s2 hlt _ _)
  have hstrict_le : (Finset.univ.filter (fun s : Fin k => lo s < hi s)).card ≤ bPow - 1 :=
    strict_steps_le k bPow lo hi (fun s => ⟨hlo_le_hi s, hrank_lt _⟩) hhi_le_lo
  let flat := Finset.univ.filter (fun s : Fin k => lo s = hi s)
  have hflat_card : bPow * h - (bPow - 1) ≤ flat.card := by
    have hsum := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin k))
      (fun s => lo s < hi s) (fun _ => (1 : Nat))
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at hsum
    have hcomp : Finset.univ.filter (fun s : Fin k => ¬ lo s < hi s) = flat := by
      ext s; simp only [flat, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      have := hlo_le_hi s; omega
    rw [hcomp] at hsum
    have hmul_le : bPow * h ≤ q * h := Nat.mul_le_mul_right h hbPow_le_q
    omega
  have hex_fiber : ∃ l : Fin bPow, h ≤ (flat.filter (fun s => lo s = l.val)).card := by
    by_contra hno
    have hall : ∀ l : Fin bPow, (flat.filter (fun s => lo s = l.val)).card ≤ h - 1 := by
      intro l
      have : ¬ h ≤ (flat.filter (fun s => lo s = l.val)).card := fun hge => hno ⟨l, hge⟩
      omega
    have hsum_fib : (Finset.univ : Finset (Fin bPow)).sum (fun l => (flat.filter (fun s => lo s = l.val)).card) = flat.card := by
      have hpart := Finset.card_eq_sum_card_fiberwise (f := fun s : Fin k => (⟨lo s, hrank_lt _⟩ : Fin bPow))
        (s := flat) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      rw [hpart]
      refine Finset.sum_congr rfl fun l _ =>
        congrArg Finset.card (by ext s; simp only [Finset.mem_filter, Fin.ext_iff])
    have hsum_le : (Finset.univ : Finset (Fin bPow)).sum (fun l => (flat.filter (fun s => lo s = l.val)).card) ≤
        bPow * (h - 1) := by
      calc (Finset.univ : Finset (Fin bPow)).sum (fun l => (flat.filter (fun s => lo s = l.val)).card)
          ≤ (Finset.univ : Finset (Fin bPow)).sum (fun _ => h - 1) := Finset.sum_le_sum fun l _ => hall l
        _ = bPow * (h - 1) := by simp
    have hmul_sub : bPow * (h - 1) = bPow * h - bPow := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have hbPow_le_mul : bPow ≤ bPow * h := Nat.le_mul_of_pos_right bPow hh_pos
    rw [hsum_fib] at hsum_le
    omega
  rcases hex_fiber with ⟨l, hl_card⟩
  set Fl := flat.filter (fun s => lo s = l.val)
  have hFl_rank : ∀ s ∈ Fl, ∀ x, rankV (rawVec d k s x) = l.val := by
    intro s hs x
    rcases Finset.mem_filter.mp hs with ⟨hsflat, hslo⟩
    have hseq : lo s = hi s := (Finset.mem_filter.mp hsflat).2
    have h1 := hlo_le_rank s x
    have h2 := hrank_le_hi s x
    omega
  have hFl_not_eq : ∀ s1 ∈ Fl, ∀ s2 ∈ Fl, ∀ x1 x2 u, u < C.size → isNotOp (gateAt C u).op = true →
      (C.wires (rawVec d k s1 x1)).getD (N + 2 + u) false =
      (C.wires (rawVec d k s2 x2)).getD (N + 2 + u) false := by
    intro s1 hs1 s2 hs2 x1 x2 u hu hnotu
    have humem : u ∈ gates := List.mem_filter.mpr ⟨List.mem_range.mpr hu, hnotu⟩
    rcases List.mem_iff_getElem.mp humem with ⟨idx, hidx, rfl⟩
    have hreq : rankV (rawVec d k s1 x1) = rankV (rawVec d k s2 x2) := by
      rw [hFl_rank s1 hs1 x1, hFl_rank s2 hs2 x2]
    have htb := congrArg (fun v => v.testBit (gates.length - 1 - idx)) hreq
    dsimp only [rankV] at htb
    rw [bitsRank_testBit _ gates idx hidx, bitsRank_testBit _ gates idx hidx] at htb
    have h1 := congrArg Bool.not htb
    simp only [Bool.not_not] at h1
    exact h1
  have hFl_mono_lt : ∀ s1 ∈ Fl, ∀ s2 ∈ Fl, s1 < s2 → ∀ x1 x2 w, w < N + 2 + C.size →
      (C.wires (rawVec d k s1 x1)).getD w false = true →
      (C.wires (rawVec d k s2 x2)).getD w false = true := by
    intro s1 hs1 s2 hs2 hlt x1 x2 w hw h1
    exact mono_pre_wires (N + 2) C hfan hrb (rawVec d k s1 x1) (rawVec d k s2 x2)
      (rawVec_len d k s1 x1) (rawVec_len d k s2 x2) (rawVec_mono_lt d k s1 s2 hlt x1 x2)
      C.size (le_refl _) (fun u hu hnotu => hFl_not_eq s1 hs1 s2 hs2 x1 x2 u hu hnotu) w hw h1
  let allPos : Finset (Fin C.size) := Finset.univ.filter (fun u => isNotOp (gateAt C u.val).op = false)
  have hallPos_card : allPos.card = C.size - b := by
    have hnot_card : (Finset.univ.filter (fun u : Fin C.size => isNotOp (gateAt C u.val).op = true)).card = b := by
      have hnd : gates.Nodup := (List.pairwise_lt_range.filter _).imp (fun h => ne_of_lt h)
      rw [← hgates_len, ← List.toFinset_card_of_nodup hnd]
      refine Finset.card_bij (fun u _ => u.val) ?_ ?_ ?_
      · intro u hu
        rw [List.mem_toFinset]
        exact List.mem_filter.mpr ⟨List.mem_range.mpr u.isLt, (Finset.mem_filter.mp hu).2⟩
      · intro u1 _ u2 _ heq; exact Fin.ext heq
      · intro u hu
        rw [List.mem_toFinset] at hu
        rcases List.mem_filter.mp hu with ⟨hr, hn⟩
        exact ⟨⟨u, List.mem_range.mp hr⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, rfl⟩
    have hsum := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin C.size))
      (fun u => isNotOp (gateAt C u.val).op = true) (fun _ => (1 : Nat))
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at hsum
    have hcomp : Finset.univ.filter (fun u : Fin C.size => ¬ isNotOp (gateAt C u.val).op = true) = allPos := by
      ext u; simp [allPos]
    rw [hcomp] at hsum
    omega
  have htap_ge : ∀ s ∈ Fl, ∀ i j, N + 2 ≤ tap s i j := by
    intro s hs i j
    by_contra hlt
    have hwlt : tap s i j < N + 2 := by omega
    have hbot := hfit s (fun _ => false) i j
    have htop := hfit s (fun _ => true) i j
    simp only [Bool.and_false, Bool.and_true] at hbot htop
    rw [wires_getD_pre C _ (tap s i j) (by rw [rawVec_len]; exact hwlt)] at hbot htop
    by_cases hwN : tap s i j < N
    · have hq : tap s i j / (d + 1) < k := (Nat.div_lt_iff_lt_mul (by omega : 0 < d + 1)).mpr hwN
      have hr : tap s i j % (d + 1) < d + 1 := Nat.mod_lt _ (by omega)
      have hdm : tap s i j = (tap s i j / (d + 1)) * (d + 1) + tap s i j % (d + 1) := by
        have := Nat.div_add_mod (tap s i j) (d + 1); rw [Nat.mul_comm] at this; exact this.symm
      let q0 : Fin k := ⟨tap s i j / (d + 1), hq⟩
      by_cases hr0 : tap s i j % (d + 1) = 0
      · have hweq : tap s i j = q0.val * (d + 1) := by rw [hdm, hr0, Nat.add_zero]
        rw [hweq, rawVec_flag] at hbot htop
        rw [hbot] at htop; exact Bool.false_ne_true htop
      · let z : Fin d := ⟨tap s i j % (d + 1) - 1, by omega⟩
        have hweq : tap s i j = q0.val * (d + 1) + (z.val + 1) := by
          show tap s i j = (tap s i j / (d + 1)) * (d + 1) + ((tap s i j % (d + 1) - 1) + 1); omega
        by_cases hqs : q0 = s
        · rw [hqs] at hweq
          let xtest : Fin d → Bool := fun v => decide (v = z)
          have ht := hfit s xtest i j
          rw [wires_getD_pre C _ (tap s i j) (by rw [rawVec_len]; exact hwlt), hweq, rawVec_data] at ht
          simp only [lt_irrefl, decide_false, decide_true, Bool.false_or, Bool.true_and, xtest] at ht
          have hne : Fin.castAdd n i ≠ Fin.natAdd n j := by
            intro heq
            have hv := congrArg Fin.val heq
            simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
            have := i.isLt; omega
          by_cases h1 : Fin.castAdd n i = z
          · have h2 : Fin.natAdd n j ≠ z := fun h => hne (h1.trans h.symm)
            rw [decide_eq_false h2, Bool.and_false] at ht
            exact Bool.noConfusion ht
          · rw [decide_eq_false h1, Bool.false_and] at ht
            exact Bool.noConfusion ht
        · rw [hweq, rawVec_data] at hbot htop
          rw [decide_eq_false hqs] at hbot htop
          simp only [Bool.false_and, Bool.or_false] at hbot htop
          rw [hbot] at htop; exact Bool.false_ne_true htop
    · by_cases hw0 : tap s i j = N
      · rw [hw0, rawVec_c0] at htop; exact Bool.false_ne_true htop
      · have hw1 : tap s i j = N + 1 := by omega
        rw [hw1, rawVec_c1] at hbot; exact Bool.noConfusion hbot
  have htap_pos : ∀ s ∈ Fl, ∀ i j, isNotOp (gateAt C (tap s i j - (N + 2))).op = false := by
    intro s hs i j
    cases hnot_b : isNotOp (gateAt C (tap s i j - (N + 2))).op
    · rfl
    · have hge := htap_ge s hs i j
      have hlt : tap s i j - (N + 2) < C.size := by have := htap s i j; omega
      have heq := hFl_not_eq s hs s hs (fun _ => false) (fun _ => true) (tap s i j - (N + 2)) hlt hnot_b
      have hadd : N + 2 + (tap s i j - (N + 2)) = tap s i j := by omega
      rw [hadd, hfit s (fun _ => false) i j, hfit s (fun _ => true) i j] at heq
      simp at heq
  have hCsize_pos : 0 < C.size := by
    rcases Finset.card_pos.mp (by omega : 0 < Fl.card) with ⟨s0, hs0⟩
    have hge := htap_ge s0 hs0 ⟨0, hn⟩ ⟨0, hn⟩
    have hlt := htap s0 ⟨0, hn⟩ ⟨0, hn⟩
    omega
  let dom : Finset (Fin k × Fin n × Fin n) := Fl ×ˢ (Finset.univ ×ˢ Finset.univ)
  have hdom_card : dom.card = Fl.card * n ^ 2 := by
    dsimp only [dom]
    rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    ring
  have hcard_le : dom.card ≤ allPos.card := by
    refine Finset.card_le_card_of_injOn (fun p => ⟨tap p.1 p.2.1 p.2.2 - (N + 2), by
      have := htap p.1 p.2.1 p.2.2; omega⟩) ?_ ?_
    · intro p hp
      have hs : p.1 ∈ Fl := (Finset.mem_product.mp hp).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htap_pos p.1 hs p.2.1 p.2.2⟩
    · intro p1 hp1 p2 hp2 hEq
      have hs1 : p1.1 ∈ Fl := (Finset.mem_product.mp hp1).1
      have hs2 : p2.1 ∈ Fl := (Finset.mem_product.mp hp2).1
      have hge1 := htap_ge p1.1 hs1 p1.2.1 p1.2.2
      have hge2 := htap_ge p2.1 hs2 p2.2.1 p2.2.2
      have hval : tap p1.1 p1.2.1 p1.2.2 - (N + 2) = tap p2.1 p2.2.1 p2.2.2 - (N + 2) := congrArg Fin.val hEq
      have hteq : tap p1.1 p1.2.1 p1.2.2 = tap p2.1 p2.2.1 p2.2.2 := by omega
      have hs_eq : p1.1 = p2.1 := by
        rcases lt_trichotomy p1.1 p2.1 with hlt | heq | hgt
        · have h1 := hfit p1.1 (fun _ => true) p1.2.1 p1.2.2
          simp only [Bool.and_true] at h1
          have h2 := hFl_mono_lt p1.1 hs1 p2.1 hs2 hlt (fun _ => true) (fun _ => false)
            (tap p1.1 p1.2.1 p1.2.2) (htap p1.1 p1.2.1 p1.2.2) h1
          rw [hteq, hfit p2.1 (fun _ => false) p2.2.1 p2.2.2] at h2
          simp at h2
        · exact heq
        · have h1 := hfit p2.1 (fun _ => true) p2.2.1 p2.2.2
          simp only [Bool.and_true] at h1
          have h2 := hFl_mono_lt p2.1 hs2 p1.1 hs1 hgt (fun _ => true) (fun _ => false)
            (tap p2.1 p2.2.1 p2.2.2) (htap p2.1 p2.2.1 p2.2.2) h1
          rw [← hteq, hfit p1.1 (fun _ => false) p1.2.1 p1.2.2] at h2
          simp at h2
      rcases p1 with ⟨s1, i1, j1⟩
      rcases p2 with ⟨s2, i2, j2⟩
      dsimp only at hs_eq hteq
      subst hs_eq
      let xtest : Fin d → Bool := fun z => decide (z = Fin.castAdd n i1 ∨ z = Fin.natAdd n j1)
      have h1 := hfit s1 xtest i1 j1
      have h2 := hfit s1 xtest i2 j2
      rw [← hteq] at h2
      have hlhs : (xtest (Fin.castAdd n i1) && xtest (Fin.natAdd n j1)) = true := by
        simp [xtest]
      rw [hlhs] at h1
      rw [h1] at h2
      have hpair := Bool.and_eq_true _ _ |>.mp h2.symm
      have hi12 : i2 = i1 := by
        rcases of_decide_eq_true hpair.1 with h | h
        · exact Fin.ext (by have := congrArg Fin.val h; simp at this; exact this)
        · have := congrArg Fin.val h; simp at this; have := i2.isLt; omega
      have hj12 : j2 = j1 := by
        rcases of_decide_eq_true hpair.2 with h | h
        · have := congrArg Fin.val h; simp at this; have := i1.isLt; omega
        · exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
      subst hi12; subst hj12; rfl
  have hmul : h * n ^ 2 ≤ Fl.card * n ^ 2 := Nat.mul_le_mul_right _ hl_card
  rw [hallPos_card] at hcard_le
  omega

private def foldSharp (N mid nMidIdx : Nat) (T : Nat → Nat) :
    Nat → List Gate → (Nat → Nat) → (Nat → Nat) → List Gate × (Nat → Nat) × (Nat → Nat)
  | 0, gs, fMap, aMap => (gs, fMap, aMap)
  | m + 1, gs, fMap, aMap =>
    let prev := foldSharp N mid nMidIdx T m gs fMap aMap
    let j1 := m + 1
    let aIdx := N + 2 + prev.1.length
    let g1 := prev.1 ++ [⟨GateOp.and, [T j1, nMidIdx]⟩]
    let oIdx := N + 2 + g1.length
    let g2 := g1 ++ [⟨GateOp.or, [aIdx, T (mid + j1)]⟩]
    (g2, fun r => if r = j1 then oIdx else prev.2.1 r, fun r => if r = j1 then aIdx else prev.2.2 r)

private def unfoldSharp (N mid nMidIdx : Nat) (T : Nat → Nat) (decMap : Nat → Nat) :
    Nat → List Gate → (Nat → Nat) → List Gate × (Nat → Nat)
  | 0, gs, uMap => (gs, uMap)
  | m + 1, gs, uMap =>
    let prev := unfoldSharp N mid nMidIdx T decMap m gs uMap
    let loIdx := N + 2 + prev.1.length
    let g1 := prev.1 ++ [⟨GateOp.and, [decMap m, nMidIdx]⟩]
    let hiIdx := N + 2 + g1.length
    let g2 := g1 ++ [⟨GateOp.and, [decMap m, T mid]⟩]
    (g2, fun r => if r = m then loIdx else if r = mid + m then hiIdx else prev.2 r)

private def buildSharpDecoder (N : Nat) : Nat → List Gate → (Nat → Nat) → List Gate × (Nat → Nat)
  | 0, gs, _ => (gs, fun _ => N + 1)
  | 1, gs, T =>
    let n1 := N + 2 + gs.length
    (gs ++ [⟨GateOp.not, [T 1]⟩], fun j => if j = 0 then n1 else T 1)
  | B + 2, gs, T =>
    let mid := 2 ^ (B + 1)
    let nMidIdx := N + 2 + gs.length
    let gs1 := gs ++ [⟨GateOp.not, [T mid]⟩]
    let folded := foldSharp N mid nMidIdx T (mid - 1) gs1 (fun _ => N) (fun _ => N)
    let dec := buildSharpDecoder N (B + 1) folded.1 folded.2.1
    let baseMap : Nat → Nat := fun r =>
      if r = mid - 1 then folded.2.2 (mid - 1)
      else if r = 2 * mid - 1 then T (2 * mid - 1)
      else N
    unfoldSharp N mid nMidIdx T dec.2 (mid - 1) dec.1 baseMap

private lemma foldSharp_spec (N mid : Nat) (hmid : 2 ≤ mid) (gs : List Gate) (T : Nat → Nat)
    (hgs : ValidGates N gs)
    (hT : ∀ j, 1 ≤ j → j < 2 * mid → T j < N + 2 + gs.length) :
    let nMidIdx := N + 2 + gs.length
    let gs1 := gs ++ [⟨GateOp.not, [T mid]⟩]
    ∀ m ≤ mid - 1,
      let res := foldSharp N mid nMidIdx T m gs1 (fun _ => N) (fun _ => N)
      (∃ e1, res.1 = gs1 ++ e1 ∧ notCountL e1 = 0 ∧ posCount e1 = 2 * m) ∧
      ValidGates N res.1 ∧
      (∀ j, 1 ≤ j → j ≤ m → res.2.1 j < N + 2 + res.1.length ∧ res.2.2 j < N + 2 + res.1.length) ∧
      ∀ (x : List Bool) (v : Nat), x.length = N + 2 → v < 2 * mid →
        (∀ j, 1 ≤ j → j < 2 * mid → (evalW gs x).getD (T j) false = decide (j ≤ v)) →
        ∀ j, 1 ≤ j → j ≤ m →
          (evalW res.1 x).getD (res.2.1 j) false = decide (j ≤ (if v < mid then v else v - mid)) ∧
          (evalW res.1 x).getD (res.2.2 j) false = decide (j ≤ v ∧ v < mid) := by
  intro nMidIdx gs1
  have hTmid : T mid < N + 2 + gs.length := hT mid (by omega) (by omega)
  have hval1 : ValidGates N gs1 :=
    validGates_snoc N gs ⟨GateOp.not, [T mid]⟩ hgs (Or.inr (Or.inr rfl)) (by simp) (by
      intro i hi; simp at hi; subst hi; exact hTmid)
  intro m
  induction m with
  | zero =>
    intro _
    dsimp only [foldSharp]
    refine ⟨⟨[], by simp, rfl, by simp [posCount]⟩, hval1, fun j h1 h2 => by omega, fun _ _ _ _ _ j h1 h2 => by omega⟩
  | succ m ihm =>
    intro hm
    rcases ihm (by omega) with ⟨⟨e1, heq1, hnot1, hpos1⟩, hvalf, hbdf, hevalf⟩
    set prev := foldSharp N mid nMidIdx T m gs1 (fun _ => N) (fun _ => N)
    let j1 := m + 1
    let aIdx := N + 2 + prev.1.length
    let g1 := prev.1 ++ [⟨GateOp.and, [T j1, nMidIdx]⟩]
    let oIdx := N + 2 + g1.length
    let g2 := g1 ++ [⟨GateOp.or, [aIdx, T (mid + j1)]⟩]
    have hstep_eq : foldSharp N mid nMidIdx T (m + 1) gs1 (fun _ => N) (fun _ => N) =
        (g2, fun r => if r = j1 then oIdx else prev.2.1 r, fun r => if r = j1 then aIdx else prev.2.2 r) := rfl
    rw [hstep_eq]
    have hgs_le_prev : gs.length + 1 ≤ prev.1.length := by rw [heq1, List.length_append]; simp [gs1]
    have hTj1 : T j1 < N + 2 + gs.length := hT j1 (by omega) (by omega)
    have hTmidj1 : T (mid + j1) < N + 2 + gs.length := hT (mid + j1) (by omega) (by omega)
    have hval_g1 : ValidGates N g1 :=
      validGates_snoc N prev.1 ⟨GateOp.and, [T j1, nMidIdx]⟩ hvalf (Or.inl rfl) (by simp) (by
        intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
    have hval_g2 : ValidGates N g2 :=
      validGates_snoc N g1 ⟨GateOp.or, [aIdx, T (mid + j1)]⟩ hval_g1 (Or.inr (Or.inl rfl)) (by simp) (by
        intro i hi; simp at hi; rcases hi with rfl | rfl
        · simp [g1, aIdx]
        · simp only [g1, List.length_append, List.length_singleton]; omega)
    refine ⟨⟨e1 ++ [⟨GateOp.and, [T j1, nMidIdx]⟩, ⟨GateOp.or, [aIdx, T (mid + j1)]⟩], ?_, ?_, ?_⟩,
      hval_g2, ?_, ?_⟩
    · simp [g2, g1, heq1, List.append_assoc]
    · rw [notCountL_append, hnot1]; rfl
    · rw [posCount_append, hpos1]
      have : posCount [⟨GateOp.and, [T j1, nMidIdx]⟩, ⟨GateOp.or, [aIdx, T (mid + j1)]⟩] = 2 := rfl
      omega
    · intro j hj1 hjm
      dsimp only
      by_cases heq : j = j1
      · rw [if_pos heq, if_pos heq]
        refine ⟨by simp [g2, oIdx], ?_⟩
        simp only [g2, g1, aIdx, List.length_append, List.length_singleton]; omega
      · rw [if_neg heq, if_neg heq]
        rcases hbdf j hj1 (by omega) with ⟨h1, h2⟩
        simp only [g2, g1, List.length_append, List.length_singleton]
        exact ⟨by omega, by omega⟩
    · intro x v hx hv hTx j hj1 hjm
      dsimp only
      by_cases heq : j = j1
      · rw [if_pos heq, if_pos heq, heq]
        have ha_val : (evalW g1 x).getD aIdx false =
            ((evalW gs x).getD (T j1) false && !(evalW gs x).getD (T mid) false) := by
          have hlast1 := evalW_snoc_last prev.1 ⟨GateOp.and, [T j1, nMidIdx]⟩ x
          rw [hx] at hlast1
          change (evalW (prev.1 ++ [⟨GateOp.and, [T j1, nMidIdx]⟩]) x).getD (N + 2 + prev.1.length) false = _
          rw [hlast1]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          have h1 : (evalW prev.1 x).getD (T j1) false = (evalW gs x).getD (T j1) false := by
            rw [heq1]; dsimp only [gs1]; rw [List.append_assoc]
            exact evalW_append_pre gs ([⟨GateOp.not, [T mid]⟩] ++ e1) x (T j1) (by rw [hx]; exact hTj1)
          have h2 : (evalW prev.1 x).getD nMidIdx false = !(evalW gs x).getD (T mid) false := by
            rw [heq1, evalW_append_pre gs1 e1 x nMidIdx (by rw [hx]; simp [gs1, nMidIdx])]
            have hnotv := evalW_snoc_last gs ⟨GateOp.not, [T mid]⟩ x
            rw [hx] at hnotv
            change (evalW (gs ++ [⟨GateOp.not, [T mid]⟩]) x).getD (N + 2 + gs.length) false = _
            rw [hnotv]; simp [GateOp.eval]
          rw [h1, h2]
        have hT2_val : (evalW g1 x).getD (T (mid + j1)) false = (evalW gs x).getD (T (mid + j1)) false := by
          dsimp only [g1]; rw [heq1]; dsimp only [gs1]; rw [List.append_assoc, List.append_assoc]
          exact evalW_append_pre gs _ x (T (mid + j1)) (by rw [hx]; exact hTmidj1)
        constructor
        · have hlast2 := evalW_snoc_last g1 ⟨GateOp.or, [aIdx, T (mid + j1)]⟩ x
          rw [hx] at hlast2
          change (evalW (g1 ++ [⟨GateOp.or, [aIdx, T (mid + j1)]⟩]) x).getD (N + 2 + g1.length) false = _
          rw [hlast2]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha_val, hT2_val, hTx j1 (by omega) (by omega), hTx mid (by omega) (by omega),
            hTx (mid + j1) (by omega) (by omega)]
          by_cases hvm : v < mid
          · rw [if_pos hvm, decide_eq_false (by omega : ¬ mid ≤ v), decide_eq_false (by omega : ¬ mid + j1 ≤ v)]
            simp
          · rw [if_neg hvm, decide_eq_true (by omega : mid ≤ v)]
            simp only [Bool.not_true, Bool.and_false, Bool.false_or]
            exact decide_eq_decide.mpr (by omega)
        · rw [evalW_append_pre g1 _ x aIdx (by rw [hx]; simp [g1, aIdx])]
          rw [ha_val, hTx j1 (by omega) (by omega), hTx mid (by omega) (by omega)]
          by_cases hvm : v < mid
          · rw [decide_eq_false (by omega : ¬ mid ≤ v), Bool.not_false, Bool.and_true]
            exact decide_eq_decide.mpr (by omega)
          · rw [decide_eq_true (by omega : mid ≤ v), Bool.not_true, Bool.and_false]
            exact (decide_eq_false (by omega)).symm
      · rw [if_neg heq, if_neg heq]
        rcases hbdf j hj1 (by omega) with ⟨hbd1, hbd2⟩
        rcases hevalf x v hx hv hTx j hj1 (by omega) with ⟨he1, he2⟩
        dsimp only [g2, g1]; rw [List.append_assoc]
        rw [evalW_append_pre prev.1 _ x (prev.2.1 j) (by rw [hx]; exact hbd1)]
        rw [evalW_append_pre prev.1 _ x (prev.2.2 j) (by rw [hx]; exact hbd2)]
        exact ⟨he1, he2⟩

private lemma buildSharpDecoder_spec (N : Nat) :
    ∀ (B : Nat) (gs : List Gate) (T : Nat → Nat),
      ValidGates N gs →
      (∀ j, 1 ≤ j → j < 2 ^ B → T j < N + 2 + gs.length) →
      let res := buildSharpDecoder N B gs T
      (∃ extra, res.1 = gs ++ extra ∧ notCountL extra = B ∧ posCount extra ≤ 4 * (2 ^ B - 1 - B)) ∧
      ValidGates N res.1 ∧
      (∀ j < 2 ^ B, res.2 j < N + 2 + res.1.length) ∧
      ∀ (x : List Bool) (v : Nat), x.length = N + 2 → x.getD (N + 1) false = true → v < 2 ^ B →
        (∀ j, 1 ≤ j → j < 2 ^ B → (evalW gs x).getD (T j) false = decide (j ≤ v)) →
        ∀ j < 2 ^ B, (evalW res.1 x).getD (res.2 j) false = decide (j = v) := by
  intro B
  induction B using Nat.strong_induction_on with
  | ind B ih =>
    intro gs T hgs hT
    match B with
    | 0 =>
      dsimp only [buildSharpDecoder]
      refine ⟨⟨[], by simp, rfl, by simp [posCount]⟩, hgs, fun j _ => by omega, ?_⟩
      intro x v hx hx1 hv _ j hj
      have hv0 : v = 0 := by omega
      have hj0 : j = 0 := by omega
      subst hv0; subst hj0
      rw [evalW_pre gs x (N + 1) (by omega), hx1]; rfl
    | 1 =>
      dsimp only [buildSharpDecoder]
      have hT1 : T 1 < N + 2 + gs.length := hT 1 (by omega) (by omega)
      have hval1 : ValidGates N (gs ++ [⟨GateOp.not, [T 1]⟩]) :=
        validGates_snoc N gs ⟨GateOp.not, [T 1]⟩ hgs (Or.inr (Or.inr rfl)) (by simp) (by
          intro i hi; simp at hi; subst hi; exact hT1)
      refine ⟨⟨[⟨GateOp.not, [T 1]⟩], rfl, rfl, by simp [posCount, isNotOp]⟩, hval1, ?_, ?_⟩
      · intro j hj
        by_cases hj0 : j = 0
        · rw [if_pos hj0]; simp
        · rw [if_neg hj0]; simp only [List.length_append, List.length_singleton]; omega
      · intro x v hx _ hv hTx j hj
        have hv01 : v = 0 ∨ v = 1 := by omega
        have hj01 : j = 0 ∨ j = 1 := by omega
        by_cases hj0 : j = 0
        · rw [if_pos hj0, hj0]
          have hlast := evalW_snoc_last gs ⟨GateOp.not, [T 1]⟩ x
          rw [hx] at hlast
          rw [hlast]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
          rw [hTx 1 (by omega) (by omega)]
          rcases hv01 with rfl | rfl <;> decide
        · have hj1 : j = 1 := hj01.resolve_left hj0
          rw [if_neg hj0, hj1]
          rw [evalW_append_pre gs [⟨GateOp.not, [T 1]⟩] x (T 1) (by rw [hx]; exact hT1)]
          rw [hTx 1 (by omega) (by omega)]
          rcases hv01 with rfl | rfl <;> decide
    | B + 2 =>
      set mid := 2 ^ (B + 1)
      have hmid2 : 2 ≤ mid := by
        dsimp only [mid]
        have : 1 ≤ 2 ^ B := Nat.one_le_two_pow
        have : 2 ^ (B + 1) = 2 * 2 ^ B := by rw [pow_succ, Nat.mul_comm]
        omega
      have hpow2 : 2 ^ (B + 2) = 2 * mid := by dsimp only [mid]; rw [pow_succ, Nat.mul_comm]
      set nMidIdx := N + 2 + gs.length
      set gs1 := gs ++ [⟨GateOp.not, [T mid]⟩]
      have hT' : ∀ j, 1 ≤ j → j < 2 * mid → T j < N + 2 + gs.length :=
        fun j h1 h2 => hT j h1 (by omega)
      rcases foldSharp_spec N mid hmid2 gs T hgs hT' (mid - 1) (le_refl _) with
        ⟨⟨e1, heq1, hnot1, hpos1⟩, hvalf, hbdf, hevalf⟩
      set folded := foldSharp N mid nMidIdx T (mid - 1) gs1 (fun _ => N) (fun _ => N)
      rcases ih (B + 1) (by omega) folded.1 folded.2.1 hvalf (fun j hj1 hjm => (hbdf j hj1 (by omega)).1) with
        ⟨⟨e2, heq2, hnot2, hpos2⟩, hvald, hbdd, hevald⟩
      set dec := buildSharpDecoder N (B + 1) folded.1 folded.2.1
      have hgs1_pre : dec.1 = gs1 ++ (e1 ++ e2) := by rw [heq2, heq1, List.append_assoc]
      have hgs_pre : dec.1 = gs ++ ([⟨GateOp.not, [T mid]⟩] ++ e1 ++ e2) := by
        rw [hgs1_pre]; simp [gs1, List.append_assoc]
      have hTmid : T mid < N + 2 + gs.length := hT' mid (by omega) (by omega)
      have hTlast : T (2 * mid - 1) < N + 2 + gs.length := hT' (2 * mid - 1) (by omega) (by omega)
      let baseMap : Nat → Nat := fun r =>
        if r = mid - 1 then folded.2.2 (mid - 1)
        else if r = 2 * mid - 1 then T (2 * mid - 1)
        else N
      have hgs_le_dec : gs.length + 1 ≤ dec.1.length := by rw [hgs_pre, List.length_append]; simp
      have haLast_bd : folded.2.2 (mid - 1) < N + 2 + dec.1.length := by
        have h1 := (hbdf (mid - 1) (by omega) (le_refl _)).2
        rw [heq2, List.length_append]; omega
      have hunfold : ∀ m ≤ mid - 1,
          let u := unfoldSharp N mid nMidIdx T dec.2 m dec.1 baseMap
          (∃ e3, u.1 = dec.1 ++ e3 ∧ notCountL e3 = 0 ∧ posCount e3 = 2 * m) ∧
          ValidGates N u.1 ∧
          (∀ j < m, u.2 j < N + 2 + u.1.length ∧ u.2 (mid + j) < N + 2 + u.1.length) ∧
          u.2 (mid - 1) = folded.2.2 (mid - 1) ∧ u.2 (2 * mid - 1) = T (2 * mid - 1) ∧
          ∀ (x : List Bool) (v : Nat), x.length = N + 2 → x.getD (N + 1) false = true → v < 2 * mid →
            (∀ j, 1 ≤ j → j < 2 * mid → (evalW gs x).getD (T j) false = decide (j ≤ v)) →
            ∀ j < m, (evalW u.1 x).getD (u.2 j) false = decide (j = v) ∧
              (evalW u.1 x).getD (u.2 (mid + j)) false = decide (mid + j = v) := by
        intro m
        induction m with
        | zero =>
          intro _
          dsimp only [unfoldSharp]
          refine ⟨⟨[], by simp, rfl, by simp [posCount]⟩, hvald, fun j hj => by omega, ?_, ?_, fun _ _ _ _ _ _ j hj => by omega⟩
          · dsimp only [baseMap]; rw [if_pos rfl]
          · dsimp only [baseMap]; rw [if_neg (by omega), if_pos rfl]
        | succ m ihm =>
          intro hm
          rcases ihm (by omega) with ⟨⟨e3, heq3, hnot3, hpos3⟩, hvalu, hbdu, hlast1, hlast2, hevalu⟩
          set prev := unfoldSharp N mid nMidIdx T dec.2 m dec.1 baseMap
          let loIdx := N + 2 + prev.1.length
          let g1 := prev.1 ++ [⟨GateOp.and, [dec.2 m, nMidIdx]⟩]
          let hiIdx := N + 2 + g1.length
          let g2 := g1 ++ [⟨GateOp.and, [dec.2 m, T mid]⟩]
          have hstep_eq : unfoldSharp N mid nMidIdx T dec.2 (m + 1) dec.1 baseMap =
              (g2, fun r => if r = m then loIdx else if r = mid + m then hiIdx else prev.2 r) := rfl
          rw [hstep_eq]
          have hdec_le_prev : dec.1.length ≤ prev.1.length := by rw [heq3, List.length_append]; omega
          have hdm_lt : dec.2 m < N + 2 + dec.1.length := hbdd m (by omega)
          have hval_g1 : ValidGates N g1 :=
            validGates_snoc N prev.1 ⟨GateOp.and, [dec.2 m, nMidIdx]⟩ hvalu (Or.inl rfl) (by simp) (by
              intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
          have hval_g2 : ValidGates N g2 :=
            validGates_snoc N g1 ⟨GateOp.and, [dec.2 m, T mid]⟩ hval_g1 (Or.inl rfl) (by simp) (by
              intro i hi; simp at hi; rcases hi with rfl | rfl
              · simp only [g1, List.length_append, List.length_singleton]; omega
              · simp only [g1, List.length_append, List.length_singleton]; omega)
          refine ⟨⟨e3 ++ [⟨GateOp.and, [dec.2 m, nMidIdx]⟩, ⟨GateOp.and, [dec.2 m, T mid]⟩], ?_, ?_, ?_⟩,
            hval_g2, ?_, ?_, ?_, ?_⟩
          · simp [g2, g1, heq3, List.append_assoc]
          · rw [notCountL_append, hnot3]; rfl
          · rw [posCount_append, hpos3]
            have : posCount [⟨GateOp.and, [dec.2 m, nMidIdx]⟩, ⟨GateOp.and, [dec.2 m, T mid]⟩] = 2 := rfl
            omega
          · intro j hj
            dsimp only
            by_cases heq : j = m
            · rw [if_pos heq, if_neg (by omega : mid + j ≠ m), if_pos (by omega : mid + j = mid + m)]
              refine ⟨by simp only [g2, g1, loIdx, List.length_append, List.length_singleton]; omega,
                      by simp [g2, hiIdx]⟩
            · rw [if_neg heq, if_neg (by omega : j ≠ mid + m), if_neg (by omega : mid + j ≠ m),
                if_neg (by omega : mid + j ≠ mid + m)]
              rcases hbdu j (by omega) with ⟨h1, h2⟩
              simp only [g2, g1, List.length_append, List.length_singleton]
              exact ⟨by omega, by omega⟩
          · dsimp only
            rw [if_neg (by omega), if_neg (by omega)]; exact hlast1
          · dsimp only
            rw [if_neg (by omega), if_neg (by omega)]; exact hlast2
          · intro x v hx hx1 hv hTx j hj
            dsimp only
            by_cases heq : j = m
            · rw [if_pos heq, if_neg (by omega : mid + j ≠ m), if_pos (by omega : mid + j = mid + m)]
              subst heq
              have hdec_val : (evalW dec.1 x).getD (dec.2 j) false =
                  decide (j = if v < mid then v else v - mid) := by
                have hv' : (if v < mid then v else v - mid) < mid := by split <;> omega
                exact hevald x (if v < mid then v else v - mid) hx hx1 hv'
                  (fun r hr1 hrm => (hevalf x v hx hv hTx r hr1 (by omega)).1) j (by omega)
              have hnMid_val : (evalW prev.1 x).getD nMidIdx false = !(evalW gs x).getD (T mid) false := by
                rw [heq3, hgs1_pre, List.append_assoc, evalW_append_pre gs1 _ x nMidIdx (by rw [hx]; simp [gs1, nMidIdx])]
                have hnotv := evalW_snoc_last gs ⟨GateOp.not, [T mid]⟩ x
                rw [hx] at hnotv
                change (evalW (gs ++ [⟨GateOp.not, [T mid]⟩]) x).getD (N + 2 + gs.length) false = _
                rw [hnotv]; simp [GateOp.eval]
              have hTmid_val : (evalW g1 x).getD (T mid) false = (evalW gs x).getD (T mid) false := by
                dsimp only [g1]; rw [heq3, hgs_pre]; simp only [List.append_assoc]
                exact evalW_append_pre gs _ x (T mid) (by rw [hx]; exact hTmid)
              constructor
              · rw [evalW_append_pre g1 _ x loIdx (by rw [hx]; simp [g1, loIdx])]
                have hlast1 := evalW_snoc_last prev.1 ⟨GateOp.and, [dec.2 j, nMidIdx]⟩ x
                rw [hx] at hlast1
                change (evalW (prev.1 ++ [⟨GateOp.and, [dec.2 j, nMidIdx]⟩]) x).getD (N + 2 + prev.1.length) false = _
                rw [hlast1]
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                rw [heq3, evalW_append_pre dec.1 e3 x (dec.2 j) (by rw [hx]; exact hdm_lt)]
                rw [← heq3, hnMid_val, hdec_val, hTx mid (by omega) (by omega)]
                by_cases hvm : v < mid
                · rw [if_pos hvm, decide_eq_false (by omega : ¬ mid ≤ v)]; simp
                · rw [if_neg hvm, decide_eq_true (by omega : mid ≤ v), decide_eq_false (by omega : j ≠ v)]; simp
              · have hlast2 := evalW_snoc_last g1 ⟨GateOp.and, [dec.2 j, T mid]⟩ x
                rw [hx] at hlast2
                change (evalW (g1 ++ [⟨GateOp.and, [dec.2 j, T mid]⟩]) x).getD (N + 2 + g1.length) false = _
                rw [hlast2]
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                rw [hTmid_val]
                have hdj_g1 : (evalW g1 x).getD (dec.2 j) false = (evalW dec.1 x).getD (dec.2 j) false := by
                  dsimp only [g1]; rw [heq3, List.append_assoc]
                  exact evalW_append_pre dec.1 _ x (dec.2 j) (by rw [hx]; exact hdm_lt)
                rw [hdj_g1, hdec_val, hTx mid (by omega) (by omega)]
                by_cases hvm : v < mid
                · rw [if_pos hvm, decide_eq_false (by omega : ¬ mid ≤ v), decide_eq_false (by omega : mid + j ≠ v)]; simp
                · rw [if_neg hvm, decide_eq_true (by omega : mid ≤ v)]
                  simp only [Bool.and_true]
                  exact decide_eq_decide.mpr (by omega)
            · rw [if_neg heq, if_neg (by omega : j ≠ mid + m), if_neg (by omega : mid + j ≠ m),
                if_neg (by omega : mid + j ≠ mid + m)]
              rcases hbdu j (by omega) with ⟨hbd1, hbd2⟩
              rcases hevalu x v hx hx1 hv hTx j (by omega) with ⟨he1, he2⟩
              dsimp only [g2, g1]; rw [List.append_assoc]
              rw [evalW_append_pre prev.1 _ x (prev.2 j) (by rw [hx]; exact hbd1)]
              rw [evalW_append_pre prev.1 _ x (prev.2 (mid + j)) (by rw [hx]; exact hbd2)]
              exact ⟨he1, he2⟩
      rcases hunfold (mid - 1) (le_refl _) with ⟨⟨e3, heq3, hnot3, hpos3⟩, hvalu, hbdu, hlast1, hlast2, hevalu⟩
      have hbuild_eq : buildSharpDecoder N (B + 2) gs T =
          unfoldSharp N mid nMidIdx T dec.2 (mid - 1) dec.1 baseMap := rfl
      rw [hbuild_eq]
      refine ⟨⟨[⟨GateOp.not, [T mid]⟩] ++ e1 ++ e2 ++ e3, ?_, ?_, ?_⟩, hvalu, ?_, ?_⟩
      · rw [heq3, hgs_pre, List.append_assoc, List.append_assoc]
      · rw [notCountL_append, notCountL_append, notCountL_append, hnot1, hnot2, hnot3]
        have : notCountL [⟨GateOp.not, [T mid]⟩] = 1 := rfl
        omega
      · rw [posCount_append, posCount_append, posCount_append, hpos1, hpos3]
        have hnot0 : posCount [⟨GateOp.not, [T mid]⟩] = 0 := rfl
        have hle_mid : B + 1 ≤ mid - 1 := le_two_pow_sub_one (B + 1)
        omega
      · intro j hj
        by_cases hjm1 : j < mid - 1
        · exact (hbdu j hjm1).1
        · by_cases hj_eq1 : j = mid - 1
          · rw [hj_eq1, hlast1, heq3, List.length_append]; omega
          · by_cases hj_eq2 : j = 2 * mid - 1
            · rw [hj_eq2, hlast2, heq3, List.length_append]; omega
            · have hj' : j - mid < mid - 1 := by omega
              have heqj : j = mid + (j - mid) := by omega
              rw [heqj]
              exact (hbdu (j - mid) hj').2
      · intro x v hx hx1 hv hTx j hj
        have hTx' : ∀ r, 1 ≤ r → r < 2 * mid → (evalW gs x).getD (T r) false = decide (r ≤ v) :=
          fun r hr1 hr2 => hTx r hr1 (by omega)
        by_cases hjm1 : j < mid - 1
        · exact (hevalu x v hx hx1 (by omega) hTx' j hjm1).1
        · by_cases hj_eq1 : j = mid - 1
          · rw [hj_eq1, hlast1, heq3, heq2, List.append_assoc,
              evalW_append_pre folded.1 _ x (folded.2.2 (mid - 1))
                (by rw [hx]; exact (hbdf (mid - 1) (by omega) (le_refl _)).2)]
            rw [(hevalf x v hx (by omega) hTx' (mid - 1) (by omega) (le_refl _)).2]
            exact decide_eq_decide.mpr (by omega)
          · by_cases hj_eq2 : j = 2 * mid - 1
            · rw [hj_eq2, hlast2, heq3, hgs_pre, List.append_assoc,
                evalW_append_pre gs _ x (T (2 * mid - 1)) (by rw [hx]; exact hTlast)]
              rw [hTx' (2 * mid - 1) (by omega) (by omega)]
              exact decide_eq_decide.mpr (by omega)
            · have hj' : j - mid < mid - 1 := by omega
              have heqj : j = mid + (j - mid) := by omega
              rw [heqj]
              exact (hevalu x v hx hx1 (by omega) hTx' (j - mid) hj').2

private lemma upper_bound_proof (B m n e : Nat) (hm : 0 < m) (hn : 0 < n) (he : e ≤ B) :
    let k := 2 ^ B * m
    let d := n + n
    let N := k * (d + 1)
    let q := 2 ^ e
    let h := k / q
    ∃ (C : Circuit) (tap : Fin k → Fin n → Fin n → Nat),
      FanInTwo C ∧ ReadsBack (N + 2) C ∧ C.output < N + 2 + C.size ∧
      (∀ s i j, tap s i j < N + 2 + C.size) ∧
      (∀ s x i j, (C.wires (rawVec d k s x)).getD (tap s i j) false =
        (x (Fin.castAdd n i) && x (Fin.natAdd n j))) ∧
      notCount C ≤ e ∧
      C.size - notCount C ≤ h * n ^ 2 + (4 * n * h) * (q - 1) + 4 * (q - 1 - e) := by
  intro k d N q h
  have hqh : q * h = k := by
    dsimp only [q, h, k]
    have hpow : 2 ^ B = 2 ^ e * 2 ^ (B - e) := by rw [← pow_add]; congr 1; omega
    have hkmul : 2 ^ B * m = 2 ^ e * (2 ^ (B - e) * m) := by rw [hpow]; ring
    rw [hkmul, Nat.mul_div_cancel_left _ (Nat.two_pow_pos e)]
  have hq_pos : 1 ≤ q := Nat.one_le_two_pow
  have hh_pos : 1 ≤ h := by
    have hk_pos : 1 ≤ k := Nat.mul_pos (Nat.two_pow_pos B) hm
    exact Nat.pos_of_ne_zero fun hh0 => by rw [hh0, Nat.mul_zero] at hqh; omega
  let T : Nat → Nat := fun j => (j * h) * (d + 1)
  have hT_bd : ∀ j, 1 ≤ j → j < q → T j < N + 2 := by
    intro j _ hj
    dsimp only [T, N]
    have h1 : j * h < k := by
      have : (j + 1) * h ≤ q * h := Nat.mul_le_mul_right h hj
      have : (j + 1) * h = j * h + h := by ring
      omega
    have h2 : (j * h) * (d + 1) < k * (d + 1) := Nat.mul_lt_mul_of_pos_right h1 (by omega)
    omega
  rcases buildSharpDecoder_spec N e [] T (validGates_nil N) (fun j h1 h2 => by
      simp only [List.length_nil, Nat.add_zero]; exact hT_bd j h1 h2) with
    ⟨⟨exDec, heqDec, hnotDec, hposDec⟩, hvalDec, hbdDec, hevalDec⟩
  set dec := buildSharpDecoder N e [] T
  have hdec_eval : ∀ (s : Fin k) (x : Fin d → Bool) (p : Nat), p < q →
      (evalW dec.1 (rawVec d k s x)).getD (dec.2 p) false = decide (p = s.val / h) := by
    intro s x p hp
    have hsv_lt : s.val / h < q := by
      have h1 : s.val < q * h := by rw [hqh]; exact s.isLt
      exact (Nat.div_lt_iff_lt_mul (by omega : 0 < h)).mpr h1
    exact hevalDec (rawVec d k s x) (s.val / h) (rawVec_len d k s x) (rawVec_c1 d k s x) hsv_lt
      (fun j hj1 hjq => by
        have hjh : j * h < k := by
          have : (j + 1) * h ≤ q * h := Nat.mul_le_mul_right h hjq
          have : (j + 1) * h = j * h + h := by ring
          omega
        change (rawVec d k s x).getD ((⟨j * h, hjh⟩ : Fin k).val * (d + 1)) false = decide (j ≤ s.val / h)
        rw [rawVec_flag]
        exact decide_eq_decide.mpr (by
          show j * h ≤ s.val ↔ j ≤ s.val / h
          rw [Nat.le_div_iff_mul_le (by omega : 0 < h)]))
      p hp
  have hdata_bd : ∀ (p r z : Nat), p < q → r < h → z < d → (p * h + r) * (d + 1) + (z + 1) < N + 2 := by
    intro p r z hp hr hz
    have hidx : p * h + r < k := by
      have h1 : (p + 1) * h ≤ q * h := Nat.mul_le_mul_right h hp
      have h2 : (p + 1) * h = p * h + h := by ring
      omega
    have h1 : (p * h + r + 1) * (d + 1) ≤ k * (d + 1) := Nat.mul_le_mul_right _ hidx
    have h2 : (p * h + r + 1) * (d + 1) = (p * h + r) * (d + 1) + (d + 1) := by ring
    dsimp only [N]; omega
  have hrec_one : ∀ (r : Fin h) (z : Fin d) (gs : List Gate),
      ValidGates N gs → (∃ tail, gs = dec.1 ++ tail) →
      ∃ (gs' : List Gate) (w : Nat) (extra : List Gate),
        gs' = gs ++ extra ∧ notCountL extra = 0 ∧ posCount extra = 2 * (q - 1) ∧
        ValidGates N gs' ∧ w < N + 2 + gs'.length ∧
        ∀ (s : Fin k) (x : Fin d → Bool), s.val % h = r.val →
          (evalW gs' (rawVec d k s x)).getD w false = x z := by
    intro r z gs hgs ⟨tail, htail⟩
    have hloop : ∀ (c : Nat) (hc : c ≤ q - 1),
        ∃ (gsc : List Gate) (w : Nat) (ex : List Gate),
          gsc = gs ++ ex ∧ notCountL ex = 0 ∧ posCount ex = 2 * c ∧
          ValidGates N gsc ∧ w < N + 2 + gsc.length ∧
          ∀ (s : Fin k) (x : Fin d → Bool), s.val % h = r.val →
            (evalW gsc (rawVec d k s x)).getD w false =
              (decide (s.val / h < c ∨ s.val / h = q - 1) && x z) := by
      intro c
      induction c with
      | zero =>
        intro _
        let w0 := ((q - 1) * h + r.val) * (d + 1) + (z.val + 1)
        have hw0_lt : w0 < N + 2 := hdata_bd (q - 1) r.val z.val (by omega) r.isLt z.isLt
        refine ⟨gs, w0, [], by simp, rfl, by simp [posCount], hgs, by omega, ?_⟩
        intro s x hrem
        rw [evalW_pre gs (rawVec d k s x) w0 (by rw [rawVec_len]; exact hw0_lt)]
        have hidx : (q - 1) * h + r.val < k := by
          have h1 : (q - 1 + 1) * h = q * h := by congr 1; omega
          have h2 : (q - 1 + 1) * h = (q - 1) * h + h := by ring
          have := r.isLt; omega
        change (rawVec d k s x).getD ((⟨(q - 1) * h + r.val, hidx⟩ : Fin k).val * (d + 1) + (z.val + 1)) false = _
        rw [rawVec_data]
        have hdm : s.val = (s.val / h) * h + r.val := by
          have := Nat.div_add_mod s.val h; rw [Nat.mul_comm, hrem] at this; exact this.symm
        have hsv_lt : s.val / h < q := by
          have h1 : s.val < q * h := by rw [hqh]; exact s.isLt
          exact (Nat.div_lt_iff_lt_mul (by omega : 0 < h)).mpr h1
        have hnotlt : ¬ (⟨(q - 1) * h + r.val, hidx⟩ : Fin k) < s := by
          show ¬ (q - 1) * h + r.val < s.val
          have : (s.val / h) * h ≤ (q - 1) * h := Nat.mul_le_mul_right h (by omega)
          omega
        rw [decide_eq_false hnotlt, Bool.false_or]
        have hiff : ((⟨(q - 1) * h + r.val, hidx⟩ : Fin k) = s) ↔ (s.val / h < 0 ∨ s.val / h = q - 1) := by
          simp only [Nat.not_lt_zero, false_or, Fin.ext_iff]
          constructor
          · intro heq
            have hmul : (q - 1) * h = (s.val / h) * h := by omega
            exact (Nat.eq_of_mul_eq_mul_right (by omega) hmul).symm
          · intro heq
            show (q - 1) * h + r.val = s.val
            rw [hdm, heq]
        rw [decide_eq_decide.mpr hiff]
      | succ c ihc =>
        intro hc
        rcases ihc (by omega) with ⟨gsc, wPrev, ex, heq, hnot_ex, hpos_ex, hvalc, hwPrev, hevalc⟩
        let dW := (c * h + r.val) * (d + 1) + (z.val + 1)
        have hdW_lt : dW < N + 2 := hdata_bd c r.val z.val (by omega) r.isLt z.isLt
        have heqc_lt : dec.2 c < N + 2 + gsc.length := by
          have h1 := hbdDec c (by omega)
          rw [heq, htail, List.length_append, List.length_append]; omega
        let aIdx := N + 2 + gsc.length
        let g1 := gsc ++ [⟨GateOp.and, [dec.2 c, dW]⟩]
        let oIdx := N + 2 + g1.length
        let g2 := g1 ++ [⟨GateOp.or, [wPrev, aIdx]⟩]
        have hval1 : ValidGates N g1 :=
          validGates_snoc N gsc ⟨GateOp.and, [dec.2 c, dW]⟩ hvalc (Or.inl rfl) (by simp) (by
            intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
        have hval2 : ValidGates N g2 :=
          validGates_snoc N g1 ⟨GateOp.or, [wPrev, aIdx]⟩ hval1 (Or.inr (Or.inl rfl)) (by simp) (by
            intro i hi; simp at hi; rcases hi with rfl | rfl
            · simp only [g1, List.length_append, List.length_singleton]; omega
            · simp [g1, aIdx])
        refine ⟨g2, oIdx, ex ++ [⟨GateOp.and, [dec.2 c, dW]⟩, ⟨GateOp.or, [wPrev, aIdx]⟩], ?_, ?_, ?_, hval2, by simp [g2, oIdx], ?_⟩
        · simp [g2, g1, heq, List.append_assoc]
        · rw [notCountL_append, hnot_ex]; rfl
        · rw [posCount_append, hpos_ex]
          have : posCount [⟨GateOp.and, [dec.2 c, dW]⟩, ⟨GateOp.or, [wPrev, aIdx]⟩] = 2 := rfl
          omega
        · intro s x hrem
          have hlast2 := evalW_snoc_last g1 ⟨GateOp.or, [wPrev, aIdx]⟩ (rawVec d k s x)
          rw [rawVec_len] at hlast2
          change (evalW (g1 ++ [⟨GateOp.or, [wPrev, aIdx]⟩]) (rawVec d k s x)).getD (N + 2 + g1.length) false = _
          rw [hlast2]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          have hwP : (evalW g1 (rawVec d k s x)).getD wPrev false =
              (decide (s.val / h < c ∨ s.val / h = q - 1) && x z) := by
            rw [evalW_append_pre gsc _ (rawVec d k s x) wPrev (by rw [rawVec_len]; exact hwPrev)]
            exact hevalc s x hrem
          have haV : (evalW g1 (rawVec d k s x)).getD aIdx false =
              (decide (c = s.val / h) && x z) := by
            have hlast1 := evalW_snoc_last gsc ⟨GateOp.and, [dec.2 c, dW]⟩ (rawVec d k s x)
            rw [rawVec_len] at hlast1
            change (evalW (gsc ++ [⟨GateOp.and, [dec.2 c, dW]⟩]) (rawVec d k s x)).getD (N + 2 + gsc.length) false = _
            rw [hlast1]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            have hdec_v : (evalW gsc (rawVec d k s x)).getD (dec.2 c) false = decide (c = s.val / h) := by
              rw [heq, htail, List.append_assoc,
                evalW_append_pre dec.1 _ (rawVec d k s x) (dec.2 c) (by rw [rawVec_len]; exact hbdDec c (by omega))]
              exact hdec_eval s x c (by omega)
            rw [hdec_v]
            by_cases hcs : c = s.val / h
            · rw [decide_eq_true hcs, Bool.true_and, Bool.true_and]
              rw [evalW_pre gsc (rawVec d k s x) dW (by rw [rawVec_len]; exact hdW_lt)]
              have hidx : c * h + r.val < k := by
                have h1 : (c + 1) * h ≤ q * h := Nat.mul_le_mul_right h (by omega)
                have h2 : (c + 1) * h = c * h + h := by ring
                have := r.isLt; omega
              change (rawVec d k s x).getD ((⟨c * h + r.val, hidx⟩ : Fin k).val * (d + 1) + (z.val + 1)) false = x z
              rw [rawVec_data]
              have hdm : s.val = (s.val / h) * h + r.val := by
                have := Nat.div_add_mod s.val h; rw [Nat.mul_comm, hrem] at this; exact this.symm
              have hfeq : (⟨c * h + r.val, hidx⟩ : Fin k) = s := Fin.ext (by show c * h + r.val = s.val; rw [hdm, ← hcs])
              rw [hfeq]; simp
            · rw [decide_eq_false hcs, Bool.false_and, Bool.false_and]
          rw [hwP, haV]
          by_cases hcond1 : s.val / h < c ∨ s.val / h = q - 1
          · have hne : c ≠ s.val / h := by omega
            have hcond2 : s.val / h < c + 1 ∨ s.val / h = q - 1 := by omega
            rw [decide_eq_true hcond1, decide_eq_false hne, decide_eq_true hcond2]; simp
          · by_cases hcs : c = s.val / h
            · have hcond2 : s.val / h < c + 1 ∨ s.val / h = q - 1 := by omega
              rw [decide_eq_false hcond1, decide_eq_true hcs, decide_eq_true hcond2]; simp
            · have hcond2 : ¬ (s.val / h < c + 1 ∨ s.val / h = q - 1) := by omega
              rw [decide_eq_false hcond1, decide_eq_false hcs, decide_eq_false hcond2]; simp
    rcases hloop (q - 1) (le_refl _) with ⟨gs', w, ex, heq, hnot_ex, hpos_ex, hval', hw', heval'⟩
    refine ⟨gs', w, ex, heq, hnot_ex, hpos_ex, hval', hw', fun s x hrem => ?_⟩
    rw [heval' s x hrem]
    have hsv_lt : s.val / h < q := by
      have h1 : s.val < q * h := by rw [hqh]; exact s.isLt
      exact (Nat.div_lt_iff_lt_mul (by omega : 0 < h)).mpr h1
    have htr : s.val / h < q - 1 ∨ s.val / h = q - 1 := by omega
    rw [decide_eq_true htr, Bool.true_and]
  have hrec_row : ∀ (r : Fin h) (c : Nat) (hc : c ≤ d) (gs : List Gate),
      ValidGates N gs → (∃ tail, gs = dec.1 ++ tail) →
      ∃ (gs' : List Gate) (wRow : Nat → Nat) (extra : List Gate),
        gs' = gs ++ extra ∧ notCountL extra = 0 ∧ posCount extra = c * (2 * (q - 1)) ∧
        ValidGates N gs' ∧ (∀ z < c, wRow z < N + 2 + gs'.length) ∧
        ∀ (s : Fin k) (x : Fin d → Bool), s.val % h = r.val →
          ∀ (z : Fin d), z.val < c → (evalW gs' (rawVec d k s x)).getD (wRow z.val) false = x z := by
    intro r c
    induction c with
    | zero =>
      intro _ gs hgs _
      exact ⟨gs, fun _ => N, [], by simp, rfl, by simp [posCount], hgs, fun z hz => by omega, fun _ _ _ z hz => by omega⟩
    | succ c ihc =>
      intro hc gs hgs htail
      rcases ihc (by omega) gs hgs htail with ⟨gs1, w1, ex1, heq1, hnot1, hpos1, hval1, hbd1, heval1⟩
      rcases htail with ⟨tail, htail_eq⟩
      rcases hrec_one r ⟨c, hc⟩ gs1 hval1 ⟨tail ++ ex1, by rw [heq1, htail_eq, List.append_assoc]⟩ with
        ⟨gs2, w2, ex2, heq2, hnot2, hpos2, hval2, hbd2, heval2⟩
      refine ⟨gs2, fun z => if z = c then w2 else w1 z, ex1 ++ ex2, ?_, ?_, ?_, hval2, ?_, ?_⟩
      · rw [heq2, heq1, List.append_assoc]
      · rw [notCountL_append, hnot1, hnot2]
      · rw [posCount_append, hpos1, hpos2]
        have : (c + 1) * (2 * (q - 1)) = c * (2 * (q - 1)) + 2 * (q - 1) := by ring
        omega
      · intro z hz
        dsimp only
        by_cases hzc : z = c
        · rw [if_pos hzc]; exact hbd2
        · rw [if_neg hzc]; have := hbd1 z (by omega); rw [heq2, List.length_append]; omega
      · intro s x hrem z hz
        dsimp only
        by_cases hzc : z.val = c
        · rw [if_pos hzc]
          have hzeq : z = ⟨c, hc⟩ := Fin.ext hzc
          rw [hzeq]; exact heval2 s x hrem
        · rw [if_neg hzc, heq2, evalW_append_pre gs1 ex2 (rawVec d k s x) (w1 z.val)
            (by rw [rawVec_len]; exact hbd1 z.val (by omega))]
          exact heval1 s x hrem z (by omega)
  have hrec_all : ∀ (c : Nat) (hc : c ≤ h),
      ∃ (gs3 : List Gate) (bitW : Nat → Nat → Nat) (ex3 : List Gate),
        gs3 = dec.1 ++ ex3 ∧ notCountL ex3 = 0 ∧ posCount ex3 = c * (d * (2 * (q - 1))) ∧
        ValidGates N gs3 ∧ (∀ r < c, ∀ z < d, bitW r z < N + 2 + gs3.length) ∧
        ∀ (s : Fin k) (x : Fin d → Bool), s.val % h < c →
          ∀ (z : Fin d), (evalW gs3 (rawVec d k s x)).getD (bitW (s.val % h) z.val) false = x z := by
    intro c
    induction c with
    | zero =>
      intro _
      exact ⟨dec.1, fun _ _ => N, [], by simp, rfl, by simp [posCount], hvalDec,
        fun r hr => by omega, fun s _ hs => by omega⟩
    | succ c ihc =>
      intro hc
      rcases ihc (by omega) with ⟨gs1, bw1, ex1, heq1, hnot1, hpos1, hval1, hbd1, heval1⟩
      rcases hrec_row ⟨c, hc⟩ d (le_refl d) gs1 hval1 ⟨ex1, heq1⟩ with
        ⟨gs2, w2, ex2, heq2, hnot2, hpos2, hval2, hbd2, heval2⟩
      refine ⟨gs2, fun r z => if r = c then w2 z else bw1 r z, ex1 ++ ex2, ?_, ?_, ?_, hval2, ?_, ?_⟩
      · rw [heq2, heq1, List.append_assoc]
      · rw [notCountL_append, hnot1, hnot2]
      · rw [posCount_append, hpos1, hpos2]
        have : (c + 1) * (d * (2 * (q - 1))) = c * (d * (2 * (q - 1))) + d * (2 * (q - 1)) := by ring
        omega
      · intro r hr z hz
        dsimp only
        by_cases hrc : r = c
        · rw [if_pos hrc]; exact hbd2 z hz
        · rw [if_neg hrc]; have := hbd1 r (by omega) z hz; rw [heq2, List.length_append]; omega
      · intro s x hrem z
        dsimp only
        by_cases hrc : s.val % h = c
        · rw [if_pos hrc]
          exact heval2 s x hrc z z.isLt
        · rw [if_neg hrc, heq2, evalW_append_pre gs1 ex2 (rawVec d k s x) (bw1 (s.val % h) z.val)
            (by rw [rawVec_len]; exact hbd1 (s.val % h) (by omega) z.val z.isLt)]
          exact heval1 s x (by omega) z
  rcases hrec_all h (le_refl h) with ⟨gs3, bitW, ex3, heq3, hnot3, hpos3, hval3, hbd3, heval3⟩
  have hprod_row : ∀ (r : Fin h) (i : Fin n) (c : Nat) (hc : c ≤ n) (gs : List Gate),
      ValidGates N gs → (∃ tail, gs = gs3 ++ tail) →
      ∃ (gs' : List Gate) (pW : Nat → Nat) (extra : List Gate),
        gs' = gs ++ extra ∧ notCountL extra = 0 ∧ posCount extra = c ∧
        ValidGates N gs' ∧ (∀ j < c, pW j < N + 2 + gs'.length) ∧
        ∀ (s : Fin k) (x : Fin d → Bool), s.val % h = r.val →
          ∀ (j : Fin n), j.val < c →
            (evalW gs' (rawVec d k s x)).getD (pW j.val) false =
              (x (Fin.castAdd n i) && x (Fin.natAdd n j)) := by
    intro r i c
    induction c with
    | zero =>
      intro _ gs hgs _
      exact ⟨gs, fun _ => N, [], by simp, rfl, by simp [posCount], hgs, fun j hj => by omega, fun _ _ _ j hj => by omega⟩
    | succ c ihc =>
      intro hc gs hgs htail
      rcases ihc (by omega) gs hgs htail with ⟨gs1, p1, ex1, heq1, hnot1, hpos1, hval1, hbd1, heval1⟩
      rcases htail with ⟨tail, htail_eq⟩
      have hbi_lt : bitW r.val i.val < N + 2 + gs1.length := by
        have h1 := hbd3 r.val r.isLt i.val (by have := i.isLt; dsimp only [d]; omega)
        rw [heq1, htail_eq, List.length_append, List.length_append]; omega
      have hbj_lt : bitW r.val (n + c) < N + 2 + gs1.length := by
        have h1 := hbd3 r.val r.isLt (n + c) (by dsimp only [d]; omega)
        rw [heq1, htail_eq, List.length_append, List.length_append]; omega
      let gNew : Gate := ⟨GateOp.and, [bitW r.val i.val, bitW r.val (n + c)]⟩
      let wNew := N + 2 + gs1.length
      have hval2 : ValidGates N (gs1 ++ [gNew]) :=
        validGates_snoc N gs1 gNew hval1 (Or.inl rfl) (by simp [gNew]) (by
          intro v hv; simp [gNew] at hv; rcases hv with rfl | rfl <;> assumption)
      refine ⟨gs1 ++ [gNew], fun j => if j = c then wNew else p1 j, ex1 ++ [gNew], ?_, ?_, ?_, hval2, ?_, ?_⟩
      · rw [heq1, List.append_assoc]
      · rw [notCountL_append, hnot1]; rfl
      · rw [posCount_append, hpos1]; rfl
      · intro j hj
        dsimp only
        by_cases hjc : j = c
        · rw [if_pos hjc]; simp [wNew]
        · rw [if_neg hjc]; have := hbd1 j (by omega); simp only [List.length_append, List.length_singleton]; omega
      · intro s x hrem j hj
        dsimp only
        by_cases hjc : j.val = c
        · rw [if_pos hjc]
          have hlast := evalW_snoc_last gs1 gNew (rawVec d k s x)
          rw [rawVec_len] at hlast
          change (evalW (gs1 ++ [gNew]) (rawVec d k s x)).getD (N + 2 + gs1.length) false = _
          rw [hlast]
          simp only [gNew, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          have h1 : (evalW gs1 (rawVec d k s x)).getD (bitW r.val i.val) false = x (Fin.castAdd n i) := by
            rw [heq1, htail_eq, List.append_assoc,
              evalW_append_pre gs3 _ (rawVec d k s x) (bitW r.val i.val)
                (by rw [rawVec_len]; exact hbd3 r.val r.isLt i.val (by have := i.isLt; dsimp only [d]; omega))]
            rw [← hrem]
            exact heval3 s x (Nat.mod_lt s.val (by omega)) (Fin.castAdd n i)
          have h2 : (evalW gs1 (rawVec d k s x)).getD (bitW r.val (n + c)) false = x (Fin.natAdd n j) := by
            rw [heq1, htail_eq, List.append_assoc,
              evalW_append_pre gs3 _ (rawVec d k s x) (bitW r.val (n + c))
                (by rw [rawVec_len]; exact hbd3 r.val r.isLt (n + c) (by dsimp only [d]; omega))]
            have hnc : n + c = (Fin.natAdd n j).val := by show n + c = n + j.val; omega
            rw [← hrem, hnc]
            exact heval3 s x (Nat.mod_lt s.val (by omega)) (Fin.natAdd n j)
          rw [h1, h2]
        · rw [if_neg hjc, evalW_append_pre gs1 [gNew] (rawVec d k s x) (p1 j.val)
            (by rw [rawVec_len]; exact hbd1 j.val (by omega))]
          exact heval1 s x hrem j (by omega)
  have hprod_bank : ∀ (r : Fin h) (c : Nat) (hc : c ≤ n) (gs : List Gate),
      ValidGates N gs → (∃ tail, gs = gs3 ++ tail) →
      ∃ (gs' : List Gate) (bW : Nat → Nat → Nat) (extra : List Gate),
        gs' = gs ++ extra ∧ notCountL extra = 0 ∧ posCount extra = c * n ∧
        ValidGates N gs' ∧ (∀ i < c, ∀ j < n, bW i j < N + 2 + gs'.length) ∧
        ∀ (s : Fin k) (x : Fin d → Bool), s.val % h = r.val →
          ∀ (i : Fin n), i.val < c → ∀ (j : Fin n),
            (evalW gs' (rawVec d k s x)).getD (bW i.val j.val) false =
              (x (Fin.castAdd n i) && x (Fin.natAdd n j)) := by
    intro r c
    induction c with
    | zero =>
      intro _ gs hgs _
      exact ⟨gs, fun _ _ => N, [], by simp, rfl, by simp [posCount], hgs,
        fun i hi => by omega, fun _ _ _ i hi => by omega⟩
    | succ c ihc =>
      intro hc gs hgs htail
      rcases ihc (by omega) gs hgs htail with ⟨gs1, b1, ex1, heq1, hnot1, hpos1, hval1, hbd1, heval1⟩
      rcases htail with ⟨tail, htail_eq⟩
      rcases hprod_row r ⟨c, hc⟩ n (le_refl n) gs1 hval1 ⟨tail ++ ex1, by rw [heq1, htail_eq, List.append_assoc]⟩ with
        ⟨gs2, p2, ex2, heq2, hnot2, hpos2, hval2, hbd2, heval2⟩
      refine ⟨gs2, fun i j => if i = c then p2 j else b1 i j, ex1 ++ ex2, ?_, ?_, ?_, hval2, ?_, ?_⟩
      · rw [heq2, heq1, List.append_assoc]
      · rw [notCountL_append, hnot1, hnot2]
      · rw [posCount_append, hpos1, hpos2]
        have : (c + 1) * n = c * n + n := by ring
        omega
      · intro i hi j hj
        dsimp only
        by_cases hic : i = c
        · rw [if_pos hic]; exact hbd2 j hj
        · rw [if_neg hic]; have := hbd1 i (by omega) j hj; rw [heq2, List.length_append]; omega
      · intro s x hrem i hi j
        dsimp only
        by_cases hic : i.val = c
        · rw [if_pos hic]
          have hieq : i = ⟨c, hc⟩ := Fin.ext hic
          rw [hieq]; exact heval2 s x hrem j j.isLt
        · rw [if_neg hic, heq2, evalW_append_pre gs1 ex2 (rawVec d k s x) (b1 i.val j.val)
            (by rw [rawVec_len]; exact hbd1 i.val (by omega) j.val j.isLt)]
          exact heval1 s x hrem i (by omega) j
  have hprod_all : ∀ (c : Nat) (hc : c ≤ h),
      ∃ (gs4 : List Gate) (allW : Nat → Nat → Nat → Nat) (ex4 : List Gate),
        gs4 = gs3 ++ ex4 ∧ notCountL ex4 = 0 ∧ posCount ex4 = c * n ^ 2 ∧
        ValidGates N gs4 ∧ (∀ r < c, ∀ i < n, ∀ j < n, allW r i j < N + 2 + gs4.length) ∧
        ∀ (s : Fin k) (x : Fin d → Bool), s.val % h < c →
          ∀ (i j : Fin n),
            (evalW gs4 (rawVec d k s x)).getD (allW (s.val % h) i.val j.val) false =
              (x (Fin.castAdd n i) && x (Fin.natAdd n j)) := by
    intro c
    induction c with
    | zero =>
      intro _
      exact ⟨gs3, fun _ _ _ => N, [], by simp, rfl, by simp [posCount], hval3,
        fun r hr => by omega, fun _ _ hs => by omega⟩
    | succ c ihc =>
      intro hc
      rcases ihc (by omega) with ⟨gs1, a1, ex1, heq1, hnot1, hpos1, hval1, hbd1, heval1⟩
      rcases hprod_bank ⟨c, hc⟩ n (le_refl n) gs1 hval1 ⟨ex1, heq1⟩ with
        ⟨gs2, b2, ex2, heq2, hnot2, hpos2, hval2, hbd2, heval2⟩
      refine ⟨gs2, fun r i j => if r = c then b2 i j else a1 r i j, ex1 ++ ex2, ?_, ?_, ?_, hval2, ?_, ?_⟩
      · rw [heq2, heq1, List.append_assoc]
      · rw [notCountL_append, hnot1, hnot2]
      · rw [posCount_append, hpos1, hpos2]
        have : (c + 1) * n ^ 2 = c * n ^ 2 + n * n := by ring
        omega
      · intro r hr i hi j hj
        dsimp only
        by_cases hrc : r = c
        · rw [if_pos hrc]; exact hbd2 i hi j hj
        · rw [if_neg hrc]; have := hbd1 r (by omega) i hi j hj; rw [heq2, List.length_append]; omega
      · intro s x hrem i j
        dsimp only
        by_cases hrc : s.val % h = c
        · rw [if_pos hrc]
          exact heval2 s x hrc i i.isLt j
        · rw [if_neg hrc, heq2, evalW_append_pre gs1 ex2 (rawVec d k s x) (a1 (s.val % h) i.val j.val)
            (by rw [rawVec_len]; exact hbd1 (s.val % h) (by omega) i.val i.isLt j.val j.isLt)]
          exact heval1 s x (by omega) i j
  rcases hprod_all h (le_refl h) with ⟨gsFinal, allW, ex4, heq4, hnot4, hpos4, hvalFinal, hbdFinal, hevalFinal⟩
  let C : Circuit := ⟨gsFinal, 0⟩
  have hnotFinal : notCount C = e := by
    rw [notCount_eq_notCountL]
    dsimp only [C]
    rw [heq4, heq3, heqDec, List.nil_append, notCountL_append, notCountL_append, hnotDec, hnot3, hnot4]
    omega
  have hposFinal : C.size - notCount C = posCount gsFinal := by
    have htot := posCount_add_notCountL gsFinal
    have hnc := notCount_eq_notCountL C
    dsimp only [C, Circuit.size] at hnc ⊢
    omega
  have hpos_le : posCount gsFinal ≤ h * n ^ 2 + (4 * n * h) * (q - 1) + 4 * (q - 1 - e) := by
    rw [heq4, heq3, heqDec, List.nil_append, posCount_append, posCount_append, hpos3, hpos4]
    have h4nh : h * (d * (2 * (q - 1))) = (4 * n * h) * (q - 1) := by dsimp only [d]; ring
    rw [h4nh]
    omega
  rcases validGates_to_valid N gsFinal hvalFinal with ⟨hfan, hrb, hout⟩
  refine ⟨C, fun s i j => allW (s.val % h) i.val j.val, hfan, hrb, hout, ?_, ?_, le_of_eq hnotFinal, by rw [hposFinal]; exact hpos_le⟩
  · intro s i j
    exact hbdFinal (s.val % h) (Nat.mod_lt s.val (by omega)) i.val i.isLt j.val j.isLt
  · intro s x i j
    exact hevalFinal s x (Nat.mod_lt s.val (by omega)) i j

private lemma main_body (B m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    let k := 2 ^ B * m
    let d := n + n
    let N := k * (d + 1)
    let fits := fun (C : Circuit) (tap : Fin k → Fin n → Fin n → Nat) =>
      FanInTwo C ∧ ReadsBack (N + 2) C ∧ C.output < N + 2 + C.size ∧
      (∀ s i j, tap s i j < N + 2 + C.size) ∧
      ∀ s x i j, (C.wires (rawVec d k s x)).getD (tap s i j) false =
        (x (Fin.castAdd n i) && x (Fin.natAdd n j))
    (∀ e, e ≤ B →
      let q := 2 ^ e
      let h := k / q
      (∀ C tap, fits C tap → notCount C ≤ e → h * n ^ 2 ≤ C.size - notCount C) ∧
      ∃ C tap, fits C tap ∧ notCount C ≤ e ∧
        C.size - notCount C ≤ h * n ^ 2 + (4 * n * h) * (q - 1) + 4 * (q - 1 - e)) ∧
    (8 * 2 ^ B ≤ n → ∀ e, e < B → ∃ C tap, fits C tap ∧ notCount C ≤ e + 1 ∧
      ∀ D out, fits D out → notCount D ≤ e → C.size < D.size) := by
  intro k d N fits
  have hpart1 : ∀ e, e ≤ B →
      let q := 2 ^ e
      let h := k / q
      (∀ C tap, fits C tap → notCount C ≤ e → h * n ^ 2 ≤ C.size - notCount C) ∧
      ∃ C tap, fits C tap ∧ notCount C ≤ e ∧
        C.size - notCount C ≤ h * n ^ 2 + (4 * n * h) * (q - 1) + 4 * (q - 1 - e) := by
    intro e he
    refine ⟨fun C tap hfit hnot =>
      lower_bound_proof B m n e hm hn he C tap hfit.1 hfit.2.1 hfit.2.2.1 hfit.2.2.2.1 hfit.2.2.2.2 hnot, ?_⟩
    rcases upper_bound_proof B m n e hm hn he with ⟨C, tap, h1, h2, h3, h4, h5, hnot, hsz⟩
    exact ⟨C, tap, ⟨h1, h2, h3, h4, h5⟩, hnot, hsz⟩
  refine ⟨hpart1, ?_⟩
  intro h8n e he
  rcases (hpart1 (e + 1) (by omega)).2 with ⟨C, tap, hfitC, hnotC, hszC⟩
  refine ⟨C, tap, hfitC, hnotC, fun D out hfitD hnotD => ?_⟩
  have hlbD := (hpart1 e (by omega)).1 D out hfitD hnotD
  set q := 2 ^ e
  set q1 := 2 ^ (e + 1)
  set h := k / q
  set h1 := k / q1
  have hq1_eq : q1 = 2 * q := by dsimp only [q1, q]; rw [pow_succ, Nat.mul_comm]
  have hq1_le_B : q1 ≤ 2 ^ B := Nat.pow_le_pow_right (by omega) (by omega)
  have hq1_ge2 : 2 ≤ q1 := by have : 1 ≤ q := Nat.one_le_two_pow; omega
  have hh_eq : h = 2 * h1 := by
    dsimp only [h, h1, q, q1, k]
    have hp1 : 2 ^ B = 2 ^ (e + 1) * 2 ^ (B - (e + 1)) := by rw [← pow_add]; congr 1; omega
    have hp0 : 2 ^ B = 2 ^ e * (2 * 2 ^ (B - (e + 1))) := by
      rw [hp1, pow_succ]; ring
    have hk1 : 2 ^ B * m = 2 ^ (e + 1) * (2 ^ (B - (e + 1)) * m) := by rw [hp1]; ring
    have hk0 : 2 ^ B * m = 2 ^ e * (2 * (2 ^ (B - (e + 1)) * m)) := by rw [hp0]; ring
    conv_lhs => rw [hk0]
    conv_rhs => rw [hk1]
    rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos (e + 1)),
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos e)]
  have hh1_pos : 1 ≤ h1 := by
    dsimp only [h1, q1, k]
    have hp1 : 2 ^ B = 2 ^ (e + 1) * 2 ^ (B - (e + 1)) := by rw [← pow_add]; congr 1; omega
    have hk1 : 2 ^ B * m = 2 ^ (e + 1) * (2 ^ (B - (e + 1)) * m) := by rw [hp1]; ring
    rw [hk1, Nat.mul_div_cancel_left _ (Nat.two_pow_pos (e + 1))]
    exact Nat.mul_pos (Nat.two_pow_pos _) hm
  have hC_tot : C.size ≤ h1 * n ^ 2 + (4 * n * h1) * (q1 - 1) + 4 * (q1 - 1 - (e + 1)) + (e + 1) := by
    have hnot_le_sz : notCount C ≤ C.size := by
      rw [notCount_eq_notCountL]
      have := posCount_add_notCountL C.gates
      dsimp only [Circuit.size]; omega
    omega
  have hD_tot : 2 * h1 * n ^ 2 ≤ D.size := by
    rw [hh_eq] at hlbD
    have : 2 * h1 * n ^ 2 = (2 * h1) * n ^ 2 := by ring
    omega
  have h4q1 : 4 * (q1 - 1 - (e + 1)) + (e + 1) < 4 * q1 := by
    have he1_le : e + 1 ≤ q1 - 1 := le_two_pow_sub_one (e + 1)
    omega
  have h4q1_lt : 4 * q1 < 4 * n * h1 := by
    have : 4 * q1 < n := by omega
    have : n ≤ 4 * n * h1 := by nlinarith
    omega
  have hmul1 : (4 * n * h1) * (q1 - 1) + 4 * n * h1 = 4 * q1 * (n * h1) := by
    have : (q1 - 1) + 1 = q1 := by omega
    calc (4 * n * h1) * (q1 - 1) + 4 * n * h1
        = (4 * n * h1) * ((q1 - 1) + 1) := by ring
      _ = (4 * n * h1) * q1 := by rw [this]
      _ = 4 * q1 * (n * h1) := by ring
  have hmul2 : 4 * q1 * (n * h1) ≤ h1 * n ^ 2 := by
    have hle1 : 4 * q1 ≤ n := by omega
    have hle2 : 4 * q1 * (n * h1) ≤ n * (n * h1) := Nat.mul_le_mul_right _ hle1
    have hring : n * (n * h1) = h1 * n ^ 2 := by ring
    omega
  have h2hn : 2 * h1 * n ^ 2 = h1 * n ^ 2 + h1 * n ^ 2 := by ring
  omega

private lemma main_bridge :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (B m n : Nat), 0 < m → 0 < n →
      let k := 2 ^ B * m
      let d := n + n
      let N := k * (d + 1)
      let raw := fun (s : Fin k) (x : Fin d → Bool) =>
        (List.ofFn (fun i : Fin k => decide (i ≤ s) :: List.ofFn (fun z : Fin d =>
          decide (i < s) || (decide (i = s) && x z)))).flatten ++ [false, true]
      let fits := fun (C : Circuit) (tap : Fin k → Fin n → Fin n → Nat) =>
        FanInTwo C ∧ ReadsBack (N + 2) C ∧
        C.output < N + 2 + C.size ∧ (∀ s i j, tap s i j < N + 2 + C.size) ∧
        ∀ s x i j, (C.wires (raw s x)).getD (tap s i j) false =
          (x (Fin.castAdd n i) && x (Fin.natAdd n j))
      let bcount := notCount
      (∀ e, e ≤ B →
        let q := 2 ^ e
        let h := k / q
        (∀ C tap, fits C tap → bcount C ≤ e → h * n ^ 2 ≤ C.size - bcount C) ∧
        ∃ C tap, fits C tap ∧ bcount C ≤ e ∧
          C.size - bcount C ≤ h * n ^ 2 + (4 * n * h) * (q - 1) + 4 * (q - 1 - e)) ∧
      (8 * 2 ^ B ≤ n → ∀ e, e < B → ∃ C tap, fits C tap ∧ bcount C ≤ e + 1 ∧
        ∀ D out, fits D out → bcount D ≤ e → C.size < D.size) := by
  intro B m n hm hn k d N raw fits bcount
  have hraw_eq : ∀ (s : Fin k) (x : Fin d → Bool), raw s x = rawVec d k s x := by
    intro s x
    dsimp only [raw, rawVec]
    congr 1; congr 1; congr 1; funext i
    congr 1
    · exact congrArg (@decide (i ≤ s)) (Subsingleton.elim _ _)
    · congr 1; funext z
      have h1 : @decide (i < s) (Classical.propDecidable _) = decide (i < s) :=
        congrArg (@decide (i < s)) (Subsingleton.elim _ _)
      have h2 : @decide (i = s) (Classical.propDecidable _) = decide (i = s) :=
        congrArg (@decide (i = s)) (Subsingleton.elim _ _)
      rw [h1, h2]
  have hfits_iff : ∀ C tap, fits C tap ↔
      (FanInTwo C ∧ ReadsBack (N + 2) C ∧ C.output < N + 2 + C.size ∧
      (∀ s i j, tap s i j < N + 2 + C.size) ∧
      ∀ s x i j, (C.wires (rawVec d k s x)).getD (tap s i j) false =
        (x (Fin.castAdd n i) && x (Fin.natAdd n j))) := by
    intro C tap
    dsimp only [fits]
    simp only [hraw_eq]
  rcases main_body B m n hm hn with ⟨hp1, hp2⟩
  refine ⟨fun e he => ?_, fun h8n e he => ?_⟩
  · rcases hp1 e he with ⟨hlb, C, tap, hfit, hnot, hsz⟩
    exact ⟨fun C' tap' hfit' hnot' => hlb C' tap' ((hfits_iff C' tap').mp hfit') hnot',
           C, tap, (hfits_iff C tap).mpr hfit, hnot, hsz⟩
  · rcases hp2 h8n e he with ⟨C, tap, hfit, hnot, hsep⟩
    exact ⟨C, tap, (hfits_iff C tap).mpr hfit, hnot,
      fun D out hfitD hnotD => hsep D out ((hfits_iff D out).mp hfitD) hnotD⟩

end PEqualNP.Outside.L_lib_1331

theorem PEqualNP.Outside.L_lib_1331 : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (B m n : Nat), 0 < m → 0 < n →
  let k := 2^B*m
  let d := n+n
  let N := k*(d+1)
  let raw := fun (s : Fin k) (x : Fin d → Bool) =>
    (List.ofFn (fun i : Fin k => decide (i ≤ s) :: List.ofFn (fun z : Fin d =>
      decide (i < s) || (decide (i=s) && x z)))).flatten ++ [false,true]
  let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin k → Fin n → Fin n → Nat) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+2) C ∧
    C.output < N+2+C.size ∧ (∀ s i j, tap s i j < N+2+C.size) ∧
    ∀ s x i j, (C.wires (raw s x)).getD (tap s i j) false =
      (x (Fin.castAdd n i) && x (Fin.natAdd n j))
  let bcount := PEqualNP.NotBracket.notCount
  (∀ e, e ≤ B →
    let q := 2^e
    let h := k/q
    (∀ C tap, fits C tap → bcount C ≤ e → h*n^2 ≤ C.size-bcount C) ∧
    ∃ C tap, fits C tap ∧ bcount C ≤ e ∧
      C.size-bcount C ≤ h*n^2 + (4*n*h)*(q-1) + 4*(q-1-e)) ∧
  (8*2^B ≤ n → ∀ e, e < B → ∃ C tap, fits C tap ∧ bcount C ≤ e+1 ∧
    ∀ D out, fits D out → bcount D ≤ e → C.size < D.size) :=
  PEqualNP.Outside.L_lib_1331.main_bridge
